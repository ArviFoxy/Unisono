// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! unisono for programs written in C: see `include/unisono.h`, which says
//! what each function does.
//!
//! A sender is the capture end of [`unisono_runtime::send`] with a thread
//! that runs the network end; a receiver is the audio end of
//! [`unisono_runtime::receive`] with a thread that runs its network end.
//! Each network thread is held to the system calls that such a thread makes
//! where the system does that ([`unisono_runtime::syscalls`]).

use std::ffi::{CStr, c_char, c_int};
use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::JoinHandle;
use std::time::Duration;

use unisono_core::packet::Format;
use unisono_core::player::Regulation;
use unisono_core::sender::Settings as StreamSettings;
use unisono_dsp::Parameters;
use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::level::{Choice, Weights};
use unisono_runtime::pump::{ReceiverPlayback, Settings as PlaybackSettings};
use unisono_runtime::receive::{self, Intake, ReceiverAudio, ReceiverNetwork, Reporting, Sizes};
use unisono_runtime::send::{self, CaptureEnd, SenderNetwork, Settings as SenderSettings};
use unisono_runtime::socket::Socket;
use unisono_runtime::{clock, syscalls};

/// The receiver's audio end: room for 16,384 frames, 64 samples of the
/// sender's clock, the arrivals of 8 packets, and 64 reports of its device.
type Audio = ReceiverAudio<256, 64, 8, 64>;

/// The stack of a network thread: 512 KiB, of which it uses a small part.
const STACK: usize = 512 * 1024;

/// What a sender is set up with; `unisono_sender_settings` in the header.
#[repr(C)]
pub struct SenderOptions {
    bind: *const c_char,
    receivers: *const *const c_char,
    receiver_count: usize,
    stream: u16,
    rate: u32,
    channels: u8,
    bits: u8,
    packet_frames: u16,
    cycle_frames: u32,
    level: i64,
    choose_level: c_int,
    protection: c_int,
}

/// A sender that runs; `unisono_sender` in the header.
pub struct Sender {
    capture: CaptureEnd,
    channels: usize,
    stop: Arc<AtomicBool>,
    network: Option<JoinHandle<()>>,
}

/// What a receiver is set up with; `unisono_receiver_settings` in the
/// header.
#[repr(C)]
pub struct ReceiverOptions {
    listen: *const c_char,
    stream: u16,
    identity: u64,
    rate: u32,
    channels: u8,
}

/// A receiver that runs; `unisono_receiver` in the header.
pub struct Receiver {
    audio: Audio,
    channels: usize,
    port: u16,
    stop: Arc<AtomicBool>,
    network: Option<JoinHandle<()>>,
}

/// The host's clock that no one adjusts, in nanoseconds.
#[unsafe(no_mangle)]
pub extern "C" fn unisono_clock() -> i64 {
    clock::raw()
}

/// Writes `reason` to the `size` bytes at `error`, cut to fit, with the zero
/// that ends it.
///
/// # Safety
///
/// `error` is null or points to `size` bytes that may be written.
unsafe fn explain(error: *mut c_char, size: usize, reason: &str) {
    if error.is_null() || size == 0 {
        return;
    }
    let length = reason.len().min(size - 1);
    // SAFETY: `length + 1` is at most `size`, and the bytes of `reason` do
    // not overlap the caller's.
    unsafe {
        std::ptr::copy_nonoverlapping(reason.as_ptr(), error.cast::<u8>(), length);
        error.add(length).write(0);
    }
}

/// The address in the text at `text`.
///
/// # Safety
///
/// `text` is null or points to text that ends with a zero.
unsafe fn address(text: *const c_char) -> Result<SocketAddr, String> {
    if text.is_null() {
        return Err("an address is missing".into());
    }
    // SAFETY: the caller says that the text ends with a zero.
    let text = unsafe { CStr::from_ptr(text) }.to_string_lossy();
    text.parse()
        .map_err(|_| format!("`{text}` is not an address with a port"))
}

/// Fills `settings` with what the program takes when nothing is said.
///
/// # Safety
///
/// `settings` is null or points to a `unisono_sender_settings`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_sender_defaults(settings: *mut SenderOptions) {
    if settings.is_null() {
        return;
    }
    // SAFETY: the caller says that `settings` points to room for one.
    unsafe {
        settings.write(SenderOptions {
            bind: std::ptr::null(),
            receivers: std::ptr::null(),
            receiver_count: 0,
            stream: 1,
            rate: 48_000,
            channels: 2,
            bits: 24,
            packet_frames: 240,
            cycle_frames: 4_096,
            level: 30_000_000,
            choose_level: 1,
            protection: 1,
        });
    }
}

/// The sender that `options` describe, started.
///
/// # Safety
///
/// The pointers of `options` are null or point to what the header says.
unsafe fn start_sender(options: &SenderOptions) -> Result<Sender, String> {
    let format = match options.bits {
        16 => Format::Signed16,
        24 => Format::Signed24,
        _ => return Err("the bits of a sample are 16 or 24".into()),
    };
    if options.rate == 0
        || options.channels == 0
        || options.packet_frames == 0
        || options.cycle_frames == 0
    {
        return Err("the rate, channels, packet and cycle are not zero".into());
    }
    if options.receivers.is_null() || options.receiver_count == 0 {
        return Err("a sender needs a receiver".into());
    }
    let mut receivers = Vec::with_capacity(options.receiver_count);
    for place in 0..options.receiver_count {
        // SAFETY: the caller says that `receivers` points to
        // `receiver_count` texts.
        receivers.push(unsafe { address(*options.receivers.add(place)) }?);
    }
    let bind = if options.bind.is_null() {
        SocketAddr::from(([0, 0, 0, 0], 0))
    } else {
        // SAFETY: the caller says that `bind` is a text.
        unsafe { address(options.bind) }?
    };
    let socket = Socket::bind(bind).map_err(|error| format!("binding {bind}: {error}"))?;
    let window = 2_400;
    // The needs of the last two minutes, and the costs that the program
    // takes when none are given.
    let stretches =
        usize::try_from(120 * u64::from(options.rate) / u64::from(window)).unwrap_or(usize::MAX);
    let choice = (options.choose_level != 0).then_some(Choice {
        weights: Weights {
            latency: 1_000.0,
            target: 0,
            off_target: 0.0,
            gap: 600.0,
            missed: 60_000.0,
            moving: 60.0,
        },
        history: stretches,
        slope: 500_000,
    });
    let channels = usize::from(options.channels);
    let cycle = usize::try_from(options.cycle_frames).unwrap_or(usize::MAX);
    let (capture, sender_end) = send::link(64, cycle, channels);
    let mut network = SenderNetwork::new(
        socket,
        sender_end,
        SenderSettings {
            stream: StreamSettings {
                stream: options.stream,
                rate: options.rate,
                channels: options.channels,
                format,
                span: 2_000,
                window,
                clock: send::clock_identity(),
            },
            packet: options.packet_frames,
            level: options.level,
            choice,
            timeline: send::first_timeline(),
            receivers,
            kept: if options.protection != 0 { 256 } else { 0 },
        },
    );
    let stop = Arc::new(AtomicBool::new(false));
    let stopping = Arc::clone(&stop);
    let thread = std::thread::Builder::new()
        .name("unisono-network".into())
        .stack_size(STACK)
        .spawn(move || {
            // Where the system does not take the list the thread runs on.
            let _ = syscalls::restrict();
            while !stopping.load(Ordering::Relaxed) {
                if network.turn(2).is_err() {
                    break;
                }
                std::thread::sleep(Duration::from_micros(200));
            }
        })
        .map_err(|error| format!("starting the network thread: {error}"))?;
    Ok(Sender {
        capture,
        channels,
        stop,
        network: Some(thread),
    })
}

/// Starts a sender; null on failure, with the reason at `error`.
///
/// # Safety
///
/// `settings` is null or points to a `unisono_sender_settings` whose
/// pointers are as the header says, and `error` is null or points to
/// `error_size` bytes that may be written.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_sender_start(
    settings: *const SenderOptions,
    error: *mut c_char,
    error_size: usize,
) -> *mut Sender {
    // SAFETY: the caller says that `settings` is null or points to one.
    let Some(options) = (unsafe { settings.as_ref() }) else {
        // SAFETY: `error` is as the caller says.
        unsafe { explain(error, error_size, "the settings are missing") };
        return std::ptr::null_mut();
    };
    // SAFETY: the pointers of the settings are as the caller says.
    match unsafe { start_sender(options) } {
        Ok(sender) => Box::into_raw(Box::new(sender)),
        Err(reason) => {
            // SAFETY: `error` is as the caller says.
            unsafe { explain(error, error_size, &reason) };
            std::ptr::null_mut()
        }
    }
}

/// Hands over the frames of one cycle of the capture device.
///
/// # Safety
///
/// `sender` is null or came from `unisono_sender_start` and was not
/// stopped, and no other thread uses it; `frames` points to `frame_count`
/// frames of the sender's channels.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_sender_capture(
    sender: *mut Sender,
    frames: *const f32,
    frame_count: usize,
    position: u64,
    time: i64,
) {
    // SAFETY: the caller says that `sender` is null or a sender that no one
    // else uses.
    let Some(sender) = (unsafe { sender.as_mut() }) else {
        return;
    };
    if frames.is_null() {
        return;
    }
    let samples = frame_count.saturating_mul(sender.channels);
    // SAFETY: the caller says that `frames` points to that many samples.
    let frames = unsafe { std::slice::from_raw_parts(frames, samples) };
    sender.capture.cycle(frames, position, time);
}

/// Stops a sender and frees it.
///
/// # Safety
///
/// `sender` is null or came from `unisono_sender_start` and was not stopped
/// before; it is not used after.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_sender_stop(sender: *mut Sender) {
    if sender.is_null() {
        return;
    }
    // SAFETY: the caller says that `sender` came from `Box::into_raw` in
    // `unisono_sender_start` and is given up here.
    let mut sender = unsafe { Box::from_raw(sender) };
    sender.stop.store(true, Ordering::Relaxed);
    if let Some(thread) = sender.network.take() {
        let _ = thread.join();
    }
}

/// Fills `settings` with what the program takes when nothing is said.
///
/// # Safety
///
/// `settings` is null or points to a `unisono_receiver_settings`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_defaults(settings: *mut ReceiverOptions) {
    if settings.is_null() {
        return;
    }
    // SAFETY: the caller says that `settings` points to room for one.
    unsafe {
        settings.write(ReceiverOptions {
            listen: std::ptr::null(),
            stream: 1,
            identity: 1,
            rate: 48_000,
            channels: 2,
        });
    }
}

/// The receiver that `options` describe, started.
///
/// # Safety
///
/// The pointers of `options` are null or point to what the header says.
unsafe fn start_receiver(options: &ReceiverOptions) -> Result<Receiver, String> {
    if options.rate == 0 || options.channels == 0 {
        return Err("the rate and channels are not zero".into());
    }
    // SAFETY: the caller says that `listen` is null or a text.
    let listen = unsafe { address(options.listen) }?;
    let socket = Socket::bind(listen).map_err(|error| format!("binding {listen}: {error}"))?;
    let port = socket
        .address()
        .map_err(|error| format!("the address of the socket: {error}"))?
        .port();
    let playback = ReceiverPlayback::new(&PlaybackSettings {
        stream: options.stream,
        rate: options.rate,
        channels: options.channels,
        identity: options.identity,
        silence: 1_000_000_000,
        slope_limit: 200_000,
        regulation: Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: options.rate / 200,
        },
        concealment: Parameters::for_rate(options.rate),
        block: 256,
        device_range: 10_000_000,
    });
    let sizes = Sizes {
        buffers: 64,
        datagram: 9_000,
        messages: 64,
    };
    let (network_end, audio_end) = receive::link(sizes);
    let mut network = ReceiverNetwork::new(socket, network_end, options.stream, sizes);
    let audio = Audio::new(
        playback,
        audio_end,
        Intake {
            items: 16,
            reports: Some(Reporting::USUAL),
        },
    );
    let stop = Arc::new(AtomicBool::new(false));
    let stopping = Arc::clone(&stop);
    let thread = std::thread::Builder::new()
        .name("unisono-network".into())
        .stack_size(STACK)
        .spawn(move || {
            // Where the system does not take the list the thread runs on.
            let _ = syscalls::restrict();
            while !stopping.load(Ordering::Relaxed) {
                if network.turn(2).is_err() {
                    break;
                }
            }
        })
        .map_err(|error| format!("starting the network thread: {error}"))?;
    Ok(Receiver {
        audio,
        channels: usize::from(options.channels),
        port,
        stop,
        network: Some(thread),
    })
}

/// Starts a receiver; null on failure, with the reason at `error`.
///
/// # Safety
///
/// `settings` is null or points to a `unisono_receiver_settings` whose
/// pointer is as the header says, and `error` is null or points to
/// `error_size` bytes that may be written.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_start(
    settings: *const ReceiverOptions,
    error: *mut c_char,
    error_size: usize,
) -> *mut Receiver {
    // SAFETY: the caller says that `settings` is null or points to one.
    let Some(options) = (unsafe { settings.as_ref() }) else {
        // SAFETY: `error` is as the caller says.
        unsafe { explain(error, error_size, "the settings are missing") };
        return std::ptr::null_mut();
    };
    // SAFETY: the pointer of the settings is as the caller says.
    match unsafe { start_receiver(options) } {
        Ok(receiver) => Box::into_raw(Box::new(receiver)),
        Err(reason) => {
            // SAFETY: `error` is as the caller says.
            unsafe { explain(error, error_size, &reason) };
            std::ptr::null_mut()
        }
    }
}

/// The port that the receiver receives on.
///
/// # Safety
///
/// `receiver` is null or came from `unisono_receiver_start` and was not
/// stopped.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_port(receiver: *const Receiver) -> u16 {
    // SAFETY: the caller says that `receiver` is null or a receiver.
    unsafe { receiver.as_ref() }.map_or(0, |receiver| receiver.port)
}

/// Fills the frames of one cycle of the playback device.
///
/// # Safety
///
/// `receiver` is null or came from `unisono_receiver_start` and was not
/// stopped, and no other thread uses it; `frames` points to `frame_count`
/// frames of the receiver's channels that may be written.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_play(
    receiver: *mut Receiver,
    frames: *mut f32,
    frame_count: usize,
    position: u64,
    time: i64,
) {
    // SAFETY: the caller says that `receiver` is null or a receiver that no
    // one else uses.
    let Some(receiver) = (unsafe { receiver.as_mut() }) else {
        return;
    };
    if frames.is_null() {
        return;
    }
    let samples = frame_count.saturating_mul(receiver.channels);
    // SAFETY: the caller says that `frames` points to that many samples,
    // which may be written.
    let frames = unsafe { std::slice::from_raw_parts_mut(frames, samples) };
    receiver.audio.cycle(frames, position, time);
}

/// Stops a receiver and frees it.
///
/// # Safety
///
/// `receiver` is null or came from `unisono_receiver_start` and was not
/// stopped before; it is not used after.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_stop(receiver: *mut Receiver) {
    if receiver.is_null() {
        return;
    }
    // SAFETY: the caller says that `receiver` came from `Box::into_raw` in
    // `unisono_receiver_start` and is given up here.
    let mut receiver = unsafe { Box::from_raw(receiver) };
    receiver.stop.store(true, Ordering::Relaxed);
    if let Some(thread) = receiver.network.take() {
        let _ = thread.join();
    }
}
