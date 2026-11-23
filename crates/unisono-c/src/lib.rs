// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! C FFI bindings for `unisono` (public ABI documented in `include/unisono.h`).
//!
//! Wraps the capture end of [`unisono_runtime::send`] and the audio end of
//! [`unisono_runtime::receive`], each paired with a managed [`NetworkThread`]
//! running under [`unisono_runtime::syscalls`] seccomp restrictions on Linux
//! and returning its socket on shutdown so `close(fd)` runs outside the filter.

use std::ffi::{CStr, c_char, c_int};
use std::net::SocketAddr;
use std::panic::{AssertUnwindSafe, catch_unwind};

use unisono_core::kalman::NoisePrior;
use unisono_core::packet::Format;
use unisono_core::player::{ModalRegulation, Regulation};
use unisono_core::sender::Settings as StreamSettings;
use unisono_core::sync::{MAX_DIRECT_PEERS, SyncSettings, WEIGHT_UNITY_Q16};
use unisono_dsp::Parameters;
use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::clock;
use unisono_runtime::level::{Choice, Weights};
use unisono_runtime::network_thread::NetworkThread;
use unisono_runtime::pump::{ReceiverPlayback, Settings as PlaybackSettings};
use unisono_runtime::receive::{
    self, Intake, NetConfig, PeerConfig, ReceiverAudio, ReceiverNetwork, Reporting, Sizes, SyncMode,
};
use unisono_runtime::send::{self, CaptureEnd, SenderNetwork, Settings as SenderSettings};
use unisono_runtime::socket::{self, Socket};

/// The receiver's audio end: room for 16,384 frames, 64 samples of the
/// sender's clock, the arrivals of 8 packets, and 64 reports of its device.
type Audio = ReceiverAudio<256, 64, 8, 64>;

/// Maximum number of receivers accepted by one sender.
const MAX_RECEIVERS: usize = 4_096;

/// Maximum sample rate accepted through the C API, bounding the level
/// chooser's 2-minute stretch history allocation (`<= 50,000` stretches).
const MAX_RATE: u32 = 1_000_000;

/// Number of buffers in the capture-to-network ring.
const CAPTURE_BUFFERS: usize = 64;

/// Maximum total bytes allocated for the capture ring (`64 MiB`).
const MAX_CAPTURE_RING_BYTES: usize = 64 * 1024 * 1024;

/// Poll timeout in milliseconds for each network turn.
const NETWORK_TURN_MS: i32 = 2;

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
    network: Option<NetworkThread<SenderNetwork>>,
}

/// Receiver sync mode constants matching `include/unisono.h`.
const SYNC_PEER: u8 = 0;
const SYNC_HULL: u8 = 1;

/// Modal gain preset constants matching `include/unisono.h`.
const MODE_LIPSYNC: u8 = 0;
const MODE_LOW_LATENCY: u8 = 1;

/// Oscillator noise prior constants matching `include/unisono.h`.
const CLOCK_CONSUMER: u8 = 0;
const CLOCK_TCXO: u8 = 1;
const CLOCK_WANDERING: u8 = 2;

/// One direct peer entry; `unisono_peer` in the header.
#[repr(C)]
pub struct PeerEntry {
    identity: u64,
    address: *const c_char,
    weight_q16: u32,
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
    sync_mode: u8,
    mode: u8,
    clock_prior: u8,
    sender_clock_prior: u8,
    star_gain_q16: u32,
    common_gain_q16: u32,
    diff_gain_q16: u32,
    sender_weight_q16: u32,
    peers: *const PeerEntry,
    peer_count: usize,
}

/// A receiver that runs; `unisono_receiver` in the header.
pub struct Receiver {
    audio: Audio,
    channels: usize,
    port: u16,
    network: Option<NetworkThread<ReceiverNetwork>>,
}

/// The host's clock that no one adjusts, in nanoseconds.
#[unsafe(no_mangle)]
pub extern "C" fn unisono_clock() -> i64 {
    catch_unwind(clock::raw).unwrap_or(0)
}

/// Writes `reason` to the `size` bytes at `error`, cut on a UTF-8 character
/// boundary to fit, with the zero that ends it.
///
/// # Safety
///
/// `error` is null or points to `size` bytes that may be written.
unsafe fn explain(error: *mut c_char, size: usize, reason: &str) {
    if error.is_null() || size == 0 {
        return;
    }
    let length = reason.floor_char_boundary(size - 1);
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

/// Computes the sample count for `frame_count` frames of `channels` samples,
/// ensuring both sample count and byte size stay within Rust slice limits.
fn checked_sample_count(frame_count: usize, channels: usize) -> Option<usize> {
    if frame_count == 0 {
        return None;
    }
    let samples = frame_count.checked_mul(channels)?;
    let bytes = samples.checked_mul(size_of::<f32>())?;
    if bytes > isize::MAX.unsigned_abs() {
        return None;
    }
    Some(samples)
}

/// Fills `settings` with what the program takes when nothing is said.
///
/// # Safety
///
/// `settings` is null or points to a properly aligned `unisono_sender_settings`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_sender_defaults(settings: *mut SenderOptions) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if settings.is_null() || !settings.is_aligned() {
            return;
        }
        // SAFETY: the caller says that `settings` points to room for one,
        // and we checked it is non-null and aligned.
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
    }));
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
    if options.cycle_frames == 0 {
        return Err("the cycle frame count is not zero".into());
    }
    if options.rate > MAX_RATE {
        return Err(format!("sample rate exceeds maximum ({MAX_RATE} Hz)"));
    }
    if options.receivers.is_null() || !options.receivers.is_aligned() || options.receiver_count == 0
    {
        return Err("a sender needs a receiver".into());
    }
    if options.receiver_count > MAX_RECEIVERS {
        return Err(format!("at most {MAX_RECEIVERS} receivers are supported"));
    }
    let mut receivers = Vec::with_capacity(options.receiver_count.min(64));
    for place in 0..options.receiver_count {
        // SAFETY: the caller says that `receivers` points to
        // `receiver_count` texts, and `receiver_count <= MAX_RECEIVERS`.
        receivers.push(unsafe { address(*options.receivers.add(place)) }?);
    }
    let bind = if options.bind.is_null() {
        socket::unspecified_for(&receivers)
    } else {
        // SAFETY: the caller says that `bind` is a text.
        unsafe { address(options.bind) }?
    };
    let window = 2_400;
    // The needs of the last two minutes, and the costs that the program
    // takes when none are given.
    let stretches = usize::try_from(120 * u64::from(options.rate) / u64::from(window))
        .unwrap_or(usize::MAX)
        .max(1);
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
    let settings = SenderSettings {
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
    };
    settings.validate().map_err(|error| error.to_string())?;

    let channels = usize::from(options.channels);
    let cycle = usize::try_from(options.cycle_frames)
        .map_err(|_| "cycle frame count exceeds platform limits".to_string())?;
    let ring_bytes = CAPTURE_BUFFERS
        .checked_mul(cycle)
        .and_then(|n| n.checked_mul(channels))
        .and_then(|n| n.checked_mul(size_of::<f32>()));
    if ring_bytes.is_none_or(|bytes| bytes > MAX_CAPTURE_RING_BYTES) {
        return Err("capture cycle buffer size exceeds limit".into());
    }

    let socket = Socket::bind(bind).map_err(|error| format!("binding {bind}: {error}"))?;
    let (capture, sender_end) = send::link(CAPTURE_BUFFERS, cycle, channels);
    let network = SenderNetwork::new(socket, sender_end, settings);
    let thread = NetworkThread::spawn("unisono-network", network, NETWORK_TURN_MS)
        .map_err(|error| format!("starting the network thread: {error}"))?;
    Ok(Sender {
        capture,
        channels,
        network: Some(thread),
    })
}

/// Starts a sender; null on failure, with the reason at `error`.
///
/// # Safety
///
/// `settings` is null or points to a properly aligned
/// `unisono_sender_settings` whose pointers are as the header says, and
/// `error` is null or points to `error_size` bytes that may be written.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_sender_start(
    settings: *const SenderOptions,
    error: *mut c_char,
    error_size: usize,
) -> *mut Sender {
    catch_unwind(AssertUnwindSafe(|| {
        if settings.is_null() || !settings.is_aligned() {
            // SAFETY: `error` is as the caller says.
            unsafe { explain(error, error_size, "the settings are missing") };
            return std::ptr::null_mut();
        }
        // SAFETY: `settings` is non-null, aligned, and points to a `SenderOptions`.
        let options = unsafe { &*settings };
        // SAFETY: the pointers of the settings are as the caller says.
        match unsafe { start_sender(options) } {
            Ok(sender) => Box::into_raw(Box::new(sender)),
            Err(reason) => {
                // SAFETY: `error` is as the caller says.
                unsafe { explain(error, error_size, &reason) };
                std::ptr::null_mut()
            }
        }
    }))
    .unwrap_or_else(|_| {
        // SAFETY: `error` is as the caller says.
        unsafe { explain(error, error_size, "internal error") };
        std::ptr::null_mut()
    })
}

/// Hands over the frames of one cycle of the capture device.
///
/// # Safety
///
/// `sender` is null or came from `unisono_sender_start` and was not
/// stopped, and no other thread uses it; `frames` points to `frame_count`
/// initialized frames of the sender's channels.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_sender_capture(
    sender: *mut Sender,
    frames: *const f32,
    frame_count: usize,
    position: u64,
    time: i64,
) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if sender.is_null() || !sender.is_aligned() || frames.is_null() || !frames.is_aligned() {
            return;
        }
        // SAFETY: `sender` is non-null, aligned, and exclusively accessed.
        let sender = unsafe { &mut *sender };
        let Some(samples) = checked_sample_count(frame_count, sender.channels) else {
            return;
        };
        // SAFETY: `frames` is non-null, aligned, `samples * 4 <= isize::MAX`,
        // and the caller says it points to that many initialized samples.
        let frames = unsafe { std::slice::from_raw_parts(frames, samples) };
        sender.capture.cycle(frames, position, time);
    }));
}

/// Stops a sender and frees it.
///
/// # Safety
///
/// `sender` is null or came from `unisono_sender_start` and was not stopped
/// before; it is not used after.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_sender_stop(sender: *mut Sender) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if sender.is_null() || !sender.is_aligned() {
            return;
        }
        // SAFETY: the caller says that `sender` came from `Box::into_raw` in
        // `unisono_sender_start` and is given up here.
        let mut sender = unsafe { Box::from_raw(sender) };
        if let Some(network) = sender.network.take() {
            let _ = network.stop();
        }
    }));
}

/// Maps a C oscillator prior enum value to [`NoisePrior`].
fn decode_clock_prior(code: u8) -> Result<NoisePrior, String> {
    match code {
        CLOCK_CONSUMER => Ok(NoisePrior::CONSUMER_QUARTZ),
        CLOCK_TCXO => Ok(NoisePrior::TCXO),
        CLOCK_WANDERING => Ok(NoisePrior::WANDERING_QUARTZ),
        _ => Err(format!("unknown clock prior value `{code}`")),
    }
}

/// Fills `settings` with what the program takes when nothing is said.
///
/// # Safety
///
/// `settings` is null or points to a properly aligned `unisono_receiver_settings`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_defaults(settings: *mut ReceiverOptions) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if settings.is_null() || !settings.is_aligned() {
            return;
        }
        // SAFETY: the caller says that `settings` points to room for one,
        // and we checked it is non-null and aligned.
        unsafe {
            settings.write(ReceiverOptions {
                listen: std::ptr::null(),
                stream: 1,
                identity: 1,
                rate: 48_000,
                channels: 2,
                sync_mode: SYNC_PEER,
                mode: MODE_LIPSYNC,
                clock_prior: CLOCK_CONSUMER,
                sender_clock_prior: CLOCK_CONSUMER,
                star_gain_q16: 0,
                common_gain_q16: 0,
                diff_gain_q16: 0,
                sender_weight_q16: 0,
                peers: std::ptr::null(),
                peer_count: 0,
            });
        }
    }));
}

/// The receiver that `options` describe, started.
/// Builds modal regulation and network sync configuration from C receiver options.
///
/// # Safety
///
/// `options.peers` is either unused (`peer_count == 0`) or points to
/// `options.peer_count` valid [`Peer`] entries whose `address` strings are
/// valid NUL-terminated UTF-8 or null.
unsafe fn build_receiver_sync(
    options: &ReceiverOptions,
    datagram: usize,
    jump: u32,
) -> Result<(Option<ModalRegulation>, NetConfig), String> {
    let sync_mode = match options.sync_mode {
        SYNC_PEER => SyncMode::Peer,
        SYNC_HULL => SyncMode::Hull,
        code => return Err(format!("unknown sync mode `{code}`")),
    };
    match sync_mode {
        SyncMode::Hull => {
            if options.peer_count > 0 {
                return Err("peers cannot be configured in hull sync mode".into());
            }
            Ok((None, NetConfig::hull(options.stream, datagram)))
        }
        SyncMode::Peer => {
            if options.peer_count > MAX_DIRECT_PEERS {
                return Err(format!("at most {MAX_DIRECT_PEERS} peers are supported"));
            }
            let base_modal = match options.mode {
                MODE_LIPSYNC => ModalRegulation::lipsync(1_000_000, jump),
                MODE_LOW_LATENCY => ModalRegulation::low_latency(1_000_000, jump),
                code => return Err(format!("unknown modal preset `{code}`")),
            };
            let modal = ModalRegulation {
                star_gain: if options.star_gain_q16 == 0 {
                    base_modal.star_gain
                } else {
                    options.star_gain_q16
                },
                common_gain: if options.common_gain_q16 == 0 {
                    base_modal.common_gain
                } else {
                    options.common_gain_q16
                },
                diff_gain: if options.diff_gain_q16 == 0 {
                    base_modal.diff_gain
                } else {
                    options.diff_gain_q16
                },
                limit: base_modal.limit,
                jump,
            };
            let mut sync_settings = SyncSettings::standard(options.stream, options.identity);
            sync_settings.local_prior = decode_clock_prior(options.clock_prior)?;
            sync_settings.sender_prior = decode_clock_prior(options.sender_clock_prior)?;
            let mut peers = Vec::with_capacity(options.peer_count);
            if options.peer_count > 0 {
                if options.peers.is_null() || !options.peers.is_aligned() {
                    return Err("peer array pointer is null or misaligned".into());
                }
                for idx in 0..options.peer_count {
                    // SAFETY: `options.peers` is non-null, aligned, and points
                    // to `options.peer_count <= MAX_DIRECT_PEERS` entries.
                    let entry = unsafe { &*options.peers.add(idx) };
                    // SAFETY: `entry.address` is null or a NUL-terminated string.
                    let addr = unsafe { address(entry.address) }?;
                    peers.push(PeerConfig {
                        identity: entry.identity,
                        address: addr,
                        weight_q16: if entry.weight_q16 == 0 {
                            WEIGHT_UNITY_Q16
                        } else {
                            entry.weight_q16
                        },
                    });
                }
            }
            let net_cfg = NetConfig {
                stream: options.stream,
                sync_mode: SyncMode::Peer,
                sync_settings,
                sender_weight_q16: if options.sender_weight_q16 == 0 {
                    WEIGHT_UNITY_Q16
                } else {
                    options.sender_weight_q16
                },
                peers,
                datagram,
            };
            net_cfg.validate().map_err(|error| error.to_string())?;
            Ok((Some(modal), net_cfg))
        }
    }
}

///
/// # Safety
///
/// The pointers of `options` are null or point to what the header says.
unsafe fn start_receiver(options: &ReceiverOptions) -> Result<Receiver, String> {
    if options.rate > MAX_RATE {
        return Err(format!("sample rate exceeds maximum ({MAX_RATE} Hz)"));
    }
    // SAFETY: the caller says that `listen` is null or a text.
    let listen = unsafe { address(options.listen) }?;
    let sizes = Sizes {
        buffers: 64,
        datagram: send::MAX_DATAGRAM,
        messages: 64,
    };
    let jump = (options.rate / 200).max(1);
    // SAFETY: the caller guarantees `options` pointers follow the header contract.
    let (modal_regulation, net_config) =
        unsafe { build_receiver_sync(options, sizes.datagram, jump) }?;
    let playback_settings = PlaybackSettings {
        stream: options.stream,
        rate: options.rate,
        channels: options.channels,
        identity: options.identity,
        silence: 1_000_000_000,
        slope_limit: 200_000,
        regulation: Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump,
        },
        modal_regulation,
        concealment: Parameters::for_rate(options.rate),
        block: 256,
        device_range: 10_000_000,
    };
    playback_settings
        .validate()
        .map_err(|error| error.to_string())?;

    let socket = Socket::bind(listen).map_err(|error| format!("binding {listen}: {error}"))?;
    let port = socket
        .address()
        .map_err(|error| format!("the address of the socket: {error}"))?
        .port();
    let playback = ReceiverPlayback::new(&playback_settings);
    let (network_end, audio_end) = receive::link(sizes);
    let network = ReceiverNetwork::with_config(socket, network_end, &net_config);
    let audio = Audio::new(
        playback,
        audio_end,
        Intake {
            items: 16,
            reports: Some(Reporting::USUAL),
        },
    );
    let thread = NetworkThread::spawn("unisono-network", network, NETWORK_TURN_MS)
        .map_err(|error| format!("starting the network thread: {error}"))?;
    Ok(Receiver {
        audio,
        channels: usize::from(options.channels),
        port,
        network: Some(thread),
    })
}

/// Starts a receiver; null on failure, with the reason at `error`.
///
/// # Safety
///
/// `settings` is null or points to a properly aligned
/// `unisono_receiver_settings` whose pointer is as the header says, and
/// `error` is null or points to `error_size` bytes that may be written.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_start(
    settings: *const ReceiverOptions,
    error: *mut c_char,
    error_size: usize,
) -> *mut Receiver {
    catch_unwind(AssertUnwindSafe(|| {
        if settings.is_null() || !settings.is_aligned() {
            // SAFETY: `error` is as the caller says.
            unsafe { explain(error, error_size, "the settings are missing") };
            return std::ptr::null_mut();
        }
        // SAFETY: `settings` is non-null, aligned, and points to `ReceiverOptions`.
        let options = unsafe { &*settings };
        // SAFETY: the pointer of the settings is as the caller says.
        match unsafe { start_receiver(options) } {
            Ok(receiver) => Box::into_raw(Box::new(receiver)),
            Err(reason) => {
                // SAFETY: `error` is as the caller says.
                unsafe { explain(error, error_size, &reason) };
                std::ptr::null_mut()
            }
        }
    }))
    .unwrap_or_else(|_| {
        // SAFETY: `error` is as the caller says.
        unsafe { explain(error, error_size, "internal error") };
        std::ptr::null_mut()
    })
}

/// The port that the receiver receives on.
///
/// # Safety
///
/// `receiver` is null or came from `unisono_receiver_start` and was not
/// stopped, and no other thread is concurrently calling `unisono_receiver_play`
/// or `unisono_receiver_stop` on it.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_port(receiver: *const Receiver) -> u16 {
    catch_unwind(AssertUnwindSafe(|| {
        if receiver.is_null() || !receiver.is_aligned() {
            return 0;
        }
        // SAFETY: `receiver` is non-null, aligned, and valid per caller contract.
        unsafe { (&*receiver).port }
    }))
    .unwrap_or(0)
}

/// Fills the frames of one cycle of the playback device.
///
/// # Safety
///
/// `receiver` is null or came from `unisono_receiver_start` and was not
/// stopped, and no other thread uses it; `frames` points to `frame_count`
/// writable (not necessarily initialized) frames of the receiver's channels.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_play(
    receiver: *mut Receiver,
    frames: *mut f32,
    frame_count: usize,
    position: u64,
    time: i64,
) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if receiver.is_null() || !receiver.is_aligned() || frames.is_null() || !frames.is_aligned()
        {
            return;
        }
        // SAFETY: `receiver` is non-null, aligned, and exclusively accessed.
        let receiver = unsafe { &mut *receiver };
        let Some(samples) = checked_sample_count(frame_count, receiver.channels) else {
            return;
        };
        // SAFETY: C callers routinely pass uninitialized stack or `malloc`
        // buffers to output functions. Zero-initializing with `write_bytes`
        // establishes valid `f32` values before constructing `&mut [f32]`.
        let frames = unsafe {
            std::ptr::write_bytes(frames, 0, samples);
            std::slice::from_raw_parts_mut(frames, samples)
        };
        receiver.audio.cycle(frames, position, time);
    }));
}

/// Stops a receiver and frees it.
///
/// # Safety
///
/// `receiver` is null or came from `unisono_receiver_start` and was not
/// stopped before; it is not used after.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unisono_receiver_stop(receiver: *mut Receiver) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if receiver.is_null() || !receiver.is_aligned() {
            return;
        }
        // SAFETY: the caller says that `receiver` came from `Box::into_raw` in
        // `unisono_receiver_start` and is given up here.
        let mut receiver = unsafe { Box::from_raw(receiver) };
        if let Some(network) = receiver.network.take() {
            let _ = network.stop();
        }
    }));
}

#[cfg(test)]
mod tests {
    use std::ffi::{CStr, CString, c_char};
    use std::mem::MaybeUninit;
    use std::net::UdpSocket;

    use super::{
        CLOCK_TCXO, MODE_LOW_LATENCY, PeerEntry, ReceiverOptions, SYNC_HULL, SYNC_PEER,
        SenderOptions, explain, unisono_clock, unisono_receiver_defaults, unisono_receiver_play,
        unisono_receiver_port, unisono_receiver_start, unisono_receiver_stop,
        unisono_sender_capture, unisono_sender_defaults, unisono_sender_start, unisono_sender_stop,
    };

    #[test]
    fn explain_truncates_on_utf8_char_boundary() {
        let mut buf = [0x55 as c_char; 5];
        // "aé" is 3 bytes (`a` = 1 byte, `é` = 2 bytes). With size = 3, only 2
        // content bytes fit; "aé" needs 3, so it must truncate to "a" (1 byte)
        // rather than slicing inside `é`! Wait: size = 3 => max_len = 2, and
        // `a` (1 byte) + half of `é` (1 byte) -> floor_char_boundary(2) = 1.
        // SAFETY: `buf` has 5 bytes.
        unsafe { explain(buf.as_mut_ptr(), 3, "aé!") };
        let text = unsafe { CStr::from_ptr(buf.as_ptr()) }
            .to_str()
            .expect("valid UTF-8");
        assert_eq!(text, "a");
    }

    #[test]
    fn receiver_low_rate_uninit_buffer_zero_frames_and_immediate_port_reuse() {
        let listen = CString::new("127.0.0.1:0").expect("cstr");
        let mut opts = MaybeUninit::<ReceiverOptions>::uninit();
        let mut err = [0 as c_char; 128];
        // SAFETY: valid pointers.
        unsafe {
            unisono_receiver_defaults(opts.as_mut_ptr());
            let mut opts = opts.assume_init();
            opts.listen = listen.as_ptr();
            opts.rate = 100; // < 200: previously produced `jump == 0` and panicked
            let rx = unisono_receiver_start(&raw const opts, err.as_mut_ptr(), err.len());
            assert!(
                !rx.is_null(),
                "start failed: {:?}",
                CStr::from_ptr(err.as_ptr())
            );
            let port = unisono_receiver_port(rx);
            assert_ne!(port, 0);

            // Zero frames is a safe no-op.
            let mut uninit_frames = [MaybeUninit::<f32>::uninit(); 16];
            unisono_receiver_play(rx, uninit_frames.as_mut_ptr().cast(), 0, 0, unisono_clock());
            // Uninitialized buffer is safely zero-initialized and played into.
            unisono_receiver_play(rx, uninit_frames.as_mut_ptr().cast(), 8, 0, unisono_clock());
            for slot in &uninit_frames {
                assert!(slot.assume_init().is_finite());
            }
            // Huge overflowing frame_count is safely ignored.
            unisono_receiver_play(
                rx,
                uninit_frames.as_mut_ptr().cast(),
                usize::MAX,
                8,
                unisono_clock(),
            );

            unisono_receiver_stop(rx);

            // Socket was closed outside seccomp, so immediate rebind must succeed.
            let rebound = UdpSocket::bind(("127.0.0.1", port))
                .expect("immediate rebind after unisono_receiver_stop");
            drop(rebound);
        }
    }

    #[test]
    fn sender_rejects_bad_settings_and_handles_ipv6_default_bind_and_zero_frames() {
        let mut opts = MaybeUninit::<SenderOptions>::uninit();
        let mut err = [0 as c_char; 128];
        let ipv6_target = CString::new("[::1]:9999").expect("cstr");
        let targets = [ipv6_target.as_ptr()];
        // SAFETY: valid pointers.
        unsafe {
            unisono_sender_defaults(opts.as_mut_ptr());
            let mut opts = opts.assume_init();
            opts.receivers = targets.as_ptr();
            opts.receiver_count = 1;
            opts.level = -1;
            assert!(unisono_sender_start(&raw const opts, err.as_mut_ptr(), err.len()).is_null());

            opts.level = 30_000_000;
            opts.rate = 2_000_000; // exceeds MAX_RATE
            assert!(unisono_sender_start(&raw const opts, err.as_mut_ptr(), err.len()).is_null());

            opts.rate = 100;
            opts.packet_frames = 1_500; // exceeds MAX_DATAGRAM (9000 bytes)
            assert!(unisono_sender_start(&raw const opts, err.as_mut_ptr(), err.len()).is_null());

            // Unconditionally test low-rate start plus zero/overflow capture on IPv4.
            let ipv4_target = CString::new("127.0.0.1:9999").expect("cstr");
            let v4_targets = [ipv4_target.as_ptr()];
            opts.receivers = v4_targets.as_ptr();
            opts.packet_frames = 10;
            let tx_v4 = unisono_sender_start(&raw const opts, err.as_mut_ptr(), err.len());
            assert!(
                !tx_v4.is_null(),
                "IPv4 start failed: {:?}",
                CStr::from_ptr(err.as_ptr())
            );
            let sample = [0.0f32; 4];
            unisono_sender_capture(tx_v4, sample.as_ptr(), 0, 0, unisono_clock());
            unisono_sender_capture(tx_v4, sample.as_ptr(), usize::MAX, 0, unisono_clock());
            unisono_sender_stop(tx_v4);

            // When IPv6 is available on the host, NULL bind with an IPv6 target
            // must select `[::]:0` and succeed (never silently ignored).
            if UdpSocket::bind("[::1]:0").is_ok() {
                opts.receivers = targets.as_ptr();
                let tx_v6 = unisono_sender_start(&raw const opts, err.as_mut_ptr(), err.len());
                assert!(
                    !tx_v6.is_null(),
                    "IPv6 default-bind start failed: {:?}",
                    CStr::from_ptr(err.as_ptr())
                );
                unisono_sender_stop(tx_v6);
            }
        }
    }

    #[test]
    fn receiver_peer_sync_options_validate_and_start_cleanly() {
        let listen = CString::new("127.0.0.1:0").expect("cstr");
        let peer_addr = CString::new("127.0.0.1:50002").expect("cstr");
        let mut opts = MaybeUninit::<ReceiverOptions>::uninit();
        let mut err = [0 as c_char; 160];
        // SAFETY: valid pointers.
        unsafe {
            unisono_receiver_defaults(opts.as_mut_ptr());
            let mut opts = opts.assume_init();
            assert_eq!(opts.sync_mode, SYNC_PEER);
            opts.listen = listen.as_ptr();
            opts.identity = 1;
            opts.mode = MODE_LOW_LATENCY;
            opts.clock_prior = CLOCK_TCXO;
            opts.sender_clock_prior = CLOCK_TCXO;

            // Rejects peer_count > 0 with null peers pointer.
            opts.peer_count = 1;
            opts.peers = std::ptr::null();
            assert!(unisono_receiver_start(&raw const opts, err.as_mut_ptr(), err.len()).is_null());

            // Rejects peers in hull mode.
            let peer = PeerEntry {
                identity: 2,
                address: peer_addr.as_ptr(),
                weight_q16: 65_536,
            };
            opts.peers = &raw const peer;
            opts.sync_mode = SYNC_HULL;
            assert!(unisono_receiver_start(&raw const opts, err.as_mut_ptr(), err.len()).is_null());

            // Rejects unknown sync mode.
            opts.sync_mode = 99;
            assert!(unisono_receiver_start(&raw const opts, err.as_mut_ptr(), err.len()).is_null());

            // Starts cleanly in peer mode with one configured peer.
            opts.sync_mode = SYNC_PEER;
            let rx = unisono_receiver_start(&raw const opts, err.as_mut_ptr(), err.len());
            assert!(
                !rx.is_null(),
                "peer receiver start failed: {:?}",
                CStr::from_ptr(err.as_ptr())
            );
            unisono_receiver_stop(rx);
        }
    }
}
