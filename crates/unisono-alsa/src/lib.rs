// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! ALSA as an audio system for unisono.
//!
//! [`play`] opens an ALSA device and plays on it what a [`Playback`] gives,
//! and [`capture`] opens one and hands what it captures to a [`Capture`].
//! Each runs a thread of its own that waits for the device, cycle after
//! cycle, and asks the system to schedule it ahead of ordinary threads.
//! Nothing else of unisono knows ALSA: the program uses this crate only
//! when it is built with it.
//!
//! # Times
//!
//! Before each cycle the device is asked for its state: how many frames lie
//! between the program and the converter, and when that was so. A playback
//! device says how many frames are written and not yet played, so the first
//! frame that is written now leaves the device that many frames after the
//! time of the state. A capture device says how many frames are captured
//! and not yet read, so the first frame that is read now was captured that
//! many frames before the time of the state. The count of frames that goes
//! with a time is the number of frames written, or read, so far.
//!
//! The device is asked to give its times on the raw clock, which unisono
//! times everything by. One that gives them on the monotonic or system clock
//! has them converted through a typed [`Tracker`]; one that gives no time has
//! the raw clock read in its place.
//!
//! Samples are 32-bit floats, interleaved; a device that takes another
//! format is opened through ALSA's `plug` device, which converts.

use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, mpsc};
use std::thread::JoinHandle;

use alsa::pcm::{Access, Format, Frames, HwParams, PCM, State, TstampType};
use alsa::{Direction, ValueOr};
use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::clock::{self, Monotonic, MonotonicNs, System, SystemNs, Tracker};

/// How far a time of the device may be from the latest measurement of the
/// monotonic or system clock against the raw clock, in nanoseconds: 50 ms.
const LONGEST_AGE: i64 = 50_000_000;

/// After how long the clocks are measured again, in nanoseconds: 10 ms.
const REFRESH: i64 = 10_000_000;

/// For how long the thread waits for the device before it looks whether it
/// is to stop, in milliseconds.
const PATIENCE: u32 = 100;

/// Stack size of the audio thread, in bytes (512 KiB).
const STACK_SIZE: usize = 512 * 1024;

/// The priority that the thread asks for among the threads scheduled ahead
/// of ordinary ones (clamped to `RLIMIT_RTPRIO` when set).
const PRIORITY: libc::c_int = 70;

/// What a device is opened with.
#[derive(Clone, Debug)]
pub struct Settings {
    /// The name of the device, as ALSA knows it: `default`, `hw:0,0`,
    /// `plughw:1`.
    pub device: String,
    /// Frames per second.
    pub rate: u32,
    /// Samples in a frame.
    pub channels: u32,
    /// Frames in a cycle.
    pub cycle: u32,
    /// How many cycles the device holds.
    pub cycles: u32,
}

/// What went wrong when a device was opened.
#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

/// A device that is running.
pub struct Running {
    stop: Arc<AtomicBool>,
    realtime: bool,
    cycle: usize,
    thread: Option<JoinHandle<Result<(), Error>>>,
}

impl Running {
    /// Whether the system schedules the device's thread ahead of ordinary
    /// threads; it says no when the program lacks the privilege.
    #[must_use]
    pub fn realtime(&self) -> bool {
        self.realtime
    }

    /// Negotiated number of frames per cycle on the opened ALSA device.
    #[must_use]
    pub fn cycle(&self) -> usize {
        self.cycle
    }

    /// Whether the audio thread has exited (for example after the device was
    /// disconnected).
    #[must_use]
    pub fn is_finished(&self) -> bool {
        self.thread.as_ref().is_none_or(JoinHandle::is_finished)
    }

    /// Stops the device, waits for its thread to end, and returns any fatal
    /// device error that ended the audio loop early.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the ALSA device encountered an unrecoverable
    /// error (such as disconnection or I/O failure) or if the thread panicked.
    pub fn stop(mut self) -> Result<(), Error> {
        self.shutdown()
    }

    fn shutdown(&mut self) -> Result<(), Error> {
        self.stop.store(true, Ordering::Release);
        match self.thread.take() {
            Some(thread) => match thread.join() {
                Ok(result) => result,
                Err(_) => Err(Error("the ALSA audio thread panicked".into())),
            },
            None => Ok(()),
        }
    }
}

impl Drop for Running {
    fn drop(&mut self) {
        let _ = self.shutdown();
    }
}

/// Converts ALSA timestamps from the device's negotiated clock domain to the
/// host's raw monotonic clock.
enum StampClock {
    /// Device already stamps with `CLOCK_MONOTONIC_RAW`.
    Raw,
    /// Device stamps with `CLOCK_MONOTONIC`.
    Monotonic(Tracker<Monotonic>),
    /// Device stamps with `CLOCK_REALTIME` (`gettimeofday`).
    System(Tracker<System>),
}

impl StampClock {
    fn for_type(stamps: TstampType) -> StampClock {
        match stamps {
            TstampType::MonotonicRaw => StampClock::Raw,
            TstampType::Monotonic => {
                let mut tracker = Tracker::monotonic(LONGEST_AGE);
                tracker.refresh();
                StampClock::Monotonic(tracker)
            }
            TstampType::Gettimeofday => {
                let mut tracker = Tracker::system(LONGEST_AGE);
                tracker.refresh();
                StampClock::System(tracker)
            }
        }
    }

    fn convert(&mut self, stamped: i64, now: clock::RawNs) -> i64 {
        if stamped == 0 {
            return now.as_i64();
        }
        match self {
            StampClock::Raw => stamped,
            StampClock::Monotonic(tracker) => {
                tracker.refresh_if_older(now, REFRESH);
                tracker
                    .to_raw(MonotonicNs(stamped))
                    .map_or(now.as_i64(), |converted| converted.time.as_i64())
            }
            StampClock::System(tracker) => {
                tracker.refresh_if_older(now, REFRESH);
                tracker
                    .to_raw(SystemNs(stamped))
                    .map_or(now.as_i64(), |converted| converted.time.as_i64())
            }
        }
    }
}

/// Timing and geometry of an opened ALSA device, separated from `PCM` so
/// `pcm.io_f32()` can be held across the entire real-time loop without
/// borrowing conflict or `unsafe`.
struct Timing {
    /// Frames in a cycle, as the device took them.
    cycle: usize,
    channels: usize,
    rate: u32,
    /// Converts the device's timestamps to the raw clock.
    clock: StampClock,
}

impl Timing {
    /// `frames` frames of the device as nanoseconds.
    fn nanoseconds(&self, frames: i64) -> i64 {
        let wide = i128::from(frames) * 1_000_000_000 / i128::from(self.rate);
        i64::try_from(wide).unwrap_or(0)
    }
}

/// Unrecoverable cause that ended the ALSA real-time loop, formatted to an
/// [`Error`] only after leaving the loop so steady-state audio paths never
/// allocate.
enum FatalReason {
    Alsa(&'static str, alsa::Error),
    Disconnected,
}

impl FatalReason {
    fn into_error(self) -> Error {
        match self {
            FatalReason::Alsa(what, error) => Error(format!("ALSA {what}: {error}")),
            FatalReason::Disconnected => Error("ALSA device disconnected".into()),
        }
    }
}

/// Outcome of polling an ALSA device for the next cycle.
enum Due {
    /// A full cycle is ready, with `(raw_time_ns, delay_frames)`.
    Ready(i64, i64),
    /// Timed out or waiting for more frames; keep waiting.
    Wait,
    /// Recovered from an xrun or transient device error; keep waiting and
    /// advance frame positions across the gap on the next ready cycle.
    Recovered,
    /// Unrecoverable device error (e.g. `ENODEV`, `EIO`, `EBADFD`); exit the
    /// audio loop and report the cause.
    Fatal(FatalReason),
}

/// Opens the ALSA device named by `settings` for `direction`.
fn open(settings: &Settings, direction: Direction) -> Result<(PCM, Timing), Error> {
    if settings.device.contains('\0') {
        return Err(Error(
            "ALSA device name contains an interior NUL byte".into(),
        ));
    }
    if settings.rate == 0 || settings.channels == 0 || settings.cycle == 0 {
        return Err(Error(
            "ALSA rate, channels, and cycle frames must all be positive".into(),
        ));
    }
    let wrong = |what: &str, error: alsa::Error| {
        Error(format!(
            "{what} of the ALSA device `{}`: {error}",
            settings.device
        ))
    };
    let pcm =
        PCM::new(&settings.device, direction, false).map_err(|error| wrong("opening", error))?;
    let cycle = {
        let hardware = HwParams::any(&pcm).map_err(|error| wrong("the settings", error))?;
        hardware
            .set_access(Access::RWInterleaved)
            .and_then(|()| hardware.set_format(Format::float()))
            .and_then(|()| hardware.set_channels(settings.channels))
            .and_then(|()| hardware.set_rate(settings.rate, ValueOr::Nearest))
            .map_err(|error| wrong("the format, channels or rate", error))?;
        let cycle = hardware
            .set_period_size_near(Frames::from(settings.cycle.max(1)), ValueOr::Nearest)
            .map_err(|error| wrong("the cycle", error))?;
        hardware
            .set_buffer_size_near(cycle.saturating_mul(Frames::from(settings.cycles.max(2))))
            .map_err(|error| wrong("the buffer", error))?;
        pcm.hw_params(&hardware)
            .map_err(|error| wrong("the settings", error))?;
        cycle
    };
    let stamps = {
        let software = pcm
            .sw_params_current()
            .map_err(|error| wrong("the settings", error))?;
        software
            .set_avail_min(cycle)
            .and_then(|()| software.set_start_threshold(cycle))
            .and_then(|()| software.set_tstamp_mode(true))
            .map_err(|error| wrong("the settings", error))?;
        // The raw clock, where the device gives its times on it.
        let _ = software.set_tstamp_type(TstampType::MonotonicRaw);
        pcm.sw_params(&software)
            .map_err(|error| wrong("the settings", error))?;
        software.get_tstamp_type().unwrap_or(TstampType::Monotonic)
    };
    let cycle_frames = usize::try_from(cycle)
        .ok()
        .filter(|&n| n > 0)
        .ok_or_else(|| Error("ALSA negotiated a non-positive period size".into()))?;
    let channels = usize::try_from(settings.channels).unwrap_or(0);
    if cycle_frames.checked_mul(channels).is_none() {
        return Err(Error("ALSA cycle sample count overflow".into()));
    }
    Ok((
        pcm,
        Timing {
            cycle: cycle_frames,
            channels,
            rate: settings.rate.max(1),
            clock: StampClock::for_type(stamps),
        },
    ))
}

/// Recovers from a transient ALSA error (`EPIPE`, `ESTRPIPE`, `EINTR`),
/// restarting capture devices immediately if recovery left them `Prepared`.
/// Returns `Err` with the underlying ALSA error if recovery fails.
fn recover(pcm: &PCM, error: alsa::Error, direction: Direction) -> Result<(), alsa::Error> {
    pcm.try_recover(error, true)?;
    if direction == Direction::Capture && pcm.state() == State::Prepared {
        pcm.start()?;
    }
    Ok(())
}

/// Polls `pcm` until a full cycle is ready, returning its timestamp and delay
/// or reporting whether to keep waiting or exit on a fatal device error.
// The numbers of the system are narrower on machines of 32 bits.
#[allow(clippy::useless_conversion)]
fn due(pcm: &PCM, timing: &mut Timing, direction: Direction) -> Due {
    if direction == Direction::Capture
        && pcm.state() == State::Prepared
        && let Err(error) = pcm.start()
    {
        return Due::Fatal(FatalReason::Alsa("starting capture device", error));
    }
    match pcm.wait(Some(PATIENCE)) {
        Ok(true) => {}
        Ok(false) => return Due::Wait,
        Err(error) => {
            return match recover(pcm, error, direction) {
                Ok(()) => Due::Recovered,
                Err(error) => Due::Fatal(FatalReason::Alsa("waiting on device", error)),
            };
        }
    }
    let status = match pcm.status() {
        Ok(status) => status,
        Err(error) => {
            return match recover(pcm, error, direction) {
                Ok(()) => Due::Recovered,
                Err(error) => Due::Fatal(FatalReason::Alsa("reading device status", error)),
            };
        }
    };
    match status.get_state() {
        State::XRun => {
            if let Err(error) = pcm.prepare() {
                return Due::Fatal(FatalReason::Alsa("preparing device after xrun", error));
            }
            if direction == Direction::Capture
                && let Err(error) = pcm.start()
            {
                return Due::Fatal(FatalReason::Alsa("restarting capture after xrun", error));
            }
            return Due::Recovered;
        }
        State::Disconnected => return Due::Fatal(FatalReason::Disconnected),
        _ => {}
    }
    if usize::try_from(status.get_avail()).unwrap_or(0) < timing.cycle {
        return Due::Wait;
    }
    let stamp = status.get_htstamp();
    let stamped = i64::from(stamp.tv_sec)
        .saturating_mul(1_000_000_000)
        .saturating_add(i64::from(stamp.tv_nsec));
    let now = clock::raw_ns();
    let time = timing.clock.convert(stamped, now);
    Due::Ready(time, i64::from(status.get_delay()))
}

/// Asks the system to schedule the calling thread ahead of ordinary
/// threads, clamping the requested priority to `RLIMIT_RTPRIO` when set, and
/// says whether it succeeded.
fn ahead() -> bool {
    #[cfg(target_os = "linux")]
    {
        // SAFETY: pure range query for `SCHED_FIFO`.
        let min = unsafe { libc::sched_get_priority_min(libc::SCHED_FIFO) };
        // SAFETY: pure range query for `SCHED_FIFO`.
        let max = unsafe { libc::sched_get_priority_max(libc::SCHED_FIFO) };
        if min < 0 || max < 0 || min > max {
            return false;
        }
        let mut priority = PRIORITY.clamp(min, max);
        let mut limit = libc::rlimit {
            rlim_cur: 0,
            rlim_max: 0,
        };
        // SAFETY: `limit` is a valid writable `rlimit` struct.
        if unsafe { libc::getrlimit(libc::RLIMIT_RTPRIO, &raw mut limit) } == 0
            && limit.rlim_cur > 0
            && limit.rlim_cur != libc::RLIM_INFINITY
        {
            let cap = libc::c_int::try_from(limit.rlim_cur).unwrap_or(max);
            priority = priority.min(cap).max(min);
        }
        let wanted = libc::sched_param {
            sched_priority: priority,
        };
        // SAFETY: the call reads `wanted` and changes how this thread is
        // scheduled, nothing in memory.
        unsafe { libc::sched_setscheduler(0, libc::SCHED_FIFO, &raw const wanted) == 0 }
    }
    #[cfg(not(target_os = "linux"))]
    {
        false
    }
}

/// Which side of an ALSA stream the shared thread loop serves.
enum Side<P, C> {
    Playback(P),
    Capture(C),
}

struct NoPlayback;

impl Playback for NoPlayback {
    fn channels(&self) -> usize {
        0
    }

    fn cycle(&mut self, _: &mut [f32], _: u64, _: i64) {}
}

struct NoCapture;

impl Capture for NoCapture {
    fn channels(&self) -> usize {
        0
    }

    fn cycle(&mut self, _: &[f32], _: u64, _: i64) {}
}

/// Runs the ALSA real-time I/O loop after obtaining `io_f32` and setting
/// `SCHED_FIFO` once up front. Returns `Err` if an unrecoverable ALSA error
/// ended the loop early.
fn serve<P: Playback, C: Capture>(
    pcm: &PCM,
    timing: &mut Timing,
    side: &mut Side<P, C>,
    direction: Direction,
    samples: &mut [f32],
    stopping: &AtomicBool,
    ready: &mpsc::SyncSender<Result<bool, Error>>,
) -> Result<(), Error> {
    let io = match pcm.io_f32() {
        Ok(io) => io,
        Err(error) => {
            let _ = ready.send(Err(Error(format!("opening ALSA float I/O: {error}"))));
            return Ok(());
        }
    };
    let _ = ready.send(Ok(ahead()));
    let mut frames_done: u64 = 0;
    let mut last_ready: Option<(i64, u64)> = None;
    let mut xrun = false;
    let mut fatal_reason: Option<FatalReason> = None;
    while !stopping.load(Ordering::Acquire) {
        let (time, waiting) = match due(pcm, timing, direction) {
            Due::Ready(time, waiting) => (time, waiting),
            Due::Wait => continue,
            Due::Recovered => {
                xrun = true;
                continue;
            }
            Due::Fatal(reason) => {
                fatal_reason = Some(reason);
                break;
            }
        };
        if xrun {
            if let Some((prev_time, prev_frames)) = last_ready {
                let elapsed_ns = time.saturating_sub(prev_time);
                if elapsed_ns > 0 {
                    let elapsed_frames = u64::try_from(
                        i128::from(elapsed_ns) * i128::from(timing.rate) / 1_000_000_000,
                    )
                    .unwrap_or(0);
                    if elapsed_frames > prev_frames {
                        frames_done = frames_done.saturating_add(elapsed_frames - prev_frames);
                    }
                }
            }
            xrun = false;
        }
        match side {
            Side::Playback(playback) => {
                // The frame written now leaves after those that wait.
                let leaves = time.saturating_add(timing.nanoseconds(waiting));
                playback.cycle(samples, frames_done, leaves);
                let mut offset_frames = 0usize;
                while offset_frames < timing.cycle && !stopping.load(Ordering::Acquire) {
                    let slice = samples
                        .get(offset_frames * timing.channels..)
                        .unwrap_or(&[]);
                    match io.writei(slice) {
                        Ok(0) => break,
                        Ok(written) => {
                            offset_frames = offset_frames.saturating_add(written);
                            frames_done = frames_done.saturating_add(written as u64);
                        }
                        Err(error) => {
                            match recover(pcm, error, direction) {
                                Ok(()) => xrun = true,
                                Err(error) => {
                                    fatal_reason = Some(FatalReason::Alsa("writing audio", error));
                                }
                            }
                            break;
                        }
                    }
                }
                if fatal_reason.is_some() {
                    break;
                }
                if offset_frames > 0 {
                    last_ready = Some((time, offset_frames as u64));
                }
            }
            Side::Capture(capture) => {
                // The frame read now was captured before those that wait.
                let captured = time.saturating_sub(timing.nanoseconds(waiting));
                match io.readi(samples) {
                    Ok(0) => {}
                    Ok(read) => {
                        let count = read.saturating_mul(timing.channels);
                        capture.cycle(samples.get(..count).unwrap_or(&[]), frames_done, captured);
                        frames_done = frames_done.saturating_add(read as u64);
                        last_ready = Some((time, read as u64));
                    }
                    Err(error) => match recover(pcm, error, direction) {
                        Ok(()) => xrun = true,
                        Err(error) => {
                            fatal_reason = Some(FatalReason::Alsa("reading audio", error));
                            break;
                        }
                    },
                }
            }
        }
    }
    match fatal_reason {
        Some(reason) => Err(reason.into_error()),
        None => Ok(()),
    }
}

/// Shared launcher for ALSA playback and capture threads with a bounded stack,
/// synchronous `SCHED_FIFO` + `io_f32` startup handshake, and clean exit on
/// unrecoverable device errors.
fn run<P, C>(mut side: Side<P, C>, settings: &Settings) -> Result<Running, Error>
where
    P: Playback + Send + 'static,
    C: Capture + Send + 'static,
{
    let direction = match side {
        Side::Playback(_) => Direction::Playback,
        Side::Capture(_) => Direction::Capture,
    };
    let (pcm, mut timing) = open(settings, direction)?;
    if direction == Direction::Capture {
        pcm.start().map_err(|error| {
            Error(format!(
                "starting the ALSA device `{}`: {error}",
                settings.device
            ))
        })?;
    }
    let cycle = timing.cycle;
    let mut samples = vec![0.0f32; timing.cycle * timing.channels].into_boxed_slice();
    let stop = Arc::new(AtomicBool::new(false));
    let stopping = Arc::clone(&stop);
    let (ready_tx, ready_rx) = mpsc::sync_channel::<Result<bool, Error>>(1);
    let thread_name = match direction {
        Direction::Playback => "unisono-alsa-play",
        Direction::Capture => "unisono-alsa-capture",
    };
    let thread = std::thread::Builder::new()
        .name(thread_name.into())
        .stack_size(STACK_SIZE)
        .spawn(move || {
            serve(
                &pcm,
                &mut timing,
                &mut side,
                direction,
                &mut samples,
                &stopping,
                &ready_tx,
            )
        })
        .map_err(|error| Error(format!("starting the thread of the device: {error}")))?;

    match ready_rx.recv() {
        Ok(Ok(realtime)) => Ok(Running {
            stop,
            realtime,
            cycle,
            thread: Some(thread),
        }),
        Ok(Err(error)) => {
            let _ = thread.join();
            Err(error)
        }
        Err(_) => {
            let _ = thread.join();
            Err(Error("the ALSA audio thread exited during startup".into()))
        }
    }
}

/// Plays what `playback` gives in each cycle of the device.
///
/// # Errors
///
/// When the device cannot be opened as the settings say.
pub fn play<P: Playback + Send + 'static>(
    playback: P,
    settings: &Settings,
) -> Result<Running, Error> {
    run(Side::<P, NoCapture>::Playback(playback), settings)
}

/// Hands what the device captures in each cycle to `capture`.
///
/// # Errors
///
/// When the device cannot be opened as the settings say.
pub fn capture<C: Capture + Send + 'static>(
    capture: C,
    settings: &Settings,
) -> Result<Running, Error> {
    run(Side::<NoPlayback, C>::Capture(capture), settings)
}

#[cfg(test)]
mod tests {
    use alsa::Direction;

    use super::{Settings, open};

    #[test]
    fn interior_nul_device_name_is_rejected_without_panic() {
        let settings = Settings {
            device: "default\0bad".into(),
            rate: 48_000,
            channels: 2,
            cycle: 256,
            cycles: 4,
        };
        assert!(open(&settings, Direction::Playback).is_err());
    }

    #[test]
    fn zero_rate_channels_or_cycle_are_rejected() {
        let base = Settings {
            device: "default".into(),
            rate: 48_000,
            channels: 2,
            cycle: 256,
            cycles: 4,
        };
        assert!(
            open(
                &Settings {
                    rate: 0,
                    ..base.clone()
                },
                Direction::Playback
            )
            .is_err()
        );
        assert!(
            open(
                &Settings {
                    channels: 0,
                    ..base.clone()
                },
                Direction::Playback
            )
            .is_err()
        );
        assert!(open(&Settings { cycle: 0, ..base }, Direction::Playback).is_err());
    }
}
