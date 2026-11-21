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
//! times everything by. One that gives them on the monotonic clock has them
//! converted through a [`Tracker`]; one that gives no time has the raw
//! clock read in its place.
//!
//! How well a device of hardware keeps these numbers is for the measurement
//! on hardware to show. Against PipeWire's device for ALSA programs, played
//! into a sink and captured from it, the frames arrive in order and without
//! a break, and the times agree with those that PipeWire gives its own
//! streams within 21 microseconds (`tests/device.rs`).
//!
//! Samples are 32-bit floats, interleaved; a device that takes another
//! format is opened through ALSA's `plug` device, which converts.

use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::JoinHandle;

use alsa::pcm::{Access, Format, Frames, HwParams, PCM, State, TstampType};
use alsa::{Direction, ValueOr};
use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::clock::{self, Monotonic, MonotonicNs, System, SystemNs, Tracker};

/// How far a time of the device may be from the latest measurement of the
/// monotonic clock against the raw clock, in nanoseconds: 50 ms.
const LONGEST_AGE: i64 = 50_000_000;

/// After how long the clocks are measured again, in nanoseconds: 10 ms.
const REFRESH: i64 = 10_000_000;

/// For how long the thread waits for the device before it looks whether it
/// is to stop, in milliseconds.
const PATIENCE: u32 = 100;

/// The priority that the thread asks for among the threads scheduled ahead
/// of ordinary ones.
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
    realtime: Arc<AtomicBool>,
    thread: JoinHandle<()>,
}

impl Running {
    /// Whether the system schedules the device's thread ahead of ordinary
    /// threads; it says no when the program lacks the privilege.
    #[must_use]
    pub fn realtime(&self) -> bool {
        self.realtime.load(Ordering::Relaxed)
    }

    /// Stops the device and waits for its thread to end.
    pub fn stop(self) {
        self.stop.store(true, Ordering::Relaxed);
        let _ = self.thread.join();
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

/// A device that is open, and what its cycles are like.
struct Device {
    pcm: PCM,
    /// Frames in a cycle, as the device took them.
    cycle: usize,
    channels: usize,
    rate: u32,
    /// Converts the device's timestamps to the raw clock.
    clock: StampClock,
}

impl Device {
    /// Opens the device that `settings` name for `direction`.
    fn open(settings: &Settings, direction: Direction) -> Result<Device, Error> {
        let wrong = |what: &str, error: alsa::Error| {
            Error(format!(
                "{what} of the ALSA device `{}`: {error}",
                settings.device
            ))
        };
        let pcm = PCM::new(&settings.device, direction, false)
            .map_err(|error| wrong("opening", error))?;
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
        Ok(Device {
            pcm,
            cycle: usize::try_from(cycle).unwrap_or(0),
            channels: usize::try_from(settings.channels).unwrap_or(0),
            rate: settings.rate.max(1),
            clock: StampClock::for_type(stamps),
        })
    }

    /// The device's state before a cycle, once a cycle's frames can be
    /// written or read: the raw clock's time of the state, and the frames
    /// between the program and the converter then. `None` when no cycle is
    /// due yet, or the device had to be started again.
    // The numbers of the system are narrower on machines of 32 bits.
    #[allow(clippy::useless_conversion)]
    fn due(&mut self) -> Option<(i64, i64)> {
        match self.pcm.wait(Some(PATIENCE)) {
            Ok(true) => {}
            Ok(false) => return None,
            Err(error) => {
                let _ = self.pcm.try_recover(error, true);
                return None;
            }
        }
        let status = match self.pcm.status() {
            Ok(status) => status,
            Err(error) => {
                let _ = self.pcm.try_recover(error, true);
                return None;
            }
        };
        if status.get_state() == State::XRun {
            let _ = self.pcm.prepare();
            return None;
        }
        if usize::try_from(status.get_avail()).unwrap_or(0) < self.cycle {
            return None;
        }
        let stamp = status.get_htstamp();
        let stamped = i64::from(stamp.tv_sec)
            .saturating_mul(1_000_000_000)
            .saturating_add(i64::from(stamp.tv_nsec));
        let now = clock::raw_ns();
        let time = self.clock.convert(stamped, now);
        Some((time, i64::from(status.get_delay())))
    }

    /// `frames` frames of the device as nanoseconds.
    fn nanoseconds(&self, frames: i64) -> i64 {
        let wide = i128::from(frames) * 1_000_000_000 / i128::from(self.rate);
        i64::try_from(wide).unwrap_or(0)
    }
}

/// Asks the system to schedule the calling thread ahead of ordinary
/// threads, and says whether it does.
fn ahead() -> bool {
    #[cfg(target_os = "linux")]
    {
        let wanted = libc::sched_param {
            sched_priority: PRIORITY,
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

/// Plays what `playback` gives in each cycle of the device.
///
/// # Errors
///
/// When the device cannot be opened as the settings say.
pub fn play<P: Playback + Send + 'static>(
    mut playback: P,
    settings: &Settings,
) -> Result<Running, Error> {
    let mut device = Device::open(settings, Direction::Playback)?;
    let stop = Arc::new(AtomicBool::new(false));
    let realtime = Arc::new(AtomicBool::new(false));
    let (stopping, scheduled) = (Arc::clone(&stop), Arc::clone(&realtime));
    let mut samples = vec![0.0f32; device.cycle * device.channels].into_boxed_slice();
    let thread = std::thread::Builder::new()
        .name("unisono-alsa-play".into())
        .spawn(move || {
            scheduled.store(ahead(), Ordering::Relaxed);
            let mut written: u64 = 0;
            while !stopping.load(Ordering::Relaxed) {
                let Some((time, waiting)) = device.due() else {
                    continue;
                };
                // The frame written now leaves after those that wait.
                let leaves = time.saturating_add(device.nanoseconds(waiting));
                playback.cycle(&mut samples, written, leaves);
                let Ok(io) = device.pcm.io_f32() else {
                    return;
                };
                match io.writei(&samples) {
                    Ok(frames) => written = written.saturating_add(frames as u64),
                    Err(error) => {
                        let _ = device.pcm.try_recover(error, true);
                    }
                }
            }
        })
        .map_err(|error| Error(format!("starting the thread of the device: {error}")))?;
    Ok(Running {
        stop,
        realtime,
        thread,
    })
}

/// Hands what the device captures in each cycle to `capture`.
///
/// # Errors
///
/// When the device cannot be opened as the settings say.
pub fn capture<C: Capture + Send + 'static>(
    mut capture: C,
    settings: &Settings,
) -> Result<Running, Error> {
    let mut device = Device::open(settings, Direction::Capture)?;
    device.pcm.start().map_err(|error| {
        Error(format!(
            "starting the ALSA device `{}`: {error}",
            settings.device
        ))
    })?;
    let stop = Arc::new(AtomicBool::new(false));
    let realtime = Arc::new(AtomicBool::new(false));
    let (stopping, scheduled) = (Arc::clone(&stop), Arc::clone(&realtime));
    let mut samples = vec![0.0f32; device.cycle * device.channels].into_boxed_slice();
    let thread = std::thread::Builder::new()
        .name("unisono-alsa-capture".into())
        .spawn(move || {
            scheduled.store(ahead(), Ordering::Relaxed);
            let mut read: u64 = 0;
            while !stopping.load(Ordering::Relaxed) {
                let Some((time, waiting)) = device.due() else {
                    // A device that stopped is started again.
                    if device.pcm.state() == State::Prepared {
                        let _ = device.pcm.start();
                    }
                    continue;
                };
                // The frame read now was captured before those that wait.
                let captured = time.saturating_sub(device.nanoseconds(waiting));
                let Ok(io) = device.pcm.io_f32() else {
                    return;
                };
                match io.readi(&mut samples) {
                    Ok(frames) => {
                        let count = frames.saturating_mul(device.channels);
                        capture.cycle(samples.get(..count).unwrap_or(&[]), read, captured);
                        read = read.saturating_add(frames as u64);
                    }
                    Err(error) => {
                        let _ = device.pcm.try_recover(error, true);
                    }
                }
            }
        })
        .map_err(|error| Error(format!("starting the thread of the device: {error}")))?;
    Ok(Running {
        stop,
        realtime,
        thread,
    })
}
