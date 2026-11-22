// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! PipeWire as an audio system for unisono.
//!
//! [`play`] makes a PipeWire stream that plays what a [`Playback`] gives it,
//! and [`capture`] one that hands what it captures to a [`Capture`]. Each
//! runs PipeWire's loop on a thread of its own and is called by PipeWire on
//! the thread of the graph, once in each cycle. Nothing else of unisono knows
//! PipeWire: the program uses this crate only when it is built with it.
//!
//! # Times
//!
//! In each cycle PipeWire reports the graph time on the monotonic clock, the
//! path delay, any queued buffers and resampler buffering, and the graph tick
//! counter. Stream frame positions advance by the stream frames actually
//! delivered or captured, using tick deltas to detect xrun gaps even when the
//! graph rate differs from the stream rate. Times are converted to the raw
//! monotonic clock through a typed [`Tracker<Monotonic>`].
//!
//! Samples are 32-bit floats, interleaved, at the rate and with the number
//! of channels that are asked for; PipeWire converts what its devices take
//! or give.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;
use std::thread::JoinHandle;

use pipewire as pw;
use pw::properties::properties;
use pw::spa;
use pw::spa::pod::Pod;
use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::clock::{self, Monotonic, MonotonicNs, Tracker};

/// How far a time of PipeWire may be from the latest measurement of the
/// monotonic clock against the raw clock, in nanoseconds: 50 ms.
const LONGEST_AGE: i64 = 50_000_000;

/// After how long the clocks are measured again, in nanoseconds: 10 ms.
const REFRESH: i64 = 10_000_000;

/// Maximum queued capture buffers drained in a single PipeWire `process`
/// callback.
const MAX_CAPTURE_BUFFERS: usize = 16;

/// Stack size of the PipeWire mainloop thread, in bytes (512 KiB).
const STACK_SIZE: usize = 512 * 1024;

/// What a stream is set up with.
#[derive(Clone, Debug)]
pub struct Settings {
    /// The name of the stream's node.
    pub name: String,
    /// Frames per second.
    pub rate: u32,
    /// Samples in a frame.
    pub channels: u32,
    /// The node to connect to, by its name; `None` for the default.
    pub target: Option<String>,
    /// For a capture stream whose target is a sink: whether to capture what
    /// the sink plays.
    pub monitor: bool,
    /// The most frames that a cycle can have.
    pub largest_cycle: usize,
    /// The number of frames in a cycle that the stream asks the graph for;
    /// the graph runs at the smallest that any of its streams asks for.
    pub cycle: u32,
}

impl Settings {
    fn validate(&self) -> Result<(), Error> {
        if self.name.contains('\0') {
            return Err(Error(
                "PipeWire stream name contains an interior NUL byte".into(),
            ));
        }
        if self
            .target
            .as_deref()
            .is_some_and(|target| target.contains('\0'))
        {
            return Err(Error(
                "PipeWire target name contains an interior NUL byte".into(),
            ));
        }
        if self.rate == 0 || self.channels == 0 || self.cycle == 0 || self.largest_cycle == 0 {
            return Err(Error(
                "PipeWire rate, channels, cycle, and largest_cycle must all be positive".into(),
            ));
        }
        let channels = usize::try_from(self.channels)
            .map_err(|_| Error("PipeWire channel count out of range".into()))?;
        if self
            .largest_cycle
            .checked_mul(channels)
            .and_then(|s| s.checked_mul(4))
            .is_none()
        {
            return Err(Error("PipeWire sample buffer size overflow".into()));
        }
        Ok(())
    }
}

/// What went wrong when a stream was made.
#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

/// A stream that runs, until it is stopped.
pub struct Running {
    quit: pw::channel::Sender<()>,
    thread: Option<JoinHandle<Result<(), Error>>>,
}

impl Running {
    /// Whether the PipeWire mainloop thread has exited (for example after a
    /// fatal stream error).
    #[must_use]
    pub fn is_finished(&self) -> bool {
        self.thread.as_ref().is_none_or(JoinHandle::is_finished)
    }

    /// Stops the stream, waits for its thread to end, and returns any fatal
    /// stream error that ended the mainloop early.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the PipeWire stream entered an error state or
    /// if its thread panicked.
    pub fn stop(mut self) -> Result<(), Error> {
        self.shutdown()
    }

    fn shutdown(&mut self) -> Result<(), Error> {
        // A loop that ended already does not take the message.
        let _ = self.quit.send(());
        match self.thread.take() {
            Some(thread) => match thread.join() {
                Ok(result) => result,
                Err(_) => Err(Error("the PipeWire stream thread panicked".into())),
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

/// Plays what `playback` gives in each cycle of the graph.
///
/// # Errors
///
/// When PipeWire cannot be reached or the stream cannot be made.
pub fn play<P: Playback + Send + 'static>(
    playback: P,
    settings: Settings,
) -> Result<Running, Error> {
    run(Side::<P, NoCapture>::Playback(playback), settings)
}

/// Hands what is captured in each cycle of the graph to `capture`.
///
/// # Errors
///
/// When PipeWire cannot be reached or the stream cannot be made.
pub fn capture<C: Capture + Send + 'static>(
    capture: C,
    settings: Settings,
) -> Result<Running, Error> {
    run(Side::<NoPlayback, C>::Capture(capture), settings)
}

/// Which way a stream goes, with what it serves.
enum Side<P, C> {
    Playback(P),
    Capture(C),
}

/// What a capture stream has in place of a playback.
struct NoPlayback;

impl Playback for NoPlayback {
    fn channels(&self) -> usize {
        0
    }

    fn cycle(&mut self, _: &mut [f32], _: u64, _: i64) {}
}

/// What a playback stream has in place of a capture.
struct NoCapture;

impl Capture for NoCapture {
    fn channels(&self) -> usize {
        0
    }

    fn cycle(&mut self, _: &[f32], _: u64, _: i64) {}
}

/// What the stream's callback keeps.
struct State<P, C> {
    side: Side<P, C>,
    tracker: Tracker<Monotonic>,
    /// The samples of a cycle, made once.
    samples: Box<[f32]>,
    channels: usize,
    /// Frames per second.
    rate: u32,
    /// Cumulative stream-frame position across cycles.
    position: u64,
    /// Previous callback's graph tick count and total stream frames delivered
    /// since that tick, used to detect xrun gaps independent of graph rate.
    last_ticks: Option<(u64, u64)>,
}

impl<P: Playback, C: Capture> State<P, C> {
    /// The raw clock's time for a time of the monotonic clock.
    fn raw(&mut self, monotonic: i64) -> i64 {
        let now = clock::raw_ns();
        self.tracker.refresh_if_older(now, REFRESH);
        self.tracker
            .to_raw(MonotonicNs(monotonic))
            .map_or(now.as_i64(), |converted| converted.time.as_i64())
    }

    /// Converts `frames` at the stream sample rate into nanoseconds.
    fn frames_ns(&self, frames: u64) -> i64 {
        let wide = u128::from(frames) * 1_000_000_000 / u128::from(self.rate.max(1));
        i64::try_from(wide).unwrap_or(i64::MAX)
    }

    /// Computes total delay in nanoseconds from `time.delay()` (graph path
    /// delay) and `time.buffered()` (adapter/resampler-buffered stream frames).
    fn total_delay_ns(&self, time: &pw::stream::Time) -> i64 {
        let rate = time.rate();
        let path_delay = if rate.denom == 0 {
            0
        } else {
            let nanoseconds = i128::from(time.delay()) * i128::from(rate.num) * 1_000_000_000
                / i128::from(rate.denom);
            i64::try_from(nanoseconds).unwrap_or(0)
        };
        path_delay.saturating_add(self.frames_ns(time.buffered()))
    }

    /// Advances `self.position` across any xrun gap indicated by `time.ticks()`
    /// jumping further than the previous cycle's delivered stream frames.
    fn sync_position(&mut self, time: &pw::stream::Time) {
        let rate = time.rate();
        let ticks = time.ticks();
        if let Some((prev_ticks, prev_frames)) = self.last_ticks
            && rate.num > 0
            && rate.denom > 0
            && ticks > prev_ticks
        {
            let dticks = ticks - prev_ticks;
            let elapsed_frames =
                (u128::from(dticks) * u128::from(rate.num) * u128::from(self.rate)
                    + u128::from(rate.denom) / 2)
                    / u128::from(rate.denom);
            let prev = u128::from(prev_frames);
            // Allow +/-2 frames of rounding slack when graph rate != stream rate.
            if elapsed_frames > prev.saturating_add(2) {
                let gap = u64::try_from(elapsed_frames - prev).unwrap_or(u64::MAX);
                self.position = self.position.saturating_add(gap);
            }
        }
    }

    /// One cycle of the graph.
    fn process(&mut self, stream: &pw::stream::Stream) {
        let channels = self.channels;
        let stride = channels * 4;
        if stride == 0 {
            return;
        }
        match self.side {
            Side::Playback(_) => self.process_playback(stream, channels, stride),
            Side::Capture(_) => self.process_capture(stream, channels, stride),
        }
    }

    fn process_playback(&mut self, stream: &pw::stream::Stream, channels: usize, stride: usize) {
        let Some(mut buffer) = stream.dequeue_buffer() else {
            return;
        };
        let requested = usize::try_from(buffer.requested()).unwrap_or(usize::MAX);
        let Ok(time) = stream.time() else {
            clear_chunk(&mut buffer, stride);
            return;
        };
        let Some(data) = buffer.datas_mut().first_mut() else {
            return;
        };
        let Some(bytes) = data.data() else {
            let chunk = data.chunk_mut();
            *chunk.offset_mut() = 0;
            *chunk.stride_mut() = i32::try_from(stride).unwrap_or(0);
            *chunk.size_mut() = 0;
            return;
        };
        let mut frames = (bytes.len() / stride).min(self.samples.len() / channels);
        if requested > 0 {
            frames = frames.min(requested);
        }
        if frames == 0 {
            let chunk = data.chunk_mut();
            *chunk.offset_mut() = 0;
            *chunk.stride_mut() = i32::try_from(stride).unwrap_or(0);
            *chunk.size_mut() = 0;
            return;
        }
        self.sync_position(&time);
        let now = self.raw(time.now());
        let delay = self.total_delay_ns(&time);
        let position = self.position;
        if let Side::Playback(playback) = &mut self.side
            && let Some(samples) = self.samples.get_mut(..frames * channels)
        {
            playback.cycle(samples, position, now.saturating_add(delay));
            for (place, sample) in bytes.as_chunks_mut::<4>().0.iter_mut().zip(samples.iter()) {
                *place = sample.to_le_bytes();
            }
        }
        let chunk = data.chunk_mut();
        *chunk.offset_mut() = 0;
        *chunk.stride_mut() = i32::try_from(stride).unwrap_or(0);
        *chunk.size_mut() = u32::try_from(frames * stride).unwrap_or(0);
        self.position = self.position.saturating_add(frames as u64);
        self.last_ticks = Some((time.ticks(), frames as u64));
    }

    fn process_capture(&mut self, stream: &pw::stream::Stream, channels: usize, stride: usize) {
        let mut buffers: [Option<pw::buffer::Buffer<'_>>; MAX_CAPTURE_BUFFERS] =
            [const { None }; MAX_CAPTURE_BUFFERS];
        let mut frame_counts = [0usize; MAX_CAPTURE_BUFFERS];
        let mut count = 0usize;
        let mut total_frames = 0u64;
        let max_frames = self.samples.len() / channels;
        while count < MAX_CAPTURE_BUFFERS {
            let Some(mut buffer) = stream.dequeue_buffer() else {
                break;
            };
            let frames = buffer
                .datas_mut()
                .first_mut()
                .and_then(|data| {
                    let (offset, size) =
                        (data.chunk().offset() as usize, data.chunk().size() as usize);
                    let bytes = data.data()?.get(offset..offset.saturating_add(size))?;
                    Some((bytes.len() / stride).min(max_frames))
                })
                .unwrap_or(0);
            if frames == 0 {
                continue;
            }
            frame_counts[count] = frames;
            total_frames = total_frames.saturating_add(frames as u64);
            buffers[count] = Some(buffer);
            count += 1;
        }
        if count == 0 {
            return;
        }
        let Ok(time) = stream.time() else {
            // Advance past the dequeued frames so later callbacks do not stamp
            // subsequent audio as if these frames never existed, and keep
            // `last_ticks` aligned so `sync_position` will not double-count them.
            self.position = self.position.saturating_add(total_frames);
            if let Some((_, prev_frames)) = &mut self.last_ticks {
                *prev_frames = prev_frames.saturating_add(total_frames);
            }
            return;
        };
        self.sync_position(&time);
        let now = self.raw(time.now());
        let delay = self.total_delay_ns(&time);
        let mut remaining = total_frames;
        for idx in 0..count {
            let Some(mut buffer) = buffers[idx].take() else {
                continue;
            };
            let frames = frame_counts[idx];
            let first = now
                .saturating_sub(delay)
                .saturating_sub(self.frames_ns(remaining));
            remaining = remaining.saturating_sub(frames as u64);
            let position = self.position;
            if let Some(data) = buffer.datas_mut().first_mut() {
                let (offset, size) = (data.chunk().offset() as usize, data.chunk().size() as usize);
                if let Some(bytes) = data
                    .data()
                    .and_then(|raw| raw.get(offset..offset.saturating_add(size)))
                    && let Side::Capture(capture) = &mut self.side
                    && let Some(samples) = self.samples.get_mut(..frames * channels)
                {
                    for (sample, place) in samples.iter_mut().zip(bytes.as_chunks::<4>().0) {
                        *sample = f32::from_le_bytes(*place);
                    }
                    capture.cycle(samples, position, first);
                }
            }
            self.position = self.position.saturating_add(frames as u64);
        }
        self.last_ticks = Some((time.ticks(), total_frames));
    }
}

/// Resets chunk metadata on a dequeued playback buffer so returning early
/// never replays stale samples from a previous cycle.
fn clear_chunk(buffer: &mut pw::buffer::Buffer<'_>, stride: usize) {
    if let Some(data) = buffer.datas_mut().first_mut() {
        let chunk = data.chunk_mut();
        *chunk.offset_mut() = 0;
        *chunk.stride_mut() = i32::try_from(stride).unwrap_or(0);
        *chunk.size_mut() = 0;
    }
}

fn run<P, C>(side: Side<P, C>, settings: Settings) -> Result<Running, Error>
where
    P: Playback + Send + 'static,
    C: Capture + Send + 'static,
{
    settings.validate()?;
    let (made, outcome) = std::sync::mpsc::channel::<Result<pw::channel::Sender<()>, Error>>();
    let thread = std::thread::Builder::new()
        .name(format!("pipewire-{}", settings.name))
        .stack_size(STACK_SIZE)
        .spawn(move || {
            pw::init();
            serve(side, &settings, &made)
        })
        .map_err(|error| Error(format!("starting the thread of the stream: {error}")))?;
    match outcome.recv() {
        Ok(Ok(quit)) => Ok(Running {
            quit,
            thread: Some(thread),
        }),
        Ok(Err(error)) => {
            let _ = thread.join();
            Err(error)
        }
        Err(_) => {
            let _ = thread.join();
            Err(Error("the thread of the stream ended".into()))
        }
    }
}

/// Makes the stream and runs PipeWire's loop until it is told to quit or the
/// stream enters an error state. Startup errors are reported through `made`;
/// runtime stream errors after startup are returned to the joining caller.
fn serve<P, C>(
    side: Side<P, C>,
    settings: &Settings,
    made: &std::sync::mpsc::Sender<Result<pw::channel::Sender<()>, Error>>,
) -> Result<(), Error>
where
    P: Playback + Send + 'static,
    C: Capture + Send + 'static,
{
    match serve_inner(side, settings, made) {
        Ok(runtime_result) => runtime_result,
        Err(startup_error) => {
            let _ = made.send(Err(startup_error));
            Ok(())
        }
    }
}

fn serve_inner<P, C>(
    side: Side<P, C>,
    settings: &Settings,
    made: &std::sync::mpsc::Sender<Result<pw::channel::Sender<()>, Error>>,
) -> Result<Result<(), Error>, Error>
where
    P: Playback + Send + 'static,
    C: Capture + Send + 'static,
{
    let failed = |what: &'static str| move |error: pw::Error| Error(format!("{what}: {error}"));
    let mainloop = pw::main_loop::MainLoopRc::new(None).map_err(failed("making the loop"))?;
    let context =
        pw::context::ContextRc::new(&mainloop, None).map_err(failed("making the context"))?;
    let core = context
        .connect_rc(None)
        .map_err(failed("connecting to PipeWire"))?;
    let playing = matches!(side, Side::Playback(_));
    let mut properties = properties! {
        *pw::keys::MEDIA_TYPE => "Audio",
        *pw::keys::MEDIA_CATEGORY => if playing { "Playback" } else { "Capture" },
        *pw::keys::NODE_NAME => settings.name.as_str(),
        *pw::keys::NODE_LATENCY => format!("{}/{}", settings.cycle, settings.rate),
    };
    if let Some(target) = &settings.target {
        // `target.object`, which the crate names only for newer versions.
        properties.insert("target.object", target.as_str());
    }
    if settings.monitor {
        properties.insert("stream.capture.sink", "true");
    }
    let stream = pw::stream::StreamBox::new(&core, &settings.name, properties)
        .map_err(failed("making the stream"))?;
    let channels = usize::try_from(settings.channels).unwrap_or(0);
    let mut tracker = Tracker::monotonic(LONGEST_AGE);
    tracker.refresh();
    let state = State {
        side,
        tracker,
        samples: vec![0.0f32; settings.largest_cycle * channels].into_boxed_slice(),
        channels,
        rate: settings.rate,
        position: 0,
        last_ticks: None,
    };
    // Register `state_changed` on its own `()` listener so the main-loop
    // thread and the `RT_PROCESS` data thread never hold concurrent `&mut`
    // references to `State`.
    let stream_error: Rc<RefCell<Option<String>>> = Rc::new(RefCell::new(None));
    let error_cell = Rc::clone(&stream_error);
    let loop_on_error = mainloop.clone();
    let state_listener = stream
        .add_local_listener_with_user_data(())
        .state_changed(move |_stream, (), _old, new| {
            if let pw::stream::StreamState::Error(message) = new {
                *error_cell.borrow_mut() = Some(message.clone());
                loop_on_error.quit();
            }
        })
        .register()
        .map_err(failed("listening to the stream state"))?;
    let process_listener = stream
        .add_local_listener_with_user_data(state)
        .process(|stream, state| state.process(stream))
        .register()
        .map_err(failed("listening to the stream"))?;

    let mut info = spa::param::audio::AudioInfoRaw::new();
    info.set_format(spa::param::audio::AudioFormat::F32LE);
    info.set_rate(settings.rate);
    info.set_channels(settings.channels);
    let values: Vec<u8> = spa::pod::serialize::PodSerializer::serialize(
        std::io::Cursor::new(Vec::new()),
        &spa::pod::Value::Object(spa::pod::Object {
            type_: pw::spa::sys::SPA_TYPE_OBJECT_Format,
            id: pw::spa::sys::SPA_PARAM_EnumFormat,
            properties: info.into(),
        }),
    )
    .map_err(|error| Error(format!("describing the format: {error:?}")))?
    .0
    .into_inner();
    let pod = Pod::from_bytes(&values).ok_or_else(|| Error("describing the format".into()))?;
    let mut params = [pod];
    let direction = if playing {
        spa::utils::Direction::Output
    } else {
        spa::utils::Direction::Input
    };
    stream
        .connect(
            direction,
            None,
            pw::stream::StreamFlags::AUTOCONNECT
                | pw::stream::StreamFlags::MAP_BUFFERS
                | pw::stream::StreamFlags::RT_PROCESS,
            &mut params,
        )
        .map_err(failed("connecting the stream"))?;

    let (quit, told) = pw::channel::channel::<()>();
    let _attached = told.attach(mainloop.loop_(), {
        let mainloop = mainloop.clone();
        move |()| mainloop.quit()
    });
    let _ = made.send(Ok(quit));
    mainloop.run();
    // Disconnect the stream before dropping the listeners so the RT callback
    // cannot observe torn-down user data.
    let _ = stream.disconnect();
    drop(process_listener);
    drop(state_listener);
    let runtime_result = match stream_error.borrow_mut().take() {
        Some(message) => Err(Error(format!("PipeWire stream error: {message}"))),
        None => Ok(()),
    };
    Ok(runtime_result)
}

#[cfg(test)]
mod tests {
    use super::Settings;

    fn base_settings() -> Settings {
        Settings {
            name: "unisono-test".into(),
            rate: 48_000,
            channels: 2,
            target: None,
            monitor: false,
            largest_cycle: 8_192,
            cycle: 256,
        }
    }

    #[test]
    fn settings_validation_rejects_zero_and_interior_nul() {
        assert!(base_settings().validate().is_ok());
        assert!(
            Settings {
                rate: 0,
                ..base_settings()
            }
            .validate()
            .is_err()
        );
        assert!(
            Settings {
                channels: 0,
                ..base_settings()
            }
            .validate()
            .is_err()
        );
        assert!(
            Settings {
                cycle: 0,
                ..base_settings()
            }
            .validate()
            .is_err()
        );
        assert!(
            Settings {
                largest_cycle: 0,
                ..base_settings()
            }
            .validate()
            .is_err()
        );
        assert!(
            Settings {
                name: "bad\0name".into(),
                ..base_settings()
            }
            .validate()
            .is_err()
        );
        assert!(
            Settings {
                target: Some("bad\0target".into()),
                ..base_settings()
            }
            .validate()
            .is_err()
        );
    }
}
