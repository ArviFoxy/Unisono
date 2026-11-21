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
//! In each cycle PipeWire says, for the stream, a count of frames (its
//! position) and the time of the cycle on the monotonic clock, with the
//! delay to the device. The first frame that a playback stream is given now
//! leaves the device that delay after the time of the cycle. The frames that
//! a capture stream is given were captured during the cycle before, so the
//! first of them entered the device the delay and the length of the buffer
//! before it. With a sink that plays to nothing, the times that a capture of
//! what the sink plays reports agree with those of the playback to well
//! under a microsecond (`tests/graph.rs`); what a device of hardware adds is
//! for the measurement on hardware to show. The time is converted to the
//! raw clock that unisono times everything by, through a [`Tracker`] of the
//! monotonic clock.
//!
//! Samples are 32-bit floats, interleaved, at the rate and with the number
//! of channels that are asked for; PipeWire converts what its devices take
//! or give.

use std::fmt;
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
    thread: JoinHandle<()>,
}

impl Running {
    /// Stops the stream and waits for its thread to end.
    pub fn stop(self) {
        // A loop that ended already does not take the message.
        let _ = self.quit.send(());
        let _ = self.thread.join();
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

    /// One cycle of the graph.
    fn process(&mut self, stream: &pw::stream::Stream) {
        let Ok(time) = stream.time() else {
            return;
        };
        let Some(mut buffer) = stream.dequeue_buffer() else {
            return;
        };
        // The frames that this cycle asks a playback stream for; a buffer
        // can hold many cycles.
        let requested = usize::try_from(buffer.requested()).unwrap_or(usize::MAX);
        let rate = time.rate();
        // The delay in nanoseconds: ticks of `num / denom` seconds each.
        let delay = if rate.denom == 0 {
            0
        } else {
            let nanoseconds = i128::from(time.delay()) * i128::from(rate.num) * 1_000_000_000
                / i128::from(rate.denom);
            i64::try_from(nanoseconds).unwrap_or(0)
        };
        let now = self.raw(time.now());
        let position = time.ticks();
        let channels = self.channels;
        let Some(data) = buffer.datas_mut().first_mut() else {
            return;
        };
        let stride = channels * 4;
        match &mut self.side {
            Side::Playback(playback) => {
                let Some(bytes) = data.data() else {
                    return;
                };
                let mut frames =
                    (bytes.len() / stride.max(1)).min(self.samples.len() / channels.max(1));
                if requested > 0 {
                    frames = frames.min(requested);
                }
                let samples = &mut self.samples[..frames * channels];
                playback.cycle(samples, position, now.saturating_add(delay));
                for (place, sample) in bytes.as_chunks_mut::<4>().0.iter_mut().zip(samples.iter()) {
                    *place = sample.to_le_bytes();
                }
                let chunk = data.chunk_mut();
                *chunk.offset_mut() = 0;
                *chunk.stride_mut() = i32::try_from(stride).unwrap_or(0);
                *chunk.size_mut() = u32::try_from(frames * stride).unwrap_or(0);
            }
            Side::Capture(capture) => {
                let (offset, size) = (data.chunk().offset() as usize, data.chunk().size() as usize);
                let Some(bytes) = data.data() else {
                    return;
                };
                let Some(bytes) = bytes.get(offset..offset.saturating_add(size)) else {
                    return;
                };
                let frames =
                    (bytes.len() / stride.max(1)).min(self.samples.len() / channels.max(1));
                let samples = &mut self.samples[..frames * channels];
                for (sample, place) in samples.iter_mut().zip(bytes.as_chunks::<4>().0) {
                    *sample = f32::from_le_bytes(*place);
                }
                // The frames that a cycle hands over were captured during
                // the cycle before: the first of them entered the device the
                // length of the buffer before the time of this cycle, and the
                // delay before that.
                let length =
                    i64::try_from((frames as u128) * 1_000_000_000 / u128::from(self.rate.max(1)))
                        .unwrap_or(0);
                let first = now.saturating_sub(delay).saturating_sub(length);
                capture.cycle(samples, position, first);
            }
        }
    }
}

fn run<P, C>(side: Side<P, C>, settings: Settings) -> Result<Running, Error>
where
    P: Playback + Send + 'static,
    C: Capture + Send + 'static,
{
    let (made, outcome) = std::sync::mpsc::channel::<Result<pw::channel::Sender<()>, Error>>();
    let thread = std::thread::Builder::new()
        .name(format!("pipewire-{}", settings.name))
        .stack_size(512 * 1024)
        .spawn(move || {
            pw::init();
            let result = serve(side, &settings, &made);
            if let Err(error) = result {
                let _ = made.send(Err(error));
            }
        })
        .map_err(|error| Error(format!("starting the thread of the stream: {error}")))?;
    match outcome.recv() {
        Ok(Ok(quit)) => Ok(Running { quit, thread }),
        Ok(Err(error)) => {
            let _ = thread.join();
            Err(error)
        }
        Err(_) => Err(Error("the thread of the stream ended".into())),
    }
}

/// Makes the stream and runs PipeWire's loop until it is told to quit.
fn serve<P, C>(
    side: Side<P, C>,
    settings: &Settings,
    made: &std::sync::mpsc::Sender<Result<pw::channel::Sender<()>, Error>>,
) -> Result<(), Error>
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
    };
    let _listener = stream
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
    Ok(())
}
