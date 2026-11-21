// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `unisono receive`: a receiver that plays a stream on a playback device,
//! and can keep what it played in a file.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::net::SocketAddr;

use unisono_core::player::Regulation;
use unisono_dsp::Parameters;
use unisono_metrics::{Counter, FloatGauge};
use unisono_runtime::audio::Playback as AudioPlayback;
use unisono_runtime::network_thread::NetworkThread;
use unisono_runtime::pump::{ReceiverPlayback, Settings};
use unisono_runtime::receive::{
    self, Intake, NetworkCounts, ReceiverAudio, ReceiverNetwork, Reporting, Sizes,
};
use unisono_runtime::socket::Socket;
use unisono_runtime::software::{Device, Output};
use unisono_runtime::{clock, memory};

use crate::exported::{Metrics, Server, Tally};
use crate::options::{Options, Wrong};
use crate::{MAX_CYCLE, System, sleep_until, validate_drift};

/// The receiver: room for 16,384 frames, 64 samples of the sender's clock,
/// the arrivals of 8 packets, and 64 reports of its device.
type Playback = ReceiverPlayback<256, 64, 8, 64>;

/// The receiver's audio thread.
type Audio = ReceiverAudio<256, 64, 8, 64>;

/// The options of `unisono receive`.
pub(crate) const OPTIONS: &[&str] = &[
    "listen",
    "audio",
    "device",
    "stream",
    "identity",
    "rate",
    "channels",
    "cycle",
    "drift",
    "lead",
    "path",
    "report-period",
    "report-period-at-start",
    "seconds",
    "record",
    "metrics",
    "clock-offset",
    "clock-skew",
];

pub(crate) const HELP: &str = "\
unisono receive --listen ADDRESS [options]

Receives a stream and plays it on a software device.

  --listen ADDRESS    where to receive; with port 0 the system chooses the
                      port, and the first line written says which
  --stream N          the stream's number (1)
  --identity N        a number that tells this receiver from the others (1)
  --rate HZ           frames per second (48000)
  --channels N        samples in a frame (2)
  --audio software|pipewire|alsa
                      the device to play on: one of software, which plays to
                      nothing at its own rate, or PipeWire or ALSA, when the
                      program is built with them (software)
  --device NAME       with PipeWire, the node to play to; with ALSA, the
                      device (the default)
  --cycle FRAMES      frames in a cycle of the device (256)
  --drift PPB         how much faster the device runs, in parts per billion (0)
  --lead MS           how long before a cycle plays it is asked for (4)
  --path NS           the delay of the path from the sender, if it is known;
                      the receiver then does not measure it from the answers
                      to its reports
  --report-period-at-start MS
                      time between reports to the sender in the first five
                      seconds (50)
  --report-period MS  time between reports after that (200)
  --seconds S         stop after this long (0: run until stopped)
  --record FILE       keep what is played, with the device's times (needs
                      --seconds)
  --metrics ADDRESS   serve metrics in the Prometheus text format here
  --clock-offset NS, --clock-skew PPB
                      move this process's clock (for tests on one host)
";

/// What plays the frames.
enum Playing {
    /// The software output device, driven on the main thread.
    Software(Box<Counted>),
    /// A PipeWire stream.
    #[cfg(feature = "pipewire")]
    PipeWire(unisono_pipewire::Running),
    /// An ALSA device.
    #[cfg(feature = "alsa")]
    Alsa(unisono_alsa::Running),
}

impl Playing {
    /// Whether an active audio backend has already stopped.
    #[cfg_attr(not(any(feature = "pipewire", feature = "alsa")), allow(dead_code))]
    fn is_finished(&self) -> bool {
        match self {
            Playing::Software(_) => false,
            #[cfg(feature = "pipewire")]
            Playing::PipeWire(running) => running.is_finished(),
            #[cfg(feature = "alsa")]
            Playing::Alsa(running) => running.is_finished(),
        }
    }

    /// Stops the playback backend and returns any fatal audio-device error.
    #[cfg_attr(
        not(any(feature = "pipewire", feature = "alsa")),
        allow(clippy::unnecessary_wraps)
    )]
    fn finish(self) -> Result<(), Wrong> {
        match self {
            Playing::Software(_) => Ok(()),
            #[cfg(feature = "pipewire")]
            Playing::PipeWire(running) => running
                .stop()
                .map_err(|error| Wrong(format!("playing with PipeWire: {error}"))),
            #[cfg(feature = "alsa")]
            Playing::Alsa(running) => running
                .stop()
                .map_err(|error| Wrong(format!("playing with ALSA: {error}"))),
        }
    }
}

/// Validated configuration parsed from `unisono receive` CLI options.
struct Config {
    listen: SocketAddr,
    stream: u16,
    rate: u32,
    channels: u8,
    cycle: usize,
    drift: i32,
    lead: i64,
    report_at_start: i64,
    report_after: i64,
    seconds: i64,
    record: Option<String>,
    kept: usize,
    system: System,
}

impl Config {
    fn from_options(options: &Options) -> Result<Config, Wrong> {
        let listen: SocketAddr = options.need("listen")?;
        let stream: u16 = options.get("stream", 1)?;
        let rate: u32 = options.get("rate", 48_000)?;
        let channels: u8 = options.get("channels", 2)?;
        let cycle: usize = options.get("cycle", 256)?;
        let drift: i32 = options.get("drift", 0)?;
        let lead = options
            .get::<i64>("lead", 4)?
            .checked_mul(1_000_000)
            .filter(|ns| *ns >= 0)
            .ok_or_else(|| {
                Wrong("`--lead` must be a non-negative number of milliseconds".into())
            })?;
        let report_at_start = options
            .get::<i64>("report-period-at-start", 50)?
            .checked_mul(1_000_000)
            .filter(|ns| *ns > 0)
            .ok_or_else(|| {
                Wrong("`--report-period-at-start` must be a positive number of milliseconds".into())
            })?;
        let report_after = options
            .get::<i64>("report-period", 200)?
            .checked_mul(1_000_000)
            .filter(|ns| *ns > 0)
            .ok_or_else(|| {
                Wrong("`--report-period` must be a positive number of milliseconds".into())
            })?;
        let seconds: i64 = options.get("seconds", 0)?;
        let record: Option<String> = options.one("record")?;
        let system = System::from_options(options)?;
        if record.is_some() && system != System::Software {
            return Err(Wrong("`--record` needs the software device".into()));
        }
        if cycle == 0 || cycle > MAX_CYCLE {
            return Err(Wrong(format!("`--cycle` must be in 1..={MAX_CYCLE}")));
        }
        if seconds < 0 {
            return Err(Wrong("`--seconds` must not be negative".into()));
        }
        if record.is_some() && seconds == 0 {
            return Err(Wrong("`--record` needs `--seconds`".into()));
        }
        validate_drift(drift)?;
        let kept = if record.is_some() {
            let frames = usize::try_from(seconds)
                .ok()
                .and_then(|s| s.checked_mul(usize::try_from(rate).ok()?));
            let bytes = frames
                .and_then(|f| f.checked_mul(usize::from(channels)))
                .and_then(|samples| samples.checked_mul(size_of::<f32>()));
            if bytes.is_none_or(|b| b > isize::MAX.unsigned_abs()) {
                return Err(Wrong("`--record` size exceeds memory limits".into()));
            }
            frames.unwrap_or(0)
        } else {
            0
        };
        Ok(Config {
            listen,
            stream,
            rate,
            channels,
            cycle,
            drift,
            lead,
            report_at_start,
            report_after,
            seconds,
            record,
            kept,
            system,
        })
    }
}

/// Runs `unisono receive`.
pub(crate) fn run(options: &Options) -> Result<(), Wrong> {
    let config = Config::from_options(options)?;
    let playback = playback(options, config.stream, config.rate, config.channels)?;
    let (counters, _metrics_server) = Counters::served(options)?;

    let socket = Socket::bind(config.listen)
        .map_err(|error| Wrong(format!("binding {}: {error}", config.listen)))?;
    // With port 0 the system chooses the port: say which, before anything
    // else, so that whoever started the program can send to it.
    let listening = socket
        .address()
        .map_err(|error| Wrong(format!("the address of the socket: {error}")))?;
    println!("listening {listening}");

    let sizes = Sizes {
        buffers: 64,
        datagram: unisono_runtime::send::MAX_DATAGRAM,
        messages: 64,
    };
    let (network_end, audio_end) = receive::link(sizes);
    let network = ReceiverNetwork::new(socket, network_end, config.stream, sizes);
    // Reports carry what the frames needed, for the sender's choice of the
    // level, whether or not the delay of the path is measured from them.
    let reports = Some(Reporting {
        at_start: config.report_at_start,
        after: config.report_after,
        ..Reporting::USUAL
    });
    let audio: Audio = ReceiverAudio::new(playback, audio_end, Intake { items: 16, reports });
    let start = clock::raw();
    let device = Device {
        rate: config.rate,
        channels: usize::from(config.channels),
        cycle: config.cycle,
        drift: config.drift,
        start,
        lead: config.lead,
        hidden: 0,
    };
    let mut output = Output::new(device, config.kept);

    let networking = NetworkThread::spawn("unisono-network", network, 2)
        .map_err(|error| Wrong(format!("starting the network thread: {error}")))?;
    if !networking.restricted() {
        eprintln!("unisono: the network thread's system calls are not restricted");
    }

    let seen = Seen::of(&counters);
    let counted = Counted { audio, counters };
    let shape = Shape {
        rate: config.rate,
        channels: config.channels,
        cycle: config.cycle,
    };
    let mut playing = start_playback(config.system, counted, shape)?;

    // Lock memory only after both network and audio threads/buffers are up so
    // PipeWire/ALSA initialization is not constrained by `MCL_FUTURE`.
    if let Err(error) = memory::lock() {
        eprintln!("unisono: memory is not locked: {error}");
    }

    let end = (config.seconds > 0)
        .then(|| start.saturating_add(config.seconds.saturating_mul(1_000_000_000)));
    match &mut playing {
        Playing::Software(counted) => {
            while end.is_none_or(|end| clock::raw() < end)
                && !crate::interrupted()
                && !networking.is_finished()
            {
                output.run(clock::raw(), counted.as_mut());
                sleep_until(output.due());
            }
        }
        #[cfg(any(feature = "pipewire", feature = "alsa"))]
        _ => {
            while end.is_none_or(|end| clock::raw() < end)
                && !crate::interrupted()
                && !networking.is_finished()
                && !playing.is_finished()
            {
                std::thread::sleep(std::time::Duration::from_millis(20));
            }
        }
    }

    let audio_result = playing.finish();
    let stopped = networking
        .stop()
        .map_err(|_| Wrong("the network thread failed".into()))?;
    summarize(&stopped.network.counts(), &seen);
    if let Some(path) = config.record {
        write_record(&path, &output).map_err(|error| Wrong(format!("writing {path}: {error}")))?;
    }
    if let Some(error) = stopped.error {
        return Err(Wrong(format!("receiving: {error}")));
    }
    audio_result
}

/// What a device of the stream is like, which an audio system is told.
#[derive(Clone, Copy)]
#[cfg_attr(not(any(feature = "pipewire", feature = "alsa")), allow(dead_code))]
struct Shape {
    rate: u32,
    channels: u8,
    cycle: usize,
}

/// Starts the playback backend for `system`.
#[cfg_attr(
    not(any(feature = "pipewire", feature = "alsa")),
    allow(
        unused_variables,
        clippy::needless_pass_by_value,
        clippy::unnecessary_wraps
    )
)]
fn start_playback(system: System, counted: Counted, shape: Shape) -> Result<Playing, Wrong> {
    match system {
        System::Software => Ok(Playing::Software(Box::new(counted))),
        #[cfg(feature = "pipewire")]
        System::PipeWire(target) => {
            let settings = unisono_pipewire::Settings {
                name: "unisono-receive".into(),
                rate: shape.rate,
                channels: u32::from(shape.channels),
                target,
                monitor: false,
                largest_cycle: shape.cycle.max(8_192),
                cycle: u32::try_from(shape.cycle)
                    .map_err(|_| Wrong("`--cycle` exceeds PipeWire limit".into()))?,
            };
            let running = unisono_pipewire::play(counted, settings)
                .map_err(|error| Wrong(format!("playing with PipeWire: {error}")))?;
            Ok(Playing::PipeWire(running))
        }
        #[cfg(feature = "alsa")]
        System::Alsa(device) => {
            let settings = unisono_alsa::Settings {
                device,
                rate: shape.rate,
                channels: u32::from(shape.channels),
                cycle: u32::try_from(shape.cycle)
                    .map_err(|_| Wrong("`--cycle` exceeds ALSA limit".into()))?,
                cycles: 4,
            };
            let running = unisono_alsa::play(counted, &settings)
                .map_err(|error| Wrong(format!("playing with ALSA: {error}")))?;
            if !running.realtime() {
                eprintln!("unisono: the device's thread is not scheduled ahead of others");
            }
            Ok(Playing::Alsa(running))
        }
    }
}

/// Writes what `output` played: a line that says what the device was like,
/// then the samples as 32-bit floats, least significant byte first.
fn write_record(path: &str, output: &Output) -> std::io::Result<()> {
    let device = output.device();
    let mut file = BufWriter::new(File::create(path)?);
    writeln!(
        file,
        "unisono record rate {} channels {} cycle {} drift {} start {} lead {}",
        device.rate, device.channels, device.cycle, device.drift, device.start, device.lead
    )?;
    for sample in output.recorded() {
        file.write_all(&sample.to_le_bytes())?;
    }
    file.flush()
}

/// The receiver's playback as `options` set it up.
fn playback(options: &Options, stream: u16, rate: u32, channels: u8) -> Result<Playback, Wrong> {
    let settings = Settings {
        stream,
        rate,
        channels,
        identity: options.get("identity", 1)?,
        silence: 1_000_000_000,
        slope_limit: 200_000,
        regulation: Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: (rate / 200).max(1),
        },
        concealment: Parameters::for_rate(rate),
        block: 256,
        device_range: 10_000_000,
    };
    settings
        .validate()
        .map_err(|error| Wrong(error.to_string()))?;
    let mut playback = Playback::new(&settings);
    if let Some(path) = options.one::<i64>("path")? {
        playback.path(path);
    }
    Ok(playback)
}

/// The receiver's counters among the metrics.
struct Counters {
    played: Tally,
    concealed: Tally,
    jumps: Tally,
    delay: FloatGauge,
    revisions: Tally,
    squares: FloatGauge,
    products: FloatGauge,
}

impl Counters {
    /// The counters, among metrics that are served where `--metrics` says.
    fn served(options: &Options) -> Result<(Counters, Option<Server>), Wrong> {
        let mut metrics = Metrics::new();
        let counters = Counters::new(&mut metrics)?;
        let server = match options.one::<SocketAddr>("metrics")? {
            Some(address) => Some(
                metrics
                    .serve(address)
                    .map_err(|error| Wrong(format!("serving metrics at {address}: {error}")))?,
            ),
            None => None,
        };
        Ok((counters, server))
    }

    fn new(metrics: &mut Metrics) -> Result<Counters, Wrong> {
        let named = |error| Wrong(format!("registering metrics: {error:?}"));
        Ok(Counters {
            played: metrics
                .tally(
                    "unisono_receiver_played_frames_total",
                    "Frames played from the stream.",
                )
                .map_err(named)?,
            concealed: metrics
                .tally(
                    "unisono_receiver_concealed_frames_total",
                    "Frames of the stream that were missing when they were due, and concealed.",
                )
                .map_err(named)?,
            jumps: metrics
                .tally(
                    "unisono_receiver_jumps_total",
                    "Cycles that did not go on where the one before ended.",
                )
                .map_err(named)?,
            delay: metrics
                .gauge(
                    "unisono_receiver_path_delay_seconds",
                    "The receiver's estimate of the smallest delay of a packet from the sender.",
                )
                .map_err(named)?,
            revisions: metrics
                .tally(
                    "unisono_receiver_schedule_revisions_total",
                    "Cycles at whose start the position that is due was held against where \
                     the cycle before expected it.",
                )
                .map_err(named)?,
            squares: metrics
                .gauge(
                    "unisono_receiver_schedule_revision_squares",
                    "The squares of those differences, added up, in square frames.",
                )
                .map_err(named)?,
            products: metrics
                .gauge(
                    "unisono_receiver_schedule_revision_products",
                    "The products of each of those differences with the one before it, added \
                     up, in square frames: nothing against the squares when the differences \
                     cannot be foreseen.",
                )
                .map_err(named)?,
        })
    }

    fn update(&mut self, playback: &Playback) {
        let totals = playback.totals();
        self.played.update(totals.played);
        self.concealed.update(totals.concealed);
        self.jumps.update(totals.jumps);
        let revisions = playback.revisions();
        self.revisions.update(revisions.count);
        self.squares.set(revisions.squares);
        self.products.set(revisions.products);
        // A delay in nanoseconds is exact as a float.
        #[allow(clippy::cast_precision_loss)]
        self.delay.set(playback.receiver().delay() as f64 * 1e-9);
    }
}

/// What the receiver did, read from its metrics.
struct Seen {
    played: Counter,
    concealed: Counter,
    jumps: Counter,
    delay: FloatGauge,
}

impl Seen {
    fn of(counters: &Counters) -> Seen {
        Seen {
            played: counters.played.handle(),
            concealed: counters.concealed.handle(),
            jumps: counters.jumps.handle(),
            delay: counters.delay.clone(),
        }
    }
}

/// Says what the receiver did.
fn summarize(counts: &NetworkCounts, seen: &Seen) {
    println!(
        "received packets {} answers {} reports {} dropped {} played {} concealed {} jumps {} \
         delay {} requests {} unsent {} blocked {}",
        counts.packets,
        counts.answers,
        counts.reports,
        counts.dropped,
        seen.played.get(),
        seen.concealed.get(),
        seen.jumps.get(),
        (seen.delay.get() * 1e9).round(),
        counts.requests,
        counts.unsent,
        counts.blocked,
    );
}

/// The receiver's audio thread, which puts what it did into the metrics
/// after each cycle.
struct Counted {
    audio: Audio,
    counters: Counters,
}

impl AudioPlayback for Counted {
    fn channels(&self) -> usize {
        self.audio.channels()
    }

    fn cycle(&mut self, frames: &mut [f32], position: u64, time: i64) {
        self.audio.cycle(frames, position, time);
        self.counters.update(self.audio.playback());
    }
}
