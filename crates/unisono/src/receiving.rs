// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `unisono receive`: a receiver that plays a stream on a software playback
//! device, and can keep what it played in a file.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use unisono_core::player::Regulation;
use unisono_dsp::Parameters;
use unisono_runtime::audio::Playback as AudioPlayback;
use unisono_runtime::pump::{ReceiverPlayback, Settings};
use unisono_runtime::receive::{
    self, Intake, NetworkCounts, ReceiverAudio, ReceiverNetwork, Reporting, Sizes,
};
use unisono_runtime::socket::Socket;
use unisono_runtime::software::{Device, Output};
use unisono_runtime::{clock, memory};

use crate::exported::{Metrics, Tally};
use crate::options::{Options, Wrong};
use crate::{System, sleep_until};
use unisono_metrics::{Counter, FloatGauge};

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
  --audio software|pipewire
                      the device to play on: one of software, which plays to
                      nothing at its own rate, or PipeWire, when the program
                      is built with it (software)
  --device NAME       with PipeWire, the node to play to (the default)
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

/// Runs `unisono receive`.
pub(crate) fn run(options: &Options) -> Result<(), Wrong> {
    let listen: SocketAddr = options.need("listen")?;
    let stream: u16 = options.get("stream", 1)?;
    let rate: u32 = options.get("rate", 48_000)?;
    let channels: u8 = options.get("channels", 2)?;
    let cycle: usize = options.get("cycle", 256)?;
    let drift: i32 = options.get("drift", 0)?;
    let lead: i64 = options.get("lead", 4)?;
    let seconds: i64 = options.get("seconds", 0)?;
    let record: Option<String> = options.all("record").first().cloned();
    let system = System::from_options(options)?;
    if record.is_some() && system != System::Software {
        return Err(Wrong("`--record` needs the software device".into()));
    }
    if rate == 0 || channels == 0 || cycle == 0 {
        return Err(Wrong("the rate, channels and cycle are not zero".into()));
    }
    if record.is_some() && seconds == 0 {
        return Err(Wrong("`--record` needs `--seconds`".into()));
    }

    let socket =
        Socket::bind(listen).map_err(|error| Wrong(format!("binding {listen}: {error}")))?;
    // With port 0 the system chooses the port: say which, before anything
    // else, so that whoever started the program can send to it.
    let listening = socket
        .address()
        .map_err(|error| Wrong(format!("the address of the socket: {error}")))?;
    println!("listening {listening}");
    let playback = playback(options, stream, rate, channels)?;
    let sizes = Sizes {
        buffers: 64,
        datagram: 9_000,
        messages: 64,
    };
    let (network_end, audio_end) = receive::link(sizes);
    let mut network = ReceiverNetwork::new(socket, network_end, stream, sizes);
    // Reports carry what the frames needed, for the sender's choice of the
    // level, whether or not the delay of the path is measured from them.
    let reports = Some(Reporting {
        at_start: options
            .get("report-period-at-start", 50i64)?
            .saturating_mul(1_000_000),
        after: options
            .get("report-period", 200i64)?
            .saturating_mul(1_000_000),
        ..Reporting::USUAL
    });
    let audio: Audio = ReceiverAudio::new(playback, audio_end, Intake { items: 16, reports });
    let start = clock::raw();
    let device = Device {
        rate,
        channels: usize::from(channels),
        cycle,
        drift,
        start,
        lead: lead.saturating_mul(1_000_000),
        hidden: 0,
    };
    let kept = if record.is_some() {
        usize::try_from(seconds.saturating_mul(i64::from(rate))).unwrap_or(0)
    } else {
        0
    };
    let mut output = Output::new(device, kept);

    let counters = Counters::served(options)?;

    let stop = Arc::new(AtomicBool::new(false));
    let stopping = Arc::clone(&stop);
    let networking = std::thread::Builder::new()
        .name("unisono-network".into())
        .stack_size(crate::STACK)
        .spawn(move || {
            while !stopping.load(Ordering::Relaxed) {
                if let Err(error) = network.turn(2) {
                    eprintln!("receiving: {error}");
                    break;
                }
            }
            network.counts()
        })
        .map_err(|error| Wrong(format!("starting the network thread: {error}")))?;
    // Everything the threads use is made, and they are running.
    if let Err(error) = memory::lock() {
        eprintln!("unisono: memory is not locked: {error}");
    }

    let seen = Seen::of(&counters);
    let counted = Counted { audio, counters };
    let end = (seconds > 0).then(|| start.saturating_add(seconds.saturating_mul(1_000_000_000)));
    let shape = Shape {
        rate,
        channels,
        cycle,
    };
    play(system, counted, &mut output, shape, end)?;
    stop.store(true, Ordering::Relaxed);
    let counts = networking
        .join()
        .map_err(|_| Wrong("the network thread failed".into()))?;
    summarize(&counts, &seen);
    if let Some(path) = record {
        write_record(&path, &output).map_err(|error| Wrong(format!("writing {path}: {error}")))?;
    }
    Ok(())
}

/// What a device of the stream is like, which PipeWire is told.
#[derive(Clone, Copy)]
#[cfg_attr(not(feature = "pipewire"), allow(dead_code))]
struct Shape {
    rate: u32,
    channels: u8,
    cycle: usize,
}

/// Plays on the device of `system` until the raw clock reads `end`, or for
/// ever.
// Without PipeWire there is one device, which needs neither the shape nor a
// way to fail.
#[cfg_attr(
    not(feature = "pipewire"),
    allow(
        unused_variables,
        clippy::needless_pass_by_value,
        clippy::unnecessary_wraps
    )
)]
fn play(
    system: System,
    mut counted: Counted,
    output: &mut Output,
    shape: Shape,
    end: Option<i64>,
) -> Result<(), Wrong> {
    let going = || end.is_none_or(|end| clock::raw() < end);
    match system {
        System::Software => {
            while going() {
                output.run(clock::raw(), &mut counted);
                sleep_until(output.due());
            }
        }
        #[cfg(feature = "pipewire")]
        System::PipeWire(target) => {
            let settings = unisono_pipewire::Settings {
                name: "unisono-receive".into(),
                rate: shape.rate,
                channels: u32::from(shape.channels),
                target,
                monitor: false,
                largest_cycle: 8_192,
                cycle: u32::try_from(shape.cycle).unwrap_or(256),
            };
            let running = unisono_pipewire::play(counted, settings)
                .map_err(|error| Wrong(format!("playing with PipeWire: {error}")))?;
            while going() {
                std::thread::sleep(std::time::Duration::from_millis(100));
            }
            running.stop();
        }
    }
    Ok(())
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
    let mut playback = Playback::new(&Settings {
        stream,
        rate,
        channels,
        identity: options.get("identity", 1)?,
        silence: 1_000_000_000,
        slope_limit: 200_000,
        regulation: Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: rate / 200,
        },
        concealment: Parameters::for_rate(rate),
        block: 256,
        device_range: 10_000_000,
    });
    if let Some(path) = options.all("path").first() {
        let path: i64 = path
            .parse()
            .map_err(|_| Wrong(format!("`--path {path}` is not a number of nanoseconds")))?;
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
}

impl Counters {
    /// The counters, among metrics that are served where `--metrics` says.
    fn served(options: &Options) -> Result<Counters, Wrong> {
        let mut metrics = Metrics::new();
        let counters = Counters::new(&mut metrics)?;
        if let Some(address) = options.addresses("metrics")?.first() {
            metrics
                .serve(*address)
                .map_err(|error| Wrong(format!("serving metrics at {address}: {error}")))?;
        }
        Ok(counters)
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
        })
    }

    fn update(&mut self, playback: &Playback) {
        let totals = playback.totals();
        self.played.update(totals.played);
        self.concealed.update(totals.concealed);
        self.jumps.update(totals.jumps);
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
         delay {}",
        counts.packets,
        counts.answers,
        counts.reports,
        counts.dropped,
        seen.played.get(),
        seen.concealed.get(),
        seen.jumps.get(),
        (seen.delay.get() * 1e9).round()
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
