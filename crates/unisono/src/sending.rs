// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `unisono send`: a software capture device that makes a signal, and a
//! sender that sends what it captures.

use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use unisono_core::packet::Format;
use unisono_core::sender::Settings as StreamSettings;
use unisono_metrics::FloatGauge;
use unisono_runtime::level::{Choice, Weights};
use unisono_runtime::send::{self, CaptureEnd, SenderNetwork, Settings};
use unisono_runtime::socket::Socket;
use unisono_runtime::software::{Device, Input};
use unisono_runtime::{clock, memory};

use crate::exported::{Metrics, Tally};
use crate::options::{Options, Wrong};
use crate::{Signal, System, sleep_until};

/// The options of `unisono send`.
pub(crate) const OPTIONS: &[&str] = &[
    "to",
    "audio",
    "device",
    "bind",
    "stream",
    "rate",
    "channels",
    "bits",
    "packet",
    "level",
    "level-choice",
    "gap-cost",
    "missed-cost",
    "move-cost",
    "level-slope",
    "protection",
    "signal",
    "cycle",
    "drift",
    "span",
    "window",
    "seconds",
    "metrics",
    "clock-offset",
    "clock-skew",
];

pub(crate) const HELP: &str = "\
unisono send --to ADDRESS [--to ADDRESS ...] [options]

Captures a signal with a software device and sends it to each receiver.

  --to ADDRESS        a receiver; may be given more than once
  --bind ADDRESS      where to send from (0.0.0.0:0)
  --stream N          the stream's number (1)
  --rate HZ           frames per second (48000)
  --channels N        samples in a frame (2)
  --bits 16|24        bits of a sample on the wire (24)
  --packet FRAMES     frames in a packet (240)
  --level MS          the latency that receivers hold at the start, in ms (30)
  --level-choice on|off
                      whether the level is chosen from the needs that
                      receivers report (on); the costs below are counted as
                      the seconds that a millisecond more of level, held for
                      them, costs as much as
  --gap-cost S        the cost of a gap of the group of receivers (600)
  --missed-cost S     the cost of each millisecond of frames missed (60)
  --move-cost S       the cost of moving the level (60)
  --level-slope US    how fast the level moves, in microseconds per second;
                      at most 1000, by which the receivers change their
                      pace at most, and less to leave room for the drift of
                      their clocks (500)
  --protection on|off whether packets are kept for a second, to be sent
                      again to a receiver that asks for frames it misses (on)
  --signal ramp|tone|silence
                      what the device captures (tone): a ramp that says
                      which frame a sample is, a tone of 440 Hz, or silence
  --audio software|pipewire|alsa
                      the device to capture with: one of software, which
                      captures the signal, or PipeWire or ALSA, when the
                      program is built with them (software)
  --device NAME       with PipeWire, the node to capture from; with ALSA,
                      the device (the default)
  --cycle FRAMES      frames in a cycle of the device (256)
  --drift PPB         how much faster the device runs, in parts per billion (0)
  --span MS           how long receivers remember samples of the clock (2000)
  --window FRAMES     frames in a window of the clock estimate (2400)
  --seconds S         stop after this long (0: run until stopped)
  --metrics ADDRESS   serve metrics in the Prometheus text format here
  --clock-offset NS, --clock-skew PPB
                      move this process's clock (for tests on one host)
";

/// What captures the frames.
enum Capturing {
    /// The thread of the software device, which says at its end how many
    /// cycles it dropped.
    Software(std::thread::JoinHandle<u64>),
    /// A PipeWire stream.
    #[cfg(feature = "pipewire")]
    PipeWire(unisono_pipewire::Running),
    /// An ALSA device.
    #[cfg(feature = "alsa")]
    Alsa(unisono_alsa::Running),
}

impl Capturing {
    /// Stops capturing, and says how many cycles the device dropped.
    fn finish(self) -> u64 {
        match self {
            Capturing::Software(thread) => thread.join().unwrap_or(0),
            #[cfg(feature = "pipewire")]
            Capturing::PipeWire(running) => {
                running.stop();
                0
            }
            #[cfg(feature = "alsa")]
            Capturing::Alsa(running) => {
                running.stop();
                0
            }
        }
    }
}

/// Starts capturing with the device of `system`: frames per second, samples
/// in a frame and frames in a cycle as `shape` says.
// With the software device alone, `system` says nothing more.
#[cfg_attr(
    not(any(feature = "pipewire", feature = "alsa")),
    allow(clippy::needless_pass_by_value)
)]
fn start_capture<S: FnMut(u64, i64, &mut [f32]) + Send + 'static>(
    system: System,
    mut input: Input<S>,
    mut capture_end: CaptureEnd,
    stop: Arc<AtomicBool>,
    shape: (u32, u8, usize),
) -> Result<Capturing, Wrong> {
    match system {
        System::Software => {
            // The software device needs nothing of the shape that it is not
            // made with.
            let _ = shape;
            let thread = std::thread::Builder::new()
                .name("unisono-capture".into())
                .stack_size(crate::STACK)
                .spawn(move || {
                    while !stop.load(Ordering::Relaxed) {
                        input.run(clock::raw(), &mut capture_end);
                        sleep_until(input.due());
                    }
                    capture_end.dropped()
                })
                .map_err(|error| Wrong(format!("starting the capture thread: {error}")))?;
            Ok(Capturing::Software(thread))
        }
        #[cfg(feature = "pipewire")]
        System::PipeWire(target) => {
            let (rate, channels, cycle) = shape;
            let settings = unisono_pipewire::Settings {
                name: "unisono-send".into(),
                rate,
                channels: u32::from(channels),
                target,
                monitor: false,
                largest_cycle: 8_192,
                cycle: u32::try_from(cycle).unwrap_or(256),
            };
            let running = unisono_pipewire::capture(capture_end, settings)
                .map_err(|error| Wrong(format!("capturing with PipeWire: {error}")))?;
            let _ = (input, stop);
            Ok(Capturing::PipeWire(running))
        }
        #[cfg(feature = "alsa")]
        System::Alsa(device) => {
            let (rate, channels, cycle) = shape;
            let settings = unisono_alsa::Settings {
                device,
                rate,
                channels: u32::from(channels),
                cycle: u32::try_from(cycle).unwrap_or(256),
                cycles: 4,
            };
            let running = unisono_alsa::capture(capture_end, &settings)
                .map_err(|error| Wrong(format!("capturing with ALSA: {error}")))?;
            let _ = (input, stop);
            Ok(Capturing::Alsa(running))
        }
    }
}

/// Runs `unisono send`.
pub(crate) fn run(options: &Options) -> Result<(), Wrong> {
    let receivers = options.addresses("to")?;
    if receivers.is_empty() {
        return Err(Wrong("`--to` must be given".into()));
    }
    let bind: SocketAddr = options.get("bind", SocketAddr::from(([0, 0, 0, 0], 0)))?;
    let rate: u32 = options.get("rate", 48_000)?;
    let channels: u8 = options.get("channels", 2)?;
    let format = match options.get("bits", 24u8)? {
        16 => Format::Signed16,
        24 => Format::Signed24,
        _ => return Err(Wrong("`--bits` is 16 or 24".into())),
    };
    let packet: u16 = options.get("packet", 240)?;
    let level: i64 = options.get("level", 30)?;
    let signal: Signal = options.get("signal", Signal::Tone)?;
    let cycle: usize = options.get("cycle", 256)?;
    let drift: i32 = options.get("drift", 0)?;
    let seconds: i64 = options.get("seconds", 0)?;
    let choice = level_choice(options, rate, options.get("window", 2_400)?)?;
    let system = System::from_options(options)?;
    if rate == 0 || channels == 0 || packet == 0 || cycle == 0 {
        return Err(Wrong(
            "the rate, channels, packet and cycle are not zero".into(),
        ));
    }

    let socket = Socket::bind(bind).map_err(|error| Wrong(format!("binding {bind}: {error}")))?;
    let start = clock::raw();
    let device = Device {
        rate,
        channels: usize::from(channels),
        cycle,
        drift,
        start,
        lead: 1_000_000,
        hidden: 0,
    };
    let input = Input::new(device, move |position, _, frame: &mut [f32]| {
        signal.fill(position, rate, frame);
    });
    let (capture_end, sender_end) = send::link(64, cycle, usize::from(channels));
    let network = SenderNetwork::new(
        socket,
        sender_end,
        Settings {
            stream: StreamSettings {
                stream: options.get("stream", 1)?,
                rate,
                channels,
                format,
                span: options.get("span", 2_000)?,
                window: options.get("window", 2_400)?,
                clock: send::clock_identity(),
            },
            packet,
            level: level.saturating_mul(1_000_000),
            choice,
            timeline: send::first_timeline(),
            receivers,
            kept: kept_packets(options)?,
        },
    );

    let mut metrics = Metrics::new();
    let counters = Counters::new(&mut metrics)?;
    if let Some(address) = options.addresses("metrics")?.first() {
        metrics
            .serve(*address)
            .map_err(|error| Wrong(format!("serving metrics at {address}: {error}")))?;
    }

    let stop = Arc::new(AtomicBool::new(false));
    let shape = (rate, channels, cycle);
    let capturing = start_capture(system, input, capture_end, Arc::clone(&stop), shape)?;
    let ending = Arc::new(AtomicBool::new(false));
    let networking = start_network(network, counters, Arc::clone(&ending))?;
    // Everything the threads use is made, and they are running.
    if let Err(error) = memory::lock() {
        eprintln!("unisono: memory is not locked: {error}");
    }

    println!("capture start {start} rate {rate} drift {drift} cycle {cycle}");
    let end = start.saturating_add(seconds.saturating_mul(1_000_000_000));
    while (seconds == 0 || clock::raw() < end) && !networking.is_finished() {
        std::thread::sleep(Duration::from_millis(5));
    }
    ending.store(true, Ordering::Relaxed);
    let network = networking
        .join()
        .map_err(|_| Wrong("the network thread failed".into()))??;
    stop.store(true, Ordering::Relaxed);
    let dropped = capturing.finish();
    summarize(&network, dropped);
    Ok(())
}

/// Says what the sender did.
fn summarize(network: &SenderNetwork, dropped: u64) {
    let counts = network.counts();
    println!(
        "sent packets {} answers {} filled {} restarts {} unsent {} dropped-cycles {dropped} \
         level-moves {} level {} again {}",
        counts.packets,
        counts.answers,
        counts.filled,
        counts.restarts,
        counts.unsent,
        counts.moves,
        network.sender().current_level(),
        counts.again
    );
}

/// How many packets the sender keeps to send again, as the options say: a
/// second and more of packets of five milliseconds, or none.
fn kept_packets(options: &Options) -> Result<usize, Wrong> {
    match options.get("protection", String::from("on"))?.as_str() {
        "on" => Ok(256),
        "off" => Ok(0),
        _ => Err(Wrong("`--protection` is on or off".into())),
    }
}

/// Starts the network thread: it sends what the capture thread hands it,
/// answers reports and keeps the counters, until `ending` is set, and gives
/// the sender's network end back.
fn start_network(
    mut network: SenderNetwork,
    mut counters: Counters,
    ending: Arc<AtomicBool>,
) -> Result<std::thread::JoinHandle<Result<SenderNetwork, Wrong>>, Wrong> {
    std::thread::Builder::new()
        .name("unisono-network".into())
        .stack_size(crate::STACK)
        .spawn(move || {
            crate::restrict_network_thread();
            while !ending.load(Ordering::Relaxed) {
                network
                    .turn(2)
                    .map_err(|error| Wrong(format!("sending: {error}")))?;
                counters.update(&network);
                std::thread::sleep(Duration::from_micros(200));
            }
            Ok(network)
        })
        .map_err(|error| Wrong(format!("starting the network thread: {error}")))
}

/// The sender's counters among the metrics.
struct Counters {
    packets: Tally,
    answers: Tally,
    filled: Tally,
    restarts: Tally,
    moves: Tally,
    again: Tally,
    level: FloatGauge,
    stretches: Tally,
    largest: Tally,
    expected: FloatGauge,
    beyond: FloatGauge,
    replaced: Tally,
    outlasted: Tally,
}

impl Counters {
    fn new(metrics: &mut Metrics) -> Result<Counters, Wrong> {
        let named = |error| Wrong(format!("registering metrics: {error:?}"));
        Ok(Counters {
            packets: metrics
                .tally(
                    "unisono_sender_packets_total",
                    "Audio packets made and sent to every receiver.",
                )
                .map_err(named)?,
            answers: metrics
                .tally(
                    "unisono_sender_answers_total",
                    "Reports of receivers answered.",
                )
                .map_err(named)?,
            filled: metrics
                .tally(
                    "unisono_sender_filled_frames_total",
                    "Frames sent as silence for cycles of the capture device that were dropped.",
                )
                .map_err(named)?,
            restarts: metrics
                .tally(
                    "unisono_sender_timeline_restarts_total",
                    "Timelines started after the first.",
                )
                .map_err(named)?,
            moves: metrics
                .tally(
                    "unisono_sender_level_moves_total",
                    "Moves of the level that were begun.",
                )
                .map_err(named)?,
            again: metrics
                .tally(
                    "unisono_sender_packets_sent_again_total",
                    "Packets sent again to a receiver that asked for their frames.",
                )
                .map_err(named)?,
            level: metrics
                .gauge(
                    "unisono_sender_level_seconds",
                    "The latency that every receiver holds for the next frame.",
                )
                .map_err(named)?,
            stretches: metrics
                .tally(
                    "unisono_sender_level_stretches_total",
                    "Stretches of the stream whose need was held against the needs of the \
                     stretches before them.",
                )
                .map_err(named)?,
            largest: metrics
                .tally(
                    "unisono_sender_level_largest_needs_total",
                    "Stretches that needed more than every stretch before them.",
                )
                .map_err(named)?,
            expected: metrics
                .gauge(
                    "unisono_sender_level_largest_needs_expected",
                    "How many stretches are expected to need more than every stretch before \
                     them when nothing sets a stretch apart from those before it.",
                )
                .map_err(named)?,
            beyond: metrics
                .gauge(
                    "unisono_sender_level_largest_needs_beyond",
                    "For each stretch that needed more than every stretch before it, the \
                     probability that the assumed law gave to a need as large or larger, added \
                     up: half the number of such stretches when the law holds.",
                )
                .map_err(named)?,
            replaced: metrics
                .tally(
                    "unisono_sender_level_choices_replaced_total",
                    "Levels chosen that another choice has replaced.",
                )
                .map_err(named)?,
            outlasted: metrics
                .tally(
                    "unisono_sender_level_choices_outlasted_total",
                    "Levels chosen and replaced that were held for longer than the time of \
                     the evidence they were chosen from: half of them when the needs keep \
                     their law as the rule for moving takes them to.",
                )
                .map_err(named)?,
        })
    }

    fn update(&mut self, network: &SenderNetwork) {
        let counts = network.counts();
        let level = network.sender().current_level();
        if let Some(checks) = network.checks() {
            self.stretches.update(checks.stretches);
            self.largest.update(checks.largest);
            self.expected.set(checks.expected);
            self.beyond.set(checks.beyond);
            self.replaced.update(checks.replaced);
            self.outlasted.update(checks.outlasted);
        }
        self.moves.update(counts.moves);
        self.again.update(counts.again);
        // A level is far below 2^53 nanoseconds, where an `f64` is exact.
        #[allow(clippy::cast_precision_loss)]
        self.level.set(level as f64 * 1e-9);
        self.packets.update(counts.packets);
        self.answers.update(counts.answers);
        self.filled.update(counts.filled);
        self.restarts.update(counts.restarts);
    }
}

/// How the level is chosen, as the options say: `None` if it is held.
///
/// The costs are counted in units in which a millisecond of level costs one
/// each second, so that a cost given as `S` seconds is what that millisecond
/// costs when it is held for `S` seconds. The evidence is the needs of the
/// last two minutes.
fn level_choice(options: &Options, rate: u32, window: u32) -> Result<Option<Choice>, Wrong> {
    match options.get("level-choice", String::from("on"))?.as_str() {
        "on" => {}
        "off" => return Ok(None),
        _ => return Err(Wrong("`--level-choice` is on or off".into())),
    }
    let gap: f64 = options.get("gap-cost", 600.0)?;
    let missed: f64 = options.get("missed-cost", 60.0)?;
    let moving: f64 = options.get("move-cost", 60.0)?;
    let slope: i32 = options.get("level-slope", 500)?;
    // A receiver of this program changes its pace by a thousandth at most,
    // and a level that moves faster than that is not followed.
    if !(1..=1_000).contains(&slope) {
        return Err(Wrong(
            "`--level-slope` is from 1 to 1000 microseconds per second".into(),
        ));
    }
    if window == 0 {
        return Err(Wrong("`--window` is not zero".into()));
    }
    let stretches = |seconds: u64| {
        usize::try_from(seconds * u64::from(rate) / u64::from(window)).unwrap_or(usize::MAX)
    };
    Ok(Some(Choice {
        weights: Weights {
            latency: 1_000.0,
            target: 0,
            off_target: 0.0,
            gap,
            // Missing a fraction of the frames each second misses a
            // thousand times that many milliseconds.
            missed: missed * 1_000.0,
            moving,
        },
        history: stretches(120),
        slope: slope.saturating_mul(1_000),
    }))
}
