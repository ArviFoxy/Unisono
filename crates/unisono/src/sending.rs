// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `unisono send` subcommand: captures audio and streams it over UDP.

use std::io;
use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Duration;

use unisono_core::packet::Format;
use unisono_core::sender::Settings as StreamSettings;
use unisono_metrics::FloatGauge;
use unisono_runtime::audio::Capture;
use unisono_runtime::level::{Choice, Weights};
use unisono_runtime::network_thread::{NetworkLoop, NetworkThread};
use unisono_runtime::send::{self, CaptureEnd, SenderNetwork, Settings};
use unisono_runtime::socket::{self, Socket};
use unisono_runtime::virtual_device::{Device, Input};
use unisono_runtime::{clock, memory};

use crate::metrics::{Metrics, Tally};
use crate::options::{Options, Wrong};
use crate::{MAX_CYCLE, Signal, System, sleep_until, validate_drift};

/// Minimum capture ring buffer size in frames for real audio backends whose
/// negotiated quantum or period may exceed `--cycle`.
#[cfg_attr(not(any(feature = "pipewire", feature = "alsa")), allow(dead_code))]
const AUDIO_RING_MIN_FRAMES: usize = 8_192;

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
  --bind ADDRESS      where to send from (0.0.0.0:0 or [::]:0)
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

/// Wraps [`CaptureEnd`] so its wait-free dropped-cycle count can be observed
/// across software, PipeWire, and ALSA backends.
struct TrackedCapture {
    inner: CaptureEnd,
    dropped: Arc<AtomicU64>,
}

impl Capture for TrackedCapture {
    fn channels(&self) -> usize {
        self.inner.channels()
    }

    fn cycle(&mut self, frames: &[f32], position: u64, time: i64) {
        self.inner.cycle(frames, position, time);
        self.dropped.store(self.inner.dropped(), Ordering::Relaxed);
    }
}

/// What captures the frames.
enum Capturing {
    /// The thread of the software device.
    Software(std::thread::JoinHandle<()>),
    /// A PipeWire stream.
    #[cfg(feature = "pipewire")]
    PipeWire(unisono_pipewire::Running),
    /// An ALSA device.
    #[cfg(feature = "alsa")]
    Alsa(unisono_alsa::Running),
}

impl Capturing {
    /// Whether the capture thread or audio stream has already exited.
    fn is_finished(&self) -> bool {
        match self {
            Capturing::Software(thread) => thread.is_finished(),
            #[cfg(feature = "pipewire")]
            Capturing::PipeWire(running) => running.is_finished(),
            #[cfg(feature = "alsa")]
            Capturing::Alsa(running) => running.is_finished(),
        }
    }

    /// Stops capturing and returns any fatal audio-device error.
    fn finish(self) -> Result<(), Wrong> {
        match self {
            Capturing::Software(thread) => thread
                .join()
                .map_err(|_| Wrong("the capture thread failed".into())),
            #[cfg(feature = "pipewire")]
            Capturing::PipeWire(running) => running
                .stop()
                .map_err(|error| Wrong(format!("capturing with PipeWire: {error}"))),
            #[cfg(feature = "alsa")]
            Capturing::Alsa(running) => running
                .stop()
                .map_err(|error| Wrong(format!("capturing with ALSA: {error}"))),
        }
    }
}

/// Starts capturing with the device of `system`: frames per second, samples
/// in a frame, requested cycle length, and ring buffer capacity in frames.
#[cfg_attr(
    not(any(feature = "pipewire", feature = "alsa")),
    allow(clippy::needless_pass_by_value)
)]
fn start_capture<S: FnMut(u64, i64, &mut [f32]) + Send + 'static>(
    system: System,
    mut input: Input<S>,
    mut capture: TrackedCapture,
    stop: Arc<AtomicBool>,
    shape: (u32, u8, usize, usize),
) -> Result<Capturing, Wrong> {
    let (rate, channels, cycle, ring_frames) = shape;
    match system {
        System::Software => {
            let _ = (rate, channels, cycle, ring_frames);
            let thread = std::thread::Builder::new()
                .name("unisono-capture".into())
                .stack_size(crate::STACK)
                .spawn(move || {
                    while !stop.load(Ordering::Relaxed) {
                        input.run(clock::raw(), &mut capture);
                        sleep_until(input.due());
                    }
                })
                .map_err(|error| Wrong(format!("starting the capture thread: {error}")))?;
            Ok(Capturing::Software(thread))
        }
        #[cfg(feature = "pipewire")]
        System::PipeWire(target) => {
            let settings = unisono_pipewire::Settings {
                name: "unisono-send".into(),
                rate,
                channels: u32::from(channels),
                target,
                monitor: false,
                largest_cycle: ring_frames,
                cycle: u32::try_from(cycle)
                    .map_err(|_| Wrong("`--cycle` exceeds PipeWire limit".into()))?,
            };
            let running = unisono_pipewire::capture(capture, settings)
                .map_err(|error| Wrong(format!("capturing with PipeWire: {error}")))?;
            let _ = (input, stop);
            Ok(Capturing::PipeWire(running))
        }
        #[cfg(feature = "alsa")]
        System::Alsa(device) => {
            let settings = unisono_alsa::Settings {
                device,
                rate,
                channels: u32::from(channels),
                cycle: u32::try_from(cycle)
                    .map_err(|_| Wrong("`--cycle` exceeds ALSA limit".into()))?,
                cycles: 4,
            };
            let running = unisono_alsa::capture(capture, &settings)
                .map_err(|error| Wrong(format!("capturing with ALSA: {error}")))?;
            let negotiated = running.cycle();
            if negotiated > ring_frames {
                let _ = running.stop();
                return Err(Wrong(format!(
                    "ALSA negotiated a cycle of {negotiated} frames, larger than the \
                     capture ring buffer of {ring_frames} frames"
                )));
            }
            if !running.realtime() {
                eprintln!("unisono: the device's thread is not scheduled ahead of others");
            }
            let _ = (input, stop);
            Ok(Capturing::Alsa(running))
        }
    }
}

/// Runs the sender network loop and mirrors its counters into Prometheus
/// metrics without allocating or making additional syscalls.
struct CountedSender {
    network: SenderNetwork,
    counters: Counters,
    dropped: Arc<AtomicU64>,
}

impl NetworkLoop for CountedSender {
    fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        self.network.turn(milliseconds)?;
        self.counters
            .update(&self.network, self.dropped.load(Ordering::Relaxed));
        Ok(())
    }
}

/// Validated configuration parsed from `unisono send` CLI options.
struct Config {
    bind: SocketAddr,
    rate: u32,
    channels: u8,
    signal: Signal,
    cycle: usize,
    drift: i32,
    seconds: i64,
    system: System,
    settings: Settings,
    metrics: Option<SocketAddr>,
}

impl Config {
    fn from_options(options: &Options) -> Result<Config, Wrong> {
        let receivers = options.addresses("to")?;
        if receivers.is_empty() {
            return Err(Wrong("`--to` must be given".into()));
        }
        let bind: SocketAddr = options
            .one("bind")?
            .unwrap_or_else(|| socket::unspecified_for(&receivers));
        let rate: u32 = options.get("rate", 48_000)?;
        let channels: u8 = options.get("channels", 2)?;
        let format = match options.get("bits", 24u8)? {
            16 => Format::Signed16,
            24 => Format::Signed24,
            _ => return Err(Wrong("`--bits` is 16 or 24".into())),
        };
        let packet: u16 = options.get("packet", 240)?;
        let level = options
            .get::<i64>("level", 30)?
            .checked_mul(1_000_000)
            .filter(|ns| *ns >= 0)
            .ok_or_else(|| {
                Wrong("`--level` must be a non-negative number of milliseconds".into())
            })?;
        let signal: Signal = options.get("signal", Signal::Tone)?;
        let cycle: usize = options.get("cycle", 256)?;
        let drift: i32 = options.get("drift", 0)?;
        let seconds: i64 = options.get("seconds", 0)?;
        let window: u32 = options.get("window", 2_400)?;
        let choice = level_choice(options, rate, window)?;
        let system = System::from_options(options)?;
        if cycle == 0 || cycle > MAX_CYCLE {
            return Err(Wrong(format!("`--cycle` must be in 1..={MAX_CYCLE}")));
        }
        if seconds < 0 {
            return Err(Wrong("`--seconds` must not be negative".into()));
        }
        validate_drift(drift)?;

        let settings = Settings {
            stream: StreamSettings {
                stream: options.get("stream", 1)?,
                rate,
                channels,
                format,
                span: options.get("span", 2_000)?,
                window,
                clock: send::clock_identity(),
            },
            packet,
            level,
            choice,
            timeline: send::first_timeline(),
            receivers,
            kept: kept_packets(options)?,
        };
        settings
            .validate()
            .map_err(|error| Wrong(error.to_string()))?;
        let metrics = options.one("metrics")?;

        Ok(Config {
            bind,
            rate,
            channels,
            signal,
            cycle,
            drift,
            seconds,
            system,
            settings,
            metrics,
        })
    }
}

/// Runs `unisono send`.
pub(crate) fn run(options: &Options) -> Result<(), Wrong> {
    let config = Config::from_options(options)?;
    let socket = Socket::bind(config.bind)
        .map_err(|error| Wrong(format!("binding {}: {error}", config.bind)))?;
    let start = clock::raw();
    let device = Device {
        rate: config.rate,
        channels: usize::from(config.channels),
        cycle: config.cycle,
        drift: config.drift,
        start,
        lead: 1_000_000,
        hidden: 0,
    };
    let signal = config.signal;
    let rate = config.rate;
    let input = Input::new(device, move |position, _, frame: &mut [f32]| {
        signal.fill(position, rate, frame);
    });
    let ring_frames = match config.system {
        System::Software => config.cycle,
        #[cfg(any(feature = "pipewire", feature = "alsa"))]
        _ => config.cycle.max(AUDIO_RING_MIN_FRAMES),
    };
    let (capture_end, sender_end) = send::link(64, ring_frames, usize::from(config.channels));
    let dropped = Arc::new(AtomicU64::new(0));
    let tracked = TrackedCapture {
        inner: capture_end,
        dropped: Arc::clone(&dropped),
    };
    let network = SenderNetwork::new(socket, sender_end, config.settings);

    let mut metrics = Metrics::new();
    let counters = Counters::new(&mut metrics)?;
    let _metrics_server = match config.metrics {
        Some(address) => Some(
            metrics
                .serve(address)
                .map_err(|error| Wrong(format!("serving metrics at {address}: {error}")))?,
        ),
        None => None,
    };

    let stop = Arc::new(AtomicBool::new(false));
    let shape = (config.rate, config.channels, config.cycle, ring_frames);
    let capturing = start_capture(config.system, input, tracked, Arc::clone(&stop), shape)?;
    let networking = match NetworkThread::spawn(
        "unisono-network",
        CountedSender {
            network,
            counters,
            dropped: Arc::clone(&dropped),
        },
        2,
    ) {
        Ok(thread) => thread,
        Err(error) => {
            stop.store(true, Ordering::Relaxed);
            let _ = capturing.finish();
            return Err(Wrong(format!("starting the network thread: {error}")));
        }
    };
    if !networking.restricted() {
        eprintln!("unisono: the network thread's system calls are not restricted");
    }
    // Everything the threads use is made, and they are running.
    if let Err(error) = memory::lock() {
        eprintln!("unisono: memory is not locked: {error}");
    }

    println!(
        "capture start {start} rate {} drift {} cycle {}",
        config.rate, config.drift, config.cycle
    );
    let end = start.saturating_add(config.seconds.saturating_mul(1_000_000_000));
    while (config.seconds == 0 || clock::raw() < end)
        && !crate::interrupted()
        && !networking.is_finished()
        && !capturing.is_finished()
    {
        std::thread::sleep(Duration::from_millis(5));
    }
    let stopped = networking
        .stop()
        .map_err(|_| Wrong("the network thread failed".into()))?;
    stop.store(true, Ordering::Relaxed);
    let audio_result = capturing.finish();
    let total_dropped = dropped.load(Ordering::Relaxed);
    summarize(&stopped.network.network, total_dropped);
    if let Some(error) = stopped.error {
        return Err(Wrong(format!("sending: {error}")));
    }
    audio_result
}

/// Says what the sender did.
fn summarize(network: &SenderNetwork, dropped: u64) {
    let counts = network.counts();
    println!(
        "sent packets {} answers {} ignored {} filled {} restarts {} unsent {} blocked {} \
         dropped-cycles {dropped} level-moves {} level {} again {}",
        counts.packets,
        counts.answers,
        counts.ignored,
        counts.filled,
        counts.restarts,
        counts.unsent,
        counts.blocked,
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

/// The sender's counters among the metrics.
struct Counters {
    packets: Tally,
    answers: Tally,
    ignored: Tally,
    unsent: Tally,
    blocked: Tally,
    filled: Tally,
    restarts: Tally,
    dropped: Tally,
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
    fn tally(
        metrics: &mut Metrics,
        name: &'static str,
        help: &'static str,
    ) -> Result<Tally, Wrong> {
        metrics
            .tally(name, help)
            .map_err(|error| Wrong(format!("registering metrics: {error:?}")))
    }

    fn gauge(
        metrics: &mut Metrics,
        name: &'static str,
        help: &'static str,
    ) -> Result<FloatGauge, Wrong> {
        metrics
            .gauge(name, help)
            .map_err(|error| Wrong(format!("registering metrics: {error:?}")))
    }

    fn new(metrics: &mut Metrics) -> Result<Counters, Wrong> {
        Ok(Counters {
            packets: Self::tally(
                metrics,
                "unisono_sender_packets_total",
                "Audio packets made and sent to every receiver.",
            )?,
            answers: Self::tally(
                metrics,
                "unisono_sender_answers_total",
                "Reports of receivers answered.",
            )?,
            ignored: Self::tally(
                metrics,
                "unisono_sender_ignored_datagrams_total",
                "Incoming datagrams dropped because their source address was not in --to.",
            )?,
            unsent: Self::tally(
                metrics,
                "unisono_sender_unsent_datagrams_total",
                "Outgoing datagrams that could not be sent due to a transient error.",
            )?,
            blocked: Self::tally(
                metrics,
                "unisono_sender_blocked_datagrams_total",
                "Outgoing datagrams rejected per destination with EPERM or EADDRNOTAVAIL.",
            )?,
            filled: Self::tally(
                metrics,
                "unisono_sender_filled_frames_total",
                "Frames sent as silence for cycles of the capture device that were dropped.",
            )?,
            restarts: Self::tally(
                metrics,
                "unisono_sender_timeline_restarts_total",
                "Timelines started after the first.",
            )?,
            dropped: Self::tally(
                metrics,
                "unisono_sender_dropped_cycles_total",
                "Cycles dropped by the capture thread before reaching the network thread.",
            )?,
            moves: Self::tally(
                metrics,
                "unisono_sender_level_moves_total",
                "Moves of the level that were begun.",
            )?,
            again: Self::tally(
                metrics,
                "unisono_sender_packets_sent_again_total",
                "Packets sent again to a receiver that asked for their frames.",
            )?,
            level: Self::gauge(
                metrics,
                "unisono_sender_level_seconds",
                "The latency that every receiver holds for the next frame.",
            )?,
            stretches: Self::tally(
                metrics,
                "unisono_sender_level_stretches_total",
                "Stretches of the stream whose need was held against the needs of the \
                 stretches before them.",
            )?,
            largest: Self::tally(
                metrics,
                "unisono_sender_level_largest_needs_total",
                "Stretches that needed more than every stretch before them.",
            )?,
            expected: Self::gauge(
                metrics,
                "unisono_sender_level_largest_needs_expected",
                "How many stretches are expected to need more than every stretch before \
                 them when nothing sets a stretch apart from those before it.",
            )?,
            beyond: Self::gauge(
                metrics,
                "unisono_sender_level_largest_needs_beyond",
                "For each stretch that needed more than every stretch before it, the \
                 probability that the assumed law gave to a need as large or larger, added \
                 up: half the number of such stretches when the law holds.",
            )?,
            replaced: Self::tally(
                metrics,
                "unisono_sender_level_choices_replaced_total",
                "Levels chosen that another choice has replaced.",
            )?,
            outlasted: Self::tally(
                metrics,
                "unisono_sender_level_choices_outlasted_total",
                "Levels chosen and replaced that were held for longer than the time of \
                 the evidence they were chosen from: half of them when the needs keep \
                 their law as the rule for moving takes them to.",
            )?,
        })
    }

    fn update(&mut self, network: &SenderNetwork, dropped: u64) {
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
        self.ignored.update(counts.ignored);
        self.unsent.update(counts.unsent);
        self.blocked.update(counts.blocked);
        self.filled.update(counts.filled);
        self.restarts.update(counts.restarts);
        self.dropped.update(dropped);
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
        usize::try_from(seconds * u64::from(rate) / u64::from(window))
            .unwrap_or(usize::MAX)
            .max(1)
    };
    let choice = Choice {
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
    };
    choice
        .validate()
        .map_err(|error| Wrong(error.to_string()))?;
    Ok(Some(choice))
}
