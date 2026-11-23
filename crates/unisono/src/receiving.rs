// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `unisono receive` subcommand: receives a stream, synchronizes playback, and
//! optionally records virtual-device output to a file.

use std::collections::HashSet;
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::net::SocketAddr;

use unisono_core::kalman::NoisePrior;
use unisono_core::player::ModalRegulation;
use unisono_core::sync::{SyncSettings, SyncSnapshot, WEIGHT_UNITY_Q16};
use unisono_metrics::{Counter, FloatGauge, Gauge};
use unisono_runtime::audio::Playback as AudioPlayback;
use unisono_runtime::network_thread::{NetworkLoop, NetworkThread};
use unisono_runtime::pump::{Settings, ShippedPlayback};
use unisono_runtime::receive::{
    self, Intake, NetConfig, NetworkCounts, PeerConfig, ReceiverNetwork, Reporting,
    SHIPPED_INTAKE_ITEMS, SHIPPED_SIZES, ShippedAudio, SyncMode,
};
use unisono_runtime::socket::Socket;
use unisono_runtime::virtual_device::{Device, Output};
use unisono_runtime::{clock, memory};

use crate::metrics::{Metrics, Server, Tally};
use crate::options::{Options, Wrong};
use crate::{MAX_CYCLE, System, sleep_until, validate_drift};

/// The receiver: room for 16,384 frames, 64 samples of the sender's clock,
/// the arrivals of 8 packets, and 64 reports of its device.
type Playback = ShippedPlayback;

/// The receiver's audio thread.
type Audio = ShippedAudio;

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
    "sync",
    "peer",
    "mode",
    "clock-prior",
    "sender-clock-prior",
    "star-gain",
    "common-gain",
    "diff-gain",
    "link-weight",
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
  --sync peer|hull    clock synchronization mode: unified Kalman/BLUE/min-RTT
                      peer/star sync (peer) or legacy one-way lower hull (hull)
  --peer ID@ADDRESS   direct peer receiver for peer sync (repeatable, up to 15)
  --mode lipsync|low-latency
                      modal playback gain preset in peer sync (lipsync)
  --clock-prior tcxo|consumer|wandering
                      oscillator process-noise prior for receiver clocks (consumer)
  --sender-clock-prior tcxo|consumer|wandering
                      oscillator process-noise prior for the sender clock
                      (defaults to --clock-prior)
  --star-gain S^-1    single-mode star playback gain per second (4.0)
  --common-gain S^-1  common-mode playback gain per second in peer sync
                      (0.5 in lipsync, 0.05 in low-latency)
  --diff-gain S^-1    differential-mode playback gain per second in peer sync (4.0)
  --link-weight TARGET=WEIGHT
                      static BLUE link weight multiplier (> 0) for `sender` or a
                      configured peer ID (repeatable, peer sync only)
  --path NS           fixed one-way path delay from the sender in hull mode;
                      rejected in peer sync mode
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

/// Parses a named oscillator noise prior preset.
fn parse_clock_prior(name: &str, value: &str) -> Result<NoisePrior, Wrong> {
    match value {
        "tcxo" => Ok(NoisePrior::TCXO),
        "consumer" => Ok(NoisePrior::CONSUMER_QUARTZ),
        "wandering" => Ok(NoisePrior::WANDERING_QUARTZ),
        other => Err(Wrong(format!(
            "`--{name} {other}` must be one of `tcxo`, `consumer`, or `wandering`"
        ))),
    }
}

/// Converts a positive floating-point gain or link weight into fixed-point Q16.
fn positive_to_q16(name: &str, value: f64) -> Result<u32, Wrong> {
    if !value.is_finite() || value <= 0.0 || value > 65_535.0 {
        return Err(Wrong(format!(
            "`--{name}` must be a finite number in (0, 65535]"
        )));
    }
    // Bounded to `(0, 65535 * 65536]`, well within `u32`.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let q16 = (value * 65_536.0).round() as u32;
    Ok(q16.max(1))
}

/// Parses one `--peer ID@ADDRESS` argument.
fn parse_peer(value: &str) -> Result<PeerConfig, Wrong> {
    let Some((id_text, addr_text)) = value.split_once('@') else {
        return Err(Wrong(format!(
            "`--peer {value}` must have the form `ID@ADDRESS`"
        )));
    };
    let identity: u64 = id_text.parse().map_err(|_| {
        Wrong(format!(
            "`--peer {value}` has invalid receiver ID `{id_text}`"
        ))
    })?;
    let address: SocketAddr = addr_text.parse().map_err(|_| {
        Wrong(format!(
            "`--peer {value}` has invalid address `{addr_text}`"
        ))
    })?;
    Ok(PeerConfig {
        identity,
        address,
        weight_q16: WEIGHT_UNITY_Q16,
    })
}

/// Target of a `--link-weight TARGET=WEIGHT` override.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum WeightTarget {
    Sender,
    Peer(u64),
}

/// Parses one `--link-weight TARGET=WEIGHT` argument.
fn parse_link_weight(value: &str) -> Result<(WeightTarget, u32), Wrong> {
    let Some((target_text, weight_text)) = value.split_once('=') else {
        return Err(Wrong(format!(
            "`--link-weight {value}` must have the form `TARGET=WEIGHT`"
        )));
    };
    let target = if target_text == "sender" {
        WeightTarget::Sender
    } else {
        let id: u64 = target_text.parse().map_err(|_| {
            Wrong(format!(
                "`--link-weight {value}` target must be `sender` or a peer ID"
            ))
        })?;
        WeightTarget::Peer(id)
    };
    let weight: f64 = weight_text.parse().map_err(|_| {
        Wrong(format!(
            "`--link-weight {value}` has invalid numeric weight"
        ))
    })?;
    let q16 = positive_to_q16("link-weight", weight)?;
    Ok((target, q16))
}

/// Validated configuration parsed from `unisono receive` CLI options.
struct Config {
    listen: SocketAddr,
    stream: u16,
    identity: u64,
    rate: u32,
    channels: u8,
    cycle: usize,
    drift: i32,
    lead: i64,
    sync_mode: SyncMode,
    modal_regulation: Option<ModalRegulation>,
    net: NetConfig,
    fixed_path: Option<i64>,
    report_at_start: i64,
    report_after: i64,
    seconds: i64,
    record: Option<String>,
    kept: usize,
    system: System,
}

impl Config {
    #[allow(clippy::too_many_lines)]
    fn from_options(options: &Options) -> Result<Config, Wrong> {
        let listen: SocketAddr = options.need("listen")?;
        let stream: u16 = options.get("stream", 1)?;
        let identity: u64 = options.get("identity", 1)?;
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
        let sync_mode = match options.get("sync", "peer".to_string())?.as_str() {
            "peer" => SyncMode::Peer,
            "hull" => SyncMode::Hull,
            other => {
                return Err(Wrong(format!("`--sync {other}` must be `peer` or `hull`")));
            }
        };
        let fixed_path: Option<i64> = options.one("path")?;
        let raw_peers = options.all("peer");
        let raw_weights = options.all("link-weight");
        let mode_opt: Option<String> = options.one("mode")?;
        let clock_prior_opt: Option<String> = options.one("clock-prior")?;
        let sender_prior_opt: Option<String> = options.one("sender-clock-prior")?;
        let star_gain_opt: Option<f64> = options.one("star-gain")?;
        let common_gain_opt: Option<f64> = options.one("common-gain")?;
        let diff_gain_opt: Option<f64> = options.one("diff-gain")?;

        let datagram = unisono_runtime::send::MAX_DATAGRAM;
        let jump = (rate / 200).max(1);
        let (modal_regulation, net_config) = match sync_mode {
            SyncMode::Hull => {
                if !raw_peers.is_empty() {
                    return Err(Wrong("`--peer` cannot be used with `--sync hull`".into()));
                }
                if !raw_weights.is_empty() {
                    return Err(Wrong(
                        "`--link-weight` cannot be used with `--sync hull`".into(),
                    ));
                }
                if mode_opt.is_some()
                    || clock_prior_opt.is_some()
                    || sender_prior_opt.is_some()
                    || star_gain_opt.is_some()
                    || common_gain_opt.is_some()
                    || diff_gain_opt.is_some()
                {
                    return Err(Wrong(
                        "modal gain and clock-prior options cannot be used with `--sync hull`"
                            .into(),
                    ));
                }
                (None, NetConfig::hull(stream, datagram))
            }
            SyncMode::Peer => {
                if fixed_path.is_some() {
                    return Err(Wrong(
                        "`--path` cannot be used with `--sync peer` (use `--sync hull` for a fixed path delay)"
                            .into(),
                    ));
                }
                let base_modal = match mode_opt.as_deref().unwrap_or("lipsync") {
                    "lipsync" => ModalRegulation::lipsync(1_000_000, jump),
                    "low-latency" => ModalRegulation::low_latency(1_000_000, jump),
                    other => {
                        return Err(Wrong(format!(
                            "`--mode {other}` must be `lipsync` or `low-latency`"
                        )));
                    }
                };
                let modal = ModalRegulation {
                    star_gain: match star_gain_opt {
                        Some(v) => positive_to_q16("star-gain", v)?,
                        None => base_modal.star_gain,
                    },
                    common_gain: match common_gain_opt {
                        Some(v) => positive_to_q16("common-gain", v)?,
                        None => base_modal.common_gain,
                    },
                    diff_gain: match diff_gain_opt {
                        Some(v) => positive_to_q16("diff-gain", v)?,
                        None => base_modal.diff_gain,
                    },
                    limit: base_modal.limit,
                    jump,
                };
                let local_prior = match clock_prior_opt.as_deref() {
                    Some(v) => parse_clock_prior("clock-prior", v)?,
                    None => NoisePrior::CONSUMER_QUARTZ,
                };
                let sender_prior = match sender_prior_opt.as_deref() {
                    Some(v) => parse_clock_prior("sender-clock-prior", v)?,
                    None => local_prior,
                };
                let mut peers = Vec::with_capacity(raw_peers.len());
                for text in raw_peers {
                    peers.push(parse_peer(text)?);
                }
                let mut sender_weight_q16 = WEIGHT_UNITY_Q16;
                let mut seen_targets = HashSet::new();
                for text in raw_weights {
                    let (target, weight_q16) = parse_link_weight(text)?;
                    if !seen_targets.insert(target) {
                        return Err(Wrong(format!(
                            "`--link-weight` specified more than once for `{text}`"
                        )));
                    }
                    match target {
                        WeightTarget::Sender => sender_weight_q16 = weight_q16,
                        WeightTarget::Peer(id) => {
                            let Some(slot) = peers.iter_mut().find(|p| p.identity == id) else {
                                return Err(Wrong(format!(
                                    "`--link-weight` references peer `{id}` which is not in `--peer`"
                                )));
                            };
                            slot.weight_q16 = weight_q16;
                        }
                    }
                }
                let mut sync_settings = SyncSettings::standard(stream, identity);
                sync_settings.local_prior = local_prior;
                sync_settings.sender_prior = sender_prior;
                let net_cfg = NetConfig {
                    stream,
                    sync_mode: SyncMode::Peer,
                    sync_settings,
                    sender_weight_q16,
                    peers,
                    datagram,
                };
                net_cfg
                    .validate()
                    .map_err(|error| Wrong(error.to_string()))?;
                (Some(modal), net_cfg)
            }
        };

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
            identity,
            rate,
            channels,
            cycle,
            drift,
            lead,
            sync_mode,
            modal_regulation,
            net: net_config,
            fixed_path,
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
    let playback = playback(&config)?;
    let (counters, net_metrics, _metrics_server) = build_metrics(options)?;

    let socket = Socket::bind(config.listen)
        .map_err(|error| Wrong(format!("binding {}: {error}", config.listen)))?;
    // With port 0 the system chooses the port: say which, before anything
    // else, so that whoever started the program can send to it.
    let listening = socket
        .address()
        .map_err(|error| Wrong(format!("the address of the socket: {error}")))?;
    println!("listening {listening}");

    let (network_end, audio_end) = receive::link(SHIPPED_SIZES);
    let network = CountedNetwork {
        network: ReceiverNetwork::with_config(socket, network_end, &config.net),
        metrics: net_metrics,
    };
    // Reports carry what the frames needed, for the sender's choice of the
    // level, whether or not the delay of the path is measured from them.
    let reports = Some(Reporting {
        at_start: config.report_at_start,
        after: config.report_after,
        ..Reporting::USUAL
    });
    let audio: Audio = Audio::new(
        playback,
        audio_end,
        Intake {
            items: SHIPPED_INTAKE_ITEMS,
            reports,
        },
    );
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
    summarize(
        &stopped.network.network.counts(),
        stopped.network.network.sync_snapshot(),
        &seen,
    );
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

/// The receiver's playback as `config` sets it up.
fn playback(config: &Config) -> Result<Playback, Wrong> {
    let settings = Settings::shipped(
        config.stream,
        config.rate,
        config.channels,
        config.identity,
        config.modal_regulation,
    )
    .map_err(|error| Wrong(error.to_string()))?;
    let mut playback = Playback::new(&settings);
    if config.sync_mode == SyncMode::Hull
        && let Some(path) = config.fixed_path
    {
        playback.path(path);
    }
    Ok(playback)
}

/// Registers audio-thread and network-thread receiver Prometheus metrics and
/// starts the metrics HTTP server if `--metrics` was given.
fn build_metrics(options: &Options) -> Result<(Counters, NetworkMetrics, Option<Server>), Wrong> {
    let mut metrics = Metrics::new();
    let counters = Counters::new(&mut metrics)?;
    let net_metrics = NetworkMetrics::new(&mut metrics)?;
    let server = match options.one::<SocketAddr>("metrics")? {
        Some(address) => Some(
            metrics
                .serve(address)
                .map_err(|error| Wrong(format!("serving metrics at {address}: {error}")))?,
        ),
        None => None,
    };
    Ok((counters, net_metrics, server))
}

/// Audio-thread receiver counters and gauges.
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

/// Network-thread receiver and peer-sync Prometheus metrics (lock-free,
/// allocation-free, updated on the network thread outside the audio callback).
struct NetworkMetrics {
    packets: Tally,
    answers: Tally,
    reports: Tally,
    requests: Tally,
    dropped: Tally,
    peer_probes_sent: Tally,
    peer_probes_answered: Tally,
    peer_echoes_received: Tally,
    peer_relays_sent: Tally,
    peer_relays_received: Tally,
    sync_valid: Gauge,
    sync_peer_active: Gauge,
    sync_active_peers: Gauge,
    sync_epoch: Gauge,
    sync_common_std: FloatGauge,
    sync_diff_std: FloatGauge,
}

impl NetworkMetrics {
    fn new(metrics: &mut Metrics) -> Result<NetworkMetrics, Wrong> {
        let named = |error| Wrong(format!("registering metrics: {error:?}"));
        Ok(NetworkMetrics {
            packets: metrics
                .tally(
                    "unisono_receiver_packets_total",
                    "Audio packets handed to the audio thread.",
                )
                .map_err(named)?,
            answers: metrics
                .tally(
                    "unisono_receiver_answers_total",
                    "Sender report echoes processed by the receiver.",
                )
                .map_err(named)?,
            reports: metrics
                .tally(
                    "unisono_receiver_reports_total",
                    "Sender reports transmitted.",
                )
                .map_err(named)?,
            requests: metrics
                .tally(
                    "unisono_receiver_requests_total",
                    "Retransmission requests transmitted.",
                )
                .map_err(named)?,
            dropped: metrics
                .tally(
                    "unisono_receiver_dropped_total",
                    "Incoming datagrams or sync snapshots dropped due to ring pressure.",
                )
                .map_err(named)?,
            peer_probes_sent: metrics
                .tally(
                    "unisono_receiver_peer_probes_sent_total",
                    "Peer-to-peer clock probes transmitted.",
                )
                .map_err(named)?,
            peer_probes_answered: metrics
                .tally(
                    "unisono_receiver_peer_probes_answered_total",
                    "Incoming peer-to-peer clock probes answered with a PeerEcho.",
                )
                .map_err(named)?,
            peer_echoes_received: metrics
                .tally(
                    "unisono_receiver_peer_echoes_received_total",
                    "Valid PeerEcho responses received from configured peers.",
                )
                .map_err(named)?,
            peer_relays_sent: metrics
                .tally(
                    "unisono_receiver_peer_relays_sent_total",
                    "PeerRelay link-state packets transmitted to configured peers.",
                )
                .map_err(named)?,
            peer_relays_received: metrics
                .tally(
                    "unisono_receiver_peer_relays_received_total",
                    "Valid PeerRelay link-state packets received from configured peers.",
                )
                .map_err(named)?,
            sync_valid: metrics
                .int_gauge(
                    "unisono_receiver_sync_valid",
                    "1 when the receiver's peer/star sync snapshot holds a valid clock estimate.",
                )
                .map_err(named)?,
            sync_peer_active: metrics
                .int_gauge(
                    "unisono_receiver_sync_peer_active",
                    "1 when peer-assisted BLUE + modal synchronization is active, 0 in star mode.",
                )
                .map_err(named)?,
            sync_active_peers: metrics
                .int_gauge(
                    "unisono_receiver_sync_active_peers",
                    "Number of active peers contributing to the BLUE host graph.",
                )
                .map_err(named)?,
            sync_epoch: metrics
                .int_gauge(
                    "unisono_receiver_sync_epoch",
                    "Peer membership and clock-reset epoch counter.",
                )
                .map_err(named)?,
            sync_common_std: metrics
                .gauge(
                    "unisono_receiver_sync_common_std_seconds",
                    "Estimated common-mode (or star) measurement standard deviation, in seconds.",
                )
                .map_err(named)?,
            sync_diff_std: metrics
                .gauge(
                    "unisono_receiver_sync_diff_std_seconds",
                    "Estimated self differential-mode measurement standard deviation, in seconds.",
                )
                .map_err(named)?,
        })
    }

    fn update(&mut self, counts: &NetworkCounts, snapshot: Option<SyncSnapshot>) {
        self.packets.update(counts.packets);
        self.answers.update(counts.answers);
        self.reports.update(counts.reports);
        self.requests.update(counts.requests);
        self.dropped.update(counts.dropped);
        self.peer_probes_sent.update(counts.peer_probes_sent);
        self.peer_probes_answered
            .update(counts.peer_probes_answered);
        self.peer_echoes_received
            .update(counts.peer_echoes_received);
        self.peer_relays_sent.update(counts.peer_relays_sent);
        self.peer_relays_received
            .update(counts.peer_relays_received);
        if let Some(snap) = snapshot {
            self.sync_valid.set(i64::from(snap.valid));
            self.sync_peer_active.set(i64::from(snap.peer_active));
            self.sync_active_peers.set(i64::from(snap.active_peers));
            self.sync_epoch.set(i64::from(snap.epoch));
            #[allow(clippy::cast_precision_loss)]
            {
                self.sync_common_std
                    .set((snap.common_var_ns2 as f64).sqrt() * 1e-9);
                self.sync_diff_std
                    .set((snap.diff_var_ns2 as f64).sqrt() * 1e-9);
            }
        }
    }
}

/// Network loop wrapper updating lock-free [`NetworkMetrics`] on each turn.
struct CountedNetwork {
    network: ReceiverNetwork,
    metrics: NetworkMetrics,
}

impl NetworkLoop for CountedNetwork {
    fn turn(&mut self, milliseconds: i32) -> io::Result<()> {
        let result = self.network.turn(milliseconds);
        self.metrics
            .update(&self.network.counts(), self.network.sync_snapshot());
        result
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
fn summarize(counts: &NetworkCounts, snapshot: Option<SyncSnapshot>, seen: &Seen) {
    let active_peers = snapshot.map_or(0, |s| s.active_peers);
    println!(
        "received packets {} answers {} reports {} dropped {} played {} concealed {} jumps {} \
         delay {} requests {} unsent {} blocked {} peer_probes {} peer_relays {} active_peers {}",
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
        counts.peer_probes_sent,
        counts.peer_relays_sent,
        active_peers,
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
