// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Faithful discrete-event simulator driving the shipped [`unisono_runtime`]
//! pipeline (`CaptureEnd`, `SenderNetBridge`, `ReceiverNetBridge`,
//! `ShippedAudio` / `ReceiverAudio<256, 64, 8, 64>`) through real preallocated
//! SPSC rings and serialized UDP wire bytes over simulated IEEE 1139 clocks
//! and impaired links.
//!
//! The simulator treats both sender and receiver as black boxes: the sender
//! captures a deterministic bandlimited stereo probe waveform ([`crate::probe`])
//! and every canonical objective in `Unisono.Spec.Objectives` is scored
//! directly from the receiver's actual rendered `f32` PCM output via
//! [`ProbeDecoder`], without inspecting internal playback plans or held-frame
//! bitmaps.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, VecDeque};
use std::convert::Infallible;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use unisono_core::packet::{self, Format};
use unisono_core::player::{ModalRegulation, Regulation};
use unisono_core::sync::{SyncSettings, SyncSnapshot, WEIGHT_UNITY_Q16};
use unisono_runtime::audio::{Capture, Playback};
use unisono_runtime::level::Choice;
use unisono_runtime::pump::{
    SHIPPED_LEAD_NS, SHIPPED_REGULATION_GAIN, SHIPPED_REGULATION_LIMIT, SHIPPED_SILENCE_NS,
    SHIPPED_SLOPE_LIMIT, Settings as PlaybackSettings, ShippedPlayback,
};
use unisono_runtime::receive::{
    self, Intake, NetConfig, NetworkCounts, PeerConfig, ReceiverNetBridge, Reporting,
    SHIPPED_INTAKE_ITEMS, SHIPPED_SIZES, ShippedAudio, SyncMode,
};
use unisono_runtime::send::{
    self, CaptureEnd, MAX_DATAGRAM, SHIPPED_CAPTURE_BUFFERS, SHIPPED_KEPT_PACKETS, SHIPPED_SPAN_MS,
    SHIPPED_WINDOW_FRAMES, SenderCounts, SenderNetBridge, Settings as RuntimeSenderSettings,
};
use unisono_runtime::socket::{DatagramSink, SendStatus};

use crate::clock::{Course, OscillatorModel};
use crate::link::{Link, LinkModel, SharedContention, SharedContentionModel};
use crate::objectives::{ObjectiveRecorder, ObjectiveReport, ObjectiveWeights};
use crate::probe::{self, ProbeDecoder};
use crate::random::Generator;
use crate::{TrueTime, nanos_to_seconds, seconds_to_nanos};

/// Converts a `u64` frame count to `f64` (exact below `2^53`).
fn u64_to_f64(value: u64) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let float = value as f64;
    float
}

/// Converts a `usize` count to `f64`.
fn usize_to_f64(value: usize) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let float = value as f64;
    float
}

/// How a receiver learns how long a cycle of its device takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CycleLength {
    /// Exact cycle timestamps into `ReceiverPlayback`'s device line (`Device`).
    Measured,
    /// Forces nominal cycle duration by setting `device_range = 0` on
    /// `ReceiverPlayback` (fault-injection control).
    Nominal,
    /// Device timestamps perturbed uniformly within `[-err, +err]` ns into
    /// `ReceiverPlayback`'s 64-report least-squares line (`Device`).
    Fitted(i64),
}

/// How a receiver learns the minimum forward link delay from the sender.
#[derive(Clone, Copy, Debug)]
pub enum PathDelay {
    /// Explicitly configured fixed path delay (`ReceiverPlayback::path`) equal
    /// to the link's true minimum propagation delay; no reports sent.
    Told,
    /// Measured online via `Report` / `Echo` exchanges scheduled by
    /// `ReceiverAudio`'s built-in `ReportSchedule` under the given
    /// [`Reporting`] cadence.
    Measured(Reporting),
    /// Leaves path delay at zero with no reports sent (fault-injection
    /// control).
    Unknown,
}

/// Configuration of the simulated sender host and capture stream.
#[derive(Clone, Debug)]
pub struct SenderConfig {
    /// Host clock oscillator of the sender (node `0`).
    pub clock: OscillatorModel,
    /// Audio capture device oscillator.
    pub device: OscillatorModel,
    /// Stream identifier.
    pub stream: u16,
    /// Initial timeline identifier (defaults to `1_000`).
    pub timeline: u64,
    /// Initial sender clock identity carried in audio headers.
    pub clock_id: u32,
    /// Nominal audio sample rate in frames per second.
    pub rate: u32,
    /// Channel count.
    pub channels: u8,
    /// Wire sample encoding (`Signed16` or `Signed24`).
    pub format: Format,
    /// Frames per audio packet.
    pub packet_frames: u16,
    /// Initial playout latency level, in nanoseconds.
    pub level_ns: i64,
    /// Capture-to-send handoff delay after the last frame of a packet, in
    /// seconds.
    pub send_delay_s: f64,
    /// Lower-hull clock estimate span carried in headers, in milliseconds.
    pub span_ms: u32,
    /// Frames per lower-hull / need window carried in headers.
    pub window_frames: u32,
    /// Retransmission buffer depth in packets (`0` disables on-request
    /// retransmission).
    pub kept_packets: usize,
    /// Optional adaptive playout-level chooser configuration.
    pub choice: Option<Choice>,
    /// Standard deviation of Gaussian capture-device timestamp noise, in
    /// seconds.
    pub capture_timestamp_std_s: f64,
    /// Uncalibrated capture hardware latency, in seconds. Audio frame `f`
    /// physically enters the ADC at `device_time - hidden_latency_s` while the
    /// driver reports `device_time`.
    pub hidden_latency_s: f64,
    /// Software processing delay on the sender between kernel RX arrival (`T2`)
    /// and reading `clock::raw()` (`T3`) before replying to a report, in
    /// seconds.
    pub reply_processing_s: f64,
    /// Kernel/NIC send latency on the sender after `T3 = clock::raw()` is
    /// stamped and before an `Echo` reply departs onto the wire, in seconds.
    /// Models the real runtime (`send.rs`) reading `T3` prior to `socket.send`,
    /// which adds `-reply_send_latency_s / 2` bias to the four-timestamp edge.
    pub reply_send_latency_s: f64,
}

impl SenderConfig {
    /// Standard 48 kHz stereo 240-frame sender configuration using the exact
    /// shipped CLI/runtime defaults (`span = 2000 ms`, `window = 2400 frames`,
    /// `kept = 256` retransmission cache, adaptive [`Choice::shipped_default`]).
    ///
    /// # Panics
    ///
    /// Panics only if the compile-time shipped default parameters fail validation.
    #[must_use]
    pub fn standard(clock: OscillatorModel, device: OscillatorModel, level_ns: i64) -> Self {
        let choice = Choice::shipped_default(48_000, SHIPPED_WINDOW_FRAMES)
            .expect("shipped default choice is valid");
        Self {
            clock,
            device,
            stream: 1,
            timeline: 1_000,
            clock_id: 1,
            rate: 48_000,
            channels: 2,
            format: Format::Signed24,
            packet_frames: 240,
            level_ns,
            send_delay_s: 50e-6,
            span_ms: SHIPPED_SPAN_MS,
            window_frames: SHIPPED_WINDOW_FRAMES,
            kept_packets: SHIPPED_KEPT_PACKETS,
            choice: Some(choice),
            capture_timestamp_std_s: 0.0,
            hidden_latency_s: 0.0,
            reply_processing_s: 0.0,
            reply_send_latency_s: 0.0,
        }
    }

    /// Disables adaptive level control (`--level-choice off`), holding the
    /// playout level fixed at `level_ns`.
    #[must_use]
    pub fn with_fixed_level(mut self) -> Self {
        self.choice = None;
        self
    }

    /// Disables packet retransmission caching (`--protection off`).
    #[must_use]
    pub fn without_protection(mut self) -> Self {
        self.kept_packets = 0;
        self
    }

    /// Sets responder processing delay (`T2 -> T3`) and post-`T3` wire send
    /// latency on outgoing sender replies.
    #[must_use]
    pub fn with_reply_latency(mut self, processing_s: f64, send_latency_s: f64) -> Self {
        self.reply_processing_s = processing_s;
        self.reply_send_latency_s = send_latency_s;
        self
    }
}

/// Configuration of one receiver host (indexed `0..H`; node `h + 1` in link
/// matrices).
#[derive(Clone, Copy, Debug)]
pub struct HostConfig {
    /// Host clock oscillator.
    pub clock: OscillatorModel,
    /// Directed link from sender (node `0`) to this host.
    pub from_sender: LinkModel,
    /// Directed link from this host back to sender (node `0`).
    pub to_sender: LinkModel,
    /// Software processing delay between kernel RX arrival (`T2`) and reading
    /// `clock::raw()` (`T3`) when answering a `PeerProbe`, in seconds.
    pub reply_processing_s: f64,
    /// Kernel/NIC send latency after `T3 = clock::raw()` and before a
    /// `PeerEcho` reply leaves onto the wire, in seconds.
    pub reply_send_latency_s: f64,
}

impl HostConfig {
    /// Builds a host with zero responder processing and send latency.
    #[must_use]
    pub fn new(clock: OscillatorModel, from_sender: LinkModel, to_sender: LinkModel) -> Self {
        Self {
            clock,
            from_sender,
            to_sender,
            reply_processing_s: 0.0,
            reply_send_latency_s: 0.0,
        }
    }

    /// Sets responder processing delay (`T2 -> T3`) and post-`T3` wire send
    /// latency on outgoing `PeerEcho` replies from this host.
    #[must_use]
    pub fn with_reply_latency(mut self, processing_s: f64, send_latency_s: f64) -> Self {
        self.reply_processing_s = processing_s;
        self.reply_send_latency_s = send_latency_s;
        self
    }
}

/// Configuration of one simulated receiver speaker.
#[derive(Clone, Debug)]
pub struct ReceiverConfig {
    /// Index into `SceneConfig::hosts` (`0..H`).
    pub host: usize,
    /// Non-zero unique receiver identity (used by `Sync` and `Report`).
    pub identity: u64,
    /// Playback device oscillator.
    pub device: OscillatorModel,
    /// Audio output frames per playback cycle.
    pub cycle_frames: u32,
    /// Scheduling lead before a cycle's first frame leaves the DAC, in
    /// seconds (defaults to [`SHIPPED_LEAD_NS`] = `4 ms`).
    pub lead_s: f64,
    /// Clock synchronization mode (`SyncMode::Peer` or `SyncMode::Hull`).
    pub sync_mode: SyncMode,
    /// `Sync` settings used when `sync_mode == SyncMode::Peer` (defaults to
    /// `SyncSettings::standard`, which uses `NoisePrior::CONSUMER_QUARTZ`).
    pub sync_settings: SyncSettings,
    /// Q16 link weight multiplier for the direct sender link.
    pub sender_weight_q16: u32,
    /// Configured peer speakers as `(receiver_index, weight_q16)`.
    pub peers: Vec<(usize, u32)>,
    /// Legacy single-mode regulation (used in `Hull` mode).
    pub regulation: Regulation,
    /// Modal regulation (used in `Peer` mode; defaults to
    /// `ModalRegulation::lipsync` when `None` and `sync_mode == Peer`).
    pub modal_regulation: Option<ModalRegulation>,
    /// Silence duration before adopting a new timeline, in nanoseconds.
    pub silence_ns: i64,
    /// Lower-hull clock slope bound, in ppb.
    pub slope_limit: i64,
    /// How this receiver learns its forward path delay.
    pub path: PathDelay,
    /// How this receiver learns its playback cycle length.
    pub cycle_length: CycleLength,
    /// Optional single device stall `(at_cycle, duration_s)` for fault tests.
    pub stands_still: Option<(u64, f64)>,
    /// Uncalibrated DAC/output hardware latency, in seconds. The driver
    /// reports `leaves_s` while sound physically exits the converter at
    /// `leaves_s + hidden_latency_s`.
    pub hidden_latency_s: f64,
    /// Whether to retain rendered PCM and black-box decoded source positions
    /// for every cycle.
    pub record_pcm: bool,
}

impl ReceiverConfig {
    /// Creates a `SyncMode::Peer` receiver configuration on `host` using the
    /// exact shipped CLI/runtime defaults (`lead = 4 ms`,
    /// `NoisePrior::CONSUMER_QUARTZ`, `ModalRegulation::lipsync`,
    /// `Reporting::USUAL`) and zero initial peers (Star mode until peers are
    /// added).
    #[must_use]
    pub fn peer(host: usize, identity: u64, device: OscillatorModel) -> Self {
        let sync_settings = SyncSettings::standard(1, identity);
        Self {
            host,
            identity,
            device,
            cycle_frames: 256,
            lead_s: nanos_to_seconds(SHIPPED_LEAD_NS),
            sync_mode: SyncMode::Peer,
            sync_settings,
            sender_weight_q16: WEIGHT_UNITY_Q16,
            peers: Vec::new(),
            regulation: Regulation {
                gain: SHIPPED_REGULATION_GAIN,
                limit: SHIPPED_REGULATION_LIMIT,
                jump: 240,
            },
            modal_regulation: Some(ModalRegulation::lipsync(SHIPPED_REGULATION_LIMIT, 240)),
            silence_ns: SHIPPED_SILENCE_NS,
            slope_limit: SHIPPED_SLOPE_LIMIT,
            path: PathDelay::Measured(Reporting::USUAL),
            cycle_length: CycleLength::Measured,
            stands_still: None,
            hidden_latency_s: 0.0,
            record_pcm: false,
        }
    }

    /// Creates a legacy `SyncMode::Hull` receiver configuration on `host`.
    #[must_use]
    pub fn hull(host: usize, identity: u64, device: OscillatorModel) -> Self {
        let mut cfg = Self::peer(host, identity, device);
        cfg.sync_mode = SyncMode::Hull;
        cfg.modal_regulation = None;
        cfg
    }
}

/// Complete scenario specification for [`Scene`].
#[derive(Clone, Debug)]
pub struct SceneConfig {
    /// Sender host and stream configuration.
    pub sender: SenderConfig,
    /// Receiver hosts (node `h + 1` in the link matrix).
    pub hosts: Vec<HostConfig>,
    /// Receiver speakers attached to `hosts`.
    pub receivers: Vec<ReceiverConfig>,
    /// Default directed link model for distinct receiver-to-receiver pairs.
    pub peer_link: LinkModel,
    /// Explicit directed link overrides `(src_node, dst_node, model)` where
    /// node `0` is the sender and node `h + 1` is receiver host `h`.
    pub link_overrides: Vec<(usize, usize, LinkModel)>,
    /// Optional shared TX/RX and wireless AP contention model over all
    /// `hosts.len() + 1` nodes.
    pub contention: Option<SharedContentionModel>,
    /// Optional canonical objective scoring window `[start_s, end_s)` in true
    /// seconds.
    pub objective_window: Option<(f64, f64)>,
    /// Objective weights passed to [`ObjectiveRecorder`].
    pub objective_weights: ObjectiveWeights,
    /// Fixed application target latency `L*` (seconds) for `tracking_s2`
    /// (`World.target`); defaults to `sender.level_ns * 1e-9` and never tracks
    /// adaptive changes to the sender's current playout level.
    pub target_latency_s: Option<f64>,
    /// When `true` (default), speakers co-located on the same receiver host
    /// receive the same NIC arrival time for a single sender audio packet
    /// emission.
    pub share_same_host_audio_arrival: bool,
    /// When `true` (default), decodes every cycle from `t = 0` into per-speaker
    /// [`Trace`] diagnostics. Set to `false` on long multi-seed steady-state
    /// runs to skip decoding cycles strictly earlier than `window_start - 1 s`
    /// (the real production DSP still runs on every cycle from `t = 0`).
    pub record_trace: bool,
}

impl SceneConfig {
    /// Builds a basic [`SceneConfig`] with `peer_link = LinkModel::WIRED_CALM`
    /// and no shared contention or objective scoring window.
    #[must_use]
    pub fn new(
        sender: SenderConfig,
        hosts: Vec<HostConfig>,
        receivers: Vec<ReceiverConfig>,
    ) -> Self {
        Self {
            sender,
            hosts,
            receivers,
            peer_link: LinkModel::WIRED_CALM,
            link_overrides: Vec::new(),
            contention: None,
            objective_window: None,
            objective_weights: ObjectiveWeights::ZERO,
            target_latency_s: None,
            share_same_host_audio_arrival: true,
            record_trace: true,
        }
    }
}

/// Per-cycle timing trace for one receiver (used by timing regression tests).
#[derive(Clone, Debug, Default)]
pub struct Trace {
    /// `(true_out_time_s, timing_error_s)` decoded from rendered PCM for each
    /// cycle with at least one valid probe sample (positive error = playing
    /// late relative to `capture + level`).
    pub errors: Vec<(f64, f64)>,
    /// True acoustic output times (seconds) of cycles whose playback jumped.
    pub jumps: Vec<f64>,
    /// Number of silent/idle playback cycles (`played == 0`).
    pub idle_cycles: u64,
    /// Total stream frames marked held by `ReceiverPlayback` diagnostics.
    pub held: u64,
    /// Total stream frames marked absent/concealed by `ReceiverPlayback`
    /// diagnostics.
    pub absent: u64,
}

/// Recorded rendered PCM output and black-box decoded source frame positions
/// from one playback cycle.
#[derive(Clone, Debug)]
pub struct RecordedCycle {
    /// True acoustic output time of the cycle's first frame, in seconds.
    pub out_start_s: f64,
    /// True acoustic output time of the next cycle's first frame, in seconds.
    pub out_end_s: f64,
    /// Black-box decoded global source frame position (`Option<f64>`) per
    /// output frame in this cycle.
    pub decoded: Vec<Option<f64>>,
    /// Channel-0 output PCM samples rendered by `ShippedAudio::cycle`.
    pub channel0: Vec<f32>,
}

/// Outgoing datagram collected from a [`SenderNetBridge`] or
/// [`ReceiverNetBridge`] during a simulation event.
#[derive(Clone, Debug)]
struct SentDatagram {
    to: SocketAddr,
    bytes: Vec<u8>,
    tag: Option<u64>,
}

/// In-memory [`DatagramSink`] buffering outgoing wire packets for simulated
/// link delivery.
#[derive(Default)]
struct SimSink {
    sent: Vec<SentDatagram>,
}

impl DatagramSink for SimSink {
    type Error = Infallible;

    fn send(
        &mut self,
        to: SocketAddr,
        bytes: &[u8],
        tag: Option<u64>,
    ) -> Result<SendStatus, Infallible> {
        self.sent.push(SentDatagram {
            to,
            bytes: bytes.to_vec(),
            tag,
        });
        Ok(SendStatus::Sent)
    }
}

/// Discrete event processed by [`Scene`].
enum Event {
    /// Sender capture block handoff for packet emission.
    Capture { epoch: u64, block_index: u64 },
    /// Deferred wire emission of sender replies after `reply_processing_s +
    /// reply_send_latency_s` so `Link::deliver` is always called in strict
    /// chronological order.
    EmitFromSender { epoch: u64, sent: Vec<SentDatagram> },
    /// Sender TX departure timestamp arriving back from the NIC.
    SenderDeparture { epoch: u64, tag: u64, tx_ns: i64 },
    /// Datagram arriving at the sender socket.
    DeliverToSender {
        from_node: usize,
        from_addr: SocketAddr,
        bytes: Vec<u8>,
    },
    /// Deferred wire emission of receiver replies after `reply_processing_s +
    /// reply_send_latency_s`.
    EmitFromReceiver {
        speaker: usize,
        epoch: u64,
        sent: Vec<SentDatagram>,
    },
    /// Datagram arriving at a receiver speaker socket.
    DeliverToReceiver {
        speaker: usize,
        from_node: usize,
        from_addr: SocketAddr,
        bytes: Vec<u8>,
    },
    /// Receiver TX departure timestamp arriving back from the NIC.
    ReceiverDeparture {
        speaker: usize,
        epoch: u64,
        tag: u64,
        tx_ns: i64,
    },
    /// Periodic network engine wake for a receiver speaker.
    ReceiverNetStep {
        speaker: usize,
        epoch: u64,
        generation: u64,
    },
    /// Playback cycle callback for a receiver speaker.
    PlayCycle {
        speaker: usize,
        epoch: u64,
        cycle: u64,
    },
}

/// Runtime state of one simulated receiver speaker driving the shipped
/// `ReceiverNetBridge` + `ShippedAudio` SPSC-ring pipeline.
struct Speaker {
    config: ReceiverConfig,
    addr: SocketAddr,
    audio: ShippedAudio,
    net: ReceiverNetBridge,
    device: Course,
    device_noise_rng: Generator,
    pcm_buf: Vec<f32>,
    decoder: ProbeDecoder,
    recorded_cycles: Vec<RecordedCycle>,
    trace: Trace,
    epoch: u64,
    net_wake_gen: u64,
    next_cycle_index: u64,
    device_frame_cursor: u64,
}

impl Speaker {
    /// True time (seconds) when playback device frame `frame` is scheduled to
    /// leave the driver (before adding uncalibrated `hidden_latency_s`).
    fn leaves_s(&mut self, frame: f64, rate: f64) -> f64 {
        let counted = self.device.when_seconds(frame / rate);
        match self.config.stands_still {
            Some((cycle, seconds))
                if frame
                    >= u64_to_f64(cycle.saturating_mul(u64::from(self.config.cycle_frames))) =>
            {
                counted + seconds
            }
            _ => counted,
        }
    }
}

/// Synthetic sender socket address (`10.0.0.1:9000`).
fn sender_addr() -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1)), 9_000)
}

/// Synthetic receiver socket address (`10.0.<host>.<speaker>:10000 + speaker`).
fn receiver_addr(host: usize, speaker: usize) -> SocketAddr {
    let h = u8::try_from((host + 1).min(254)).unwrap_or(254);
    let s = u8::try_from((speaker + 1).min(254)).unwrap_or(254);
    let port = u16::try_from(10_000 + speaker).unwrap_or(65_000);
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, h, s)), port)
}

/// Builds a validated [`ShippedAudio`] + [`ReceiverNetBridge`] pair wired via
/// the shipped SPSC rings ([`SHIPPED_SIZES`], [`SHIPPED_INTAKE_ITEMS`]).
fn build_receiver_parts(
    sender_cfg: &SenderConfig,
    rec_cfg: &ReceiverConfig,
    all_addrs: &[(u64, SocketAddr)],
    true_min_delay_ns: i64,
) -> (ShippedAudio, ReceiverNetBridge) {
    let jump = (sender_cfg.rate / 200).max(1);
    let modal_regulation = match rec_cfg.sync_mode {
        SyncMode::Hull => None,
        SyncMode::Peer => Some(
            rec_cfg
                .modal_regulation
                .unwrap_or_else(|| ModalRegulation::lipsync(SHIPPED_REGULATION_LIMIT, jump)),
        ),
    };
    let mut pb_settings = PlaybackSettings::shipped(
        sender_cfg.stream,
        sender_cfg.rate,
        sender_cfg.channels,
        rec_cfg.identity,
        modal_regulation,
    )
    .expect("shipped playback settings must validate");
    pb_settings.silence = rec_cfg.silence_ns;
    pb_settings.slope_limit = rec_cfg.slope_limit;
    pb_settings.regulation = rec_cfg.regulation;
    if matches!(rec_cfg.cycle_length, CycleLength::Nominal) {
        pb_settings.device_range = 0;
    }
    pb_settings
        .validate()
        .expect("receiver playback settings failed validation");

    let mut playback = ShippedPlayback::new(&pb_settings);
    if matches!(rec_cfg.path, PathDelay::Told) {
        playback.path(true_min_delay_ns);
    }

    let mut sync_settings = rec_cfg.sync_settings;
    sync_settings.stream = sender_cfg.stream;
    sync_settings.identity = rec_cfg.identity;

    let peers = match rec_cfg.sync_mode {
        SyncMode::Hull => Vec::new(),
        SyncMode::Peer => rec_cfg
            .peers
            .iter()
            .filter_map(|&(peer_idx, weight)| {
                all_addrs.get(peer_idx).map(|&(id, addr)| PeerConfig {
                    identity: id,
                    address: addr,
                    weight_q16: if weight == 0 {
                        WEIGHT_UNITY_Q16
                    } else {
                        weight
                    },
                })
            })
            .collect(),
    };
    let net_config = NetConfig {
        stream: sender_cfg.stream,
        sync_mode: rec_cfg.sync_mode,
        sync_settings,
        sender_weight_q16: if rec_cfg.sender_weight_q16 == 0 {
            WEIGHT_UNITY_Q16
        } else {
            rec_cfg.sender_weight_q16
        },
        peers,
        datagram: MAX_DATAGRAM,
    };
    net_config
        .validate()
        .expect("receiver net config failed validation");

    let (net_end, audio_end) = receive::link(SHIPPED_SIZES);
    let reports = match rec_cfg.path {
        PathDelay::Measured(reporting) => Some(reporting),
        PathDelay::Told | PathDelay::Unknown => None,
    };
    let audio = ShippedAudio::new(
        playback,
        audio_end,
        Intake {
            items: SHIPPED_INTAKE_ITEMS,
            reports,
        },
    );
    let net = ReceiverNetBridge::new(net_end, &net_config);
    (audio, net)
}

/// Builds a validated [`CaptureEnd`] + [`SenderNetBridge`] pair wired via the
/// shipped capture SPSC ring ([`SHIPPED_CAPTURE_BUFFERS`]).
fn build_sender_parts(
    cfg: &SenderConfig,
    timeline: u64,
    clock_id: u32,
    level_ns: i64,
    receiver_addrs: &[SocketAddr],
) -> (CaptureEnd, SenderNetBridge) {
    let mut runtime_settings = RuntimeSenderSettings::shipped(
        cfg.stream,
        cfg.rate,
        cfg.channels,
        cfg.format,
        cfg.packet_frames,
        level_ns,
        timeline,
        clock_id,
        receiver_addrs.to_vec(),
        cfg.choice.is_some(),
        cfg.kept_packets > 0,
    )
    .expect("shipped sender settings must validate");
    runtime_settings.stream.span = cfg.span_ms;
    runtime_settings.stream.window = cfg.window_frames;
    runtime_settings.kept = cfg.kept_packets;
    runtime_settings.choice = cfg.choice;
    runtime_settings
        .validate()
        .expect("sender settings failed validation");

    let (capture_end, sender_end) = send::link(
        SHIPPED_CAPTURE_BUFFERS,
        usize::from(cfg.packet_frames),
        usize::from(cfg.channels),
    );
    let bridge = SenderNetBridge::new(sender_end, runtime_settings);
    (capture_end, bridge)
}

/// Faithful multi-host discrete-event simulation scene driving shipped
/// `unisono-runtime` SPSC-ring pipelines over real serialized UDP datagrams
/// and scoring black-box PCM output via [`ProbeDecoder`].
pub struct Scene {
    config: SceneConfig,
    /// Host clocks: index `0` is sender, index `h + 1` is receiver host `h`.
    host_clocks: Vec<Course>,
    /// Directed link matrix `[src_node][dst_node]` over `0..=H`.
    links: Vec<Vec<Link>>,
    /// Partition flags `[src_node][dst_node]` (drops all packets when `true`).
    partitioned: Vec<Vec<bool>>,
    /// Optional shared TX/RX and wireless AP contention process.
    contention: Option<SharedContention>,
    /// Sender audio capture device oscillator.
    sender_device: Course,
    sender_stamp_rng: Generator,
    capture_end: CaptureEnd,
    sender_bridge: SenderNetBridge,
    sender_addr: SocketAddr,
    sender_epoch: u64,
    sender_timeline: u64,
    sender_clock_id: u32,
    /// Next capture frame index on `sender_device` (monotonic across restarts).
    sender_capture_cursor: u64,
    /// Preallocated capture PCM buffer reused across `on_capture` calls.
    capture_buf: Vec<f32>,
    /// Rolling true physical capture times for `Trace` evaluation (populated
    /// only when `config.record_trace` is `true`).
    capture_times: VecDeque<f64>,
    capture_times_base: u64,
    max_capture_history: usize,
    /// Monotonic count of captured frames across the simulation.
    global_captured_frames: u64,
    /// Receiver speakers.
    speakers: Vec<Speaker>,
    /// Address lookup: receiver `SocketAddr` -> speaker index `0..R`.
    addr_to_speaker: HashMap<SocketAddr, usize>,
    /// All receiver `(identity, SocketAddr)` pairs (cached for restarts).
    speaker_addrs: Vec<(u64, SocketAddr)>,
    /// True minimum forward delay (ns) per receiver host.
    host_true_min_delay_ns: Vec<i64>,
    /// Optional canonical objective recorder.
    objectives: Option<ObjectiveRecorder>,
    /// Event priority queue ordered by `(TrueTime, tie_breaker)`.
    events: BinaryHeap<(Reverse<TrueTime>, Reverse<u64>, usize)>,
    event_payloads: Vec<Option<Event>>,
    free_slots: Vec<usize>,
    next_order: u64,
    /// Current simulation true time.
    now: TrueTime,
    /// Seeded generator for dynamic restarts/faults.
    rng: Generator,
}

/// Builds the directed link matrix and per-host sender minimum delays.
fn build_link_matrix(config: &SceneConfig, generator: &Generator) -> (Vec<Vec<Link>>, Vec<i64>) {
    let host_count = config.hosts.len();
    let node_count = host_count + 1;
    let mut link_models = vec![vec![config.peer_link; node_count]; node_count];
    for (node, row) in link_models.iter_mut().enumerate() {
        row[node] = LinkModel {
            minimum: 10e-6,
            ..LinkModel::IDEAL
        };
    }
    for (h, host_cfg) in config.hosts.iter().enumerate() {
        let node = h + 1;
        link_models[0][node] = host_cfg.from_sender;
        link_models[node][0] = host_cfg.to_sender;
    }
    for &(src, dst, model) in &config.link_overrides {
        if src < node_count && dst < node_count {
            link_models[src][dst] = model;
        }
    }
    let mut links = Vec::with_capacity(node_count);
    for (src, row) in link_models.iter().enumerate() {
        let mut dst_links = Vec::with_capacity(node_count);
        for (dst, &model) in row.iter().enumerate() {
            let seed =
                10_000 + u64::try_from(src).unwrap_or(0) * 1_000 + u64::try_from(dst).unwrap_or(0);
            dst_links.push(Link::new(model, generator.fork(seed)));
        }
        links.push(dst_links);
    }
    let host_true_min_delay_ns = (0..host_count)
        .map(|h| seconds_to_nanos(link_models[0][h + 1].minimum))
        .collect();
    (links, host_true_min_delay_ns)
}

/// Builds initial speaker runtime states from `config`.
fn build_speakers(
    config: &SceneConfig,
    speaker_addrs: &[(u64, SocketAddr)],
    host_true_min_delay_ns: &[i64],
    generator: &Generator,
) -> Vec<Speaker> {
    let mut speakers = Vec::with_capacity(config.receivers.len());
    for (idx, rec_cfg) in config.receivers.iter().enumerate() {
        let min_delay_ns = host_true_min_delay_ns
            .get(rec_cfg.host)
            .copied()
            .unwrap_or(0);
        let (audio, net) =
            build_receiver_parts(&config.sender, rec_cfg, speaker_addrs, min_delay_ns);
        let pcm_len = (rec_cfg.cycle_frames as usize) * usize::from(config.sender.channels);
        speakers.push(Speaker {
            config: rec_cfg.clone(),
            addr: speaker_addrs[idx].1,
            audio,
            net,
            device: Course::new(
                rec_cfg.device,
                generator.fork(20_000 + u64::try_from(idx).unwrap_or(0)),
            ),
            device_noise_rng: generator.fork(30_000 + u64::try_from(idx).unwrap_or(0)),
            pcm_buf: vec![0.0; pcm_len],
            decoder: ProbeDecoder::new(),
            recorded_cycles: Vec::new(),
            trace: Trace::default(),
            epoch: 0,
            net_wake_gen: 0,
            next_cycle_index: 0,
            device_frame_cursor: 0,
        });
    }
    speakers
}

/// Builds the host clock courses (node 0 = sender, nodes `1..=H` = receiver
/// hosts).
fn build_host_clocks(config: &SceneConfig, generator: &Generator) -> Vec<Course> {
    let mut clocks = Vec::with_capacity(config.hosts.len() + 1);
    clocks.push(Course::new(config.sender.clock, generator.fork(1)));
    for (h, host_cfg) in config.hosts.iter().enumerate() {
        clocks.push(Course::new(
            host_cfg.clock,
            generator.fork(100 + u64::try_from(h).unwrap_or(0)),
        ));
    }
    clocks
}

impl Scene {
    /// Creates a new faithful discrete-event simulation scene from `config`
    /// and deterministic PRNG `generator`.
    #[must_use]
    pub fn new(config: SceneConfig, generator: &Generator) -> Scene {
        let node_count = config.hosts.len() + 1;
        let host_clocks = build_host_clocks(&config, generator);

        let (links, host_true_min_delay_ns) = build_link_matrix(&config, generator);
        let contention = config
            .contention
            .clone()
            .map(|m| SharedContention::new(m, generator.fork(50_000)));

        let speaker_addrs: Vec<(u64, SocketAddr)> = config
            .receivers
            .iter()
            .enumerate()
            .map(|(idx, r)| (r.identity, receiver_addr(r.host, idx)))
            .collect();
        let addr_to_speaker: HashMap<SocketAddr, usize> = speaker_addrs
            .iter()
            .enumerate()
            .map(|(idx, &(_, addr))| (addr, idx))
            .collect();
        let raw_rx_addrs: Vec<SocketAddr> = speaker_addrs.iter().map(|&(_, a)| a).collect();

        let (capture_end, sender_bridge) = build_sender_parts(
            &config.sender,
            config.sender.timeline,
            config.sender.clock_id,
            config.sender.level_ns,
            &raw_rx_addrs,
        );
        let capture_samples =
            usize::from(config.sender.packet_frames) * usize::from(config.sender.channels);
        let max_history = (config.sender.rate as usize).saturating_mul(4).max(65_536);
        let speakers = build_speakers(&config, &speaker_addrs, &host_true_min_delay_ns, generator);

        let objectives = config.objective_window.map(|(start_s, end_s)| {
            let cycle_frames = config
                .receivers
                .first()
                .map_or(256, |r| r.cycle_frames as usize);
            ObjectiveRecorder::new(
                config.receivers.len(),
                start_s,
                end_s,
                cycle_frames,
                config.objective_weights,
            )
            .with_max_buffered_frames(max_history)
        });

        let initial_timeline = config.sender.timeline;
        let initial_clock_id = config.sender.clock_id;
        let sender_device = Course::new(config.sender.device, generator.fork(2));
        let mut scene = Scene {
            config,
            host_clocks,
            links,
            partitioned: vec![vec![false; node_count]; node_count],
            contention,
            sender_device,
            sender_stamp_rng: generator.fork(3),
            capture_end,
            sender_bridge,
            sender_addr: sender_addr(),
            sender_epoch: 0,
            sender_timeline: initial_timeline,
            sender_clock_id: initial_clock_id,
            sender_capture_cursor: 0,
            capture_buf: vec![0.0; capture_samples],
            capture_times: VecDeque::new(),
            capture_times_base: 0,
            max_capture_history: max_history,
            global_captured_frames: 0,
            speakers,
            addr_to_speaker,
            speaker_addrs,
            host_true_min_delay_ns,
            objectives,
            events: BinaryHeap::new(),
            event_payloads: Vec::new(),
            free_slots: Vec::new(),
            next_order: 0,
            now: TrueTime::ZERO,
            rng: generator.fork(90_000),
        };
        scene.schedule_initial_events();
        scene
    }

    /// Schedules the initial capture block, speaker playback cycles, and
    /// staggered initial network-engine wakes.
    fn schedule_initial_events(&mut self) {
        self.schedule_capture(0, 0);
        for idx in 0..self.speakers.len() {
            self.schedule_play_cycle(idx, 0);
            // Stagger initial network engine wake by 1 ms per speaker so
            // initial peer probes do not artificially collide at t = 0.
            let initial_wake = TrueTime(i64::try_from(idx + 1).unwrap_or(1) * 1_000_000);
            self.schedule_net_step_at(idx, initial_wake);
        }
    }

    /// Advances the simulation up to true time `until`.
    pub fn run(&mut self, until: TrueTime) {
        while let Some(&(Reverse(at), _, _)) = self.events.peek() {
            if at > until {
                break;
            }
            let Some((_, _, slot)) = self.events.pop() else {
                break;
            };
            let Some(event) = self.event_payloads[slot].take() else {
                continue;
            };
            self.free_slots.push(slot);
            self.now = at;
            self.dispatch(at, event);
        }
        self.now = self.now.max(until);
    }

    /// Current true simulation time.
    #[must_use]
    pub fn now(&self) -> TrueTime {
        self.now
    }

    /// Restarts the sender on a new timeline (`timeline + 1`) while keeping
    /// the same host clock and `clock_id`.
    pub fn restart_sender(&mut self) {
        self.sender_epoch += 1;
        self.sender_timeline = self.sender_timeline.wrapping_add(1);
        let level_ns = self.sender_bridge.sender().current_level();
        let raw_rx_addrs: Vec<SocketAddr> = self.speaker_addrs.iter().map(|&(_, a)| a).collect();
        let (capture_end, sender_bridge) = build_sender_parts(
            &self.config.sender,
            self.sender_timeline,
            self.sender_clock_id,
            level_ns,
            &raw_rx_addrs,
        );
        self.capture_end = capture_end;
        self.sender_bridge = sender_bridge;
        let rate = f64::from(self.config.sender.rate);
        let current_frame_f = (self.sender_device.read_seconds(self.now.seconds()) * rate)
            .ceil()
            .max(0.0);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let next_frame = (current_frame_f as u64).max(self.sender_capture_cursor);
        self.sender_capture_cursor = next_frame;
        self.schedule_capture(self.sender_epoch, 0);
    }

    /// Simulates a sender host reboot: replaces the sender's host clock with
    /// `(new_offset_s, new_ppm)` and increments `clock_id`, then restarts on a
    /// new timeline.
    pub fn reboot_sender(&mut self, new_offset_s: f64, new_ppm: f64) {
        let mut model = self.config.sender.clock;
        model.offset = new_offset_s;
        model.frequency = new_ppm * 1e-6;
        let fork = self.rng.fork(self.sender_epoch + 1);
        self.host_clocks[0] = Course::new(model, fork);
        self.sender_clock_id = self.sender_clock_id.wrapping_add(1);
        self.restart_sender();
    }

    /// Restarts receiver speaker `speaker`, resetting its playback pipeline,
    /// SPSC rings, sync engine, and output decoder while preserving its host
    /// clock and playback DAC oscillator.
    pub fn restart_receiver(&mut self, speaker: usize) {
        let Some(sp) = self.speakers.get_mut(speaker) else {
            return;
        };
        sp.epoch += 1;
        sp.net_wake_gen += 1;
        let min_delay_ns = self
            .host_true_min_delay_ns
            .get(sp.config.host)
            .copied()
            .unwrap_or(0);
        let (audio, net) = build_receiver_parts(
            &self.config.sender,
            &sp.config,
            &self.speaker_addrs,
            min_delay_ns,
        );
        sp.audio = audio;
        sp.net = net;
        sp.decoder.reset();
        let next_cycle = sp.next_cycle_index;
        let wake_at = self.now.plus_seconds(1e-3);
        self.schedule_play_cycle(speaker, next_cycle);
        self.schedule_net_step_at(speaker, wake_at);
    }

    /// Enables or clears a directed link partition between `src_node` and
    /// `dst_node` (node `0` = sender, node `h + 1` = receiver host `h`).
    pub fn set_link_partitioned(&mut self, src_node: usize, dst_node: usize, is_partitioned: bool) {
        if let Some(row) = self.partitioned.get_mut(src_node)
            && let Some(cell) = row.get_mut(dst_node)
        {
            *cell = is_partitioned;
        }
    }

    /// Applies an instantaneous frequency step of `delta_ppm` ppm to host node
    /// `node` (`0` = sender, `h + 1` = receiver host `h`) at the current true
    /// simulation time.
    pub fn step_host_frequency(&mut self, node: usize, delta_ppm: f64) {
        if let Some(clock) = self.host_clocks.get_mut(node) {
            clock.step_frequency(self.now, delta_ppm);
        }
    }

    /// Timeline currently followed by speaker `speaker`, if any.
    #[must_use]
    pub fn followed(&self, speaker: usize) -> Option<u64> {
        self.speakers
            .get(speaker)
            .and_then(|sp| sp.audio.playback().receiver().timeline())
    }

    /// Current estimated forward path delay (ns) on speaker `speaker`.
    #[must_use]
    pub fn delay(&self, speaker: usize) -> Option<i64> {
        self.speakers
            .get(speaker)
            .map(|sp| sp.audio.playback().receiver().delay())
    }

    /// Latest [`SyncSnapshot`] from speaker `speaker`'s network bridge, or
    /// `None` in legacy hull mode.
    #[must_use]
    pub fn sync_snapshot(&self, speaker: usize) -> Option<SyncSnapshot> {
        self.speakers
            .get(speaker)
            .and_then(|sp| sp.net.sync_snapshot())
    }

    /// Cumulative network counters for speaker `speaker`.
    #[must_use]
    pub fn network_counts(&self, speaker: usize) -> Option<NetworkCounts> {
        self.speakers.get(speaker).map(|sp| sp.net.counts())
    }

    /// Cumulative sender network counters.
    #[must_use]
    pub fn sender_counts(&self) -> SenderCounts {
        self.sender_bridge.counts()
    }

    /// Current sender playout latency level, in nanoseconds.
    #[must_use]
    pub fn sender_level_ns(&self) -> i64 {
        self.sender_bridge.sender().current_level()
    }

    /// Per-speaker timing traces recorded over the simulation.
    #[must_use]
    pub fn traces(&self) -> Vec<&Trace> {
        self.speakers.iter().map(|sp| &sp.trace).collect()
    }

    /// Recorded rendered PCM and decoded frame positions for speaker `speaker`.
    #[must_use]
    pub fn recorded_cycles(&self, speaker: usize) -> &[RecordedCycle] {
        self.speakers
            .get(speaker)
            .map_or(&[], |sp| sp.recorded_cycles.as_slice())
    }

    /// Finalizes and returns the canonical [`ObjectiveReport`] if
    /// `SceneConfig::objective_window` was set.
    #[must_use]
    pub fn finish_objectives(self) -> Option<ObjectiveReport> {
        self.objectives.map(ObjectiveRecorder::finish)
    }

    /// Linearly interpolates the true physical capture time of fractional
    /// global source frame `position` from `self.capture_times`.
    fn capture_time_at(&self, position: f64) -> Option<f64> {
        if self.capture_times.is_empty() || !position.is_finite() {
            return None;
        }
        let base_f = u64_to_f64(self.capture_times_base);
        let nominal_dt = 1.0 / f64::from(self.config.sender.rate);
        if position < base_f {
            return Some(self.capture_times[0] + (position - base_f) * nominal_dt);
        }
        let floored = position.floor();
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let frame_u64 = floored as u64;
        let frac = position - floored;
        let rel = usize::try_from(frame_u64.saturating_sub(self.capture_times_base))
            .unwrap_or(usize::MAX);
        if rel + 1 < self.capture_times.len() {
            let t0 = self.capture_times[rel];
            let t1 = self.capture_times[rel + 1];
            Some(t0 + frac * (t1 - t0))
        } else if rel < self.capture_times.len() && frac.abs() <= 1e-15 {
            Some(self.capture_times[rel])
        } else {
            let last = self.capture_times.len() - 1;
            let last_f = base_f + usize_to_f64(last);
            let step = if last >= 1 {
                self.capture_times[last] - self.capture_times[last - 1]
            } else {
                nominal_dt
            };
            Some(self.capture_times[last] + (position - last_f) * step)
        }
    }

    fn push_event(&mut self, at: TrueTime, event: Event) {
        let slot = if let Some(free) = self.free_slots.pop() {
            self.event_payloads[free] = Some(event);
            free
        } else {
            let idx = self.event_payloads.len();
            self.event_payloads.push(Some(event));
            idx
        };
        let order = self.next_order;
        self.next_order += 1;
        self.events.push((Reverse(at), Reverse(order), slot));
    }

    fn schedule_capture(&mut self, epoch: u64, block_index: u64) {
        let packet_frames = u64::from(self.config.sender.packet_frames);
        let rate = f64::from(self.config.sender.rate);
        let last_frame = self
            .sender_capture_cursor
            .saturating_add(packet_frames.saturating_sub(1));
        let handoff_s = self
            .sender_device
            .when_seconds(u64_to_f64(last_frame) / rate)
            + self.config.sender.send_delay_s;
        let handoff = TrueTime::from_seconds(handoff_s).max(self.now);
        self.push_event(handoff, Event::Capture { epoch, block_index });
    }

    fn schedule_play_cycle(&mut self, speaker: usize, cycle: u64) {
        let rate = f64::from(self.config.sender.rate);
        let (epoch, plan_at) = {
            let sp = &mut self.speakers[speaker];
            let first = cycle.saturating_mul(u64::from(sp.config.cycle_frames));
            let out_s = sp.leaves_s(u64_to_f64(first), rate);
            let plan_at = TrueTime::from_seconds(out_s - sp.config.lead_s).max(self.now);
            (sp.epoch, plan_at)
        };
        self.push_event(
            plan_at,
            Event::PlayCycle {
                speaker,
                epoch,
                cycle,
            },
        );
    }

    fn schedule_net_step_at(&mut self, speaker: usize, at: TrueTime) {
        let (epoch, generation) = {
            let sp = &mut self.speakers[speaker];
            sp.net_wake_gen += 1;
            (sp.epoch, sp.net_wake_gen)
        };
        self.push_event(
            at,
            Event::ReceiverNetStep {
                speaker,
                epoch,
                generation,
            },
        );
    }

    fn schedule_next_net_wake(&mut self, speaker: usize, local_now_ns: i64) {
        let Some(wake_ns) = self.speakers[speaker].net.next_wake_ns(local_now_ns) else {
            return;
        };
        let host_node = self.speakers[speaker].config.host + 1;
        let min_step_ns = if self.speakers[speaker]
            .net
            .engine()
            .has_pending_sync_update()
        {
            // If the incoming audio ring was momentarily full, retry after a
            // short poll interval instead of tight-spinning until the next
            // audio callback drains the ring.
            500_000
        } else {
            1_000
        };
        let wake_true = if wake_ns <= local_now_ns {
            TrueTime(self.now.0.saturating_add(min_step_ns))
        } else {
            let t_s = self.host_clocks[host_node].when_seconds(nanos_to_seconds(wake_ns));
            TrueTime::from_seconds(t_s).max(TrueTime(self.now.0.saturating_add(min_step_ns)))
        };
        self.schedule_net_step_at(speaker, wake_true);
    }

    fn dispatch(&mut self, at: TrueTime, event: Event) {
        match event {
            Event::Capture { epoch, block_index } => {
                if epoch == self.sender_epoch {
                    self.on_capture(at, epoch, block_index);
                }
            }
            Event::EmitFromSender { epoch, sent } => {
                if epoch == self.sender_epoch {
                    self.deliver_from_sender(at, epoch, sent);
                }
            }
            Event::SenderDeparture { epoch, tag, tx_ns } => {
                if epoch == self.sender_epoch {
                    self.sender_bridge.on_departure(tag, tx_ns);
                }
            }
            Event::DeliverToSender {
                from_node,
                from_addr,
                bytes,
            } => {
                self.on_sender_datagram(at, from_node, from_addr, &bytes);
            }
            Event::EmitFromReceiver {
                speaker,
                epoch,
                sent,
            } => {
                if self.speakers[speaker].epoch == epoch {
                    self.deliver_from_receiver(at, speaker, sent);
                }
            }
            Event::DeliverToReceiver {
                speaker,
                from_node,
                from_addr,
                bytes,
            } => {
                self.on_receiver_datagram(at, speaker, from_node, from_addr, &bytes);
            }
            Event::ReceiverDeparture {
                speaker,
                epoch,
                tag,
                tx_ns,
            } => {
                if self.speakers[speaker].epoch == epoch {
                    self.speakers[speaker].net.deliver_departure(tag, tx_ns);
                }
            }
            Event::ReceiverNetStep {
                speaker,
                epoch,
                generation,
            } => {
                if self.speakers[speaker].epoch == epoch
                    && self.speakers[speaker].net_wake_gen == generation
                {
                    self.on_receiver_net_step(at, speaker);
                }
            }
            Event::PlayCycle {
                speaker,
                epoch,
                cycle,
            } => {
                if self.speakers[speaker].epoch == epoch {
                    self.on_play_cycle(at, speaker, cycle);
                }
            }
        }
    }

    fn on_capture(&mut self, at: TrueTime, epoch: u64, block_index: u64) {
        let packet_frames = usize::from(self.config.sender.packet_frames);
        let channels = usize::from(self.config.sender.channels);
        let rate = f64::from(self.config.sender.rate);
        let first_frame = self.sender_capture_cursor;
        let first_device_s = self
            .sender_device
            .when_seconds(u64_to_f64(first_frame) / rate);
        // Fixed application target latency `World.target` (never tracks
        // adaptive changes to the sender's current playout level).
        let target_lat_s = self
            .config
            .target_latency_s
            .unwrap_or_else(|| nanos_to_seconds(self.config.sender.level_ns));
        let hidden_cap = self.config.sender.hidden_latency_s;

        probe::fill_capture(
            self.global_captured_frames,
            channels,
            packet_frames,
            &mut self.capture_buf,
        );

        let record_trace = self.config.record_trace;
        for offset in 0..packet_frames {
            let f_idx = first_frame + offset as u64;
            let device_s = self.sender_device.when_seconds(u64_to_f64(f_idx) / rate);
            let true_cap_s = device_s - hidden_cap;
            if let Some(rec) = self.objectives.as_mut() {
                rec.record_capture_frame(true_cap_s, target_lat_s);
            }
            if record_trace {
                self.capture_times.push_back(true_cap_s);
                while self.capture_times.len() > self.max_capture_history {
                    self.capture_times.pop_front();
                    self.capture_times_base = self.capture_times_base.saturating_add(1);
                }
            }
        }
        self.global_captured_frames = self
            .global_captured_frames
            .saturating_add(packet_frames as u64);

        let report_ns = self.host_clocks[0].read_noisy(
            TrueTime::from_seconds(first_device_s),
            self.config.sender.capture_timestamp_std_s,
            &mut self.sender_stamp_rng,
        );
        self.capture_end
            .cycle(&self.capture_buf, first_frame, report_ns);
        let mut sink = SimSink::default();
        let _ = self.sender_bridge.drain_captured(&mut sink);
        self.deliver_from_sender(at, epoch, sink.sent);

        self.sender_capture_cursor = self
            .sender_capture_cursor
            .saturating_add(packet_frames as u64);
        self.schedule_capture(epoch, block_index + 1);
    }

    fn on_sender_datagram(
        &mut self,
        at: TrueTime,
        from_node: usize,
        from_addr: SocketAddr,
        bytes: &[u8],
    ) {
        let true_arrival_ns = self.host_clocks[0].read(at);
        let arrival_ns = self.links[from_node][0].stamp_rx(true_arrival_ns);
        let t3_true = at.plus_seconds(self.config.sender.reply_processing_s.max(0.0));
        // Production `SenderNetwork` reads software `clock::raw()` before
        // `socket.send()`, so `reply_ns` reflects `t3_true` while the reply
        // leaves onto the wire at `t3_true + reply_send_latency_s`.
        let reply_ns = self.host_clocks[0].read(t3_true).max(arrival_ns);
        let mut sink = SimSink::default();
        let _ = self
            .sender_bridge
            .on_datagram(from_addr, bytes, arrival_ns, reply_ns, &mut sink);
        if !sink.sent.is_empty() {
            let wire_depart =
                t3_true.plus_seconds(self.config.sender.reply_send_latency_s.max(0.0));
            if wire_depart > at {
                self.push_event(
                    wire_depart,
                    Event::EmitFromSender {
                        epoch: self.sender_epoch,
                        sent: sink.sent,
                    },
                );
            } else {
                self.deliver_from_sender(at, self.sender_epoch, sink.sent);
            }
        }
    }

    fn deliver_from_sender(&mut self, at: TrueTime, epoch: u64, sent: Vec<SentDatagram>) {
        // Cache per-destination-host arrival for simultaneous audio packet
        // fanout when `share_same_host_audio_arrival` is enabled.
        let mut shared_audio_arrival: HashMap<(usize, u64, u64), Option<TrueTime>> = HashMap::new();
        for dgram in sent {
            let Some(&speaker) = self.addr_to_speaker.get(&dgram.to) else {
                continue;
            };
            let dst_node = self.speakers[speaker].config.host + 1;
            if let Some(tag) = dgram.tag {
                let true_tx = self.host_clocks[0].read(at);
                let tx_ns = self.links[0][dst_node].stamp_tx(true_tx);
                self.push_event(at, Event::SenderDeparture { epoch, tag, tx_ns });
            }
            if self.partitioned[0][dst_node] {
                continue;
            }
            let audio_key = if self.config.share_same_host_audio_arrival {
                packet::parse_audio(&dgram.bytes)
                    .ok()
                    .map(|hdr| (dst_node, hdr.timeline, hdr.index))
            } else {
                None
            };
            let arrival = if let Some(key) = audio_key {
                if let Some(&cached) = shared_audio_arrival.get(&key) {
                    cached
                } else {
                    let shared = self
                        .contention
                        .as_mut()
                        .map_or(0.0, |c| c.delay(0, dst_node, at));
                    let arr = self.links[0][dst_node].deliver(at, shared);
                    shared_audio_arrival.insert(key, arr);
                    arr
                }
            } else {
                let shared = self
                    .contention
                    .as_mut()
                    .map_or(0.0, |c| c.delay(0, dst_node, at));
                self.links[0][dst_node].deliver(at, shared)
            };
            if let Some(arrive_at) = arrival {
                self.push_event(
                    arrive_at,
                    Event::DeliverToReceiver {
                        speaker,
                        from_node: 0,
                        from_addr: self.sender_addr,
                        bytes: dgram.bytes,
                    },
                );
            }
        }
    }

    fn deliver_from_receiver(&mut self, at: TrueTime, speaker: usize, sent: Vec<SentDatagram>) {
        let src_node = self.speakers[speaker].config.host + 1;
        let src_addr = self.speakers[speaker].addr;
        let epoch = self.speakers[speaker].epoch;
        for dgram in sent {
            let dst_node = if dgram.to == self.sender_addr {
                0
            } else if let Some(&dst_sp) = self.addr_to_speaker.get(&dgram.to) {
                self.speakers[dst_sp].config.host + 1
            } else {
                continue;
            };
            if let Some(tag) = dgram.tag {
                let true_tx = self.host_clocks[src_node].read(at);
                let tx_ns = self.links[src_node][dst_node].stamp_tx(true_tx);
                self.push_event(
                    at,
                    Event::ReceiverDeparture {
                        speaker,
                        epoch,
                        tag,
                        tx_ns,
                    },
                );
            }
            if self.partitioned[src_node][dst_node] {
                continue;
            }
            let shared = self
                .contention
                .as_mut()
                .map_or(0.0, |c| c.delay(src_node, dst_node, at));
            let Some(arrive_at) = self.links[src_node][dst_node].deliver(at, shared) else {
                continue;
            };
            if dst_node == 0 {
                self.push_event(
                    arrive_at,
                    Event::DeliverToSender {
                        from_node: src_node,
                        from_addr: src_addr,
                        bytes: dgram.bytes,
                    },
                );
            } else if let Some(&dst_sp) = self.addr_to_speaker.get(&dgram.to) {
                self.push_event(
                    arrive_at,
                    Event::DeliverToReceiver {
                        speaker: dst_sp,
                        from_node: src_node,
                        from_addr: src_addr,
                        bytes: dgram.bytes,
                    },
                );
            }
        }
    }

    fn on_receiver_datagram(
        &mut self,
        at: TrueTime,
        speaker: usize,
        from_node: usize,
        from_addr: SocketAddr,
        bytes: &[u8],
    ) {
        let host_idx = self.speakers[speaker].config.host;
        let dst_node = host_idx + 1;
        let host_cfg = self.config.hosts[host_idx];
        let true_arrival_ns = self.host_clocks[dst_node].read(at);
        let arrival_ns = self.links[from_node][dst_node].stamp_rx(true_arrival_ns);
        let t3_true = at.plus_seconds(host_cfg.reply_processing_s.max(0.0));
        // Production `ReceiverNetwork` reads software `clock::raw()` before
        // `socket.send()`, so `reply_ns` reflects `t3_true` while any
        // `PeerEcho` leaves onto the wire at `t3_true + reply_send_latency_s`.
        let reply_ns = self.host_clocks[dst_node].read(t3_true).max(arrival_ns);
        let mut sink = SimSink::default();
        let _ = self.speakers[speaker]
            .net
            .deliver_datagram(from_addr, bytes, arrival_ns, reply_ns, &mut sink);
        if !sink.sent.is_empty() {
            let wire_depart = t3_true.plus_seconds(host_cfg.reply_send_latency_s.max(0.0));
            if wire_depart > at {
                let epoch = self.speakers[speaker].epoch;
                self.push_event(
                    wire_depart,
                    Event::EmitFromReceiver {
                        speaker,
                        epoch,
                        sent: sink.sent,
                    },
                );
            } else {
                self.deliver_from_receiver(at, speaker, sink.sent);
            }
        }
        self.schedule_next_net_wake(speaker, arrival_ns);
    }

    fn on_receiver_net_step(&mut self, at: TrueTime, speaker: usize) {
        let host_node = self.speakers[speaker].config.host + 1;
        let local_now_ns = self.host_clocks[host_node].read(at);
        let mut sink = SimSink::default();
        let _ = self.speakers[speaker].net.step(local_now_ns, &mut sink);
        if !sink.sent.is_empty() {
            self.deliver_from_receiver(at, speaker, sink.sent);
        }
        self.schedule_next_net_wake(speaker, local_now_ns);
    }

    fn on_play_cycle(&mut self, at: TrueTime, speaker: usize, cycle: u64) {
        let rate = f64::from(self.config.sender.rate);
        let channels = usize::from(self.config.sender.channels);
        let host_node = self.speakers[speaker].config.host + 1;
        let frame_count = self.speakers[speaker].config.cycle_frames;
        let first_dev_frame = cycle.saturating_mul(u64::from(frame_count));

        let (out_start_s, out_end_s, hidden_out) = {
            let sp = &mut self.speakers[speaker];
            let s0 = sp.leaves_s(u64_to_f64(first_dev_frame), rate);
            let s1 = sp.leaves_s(u64_to_f64(first_dev_frame + u64::from(frame_count)), rate);
            (s0, s1, sp.config.hidden_latency_s)
        };
        let true_start_ns = self.host_clocks[host_node].read(TrueTime::from_seconds(out_start_s));
        let reported_start_ns = match self.speakers[speaker].config.cycle_length {
            CycleLength::Measured | CycleLength::Nominal => true_start_ns,
            CycleLength::Fitted(half_range) => {
                if half_range > 0 {
                    let span = half_range.saturating_mul(2);
                    let u = self.speakers[speaker].device_noise_rng.uniform();
                    #[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
                    let jitter = ((u - 0.5) * span as f64).round() as i64;
                    true_start_ns.saturating_add(jitter)
                } else {
                    true_start_ns
                }
            }
        };

        let mut report_sink = SimSink::default();
        let played = {
            let sp = &mut self.speakers[speaker];
            let dev_pos = sp.device_frame_cursor;
            sp.device_frame_cursor = sp
                .device_frame_cursor
                .saturating_add(u64::from(frame_count));
            sp.next_cycle_index = cycle + 1;
            sp.audio.cycle(&mut sp.pcm_buf, dev_pos, reported_start_ns);
            let _ = sp.net.flush_reports(&mut report_sink);
            sp.audio.playback().last()
        };
        if !report_sink.sent.is_empty() {
            self.deliver_from_receiver(at, speaker, report_sink.sent);
        }

        let acoustic_start_s = out_start_s + hidden_out;
        let acoustic_end_s = out_end_s + hidden_out;

        let need_decode = self.config.record_trace
            || self.speakers[speaker].config.record_pcm
            || self
                .config
                .objective_window
                .is_some_and(|(ws, _)| acoustic_end_s >= ws - 1.0);

        if need_decode {
            let max_captured = self.global_captured_frames;
            self.score_decoded_cycle(
                speaker,
                channels,
                frame_count as usize,
                acoustic_start_s,
                acoustic_end_s,
                played,
                max_captured,
            );
        }

        self.schedule_play_cycle(speaker, cycle + 1);
    }

    #[allow(clippy::too_many_arguments)]
    fn score_decoded_cycle(
        &mut self,
        speaker: usize,
        channels: usize,
        frame_count: usize,
        acoustic_start_s: f64,
        acoustic_end_s: f64,
        played: unisono_runtime::pump::Played,
        max_captured: u64,
    ) {
        let count_f = usize_to_f64(frame_count.max(1));
        let dt_cycle = acoustic_end_s - acoustic_start_s;
        let record_trace = self.config.record_trace;

        let first_valid = {
            let sp = &mut self.speakers[speaker];
            let decoded = sp.decoder.decode_cycle(&sp.pcm_buf, channels, max_captured);

            if sp.config.record_pcm {
                let ch_count = channels.max(1);
                let first_channel = sp
                    .pcm_buf
                    .chunks_exact(ch_count)
                    .map(|frame| frame[0])
                    .collect();
                sp.recorded_cycles.push(RecordedCycle {
                    out_start_s: acoustic_start_s,
                    out_end_s: acoustic_end_s,
                    decoded: decoded.to_vec(),
                    channel0: first_channel,
                });
            }

            if let Some(rec) = self.objectives.as_mut() {
                for (idx, &pos) in decoded.iter().enumerate() {
                    let out_s = acoustic_start_s + (usize_to_f64(idx) / count_f) * dt_cycle;
                    rec.record_playback_sample(speaker, out_s, pos);
                }
            }

            if record_trace {
                sp.trace.held = sp.trace.held.saturating_add(u64::from(played.held));
                sp.trace.absent = sp.trace.absent.saturating_add(u64::from(played.concealed));
                if played.played == 0 {
                    sp.trace.idle_cycles += 1;
                } else if played.jumped {
                    sp.trace.jumps.push(acoustic_start_s);
                }
                decoded
                    .iter()
                    .enumerate()
                    .find_map(|(idx, &opt)| opt.map(|pos| (idx, pos)))
            } else {
                None
            }
        };

        if let Some((idx, global_pos)) = first_valid
            && let Some(cap_true_s) = self.capture_time_at(global_pos)
        {
            let out_s = acoustic_start_s + (usize_to_f64(idx) / count_f) * dt_cycle;
            let cap_sender_s = self.host_clocks[0].read_seconds(cap_true_s);
            let due_true_s = self.host_clocks[0]
                .when_seconds(cap_sender_s + nanos_to_seconds(self.config.sender.level_ns));
            self.speakers[speaker]
                .trace
                .errors
                .push((out_s, out_s - due_true_s));
        }
    }
}

#[cfg(test)]
mod tests {
    use unisono_core::kalman::NoisePrior;
    use unisono_core::sync::WEIGHT_UNITY_Q16;

    use super::{HostConfig, ReceiverConfig, Scene, SceneConfig, SenderConfig};
    use crate::TrueTime;
    use crate::clock::OscillatorModel;
    use crate::link::LinkModel;
    use crate::objectives::ObjectiveWeights;
    use crate::random::Generator;

    #[test]
    fn black_box_pcm_scoring_recovers_ideal_playback_and_detects_faults() {
        let build = |hidden_out_s: f64, sender_reply_send_s: f64| {
            let sender = SenderConfig::standard(
                OscillatorModel::ideal(5.0),
                OscillatorModel::ideal(0.0),
                20_000_000,
            )
            .with_fixed_level()
            .with_reply_latency(0.0, sender_reply_send_s);
            let hosts = vec![
                HostConfig::new(
                    OscillatorModel::ideal(-10.0),
                    LinkModel::IDEAL,
                    LinkModel::IDEAL,
                ),
                HostConfig::new(
                    OscillatorModel::ideal(12.0),
                    LinkModel::IDEAL,
                    LinkModel::IDEAL,
                ),
            ];
            let mut rx0 = ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0));
            let mut rx1 = ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0));
            rx0.sync_settings.sender_prior = NoisePrior::TCXO;
            rx0.sync_settings.local_prior = NoisePrior::TCXO;
            rx1.sync_settings.sender_prior = NoisePrior::TCXO;
            rx1.sync_settings.local_prior = NoisePrior::TCXO;
            rx1.hidden_latency_s = hidden_out_s;
            rx0.peers = vec![(1, WEIGHT_UNITY_Q16)];
            rx1.peers = vec![(0, WEIGHT_UNITY_Q16)];
            rx0.record_pcm = true;
            let mut cfg = SceneConfig::new(sender, hosts, vec![rx0, rx1]);
            cfg.peer_link = LinkModel::IDEAL;
            cfg.objective_window = Some((4.0, 5.5));
            cfg.objective_weights = ObjectiveWeights {
                sync: 1e6,
                latency: 1.0,
                tracking: 1e4,
                roughness: 1.0,
                missed: 1.0,
                discontinuities: 1.0,
            };
            let mut scene = Scene::new(cfg, &Generator::new(7));
            scene.run(TrueTime::from_seconds(5.7));
            scene
        };

        // 1. Clean ideal run: near-zero sync, tracking, roughness, zero misses.
        let clean = build(0.0, 0.0);
        let decoded_cycles = clean
            .recorded_cycles(0)
            .iter()
            .filter(|c| c.out_start_s >= 4.0 && c.decoded.iter().all(Option::is_some))
            .count();
        assert!(
            decoded_cycles > 250,
            "expected >250 fully decoded clean cycles, got {decoded_cycles}"
        );
        let clean_obj = clean.finish_objectives().expect("clean objectives");
        assert!(
            clean_obj.sync_rms_us < 0.1,
            "clean sync_rms_us={}",
            clean_obj.sync_rms_us
        );
        assert!(
            clean_obj.tracking_s2.sqrt() * 1e6 < 0.5,
            "clean tracking_rms_us={}",
            clean_obj.tracking_s2.sqrt() * 1e6
        );
        assert!(
            clean_obj.roughness_per_s2 < 1e-6,
            "clean roughness={}",
            clean_obj.roughness_per_s2
        );
        assert_eq!(clean_obj.missed_per_s, 0.0);
        assert_eq!(clean_obj.discontinuities_per_s, 0.0);

        // 2. Uncalibrated 200 us DAC latency on speaker 1 shifts playback 1:1
        //    (RMS spread across 2 speakers = 200 / 2 = 100 us).
        let hidden = build(200e-6, 0.0).finish_objectives().expect("hidden");
        assert!(
            (hidden.sync_rms_us - 100.0).abs() < 2.0,
            "expected ~100 us RMS spread for 200 us hidden DAC latency, got {}",
            hidden.sync_rms_us
        );

        // 3. Sender post-T3 send latency of 40 us introduces a 20 us edge bias
        //    into tracking (half of responder send latency).
        let reply_bias = build(0.0, 40e-6).finish_objectives().expect("reply bias");
        let tracking_rms_us = reply_bias.tracking_s2.sqrt() * 1e6;
        assert!(
            (tracking_rms_us - 20.0).abs() < 2.0,
            "expected ~20 us tracking bias for 40 us sender reply send latency, got {tracking_rms_us}"
        );
    }

    #[test]
    fn black_box_pcm_decoder_scores_packet_loss_concealment_as_missed() {
        let sender = SenderConfig::standard(
            OscillatorModel::ideal(0.0),
            OscillatorModel::ideal(0.0),
            30_000_000,
        )
        .with_fixed_level()
        .without_protection();
        let hosts = vec![HostConfig::new(
            OscillatorModel::ideal(0.0),
            LinkModel::IDEAL,
            LinkModel::IDEAL,
        )];
        let rx = ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0));
        let mut cfg = SceneConfig::new(sender, hosts, vec![rx]);
        cfg.objective_window = Some((0.5, 2.5));
        let mut scene = Scene::new(cfg, &Generator::new(13));
        scene.run(TrueTime::from_seconds(1.2));
        // Partition audio from sender -> receiver for 40 ms so packets drop
        // and the receiver must conceal them.
        scene.set_link_partitioned(0, 1, true);
        scene.run(TrueTime::from_seconds(1.24));
        scene.set_link_partitioned(0, 1, false);
        scene.run(TrueTime::from_seconds(2.6));
        let report = scene.finish_objectives().expect("objectives");
        assert!(
            report.missed_per_s > 400.0,
            "40 ms partition (~1920 frames over 2 s = ~960/s) must be caught as missed PCM, got {}",
            report.missed_per_s
        );
        assert!(
            report.discontinuities_per_s > 0.0,
            "partition must produce at least one discontinuity in decoded PCM"
        );
    }
}
