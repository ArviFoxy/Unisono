// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Faithful discrete-event simulator driving the production [`unisono_runtime`]
//! engines (`SenderNetEngine`, `ReceiverNetEngine`, `ReceiverPlayback`,
//! `ReportSchedule`) over real serialized UDP wire bytes and simulated
//! IEEE 1139 clocks and impaired links.
//!
//! Supports both [`AudioMode::FastCore`] (bypassing only FIR resampling and
//! concealment DSP via `packet_header_only` / `cycle_plan_only` while running
//! identical protocol bytes, timestamps, sync, and core playback planning) and
//! [`AudioMode::FullDsp`] (end-to-end PCM encoding, `Store`, `Pump`,
//! `Resampler`, and `Concealment`). Scores playback against all six canonical
//! objectives of `Unisono.Spec.Objectives` with exact resampler lookahead
//! playability enforcement.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, VecDeque};
use std::convert::Infallible;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use unisono_core::packet::{self, Audio, Format};
use unisono_core::player::{ModalRegulation, Plan, Regulation};
use unisono_core::sender::Settings as CoreSenderSettings;
use unisono_core::sync::{SyncSettings, SyncSnapshot, WEIGHT_UNITY_Q16};
use unisono_dsp::Parameters;
use unisono_runtime::audio::Playback;
use unisono_runtime::level::Choice;
use unisono_runtime::pump::{ReceiverPlayback, Settings as PlaybackSettings};
use unisono_runtime::receive::{
    ConfirmedState, DatagramAction, NetConfig, NetworkCounts, Outgoing, PeerConfig,
    ReceiverNetEngine, ReportSchedule, Reporting, SyncMode,
};
use unisono_runtime::send::{
    MAX_DATAGRAM, SenderCounts, SenderNetEngine, Settings as RuntimeSenderSettings,
};
use unisono_runtime::socket::{DatagramSink, SendStatus};

use crate::clock::{Course, OscillatorModel};
use crate::link::{Link, LinkModel, SharedContention, SharedContentionModel};
use crate::objectives::{
    ObjectiveRecorder, ObjectiveReport, ObjectiveWeights, playable as check_playable,
};
use crate::random::Generator;
use crate::{TrueTime, nanos_to_seconds, seconds_to_nanos};

/// Default device clock range accepted by `ReceiverPlayback` (1% = 10,000 ppm).
const DEFAULT_DEVICE_RANGE: u32 = 10_000_000;

/// Triangle-wave half-period (frames) for [`SignalMode::Ramp`].
pub const RAMP_HALF_PERIOD: u64 = 4_096;

/// Slope per source frame of [`SignalMode::Ramp`], keeping peak amplitude in
/// `[-0.8, 0.8]` for exact 24-bit linear recovery.
pub const RAMP_SLOPE: f64 = 1.6 / 4_096.0;

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

/// Converts a `2^-64`-frame fixed-point fractional stream position to `f64`
/// frames.
fn position_to_f64(pos: unisono_core::timing::Position) -> f64 {
    u64_to_f64(pos.frame()) + u64_to_f64(pos.fraction()) / 18_446_744_073_709_551_616.0
}

/// Deterministic triangle-wave sample value at source frame `frame` for
/// [`SignalMode::Ramp`].
#[must_use]
pub fn ramp_sample(frame: u64) -> f32 {
    let period = RAMP_HALF_PERIOD * 2;
    let phase = frame % period;
    let linear = if phase <= RAMP_HALF_PERIOD {
        -0.8 + u64_to_f64(phase) * RAMP_SLOPE
    } else {
        0.8 - u64_to_f64(phase - RAMP_HALF_PERIOD) * RAMP_SLOPE
    };
    #[allow(clippy::cast_possible_truncation)]
    let sample = linear as f32;
    sample
}

/// Decodes a [`SignalMode::Ramp`] sample near `expected_frame` back into a
/// fractional source frame index, returning `None` if `expected_frame` is
/// within `margin_frames` of a triangle turnaround corner (where FIR taps
/// span both slopes).
#[must_use]
pub fn decode_ramp_position(sample: f32, expected_frame: f64, margin_frames: f64) -> Option<f64> {
    if !expected_frame.is_finite() || expected_frame < 0.0 {
        return None;
    }
    let half = u64_to_f64(RAMP_HALF_PERIOD);
    let period = half * 2.0;
    let cycle = (expected_frame / period).floor();
    let phase = expected_frame - cycle * period;
    if phase < margin_frames
        || (half - phase).abs() < margin_frames
        || (period - phase) < margin_frames
    {
        return None;
    }
    let val = f64::from(sample);
    let decoded_phase = if phase < half {
        (val + 0.8) / RAMP_SLOPE
    } else {
        half + (0.8 - val) / RAMP_SLOPE
    };
    Some(cycle * period + decoded_phase)
}

/// Audio payload execution mode for a simulated receiver.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum AudioMode {
    /// Skips FIR resampling and concealment DSP via `packet_header_only` /
    /// `cycle_plan_only` while running identical serialized wire bytes,
    /// `SenderNetEngine`, `ReceiverNetEngine`, `Sync`, `ReportSchedule`, and
    /// `ReceiverPlayback` core planning.
    #[default]
    FastCore,
    /// Runs full PCM encoding/decoding, `Store`, `Pump`, Kaiser-sinc
    /// `Resampler`, and Burg `Concealment`.
    FullDsp,
}

/// Source waveform generated by the simulated sender.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SignalMode {
    /// Zero-filled PCM frames (fast path).
    #[default]
    Silent,
    /// Linear triangle-wave ramp ([`ramp_sample`]) for end-to-end `FullDsp`
    /// fractional-position verification.
    Ramp,
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
    /// `ReportSchedule` under the given [`Reporting`] cadence.
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
    /// Source PCM waveform mode.
    pub signal: SignalMode,
    /// Standard deviation of Gaussian capture-device timestamp noise, in
    /// seconds.
    pub capture_timestamp_std_s: f64,
}

impl SenderConfig {
    /// Standard 48 kHz stereo 240-frame packet sender configuration.
    #[must_use]
    pub fn standard(clock: OscillatorModel, device: OscillatorModel, level_ns: i64) -> Self {
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
            span_ms: 11_000,
            window_frames: 15_360,
            kept_packets: 0,
            choice: None,
            signal: SignalMode::Silent,
            capture_timestamp_std_s: 0.0,
        }
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
    /// seconds.
    pub lead_s: f64,
    /// Clock synchronization mode (`SyncMode::Peer` or `SyncMode::Hull`).
    pub sync_mode: SyncMode,
    /// `Sync` settings used when `sync_mode == SyncMode::Peer`.
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
    /// Execution mode (`FastCore` or `FullDsp`).
    pub audio_mode: AudioMode,
    /// Whether to retain decoded `FullDsp` cycle PCM and plan metadata.
    pub record_pcm: bool,
}

impl ReceiverConfig {
    /// Creates a `SyncMode::Peer` receiver configuration on `host` with
    /// standard settings and zero initial peers (Star mode until peers are
    /// added).
    #[must_use]
    pub fn peer(host: usize, identity: u64, device: OscillatorModel) -> Self {
        let mut sync_settings = SyncSettings::standard(1, identity);
        sync_settings.stream = 1;
        Self {
            host,
            identity,
            device,
            cycle_frames: 256,
            lead_s: 8e-3,
            sync_mode: SyncMode::Peer,
            sync_settings,
            sender_weight_q16: WEIGHT_UNITY_Q16,
            peers: Vec::new(),
            regulation: Regulation {
                gain: 4 << 16,
                limit: 1_000_000,
                jump: 240,
            },
            modal_regulation: Some(ModalRegulation::lipsync(1_000_000, 240)),
            silence_ns: 1_000_000_000,
            slope_limit: 200_000,
            path: PathDelay::Measured(Reporting::USUAL),
            cycle_length: CycleLength::Measured,
            stands_still: None,
            audio_mode: AudioMode::FastCore,
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
    /// Optional target latency `L*` (seconds) for `tracking_s2`; defaults to
    /// `sender.level_ns * 1e-9`.
    pub target_latency_s: Option<f64>,
    /// When `true` (default), speakers co-located on the same receiver host
    /// receive the same NIC arrival time for a single sender audio packet
    /// emission.
    pub share_same_host_audio_arrival: bool,
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
        }
    }
}

/// Per-cycle timing trace for one receiver (used by timing regression tests).
#[derive(Clone, Debug, Default)]
pub struct Trace {
    /// `(true_out_time_s, timing_error_s)` for each non-idle cycle's first
    /// frame (positive error = playing late relative to `capture + level`).
    pub errors: Vec<(f64, f64)>,
    /// True output times (seconds) of cycles whose playback plan jumped.
    pub jumps: Vec<f64>,
    /// Number of idle playback cycles (`plan.frames == 0`).
    pub idle_cycles: u64,
    /// Total stream frames marked held while advancing playhead.
    pub held: u64,
    /// Total stream frames marked absent/concealed while advancing playhead.
    pub absent: u64,
}

/// Recorded PCM output and exact plan metadata from one `FullDsp` cycle.
#[derive(Clone, Debug)]
pub struct RecordedCycle {
    /// True output time of the cycle's first frame, in seconds.
    pub out_start_s: f64,
    /// True output time of the next cycle's first frame, in seconds.
    pub out_end_s: f64,
    /// Playback plan executed for this cycle.
    pub plan: Plan,
    /// Channel-0 output PCM samples rendered by `ReceiverPlayback::cycle`.
    pub channel0: Vec<f32>,
}

/// Compact rolling bitmap of held frame indices for one timeline, providing
/// O(1) contiguous range checks and exact membership queries matching
/// `Unisono.Spec.playable`.
#[derive(Clone, Debug)]
struct HeldFrames {
    /// Lowest frame index represented by word 0 (always a multiple of 64).
    base: u64,
    /// Bitset words covering `[base, base + words.len() * 64)`.
    words: VecDeque<u64>,
    /// Exclusive upper bound of the contiguous held prefix starting at
    /// `contiguous_start`.
    contiguous_start: u64,
    contiguous_end: u64,
    /// Maximum frames retained before pruning old words from the front.
    max_words: usize,
}

impl HeldFrames {
    fn new(max_frames: usize) -> Self {
        let max_words = (max_frames / 64).max(128);
        Self {
            base: 0,
            words: VecDeque::new(),
            contiguous_start: 0,
            contiguous_end: 0,
            max_words,
        }
    }

    fn reset(&mut self) {
        self.base = 0;
        self.words.clear();
        self.contiguous_start = 0;
        self.contiguous_end = 0;
    }

    fn mark_range(&mut self, first: u64, count: u64) {
        if count == 0 {
            return;
        }
        let end = first.saturating_add(count);
        if self.words.is_empty() {
            self.base = first & !63;
            self.contiguous_start = first;
            self.contiguous_end = first;
        }
        if end <= self.base {
            return;
        }
        let effective_first = first.max(self.base);
        let needed_words = usize::try_from(((end - 1) - self.base) / 64 + 1).unwrap_or(0);
        if needed_words > self.max_words.saturating_mul(2) {
            // Far forward jump: restart bitmap near `first`.
            self.reset();
            self.base = first & !63;
            self.contiguous_start = first;
            self.contiguous_end = first;
            self.mark_range(first, count);
            return;
        }
        while self.words.len() < needed_words {
            self.words.push_back(0);
        }
        for frame in effective_first..end {
            let rel = frame - self.base;
            let word = usize::try_from(rel / 64).unwrap_or(usize::MAX);
            let bit = (rel % 64) as u32;
            if let Some(slot) = self.words.get_mut(word) {
                *slot |= 1u64 << bit;
            }
        }
        // Advance the contiguous prefix cursor when new frames extend it.
        if effective_first <= self.contiguous_end && end > self.contiguous_end {
            let mut cursor = end;
            while self.is_held(cursor) {
                cursor += 1;
            }
            self.contiguous_end = cursor;
        }
        // Prune very old words from the front to keep memory bounded.
        while self.words.len() > self.max_words {
            self.words.pop_front();
            self.base += 64;
            if self.contiguous_start < self.base {
                self.contiguous_start = self.base;
                if self.contiguous_end < self.base {
                    self.contiguous_end = self.base;
                }
            }
        }
    }

    fn is_held(&self, frame: u64) -> bool {
        if frame < self.base {
            return false;
        }
        let rel = frame - self.base;
        let word = usize::try_from(rel / 64).unwrap_or(usize::MAX);
        let bit = (rel % 64) as u32;
        self.words
            .get(word)
            .is_some_and(|bits| (bits & (1u64 << bit)) != 0)
    }

    fn range_fully_held(&self, lo: u64, hi_inclusive: u64) -> bool {
        if lo > hi_inclusive {
            return true;
        }
        if lo >= self.contiguous_start && hi_inclusive < self.contiguous_end {
            return true;
        }
        if lo < self.base {
            return false;
        }
        (lo..=hi_inclusive).all(|f| self.is_held(f))
    }
}

/// Outgoing datagram collected from a [`SenderNetEngine`] or
/// [`ReceiverNetEngine`] during a simulation event.
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
    /// Sender TX departure timestamp arriving back from the NIC.
    SenderDeparture { epoch: u64, tag: u64, tx_ns: i64 },
    /// Datagram arriving at the sender socket.
    DeliverToSender {
        from_node: usize,
        from_addr: SocketAddr,
        bytes: Vec<u8>,
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

/// Metadata recorded for a sender timeline so per-cycle traces and
/// `ObjectiveRecorder` map timeline frame indices to exact true capture times.
#[derive(Clone, Debug)]
struct TimelineInfo {
    /// Monotonic frame offset in `ObjectiveRecorder` for frame 0 of this
    /// timeline.
    global_frame_base: u64,
    /// True-time start of frame 0 on the capture device's clock (seconds).
    origin_capture_frame: u64,
    /// Capture device course snapshot offset (frame count at timeline start).
    level_ns: i64,
}

/// Runtime state of one simulated receiver speaker.
struct Speaker {
    config: ReceiverConfig,
    addr: SocketAddr,
    playback: ReceiverPlayback<64, 64, 8, 64>,
    net: ReceiverNetEngine,
    report_schedule: ReportSchedule,
    device: Course,
    device_noise_rng: Generator,
    held_frames: HeldFrames,
    pcm_buf: Vec<f32>,
    recorded_cycles: Vec<RecordedCycle>,
    trace: Trace,
    epoch: u64,
    net_wake_gen: u64,
    last_timeline: Option<u64>,
    /// True-time stamp (seconds) of the last cycle recorded in `Trace`.
    next_cycle_index: u64,
    /// Next cycle frame counter passed to `ReceiverPlayback`.
    device_frame_cursor: u64,
}

impl Speaker {
    fn confirmed_state(&self) -> ConfirmedState {
        let rx = self.playback.receiver();
        ConfirmedState {
            attached: true,
            active: rx.timeline().is_some(),
            timeline: rx.timeline().unwrap_or(0),
            clock_id: rx.clock_id().unwrap_or(0),
            rate: self.playback.rate(),
            channels: self.playback.channels_u8(),
        }
    }

    /// True time (seconds) when playback device frame `frame` leaves the DAC.
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

/// Builds a [`PlaybackSettings`] and [`NetConfig`] pair for speaker `index`.
fn build_receiver_parts(
    sender_cfg: &SenderConfig,
    rec_cfg: &ReceiverConfig,
    all_addrs: &[(u64, SocketAddr)],
    true_min_delay_ns: i64,
) -> (ReceiverPlayback<64, 64, 8, 64>, ReceiverNetEngine) {
    let jump = (sender_cfg.rate / 200).max(1);
    let modal_regulation = match rec_cfg.sync_mode {
        SyncMode::Hull => None,
        SyncMode::Peer => Some(
            rec_cfg
                .modal_regulation
                .unwrap_or_else(|| ModalRegulation::lipsync(1_000_000, jump)),
        ),
    };
    let device_range = match rec_cfg.cycle_length {
        CycleLength::Nominal => 0,
        CycleLength::Measured | CycleLength::Fitted(_) => DEFAULT_DEVICE_RANGE,
    };
    let pb_settings = PlaybackSettings {
        stream: sender_cfg.stream,
        rate: sender_cfg.rate,
        channels: sender_cfg.channels,
        identity: rec_cfg.identity,
        silence: rec_cfg.silence_ns,
        slope_limit: rec_cfg.slope_limit,
        regulation: rec_cfg.regulation,
        modal_regulation,
        concealment: Parameters::for_rate(sender_cfg.rate),
        block: 256,
        device_range,
    };
    let mut playback = ReceiverPlayback::new(&pb_settings);
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
    let net = ReceiverNetEngine::new(&net_config);
    (playback, net)
}

/// Builds a [`SenderNetEngine`] from [`SenderConfig`] and receiver addresses.
fn build_sender_engine(
    cfg: &SenderConfig,
    timeline: u64,
    clock_id: u32,
    level_ns: i64,
    receiver_addrs: &[SocketAddr],
) -> SenderNetEngine {
    let runtime_settings = RuntimeSenderSettings {
        stream: CoreSenderSettings {
            stream: cfg.stream,
            rate: cfg.rate,
            channels: cfg.channels,
            format: cfg.format,
            span: cfg.span_ms,
            window: cfg.window_frames,
            clock: clock_id,
        },
        packet: cfg.packet_frames,
        level: level_ns,
        timeline,
        receivers: receiver_addrs.to_vec(),
        kept: cfg.kept_packets,
        choice: cfg.choice,
    };
    SenderNetEngine::new(runtime_settings)
}

/// Faithful multi-host discrete-event simulation scene driving production
/// `unisono-runtime` engines over real serialized UDP datagrams.
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
    sender_engine: SenderNetEngine,
    sender_addr: SocketAddr,
    sender_epoch: u64,
    sender_timeline: u64,
    sender_clock_id: u32,
    /// Next capture frame index on `sender_device` (monotonic across restarts).
    sender_capture_cursor: u64,
    /// Preallocated capture PCM buffer reused across `on_capture` calls.
    capture_buf: Vec<f32>,
    /// Map from `timeline` -> [`TimelineInfo`].
    timelines: HashMap<u64, TimelineInfo>,
    /// Monotonic count of captured frames recorded into `objectives`.
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
    max_held: usize,
    generator: &Generator,
) -> Vec<Speaker> {
    let mut speakers = Vec::with_capacity(config.receivers.len());
    for (idx, rec_cfg) in config.receivers.iter().enumerate() {
        let min_delay_ns = host_true_min_delay_ns
            .get(rec_cfg.host)
            .copied()
            .unwrap_or(0);
        let (playback, net) =
            build_receiver_parts(&config.sender, rec_cfg, speaker_addrs, min_delay_ns);
        let pcm_len = (rec_cfg.cycle_frames as usize) * usize::from(config.sender.channels);
        speakers.push(Speaker {
            config: rec_cfg.clone(),
            addr: speaker_addrs[idx].1,
            playback,
            net,
            report_schedule: ReportSchedule::new(),
            device: Course::new(
                rec_cfg.device,
                generator.fork(20_000 + u64::try_from(idx).unwrap_or(0)),
            ),
            device_noise_rng: generator.fork(30_000 + u64::try_from(idx).unwrap_or(0)),
            held_frames: HeldFrames::new(max_held),
            pcm_buf: vec![0.0; pcm_len],
            recorded_cycles: Vec::new(),
            trace: Trace::default(),
            epoch: 0,
            net_wake_gen: 0,
            last_timeline: None,
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

        let sender_engine = build_sender_engine(
            &config.sender,
            config.sender.timeline,
            config.sender.clock_id,
            config.sender.level_ns,
            &raw_rx_addrs,
        );
        let capture_samples =
            usize::from(config.sender.packet_frames) * usize::from(config.sender.channels);
        let max_held = (config.sender.rate as usize).saturating_mul(4).max(65_536);
        let speakers = build_speakers(
            &config,
            &speaker_addrs,
            &host_true_min_delay_ns,
            max_held,
            generator,
        );

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
            .with_max_buffered_frames(max_held)
        });

        let mut timelines = HashMap::new();
        timelines.insert(
            config.sender.timeline,
            TimelineInfo {
                global_frame_base: 0,
                origin_capture_frame: 0,
                level_ns: config.sender.level_ns,
            },
        );

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
            sender_engine,
            sender_addr: sender_addr(),
            sender_epoch: 0,
            sender_timeline: initial_timeline,
            sender_clock_id: initial_clock_id,
            sender_capture_cursor: 0,
            capture_buf: vec![0.0; capture_samples],
            timelines,
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
        let level_ns = self.sender_engine.sender().current_level();
        let raw_rx_addrs: Vec<SocketAddr> = self.speaker_addrs.iter().map(|&(_, a)| a).collect();
        self.sender_engine = build_sender_engine(
            &self.config.sender,
            self.sender_timeline,
            self.sender_clock_id,
            level_ns,
            &raw_rx_addrs,
        );
        let rate = f64::from(self.config.sender.rate);
        let current_frame_f = (self.sender_device.read_seconds(self.now.seconds()) * rate)
            .ceil()
            .max(0.0);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let next_frame = (current_frame_f as u64).max(self.sender_capture_cursor);
        self.sender_capture_cursor = next_frame;
        self.timelines.insert(
            self.sender_timeline,
            TimelineInfo {
                global_frame_base: self.global_captured_frames,
                origin_capture_frame: next_frame,
                level_ns,
            },
        );
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
    /// sync engine, and report schedule while preserving its host clock and
    /// playback DAC oscillator.
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
        let (playback, net) = build_receiver_parts(
            &self.config.sender,
            &sp.config,
            &self.speaker_addrs,
            min_delay_ns,
        );
        sp.playback = playback;
        sp.net = net;
        sp.report_schedule.reset();
        sp.held_frames.reset();
        sp.last_timeline = None;
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
            .and_then(|sp| sp.playback.receiver().timeline())
    }

    /// Current estimated forward path delay (ns) on speaker `speaker`.
    #[must_use]
    pub fn delay(&self, speaker: usize) -> Option<i64> {
        self.speakers
            .get(speaker)
            .map(|sp| sp.playback.receiver().delay())
    }

    /// Latest [`SyncSnapshot`] from speaker `speaker`'s network engine, or
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
        self.sender_engine.counts()
    }

    /// Current sender playout latency level, in nanoseconds.
    #[must_use]
    pub fn sender_level_ns(&self) -> i64 {
        self.sender_engine.sender().current_level()
    }

    /// Per-speaker timing traces recorded over the simulation.
    #[must_use]
    pub fn traces(&self) -> Vec<&Trace> {
        self.speakers.iter().map(|sp| &sp.trace).collect()
    }

    /// Recorded `FullDsp` cycle PCM outputs for speaker `speaker`.
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
        let wake_true = if wake_ns <= local_now_ns {
            TrueTime(self.now.0.saturating_add(1_000))
        } else {
            let t_s = self.host_clocks[host_node].when_seconds(nanos_to_seconds(wake_ns));
            TrueTime::from_seconds(t_s).max(TrueTime(self.now.0.saturating_add(1_000)))
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
            Event::SenderDeparture { epoch, tag, tx_ns } => {
                if epoch == self.sender_epoch {
                    self.sender_engine.on_departure(tag, tx_ns);
                }
            }
            Event::DeliverToSender {
                from_node,
                from_addr,
                bytes,
            } => {
                self.on_sender_datagram(at, from_node, from_addr, &bytes);
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
                if self.speakers[speaker].epoch == epoch
                    && let Some((seq, dep_ns)) = self.speakers[speaker].net.on_departure(tag, tx_ns)
                {
                    self.speakers[speaker].playback.reported(seq, dep_ns);
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
        let first_cap_s = self
            .sender_device
            .when_seconds(u64_to_f64(first_frame) / rate);
        let target_lat_s = self
            .config
            .target_latency_s
            .unwrap_or_else(|| nanos_to_seconds(self.sender_engine.sender().current_level()));

        if let Some(rec) = self.objectives.as_mut() {
            for offset in 0..packet_frames {
                let f_idx = first_frame + offset as u64;
                let cap_s = self.sender_device.when_seconds(u64_to_f64(f_idx) / rate);
                rec.record_capture_frame(cap_s, target_lat_s);
            }
        }
        self.global_captured_frames = self
            .global_captured_frames
            .saturating_add(packet_frames as u64);

        match self.config.sender.signal {
            SignalMode::Silent => {}
            SignalMode::Ramp => {
                let tl_base = self
                    .timelines
                    .get(&self.sender_timeline)
                    .map_or(0, |info| info.origin_capture_frame);
                for offset in 0..packet_frames {
                    let timeline_frame = (first_frame + offset as u64).saturating_sub(tl_base);
                    let val = ramp_sample(timeline_frame);
                    let base = offset * channels;
                    for ch in 0..channels {
                        self.capture_buf[base + ch] = val;
                    }
                }
            }
        }

        let report_ns = self.host_clocks[0].read_noisy(
            TrueTime::from_seconds(first_cap_s),
            self.config.sender.capture_timestamp_std_s,
            &mut self.sender_stamp_rng,
        );
        let mut sink = SimSink::default();
        let _ = self.sender_engine.on_capture(
            &self.capture_buf,
            packet_frames,
            first_frame,
            report_ns,
            &mut sink,
        );
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
        let true_ns = self.host_clocks[0].read(at);
        let arrival_ns = self.links[from_node][0].stamp_rx(true_ns);
        let reply_ns = self.links[0][from_node].stamp_tx(true_ns);
        let mut sink = SimSink::default();
        let _ = self
            .sender_engine
            .on_datagram(from_addr, bytes, arrival_ns, reply_ns, &mut sink);
        self.deliver_from_sender(at, self.sender_epoch, sink.sent);
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

    fn apply_pending_sync(&mut self, speaker: usize) {
        let sp = &mut self.speakers[speaker];
        if let Some((clock_id, snap)) = sp.net.take_sync_update()
            && sp.playback.receiver().clock_id() == Some(clock_id)
        {
            sp.playback.apply_sync(snap);
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
        let dst_node = self.speakers[speaker].config.host + 1;
        let true_ns = self.host_clocks[dst_node].read(at);
        let arrival_ns = self.links[from_node][dst_node].stamp_rx(true_ns);
        let reply_ns = self.links[dst_node][from_node].stamp_tx(true_ns);
        let confirmed = self.speakers[speaker].confirmed_state();
        let mut sink = SimSink::default();
        let action = self.speakers[speaker]
            .net
            .on_datagram(
                from_addr, bytes, arrival_ns, reply_ns, confirmed, true, &mut sink,
            )
            .unwrap_or(DatagramAction::Consumed);
        match action {
            DatagramAction::Consumed => {}
            DatagramAction::Audio(header) => {
                self.ingest_audio(speaker, &header, bytes, arrival_ns);
            }
            DatagramAction::HullEcho(echo) => {
                self.speakers[speaker].playback.echo(&echo);
            }
        }
        self.apply_pending_sync(speaker);
        if !sink.sent.is_empty() {
            self.deliver_from_receiver(at, speaker, sink.sent);
        }
        self.schedule_next_net_wake(speaker, arrival_ns);
    }

    fn ingest_audio(&mut self, speaker: usize, header: &Audio, bytes: &[u8], arrival_ns: i64) {
        let sp = &mut self.speakers[speaker];
        let heard = match sp.config.audio_mode {
            AudioMode::FastCore => sp.playback.packet_header_only(header, arrival_ns),
            AudioMode::FullDsp => {
                let payload = bytes.get(packet::HEADER..).unwrap_or(&[]);
                sp.playback.packet(header, payload, arrival_ns)
            }
        };
        if let Some(heard) = heard {
            if heard.adopted || heard.restarted {
                sp.report_schedule.reset();
                sp.held_frames.reset();
                sp.last_timeline = Some(header.timeline);
                let confirmed = sp.confirmed_state();
                sp.net.sync_confirmed(confirmed);
            }
            if !heard.ignored {
                sp.held_frames
                    .mark_range(header.index, u64::from(header.frames));
            }
        }
    }

    fn on_receiver_net_step(&mut self, at: TrueTime, speaker: usize) {
        let host_node = self.speakers[speaker].config.host + 1;
        let local_now_ns = self.host_clocks[host_node].read(at);
        let confirmed = self.speakers[speaker].confirmed_state();
        let mut sink = SimSink::default();
        let _ = self.speakers[speaker]
            .net
            .step(local_now_ns, confirmed, &mut sink);
        self.apply_pending_sync(speaker);
        if !sink.sent.is_empty() {
            self.deliver_from_receiver(at, speaker, sink.sent);
        }
        self.schedule_next_net_wake(speaker, local_now_ns);
    }

    fn on_play_cycle(&mut self, at: TrueTime, speaker: usize, cycle: u64) {
        let rate = f64::from(self.config.sender.rate);
        let host_node = self.speakers[speaker].config.host + 1;
        let frame_count = self.speakers[speaker].config.cycle_frames;
        let first_dev_frame = cycle.saturating_mul(u64::from(frame_count));

        let (out_start_s, out_end_s) = {
            let sp = &mut self.speakers[speaker];
            let s0 = sp.leaves_s(u64_to_f64(first_dev_frame), rate);
            let s1 = sp.leaves_s(u64_to_f64(first_dev_frame + u64::from(frame_count)), rate);
            (s0, s1)
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

        let (plan, played) = {
            let sp = &mut self.speakers[speaker];
            let dev_pos = sp.device_frame_cursor;
            sp.device_frame_cursor = sp
                .device_frame_cursor
                .saturating_add(u64::from(frame_count));
            sp.next_cycle_index = cycle + 1;
            match sp.config.audio_mode {
                AudioMode::FastCore => {
                    let plan = sp
                        .playback
                        .cycle_plan_only(dev_pos, reported_start_ns, frame_count);
                    (plan, sp.playback.last())
                }
                AudioMode::FullDsp => {
                    sp.playback
                        .cycle(&mut sp.pcm_buf, dev_pos, reported_start_ns);
                    let plan = sp.playback.last_plan();
                    if sp.config.record_pcm {
                        let ch_count = usize::from(sp.playback.channels_u8()).max(1);
                        let channel0 = sp
                            .pcm_buf
                            .chunks_exact(ch_count)
                            .map(|frame| frame[0])
                            .collect();
                        sp.recorded_cycles.push(RecordedCycle {
                            out_start_s,
                            out_end_s,
                            plan,
                            channel0,
                        });
                    }
                    (plan, sp.playback.last())
                }
            }
        };

        self.record_cycle_trace_and_objectives(speaker, out_start_s, out_end_s, &plan, played);
        self.maybe_send_report(at, speaker);
        self.schedule_play_cycle(speaker, cycle + 1);
    }

    fn record_cycle_trace_and_objectives(
        &mut self,
        speaker: usize,
        out_start_s: f64,
        out_end_s: f64,
        plan: &Plan,
        played: unisono_runtime::pump::Played,
    ) {
        let rate = f64::from(self.config.sender.rate);
        let frame_count = self.speakers[speaker].config.cycle_frames as usize;
        let followed_tl = self.speakers[speaker].playback.receiver().timeline();
        let tl_info = followed_tl.and_then(|tl| self.timelines.get(&tl).cloned());

        // Update legacy Trace diagnostics.
        {
            let trace = &mut self.speakers[speaker].trace;
            trace.held = trace.held.saturating_add(u64::from(played.held));
            trace.absent = trace.absent.saturating_add(u64::from(played.concealed));
            if plan.frames == 0 {
                trace.idle_cycles += 1;
            } else {
                if plan.jumped {
                    trace.jumps.push(out_start_s);
                }
                if let Some(info) = &tl_info {
                    let pos = position_to_f64(plan.start);
                    let cap_frame = u64_to_f64(info.origin_capture_frame) + pos;
                    let cap_true_s = self.sender_device.when_seconds(cap_frame / rate);
                    let cap_sender_s = self.host_clocks[0].read_seconds(cap_true_s);
                    let due_true_s = self.host_clocks[0]
                        .when_seconds(cap_sender_s + nanos_to_seconds(info.level_ns));
                    trace.errors.push((out_start_s, out_start_s - due_true_s));
                }
            }
        }

        // Update canonical sample-level ObjectiveRecorder if enabled.
        let Some(rec) = self.objectives.as_mut() else {
            return;
        };
        let sp = &self.speakers[speaker];
        let lookahead = sp.playback.reach();
        let count_f = usize_to_f64(frame_count.max(1));
        let dt_cycle = out_end_s - out_start_s;
        let wanted = usize::try_from(plan.frames).unwrap_or(0).min(frame_count);
        let global_base = tl_info.as_ref().map_or(0, |info| info.global_frame_base);

        // Fast path: check if the entire planned cycle's resampler window is
        // contiguously held, avoiding per-sample `is_playable` scans.
        let all_playable = if wanted > 0 {
            let first_pos = position_to_f64(plan.start);
            let last_pos = plan
                .start
                .advance(plan.step, (wanted - 1) as u64)
                .map_or(first_pos, position_to_f64);
            let reach = usize_to_f64(lookahead);
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let lo = (first_pos - reach).floor().max(0.0) as u64;
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let hi = (last_pos + reach).ceil().max(0.0) as u64;
            sp.held_frames.range_fully_held(lo, hi)
        } else {
            false
        };

        for idx in 0..frame_count {
            let out_s = out_start_s + (usize_to_f64(idx) / count_f) * dt_cycle;
            let effective = if idx < wanted {
                plan.start.advance(plan.step, idx as u64).and_then(|pos| {
                    let local_pos = position_to_f64(pos);
                    let checked = if all_playable {
                        Some(local_pos)
                    } else {
                        check_playable(Some(local_pos), lookahead, |f| sp.held_frames.is_held(f))
                    };
                    checked.map(|p| p + u64_to_f64(global_base))
                })
            } else {
                None
            };
            rec.record_playback_sample(speaker, out_s, effective);
        }
    }

    fn maybe_send_report(&mut self, at: TrueTime, speaker: usize) {
        let PathDelay::Measured(reporting) = self.speakers[speaker].config.path else {
            return;
        };
        let host_node = self.speakers[speaker].config.host + 1;
        let local_now_ns = self.host_clocks[host_node].read(at);
        let sp = &mut self.speakers[speaker];
        if sp.playback.receiver().timeline().is_none() {
            return;
        }
        if !sp.report_schedule.due(reporting, local_now_ns) {
            return;
        }
        let Some(report) = sp.playback.report() else {
            return;
        };
        sp.report_schedule.record_sent(reporting, local_now_ns);
        let outgoing = Outgoing {
            report,
            needs: sp.playback.recent(),
        };
        let confirmed = sp.confirmed_state();
        sp.net.sync_confirmed(confirmed);
        let mut sink = SimSink::default();
        let _ = sp.net.send_report(&outgoing, &mut sink);
        if !sink.sent.is_empty() {
            self.deliver_from_receiver(at, speaker, sink.sent);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AudioMode, HeldFrames, ReceiverConfig, Scene, SceneConfig, SenderConfig, SignalMode,
        decode_ramp_position, ramp_sample,
    };
    use crate::TrueTime;
    use crate::clock::{FrequencyNoise, OscillatorModel};
    use crate::link::LinkModel;
    use crate::objectives::{ObjectiveWeights, is_playable};
    use crate::random::Generator;
    use crate::scene::HostConfig;

    #[test]
    fn held_frames_bitmap_matches_naive_playable_checks() {
        let mut held = HeldFrames::new(4_096);
        held.mark_range(0, 240);
        held.mark_range(240, 240);
        held.mark_range(720, 240); // gap at [480, 720)
        assert!(held.range_fully_held(0, 479));
        assert!(!held.range_fully_held(0, 480));
        assert!(is_playable(200.5, 24, |f| held.is_held(f)));
        assert!(!is_playable(470.5, 24, |f| held.is_held(f)));
        assert!(!is_playable(730.0, 24, |f| held.is_held(f)));
        assert!(is_playable(800.25, 24, |f| held.is_held(f)));
    }

    #[test]
    fn ramp_signal_roundtrips_fractional_positions_away_from_corners() {
        for &frame in &[100u32, 5_000, 13_000, 13_200, 20_000, 30_000] {
            let sample = ramp_sample(u64::from(frame));
            let expected = f64::from(frame);
            let decoded =
                decode_ramp_position(sample, expected, 30.0).expect("interior frame should decode");
            assert!(
                (decoded - expected).abs() < 1e-3,
                "frame {frame}: decoded {decoded}"
            );
        }
    }

    #[test]
    fn fast_core_and_full_dsp_produce_identical_plans_and_accurate_ramp_pcm() {
        let build = |mode: AudioMode| {
            let mut sender = SenderConfig::standard(
                OscillatorModel::ideal(5.0),
                OscillatorModel::ideal(0.0),
                20_000_000,
            );
            sender.signal = SignalMode::Ramp;
            let hosts = vec![HostConfig {
                clock: OscillatorModel {
                    offset: -10.0,
                    frequency: 20e-6,
                    noise: FrequencyNoise::ZERO,
                },
                from_sender: LinkModel::IDEAL,
                to_sender: LinkModel::IDEAL,
            }];
            let mut rx = ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0));
            rx.audio_mode = mode;
            rx.record_pcm = mode == AudioMode::FullDsp;
            let mut cfg = SceneConfig::new(sender, hosts, vec![rx]);
            cfg.objective_window = Some((0.8, 1.5));
            cfg.objective_weights = ObjectiveWeights {
                sync: 1e6,
                latency: 1.0,
                tracking: 1e4,
                roughness: 1.0,
                missed: 1.0,
                discontinuities: 1.0,
            };
            let mut scene = Scene::new(cfg, &Generator::new(7));
            scene.run(TrueTime::from_seconds(1.6));
            scene
        };

        let fast = build(AudioMode::FastCore);
        let full = build(AudioMode::FullDsp);

        // Plans and timing traces must match identically between FastCore and FullDsp.
        assert_eq!(fast.traces()[0].errors.len(), full.traces()[0].errors.len());
        for (a, b) in fast.traces()[0].errors.iter().zip(&full.traces()[0].errors) {
            assert!((a.0 - b.0).abs() < 1e-12);
            assert!((a.1 - b.1).abs() < 1e-12);
        }

        // Verify FullDsp decoded PCM ramp matches exact planned source positions.
        let mut checked = 0usize;
        let mut max_err = 0.0_f64;
        let mut worst_info = (0.0_f64, 0.0_f32, 0.0_f64, 0.0_f64);
        for cycle in full.recorded_cycles(0) {
            if cycle.out_start_s < 0.8 || cycle.plan.frames == 0 {
                continue;
            }
            for (i, &sample) in cycle.channel0.iter().enumerate() {
                if i >= cycle.plan.frames as usize {
                    break;
                }
                let Some(pos) = cycle.plan.start.advance(cycle.plan.step, i as u64) else {
                    continue;
                };
                let expected = super::position_to_f64(pos);
                if let Some(decoded) = decode_ramp_position(sample, expected, 40.0) {
                    let err = (decoded - expected).abs();
                    if err > max_err {
                        max_err = err;
                        worst_info = (cycle.out_start_s, sample, expected, decoded);
                    }
                    checked += 1;
                }
            }
        }
        assert!(
            checked > 20_000,
            "expected >20k checked samples, got {checked}"
        );
        assert!(
            max_err < 1e-3,
            "FullDsp ramp error {max_err} frames exceeds 1e-3 (out={:.4}, sample={}, expected={:.3}, decoded={:.3})",
            worst_info.0,
            worst_info.1,
            worst_info.2,
            worst_info.3
        );

        let fast_obj = fast.finish_objectives().expect("fast objectives");
        let full_obj = full.finish_objectives().expect("full objectives");
        assert!(
            (fast_obj.tracking_s2 - full_obj.tracking_s2).abs() < 1e-15
                && (fast_obj.roughness_per_s2 - full_obj.roughness_per_s2).abs() < 1e-15,
            "FastCore and FullDsp objectives diverged: {fast_obj:?} vs {full_obj:?}"
        );
    }
}
