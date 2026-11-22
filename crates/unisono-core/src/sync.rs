// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Unified fixed-point synchronization engine (Peer by default, degenerating
//! mathematically and structurally to Star when no peers are active).
//!
//! Each receiver maintains:
//! - One 4-timestamp NTP exchange pipeline ([`SlidingMinRtt`] +
//!   [`KalmanFilter`]) to the stream sender (`host 0`), driven by `Report` and
//!   v2 `Echo` packets.
//! - Zero to [`MAX_DIRECT_PEERS`] direct peer pipelines driven by `PeerProbe`
//!   and `PeerEcho` packets.
//! - A bounded table of non-incident link measurements received via
//!   `PeerRelay` broadcasts, extrapolated across their clock-offset-invariant
//!   `age_ns` plus relayer one-way path delay.
//!
//! When zero peers are configured or reachable, [`Sync::step`] exports the
//! sender [`KalmanFilter`] line directly (`peer_active = false`), yielding
//! exact Star synchronization. When one or more peers are active,
//! [`Sync::step`] solves the host-graph BLUE via [`solve_blue`], updates
//! decoupled common-mode (`sender - fleet_mean`) and differential-mode
//! (`fleet_mean - self`) Kalman filters with bumpless membership transfers,
//! and exports a compact [`SyncSnapshot`] for O(1) audio-thread playback.

use crate::arrivals::Arrivals;
use crate::blue::{EdgeObs, MAX_EDGES, MAX_HOSTS, solve_blue};
use crate::fixed::{
    div_floor_wide, saturate, saturating_mul_i64, saturating_mul_i128, scale_div_pow2,
};
use crate::kalman::{DEFAULT_JUMP_NS, KalmanFilter, LINE_RUN, NoisePrior};
use crate::min_rtt::{
    DEFAULT_INITIAL_VARIANCE_NS2, DEFAULT_VARIANCE_FLOOR_NS2, Exchange, Measurement, SlidingMinRtt,
};
use crate::packet::{Echo, MAX_RELAY_EDGES, PeerEcho, PeerProbe, PeerRelay, RelayEdge};
use crate::relation::Line;

/// Maximum number of direct peers configured on one receiver (`1` sender +
/// `1` self + `15` peers = [`MAX_HOSTS`] = `17`).
pub const MAX_DIRECT_PEERS: usize = 15;

/// Capacity of the sliding-window minimum-RTT selector per link.
pub const MIN_RTT_WINDOW: usize = 8;

/// Stride of the sliding-window minimum-RTT selector per link.
pub const MIN_RTT_STRIDE: usize = 4;

/// Number of recent in-flight probe/report departures remembered per link.
pub const INFLIGHT_CAP: usize = 8;

/// Maximum non-incident relayed edges retained in the local graph table.
pub const MAX_RELAY_TABLE: usize = 128;

/// Default peer / relayed-edge staleness timeout, in nanoseconds (`5 s`).
pub const DEFAULT_PEER_STALE_NS: i64 = 5_000_000_000;

/// Default fast-probing startup window, in nanoseconds (`4 s`).
pub const DEFAULT_STARTUP_DURATION_NS: i64 = 4_000_000_000;

/// Default startup probe cadence, in nanoseconds (`50 ms` = 20 Hz).
pub const DEFAULT_STARTUP_PROBE_NS: i64 = 50_000_000;

/// Default steady-state probe cadence, in nanoseconds (`250 ms` = 4 Hz).
pub const DEFAULT_STEADY_PROBE_NS: i64 = 250_000_000;

/// Default peer link-state relay broadcast cadence, in nanoseconds (`250 ms`).
pub const DEFAULT_RELAY_INTERVAL_NS: i64 = 250_000_000;

/// Unity static link-weight multiplier in Q16 (`1.0`).
pub const WEIGHT_UNITY_Q16: u32 = 65_536;

/// One second in nanoseconds.
const BILLION: i128 = 1_000_000_000;

/// Maximum variance cap for extrapolated/weighted edges (`(1 s)^2`).
const MAX_EDGE_VAR_NS2: u64 = 1_000_000_000_000_000_000;

/// Maximum fractional frequency magnitude tracked on a relayed edge (`500 ppm`
/// in Q48).
const MAX_RELAY_FREQ_Q48: i64 = 140_737_488_355;

/// Minimum elapsed time between relayed measurements before updating the
/// per-edge frequency slope (`50 ms`).
const MIN_RELAY_SLOPE_DT_NS: i64 = 50_000_000;

/// A zero-valued [`Line`] used before lock or for unused modal components.
pub const ZERO_LINE: Line = Line {
    time: 0,
    value: 0,
    rise: 0,
    run: LINE_RUN,
};

/// Configuration for [`Sync`].
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct SyncSettings {
    /// Stream identifier accepted by this receiver.
    pub stream: u16,
    /// Unique non-zero receiver identity.
    pub identity: u64,
    /// Process noise prior for the stream sender's clock.
    pub sender_prior: NoisePrior,
    /// Process noise prior for receiver host clocks.
    pub local_prior: NoisePrior,
    /// Conservative floor on online measurement variance, in square
    /// nanoseconds.
    pub variance_floor_ns2: u64,
    /// Initial online variance prior before enough exchanges arrive, in
    /// square nanoseconds.
    pub initial_variance_ns2: u64,
    /// Step threshold above which a link Kalman filter re-anchors, in
    /// nanoseconds.
    pub jump_ns: i64,
    /// Age after which a silent peer or relayed edge is excluded from the
    /// BLUE graph, in nanoseconds.
    pub peer_stale_ns: i64,
    /// Duration of fast startup probing after the first activity, in
    /// nanoseconds.
    pub startup_duration_ns: i64,
    /// Probe interval during startup, in nanoseconds.
    pub startup_probe_ns: i64,
    /// Probe interval during steady state, in nanoseconds.
    pub steady_probe_ns: i64,
    /// Interval between peer link-state relay broadcasts, in nanoseconds.
    pub relay_interval_ns: i64,
}

impl SyncSettings {
    /// Standard conservative settings for consumer quartz hosts with a
    /// `(5 us)^2` variance floor, 20 Hz startup probing (4 s), and 4 Hz
    /// steady-state probing/relaying.
    #[must_use]
    pub fn standard(stream: u16, identity: u64) -> Self {
        SyncSettings {
            stream,
            identity,
            sender_prior: NoisePrior::CONSUMER_QUARTZ,
            local_prior: NoisePrior::CONSUMER_QUARTZ,
            variance_floor_ns2: DEFAULT_VARIANCE_FLOOR_NS2,
            initial_variance_ns2: DEFAULT_INITIAL_VARIANCE_NS2,
            jump_ns: DEFAULT_JUMP_NS,
            peer_stale_ns: DEFAULT_PEER_STALE_NS,
            startup_duration_ns: DEFAULT_STARTUP_DURATION_NS,
            startup_probe_ns: DEFAULT_STARTUP_PROBE_NS,
            steady_probe_ns: DEFAULT_STEADY_PROBE_NS,
            relay_interval_ns: DEFAULT_RELAY_INTERVAL_NS,
        }
    }
}

/// Compact, wait-free snapshot published from [`Sync`] on the network thread
/// to [`crate::receiver::Receiver`] on the real-time audio thread.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct SyncSnapshot {
    /// Whether a valid clock estimate has been established.
    pub valid: bool,
    /// Whether peer-assisted BLUE + modal control is currently active
    /// (`active_peers > 0`). When `false`, `common_line` gives the direct Star
    /// estimate `sender_clock - local_clock` and `fleet_line` is [`ZERO_LINE`].
    pub peer_active: bool,
    /// Incremented whenever the active peer set changes or `peer_active`
    /// toggles, telling [`crate::player::ModalPlayer`] to perform a bumpless
    /// anchor transfer.
    pub epoch: u32,
    /// In Peer mode: estimates `fleet_mean_clock - local_clock` as a function
    /// of `local_clock`. Zero in Star mode.
    pub fleet_line: Line,
    /// In Peer mode: estimates `sender_clock - fleet_mean_clock` as a function
    /// of `local_clock`.
    /// In Star mode: estimates `sender_clock - local_clock` as a function of
    /// `local_clock`.
    pub common_line: Line,
    /// Causal half-RTT one-way path delay from sender to this receiver, in
    /// nanoseconds.
    pub path_ns: i64,
    /// Number of active peers currently contributing to the BLUE graph (`0` in
    /// Star mode).
    pub active_peers: u8,
    /// Common-mode measurement variance (or sender-link variance in Star), in
    /// square nanoseconds.
    pub common_var_ns2: u64,
    /// Self differential-mode measurement variance (`0` in Star), in square
    /// nanoseconds.
    pub diff_var_ns2: u64,
}

impl SyncSnapshot {
    /// Empty snapshot before any valid clock estimate exists.
    pub const EMPTY: SyncSnapshot = SyncSnapshot {
        valid: false,
        peer_active: false,
        epoch: 0,
        fleet_line: ZERO_LINE,
        common_line: ZERO_LINE,
        path_ns: 0,
        active_peers: 0,
        common_var_ns2: 0,
        diff_var_ns2: 0,
    };

    /// Evaluates the estimated sender clock at local clock reading `local_ns`.
    #[must_use]
    pub fn sender_time(&self, local_ns: i64) -> i64 {
        if !self.valid {
            return local_ns;
        }
        let com = self.common_line.eval(local_ns) as i128;
        let diff = if self.peer_active {
            self.fleet_line.eval(local_ns) as i128
        } else {
            0
        };
        saturate((local_ns as i128).saturating_add(diff).saturating_add(com))
    }

    /// Evaluates the common-mode offset `sender_clock - fleet_mean_clock` (in
    /// Peer mode) or `sender_clock - local_clock` (in Star mode) at `local_ns`.
    #[must_use]
    pub fn common_offset_ns(&self, local_ns: i64) -> i64 {
        if !self.valid {
            return 0;
        }
        self.common_line.eval(local_ns)
    }

    /// Evaluates the differential offset `fleet_mean_clock - local_clock` in
    /// Peer mode, or `0` in Star mode.
    #[must_use]
    pub fn diff_offset_ns(&self, local_ns: i64) -> i64 {
        if !self.valid || !self.peer_active {
            return 0;
        }
        self.fleet_line.eval(local_ns)
    }
}

/// Direct peer-link estimation and probing state.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
#[allow(clippy::struct_excessive_bools)]
struct PeerSlot {
    configured: bool,
    identity: u64,
    weight_q16: u32,
    next_seq: u64,
    has_probed: bool,
    next_probe_ns: i64,
    departures: Arrivals<INFLIGHT_CAP>,
    rtt_selector: SlidingMinRtt<MIN_RTT_WINDOW>,
    filter: KalmanFilter,
    has_meas: bool,
    last_meas: Measurement,
    last_heard_ns: i64,
    has_relay_seq: bool,
    last_relay_seq: u64,
}

impl PeerSlot {
    fn empty(prior: NoisePrior, settings: &SyncSettings) -> Self {
        PeerSlot {
            configured: false,
            identity: 0,
            weight_q16: WEIGHT_UNITY_Q16,
            next_seq: 0,
            has_probed: false,
            next_probe_ns: 0,
            departures: Arrivals::new(),
            rtt_selector: SlidingMinRtt::new(
                MIN_RTT_STRIDE,
                settings.initial_variance_ns2,
                settings.variance_floor_ns2,
            ),
            filter: KalmanFilter::new(prior, settings.jump_ns),
            has_meas: false,
            last_meas: Measurement {
                id: 0,
                midpoint_ns: 0,
                offset_ns: 0,
                rtt_ns: 0,
                variance_ns2: settings.initial_variance_ns2,
            },
            last_heard_ns: 0,
            has_relay_seq: false,
            last_relay_seq: 0,
        }
    }
}

/// One non-incident link measurement received via [`PeerRelay`], stored in
/// canonical host-identity order (`from_id < to_id`, where `0` is sender).
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
struct RelayedSlot {
    used: bool,
    from_id: u64,
    to_id: u64,
    /// Estimated local-clock timestamp when the measurement midpoint occurred.
    meas_time_ns: i64,
    /// Local-clock timestamp when this slot was last refreshed.
    last_rx_ns: i64,
    /// Measured offset `clock(to_id) - clock(from_id)` at `meas_time_ns`.
    offset_ns: i64,
    /// Variance of `offset_ns` at `meas_time_ns`, in square nanoseconds.
    variance_ns2: u64,
    /// Whether a per-edge slope estimate has been initialized.
    has_freq: bool,
    /// Smoothed relative fractional frequency of `clock(to_id) - clock(from_id)`
    /// in Q48 units.
    freq_q48: i64,
}

impl RelayedSlot {
    const EMPTY: RelayedSlot = RelayedSlot {
        used: false,
        from_id: 0,
        to_id: 0,
        meas_time_ns: 0,
        last_rx_ns: 0,
        offset_ns: 0,
        variance_ns2: 0,
        has_freq: false,
        freq_q48: 0,
    };
}

/// Clamps a variance `i128` into `[1, MAX_EDGE_VAR_NS2]` as `u64`.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn clamp_var_u64(v: i128) -> u64 {
    if v <= 1 {
        1
    } else if v > MAX_EDGE_VAR_NS2 as i128 {
        MAX_EDGE_VAR_NS2
    } else {
        v as u64
    }
}

/// Applies an optional Q16 static link-weight multiplier to a variance
/// (`weight_q16 = 65_536` leaves `var_ns2` unchanged; larger weights reduce
/// effective variance proportionally).
fn apply_weight_q16(var_ns2: u64, weight_q16: u32) -> u64 {
    if weight_q16 == 0 || weight_q16 == WEIGHT_UNITY_Q16 {
        return if var_ns2 == 0 { 1 } else { var_ns2 };
    }
    let scaled = div_floor_wide(
        saturating_mul_i128(var_ns2 as i128, WEIGHT_UNITY_Q16 as i128),
        weight_q16 as i128,
    );
    clamp_var_u64(scaled)
}

/// Inflates a measurement variance by clock-drift uncertainty over `age_ns`
/// using the pair's [`NoisePrior`] and an optional frequency variance
/// `p11_q80` (in Q80 dimensionless units).
fn inflate_variance(base_var_ns2: u64, age_ns: i64, prior: NoisePrior, p11_q80: i128) -> u64 {
    if age_ns <= 0 {
        return if base_var_ns2 == 0 { 1 } else { base_var_ns2 };
    }
    let age = if age_ns > 100_000_000_000 {
        100_000_000_000
    } else {
        age_ns
    } as i128;
    // White-frequency term: `(q0_q16_ns2_per_s * age / 1e9) >> 16`.
    let white_q16 = div_floor_wide(saturating_mul_i128(prior.q0_q16_ns2_per_s, age), BILLION);
    let white_ns2 = if white_q16 > 0 {
        white_q16.wrapping_shr(16)
    } else {
        0
    };
    // Frequency-uncertainty term: `p11_q80 * age^2 >> 80`.
    let p11_pos = if p11_q80 > 0 { p11_q80 } else { 0 };
    let p11_step1 = saturating_mul_i128(p11_pos, age).wrapping_shr(40);
    let freq_ns2 = saturating_mul_i128(p11_step1, age).wrapping_shr(40);
    // Random-walk term: `(q2_q80_per_s * age / 1e9) * age^2 / 3 >> 80`.
    let q2_pos = if prior.q2_q80_per_s > 0 {
        prior.q2_q80_per_s
    } else {
        0
    };
    let q2_dt = div_floor_wide(saturating_mul_i128(q2_pos, age), BILLION);
    let walk_step1 = saturating_mul_i128(q2_dt, age).wrapping_shr(40);
    let walk_ns2 = div_floor_wide(saturating_mul_i128(walk_step1, age).wrapping_shr(40), 3);
    let total = (base_var_ns2 as i128)
        .saturating_add(white_ns2)
        .saturating_add(freq_ns2)
        .saturating_add(walk_ns2);
    clamp_var_u64(total)
}

/// Extrapolates an offset by `freq_q48 * age_ns / 2^48` safely.
fn extrapolate_offset(offset_ns: i64, freq_q48: i64, age_ns: i64) -> i64 {
    if age_ns <= 0 || freq_q48 == 0 {
        return offset_ns;
    }
    let age = if age_ns > 100_000_000_000 {
        100_000_000_000
    } else {
        age_ns
    } as i128;
    let delta = saturating_mul_i128(freq_q48 as i128, age).wrapping_shr(48);
    saturate((offset_ns as i128).saturating_add(delta))
}

/// Clamps `x` to `[-hi, hi]` in `i64` for `hi >= 0`.
fn clamp_i64(x: i64, hi: i64) -> i64 {
    let lo = 0i64.wrapping_sub(hi);
    if x > hi {
        hi
    } else if x < lo {
        lo
    } else {
        x
    }
}

/// Reads `slice[idx]` with default `false`.
fn get_bool(slice: &[bool], idx: usize) -> bool {
    match slice.get(idx) {
        Some(v) => *v,
        None => false,
    }
}

/// Converts a non-negative `i64` age in nanoseconds to `u32` (saturating at
/// `u32::MAX`).
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn age_to_u32(age_ns: i64) -> u32 {
    if age_ns <= 0 {
        0
    } else if age_ns > u32::MAX as i64 {
        u32::MAX
    } else {
        age_ns as u32
    }
}

/// Unified fixed-point Peer / Star clock synchronization state machine.
#[cfg_attr(not(translating), derive(Debug))]
#[allow(clippy::struct_excessive_bools)]
pub struct Sync {
    settings: SyncSettings,
    has_started: bool,
    start_ns: i64,

    // Sender link (`0 <-> self`).
    sender_weight_q16: u32,
    sender_departures: Arrivals<INFLIGHT_CAP>,
    sender_min_rtt: SlidingMinRtt<MIN_RTT_WINDOW>,
    sender_filter: KalmanFilter,
    sender_has_meas: bool,
    sender_last_meas: Measurement,

    // Direct peers (`1..=peer_count`).
    peer_count: usize,
    peers: [PeerSlot; MAX_DIRECT_PEERS],

    // Relayed non-incident edges.
    relayed: [RelayedSlot; MAX_RELAY_TABLE],
    relay_seq: u64,
    has_relayed: bool,
    next_relay_ns: i64,

    // Modal Kalman filters (used when `active_peers > 0`).
    common_filter: KalmanFilter,
    diff_filter: KalmanFilter,
    peer_active: bool,
    last_active_mask: u32,
    epoch: u32,
    dirty: bool,
    has_fused: bool,
    last_fuse_ns: i64,
    snapshot: SyncSnapshot,
}

impl Sync {
    /// Creates a new synchronization engine with zero configured peers (Star
    /// until peers are registered via [`Sync::add_peer`]).
    #[must_use]
    pub fn new(settings: SyncSettings) -> Self {
        let sender_pair_prior = settings.sender_prior.combine(settings.local_prior);
        let peer_pair_prior = settings.local_prior.combine(settings.local_prior);
        let empty_peer = PeerSlot::empty(peer_pair_prior, &settings);
        Sync {
            settings,
            has_started: false,
            start_ns: 0,
            sender_weight_q16: WEIGHT_UNITY_Q16,
            sender_departures: Arrivals::new(),
            sender_min_rtt: SlidingMinRtt::new(
                MIN_RTT_STRIDE,
                settings.initial_variance_ns2,
                settings.variance_floor_ns2,
            ),
            sender_filter: KalmanFilter::new(sender_pair_prior, settings.jump_ns),
            sender_has_meas: false,
            sender_last_meas: Measurement {
                id: 0,
                midpoint_ns: 0,
                offset_ns: 0,
                rtt_ns: 0,
                variance_ns2: settings.initial_variance_ns2,
            },
            peer_count: 0,
            peers: [empty_peer; MAX_DIRECT_PEERS],
            relayed: [RelayedSlot::EMPTY; MAX_RELAY_TABLE],
            relay_seq: 0,
            has_relayed: false,
            next_relay_ns: 0,
            common_filter: KalmanFilter::new(sender_pair_prior, settings.jump_ns),
            diff_filter: KalmanFilter::new(settings.local_prior, settings.jump_ns),
            peer_active: false,
            last_active_mask: 0,
            epoch: 0,
            dirty: false,
            has_fused: false,
            last_fuse_ns: 0,
            snapshot: SyncSnapshot::EMPTY,
        }
    }

    /// Sets an optional Q16 static weight multiplier for the direct sender
    /// link (`WEIGHT_UNITY_Q16 = 65_536` for `1.0`).
    pub fn set_sender_weight_q16(&mut self, weight_q16: u32) {
        self.sender_weight_q16 = if weight_q16 == 0 {
            WEIGHT_UNITY_Q16
        } else {
            weight_q16
        };
    }

    /// Registers a direct peer with the given non-zero `identity` and optional
    /// Q16 static weight multiplier. Returns its peer slot index
    /// (`0..MAX_DIRECT_PEERS`), or `None` if `identity` is `0`, equals this
    /// receiver's identity, is already registered, or the table is full.
    pub fn add_peer(&mut self, identity: u64, weight_q16: u32) -> Option<usize> {
        if identity == 0
            || identity == self.settings.identity
            || self.peer_count >= MAX_DIRECT_PEERS
        {
            return None;
        }
        let mut i = 0usize;
        while i < self.peer_count {
            if let Some(p) = self.peers.get(i)
                && p.configured
                && p.identity == identity
            {
                return None;
            }
            i = i.saturating_add(1);
        }
        let idx = self.peer_count;
        let peer_pair_prior = self.settings.local_prior.combine(self.settings.local_prior);
        let mut slot = PeerSlot::empty(peer_pair_prior, &self.settings);
        slot.configured = true;
        slot.identity = identity;
        slot.weight_q16 = if weight_q16 == 0 {
            WEIGHT_UNITY_Q16
        } else {
            weight_q16
        };
        if let Some(dst) = self.peers.get_mut(idx) {
            *dst = slot;
            self.peer_count = idx.saturating_add(1);
            Some(idx)
        } else {
            None
        }
    }

    /// Number of configured direct peers (`0..=MAX_DIRECT_PEERS`).
    #[must_use]
    pub fn peer_count(&self) -> usize {
        self.peer_count
    }

    /// Looks up the slot index of a configured peer by `identity`.
    #[must_use]
    pub fn find_peer(&self, identity: u64) -> Option<usize> {
        let mut i = 0usize;
        while i < self.peer_count {
            if let Some(p) = self.peers.get(i)
                && p.configured
                && p.identity == identity
            {
                return Some(i);
            }
            i = i.saturating_add(1);
        }
        None
    }

    /// Latest published [`SyncSnapshot`].
    #[must_use]
    pub fn snapshot(&self) -> SyncSnapshot {
        self.snapshot
    }

    /// Current probing interval (`startup_probe_ns` during the fast startup
    /// window, `steady_probe_ns` thereafter).
    #[must_use]
    pub fn probe_interval_ns(&self, now_ns: i64) -> i64 {
        let startup = if self.settings.startup_probe_ns > 0 {
            self.settings.startup_probe_ns
        } else {
            DEFAULT_STARTUP_PROBE_NS
        };
        let steady = if self.settings.steady_probe_ns > 0 {
            self.settings.steady_probe_ns
        } else {
            DEFAULT_STEADY_PROBE_NS
        };
        if !self.has_started {
            return startup;
        }
        if now_ns.saturating_sub(self.start_ns) < self.settings.startup_duration_ns {
            startup
        } else {
            steady
        }
    }

    /// Records the first observed local-clock timestamp to anchor the fast
    /// startup probing phase.
    fn note_started(&mut self, now_ns: i64) {
        if !self.has_started {
            self.has_started = true;
            self.start_ns = now_ns;
        }
    }

    /// Resets sender-clock state (for example when the sender reboots and
    /// changes its `clock_id`), preserving direct peer-to-peer estimates.
    pub fn reset_sender_clock(&mut self) {
        self.sender_departures = Arrivals::new();
        self.sender_min_rtt.reset();
        self.sender_filter.reset();
        self.sender_has_meas = false;
        self.common_filter.reset();
        // Drop relayed sender edges `(0, peer)` since sender clock epoch changed.
        let mut i = 0usize;
        while i < MAX_RELAY_TABLE {
            if let Some(slot) = self.relayed.get_mut(i)
                && slot.used
                && slot.from_id == 0
            {
                *slot = RelayedSlot::EMPTY;
            }
            i = i.saturating_add(1);
        }
        self.epoch = self.epoch.wrapping_add(1);
        self.snapshot = SyncSnapshot::EMPTY;
        self.has_fused = false;
        self.dirty = false;
    }

    /// Records the local departure timestamp `t1_ns` of a sent stream `Report`.
    pub fn report_departed(&mut self, sequence: u64, t1_ns: i64) {
        self.note_started(t1_ns);
        self.sender_departures.record(sequence, t1_ns);
    }

    /// Processes a sender v2 [`Echo`] that arrived at local clock reading
    /// `t4_ns`. Returns `true` if a new deduplicated minimum-RTT measurement
    /// was accepted.
    pub fn on_sender_echo(&mut self, echo: &Echo, t4_ns: i64) -> bool {
        if echo.stream != self.settings.stream || echo.receiver != self.settings.identity {
            return false;
        }
        self.note_started(t4_ns);
        let Some(t1_ns) = self.sender_departures.find(echo.sequence) else {
            return false;
        };
        let ex = Exchange {
            id: echo.sequence,
            t1: t1_ns,
            t2: echo.arrival,
            t3: echo.departure,
            t4: t4_ns,
        };
        let Some(meas) = self.sender_min_rtt.observe(ex) else {
            return false;
        };
        self.sender_has_meas = true;
        self.sender_last_meas = meas;
        let weighted_var = apply_weight_q16(meas.variance_ns2, self.sender_weight_q16);
        self.sender_filter
            .update(meas.midpoint_ns, meas.offset_ns, weighted_var);
        self.dirty = true;
        true
    }

    /// Earliest local-clock time at which any configured peer is due for its
    /// next probe, or `None` when no peers are configured.
    #[must_use]
    pub fn next_peer_probe_at(&self, now_ns: i64) -> Option<i64> {
        if self.peer_count == 0 {
            return None;
        }
        let mut earliest: Option<i64> = None;
        let mut i = 0usize;
        while i < self.peer_count {
            if let Some(p) = self.peers.get(i)
                && p.configured
            {
                let due = if p.has_probed {
                    p.next_probe_ns
                } else {
                    now_ns
                };
                earliest = match earliest {
                    Some(prev) if prev <= due => Some(prev),
                    _ => Some(due),
                };
            }
            i = i.saturating_add(1);
        }
        earliest
    }

    /// Emits the next due [`PeerProbe`] at `now_ns`, returning
    /// `(peer_idx, probe)`. Callers should repeat until `None` when draining
    /// due probes on a tick.
    pub fn next_peer_probe(&mut self, now_ns: i64) -> Option<(usize, PeerProbe)> {
        if self.peer_count == 0 {
            return None;
        }
        self.note_started(now_ns);
        let interval = self.probe_interval_ns(now_ns);
        let stagger_step = if self.peer_count > 1 {
            saturate(div_floor_wide(interval as i128, self.peer_count as i128))
        } else {
            0
        };
        let mut i = 0usize;
        while i < self.peer_count {
            if let Some(p) = self.peers.get_mut(i)
                && p.configured
                && (!p.has_probed || now_ns >= p.next_probe_ns)
            {
                let seq = p.next_seq;
                p.next_seq = seq.wrapping_add(1);
                let next_at = if p.has_probed {
                    now_ns.saturating_add(interval)
                } else {
                    // `i < MAX_DIRECT_PEERS`, so the cast never wraps.
                    #[allow(clippy::cast_possible_wrap)]
                    let offset = saturating_mul_i64(i as i64, stagger_step);
                    now_ns.saturating_add(interval).saturating_add(offset)
                };
                p.has_probed = true;
                p.next_probe_ns = next_at;
                let probe = PeerProbe {
                    stream: self.settings.stream,
                    prober: self.settings.identity,
                    target: p.identity,
                    sequence: seq,
                };
                return Some((i, probe));
            }
            i = i.saturating_add(1);
        }
        None
    }

    /// Records the local departure timestamp `t1_ns` of a sent [`PeerProbe`]
    /// to `peer_idx`.
    pub fn peer_probe_departed(&mut self, peer_idx: usize, sequence: u64, t1_ns: i64) {
        self.note_started(t1_ns);
        if let Some(p) = self.peers.get_mut(peer_idx)
            && p.configured
        {
            p.departures.record(sequence, t1_ns);
        }
    }

    /// Answers an incoming [`PeerProbe`] from a configured peer with an
    /// immediate [`PeerEcho`] carrying `arrival` (`T2`) and `departure` (`T3`).
    #[must_use]
    pub fn on_peer_probe(
        &self,
        probe: &PeerProbe,
        arrival_ns: i64,
        departure_ns: i64,
    ) -> Option<PeerEcho> {
        if probe.stream != self.settings.stream || probe.target != self.settings.identity {
            return None;
        }
        if self.find_peer(probe.prober).is_none() {
            return None;
        }
        Some(PeerEcho {
            stream: self.settings.stream,
            prober: probe.prober,
            responder: self.settings.identity,
            sequence: probe.sequence,
            arrival: arrival_ns,
            departure: departure_ns,
        })
    }

    /// Processes an incoming [`PeerEcho`] that arrived at `t4_ns`. Returns
    /// `true` if a new deduplicated minimum-RTT peer measurement was accepted.
    pub fn on_peer_echo(&mut self, echo: &PeerEcho, t4_ns: i64) -> bool {
        if echo.stream != self.settings.stream || echo.prober != self.settings.identity {
            return false;
        }
        self.note_started(t4_ns);
        let Some(peer_idx) = self.find_peer(echo.responder) else {
            return false;
        };
        let Some(p) = self.peers.get_mut(peer_idx) else {
            return false;
        };
        p.last_heard_ns = t4_ns;
        let Some(t1_ns) = p.departures.find(echo.sequence) else {
            return false;
        };
        let ex = Exchange {
            id: echo.sequence,
            t1: t1_ns,
            t2: echo.arrival,
            t3: echo.departure,
            t4: t4_ns,
        };
        let Some(meas) = p.rtt_selector.observe(ex) else {
            return false;
        };
        p.has_meas = true;
        p.last_meas = meas;
        let weighted_var = apply_weight_q16(meas.variance_ns2, p.weight_q16);
        p.filter
            .update(meas.midpoint_ns, meas.offset_ns, weighted_var);
        self.dirty = true;
        true
    }

    /// Earliest local-clock time at which the next [`PeerRelay`] should be
    /// broadcast, or `None` when no peers are configured.
    #[must_use]
    pub fn next_relay_at(&self, now_ns: i64) -> Option<i64> {
        if self.peer_count == 0 {
            return None;
        }
        if self.has_relayed {
            Some(self.next_relay_ns)
        } else {
            Some(now_ns)
        }
    }

    /// Whether a [`PeerRelay`] broadcast is due at `now_ns`.
    #[must_use]
    pub fn should_relay(&self, now_ns: i64) -> bool {
        if self.peer_count == 0 {
            return false;
        }
        if !self.has_relayed {
            return self.sender_has_meas;
        }
        now_ns >= self.next_relay_ns
    }

    /// Builds a [`PeerRelay`] carrying this receiver's fresh incident link
    /// measurements (sender edge plus fresh direct peer edges) for broadcast
    /// to configured peers.
    pub fn build_relay(&mut self, now_ns: i64) -> Option<PeerRelay> {
        if self.peer_count == 0 {
            return None;
        }
        self.note_started(now_ns);
        let mut relay = PeerRelay::EMPTY;
        relay.stream = self.settings.stream;
        relay.sender = self.settings.identity;
        let mut count = 0usize;

        if self.sender_has_meas {
            let age = now_ns.saturating_sub(self.sender_last_meas.midpoint_ns);
            if age >= 0 && age <= self.settings.peer_stale_ns {
                let weighted_var =
                    apply_weight_q16(self.sender_last_meas.variance_ns2, self.sender_weight_q16);
                if let Some(dst) = relay.edges.get_mut(count) {
                    // Sender measurement is `clock(0) - clock(self)`, so
                    // `clock(self) - clock(0) = -offset_ns`.
                    *dst = RelayEdge {
                        from_id: 0,
                        to_id: self.settings.identity,
                        offset_ns: saturate(
                            0i128.wrapping_sub(self.sender_last_meas.offset_ns as i128),
                        ),
                        variance_ns2: weighted_var,
                        age_ns: age_to_u32(age),
                    };
                    count = count.saturating_add(1);
                }
            }
        }

        let mut i = 0usize;
        while i < self.peer_count && count < MAX_RELAY_EDGES {
            if let Some(p) = self.peers.get(i)
                && p.configured
                && p.has_meas
            {
                let age = now_ns.saturating_sub(p.last_meas.midpoint_ns);
                if age >= 0 && age <= self.settings.peer_stale_ns {
                    let weighted_var = apply_weight_q16(p.last_meas.variance_ns2, p.weight_q16);
                    if let Some(dst) = relay.edges.get_mut(count) {
                        *dst = RelayEdge {
                            from_id: self.settings.identity,
                            to_id: p.identity,
                            offset_ns: p.last_meas.offset_ns,
                            variance_ns2: weighted_var,
                            age_ns: age_to_u32(age),
                        };
                        count = count.saturating_add(1);
                    }
                }
            }
            i = i.saturating_add(1);
        }

        if count == 0 {
            return None;
        }
        relay.sequence = self.relay_seq;
        self.relay_seq = self.relay_seq.wrapping_add(1);
        #[allow(clippy::cast_possible_truncation)]
        {
            relay.count = count as u8;
        }
        let interval = if self.settings.relay_interval_ns > 0 {
            self.settings.relay_interval_ns
        } else {
            DEFAULT_RELAY_INTERVAL_NS
        };
        self.has_relayed = true;
        self.next_relay_ns = now_ns.saturating_add(interval);
        Some(relay)
    }

    /// Processes an incoming [`PeerRelay`] from a configured peer that arrived
    /// at `rx_ns`. Returns the number of fresh non-incident edges accepted.
    pub fn on_peer_relay(&mut self, relay: &PeerRelay, rx_ns: i64) -> usize {
        if relay.stream != self.settings.stream {
            return 0;
        }
        let Some(peer_idx) = self.find_peer(relay.sender) else {
            return 0;
        };
        self.note_started(rx_ns);
        let relayer_path_ns = match self.peers.get_mut(peer_idx) {
            Some(p) => {
                p.last_heard_ns = rx_ns;
                if p.has_relay_seq && relay.sequence == p.last_relay_seq {
                    return 0;
                }
                p.has_relay_seq = true;
                p.last_relay_seq = relay.sequence;
                p.rtt_selector.path_ns()
            }
            None => return 0,
        };
        let count = if (relay.count as usize) > MAX_RELAY_EDGES {
            MAX_RELAY_EDGES
        } else {
            relay.count as usize
        };
        let mut accepted = 0usize;
        let mut e = 0usize;
        while e < count {
            if let Some(re) = relay.edges.get(e)
                && re.from_id != re.to_id
                && re.variance_ns2 > 0
                && re.from_id != self.settings.identity
                && re.to_id != self.settings.identity
            {
                // Canonicalize to `from_id < to_id` so undirected pairs map
                // to a single table slot.
                let (c_from, c_to, c_off) = if re.from_id < re.to_id {
                    (re.from_id, re.to_id, re.offset_ns)
                } else {
                    (
                        re.to_id,
                        re.from_id,
                        saturate(0i128.wrapping_sub(re.offset_ns as i128)),
                    )
                };
                // Only accept endpoints we know (`0` or a configured peer).
                let from_known = c_from == 0 || self.find_peer(c_from).is_some();
                let to_known = c_to == 0 || self.find_peer(c_to).is_some();
                if from_known && to_known {
                    let transit = (re.age_ns as i64).saturating_add(relayer_path_ns);
                    if transit <= self.settings.peer_stale_ns {
                        let meas_time_ns = rx_ns.saturating_sub(transit);
                        if self.ingest_relayed_edge(
                            c_from,
                            c_to,
                            meas_time_ns,
                            rx_ns,
                            c_off,
                            re.variance_ns2,
                        ) {
                            accepted = accepted.saturating_add(1);
                        }
                    }
                }
            }
            e = e.saturating_add(1);
        }
        if accepted > 0 {
            self.dirty = true;
        }
        accepted
    }

    /// Reads `self.relayed[idx]` by value, returning [`RelayedSlot::EMPTY`]
    /// when out of bounds.
    fn relayed_at(&self, idx: usize) -> RelayedSlot {
        match self.relayed.get(idx) {
            Some(slot) => *slot,
            None => RelayedSlot::EMPTY,
        }
    }

    /// Returns the slot index holding `(from_id, to_id)`, if present.
    fn find_matching_relayed(&self, from_id: u64, to_id: u64) -> Option<usize> {
        let mut i = 0usize;
        while i < MAX_RELAY_TABLE {
            let slot = self.relayed_at(i);
            if slot.used && slot.from_id == from_id && slot.to_id == to_id {
                return Some(i);
            }
            i = i.saturating_add(1);
        }
        None
    }

    /// Returns the first unused slot index in the relayed-edge table, if any.
    fn find_free_relayed(&self) -> Option<usize> {
        let mut i = 0usize;
        while i < MAX_RELAY_TABLE {
            if !self.relayed_at(i).used {
                return Some(i);
            }
            i = i.saturating_add(1);
        }
        None
    }

    /// Returns the index of the oldest occupied slot in the relayed-edge table.
    fn find_oldest_relayed(&self) -> usize {
        let mut oldest_idx = 0usize;
        let mut oldest_rx = self.relayed_at(0).last_rx_ns;
        let mut i = 1usize;
        while i < MAX_RELAY_TABLE {
            let rx = self.relayed_at(i).last_rx_ns;
            if rx < oldest_rx {
                oldest_rx = rx;
                oldest_idx = i;
            }
            i = i.saturating_add(1);
        }
        oldest_idx
    }

    /// Inserts or updates one canonical non-incident relayed edge slot.
    fn ingest_relayed_edge(
        &mut self,
        from_id: u64,
        to_id: u64,
        meas_time_ns: i64,
        rx_ns: i64,
        offset_ns: i64,
        variance_ns2: u64,
    ) -> bool {
        let matched_opt = self.find_matching_relayed(from_id, to_id);
        let (matched, target) = match matched_opt {
            Some(idx) => (true, idx),
            None => match self.find_free_relayed() {
                Some(free) => (false, free),
                None => (false, self.find_oldest_relayed()),
            },
        };
        let jump_limit = self.settings.jump_ns;
        let Some(slot) = self.relayed.get_mut(target) else {
            return false;
        };
        if matched {
            // Reject older measurements for the same edge.
            if meas_time_ns < slot.meas_time_ns {
                return false;
            }
            let dt = meas_time_ns.saturating_sub(slot.meas_time_ns);
            let diff = (offset_ns as i128).wrapping_sub(slot.offset_ns as i128);
            let abs_diff = if diff < 0 {
                0i128.wrapping_sub(diff)
            } else {
                diff
            };
            if jump_limit > 0 && abs_diff > jump_limit as i128 {
                // Clock step on relayed edge: reset slope cleanly.
                slot.has_freq = false;
                slot.freq_q48 = 0;
            } else if dt >= MIN_RELAY_SLOPE_DT_NS {
                let raw_q48 = clamp_i64(
                    saturate(scale_div_pow2(diff, 48, dt as i128)),
                    MAX_RELAY_FREQ_Q48,
                );
                if slot.has_freq {
                    let blended = (slot.freq_q48 as i128)
                        .wrapping_mul(7)
                        .wrapping_add(raw_q48 as i128);
                    slot.freq_q48 =
                        clamp_i64(saturate(div_floor_wide(blended, 8)), MAX_RELAY_FREQ_Q48);
                } else {
                    slot.freq_q48 = raw_q48;
                    slot.has_freq = true;
                }
            }
            let changed = dt >= MIN_RELAY_SLOPE_DT_NS
                || offset_ns != slot.offset_ns
                || variance_ns2 != slot.variance_ns2;
            if changed {
                slot.meas_time_ns = meas_time_ns;
                slot.offset_ns = offset_ns;
                slot.variance_ns2 = variance_ns2;
            }
            slot.last_rx_ns = rx_ns;
            return changed;
        }
        *slot = RelayedSlot {
            used: true,
            from_id,
            to_id,
            meas_time_ns,
            last_rx_ns: rx_ns,
            offset_ns,
            variance_ns2,
            has_freq: false,
            freq_q48: 0,
        };
        true
    }

    /// Computes the bitmask of configured peers that currently have a fresh
    /// direct link measurement at `now_ns`.
    fn active_peer_mask(&self, now_ns: i64) -> u32 {
        let mut mask = 0u32;
        let mut i = 0usize;
        while i < self.peer_count {
            if let Some(p) = self.peers.get(i)
                && p.configured
                && p.has_meas
                && now_ns.saturating_sub(p.last_meas.midpoint_ns) <= self.settings.peer_stale_ns
            {
                #[allow(clippy::cast_possible_truncation)]
                let bit = 1u32.wrapping_shl(i as u32);
                mask |= bit;
            }
            i = i.saturating_add(1);
        }
        mask
    }

    /// Minimum interval between BLUE modal-filter updates so consecutive BLUE
    /// innovations remain statistically fresh rather than double-counting
    /// unchanged edges.
    fn fusion_interval_ns(&self, now_ns: i64) -> i64 {
        let probe = self.probe_interval_ns(now_ns);
        #[allow(clippy::cast_possible_wrap)]
        let stride = MIN_RTT_STRIDE as i64;
        saturating_mul_i64(probe, stride)
    }

    /// Maps a host identity (`0` = sender, `self_id` = `1`, direct peer `i` =
    /// `i + 2`) to its dense host index in `0..MAX_HOSTS`.
    fn host_index_of(&self, id: u64) -> Option<usize> {
        if id == 0 {
            return Some(0);
        }
        if id == self.settings.identity {
            return Some(1);
        }
        match self.find_peer(id) {
            Some(peer_idx) => {
                let h = peer_idx.saturating_add(2);
                if h < MAX_HOSTS { Some(h) } else { None }
            }
            None => None,
        }
    }

    /// Publishes the direct single-mode Star snapshot from `sender_filter`.
    fn publish_star(&mut self) -> SyncSnapshot {
        if self.peer_active {
            self.peer_active = false;
            self.last_active_mask = 0;
            self.epoch = self.epoch.wrapping_add(1);
        }
        let Some(line) = self.sender_filter.to_line() else {
            self.snapshot = SyncSnapshot::EMPTY;
            return self.snapshot;
        };
        let var_ns2 = apply_weight_q16(self.sender_min_rtt.variance_ns2(), self.sender_weight_q16);
        self.snapshot = SyncSnapshot {
            valid: true,
            peer_active: false,
            epoch: self.epoch,
            fleet_line: ZERO_LINE,
            common_line: line,
            path_ns: self.sender_min_rtt.path_ns(),
            active_peers: 0,
            common_var_ns2: var_ns2,
            diff_var_ns2: 0,
        };
        self.dirty = false;
        self.snapshot
    }

    /// Advances synchronization state to `now_ns` and returns the latest
    /// [`SyncSnapshot`].
    ///
    /// - When zero peers are configured or reachable, exports the sender
    ///   [`KalmanFilter`] line directly (exact Star mode).
    /// - When one or more peers are active, runs [`solve_blue`] on the current
    ///   graph of extrapolated incident and relayed edges, updates the
    ///   common-mode and differential-mode [`KalmanFilter`]s with bumpless
    ///   transfer on peer membership changes, and exports the modal snapshot.
    #[allow(clippy::too_many_lines)]
    pub fn step(&mut self, now_ns: i64) -> SyncSnapshot {
        self.note_started(now_ns);
        let active_mask = self.active_peer_mask(now_ns);
        if active_mask == 0 {
            return self.publish_star();
        }

        let membership_changed = !self.peer_active || active_mask != self.last_active_mask;
        let fusion_due = !self.has_fused
            || now_ns.saturating_sub(self.last_fuse_ns) >= self.fusion_interval_ns(now_ns);
        if !membership_changed && (!self.dirty || !fusion_due) {
            return self.snapshot;
        }

        // Assemble host-graph edges (`0` = sender, `1` = self, `2..` = peers).
        let host_count = self.peer_count.saturating_add(2);
        let host_count = if host_count > MAX_HOSTS {
            MAX_HOSTS
        } else {
            host_count
        };
        let mut edges = [EdgeObs::ZERO; MAX_EDGES];
        let mut edge_count = 0usize;

        let sender_pair_prior = self
            .settings
            .sender_prior
            .combine(self.settings.local_prior);
        let peer_pair_prior = self.settings.local_prior.combine(self.settings.local_prior);

        // 1. Direct sender edge `0 -> 1` (`clock(self) - clock(0) = -sender_offset`).
        if self.sender_has_meas {
            let age = now_ns.saturating_sub(self.sender_last_meas.midpoint_ns);
            let extrap_sender_minus_self = extrapolate_offset(
                self.sender_last_meas.offset_ns,
                self.sender_filter.freq_q48(),
                age,
            );
            let (_, _, p11) = self.sender_filter.covariance_raw();
            let base_var =
                apply_weight_q16(self.sender_last_meas.variance_ns2, self.sender_weight_q16);
            let var_eff = inflate_variance(base_var, age, sender_pair_prior, p11);
            if let Some(dst) = edges.get_mut(edge_count) {
                *dst = EdgeObs {
                    from: 0,
                    to: 1,
                    offset_ns: saturate(0i128.wrapping_sub(extrap_sender_minus_self as i128)),
                    variance_ns2: var_eff,
                };
                edge_count = edge_count.saturating_add(1);
            }
        }

        // 2. Active direct peer edges `1 -> peer_idx + 2`.
        let mut i = 0usize;
        while i < self.peer_count && edge_count < MAX_EDGES {
            #[allow(clippy::cast_possible_truncation)]
            let bit = 1u32.wrapping_shl(i as u32);
            if (active_mask & bit) != 0
                && let Some(p) = self.peers.get(i)
                && p.has_meas
            {
                let age = now_ns.saturating_sub(p.last_meas.midpoint_ns);
                let extrap = extrapolate_offset(p.last_meas.offset_ns, p.filter.freq_q48(), age);
                let (_, _, p11) = p.filter.covariance_raw();
                let base_var = apply_weight_q16(p.last_meas.variance_ns2, p.weight_q16);
                let var_eff = inflate_variance(base_var, age, peer_pair_prior, p11);
                let to_host = i.saturating_add(2);
                if to_host < host_count
                    && let Some(dst) = edges.get_mut(edge_count)
                {
                    *dst = EdgeObs {
                        from: 1,
                        to: to_host,
                        offset_ns: extrap,
                        variance_ns2: var_eff,
                    };
                    edge_count = edge_count.saturating_add(1);
                }
            }
            i = i.saturating_add(1);
        }

        // 3. Fresh relayed non-incident edges.
        let mut r = 0usize;
        while r < MAX_RELAY_TABLE && edge_count < MAX_EDGES {
            if let Some(slot) = self.relayed.get(r)
                && slot.used
            {
                let age = now_ns.saturating_sub(slot.meas_time_ns);
                if age >= 0 && age <= self.settings.peer_stale_ns {
                    let from_h = self.host_index_of(slot.from_id);
                    let to_h = self.host_index_of(slot.to_id);
                    if let (Some(fh), Some(th)) = (from_h, to_h)
                        && fh < host_count
                        && th < host_count
                        && fh != th
                    {
                        let prior = if fh == 0 || th == 0 {
                            sender_pair_prior
                        } else {
                            peer_pair_prior
                        };
                        let extrap = extrapolate_offset(slot.offset_ns, slot.freq_q48, age);
                        let var_eff = inflate_variance(slot.variance_ns2, age, prior, 0);
                        if let Some(dst) = edges.get_mut(edge_count) {
                            *dst = EdgeObs {
                                from: fh,
                                to: th,
                                offset_ns: extrap,
                                variance_ns2: var_eff,
                            };
                            edge_count = edge_count.saturating_add(1);
                        }
                    }
                }
            }
            r = r.saturating_add(1);
        }

        let solved = solve_blue(host_count, 1, &edges, edge_count);
        if solved.active_count <= 1 {
            // Either sender is unreachable or only self is in sender's component:
            // fall back cleanly to Star mode.
            return self.publish_star();
        }

        // Compute exact reachable active-peer bitmask from `solved.reachable`.
        let mut reachable_mask = 0u32;
        let mut p_idx = 0usize;
        while p_idx < self.peer_count {
            let h = p_idx.saturating_add(2);
            if get_bool(&solved.reachable, h) {
                #[allow(clippy::cast_possible_truncation)]
                let bit = 1u32.wrapping_shl(p_idx as u32);
                reachable_mask |= bit;
            }
            p_idx = p_idx.saturating_add(1);
        }

        // Update modal process-noise priors for active receiver count `dim`.
        #[allow(clippy::cast_possible_wrap)]
        let dim = solved.active_count as i64;
        let com_prior = self
            .settings
            .sender_prior
            .combine(self.settings.local_prior.scale(1, dim));
        let diff_prior = self.settings.local_prior.scale(dim.saturating_sub(1), dim);
        self.common_filter.set_prior(com_prior);
        self.diff_filter.set_prior(diff_prior);

        let actual_membership_changed =
            !self.peer_active || reachable_mask != self.last_active_mask;
        if actual_membership_changed {
            self.epoch = self.epoch.wrapping_add(1);
            if self.peer_active
                && self.common_filter.is_anchored()
                && self.diff_filter.is_anchored()
            {
                // Bumpless peer-to-peer membership transfer: shift `diff_filter`
                // by `d_new - d_old` and `common_filter` by `-(d_new - d_old)`
                // so the sum `common + diff` is strictly continuous.
                if let Some(d_old) = self.diff_filter.predict_offset_ns(now_ns) {
                    let shift =
                        saturate((solved.self_diff_offset_ns as i128).wrapping_sub(d_old as i128));
                    let neg_shift = saturate(0i128.wrapping_sub(shift as i128));
                    self.diff_filter.shift_offset_ns(shift);
                    self.common_filter.shift_offset_ns(neg_shift);
                }
            } else {
                // Entering Peer mode from Star or startup: anchor modal filters
                // directly on the BLUE common/differential decomposition.
                // `ModalPlayer` recenters its common anchor on `epoch` change so
                // playback stays continuous without Star bias carryover.
                self.common_filter.reset();
                self.diff_filter.reset();
                self.common_filter.set_prior(com_prior);
                self.diff_filter.set_prior(diff_prior);
            }
            self.peer_active = true;
            self.last_active_mask = reachable_mask;
        }

        self.common_filter
            .update(now_ns, solved.common_offset_ns, solved.common_var_ns2);
        self.diff_filter
            .update(now_ns, solved.self_diff_offset_ns, solved.self_diff_var_ns2);
        self.has_fused = true;
        self.last_fuse_ns = now_ns;
        self.dirty = false;

        let (Some(common_line), Some(fleet_line)) =
            (self.common_filter.to_line(), self.diff_filter.to_line())
        else {
            return self.publish_star();
        };

        #[allow(clippy::cast_possible_truncation)]
        let active_peers = solved.active_count.saturating_sub(1) as u8;
        self.snapshot = SyncSnapshot {
            valid: true,
            peer_active: true,
            epoch: self.epoch,
            fleet_line,
            common_line,
            path_ns: self.sender_min_rtt.path_ns(),
            active_peers,
            common_var_ns2: solved.common_var_ns2,
            diff_var_ns2: solved.self_diff_var_ns2,
        };
        self.snapshot
    }
}

#[cfg(test)]
mod tests {
    use super::{Sync, SyncSettings, WEIGHT_UNITY_Q16};
    use crate::packet::Echo;

    #[test]
    fn zero_peers_degenerates_cleanly_to_star() {
        let mut sync = Sync::new(SyncSettings::standard(1, 101));
        assert_eq!(sync.peer_count(), 0);
        assert_eq!(sync.next_peer_probe(0), None);
        assert_eq!(sync.build_relay(0), None);

        // Simulate 8 clean 4-timestamp sender exchanges with sender +50 ms ahead
        // and +10 ppm relative drift (10_000 ns / s), 200 us symmetric RTT.
        for seq in 0..8u64 {
            let t1 = i64::try_from(seq).unwrap_or(0) * 1_000_000_000;
            let mid = t1 + 100_000;
            let true_off = 50_000_000 + (mid / 100_000);
            sync.report_departed(seq, t1);
            let echo = Echo {
                stream: 1,
                receiver: 101,
                sequence: seq,
                arrival: t1 + 100_000 + true_off,
                departure: t1 + 100_000 + true_off,
            };
            sync.on_sender_echo(&echo, t1 + 200_000);
        }
        let snap = sync.step(7_200_000_000);
        assert!(snap.valid);
        assert!(!snap.peer_active);
        assert_eq!(snap.active_peers, 0);
        assert_eq!(snap.path_ns, 100_000);
        // Check sender_time at t = 8 s (true sender = 8s + 50 ms + 80 us = 8_050_080_000).
        let est = snap.sender_time(8_000_000_000);
        assert!((est - 8_050_080_000).abs() < 2_000, "est={est}");
    }

    #[test]
    fn two_peers_reject_opposite_sender_asymmetry_and_fall_back_on_partition() {
        // Sender = 0 (clock = t).
        // Receiver 1 (id 101): clock = t + 10_000_000_000 (+10 s), sender link asymmetry +750 us.
        // Receiver 2 (id 102): clock = t - 20_000_000_000 (-20 s), sender link asymmetry -750 us.
        // Peer link 1 <-> 2: symmetric 200 us RTT (wired LAN), 0 asymmetry.
        let mut r1 = Sync::new(SyncSettings::standard(1, 101));
        let mut r2 = Sync::new(SyncSettings::standard(1, 102));
        let p12 = r1.add_peer(102, WEIGHT_UNITY_Q16).expect("peer 1->2");
        let p21 = r2.add_peer(101, WEIGHT_UNITY_Q16).expect("peer 2->1");

        let off1 = 10_000_000_000i64;
        let off2 = -20_000_000_000i64;

        for step in 0..16i64 {
            let t_phys = step * 250_000_000; // 4 Hz
            let t1_r1 = t_phys + off1;
            let t1_r2 = t_phys + off2;
            let seq = u64::try_from(step).unwrap_or(0);

            // Sender exchanges with opposite +/- 750 us one-way asymmetry AND
            // 300 us excess jitter on odd exchanges (so sender link var is large).
            let jitter = if step % 2 == 1 { 600_000 } else { 0 };
            let fwd1 = 1_000_000 + 750_000 + jitter;
            let rev1 = 1_000_000 - 750_000 + jitter;
            r1.report_departed(seq, t1_r1);
            r1.on_sender_echo(
                &Echo {
                    stream: 1,
                    receiver: 101,
                    sequence: seq,
                    arrival: t_phys + rev1,
                    departure: t_phys + rev1,
                },
                t1_r1 + fwd1 + rev1,
            );

            let fwd2 = 1_000_000 - 750_000 + jitter;
            let rev2 = 1_000_000 + 750_000 + jitter;
            r2.report_departed(seq, t1_r2);
            r2.on_sender_echo(
                &Echo {
                    stream: 1,
                    receiver: 102,
                    sequence: seq,
                    arrival: t_phys + rev2,
                    departure: t_phys + rev2,
                },
                t1_r2 + fwd2 + rev2,
            );

            // Symmetric low-jitter wired peer probes between r1 and r2.
            if let Some((idx, probe)) = r1.next_peer_probe(t1_r1) {
                assert_eq!(idx, p12);
                r1.peer_probe_departed(idx, probe.sequence, t1_r1);
                let echo = r2
                    .on_peer_probe(&probe, t1_r2 + 100_000, t1_r2 + 100_000)
                    .expect("r2 answers");
                r1.on_peer_echo(&echo, t1_r1 + 200_000);
            }
            if let Some((idx, probe)) = r2.next_peer_probe(t1_r2) {
                assert_eq!(idx, p21);
                r2.peer_probe_departed(idx, probe.sequence, t1_r2);
                let echo = r1
                    .on_peer_probe(&probe, t1_r1 + 100_000, t1_r1 + 100_000)
                    .expect("r1 answers");
                r2.on_peer_echo(&echo, t1_r2 + 200_000);
            }

            // Exchange relays after all exchanges at this step have completed
            // (`t4` is at most `t1 + 3.2 ms`).
            if let Some(rel1) = r1.build_relay(t1_r1 + 5_000_000) {
                r2.on_peer_relay(&rel1, t1_r2 + 5_100_000);
            }
            if let Some(rel2) = r2.build_relay(t1_r2 + 5_000_000) {
                r1.on_peer_relay(&rel2, t1_r1 + 5_100_000);
            }

            r1.step(t1_r1 + 5_200_000);
            r2.step(t1_r2 + 5_200_000);
        }

        let t_eval = 5_000_000_000i64;
        let s1 = r1.snapshot();
        let s2 = r2.snapshot();
        assert!(s1.valid && s1.peer_active && s1.active_peers == 1);
        assert!(s2.valid && s2.peer_active && s2.active_peers == 1);

        // At the same physical instant `t_eval`, both receivers estimate the
        // sender clock within a few microseconds despite +/- 750 us opposite
        // sender asymmetries AND 30-second arbitrary monotonic clock offsets!
        let est1 = s1.sender_time(t_eval + off1);
        let est2 = s2.sender_time(t_eval + off2);
        let spread = (est1 - est2).abs();
        assert!(
            spread < 25_000,
            "peer spread should reject 1.5 ms asymmetry, got {spread} ns (est1={est1}, est2={est2})"
        );

        // Partition: after > 5 s without peer probes, r1 falls back cleanly to Star.
        let s1_fallback = r1.step(t_eval + off1 + 10_000_000_000);
        assert!(s1_fallback.valid);
        assert!(!s1_fallback.peer_active);
        assert_eq!(s1_fallback.active_peers, 0);
    }
}
