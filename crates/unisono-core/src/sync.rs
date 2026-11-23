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
use crate::blue::{BlueResult, EdgeObs, MAX_EDGES, MAX_HOSTS, solve_blue};
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

/// Maximum fractional frequency magnitude tracked on a relayed edge (`200 ppm`
/// in Q48, matching `Receiver`'s clock slope limit).
const MAX_RELAY_FREQ_Q48: i64 = 56_294_995_342;

/// Minimum elapsed time between relayed measurements before updating the
/// per-edge frequency slope (`500 ms`).
const MIN_RELAY_SLOPE_DT_NS: i64 = 500_000_000;

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
    /// Reference timestamp and offset for per-edge slope estimation; only
    /// advances when `meas_time_ns - slope_ref_time_ns >= MIN_RELAY_SLOPE_DT_NS`
    /// so relays arriving faster than 500 ms still accumulate slope baselines.
    slope_ref_time_ns: i64,
    slope_ref_offset_ns: i64,
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
        slope_ref_time_ns: 0,
        slope_ref_offset_ns: 0,
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

/// Combines a link Kalman filter's posterior variance with its sliding
/// minimum-RTT variance, taking the tighter estimate floored at `floor_ns2`.
fn link_variance_ns2(filter_var: u64, rtt_var: u64, floor_ns2: u64) -> u64 {
    let raw = if filter_var < rtt_var {
        filter_var
    } else {
        rtt_var
    };
    if raw > floor_ns2 { raw } else { floor_ns2 }
}

/// Evaluates a direct link's `(offset_ns, variance_ns2, age_ns)` for a
/// [`PeerRelay`] message at the filter's actual observation timestamp
/// (`filter.last_time_ns()`), reporting the true measurement age on the
/// relaying host's clock so receiving peers can accurately extrapolate and
/// grow variance across age and reject stale relays.
fn link_relay_obs(
    filter: &KalmanFilter,
    rtt_var: u64,
    last: Measurement,
    now_ns: i64,
    age_ns: i64,
    floor_ns2: u64,
) -> (i64, u64, u32) {
    let f_off = filter.offset_ns();
    let f_var = filter.offset_variance_ns2();
    let obs_age = now_ns.saturating_sub(filter.last_time_ns());
    match f_off {
        Some(filtered) => (
            filtered,
            link_variance_ns2(f_var, rtt_var, floor_ns2),
            age_to_u32(obs_age),
        ),
        None => (last.offset_ns, last.variance_ns2, age_to_u32(age_ns)),
    }
}

/// Evaluates a direct link's `(offset_ns, variance_ns2)` for BLUE graph
/// assembly in [`Sync::step`], growing its variance across the observation's
/// age using `pair_prior` consistently with relayed edges.
fn link_step_obs(
    filter: &KalmanFilter,
    rtt_var: u64,
    last: Measurement,
    now_ns: i64,
    age_ns: i64,
    floor_ns2: u64,
    pair_prior: NoisePrior,
) -> (i64, u64) {
    let pred = filter.predict_offset_ns(now_ns);
    let f_var = filter.offset_variance_ns2();
    let fq = filter.freq_q48();
    let obs_age = now_ns.saturating_sub(filter.last_time_ns());
    match pred {
        Some(filtered) => {
            let base = link_variance_ns2(f_var, rtt_var, floor_ns2);
            let var_eff = inflate_variance(base, obs_age, pair_prior, 0);
            (filtered, var_eff)
        }
        None => (
            extrapolate_offset(last.offset_ns, fq, age_ns),
            inflate_variance(last.variance_ns2, age_ns, pair_prior, 0),
        ),
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
    sender_clock_id: u32,
    has_sender_clock: bool,

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
    last_direct_mask: u32,
    last_active_mask: u32,
    last_sender_relay_mask: u32,
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
            sender_clock_id: 0,
            has_sender_clock: false,
            peer_count: 0,
            peers: [empty_peer; MAX_DIRECT_PEERS],
            relayed: [RelayedSlot::EMPTY; MAX_RELAY_TABLE],
            relay_seq: 0,
            has_relayed: false,
            next_relay_ns: 0,
            common_filter: KalmanFilter::new(sender_pair_prior, settings.jump_ns),
            diff_filter: KalmanFilter::new(settings.local_prior, settings.jump_ns),
            peer_active: false,
            last_direct_mask: 0,
            last_active_mask: 0,
            last_sender_relay_mask: 0,
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

    /// Sets the active sender clock identifier (`Audio::clock`). If a different
    /// clock identifier was previously active, resets sender-clock state and
    /// purges relayed sender edges while preserving direct peer-to-peer links.
    pub fn set_sender_clock_id(&mut self, clock_id: u32) {
        if self.has_sender_clock && self.sender_clock_id != clock_id {
            self.reset_sender_clock();
        }
        self.has_sender_clock = true;
        self.sender_clock_id = clock_id;
    }

    /// Resets sender-clock state (for example when the sender reboots and
    /// changes its `clock_id`), preserving direct peer-to-peer estimates.
    pub fn reset_sender_clock(&mut self) {
        self.sender_departures = Arrivals::new();
        self.sender_min_rtt.reset();
        self.sender_filter.reset();
        self.sender_has_meas = false;
        self.has_sender_clock = false;
        self.sender_clock_id = 0;
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
        self.last_direct_mask = 0;
        self.last_active_mask = 0;
        self.last_sender_relay_mask = 0;
        self.peer_active = false;
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
        self.sender_filter
            .update(meas.midpoint_ns, meas.offset_ns, meas.variance_ns2);
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
        p.filter
            .update(meas.midpoint_ns, meas.offset_ns, meas.variance_ns2);
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
            return self.sender_has_meas && self.sender_min_rtt.len() >= 4;
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
        relay.sender_clock_id = self.sender_clock_id;
        let mut count = 0usize;

        if self.sender_has_meas && self.sender_min_rtt.len() >= 4 {
            let age = now_ns.saturating_sub(self.sender_last_meas.midpoint_ns);
            if age >= 0 && age <= self.settings.peer_stale_ns {
                let (sender_minus_self, base_var, edge_age) = link_relay_obs(
                    &self.sender_filter,
                    self.sender_min_rtt.variance_ns2(),
                    self.sender_last_meas,
                    now_ns,
                    age,
                    self.settings.variance_floor_ns2,
                );
                let weighted_var = apply_weight_q16(base_var, self.sender_weight_q16);
                if let Some(dst) = relay.edges.get_mut(count) {
                    // Sender measurement is `clock(0) - clock(self)`, so
                    // `clock(self) - clock(0) = -offset_ns`.
                    *dst = RelayEdge {
                        from_id: 0,
                        to_id: self.settings.identity,
                        offset_ns: saturate(0i128.wrapping_sub(sender_minus_self as i128)),
                        variance_ns2: weighted_var,
                        age_ns: edge_age,
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
                    let (peer_offset, base_var, edge_age) = link_relay_obs(
                        &p.filter,
                        p.rtt_selector.variance_ns2(),
                        p.last_meas,
                        now_ns,
                        age,
                        self.settings.variance_floor_ns2,
                    );
                    let weighted_var = apply_weight_q16(base_var, p.weight_q16);
                    if let Some(dst) = relay.edges.get_mut(count) {
                        *dst = RelayEdge {
                            from_id: self.settings.identity,
                            to_id: p.identity,
                            offset_ns: peer_offset,
                            variance_ns2: weighted_var,
                            age_ns: edge_age,
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
                // Only accept endpoints we know (`0` or a configured peer), and
                // fence relayed sender edges (`c_from == 0`) by `sender_clock_id`
                // so stale relays from a previous sender clock are rejected.
                let from_known = c_from == 0 || self.find_peer(c_from).is_some();
                let to_known = c_to == 0 || self.find_peer(c_to).is_some();
                if from_known
                    && to_known
                    && (c_from != 0 || relay.sender_clock_id == self.sender_clock_id)
                {
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
                // Clock step on relayed edge: reset slope and reference anchor cleanly.
                slot.has_freq = false;
                slot.freq_q48 = 0;
                slot.slope_ref_time_ns = meas_time_ns;
                slot.slope_ref_offset_ns = offset_ns;
            } else {
                let ref_dt = meas_time_ns.saturating_sub(slot.slope_ref_time_ns);
                if ref_dt >= MIN_RELAY_SLOPE_DT_NS {
                    let ref_diff =
                        (offset_ns as i128).wrapping_sub(slot.slope_ref_offset_ns as i128);
                    let abs_ref = if ref_diff < 0 {
                        0i128.wrapping_sub(ref_diff)
                    } else {
                        ref_diff
                    };
                    if jump_limit > 0 && abs_ref > jump_limit as i128 {
                        slot.has_freq = false;
                        slot.freq_q48 = 0;
                    } else {
                        let raw_q48 = clamp_i64(
                            saturate(scale_div_pow2(ref_diff, 48, ref_dt as i128)),
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
                    slot.slope_ref_time_ns = meas_time_ns;
                    slot.slope_ref_offset_ns = offset_ns;
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
            slope_ref_time_ns: meas_time_ns,
            slope_ref_offset_ns: offset_ns,
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
            self.last_direct_mask = 0;
            self.last_active_mask = 0;
            self.last_sender_relay_mask = 0;
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

    /// Estimates initial `(common_freq_q48, diff_freq_q48)` when entering Peer
    /// mode from Star, using the direct sender and peer Kalman filters so
    /// drifting clocks do not jump across the Star-to-Peer transition.
    fn initial_peer_frequencies(&self, solved: &BlueResult) -> (i64, i64) {
        let dim = solved.active_count as i128;
        if dim <= 1 {
            return (self.sender_filter.freq_q48(), 0);
        }
        let mut sum_peer_freq = 0i128;
        let mut i = 0usize;
        while i < self.peer_count {
            let h = i.saturating_add(2);
            if get_bool(&solved.reachable, h)
                && let Some(p) = self.peers.get(i)
                && p.has_meas
            {
                sum_peer_freq = sum_peer_freq.saturating_add(p.filter.freq_q48() as i128);
            }
            i = i.saturating_add(1);
        }
        let diff_freq = saturate(div_floor_wide(sum_peer_freq, dim));
        let com_freq = if self.sender_filter.is_anchored() {
            saturate((self.sender_filter.freq_q48() as i128).wrapping_sub(diff_freq as i128))
        } else {
            0
        };
        (com_freq, diff_freq)
    }

    /// Applies a [`BlueResult`] to `common_filter` and `diff_filter`, handling
    /// Star-to-Peer initialization (preserving learned frequencies), peer
    /// membership changes (bumpless transfer), and sender-edge set changes.
    fn update_modal_filters(
        &mut self,
        now_ns: i64,
        solved: &BlueResult,
        direct_mask: u32,
        reachable_mask: u32,
        sender_relay_mask: u32,
    ) {
        #[allow(clippy::cast_possible_wrap)]
        let dim = solved.active_count as i64;
        let com_prior = self
            .settings
            .sender_prior
            .combine(self.settings.local_prior.scale(1, dim));
        let diff_prior = self.settings.local_prior.scale(dim.saturating_sub(1), dim);
        self.common_filter.set_prior(com_prior);
        self.diff_filter.set_prior(diff_prior);

        let sender_relays_changed = sender_relay_mask != self.last_sender_relay_mask;
        let actual_membership_changed =
            !self.peer_active || reachable_mask != self.last_active_mask || sender_relays_changed;
        let mut anchored_common = false;
        let mut anchored_diff = false;
        if actual_membership_changed {
            self.epoch = self.epoch.wrapping_add(1);
            if self.peer_active
                && !sender_relays_changed
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
            } else if self.peer_active && sender_relays_changed && self.diff_filter.is_anchored() {
                // Set of sender edges `(0, self)` / `(0, peer)` changed:
                // re-anchor `common_filter` on the new full-graph BLUE common
                // estimate while preserving its learned frequency, and shift
                // `diff_filter` to the new differential offset.
                let c_freq = if self.common_filter.is_anchored() {
                    self.common_filter.freq_q48()
                } else {
                    0
                };
                self.common_filter.anchor_with_freq(
                    now_ns,
                    solved.common_offset_ns,
                    c_freq,
                    solved.common_var_ns2,
                );
                anchored_common = true;
                if let Some(d_old) = self.diff_filter.predict_offset_ns(now_ns) {
                    let d_shift =
                        saturate((solved.self_diff_offset_ns as i128).wrapping_sub(d_old as i128));
                    self.diff_filter.shift_offset_ns(d_shift);
                }
            } else {
                // Entering Peer mode from Star or startup: anchor modal filters
                // on the BLUE common/differential decomposition while preserving
                // the learned sender and peer clock frequencies.
                let (com_freq, diff_freq) = self.initial_peer_frequencies(solved);
                self.common_filter.anchor_with_freq(
                    now_ns,
                    solved.common_offset_ns,
                    com_freq,
                    solved.common_var_ns2,
                );
                self.diff_filter.anchor_with_freq(
                    now_ns,
                    solved.self_diff_offset_ns,
                    diff_freq,
                    solved.self_diff_var_ns2,
                );
                anchored_common = true;
                anchored_diff = true;
            }
            self.peer_active = true;
            self.last_active_mask = reachable_mask;
            self.last_sender_relay_mask = sender_relay_mask;
        }
        self.last_direct_mask = direct_mask;

        if !anchored_common {
            self.common_filter
                .update(now_ns, solved.common_offset_ns, solved.common_var_ns2);
        }
        if !anchored_diff {
            self.diff_filter
                .update(now_ns, solved.self_diff_offset_ns, solved.self_diff_var_ns2);
        }
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

        let sender_age = now_ns.saturating_sub(self.sender_last_meas.midpoint_ns);
        let sender_fresh =
            self.sender_has_meas && sender_age >= 0 && sender_age <= self.settings.peer_stale_ns;

        // Compute the bitmask of fresh sender edges: `(0, self)` (bit 0, gated
        // on calibrated RTT variance `len >= 4`) and fresh relayed `(0, peer)`
        // edges (bit `p_idx + 1`).
        let mut sender_relay_mask = 0u32;
        if sender_fresh && self.sender_min_rtt.len() >= 4 {
            sender_relay_mask = 1u32;
        }
        let mut has_relayed_sender = false;
        let mut sr = 0usize;
        while sr < MAX_RELAY_TABLE {
            if let Some(slot) = self.relayed.get(sr)
                && slot.used
                && slot.from_id == 0
            {
                let age = now_ns.saturating_sub(slot.meas_time_ns);
                if age >= 0
                    && age <= self.settings.peer_stale_ns
                    && let Some(p_idx) = self.find_peer(slot.to_id)
                {
                    has_relayed_sender = true;
                    #[allow(clippy::cast_possible_truncation)]
                    let relay_bit = 1u32.wrapping_shl(p_idx.saturating_add(1) as u32);
                    sender_relay_mask |= relay_bit;
                }
            }
            sr = sr.saturating_add(1);
        }

        let membership_changed = !self.peer_active
            || active_mask != self.last_direct_mask
            || sender_relay_mask != self.last_sender_relay_mask;
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
        // Included while fresh (`sender_age <= peer_stale_ns`), or as a fallback
        // if no peer currently relays a fresh `(0, peer)` path to the sender;
        // once stale past `peer_stale_ns` with fresh peer paths available, it
        // ages out completely so a dead report path cannot drag peer sync.
        if self.sender_has_meas && (sender_fresh || !has_relayed_sender) {
            let (extrap_sender_minus_self, raw_var) = link_step_obs(
                &self.sender_filter,
                self.sender_min_rtt.variance_ns2(),
                self.sender_last_meas,
                now_ns,
                sender_age,
                self.settings.variance_floor_ns2,
                sender_pair_prior,
            );
            let base_var = apply_weight_q16(raw_var, self.sender_weight_q16);
            if let Some(dst) = edges.get_mut(edge_count) {
                *dst = EdgeObs {
                    from: 0,
                    to: 1,
                    offset_ns: saturate(0i128.wrapping_sub(extrap_sender_minus_self as i128)),
                    variance_ns2: base_var,
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
                let (extrap, raw_var) = link_step_obs(
                    &p.filter,
                    p.rtt_selector.variance_ns2(),
                    p.last_meas,
                    now_ns,
                    age,
                    self.settings.variance_floor_ns2,
                    peer_pair_prior,
                );
                let base_var = apply_weight_q16(raw_var, p.weight_q16);
                let to_host = i.saturating_add(2);
                if to_host < host_count
                    && let Some(dst) = edges.get_mut(edge_count)
                {
                    *dst = EdgeObs {
                        from: 1,
                        to: to_host,
                        offset_ns: extrap,
                        variance_ns2: base_var,
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

        self.update_modal_filters(
            now_ns,
            &solved,
            active_mask,
            reachable_mask,
            sender_relay_mask,
        );
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
    use super::{LINE_RUN, PeerEcho, PeerRelay, RelayEdge, Sync, SyncSettings, WEIGHT_UNITY_Q16};
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

    #[test]
    fn build_relay_reports_true_measurement_age_not_zero() {
        let mut r1 = Sync::new(SyncSettings::standard(1, 101));
        r1.add_peer(102, WEIGHT_UNITY_Q16).expect("peer");
        r1.set_sender_clock_id(77);

        // Feed 4 sender echoes at t = 0..0.75 s (midpoint of last echo ~0.7501 s).
        for step in 0..4i64 {
            let t1 = step * 250_000_000;
            let seq = u64::try_from(step).unwrap_or(0);
            r1.report_departed(seq, t1);
            r1.on_sender_echo(
                &Echo {
                    stream: 1,
                    receiver: 101,
                    sequence: seq,
                    arrival: t1 + 100_000,
                    departure: t1 + 100_000,
                },
                t1 + 200_000,
            );
        }

        // Build relay 2.0 s after the last measurement midpoint: age must reflect
        // the real elapsed time (~2.0 s), not 0!
        let last_mid = r1.sender_filter.last_time_ns();
        let t_send = last_mid + 2_000_000_000;
        let relay = r1.build_relay(t_send).expect("relay");
        assert_eq!(relay.sender_clock_id, 77);
        assert_eq!(relay.count, 1);
        assert_eq!(relay.edges[0].age_ns, 2_000_000_000);
    }

    #[test]
    fn relayed_edge_slope_estimated_at_250ms_cadence_survives_relay_blackout() {
        // Defect 3 + relay-age extrapolation + measurement-time age subtraction:
        // Relays arrive every 250 ms with clocks drifting at +40 ppm. Even though
        // 250 ms < MIN_RELAY_SLOPE_DT_NS (500 ms), the relayed edge must learn
        // the slope and stay accurate across a 4.5 s relay blackout.
        let mut r1 = Sync::new(SyncSettings::standard(1, 101));
        let p12 = r1.add_peer(102, WEIGHT_UNITY_Q16).expect("peer");
        r1.set_sender_clock_id(55);

        // Clock 0 (sender) = t; clock 101 = t; clock 102 = t + 40 ppm * t.
        let skew_ns_per_s = 40_000i64;
        for step in 0..20i64 {
            let t = step * 250_000_000;
            let seq = u64::try_from(step).unwrap_or(0);
            // Direct peer exchange 101 <-> 102.
            let off12 = (t * skew_ns_per_s) / 1_000_000_000;
            r1.peer_probe_departed(p12, seq, t);
            r1.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 101,
                    responder: 102,
                    sequence: seq,
                    arrival: t + off12 + 100_000,
                    departure: t + off12 + 100_000,
                },
                t + 200_000,
            );
            // Relay from 102 carrying edge (0 -> 102) with realistic 150 ms age.
            let edge_age = 150_000_000u32;
            let meas_t = t - i64::from(edge_age);
            let off02_at_meas = (meas_t * skew_ns_per_s) / 1_000_000_000;
            let mut relay = PeerRelay::EMPTY;
            relay.stream = 1;
            relay.sender = 102;
            relay.sequence = seq;
            relay.sender_clock_id = 55;
            relay.count = 1;
            relay.edges[0] = RelayEdge {
                from_id: 0,
                to_id: 102,
                offset_ns: off02_at_meas,
                variance_ns2: 25_000_000,
                age_ns: edge_age,
            };
            let accepted = r1.on_peer_relay(&relay, t + 100_000);
            assert_eq!(accepted, 1);
            r1.step(t + 200_000);
        }

        // Verify the relayed (0, 102) slot learned the +40 ppm slope accurately.
        let slot_idx = r1.find_matching_relayed(0, 102).expect("relayed slot");
        let slot = r1.relayed_at(slot_idx);
        assert!(
            slot.has_freq,
            "relayed edge must estimate slope at 250 ms cadence"
        );
        let learned_ppm = (i128::from(slot.freq_q48) * 1_000_000) / i128::from(LINE_RUN);
        assert!(
            (learned_ppm - 40).abs() <= 2,
            "learned slope should be ~40 ppm, got {learned_ppm} ppm"
        );

        // Keep direct peer link fresh for 4.5 s while relays from 102 are blacked out
        // (and r1 has no direct sender link, so r1 relies solely on extrapolated (0, 102)!).
        let t_blackout_end = 19 * 250_000_000 + 4_200_000_000;
        let off12_end = (t_blackout_end * skew_ns_per_s) / 1_000_000_000;
        for k in 0..4u64 {
            let t = t_blackout_end - i64::try_from(3 - k).unwrap_or(0) * 250_000_000;
            let off12 = (t * skew_ns_per_s) / 1_000_000_000;
            let seq = 100 + k;
            r1.peer_probe_departed(p12, seq, t);
            r1.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 101,
                    responder: 102,
                    sequence: seq,
                    arrival: t + off12 + 100_000,
                    departure: t + off12 + 100_000,
                },
                t + 200_000,
            );
        }
        let _ = off12_end;
        let snap = r1.step(t_blackout_end + 300_000);
        assert!(snap.valid && snap.peer_active);
        let est_sender = snap.sender_time(t_blackout_end + 300_000);
        let err_ns = (est_sender - (t_blackout_end + 300_000)).abs();
        assert!(
            err_ns < 5_000,
            "extrapolated relay during blackout erred by {err_ns} ns (would be ~170 us without slope)"
        );
    }

    #[test]
    fn stale_direct_sender_edge_ages_out_in_peer_mode() {
        // Defect 4: when r1's direct report path to the sender stops answering
        // and the sender frequency shifts by +1 ppm, r1 must age out the stale
        // direct sender edge and follow peer r2's fresh path without drifting.
        let mut r1 = Sync::new(SyncSettings::standard(1, 101));
        let mut r2 = Sync::new(SyncSettings::standard(1, 102));
        let p12 = r1.add_peer(102, WEIGHT_UNITY_Q16).expect("p12");
        let p21 = r2.add_peer(101, WEIGHT_UNITY_Q16).expect("p21");
        r1.set_sender_clock_id(10);
        r2.set_sender_clock_id(10);

        // Sender clock = t for t <= 10 s; then +5 ppm shift for t > 10 s.
        let sender_clock = |t: i64| -> i64 {
            if t <= 10_000_000_000 {
                t
            } else {
                t + ((t - 10_000_000_000) * 5) / 1_000_000
            }
        };

        for step in 0..120i64 {
            let t = step * 250_000_000; // 0..30 s
            let seq = u64::try_from(step).unwrap_or(0);
            let s_t = sender_clock(t + 100_000);

            // Direct sender echo for r1 ONLY for t < 10 s; then r1's report path fails!
            if t < 10_000_000_000 {
                r1.report_departed(seq, t);
                r1.on_sender_echo(
                    &Echo {
                        stream: 1,
                        receiver: 101,
                        sequence: seq,
                        arrival: s_t,
                        departure: s_t,
                    },
                    t + 200_000,
                );
            }
            // r2 keeps receiving fresh sender echoes throughout.
            r2.report_departed(seq, t);
            r2.on_sender_echo(
                &Echo {
                    stream: 1,
                    receiver: 102,
                    sequence: seq,
                    arrival: s_t,
                    departure: s_t,
                },
                t + 200_000,
            );

            // Direct peer exchanges between r1 and r2.
            r1.peer_probe_departed(p12, seq, t);
            r1.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 101,
                    responder: 102,
                    sequence: seq,
                    arrival: t + 100_000,
                    departure: t + 100_000,
                },
                t + 200_000,
            );
            r2.peer_probe_departed(p21, seq, t);
            r2.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 102,
                    responder: 101,
                    sequence: seq,
                    arrival: t + 100_000,
                    departure: t + 100_000,
                },
                t + 200_000,
            );

            if let Some(rel2) = r2.build_relay(t + 500_000) {
                r1.on_peer_relay(&rel2, t + 600_000);
            }
            r1.step(t + 700_000);
            r2.step(t + 700_000);
        }

        // At t = 29.75 s (nearly 20 s after r1's report path died and +5 ppm shift = 100 us drift):
        let t_check = 119 * 250_000_000 + 700_000;
        let true_s = sender_clock(t_check);
        let est_r1 = r1.snapshot().sender_time(t_check);
        let err_ns = (est_r1 - true_s).abs();
        assert!(
            err_ns < 5_000,
            "stale direct sender edge dragged r1 off by {err_ns} ns (true={true_s}, est={est_r1})"
        );
    }

    #[test]
    fn entering_peer_mode_preserves_learned_frequency_without_jump() {
        // Defect 5: two receivers running in Star mode at ±40 ppm learn their
        // clock frequencies, then enable peer exchanges. The Star->Peer
        // transition must preserve frequency and NOT jump ~69 us apart.
        let mut r1 = Sync::new(SyncSettings::standard(1, 101));
        let mut r2 = Sync::new(SyncSettings::standard(1, 102));
        let p12 = r1.add_peer(102, WEIGHT_UNITY_Q16).expect("p12");
        let p21 = r2.add_peer(101, WEIGHT_UNITY_Q16).expect("p21");
        r1.set_sender_clock_id(1);
        r2.set_sender_clock_id(1);
        let clk1 = |t: i64| t + (t * 40) / 1_000_000;
        let clk2 = |t: i64| t - (t * 40) / 1_000_000;
        let feed_sender = |s: &mut Sync, id: u64, seq: u64, t: i64, clk: &dyn Fn(i64) -> i64| {
            s.report_departed(seq, clk(t));
            s.on_sender_echo(
                &Echo {
                    stream: 1,
                    receiver: id,
                    sequence: seq,
                    arrival: t + 100_000,
                    departure: t + 100_000,
                },
                clk(t + 200_000),
            );
        };

        // Phase 1 (0..10 s): Star only (no peer traffic), both learn ±40 ppm.
        for step in 0..40i64 {
            let t = step * 250_000_000;
            let seq = u64::try_from(step).unwrap_or(0);
            feed_sender(&mut r1, 101, seq, t, &clk1);
            feed_sender(&mut r2, 102, seq, t, &clk2);
            r1.step(clk1(t + 300_000));
            r2.step(clk2(t + 300_000));
        }
        assert!(!r1.snapshot().peer_active && !r2.snapshot().peer_active);

        // Phase 2 (10..15 s): Peer probes and relays turn on; measure spread on
        // the immediate Star->Peer entry step, peak across transition, and once
        // the new peer link calibrates.
        let mut entry_spread_ns = 0i64;
        let mut max_spread_ns = 0i64;
        let mut settled_spread_ns = 0i64;
        for step in 40..60i64 {
            let t = step * 250_000_000;
            let seq = u64::try_from(step).unwrap_or(0);
            feed_sender(&mut r1, 101, seq, t, &clk1);
            feed_sender(&mut r2, 102, seq, t, &clk2);
            r1.peer_probe_departed(p12, seq, clk1(t));
            r1.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 101,
                    responder: 102,
                    sequence: seq,
                    arrival: clk2(t + 100_000),
                    departure: clk2(t + 100_000),
                },
                clk1(t + 200_000),
            );
            r2.peer_probe_departed(p21, seq, clk2(t));
            r2.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 102,
                    responder: 101,
                    sequence: seq,
                    arrival: clk1(t + 100_000),
                    departure: clk1(t + 100_000),
                },
                clk2(t + 200_000),
            );
            if let Some(rel1) = r1.build_relay(clk1(t + 500_000)) {
                r2.on_peer_relay(&rel1, clk2(t + 600_000));
            }
            if let Some(rel2) = r2.build_relay(clk2(t + 500_000)) {
                r1.on_peer_relay(&rel2, clk1(t + 600_000));
            }
            r1.step(clk1(t + 700_000));
            r2.step(clk2(t + 700_000));
            let t_mid = t + 200_000_000;
            let s1 = r1.snapshot().sender_time(clk1(t_mid));
            let s2 = r2.snapshot().sender_time(clk2(t_mid));
            let spread = (s1 - s2).abs();
            if step == 40 {
                entry_spread_ns = spread;
            }
            max_spread_ns = max_spread_ns.max(spread);
            if step >= 52 {
                settled_spread_ns = settled_spread_ns.max(spread);
            }
        }
        assert!(r1.snapshot().peer_active && r2.snapshot().peer_active);
        assert!(
            entry_spread_ns < 2_000 && max_spread_ns < 15_000 && settled_spread_ns < 2_000,
            "Star->Peer transition spread too large: entry={entry_spread_ns} ns, max={max_spread_ns} ns, settled={settled_spread_ns} ns (zeroed frequency jumps ~69 us)"
        );
    }

    #[test]
    fn on_peer_relay_subtracts_relay_age_from_measurement_time() {
        // Mutation 4: ignoring `re.age_ns` when computing `meas_time_ns` causes
        // a 1.5 s-old relayed edge on a +40 ppm drifting clock to miss 60 us of
        // drift extrapolation at fusion time.
        let mut r1 = Sync::new(SyncSettings::standard(1, 101));
        let p12 = r1.add_peer(102, WEIGHT_UNITY_Q16).expect("p12");
        r1.set_sender_clock_id(1);
        let clk2 = |t: i64| t + (t * 40) / 1_000_000; // +40 ppm

        for step in 0..8i64 {
            let t = step * 250_000_000;
            let seq = u64::try_from(step).unwrap_or(0);
            r1.peer_probe_departed(p12, seq, t);
            r1.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 101,
                    responder: 102,
                    sequence: seq,
                    arrival: clk2(t + 100_000),
                    departure: clk2(t + 100_000),
                },
                t + 200_000,
            );
        }

        // Feed fresh relays to establish the -40 ppm slope of edge (0 -> 102):
        // offset(0 -> 102) = clk2(t) - t = +40 ppm * t.
        for step in 0..8i64 {
            let t = step * 500_000_000;
            let mut rel = PeerRelay::EMPTY;
            rel.stream = 1;
            rel.sender = 102;
            rel.sequence = u64::try_from(step + 1).unwrap_or(1);
            rel.sender_clock_id = 1;
            rel.count = 1;
            rel.edges[0] = RelayEdge {
                from_id: 0,
                to_id: 102,
                offset_ns: clk2(t) - t,
                variance_ns2: 25_000_000,
                age_ns: 0,
            };
            r1.on_peer_relay(&rel, t + 100_000);
        }

        // Now deliver an observation captured at t = 4.0 s when r1 receives it
        // at rx_ns = 5.5 s (age_ns = 1.5 s). Ignoring age_ns would treat the
        // 4.0 s offset as valid at 5.5 s and be off by 40 ppm * 1.5 s = 60 us!
        let mut aged = PeerRelay::EMPTY;
        aged.stream = 1;
        aged.sender = 102;
        aged.sequence = 99;
        aged.sender_clock_id = 1;
        aged.count = 1;
        aged.edges[0] = RelayEdge {
            from_id: 0,
            to_id: 102,
            offset_ns: clk2(4_000_000_000) - 4_000_000_000,
            variance_ns2: 25_000_000,
            age_ns: 1_500_000_000,
        };
        assert_eq!(r1.on_peer_relay(&aged, 5_500_100_000), 1);
        let snap = r1.step(5_500_200_000);
        assert!(snap.valid && snap.peer_active);
        let err_ns = (snap.sender_time(5_500_200_000) - 5_500_200_000).abs();
        assert!(
            err_ns < 10_000,
            "aged relay failed age subtraction / extrapolation: err={err_ns} ns (ignoring age errs ~60 us)"
        );
    }

    #[test]
    fn peer_relay_rejects_stale_sender_clock_id_and_sender_reboot_resets_sync() {
        // Defect 6: after switching to a new sender host (clock_id 200) within
        // 5 s of a peer's last echo on old clock_id 100, a stale PeerRelay
        // carrying sender_clock_id = 100 must NOT re-inject old-clock sender edges.
        let mut r1 = Sync::new(SyncSettings::standard(1, 101));
        let p12 = r1.add_peer(102, WEIGHT_UNITY_Q16).expect("peer");
        r1.set_sender_clock_id(100);

        // Establish peer link 101 <-> 102 and old sender clock 100 (offset +50 s).
        for step in 0..4i64 {
            let t = step * 250_000_000;
            let seq = u64::try_from(step).unwrap_or(0);
            r1.report_departed(seq, t);
            r1.on_sender_echo(
                &Echo {
                    stream: 1,
                    receiver: 101,
                    sequence: seq,
                    arrival: t + 50_000_000_000 + 100_000,
                    departure: t + 50_000_000_000 + 100_000,
                },
                t + 200_000,
            );
            r1.peer_probe_departed(p12, seq, t);
            r1.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 101,
                    responder: 102,
                    sequence: seq,
                    arrival: t + 100_000,
                    departure: t + 100_000,
                },
                t + 200_000,
            );
        }
        r1.step(1_000_000_000);
        assert!(r1.snapshot().valid);

        // Sender switches to new host with clock_id = 200 (offset = 0).
        r1.set_sender_clock_id(200);
        assert!(!r1.snapshot().valid, "clock_id change must reset snapshot");

        // Stale relay from peer 102 still tagged with old sender_clock_id = 100:
        let mut stale = PeerRelay::EMPTY;
        stale.stream = 1;
        stale.sender = 102;
        stale.sequence = 1;
        stale.sender_clock_id = 100;
        stale.count = 1;
        stale.edges[0] = RelayEdge {
            from_id: 0,
            to_id: 102,
            offset_ns: -50_000_000_000,
            variance_ns2: 25_000_000,
            age_ns: 10_000_000,
        };
        assert_eq!(
            r1.on_peer_relay(&stale, 1_500_000_000),
            0,
            "stale sender-clock relay edge must be rejected"
        );
        // Step must remain invalid (not misled by the stale +50 s relay!).
        let snap = r1.step(1_600_000_000);
        assert!(!snap.valid);

        // Relay tagged with new sender_clock_id = 200 IS accepted cleanly.
        let mut fresh = stale;
        fresh.sequence = 2;
        fresh.sender_clock_id = 200;
        fresh.edges[0].offset_ns = 0;
        assert_eq!(r1.on_peer_relay(&fresh, 1_700_000_000), 1);
    }

    #[test]
    fn relay_only_peer_does_not_bypass_fusion_interval() {
        // Minor defect: when peer 103 is reachable only through relays from
        // peer 102, steady steps must NOT treat `membership_changed` as true
        // on every call and bypass the fusion interval.
        let mut r1 = Sync::new(SyncSettings::standard(1, 101));
        let p12 = r1.add_peer(102, WEIGHT_UNITY_Q16).expect("p12");
        r1.add_peer(103, WEIGHT_UNITY_Q16).expect("p13");
        r1.set_sender_clock_id(9);

        for step in 0..4i64 {
            let t = step * 250_000_000;
            let seq = u64::try_from(step).unwrap_or(0);
            r1.report_departed(seq, t);
            r1.on_sender_echo(
                &Echo {
                    stream: 1,
                    receiver: 101,
                    sequence: seq,
                    arrival: t + 100_000,
                    departure: t + 100_000,
                },
                t + 200_000,
            );
            r1.peer_probe_departed(p12, seq, t);
            r1.on_peer_echo(
                &PeerEcho {
                    stream: 1,
                    prober: 101,
                    responder: 102,
                    sequence: seq,
                    arrival: t + 100_000,
                    departure: t + 100_000,
                },
                t + 200_000,
            );
        }
        // Peer 102 relays edge (102 -> 103); peer 103 has no direct probes from r1.
        let mut rel = PeerRelay::EMPTY;
        rel.stream = 1;
        rel.sender = 102;
        rel.sequence = 1;
        rel.sender_clock_id = 9;
        rel.count = 1;
        rel.edges[0] = RelayEdge {
            from_id: 102,
            to_id: 103,
            offset_ns: 0,
            variance_ns2: 25_000_000,
            age_ns: 1_000_000,
        };
        assert_eq!(r1.on_peer_relay(&rel, 1_000_000_000), 1);

        let s1 = r1.step(1_010_000_000);
        assert!(s1.peer_active && s1.active_peers == 2);
        let fuse_t1 = r1.last_fuse_ns;

        // Stepping 10 ms later (well below fusion_interval_ns) with no new inputs
        // must NOT re-run BLUE or advance `last_fuse_ns` or bump `epoch`.
        let s2 = r1.step(1_020_000_000);
        assert_eq!(s2.epoch, s1.epoch);
        assert_eq!(r1.last_fuse_ns, fuse_t1);
    }
}
