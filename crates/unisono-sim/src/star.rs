// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Simulation of star and peer (receiver-receiver) synchronization controllers.
//!
//! This module numerically evaluates the architectures proved in
//! `Unisono.Solutions.Optimal` under realistic clocks, asymmetric links, packet
//! loss, and link pauses:
//!
//! * **Clocks (`FrequencyNoise`, `PhaseCourse`).** Parameterized by IEEE 1139
//!   one-sided power-law coefficients (`white` for white frequency noise and
//!   `walk` for random-walk frequency noise), with exact continuous-time
//!   Cholesky sampling of the `[phase, frequency]` increment covariance using
//!   `white / 2` and `2 * pi^2 * walk` (matching `Unisono.Spec.ClockNoise`).
//! * **Star estimation and control (`OffsetFilter`, `SlidingMinRtt`,
//!   `compare_star`).** Compares the fixed-delay baseline (at both 1000 ppm and
//!   100 ppm slew) against a non-blocking sliding-window min-RTT front end, an
//!   exact zero-lag timestamped Kalman filter with Joseph-form covariance
//!   updates (with both oracle and online-estimated measurement variance), and
//!   the clamped `Regulation.law` pace controller, tracking all six
//!   specification objectives including missed samples and discontinuities.
//! * **Sender-disciplined timestamped schedule
//!   (`disciplined_schedule_comparison`).** Simulates heterogeneous receivers
//!   with nonzero random initial offsets and frequencies, delayed schedule
//!   delivery, shared sender-NIC jitter, and exact inverse-variance residual
//!   variance `sigma_r^2 - V_bc`.
//! * **Peer / receiver-receiver topologies (`solve_graph_blue`,
//!   `peer_topology_comparison`).** Solves the exact Graph-Laplacian BLUE
//!   (Thomson's principle) across arbitrary communication graphs and compares
//!   independent star operation against peer-mesh estimation combined with
//!   two-gain modal lip-sync control and pure-consensus low-latency control,
//!   including asymmetric Wi-Fi sender + wired peer topologies.
//! * **Playout level with discontinuities (`hold_margin_with_clicks`,
//!   `stream_pause_metrics`).** Evaluates both missed-sample fraction and
//!   discontinuity (click) rate under exponential link pauses.

use std::collections::VecDeque;
use std::f64::consts::PI;

use crate::TrueTime;
use crate::link::{Link, LinkModel};
use crate::random::Generator;

/// IEEE 1139 power-law frequency noise of an oscillator.
///
/// The one-sided fractional-frequency spectral density is
/// `white + walk / f^2`, matching `Unisono.Spec.ClockNoise`.
#[derive(Clone, Copy, Debug)]
pub struct FrequencyNoise {
    /// White frequency noise PSD coefficient (seconds, i.e. 1/Hz).
    /// Phase diffusion variance rate is `white / 2`.
    pub white: f64,
    /// Random-walk frequency noise PSD coefficient (Hz).
    /// Fractional-frequency diffusion variance rate is `2 * pi^2 * walk`.
    pub walk: f64,
}

impl FrequencyNoise {
    /// Laboratory OCXO-grade oscillator (Allan deviation around `1e-9` at 1 s).
    pub const OCXO: FrequencyNoise = FrequencyNoise {
        white: 2e-18,
        walk: 5e-20,
    };

    /// Typical consumer quartz crystal oscillator (Allan deviation around
    /// `1e-7` at 1 s, thermal drift around 0.6 ppm over 100 s).
    pub const CONSUMER_QUARTZ: FrequencyNoise = FrequencyNoise {
        white: 2e-14,
        walk: 5e-16,
    };

    /// Thermally drifting consumer oscillator (100x larger frequency random
    /// walk PSD than `CONSUMER_QUARTZ`, representative of a warming laptop or
    /// phone).
    pub const WANDERING_QUARTZ: FrequencyNoise = FrequencyNoise {
        white: 2e-14,
        walk: 5e-14,
    };

    /// Phase white-frequency variance rate `white / 2` (in s^2 / s).
    #[must_use]
    pub fn white_variance_rate(self) -> f64 {
        self.white / 2.0
    }

    /// Fractional-frequency random-walk variance rate `2 * pi^2 * walk` (1/s).
    #[must_use]
    pub fn walk_variance_rate(self) -> f64 {
        2.0 * PI * PI * self.walk
    }

    /// Sum of two independent clocks' noise parameters.
    #[must_use]
    pub fn combine(self, other: FrequencyNoise) -> FrequencyNoise {
        FrequencyNoise {
            white: self.white + other.white,
            walk: self.walk + other.walk,
        }
    }
}

/// Number of whole steps of `step` seconds covering `duration`, rounded up.
fn step_count(duration: f64, step: f64) -> usize {
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let count = (duration / step).ceil().max(0.0) as usize;
    count
}

/// Convert a count to `f64` for averages.
fn as_float(count: usize) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let value = count as f64;
    value
}

/// Advance a `(phase, frequency)` state by `dt >= 0` using exact continuous-time
/// Cholesky sampling of the integrated Brownian-motion covariance `Q(dt)`.
pub fn advance_clock(
    state: &mut (f64, f64),
    noise: FrequencyNoise,
    dt: f64,
    generator: &mut Generator,
) {
    if dt <= 0.0 {
        return;
    }
    let q0 = noise.white_variance_rate();
    let q2 = noise.walk_variance_rate();
    let z1 = generator.normal();
    let z2 = generator.normal();
    let df = (q2 * dt).sqrt() * z2;
    let cond_phase_var = q0 * dt + q2 * dt * dt * dt / 12.0;
    let dphi = state.1 * dt + 0.5 * dt * df + cond_phase_var.sqrt() * z1;
    state.0 += dphi;
    state.1 += df;
}

/// Simulated oscillator phase trajectory `C(t) - t` sampled on a uniform grid
/// of step `step` seconds.
#[derive(Clone, Debug)]
pub struct PhaseCourse {
    step: f64,
    phases: Vec<f64>,
}

impl PhaseCourse {
    /// Draw a continuous-time phase trajectory starting at `(offset, frequency)`
    /// over `duration` seconds using exact Cholesky increments.
    #[must_use]
    pub fn draw(
        offset: f64,
        frequency: f64,
        noise: FrequencyNoise,
        step: f64,
        duration: f64,
        generator: &mut Generator,
    ) -> PhaseCourse {
        let count = step_count(duration, step) + 2;
        let mut phases = Vec::with_capacity(count);
        let mut state = (offset, frequency);
        for _ in 0..count {
            phases.push(state.0);
            advance_clock(&mut state, noise, step, generator);
        }
        PhaseCourse { step, phases }
    }

    /// Interpolated phase error at true time `t` seconds.
    #[must_use]
    pub fn at(&self, t: f64) -> f64 {
        let position = (t / self.step).max(0.0);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let index = (position.floor() as usize).min(self.phases.len() - 2);
        let fraction = position - as_float(index);
        self.phases[index] + fraction * (self.phases[index + 1] - self.phases[index])
    }

    /// Clock reading `t + at(t)` at true time `t`.
    #[must_use]
    pub fn reading(&self, t: f64) -> f64 {
        t + self.at(t)
    }
}

/// One completed two-way clock probe exchange between `querier` and
/// `responder`, as observed by `querier`.
#[derive(Clone, Copy, Debug)]
pub struct Exchange {
    /// NTP offset estimate `t2 - (t1 + t4) / 2` of `responder - querier`.
    pub offset: f64,
    /// Measured round-trip time `t4 - t1` on `querier`'s clock.
    pub round_trip: f64,
    /// Midpoint timestamp `(t1 + t4) / 2` on `querier`'s clock.
    pub middle: f64,
    /// True time at which the reply arrived at `querier`.
    pub arrival: f64,
}

/// Configuration for generating two-way clock probe exchanges over potentially
/// asymmetric, lossy links with endpoint timestamp noise.
#[derive(Clone, Copy, Debug)]
pub struct ExchangeConfig {
    /// Forward link (`querier -> responder`).
    pub forward: LinkModel,
    /// Return link (`responder -> querier`).
    pub backward: LinkModel,
    /// Independent per-direction packet drop probability in `[0, 1)`.
    pub drop_rate: f64,
    /// Standard deviation of per-endpoint timestamp jitter, in seconds.
    pub timestamp_std: f64,
    /// Interval between outgoing probe attempts, in seconds.
    pub period: f64,
    /// True start time of the first probe attempt, in seconds.
    pub start: f64,
    /// Simulation horizon, in seconds.
    pub duration: f64,
}

/// Generate completed probe exchanges between `querier` and `responder` under
/// asymmetric links, packet loss, and endpoint timestamp noise.
#[must_use]
pub fn exchanges(
    responder: &PhaseCourse,
    querier: &PhaseCourse,
    config: ExchangeConfig,
    seed: u64,
) -> Vec<Exchange> {
    let base = Generator::new(seed);
    let mut forward = Link::new(config.forward, base.fork(1));
    let mut backward = Link::new(config.backward, base.fork(2));
    let mut draws = base.fork(3);
    let mut result = Vec::new();
    let mut sent = config.start;
    while sent < config.duration {
        let arrived = forward.arrival(TrueTime::from_seconds(sent)).seconds();
        let answered = backward.arrival(TrueTime::from_seconds(arrived)).seconds();
        let dropped = draws.chance(config.drop_rate) || draws.chance(config.drop_rate);
        if !dropped && answered < config.duration + 1.0 {
            let j1 = config.timestamp_std * draws.normal();
            let j2 = config.timestamp_std * draws.normal();
            let j4 = config.timestamp_std * draws.normal();
            let t1 = querier.reading(sent) + j1;
            let t2 = responder.reading(arrived) + j2;
            let t4 = querier.reading(answered) + j4;
            let rtt = (t4 - t1).max(1e-9);
            result.push(Exchange {
                offset: t2 - f64::midpoint(t1, t4),
                round_trip: rtt,
                middle: f64::midpoint(t1, t4),
                arrival: answered,
            });
        }
        sent += config.period;
    }
    result
}

/// Exact zero-lag timestamped two-state Kalman filter for relative clock
/// `(offset, frequency)` using Joseph-form covariance updates.
///
/// The filter stores its posterior state `(offset, frequency, covariance)` at
/// the timestamp `last_time` of the last incorporated measurement. Reading the
/// current estimate at playback time `now >= last_time` calls
/// [`OffsetFilter::predict_at`] without mutating filter state, eliminating
/// lag-approximation covariance drift.
#[derive(Clone, Debug)]
pub struct OffsetFilter {
    /// Posterior offset estimate at `last_time`, in seconds.
    pub offset: f64,
    /// Posterior relative fractional-frequency estimate at `last_time`.
    pub frequency: f64,
    /// Timestamp (on the local clock) of the stored posterior state.
    pub last_time: f64,
    covariance: [[f64; 2]; 2],
    noise: FrequencyNoise,
}

impl OffsetFilter {
    /// Create a filter initialized at `(offset, 0)` at timestamp `time`.
    #[must_use]
    pub fn new_at(
        offset: f64,
        time: f64,
        offset_variance: f64,
        frequency_variance: f64,
        noise: FrequencyNoise,
    ) -> OffsetFilter {
        OffsetFilter {
            offset,
            frequency: 0.0,
            last_time: time,
            covariance: [[offset_variance, 0.0], [0.0, frequency_variance]],
            noise,
        }
    }

    /// Create a filter initialized at `time = 0.0`.
    #[must_use]
    pub fn new(
        offset: f64,
        offset_variance: f64,
        frequency_variance: f64,
        noise: FrequencyNoise,
    ) -> OffsetFilter {
        OffsetFilter::new_at(offset, 0.0, offset_variance, frequency_variance, noise)
    }

    /// Advance the stored state and covariance forward by `dt >= 0` using the
    /// exact continuous-time integrated Brownian-motion covariance `Q(dt)`.
    pub fn predict(&mut self, dt: f64) {
        if dt <= 0.0 {
            return;
        }
        self.offset += self.frequency * dt;
        self.last_time += dt;
        let [[p00, p01], [_, p11]] = self.covariance;
        let q0 = self.noise.white_variance_rate();
        let q2 = self.noise.walk_variance_rate();
        let next_p00 = p00 + 2.0 * p01 * dt + p11 * dt * dt + q0 * dt + q2 * dt * dt * dt / 3.0;
        let next_p01 = p01 + p11 * dt + q2 * dt * dt / 2.0;
        let next_p11 = p11 + q2 * dt;
        self.covariance = [[next_p00, next_p01], [next_p01, next_p11]];
    }

    /// Read-only conditional-mean prediction `(offset, frequency)` at `time`
    /// without mutating the stored posterior at `last_time`.
    #[must_use]
    pub fn predict_at(&self, time: f64) -> (f64, f64) {
        let dt = (time - self.last_time).max(0.0);
        (self.offset + self.frequency * dt, self.frequency)
    }

    /// Zero-lag scalar measurement update (`H = [1, 0]`) at `last_time` using
    /// the numerically stable Joseph covariance form.
    pub fn update_zero_lag(&mut self, measured: f64, variance: f64) {
        let meas_var = variance.max(1e-18);
        let [[p00, p01], [_, p11]] = self.covariance;
        let innov_var = (p00 + meas_var).max(1e-18);
        let k0 = p00 / innov_var;
        let k1 = p01 / innov_var;
        let innovation = measured - self.offset;
        self.offset += k0 * innovation;
        self.frequency += k1 * innovation;
        // Joseph form: P+ = (I - K H) P (I - K H)^T + K R K^T with H = [1, 0].
        let one_m_k0 = 1.0 - k0;
        let next_p00 = one_m_k0 * one_m_k0 * p00 + k0 * k0 * meas_var;
        let next_p01 = one_m_k0 * (p01 - k1 * p00) + k0 * k1 * meas_var;
        let next_p11 = (k1 * k1 * p00 - 2.0 * k1 * p01 + p11) + k1 * k1 * meas_var;
        self.covariance = [[next_p00.max(0.0), next_p01], [next_p01, next_p11.max(0.0)]];
    }

    /// Incorporate a measurement stamped at `meas_time >= last_time` by
    /// predicting exactly to `meas_time` and performing a zero-lag Joseph update.
    /// Returns `false` if the measurement is older than `last_time`.
    pub fn update_at(&mut self, measured: f64, meas_time: f64, variance: f64) -> bool {
        if meas_time < self.last_time {
            return false;
        }
        self.predict(meas_time - self.last_time);
        self.update_zero_lag(measured, variance);
        true
    }

    /// Current posterior offset variance, in s^2.
    #[must_use]
    pub fn offset_variance(&self) -> f64 {
        self.covariance[0][0]
    }
}

/// Control law of `Unisono.Model.Regulation.law` with gain `g` in `(0, 1)`.
#[must_use]
pub fn law(g: f64, distance: f64, pace: f64) -> f64 {
    g * g / (2.0 - g) * distance - g * pace
}

/// Effective position weight of a decentralized star receiver with `receivers`
/// speakers and specification weights `(c_sync, c_track)`:
/// `((R - 1) / R) * c_sync + c_track`, matching `decentralized_star_cost_eq`.
#[must_use]
pub fn decentralized_star_weight(receivers: usize, c_sync: f64, c_track: f64) -> f64 {
    let count = as_float(receivers.max(1));
    ((count - 1.0) / count) * c_sync + c_track
}

/// Optimal `Regulation.law` gain `g` in `(0, 1)` for quadratic position weight
/// `c > 0` (inverting `weight g = g^4 / ((2 - g)^2 * (1 - g))` by bisection).
#[must_use]
pub fn gain_for_weight(c: f64) -> f64 {
    if c <= 0.0 {
        return 0.0;
    }
    let mut lo = 0.0_f64;
    let mut hi = 1.0_f64;
    for _ in 0..80 {
        let mid = f64::midpoint(lo, hi);
        let weight_val = mid.powi(4) / ((2.0 - mid).powi(2) * (1.0 - mid));
        if weight_val < c {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    f64::midpoint(lo, hi)
}

/// How the Kalman filter sets measurement error variance.
#[derive(Clone, Copy, Debug)]
pub enum VarianceMode {
    /// Fixed variance (e.g., from offline calibration or oracle knowledge).
    Oracle(f64),
    /// Online adaptive variance estimated from the excess RTT spread
    /// `rtt - min_rtt` inside the sliding window.
    Online {
        /// Initial variance before the window fills, in s^2.
        initial: f64,
        /// Minimum floor variance (reflecting timestamp resolution), in s^2.
        floor: f64,
    },
}

/// Non-blocking sliding-window minimum-RTT front end.
///
/// Unlike blocking chunked groups (which stall whenever any UDP probe drops),
/// this front end maintains a rolling buffer of the latest `window` received
/// exchanges and emits the minimum-RTT entry every `stride` arrivals.
#[derive(Clone, Debug)]
pub struct SlidingMinRtt {
    window: usize,
    stride: usize,
    seen: usize,
    buffer: VecDeque<Exchange>,
    ewma_excess_sq: Option<f64>,
}

impl SlidingMinRtt {
    /// Create a sliding-window min-RTT selector.
    #[must_use]
    pub fn new(window: usize, stride: usize) -> SlidingMinRtt {
        SlidingMinRtt {
            window: window.max(1),
            stride: stride.max(1),
            seen: 0,
            buffer: VecDeque::with_capacity(window.max(1)),
            ewma_excess_sq: None,
        }
    }

    /// Push a newly arrived exchange. Returns `Some((best_exchange, variance))`
    /// whenever a new filtered measurement should be fed to [`OffsetFilter`].
    pub fn push(&mut self, exchange: Exchange, mode: VarianceMode) -> Option<(Exchange, f64)> {
        if self.buffer.len() == self.window {
            self.buffer.pop_front();
        }
        self.buffer.push_back(exchange);
        self.seen += 1;
        if self.seen < self.stride || !self.seen.is_multiple_of(self.stride) {
            return None;
        }
        let best = self
            .buffer
            .iter()
            .copied()
            .min_by(|a, b| a.round_trip.total_cmp(&b.round_trip))?;
        let variance = match mode {
            VarianceMode::Oracle(var) => var,
            VarianceMode::Online { initial, floor } => {
                let mut excesses: Vec<f64> = self
                    .buffer
                    .iter()
                    .map(|e| (e.round_trip - best.round_trip).max(0.0))
                    .collect();
                excesses.sort_by(f64::total_cmp);
                let med = excesses[excesses.len() / 2];
                let raw_var = (med * med) / (4.0 * as_float(self.buffer.len()));
                let alpha = 0.15;
                let smoothed = match self.ewma_excess_sq {
                    Some(prev) => (1.0 - alpha) * prev + alpha * raw_var,
                    None => 0.5 * initial + 0.5 * raw_var,
                };
                self.ewma_excess_sq = Some(smoothed);
                smoothed.max(floor)
            }
        };
        Some((best, variance))
    }
}

/// Fixed-delay baseline playback trajectory with configurable slew limit.
#[must_use]
pub fn baseline(exchanges: &[Exchange], cycle: f64, cycles: usize, slew: f64) -> Vec<Option<f64>> {
    let mut offsets = Vec::with_capacity(cycles);
    let mut next = 0;
    let mut target: Option<f64> = None;
    let mut played: Option<f64> = None;
    for k in 0..cycles {
        let now = as_float(k) * cycle;
        while next < exchanges.len() && exchanges[next].arrival <= now {
            target = Some(exchanges[next].offset);
            next += 1;
        }
        played = match (played, target) {
            (Some(previous), Some(goal)) => {
                let limit = slew * cycle;
                Some(previous + (goal - previous).clamp(-limit, limit))
            }
            (None, Some(goal)) => Some(goal),
            (previous, None) => previous,
        };
        offsets.push(played);
    }
    offsets
}

/// Configuration for the star-optimal receiver controller.
#[derive(Clone, Copy, Debug)]
pub struct StarControllerConfig {
    /// Sliding-window capacity for min-RTT selection.
    pub window: usize,
    /// Number of received probes between filter updates.
    pub stride: usize,
    /// Measurement variance mode (`Oracle` or `Online`).
    pub variance: VarianceMode,
    /// Combined sender + receiver oscillator noise.
    pub noise: FrequencyNoise,
    /// `Regulation.law` gain `g` in `(0, 1)`.
    pub gain: f64,
    /// Maximum allowed speed deviation from nominal (e.g. `1e-3`).
    pub max_slew: f64,
}

/// Simulate one star-optimal receiver using [`SlidingMinRtt`], exact zero-lag
/// [`OffsetFilter`], and clamped `Regulation.law`.
#[must_use]
pub fn star_optimal_receiver(
    exchanges: &[Exchange],
    receiver: &PhaseCourse,
    cycle: f64,
    cycles: usize,
    config: StarControllerConfig,
) -> Vec<Option<f64>> {
    let mut selector = SlidingMinRtt::new(config.window, config.stride);
    let mut filter: Option<OffsetFilter> = None;
    let mut played: Option<(f64, f64)> = None;
    let mut offsets = Vec::with_capacity(cycles);
    let mut next = 0;

    for k in 0..cycles {
        let now = as_float(k) * cycle;
        while next < exchanges.len() && exchanges[next].arrival <= now {
            if let Some((best, var)) = selector.push(exchanges[next], config.variance) {
                match filter.as_mut() {
                    Some(filt) => {
                        let _ = filt.update_at(best.offset, best.middle, var);
                    }
                    None => {
                        filter = Some(OffsetFilter::new_at(
                            best.offset,
                            best.middle,
                            var,
                            1e-10,
                            config.noise,
                        ));
                    }
                }
            }
            next += 1;
        }
        let local_now = receiver.reading(now);
        played = match (played, filter.as_ref()) {
            (Some((offset, read)), Some(filt)) => {
                let (est_off, est_freq) = filt.predict_at(local_now);
                let distance = est_off - offset;
                let pace = read - est_freq * cycle;
                let max_step = config.max_slew * cycle;
                let next_read =
                    (read + law(config.gain, distance, pace)).clamp(-max_step, max_step);
                Some((offset + next_read, next_read))
            }
            (None, Some(filt)) => {
                let (est_off, est_freq) = filt.predict_at(local_now);
                Some((est_off, est_freq * cycle))
            }
            (previous, None) => previous,
        };
        offsets.push(played.map(|(offset, _)| offset));
    }
    offsets
}

/// All six performance metrics matching `Unisono.Spec.Objectives` over a
/// simulation run (after warm-up).
#[derive(Clone, Copy, Debug, Default)]
pub struct Outcome {
    /// RMS inter-speaker timing spread (standard deviation across speakers), in
    /// seconds.
    pub spread: f64,
    /// RMS latency tracking error across speakers, in seconds.
    pub error: f64,
    /// RMS per-cycle playback speed change (roughness proxy), dimensionless.
    pub speed_change: f64,
    /// Peak per-cycle playback speed change, dimensionless.
    pub largest_speed_change: f64,
    /// Fleet-averaged fraction of audio cycles whose stream packet arrived past
    /// the playout deadline (missed samples).
    pub missed_fraction: f64,
    /// Fleet-averaged rate of playback discontinuities (on-time to late
    /// transitions per second).
    pub discontinuity_rate: f64,
}

/// Simulate audio stream packet delivery over a forward link with playout
/// margin `margin` (seconds above minimum delay) and return
/// `(missed_fraction, discontinuity_rate)`.
#[must_use]
pub fn stream_pause_metrics(
    link: LinkModel,
    drop_rate: f64,
    cycle: f64,
    duration: f64,
    warmup: f64,
    margin: f64,
    seed: u64,
) -> (f64, f64) {
    let base = Generator::new(seed);
    let mut path = Link::new(link, base.fork(1));
    let mut drops = base.fork(2);
    let cycles = step_count(duration, cycle);
    let first = step_count(warmup, cycle);
    let deadline_excess = link.minimum + margin;
    let mut missed = 0_usize;
    let mut discontinuities = 0_usize;
    let mut counted = 0_usize;
    let mut prev_late = false;
    for k in 0..cycles {
        let sent = as_float(k) * cycle;
        let arrival = path.arrival(TrueTime::from_seconds(sent)).seconds();
        let late = drops.chance(drop_rate) || (arrival - sent > deadline_excess);
        if k >= first {
            counted += 1;
            if late {
                missed += 1;
                if !prev_late {
                    discontinuities += 1;
                }
            }
        }
        prev_late = late;
    }
    let active_time = as_float(counted.max(1)) * cycle;
    (
        as_float(missed) / as_float(counted.max(1)),
        as_float(discontinuities) / active_time,
    )
}

/// Evaluate timing and speed-change metrics from played trajectories against
/// ground truth, augmented with fleet-averaged stream missed and discontinuity
/// rates.
#[must_use]
pub fn evaluate_outcome(
    played: &[Vec<Option<f64>>],
    truth: &[Vec<f64>],
    cycle: f64,
    first: usize,
    missed_fraction: f64,
    discontinuity_rate: f64,
) -> Outcome {
    let receivers = played.len();
    let cycles = played.iter().map(Vec::len).min().unwrap_or(0);
    let mut spread_sum = 0.0;
    let mut error_sum = 0.0;
    let mut speed_sum = 0.0;
    let mut largest: f64 = 0.0;
    let mut counted = 0_usize;
    let mut speed_counted = 0_usize;
    for k in first.max(2)..cycles {
        let errors: Vec<f64> = (0..receivers)
            .filter_map(|r| played[r][k].map(|p| p - truth[r][k]))
            .collect();
        if errors.len() != receivers {
            continue;
        }
        let mean = errors.iter().sum::<f64>() / as_float(receivers);
        spread_sum += errors.iter().map(|e| (e - mean).powi(2)).sum::<f64>() / as_float(receivers);
        error_sum += errors.iter().map(|e| e * e).sum::<f64>() / as_float(receivers);
        counted += 1;
        for row in played {
            if let (Some(prev2), Some(prev1), Some(curr)) = (row[k - 2], row[k - 1], row[k]) {
                let change = (curr - 2.0 * prev1 + prev2) / cycle;
                speed_sum += change * change;
                largest = largest.max(change.abs());
                speed_counted += 1;
            }
        }
    }
    if counted == 0 {
        return Outcome {
            missed_fraction,
            discontinuity_rate,
            ..Outcome::default()
        };
    }
    Outcome {
        spread: (spread_sum / as_float(counted)).sqrt(),
        error: (error_sum / as_float(counted)).sqrt(),
        speed_change: (speed_sum / as_float(speed_counted.max(1))).sqrt(),
        largest_speed_change: largest,
        missed_fraction,
        discontinuity_rate,
    }
}

/// Per-receiver network, clock, and timestamp configuration in a star scenario.
#[derive(Clone, Copy, Debug)]
pub struct ReceiverSetting {
    /// Forward link (receiver to sender for queries).
    pub forward: LinkModel,
    /// Return link (sender to receiver for replies and audio stream delivery).
    pub backward: LinkModel,
    /// Packet loss probability per direction.
    pub drop_rate: f64,
    /// Endpoint timestamp noise standard deviation, in seconds.
    pub timestamp_std: f64,
    /// Receiver oscillator noise.
    pub clock: FrequencyNoise,
    /// Calibrated or oracle measurement variance of the min-RTT output, in s^2.
    pub oracle_variance: f64,
}

/// Full star comparison scenario.
#[derive(Clone, Debug)]
pub struct StarComparison {
    /// Playback control cycle period, in seconds.
    pub cycle: f64,
    /// Clock probe interval, in seconds.
    pub period: f64,
    /// Sliding-window size for min-RTT selection.
    pub window: usize,
    /// Stride (received probes per filter update).
    pub stride: usize,
    /// Total simulated duration, in seconds.
    pub duration: f64,
    /// Warm-up duration excluded from steady-state metrics, in seconds.
    pub warmup: f64,
    /// Playout buffer margin above minimum link delay, in seconds.
    pub playout_margin: f64,
    /// `Regulation.law` gain for the star-optimal controller.
    pub gain: f64,
    /// Sender oscillator noise.
    pub sender: FrequencyNoise,
    /// Receiver settings.
    pub receivers: Vec<ReceiverSetting>,
}

/// Four-way star comparison outcomes on the same realization: baseline at
/// 1000 ppm slew, baseline at 100 ppm slew, star-optimal with oracle variance,
/// and star-optimal with online adaptive variance.
#[derive(Clone, Copy, Debug)]
pub struct StarComparisonResult {
    /// Fixed-delay baseline with 1000 ppm slew limit.
    pub baseline_1000ppm: Outcome,
    /// Fixed-delay baseline with 100 ppm slew limit (fair roughness comparison).
    pub baseline_100ppm: Outcome,
    /// Star-optimal controller with calibrated or oracle measurement variance.
    pub star_oracle: Outcome,
    /// Star-optimal controller with online adaptive measurement variance.
    pub star_online: Outcome,
}

/// Per-receiver output trajectories for [`compare_star`].
struct StarReceiverRun {
    base_1000: Vec<Option<f64>>,
    base_100: Vec<Option<f64>>,
    opt_oracle: Vec<Option<f64>>,
    opt_online: Vec<Option<f64>>,
    truth: Vec<f64>,
    missed: f64,
    discontinuities: f64,
}

fn run_star_receiver(
    setting: &StarComparison,
    sender: &PhaseCourse,
    receiver: ReceiverSetting,
    index: usize,
    seed: u64,
    generator: &Generator,
) -> StarReceiverRun {
    let step = 1e-3;
    let length = setting.duration + 5.0;
    let cycles = step_count(setting.duration, setting.cycle);
    let label = 10 + 10 * u64::try_from(index).unwrap_or(0);
    let mut draws = generator.fork(label);
    let frequency = 2e-5 * (draws.uniform() - 0.5);
    let offset = draws.uniform() - 0.5;
    let clock = PhaseCourse::draw(offset, frequency, receiver.clock, step, length, &mut draws);
    let start = setting.period * draws.uniform();
    let measured = exchanges(
        sender,
        &clock,
        ExchangeConfig {
            forward: receiver.forward,
            backward: receiver.backward,
            drop_rate: receiver.drop_rate,
            timestamp_std: receiver.timestamp_std,
            period: setting.period,
            start,
            duration: setting.duration,
        },
        seed.wrapping_add(label + 1),
    );
    let (missed, discontinuities) = stream_pause_metrics(
        receiver.backward,
        receiver.drop_rate,
        setting.cycle,
        setting.duration,
        setting.warmup,
        setting.playout_margin,
        seed.wrapping_add(label + 2),
    );
    let noise = setting.sender.combine(receiver.clock);
    let base_1000 = baseline(&measured, setting.cycle, cycles, 1e-3);
    let base_100 = baseline(&measured, setting.cycle, cycles, 1e-4);
    let opt_oracle = star_optimal_receiver(
        &measured,
        &clock,
        setting.cycle,
        cycles,
        StarControllerConfig {
            window: setting.window,
            stride: setting.stride,
            variance: VarianceMode::Oracle(receiver.oracle_variance),
            noise,
            gain: setting.gain,
            max_slew: 1e-3,
        },
    );
    let opt_online = star_optimal_receiver(
        &measured,
        &clock,
        setting.cycle,
        cycles,
        StarControllerConfig {
            window: setting.window,
            stride: setting.stride,
            variance: VarianceMode::Online {
                initial: (200e-6_f64).powi(2),
                floor: receiver.timestamp_std.powi(2).max(1e-12),
            },
            noise,
            gain: setting.gain,
            max_slew: 1e-3,
        },
    );
    let truth = (0..cycles)
        .map(|k| {
            let t = as_float(k) * setting.cycle;
            sender.at(t) - clock.at(t)
        })
        .collect();
    StarReceiverRun {
        base_1000,
        base_100,
        opt_oracle,
        opt_online,
        truth,
        missed,
        discontinuities,
    }
}

/// Run the four-way star comparison on a single deterministic seed.
#[must_use]
pub fn compare_star(setting: &StarComparison, seed: u64) -> StarComparisonResult {
    let generator = Generator::new(seed);
    let sender = PhaseCourse::draw(
        0.0,
        0.0,
        setting.sender,
        1e-3,
        setting.duration + 5.0,
        &mut generator.fork(1),
    );
    let first = step_count(setting.warmup, setting.cycle);
    let runs: Vec<StarReceiverRun> = setting
        .receivers
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, rx)| run_star_receiver(setting, &sender, rx, idx, seed, &generator))
        .collect();

    let count = as_float(runs.len().max(1));
    let avg_missed = runs.iter().map(|r| r.missed).sum::<f64>() / count;
    let avg_disc = runs.iter().map(|r| r.discontinuities).sum::<f64>() / count;
    let truth: Vec<Vec<f64>> = runs.iter().map(|r| r.truth.clone()).collect();
    let collect = |f: fn(&StarReceiverRun) -> &Vec<Option<f64>>| -> Vec<Vec<Option<f64>>> {
        runs.iter().map(|r| f(r).clone()).collect()
    };

    StarComparisonResult {
        baseline_1000ppm: evaluate_outcome(
            &collect(|r| &r.base_1000),
            &truth,
            setting.cycle,
            first,
            avg_missed,
            avg_disc,
        ),
        baseline_100ppm: evaluate_outcome(
            &collect(|r| &r.base_100),
            &truth,
            setting.cycle,
            first,
            avg_missed,
            avg_disc,
        ),
        star_oracle: evaluate_outcome(
            &collect(|r| &r.opt_oracle),
            &truth,
            setting.cycle,
            first,
            avg_missed,
            avg_disc,
        ),
        star_online: evaluate_outcome(
            &collect(|r| &r.opt_online),
            &truth,
            setting.cycle,
            first,
            avg_missed,
            avg_disc,
        ),
    }
}

/// RMS inter-speaker spreads across receiver subgroups, in seconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct Spreads {
    /// RMS standard deviation across all receivers.
    pub all: f64,
    /// RMS pairwise difference within the first group (e.g., wired pairs).
    pub first_kind: f64,
    /// RMS pairwise difference between first-group and second-group receivers.
    pub mixed: f64,
}

/// Two heterogeneous receiver classes for the sender-disciplined schedule test.
#[derive(Clone, Copy, Debug)]
pub struct HeterogeneousKinds {
    /// Number of low-jitter receivers (first group).
    pub first: usize,
    /// Number of high-jitter receivers (second group).
    pub second: usize,
    /// Own-link measurement error standard deviation for the first group, in s.
    pub first_error: f64,
    /// Own-link measurement error standard deviation for the second group, in s.
    pub second_error: f64,
    /// Shared sender-NIC transmit jitter standard deviation common to all
    /// receivers in a step, in s.
    pub tx_common_error: f64,
    /// Delivery delay (in steps) of the sender-disciplined timestamped schedule
    /// message (non-zero to avoid idealized instantaneous broadcast).
    pub schedule_delay_steps: usize,
}

#[derive(Clone, Copy, Debug, Default)]
struct SpreadSums {
    all: f64,
    first_kind: f64,
    mixed: f64,
    steps: usize,
    first_pairs: usize,
    mixed_pairs: usize,
}

impl SpreadSums {
    fn add(&mut self, errors: &[f64], first: usize) {
        let mean = errors.iter().sum::<f64>() / as_float(errors.len());
        self.all += errors.iter().map(|e| (e - mean).powi(2)).sum::<f64>() / as_float(errors.len());
        self.steps += 1;
        for r in 0..errors.len() {
            for s in r + 1..errors.len() {
                let square = (errors[r] - errors[s]).powi(2);
                if s < first {
                    self.first_kind += square;
                    self.first_pairs += 1;
                } else if r < first {
                    self.mixed += square;
                    self.mixed_pairs += 1;
                }
            }
        }
    }

    fn finish(self) -> Spreads {
        let root = |sum: f64, count: usize| {
            if count == 0 {
                0.0
            } else {
                (sum / as_float(count)).sqrt()
            }
        };
        Spreads {
            all: root(self.all, self.steps),
            first_kind: root(self.first_kind, self.first_pairs),
            mixed: root(self.mixed, self.mixed_pairs),
        }
    }
}

/// Compare independent star filters against a **sender-disciplined timestamped
/// schedule** across heterogeneous receivers.
///
/// Unlike an idealized instantaneous broadcast:
/// * Each host starts with random nonzero initial offset and fractional
///   frequency (join-referenced at step 0).
/// * The sender embeds its precision-weighted fleet correction tagged with
///   sender time and delivered with delay `kinds.schedule_delay_steps`.
/// * Residual filters use the exact variance `sigma_r^2 - V_bc` (proved in
///   `Unisono.Solutions.Optimal.residual_variance_sub`), not `sigma_r^2 + V_bc`.
#[must_use]
pub fn disciplined_schedule_comparison(
    kinds: HeterogeneousKinds,
    sender: FrequencyNoise,
    receiver: FrequencyNoise,
    interval: f64,
    steps: usize,
    seed: u64,
) -> (Spreads, Spreads) {
    let count = kinds.first + kinds.second;
    let mut generator = Generator::new(seed);
    let error_of = |r: usize| {
        if r < kinds.first {
            kinds.first_error
        } else {
            kinds.second_error
        }
    };
    let weights: Vec<f64> = (0..count).map(|r| 1.0 / error_of(r).powi(2)).collect();
    let total_w: f64 = weights.iter().sum();
    let v_bc = 1.0 / total_w;
    let combined_noise = sender.combine(receiver);

    let mut sender_state = (
        generator.uniform() - 0.5,
        2e-5 * (generator.uniform() - 0.5),
    );
    let mut rx_states: Vec<(f64, f64)> = (0..count)
        .map(|_| {
            (
                generator.uniform() - 0.5,
                2e-5 * (generator.uniform() - 0.5),
            )
        })
        .collect();

    let init_truth: Vec<f64> = rx_states.iter().map(|p| sender_state.0 - p.0).collect();
    let init_avg: f64 = init_truth
        .iter()
        .zip(&weights)
        .map(|(val, w)| val * w)
        .sum::<f64>()
        / total_w;

    let mut own: Vec<OffsetFilter> = (0..count)
        .map(|r| OffsetFilter::new(init_truth[r], error_of(r).powi(2), 1e-10, combined_noise))
        .collect();
    let mut residual: Vec<OffsetFilter> = (0..count)
        .map(|r| {
            OffsetFilter::new(
                init_truth[r] - init_avg,
                (error_of(r).powi(2) - v_bc).max(1e-18),
                1e-10,
                receiver,
            )
        })
        .collect();
    let mut sender_sched = OffsetFilter::new(init_avg, v_bc, 1e-10, sender);
    let delay = kinds.schedule_delay_steps;
    let mut sched_queue: VecDeque<(f64, f64, f64)> = VecDeque::with_capacity(delay + 1);
    for _ in 0..delay {
        sched_queue.push_back((0.0, init_avg, 0.0));
    }

    let mut without = SpreadSums::default();
    let mut with = SpreadSums::default();

    for step in 0..steps {
        let now_t = as_float(step + 1) * interval;
        advance_clock(&mut sender_state, sender, interval, &mut generator);
        for state in &mut rx_states {
            advance_clock(state, receiver, interval, &mut generator);
        }
        let tx_common = kinds.tx_common_error * generator.normal();
        let truth: Vec<f64> = rx_states.iter().map(|p| sender_state.0 - p.0).collect();
        let measured: Vec<f64> = (0..count)
            .map(|r| truth[r] + tx_common + error_of(r) * generator.normal())
            .collect();
        let avg_meas = measured
            .iter()
            .zip(&weights)
            .map(|(val, w)| val * w)
            .sum::<f64>()
            / total_w;

        sender_sched.predict(interval);
        sender_sched.update_zero_lag(avg_meas, v_bc + kinds.tx_common_error.powi(2));
        sched_queue.push_back((now_t, sender_sched.offset, sender_sched.frequency));
        let (sched_t, sched_off, sched_freq) =
            sched_queue
                .pop_front()
                .unwrap_or((now_t, sender_sched.offset, sender_sched.frequency));
        let delivered_common = sched_off + sched_freq * (now_t - sched_t);

        let mut own_errors = Vec::with_capacity(count);
        let mut sched_errors = Vec::with_capacity(count);
        for r in 0..count {
            let own_var = error_of(r).powi(2) + kinds.tx_common_error.powi(2);
            own[r].predict(interval);
            own[r].update_zero_lag(measured[r], own_var);
            own_errors.push(own[r].offset - truth[r]);

            let res_var = (error_of(r).powi(2) - v_bc).max(1e-18);
            residual[r].predict(interval);
            residual[r].update_zero_lag(measured[r] - avg_meas, res_var);
            sched_errors.push(delivered_common + residual[r].offset - truth[r]);
        }
        if step >= steps / 10 {
            without.add(&own_errors, kinds.first);
            with.add(&sched_errors, kinds.first);
        }
    }
    (without.finish(), with.finish())
}

/// Directed weighted measurement edge `(src -> dst)` observing
/// `phase(dst) - phase(src)` with noise variance `variance` and optional
/// static one-way asymmetry bias `bias`.
#[derive(Clone, Copy, Debug)]
pub struct GraphEdge {
    /// Source host index in `0..nodes`.
    pub src: usize,
    /// Destination host index in `0..nodes`.
    pub dst: usize,
    /// Measurement noise variance (must be positive), in s^2.
    pub variance: f64,
    /// Static one-way delay asymmetry bias added to the edge measurement, in s.
    pub bias: f64,
}

/// Build the reduced `(nodes - 1) x (nodes - 1)` weighted graph Laplacian with
/// host `0` grounded at zero.
fn build_reduced_laplacian(nodes: usize, edges: &[GraphEdge]) -> Vec<Vec<f64>> {
    let dim = nodes - 1;
    let mut laplacian = vec![vec![0.0_f64; dim]; dim];
    for edge in edges {
        let weight = 1.0 / edge.variance.max(1e-18);
        let src = edge.src;
        let dst = edge.dst;
        if src > 0 {
            laplacian[src - 1][src - 1] += weight;
        }
        if dst > 0 {
            laplacian[dst - 1][dst - 1] += weight;
        }
        if src > 0 && dst > 0 {
            laplacian[src - 1][dst - 1] -= weight;
            laplacian[dst - 1][src - 1] -= weight;
        }
    }
    laplacian
}

/// Solve the exact **Graph-Laplacian BLUE** (Thomson's principle) on a
/// connected measurement graph with `nodes` hosts (host `0` grounded at `0.0`).
///
/// Given noisy edge observations `obs[e] = phi[dst] - phi[src] + eta_e` with
/// independent variances `edges[e].variance`, solves the weighted normal
/// equations for `phi_hat[1..nodes]` with `phi_hat[0] = 0.0`.
#[must_use]
pub fn solve_graph_blue(nodes: usize, edges: &[GraphEdge], obs: &[f64]) -> Vec<f64> {
    if nodes <= 1 {
        return vec![0.0; nodes];
    }
    let laplacian = build_reduced_laplacian(nodes, edges);
    let mut rhs = vec![0.0_f64; nodes - 1];
    for (edge, &meas) in edges.iter().zip(obs) {
        let weight = 1.0 / edge.variance.max(1e-18);
        if edge.src > 0 {
            rhs[edge.src - 1] -= weight * meas;
        }
        if edge.dst > 0 {
            rhs[edge.dst - 1] += weight * meas;
        }
    }
    let sol = solve_linear_system(laplacian, rhs);
    let mut phi = Vec::with_capacity(nodes);
    phi.push(0.0);
    phi.extend(sol);
    phi
}

/// Compute the exact effective resistance (the minimum unbiased linear
/// estimator variance for `phi[dst_node] - phi[src_node]` under Thomson's
/// principle) between `src_node` and `dst_node` on `edges`.
#[must_use]
pub fn effective_resistance(
    nodes: usize,
    edges: &[GraphEdge],
    src_node: usize,
    dst_node: usize,
) -> f64 {
    if nodes <= 1 || src_node == dst_node {
        return 0.0;
    }
    let laplacian = build_reduced_laplacian(nodes, edges);
    let mut rhs = vec![0.0_f64; nodes - 1];
    if dst_node > 0 {
        rhs[dst_node - 1] += 1.0;
    }
    if src_node > 0 {
        rhs[src_node - 1] -= 1.0;
    }
    let psi_rest = solve_linear_system(laplacian, rhs);
    let psi = |node: usize| if node == 0 { 0.0 } else { psi_rest[node - 1] };
    psi(dst_node) - psi(src_node)
}

/// Dense Gaussian elimination with partial pivoting for small SPD Laplacian
/// systems.
fn solve_linear_system(mut mat: Vec<Vec<f64>>, mut rhs: Vec<f64>) -> Vec<f64> {
    let dim = rhs.len();
    for col in 0..dim {
        let mut pivot = col;
        let mut max_val = mat[col][col].abs();
        for (row, row_vals) in mat.iter().enumerate().skip(col + 1) {
            let val = row_vals[col].abs();
            if val > max_val {
                max_val = val;
                pivot = row;
            }
        }
        if max_val < 1e-30 {
            continue;
        }
        mat.swap(col, pivot);
        rhs.swap(col, pivot);
        let pivot_row = mat[col][col..dim].to_vec();
        let diag = pivot_row[0];
        for row in (col + 1)..dim {
            let factor = mat[row][col] / diag;
            rhs[row] -= factor * rhs[col];
            for (cell, &piv) in mat[row][col..dim].iter_mut().zip(&pivot_row) {
                *cell -= factor * piv;
            }
        }
    }
    let mut sol = vec![0.0_f64; dim];
    for idx in (0..dim).rev() {
        let mut sum = rhs[idx];
        for col in (idx + 1)..dim {
            sum -= mat[idx][col] * sol[col];
        }
        if mat[idx][idx].abs() >= 1e-30 {
            sol[idx] = sum / mat[idx][idx];
        }
    }
    sol
}

/// Configuration for comparing Star vs Peer (receiver-receiver) topologies.
#[derive(Clone, Debug)]
pub struct PeerComparisonConfig {
    /// Number of receivers (at least 2; total hosts is `receivers + 1`, with
    /// sender at index `0`).
    pub receivers: usize,
    /// Measurement graph edges for the peer topology (star edges are the
    /// subset incident on host `0`).
    pub peer_edges: Vec<GraphEdge>,
    /// Sender oscillator noise.
    pub sender_noise: FrequencyNoise,
    /// Per-receiver oscillator noise.
    pub receiver_noise: FrequencyNoise,
    /// Control and measurement step interval, in seconds.
    pub interval: f64,
    /// Total simulated steps.
    pub steps: usize,
    /// Common-mode gain `g_com` for lip-sync mode.
    pub g_com: f64,
    /// Differential-mode gain `g_diff` for both lip-sync and low-latency modes.
    pub g_diff: f64,
}

/// Side-by-side results comparing Star, Peer Lip-Sync, and Peer Low-Latency
/// (Pure Consensus) on the same realization.
#[derive(Clone, Copy, Debug)]
pub struct PeerComparisonResult {
    /// Theoretical Star pairwise standard deviation `sqrt(R_eff(1, 2))`, in s.
    pub star_pair_std_theory: f64,
    /// Theoretical Peer pairwise standard deviation `sqrt(R_eff(1, 2))`, in s.
    pub peer_pair_std_theory: f64,
    /// Independent Star controller outcome.
    pub star: Outcome,
    /// Peer Graph-Laplacian BLUE + two-gain modal lip-sync controller outcome.
    pub peer_lipsync: Outcome,
    /// Peer Graph-Laplacian BLUE + pure-consensus low-latency controller
    /// (`g_com = 0`) outcome.
    pub peer_lowlatency: Outcome,
}

/// One step of scalar `Regulation.law` position and pace evolution.
fn step_regulator(
    state: (f64, f64),
    est_off: f64,
    est_freq: f64,
    dt: f64,
    gain: f64,
) -> (f64, f64) {
    let dist = est_off - state.0;
    let pace = state.1 - est_freq * dt;
    let next_read = state.1 + law(gain, dist, pace);
    (state.0 + next_read, next_read)
}

/// Mutable state of all three controllers during [`peer_topology_comparison`].
struct PeerSimState {
    star_filters: Vec<OffsetFilter>,
    peer_com_filter: OffsetFilter,
    peer_diff_filters: Vec<OffsetFilter>,
    star_pos: Vec<(f64, f64)>,
    lip_com: (f64, f64),
    lip_diff: Vec<(f64, f64)>,
    low_com_pos: f64,
    low_diff: Vec<(f64, f64)>,
}

impl PeerSimState {
    fn new(
        config: &PeerComparisonConfig,
        star_edges: &[GraphEdge],
        clocks: &[(f64, f64)],
        peer_com_var: f64,
        peer_diff_var: f64,
    ) -> PeerSimState {
        let r_count = clocks.len() - 1;
        let combined = config.sender_noise.combine(config.receiver_noise);
        let star_var_of = |r: usize| -> f64 {
            star_edges
                .iter()
                .find(|e| (e.src == 0 && e.dst == r + 1) || (e.dst == 0 && e.src == r + 1))
                .map_or(1e-6, |e| e.variance)
        };
        let init_truth: Vec<f64> = (0..r_count)
            .map(|r| clocks[0].0 - clocks[r + 1].0)
            .collect();
        let init_mean = init_truth.iter().sum::<f64>() / as_float(r_count);

        PeerSimState {
            star_filters: (0..r_count)
                .map(|r| OffsetFilter::new(init_truth[r], star_var_of(r), 1e-10, combined))
                .collect(),
            peer_com_filter: OffsetFilter::new(init_mean, peer_com_var.max(1e-18), 1e-10, combined),
            peer_diff_filters: (0..r_count)
                .map(|r| {
                    OffsetFilter::new(
                        init_truth[r] - init_mean,
                        peer_diff_var,
                        1e-10,
                        config.receiver_noise,
                    )
                })
                .collect(),
            star_pos: init_truth.iter().map(|&x| (x, 0.0)).collect(),
            lip_com: (init_mean, 0.0),
            lip_diff: init_truth.iter().map(|&x| (x - init_mean, 0.0)).collect(),
            low_com_pos: init_mean,
            low_diff: init_truth.iter().map(|&x| (x - init_mean, 0.0)).collect(),
        }
    }

    fn step(
        &mut self,
        config: &PeerComparisonConfig,
        clocks: &[(f64, f64)],
        edge_obs: &[f64],
        peer_com_var: f64,
        peer_diff_var: f64,
        hist: &mut PeerHistories,
    ) {
        let r_count = clocks.len() - 1;
        let nodes = clocks.len();
        let dt = config.interval;

        for (edge, &obs_val) in config.peer_edges.iter().zip(edge_obs) {
            if edge.src == 0 && edge.dst >= 1 {
                let idx = edge.dst - 1;
                self.star_filters[idx].predict(dt);
                self.star_filters[idx].update_zero_lag(-obs_val, edge.variance);
            } else if edge.dst == 0 && edge.src >= 1 {
                let idx = edge.src - 1;
                self.star_filters[idx].predict(dt);
                self.star_filters[idx].update_zero_lag(obs_val, edge.variance);
            }
        }

        let phi_hat = solve_graph_blue(nodes, &config.peer_edges, edge_obs);
        let peer_offsets: Vec<f64> = (0..r_count).map(|r| -phi_hat[r + 1]).collect();
        let mean_offset = peer_offsets.iter().sum::<f64>() / as_float(r_count);

        self.peer_com_filter.predict(dt);
        self.peer_com_filter
            .update_zero_lag(mean_offset, peer_com_var.max(1e-18));
        self.lip_com = step_regulator(
            self.lip_com,
            self.peer_com_filter.offset,
            self.peer_com_filter.frequency,
            dt,
            config.g_com,
        );

        for r in 0..r_count {
            self.star_pos[r] = step_regulator(
                self.star_pos[r],
                self.star_filters[r].offset,
                self.star_filters[r].frequency,
                dt,
                config.g_diff,
            );
            hist.star[r].push(Some(self.star_pos[r].0));
            hist.truth[r].push(clocks[0].0 - clocks[r + 1].0);

            self.peer_diff_filters[r].predict(dt);
            self.peer_diff_filters[r].update_zero_lag(peer_offsets[r] - mean_offset, peer_diff_var);
            let filt = &self.peer_diff_filters[r];
            self.lip_diff[r] = step_regulator(
                self.lip_diff[r],
                filt.offset,
                filt.frequency,
                dt,
                config.g_diff,
            );
            hist.lip[r].push(Some(self.lip_com.0 + self.lip_diff[r].0));

            self.low_diff[r] = step_regulator(
                self.low_diff[r],
                filt.offset,
                filt.frequency,
                dt,
                config.g_diff,
            );
            hist.low[r].push(Some(self.low_com_pos + self.low_diff[r].0));
        }
    }
}

struct PeerHistories {
    star: Vec<Vec<Option<f64>>>,
    lip: Vec<Vec<Option<f64>>>,
    low: Vec<Vec<Option<f64>>>,
    truth: Vec<Vec<f64>>,
}

/// Simulate and compare Star vs Peer Graph-Laplacian BLUE + Modal Control on
/// the same oscillator trajectories and edge measurements.
#[must_use]
pub fn peer_topology_comparison(config: &PeerComparisonConfig, seed: u64) -> PeerComparisonResult {
    let r_count = config.receivers.max(2);
    let nodes = r_count + 1;
    let star_edges: Vec<GraphEdge> = config
        .peer_edges
        .iter()
        .copied()
        .filter(|e| e.src == 0 || e.dst == 0)
        .collect();
    let star_reff = effective_resistance(nodes, &star_edges, 1, 2);
    let peer_reff = effective_resistance(nodes, &config.peer_edges, 1, 2);
    let peer_com_var = (0..r_count)
        .map(|r| effective_resistance(nodes, &config.peer_edges, 0, r + 1))
        .sum::<f64>()
        / as_float(r_count * r_count);
    let peer_diff_var = (peer_reff / 2.0).max(1e-18);

    let mut generator = Generator::new(seed);
    let dt = config.interval;
    let mut clocks: Vec<(f64, f64)> = (0..nodes)
        .map(|node| {
            if node == 0 {
                (0.0, 0.0)
            } else {
                (
                    generator.uniform() - 0.5,
                    2e-5 * (generator.uniform() - 0.5),
                )
            }
        })
        .collect();
    let mut sim = PeerSimState::new(config, &star_edges, &clocks, peer_com_var, peer_diff_var);
    let mut hist = PeerHistories {
        star: vec![Vec::with_capacity(config.steps); r_count],
        lip: vec![Vec::with_capacity(config.steps); r_count],
        low: vec![Vec::with_capacity(config.steps); r_count],
        truth: vec![Vec::with_capacity(config.steps); r_count],
    };

    for _ in 0..config.steps {
        advance_clock(&mut clocks[0], config.sender_noise, dt, &mut generator);
        for clk in clocks.iter_mut().skip(1) {
            advance_clock(clk, config.receiver_noise, dt, &mut generator);
        }
        let edge_obs: Vec<f64> = config
            .peer_edges
            .iter()
            .map(|e| {
                (clocks[e.dst].0 - clocks[e.src].0)
                    + e.bias
                    + e.variance.sqrt() * generator.normal()
            })
            .collect();
        sim.step(
            config,
            &clocks,
            &edge_obs,
            peer_com_var,
            peer_diff_var,
            &mut hist,
        );
    }

    let warmup = config.steps / 5;
    PeerComparisonResult {
        star_pair_std_theory: star_reff.sqrt(),
        peer_pair_std_theory: peer_reff.sqrt(),
        star: evaluate_outcome(&hist.star, &hist.truth, dt, warmup, 0.0, 0.0),
        peer_lipsync: evaluate_outcome(&hist.lip, &hist.truth, dt, warmup, 0.0, 0.0),
        peer_lowlatency: evaluate_outcome(&hist.low, &hist.truth, dt, warmup, 0.0, 0.0),
    }
}

/// Optimal playout margin for exponential pauses of rate `rate` and mean length
/// `mean`, minimizing latency, missed audio, and discontinuity rate over
/// `m >= 0` (matches `Unisono.Solutions.Optimal.margin_best_exponential_with_clicks`).
#[must_use]
pub fn hold_margin_with_clicks(
    rate: f64,
    mean: f64,
    w_lat: f64,
    w_missed: f64,
    w_click: f64,
) -> f64 {
    if rate <= 0.0 || mean <= 0.0 || w_lat <= 0.0 {
        return 0.0;
    }
    let effective_weight = w_missed + w_click / mean;
    let ratio = rate * effective_weight / w_lat;
    if ratio <= 1.0 { 0.0 } else { mean * ratio.ln() }
}

/// Optimal playout margin when discontinuities are unpriced (`w_click = 0`).
#[must_use]
pub fn hold_margin(rate: f64, mean: f64, price_ratio: f64) -> f64 {
    hold_margin_with_clicks(rate, mean, price_ratio, 1.0, 0.0)
}

/// Expected fraction of missed playback under exponential pauses (Campbell's
/// formula): `rate * mean * exp(-margin / mean)`.
#[must_use]
pub fn campbell_fraction(rate: f64, mean: f64, margin: f64) -> f64 {
    rate * mean * (-margin / mean).exp()
}

/// Expected discontinuity (click) rate per second under exponential pauses:
/// `rate * exp(-margin / mean)`.
#[must_use]
pub fn click_rate(rate: f64, mean: f64, margin: f64) -> f64 {
    rate * (-margin / mean).exp()
}
