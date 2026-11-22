// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Simulation of star and peer (receiver-receiver) synchronization controllers.
//!
//! This module numerically evaluates the architectures analyzed in
//! `Unisono.Solutions.Optimal` under consumer quartz and TCXO clocks (including
//! flicker frequency noise), asymmetric links, packet loss, and link pauses:
//!
//! * **Clocks (`FrequencyNoise`, `ClockState`, `PhaseCourse`).** Parameterized
//!   by IEEE Std 1139-2008 one-sided power-law coefficients (`h0_white`,
//!   `h1_flicker`, `h2_walk`). White and random-walk frequency noise use exact
//!   continuous-time Cholesky sampling of the `[phase, frequency]` increment
//!   covariance (`h0_white / 2` and `2 * pi^2 * h2_walk`, matching
//!   `Unisono.Spec.ClockNoise`); flicker frequency noise (`h1_flicker / f`) is
//!   synthesized by a bank of logarithmically spaced Ornstein-Uhlenbeck modes
//!   (Barnes-Jarvis / Kasdin approximation).
//! * **Star estimation and control (`OffsetFilter`, `SlidingMinRtt`,
//!   `compare_star`, `optimal_shared_star_gain`).** Compares fixed-delay
//!   baselines (1000 ppm, 100 ppm, and min-RTT + 100 ppm) against a
//!   non-blocking deduplicated sliding-window min-RTT selector, a timestamped
//!   Joseph-form Kalman filter (with calibrated or online adaptive measurement
//!   variance using a fixed conservative floor), and clamped `Regulation.law`,
//!   with coupled closed-loop block-request missed and discontinuity metrics.
//! * **Causal sender-disciplined schedule (`disciplined_schedule_comparison`).**
//!   Simulates heterogeneous receivers with noisy initialization, delayed and
//!   lossy uplink reports, a causal sender filter, and delayed downlink
//!   broadcasts (with no non-causal same-step average subtraction), reporting
//!   spread, RMS latency error, and RMS roughness.
//! * **Peer / receiver-receiver topologies (`solve_graph_blue`,
//!   `blue_common_variance`, `blue_diff_variances`, `peer_topology_comparison`).**
//!   Solves the exact Graph-Laplacian best linear unbiased estimator (BLUE,
//!   Thomson's principle), computes exact correlated common-mode and
//!   differential-mode estimator variances from the reduced Laplacian inverse,
//!   and compares Star against Peer lip-sync, bounded-latency low-latency, and
//!   unbounded pure-consensus controllers under both opposite-sign and
//!   same-sign sender-link asymmetries.
//! * **Playout level with discontinuities (`hold_margin_with_clicks`,
//!   `stream_block_pause_metrics`).** Evaluates block-request missed-sample
//!   fraction and discontinuity rate under exponential link pauses.

use std::collections::VecDeque;
use std::f64::consts::PI;

use crate::TrueTime;
use crate::link::{Link, LinkModel};
use crate::random::Generator;

/// IEEE Std 1139-2008 power-law frequency noise of an oscillator.
///
/// The one-sided fractional-frequency power spectral density is
/// `h0_white + h1_flicker / f + h2_walk / f^2`, matching
/// `Unisono.Spec.ClockNoise`.
#[derive(Clone, Copy, Debug)]
pub struct FrequencyNoise {
    /// White frequency noise PSD coefficient `h_0` (seconds, i.e. `1/Hz`).
    /// Continuous-time phase diffusion variance rate is `h0_white / 2`.
    pub h0_white: f64,
    /// Flicker frequency noise PSD coefficient `h_{-1}` (dimensionless).
    /// Allan deviation floor is `sqrt(2 * ln(2) * h1_flicker)`.
    pub h1_flicker: f64,
    /// Random-walk frequency noise PSD coefficient `h_{-2}` (`Hz`).
    /// Continuous-time fractional-frequency diffusion variance rate is
    /// `2 * pi^2 * h2_walk` (distinct from `OscillatorModel::walk`, which is
    /// already a variance rate).
    pub h2_walk: f64,
}

impl FrequencyNoise {
    /// Temperature-compensated crystal oscillator (TCXO) grade (Allan
    /// deviation around `1e-9` at 1 s).
    pub const TCXO: FrequencyNoise = FrequencyNoise {
        h0_white: 2e-18,
        h1_flicker: 0.0,
        h2_walk: 5e-20,
    };

    /// Consumer quartz crystal oscillator without flicker noise (Allan
    /// deviation around `1e-7` at 1 s, thermal drift around 0.6 ppm over
    /// 100 s).
    pub const CONSUMER_QUARTZ: FrequencyNoise = FrequencyNoise {
        h0_white: 2e-14,
        h1_flicker: 0.0,
        h2_walk: 5e-16,
    };

    /// Consumer quartz crystal oscillator with realistic `1/f` flicker
    /// frequency floor (`sigma_y ~ 1.2e-7` from 1 s to 100 s).
    pub const CONSUMER_QUARTZ_FLICKER: FrequencyNoise = FrequencyNoise {
        h0_white: 2e-14,
        h1_flicker: 1e-14,
        h2_walk: 5e-16,
    };

    /// Consumer oscillator whose random-walk frequency coefficient `h_{-2}` is
    /// 100 times larger than `CONSUMER_QUARTZ` (e.g., a warming laptop or
    /// phone).
    pub const WANDERING_QUARTZ: FrequencyNoise = FrequencyNoise {
        h0_white: 2e-14,
        h1_flicker: 0.0,
        h2_walk: 5e-14,
    };

    /// Phase white-frequency variance rate `h0_white / 2` (in `s^2 / s`).
    #[must_use]
    pub fn white_variance_rate(self) -> f64 {
        self.h0_white / 2.0
    }

    /// Fractional-frequency random-walk variance rate `2 * pi^2 * h2_walk`
    /// (in `1 / s`).
    #[must_use]
    pub fn walk_variance_rate(self) -> f64 {
        2.0 * PI * PI * self.h2_walk
    }

    /// Sum of two independent clocks' IEEE 1139 noise parameters.
    #[must_use]
    pub fn combine(self, other: FrequencyNoise) -> FrequencyNoise {
        FrequencyNoise {
            h0_white: self.h0_white + other.h0_white,
            h1_flicker: self.h1_flicker + other.h1_flicker,
            h2_walk: self.h2_walk + other.h2_walk,
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

/// Compute `(median, p25, p75)` of a non-empty slice using linear
/// interpolation.
#[must_use]
pub fn quantiles(values: &[f64]) -> (f64, f64, f64) {
    if values.is_empty() {
        return (0.0, 0.0, 0.0);
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(f64::total_cmp);
    let at = |prob: f64| -> f64 {
        let pos = prob * as_float(sorted.len() - 1);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let lo = pos.floor() as usize;
        let hi = (lo + 1).min(sorted.len() - 1);
        let frac = pos - as_float(lo);
        sorted[lo] + frac * (sorted[hi] - sorted[lo])
    };
    (at(0.5), at(0.25), at(0.75))
}

/// Advance a 2-state `(phase, frequency)` clock by `dt >= 0` using exact
/// continuous-time Cholesky sampling of the integrated Brownian-motion
/// covariance `Q(dt)` for `h0_white` and `h2_walk`.
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
    let cond_phase_var = (q0 * dt + q2 * dt * dt * dt / 12.0).max(0.0);
    let dphi = state.1 * dt + 0.5 * dt * df + cond_phase_var.sqrt() * z1;
    state.0 += dphi;
    state.1 += df;
}

/// Pole corner frequencies (in Hz, 2 poles per decade from `1e-3` to
/// `3.162 Hz`) for the multi-stage Ornstein-Uhlenbeck `1/f` flicker frequency
/// synthesis bank.
const FLICKER_POLES_HZ: [f64; 8] = [
    1.0e-3,
    3.162_277_660_168_379_5e-3,
    1.0e-2,
    3.162_277_660_168_38e-2,
    1.0e-1,
    3.162_277_660_168_379_5e-1,
    1.0,
    3.162_277_660_168_379_5,
];

/// Logarithmic spacing `ln(sqrt(10)) = ln(10) / 2` between adjacent flicker
/// poles.
const FLICKER_LOG_RATIO: f64 = 1.151_292_546_497_023;

/// Full simulated oscillator state including white frequency noise,
/// random-walk frequency noise, and optional `1/f` flicker frequency modes.
#[derive(Clone, Debug)]
pub struct ClockState {
    /// Phase error `C(t) - t`, in seconds.
    pub phase: f64,
    /// Random-walk + baseline fractional frequency component.
    pub frequency: f64,
    /// Ornstein-Uhlenbeck fractional-frequency states synthesizing `h_{-1}/f`.
    flicker_modes: [f64; 8],
    noise: FrequencyNoise,
}

impl ClockState {
    /// Create a clock state at `(phase, frequency)` with flicker modes drawn
    /// from their stationary distribution.
    #[must_use]
    pub fn new(
        phase: f64,
        frequency: f64,
        noise: FrequencyNoise,
        generator: &mut Generator,
    ) -> ClockState {
        let mut flicker_modes = [0.0; 8];
        if noise.h1_flicker > 0.0 {
            let mode_std = (noise.h1_flicker * FLICKER_LOG_RATIO).sqrt();
            for mode in &mut flicker_modes {
                *mode = mode_std * generator.normal();
            }
        }
        ClockState {
            phase,
            frequency,
            flicker_modes,
            noise,
        }
    }

    /// Instantaneous total fractional frequency including flicker modes.
    #[must_use]
    pub fn total_frequency(&self) -> f64 {
        self.frequency + self.flicker_modes.iter().sum::<f64>()
    }

    /// Advance the clock state by `dt >= 0` seconds.
    pub fn advance(&mut self, dt: f64, generator: &mut Generator) {
        if dt <= 0.0 {
            return;
        }
        let mut pair = (self.phase, self.frequency);
        advance_clock(&mut pair, self.noise, dt, generator);
        self.phase = pair.0;
        self.frequency = pair.1;

        if self.noise.h1_flicker > 0.0 {
            let mode_var = self.noise.h1_flicker * FLICKER_LOG_RATIO;
            let mut flicker_phase = 0.0;
            for (mode, &corner_hz) in self.flicker_modes.iter_mut().zip(&FLICKER_POLES_HZ) {
                let omega = 2.0 * PI * corner_hz;
                let alpha = (-omega * dt).exp();
                let innov_std = (mode_var * (1.0 - alpha * alpha).max(0.0)).sqrt();
                let prev = *mode;
                let next = alpha * prev + innov_std * generator.normal();
                *mode = next;
                flicker_phase += f64::midpoint(prev, next) * dt;
            }
            self.phase += flicker_phase;
        }
    }
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
    /// over `duration` seconds using exact Cholesky increments (plus flicker
    /// modes whenever `noise.h1_flicker > 0`).
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
        let mut state = ClockState::new(offset, frequency, noise, generator);
        for _ in 0..count {
            phases.push(state.phase);
            state.advance(step, generator);
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
    /// Monotonic sequence identifier of this completed exchange.
    pub id: u64,
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
    base: &Generator,
) -> Vec<Exchange> {
    let mut forward = Link::new(config.forward, base.fork(1));
    let mut backward = Link::new(config.backward, base.fork(2));
    let mut draws = base.fork(3);
    let mut result = Vec::new();
    let mut sent = config.start;
    let mut next_id = 1_u64;
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
                id: next_id,
                offset: t2 - f64::midpoint(t1, t4),
                round_trip: rtt,
                middle: f64::midpoint(t1, t4),
                arrival: answered,
            });
            next_id += 1;
        }
        sent += config.period;
    }
    result
}

/// Timestamped two-state Kalman filter for relative clock `(offset, frequency)`
/// using Joseph-form covariance updates.
///
/// The filter stores its posterior state `(offset, frequency, covariance)` at
/// the timestamp `last_time` of the last incorporated measurement. Reading the
/// current estimate at playback time `now >= last_time` calls
/// [`OffsetFilter::predict_at`] without mutating filter state.
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

    /// Predicted offset error variance at `time >= last_time` without mutating
    /// filter state.
    #[must_use]
    pub fn predict_variance_at(&self, time: f64) -> f64 {
        let dt = (time - self.last_time).max(0.0);
        let [[p00, p01], [_, p11]] = self.covariance;
        let q0 = self.noise.white_variance_rate();
        let q2 = self.noise.walk_variance_rate();
        (p00 + 2.0 * p01 * dt + p11 * dt * dt + q0 * dt + q2 * dt * dt * dt / 3.0).max(0.0)
    }

    /// Scalar measurement update (`H = [1, 0]`) at `last_time` using the
    /// numerically stable Joseph covariance form.
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
    /// predicting to `meas_time` and performing a Joseph update. Returns
    /// `false` if the measurement is older than `last_time`.
    pub fn update_at(&mut self, measured: f64, meas_time: f64, variance: f64) -> bool {
        if meas_time < self.last_time {
            return false;
        }
        self.predict(meas_time - self.last_time);
        self.update_zero_lag(measured, variance);
        true
    }

    /// Current posterior offset variance, in `s^2`.
    #[must_use]
    pub fn offset_variance(&self) -> f64 {
        self.covariance[0][0]
    }

    /// Current `2 x 2` posterior covariance matrix `[[p00, p01], [p01, p11]]`.
    #[must_use]
    pub fn covariance(&self) -> [[f64; 2]; 2] {
        self.covariance
    }
}

/// Control law of `Unisono.Model.Regulation.law` with gain `g` in `(0, 1)`.
#[must_use]
pub fn law(g: f64, distance: f64, pace: f64) -> f64 {
    g * g / (2.0 - g) * distance - g * pace
}

/// Effective position weight of a decentralized star receiver with `receivers`
/// speakers and specification weights `(c_sync, c_track)` when cross-receiver
/// errors are uncorrelated: `((R - 1) / R) * c_sync + c_track`, matching
/// `decentralized_star_cost_eq` and `decentralized_star_uncorrelated_optimal`.
#[must_use]
pub fn decentralized_star_weight(receivers: usize, c_sync: f64, c_track: f64) -> f64 {
    let count = as_float(receivers.max(1));
    ((count - 1.0) / count) * c_sync + c_track
}

/// Optimal `Regulation.law` gain `g` in `(0, 1)` for quadratic position weight
/// `c > 0` (inverting `weight g = g^4 / ((2 - g)^2 * (1 - g))` by bisection),
/// matching `Unisono.Solutions.Optimal.gainForWeight`.
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

/// Dimensionless per-cycle quadratic position weight `(c_pos / c_rough) * dt^4`
/// converting specification weights `(c_pos, c_rough)` (in `1/s^2` and `s^2`)
/// to the cycle model with linear speed ramps across cycles of duration `dt`
/// (matching `Unisono.Spec.cyclePositionWeight_eq`).
#[must_use]
pub fn cycle_position_weight(c_pos: f64, c_rough: f64, cycle: f64) -> f64 {
    if c_rough <= 0.0 || cycle <= 0.0 {
        return 0.0;
    }
    (c_pos / c_rough) * cycle.powi(4)
}

/// Steady-state per-cycle quadratic cost `E[c_pos * E_k^2 + w_k^2]` of applying
/// `Regulation.law` with gain `gain` in `(0, 1)` to a scalar mode whose state
/// `(E, v)` is driven by zero-mean i.i.d. innovations of covariance `sigma`.
///
/// Solves the exact `2 x 2` discrete Lyapunov equation
/// `P = A(g) P A(g)^T + sigma`, where `A(g)` is the closed-loop transition of
/// `Regulation.next` under `Regulation.law g`.
#[must_use]
pub fn mode_lyapunov_cost(gain: f64, c_pos: f64, sigma: [[f64; 2]; 2]) -> f64 {
    let ke = gain * gain / (2.0 - gain);
    let a00 = 1.0 - ke;
    let a01 = -(1.0 - gain);
    let a10 = ke;
    let a11 = 1.0 - gain;

    // Linear system for `[p00, p01, p11]` in `P - A P A^T = sigma`.
    let mat = vec![
        vec![1.0 - a00 * a00, -2.0 * a00 * a01, -a01 * a01],
        vec![-a00 * a10, 1.0 - (a00 * a11 + a01 * a10), -a01 * a11],
        vec![-a10 * a10, -2.0 * a10 * a11, 1.0 - a11 * a11],
    ];
    let rhs = vec![sigma[0][0], sigma[0][1], sigma[1][1]];
    let sol = solve_linear_system(mat, rhs);
    let (p00, p01, p11) = (sol[0], sol[1], sol[2]);
    // Stage cost: c_pos * E^2 + (ke * E - g * v)^2.
    (c_pos + ke * ke) * p00 - 2.0 * ke * gain * p01 + gain * gain * p11
}

/// Steady-state per-cycle cost of a shared scalar `Regulation.law` gain across
/// `receivers` symmetric star speakers when each speaker's innovation is the
/// sum of a common sender innovation (covariance `sigma_sender`) and an
/// independent per-receiver innovation (covariance `sigma_receiver`).
///
/// Matches the orthogonal common/private decomposition of
/// `Unisono.Solutions.Optimal.symmetric_star_cost_split`:
/// * Common mode has weight `c_track` and innovation covariance
///   `sigma_sender + sigma_receiver / R`.
/// * Differential mode has weight `c_sync + c_track` and average innovation
///   covariance `((R - 1) / R) * sigma_receiver`.
#[must_use]
pub fn star_lyapunov_cost(
    receivers: usize,
    c_sync: f64,
    c_track: f64,
    sigma_sender: [[f64; 2]; 2],
    sigma_receiver: [[f64; 2]; 2],
    gain: f64,
) -> f64 {
    let r = as_float(receivers.max(1));
    let sigma_com = [
        [
            sigma_sender[0][0] + sigma_receiver[0][0] / r,
            sigma_sender[0][1] + sigma_receiver[0][1] / r,
        ],
        [
            sigma_sender[1][0] + sigma_receiver[1][0] / r,
            sigma_sender[1][1] + sigma_receiver[1][1] / r,
        ],
    ];
    let diff_scale = (r - 1.0) / r;
    let sigma_diff = [
        [
            diff_scale * sigma_receiver[0][0],
            diff_scale * sigma_receiver[0][1],
        ],
        [
            diff_scale * sigma_receiver[1][0],
            diff_scale * sigma_receiver[1][1],
        ],
    ];
    mode_lyapunov_cost(gain, c_track, sigma_com)
        + mode_lyapunov_cost(gain, c_sync + c_track, sigma_diff)
}

/// Optimal shared scalar `Regulation.law` gain `g` in `(0, 1)` for `receivers`
/// symmetric star speakers under common sender innovation covariance
/// `sigma_sender` and independent receiver innovation covariance
/// `sigma_receiver`, found by minimizing [`star_lyapunov_cost`] via
/// golden-section search.
///
/// When `sigma_sender = 0`, this coincides with
/// `gain_for_weight(decentralized_star_weight(receivers, c_sync, c_track))`;
/// as sender wander grows, the optimal shared gain shifts down toward
/// `gain_for_weight(c_track)`.
#[must_use]
pub fn optimal_shared_star_gain(
    receivers: usize,
    c_sync: f64,
    c_track: f64,
    sigma_sender: [[f64; 2]; 2],
    sigma_receiver: [[f64; 2]; 2],
) -> f64 {
    let phi = 0.5 * (5.0_f64.sqrt() - 1.0);
    let mut lo = 1e-5_f64;
    let mut hi = 1.0 - 1e-5_f64;
    let mut x1 = hi - phi * (hi - lo);
    let mut x2 = lo + phi * (hi - lo);
    let mut f1 = star_lyapunov_cost(receivers, c_sync, c_track, sigma_sender, sigma_receiver, x1);
    let mut f2 = star_lyapunov_cost(receivers, c_sync, c_track, sigma_sender, sigma_receiver, x2);
    for _ in 0..80 {
        if f1 < f2 {
            hi = x2;
            x2 = x1;
            f2 = f1;
            x1 = hi - phi * (hi - lo);
            f1 = star_lyapunov_cost(receivers, c_sync, c_track, sigma_sender, sigma_receiver, x1);
        } else {
            lo = x1;
            x1 = x2;
            f1 = f2;
            x2 = lo + phi * (hi - lo);
            f2 = star_lyapunov_cost(receivers, c_sync, c_track, sigma_sender, sigma_receiver, x2);
        }
    }
    f64::midpoint(lo, hi)
}

/// Continuous-time `[phase, frequency * cycle]` innovation covariance matrix
/// over a single cycle of length `cycle` seconds for `FrequencyNoise`.
#[must_use]
pub fn cycle_clock_innovation_cov(noise: FrequencyNoise, cycle: f64) -> [[f64; 2]; 2] {
    let q0 = noise.white_variance_rate();
    let q2 = noise.walk_variance_rate();
    let c00 = q0 * cycle + q2 * cycle.powi(3) / 3.0;
    let c01 = (q2 * cycle * cycle / 2.0) * cycle;
    let c11 = (q2 * cycle) * cycle * cycle;
    [[c00, c01], [c01, c11]]
}

/// How the Kalman filter sets measurement error variance.
#[derive(Clone, Copy, Debug)]
pub enum VarianceMode {
    /// Fixed calibrated measurement variance, in `s^2`.
    Calibrated(f64),
    /// Online adaptive variance estimated from the excess RTT spread
    /// `rtt - min_rtt` inside the sliding window, floored at a fixed
    /// conservative `floor` (not derived from ground-truth timestamp noise).
    Online {
        /// Initial variance before the window fills, in `s^2`.
        initial: f64,
        /// Fixed conservative minimum floor variance, in `s^2`.
        floor: f64,
    },
}

/// Non-blocking, deduplicated sliding-window minimum-RTT selector.
///
/// Maintains a rolling buffer of the latest `window` received exchanges and
/// inspects the window every `stride` arrivals. Tracks `last_emitted_id` so no
/// exchange is ever fed to [`OffsetFilter`] more than once.
#[derive(Clone, Debug)]
pub struct SlidingMinRtt {
    window: usize,
    stride: usize,
    seen: usize,
    last_emitted_id: Option<u64>,
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
            last_emitted_id: None,
            buffer: VecDeque::with_capacity(window.max(1)),
            ewma_excess_sq: None,
        }
    }

    /// Push a newly arrived exchange. Returns `Some((best_exchange, variance))`
    /// every `stride` arrivals provided the window minimum has not already
    /// been emitted.
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
            VarianceMode::Calibrated(var) => var,
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
        if self.last_emitted_id.is_some_and(|prev| best.id <= prev) {
            return None;
        }
        self.last_emitted_id = Some(best.id);
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

/// Fixed-delay baseline paired with the same [`SlidingMinRtt`] selector as the
/// star controller, isolating the effect of min-RTT outlier rejection from
/// Kalman filtering and `Regulation.law`.
#[must_use]
pub fn baseline_min_rtt(
    exchanges: &[Exchange],
    cycle: f64,
    cycles: usize,
    slew: f64,
    window: usize,
    stride: usize,
) -> Vec<Option<f64>> {
    let mut selector = SlidingMinRtt::new(window, stride);
    let mut offsets = Vec::with_capacity(cycles);
    let mut next = 0;
    let mut target: Option<f64> = None;
    let mut played: Option<f64> = None;
    let dummy_mode = VarianceMode::Calibrated(1e-8);
    for k in 0..cycles {
        let now = as_float(k) * cycle;
        while next < exchanges.len() && exchanges[next].arrival <= now {
            if let Some((best, _)) = selector.push(exchanges[next], dummy_mode) {
                target = Some(best.offset);
            }
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

/// Configuration for the star receiver controller.
#[derive(Clone, Copy, Debug)]
pub struct StarControllerConfig {
    /// Sliding-window capacity for min-RTT selection.
    pub window: usize,
    /// Number of received probes between window inspections.
    pub stride: usize,
    /// Measurement variance mode (`Calibrated` or `Online`).
    pub variance: VarianceMode,
    /// Combined sender + receiver oscillator noise assumed by the filter.
    pub noise: FrequencyNoise,
    /// `Regulation.law` gain `g` in `(0, 1)`.
    pub gain: f64,
    /// Maximum allowed speed deviation from nominal (e.g. `1e-3`).
    pub max_slew: f64,
}

/// Simulate one star receiver using deduplicated [`SlidingMinRtt`],
/// timestamped Joseph [`OffsetFilter`], and clamped `Regulation.law`.
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
    /// RMS per-cycle playback speed change, dimensionless.
    pub speed_change: f64,
    /// Peak per-cycle playback speed change, dimensionless.
    pub largest_speed_change: f64,
    /// Fleet-averaged fraction of audio blocks missing required frames at
    /// block-request time.
    pub missed_fraction: f64,
    /// Fleet-averaged rate of playback discontinuities (on-time to missed
    /// transitions per second).
    pub discontinuity_rate: f64,
}

/// Precomputed per-block audio stream arrivals and drops over a receiver's
/// downlink so every compared policy sees the same realized link trace while
/// using its own closed-loop timing error as effective buffer margin.
struct StreamTrace {
    minimum: f64,
    /// `None` if the block was dropped; `Some(delay)` for `arrival - sent`.
    delays: Vec<Option<f64>>,
}

impl StreamTrace {
    fn draw(link: LinkModel, drop_rate: f64, cycle: f64, cycles: usize, base: &Generator) -> Self {
        let mut path = Link::new(link, base.fork(1));
        let mut drops = base.fork(2);
        let mut delays = Vec::with_capacity(cycles);
        for k in 0..cycles {
            let sent = as_float(k) * cycle;
            let arrival = path.arrival(TrueTime::from_seconds(sent)).seconds();
            if drops.chance(drop_rate) {
                delays.push(None);
            } else {
                delays.push(Some(arrival - sent));
            }
        }
        StreamTrace {
            minimum: link.minimum,
            delays,
        }
    }

    /// Evaluate missed-block fraction and discontinuity rate under a policy's
    /// closed-loop timing trajectory `played` vs ground truth `truth`.
    ///
    /// A positive tracking error `played - truth > 0` means the receiver plays
    /// later than nominal (larger effective buffer margin); a negative tracking
    /// error shrinks the effective margin. `lookahead_sec` accounts for the
    /// resampler's lookahead frames needed at block-request time.
    fn coupled_metrics(
        &self,
        played: &[Option<f64>],
        truth: &[f64],
        cycle: f64,
        first: usize,
        margin: f64,
        lookahead_sec: f64,
    ) -> (f64, f64) {
        let mut missed = 0_usize;
        let mut discontinuities = 0_usize;
        let mut counted = 0_usize;
        let mut prev_late = false;
        let cycles = self.delays.len().min(played.len()).min(truth.len());
        for k in 0..cycles {
            // Note: `played[k]` estimates `sender - receiver` offset, so
            // `played[k] - truth[k] > 0` advances source position (plays
            // earlier, shrinking buffer margin by `played - truth`).
            let lat_err = played[k].map_or(0.0, |p| truth[k] - p);
            let deadline = self.minimum + margin + lat_err - lookahead_sec;
            let late = match self.delays[k] {
                None => true,
                Some(delay) => delay > deadline,
            };
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
}

/// Timing configuration for [`stream_block_pause_metrics`].
#[derive(Clone, Copy, Debug)]
pub struct PauseSimConfig {
    /// Audio block cycle period, in seconds.
    pub cycle: f64,
    /// Resampler lookahead duration needed at block-request time, in seconds.
    pub lookahead: f64,
    /// Total simulated duration, in seconds.
    pub duration: f64,
    /// Warm-up duration excluded from steady-state counts, in seconds.
    pub warmup: f64,
}

/// Simulate block-requested audio stream delivery over a link with playout
/// margin `margin` (seconds above minimum delay) and timing configuration
/// `config`, returning `(missed_fraction, discontinuity_rate,
/// discontinuity_count)`.
#[must_use]
pub fn stream_block_pause_metrics(
    link: LinkModel,
    drop_rate: f64,
    margin: f64,
    config: PauseSimConfig,
    seed: u64,
) -> (f64, f64, usize) {
    let base = Generator::new(seed);
    let mut path = Link::new(link, base.fork(1));
    let mut drops = base.fork(2);
    let cycles = step_count(config.duration, config.cycle);
    let first = step_count(config.warmup, config.cycle);
    let deadline_excess = link.minimum + margin - config.lookahead;
    let mut missed = 0_usize;
    let mut discontinuities = 0_usize;
    let mut counted = 0_usize;
    let mut prev_late = false;
    for k in 0..cycles {
        let sent = as_float(k) * config.cycle;
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
    let active_time = as_float(counted.max(1)) * config.cycle;
    (
        as_float(missed) / as_float(counted.max(1)),
        as_float(discontinuities) / active_time,
        discontinuities,
    )
}

/// Fast exact event-driven block-request simulation for pure exponential link
/// pauses (no drops, zero background queueing jitter), allowing multi-million-
/// second horizons so high-margin rows collect hundreds of discontinuity
/// events.
#[must_use]
pub fn pure_pause_block_metrics(
    pause_rate: f64,
    pause_length: f64,
    cycle: f64,
    lookahead_sec: f64,
    duration: f64,
    margin: f64,
    seed: u64,
) -> (f64, f64, usize) {
    if pause_rate <= 0.0 || pause_length <= 0.0 || duration <= 0.0 {
        return (0.0, 0.0, 0);
    }
    let mut draws = Generator::new(seed);
    let effective_margin = (margin - lookahead_sec).max(0.0);
    let mut t_pause = draws.exponential(1.0 / pause_rate);
    let mut missed_blocks = 0_u64;
    let mut clicks = 0_usize;
    let mut last_missed_block: Option<u64> = None;

    while t_pause < duration {
        let length = draws.exponential(pause_length);
        let paused_until = t_pause + length;
        // A block sent at `k * cycle` inside `[t_pause, paused_until)` arrives
        // at `paused_until`, so it misses iff
        // `paused_until - k * cycle > effective_margin`, i.e.
        // `k * cycle < paused_until - effective_margin` with `k * cycle >= t_pause`.
        let cutoff = paused_until - effective_margin;
        if cutoff > t_pause {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let k_start = (t_pause / cycle).ceil().max(0.0) as u64;
            let end_time = cutoff.min(duration);
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let k_end = if end_time > 0.0 {
                // Strictly `< cutoff` (subtract tiny eps for exact boundary).
                ((end_time / cycle) - 1e-12).floor().max(0.0) as u64
            } else {
                0
            };
            if k_start <= k_end && as_float(usize::try_from(k_start).unwrap_or(0)) * cycle < cutoff
            {
                let start_clamped = match last_missed_block {
                    Some(prev) if k_start <= prev => prev + 1,
                    _ => k_start,
                };
                if start_clamped <= k_end {
                    let contiguous =
                        last_missed_block.is_some_and(|prev| start_clamped == prev + 1);
                    if !contiguous {
                        clicks += 1;
                    }
                    missed_blocks += k_end - start_clamped + 1;
                    last_missed_block = Some(k_end);
                }
            }
        }
        t_pause += draws.exponential(1.0 / pause_rate);
    }
    let total_blocks = (duration / cycle).max(1.0);
    #[allow(clippy::cast_precision_loss)]
    let missed_frac = missed_blocks as f64 / total_blocks;
    (missed_frac, as_float(clicks) / duration, clicks)
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
    /// True receiver oscillator noise.
    pub clock: FrequencyNoise,
    /// Optional mismatched combined noise prior given to the Kalman filter
    /// (when `None`, uses `setting.sender.combine(receiver.clock)`).
    pub filter_noise_override: Option<FrequencyNoise>,
    /// Offline calibrated measurement variance of the min-RTT output, in `s^2`.
    pub calibrated_variance: f64,
}

/// Full star comparison scenario.
#[derive(Clone, Debug)]
pub struct StarComparison {
    /// Playback control cycle period, in seconds.
    pub cycle: f64,
    /// Resampler lookahead duration needed at block-request time, in seconds.
    pub lookahead: f64,
    /// Clock probe interval, in seconds.
    pub period: f64,
    /// Sliding-window size for min-RTT selection.
    pub window: usize,
    /// Stride (received probes between window inspections).
    pub stride: usize,
    /// Total simulated duration, in seconds.
    pub duration: f64,
    /// Warm-up duration excluded from steady-state metrics, in seconds.
    pub warmup: f64,
    /// Playout buffer margin above minimum link delay, in seconds.
    pub playout_margin: f64,
    /// Fixed conservative floor variance for the online variance estimator, in
    /// `s^2` (never derived from ground-truth `timestamp_std`).
    pub online_variance_floor: f64,
    /// `Regulation.law` gain for the star controllers.
    pub gain: f64,
    /// Sender oscillator noise.
    pub sender: FrequencyNoise,
    /// Receiver settings.
    pub receivers: Vec<ReceiverSetting>,
}

/// Five-way star comparison outcomes on the same realization.
#[derive(Clone, Copy, Debug)]
pub struct StarComparisonResult {
    /// Fixed-delay baseline with 1000 ppm slew limit.
    pub baseline_1000ppm: Outcome,
    /// Fixed-delay baseline with 100 ppm slew limit.
    pub baseline_100ppm: Outcome,
    /// Fixed-delay baseline with the same min-RTT selector and 100 ppm slew.
    pub baseline_min_rtt_100ppm: Outcome,
    /// Star controller with offline calibrated measurement variance.
    pub star_calibrated: Outcome,
    /// Star controller with online adaptive measurement variance.
    pub star_online: Outcome,
}

struct StarReceiverRun {
    base_1000: Vec<Option<f64>>,
    base_100: Vec<Option<f64>>,
    base_min_rtt: Vec<Option<f64>>,
    opt_calibrated: Vec<Option<f64>>,
    opt_online: Vec<Option<f64>>,
    truth: Vec<f64>,
    stream: StreamTrace,
}

fn run_star_receiver(
    setting: &StarComparison,
    sender: &PhaseCourse,
    receiver: ReceiverSetting,
    index: usize,
    generator: &Generator,
) -> StarReceiverRun {
    let step = 1e-3;
    let length = setting.duration + 5.0;
    let cycles = step_count(setting.duration, setting.cycle);
    let base_tag = 100 + 16 * u64::try_from(index).unwrap_or(0);
    let mut clock_draws = generator.fork(base_tag);
    let frequency = 2e-5 * (clock_draws.uniform() - 0.5);
    let offset = clock_draws.uniform() - 0.5;
    let clock = PhaseCourse::draw(
        offset,
        frequency,
        receiver.clock,
        step,
        length,
        &mut clock_draws,
    );
    let start = setting.period * clock_draws.uniform();
    let exch_gen = generator.fork(base_tag + 1);
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
        &exch_gen,
    );
    let stream_gen = generator.fork(base_tag + 2);
    let stream = StreamTrace::draw(
        receiver.backward,
        receiver.drop_rate,
        setting.cycle,
        cycles,
        &stream_gen,
    );
    let filter_noise = receiver
        .filter_noise_override
        .unwrap_or_else(|| setting.sender.combine(receiver.clock));
    let base_1000 = baseline(&measured, setting.cycle, cycles, 1e-3);
    let base_100 = baseline(&measured, setting.cycle, cycles, 1e-4);
    let base_min_rtt = baseline_min_rtt(
        &measured,
        setting.cycle,
        cycles,
        1e-4,
        setting.window,
        setting.stride,
    );
    let opt_calibrated = star_optimal_receiver(
        &measured,
        &clock,
        setting.cycle,
        cycles,
        StarControllerConfig {
            window: setting.window,
            stride: setting.stride,
            variance: VarianceMode::Calibrated(receiver.calibrated_variance),
            noise: filter_noise,
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
                floor: setting.online_variance_floor.max(1e-12),
            },
            noise: filter_noise,
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
        base_min_rtt,
        opt_calibrated,
        opt_online,
        truth,
        stream,
    }
}

fn evaluate_star_policy(
    runs: &[StarReceiverRun],
    select: fn(&StarReceiverRun) -> &Vec<Option<f64>>,
    setting: &StarComparison,
    first: usize,
) -> Outcome {
    let count = as_float(runs.len().max(1));
    let mut missed_sum = 0.0;
    let mut disc_sum = 0.0;
    let mut played = Vec::with_capacity(runs.len());
    let mut truth = Vec::with_capacity(runs.len());
    for run in runs {
        let traj = select(run);
        let (m, d) = run.stream.coupled_metrics(
            traj,
            &run.truth,
            setting.cycle,
            first,
            setting.playout_margin,
            setting.lookahead,
        );
        missed_sum += m;
        disc_sum += d;
        played.push(traj.clone());
        truth.push(run.truth.clone());
    }
    evaluate_outcome(
        &played,
        &truth,
        setting.cycle,
        first,
        missed_sum / count,
        disc_sum / count,
    )
}

/// Run the five-way star comparison on a single deterministic seed.
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
        .map(|(idx, rx)| run_star_receiver(setting, &sender, rx, idx, &generator))
        .collect();

    StarComparisonResult {
        baseline_1000ppm: evaluate_star_policy(&runs, |r| &r.base_1000, setting, first),
        baseline_100ppm: evaluate_star_policy(&runs, |r| &r.base_100, setting, first),
        baseline_min_rtt_100ppm: evaluate_star_policy(&runs, |r| &r.base_min_rtt, setting, first),
        star_calibrated: evaluate_star_policy(&runs, |r| &r.opt_calibrated, setting, first),
        star_online: evaluate_star_policy(&runs, |r| &r.opt_online, setting, first),
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

/// Closed-loop metrics for one policy in [`disciplined_schedule_comparison`].
#[derive(Clone, Copy, Debug, Default)]
pub struct ScheduleMetrics {
    /// Inter-speaker timing spreads (all, first group, mixed pairs), in s.
    pub spreads: Spreads,
    /// RMS latency tracking error across all receivers, in s.
    pub rms_error: f64,
    /// RMS per-cycle playback speed change, dimensionless.
    pub rms_roughness: f64,
}

/// Two heterogeneous receiver classes for the causal sender-disciplined
/// schedule comparison.
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
    /// Shared sender transmit jitter standard deviation common to all
    /// receivers in a step, in s.
    pub tx_common_error: f64,
    /// Causal uplink report delay from receivers to sender, in steps (`>= 1`).
    pub uplink_delay_steps: usize,
    /// Causal downlink schedule broadcast delay from sender to receivers, in
    /// steps (`>= 1`).
    pub downlink_delay_steps: usize,
    /// Independent uplink report loss probability in `[0, 1)`.
    pub report_drop_rate: f64,
    /// `Regulation.law` gain applied to the closed-loop playback regulator.
    pub gain: f64,
}

#[derive(Clone, Copy, Debug, Default)]
struct ScheduleSums {
    all: f64,
    first_kind: f64,
    mixed: f64,
    err_sq: f64,
    rough_sq: f64,
    steps: usize,
    first_pairs: usize,
    mixed_pairs: usize,
    rough_samples: usize,
}

impl ScheduleSums {
    fn add(&mut self, errors: &[f64], first: usize, speed_changes: &[f64]) {
        let count = as_float(errors.len());
        let mean = errors.iter().sum::<f64>() / count;
        self.all += errors.iter().map(|e| (e - mean).powi(2)).sum::<f64>() / count;
        self.err_sq += errors.iter().map(|e| e * e).sum::<f64>() / count;
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
        for &sc in speed_changes {
            self.rough_sq += sc * sc;
            self.rough_samples += 1;
        }
    }

    fn finish(self) -> ScheduleMetrics {
        let root = |sum: f64, count: usize| {
            if count == 0 {
                0.0
            } else {
                (sum / as_float(count)).sqrt()
            }
        };
        ScheduleMetrics {
            spreads: Spreads {
                all: root(self.all, self.steps),
                first_kind: root(self.first_kind, self.first_pairs),
                mixed: root(self.mixed, self.mixed_pairs),
            },
            rms_error: root(self.err_sq, self.steps),
            rms_roughness: root(self.rough_sq, self.rough_samples),
        }
    }
}

struct ScheduleSim {
    kinds: HeterogeneousKinds,
    weights: Vec<f64>,
    sender_sched_noise: FrequencyNoise,
    sender_clk: ClockState,
    rx_clks: Vec<ClockState>,
    own: Vec<OffsetFilter>,
    residual: Vec<OffsetFilter>,
    sender_sched: OffsetFilter,
    uplink_queue: VecDeque<(f64, Vec<Option<f64>>)>,
    downlink_queue: VecDeque<(f64, f64, f64, f64)>,
    own_pos: Vec<(f64, f64)>,
    sched_pos: Vec<(f64, f64)>,
}

impl ScheduleSim {
    fn error_of(&self, r: usize) -> f64 {
        if r < self.kinds.first {
            self.kinds.first_error
        } else {
            self.kinds.second_error
        }
    }

    fn new(
        kinds: HeterogeneousKinds,
        sender: FrequencyNoise,
        receiver: FrequencyNoise,
        generator: &mut Generator,
    ) -> Self {
        let count = kinds.first + kinds.second;
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
        let sum_w2: f64 = weights.iter().map(|w| w * w).sum();
        let eff_count = (total_w * total_w) / sum_w2;
        let sender_sched_noise = FrequencyNoise {
            h0_white: sender.h0_white + receiver.h0_white / eff_count,
            h1_flicker: sender.h1_flicker + receiver.h1_flicker / eff_count,
            h2_walk: sender.h2_walk + receiver.h2_walk / eff_count,
        };
        let sender_clk = ClockState::new(
            generator.uniform() - 0.5,
            2e-5 * (generator.uniform() - 0.5),
            sender,
            generator,
        );
        let rx_clks: Vec<ClockState> = (0..count)
            .map(|_| {
                ClockState::new(
                    generator.uniform() - 0.5,
                    2e-5 * (generator.uniform() - 0.5),
                    receiver,
                    generator,
                )
            })
            .collect();
        let tx0 = kinds.tx_common_error * generator.normal();
        let init_meas: Vec<f64> = (0..count)
            .map(|r| (sender_clk.phase - rx_clks[r].phase) + tx0 + error_of(r) * generator.normal())
            .collect();
        let init_avg: f64 = init_meas
            .iter()
            .zip(&weights)
            .map(|(v, w)| v * w)
            .sum::<f64>()
            / total_w;
        let own = (0..count)
            .map(|r| {
                OffsetFilter::new(
                    init_meas[r],
                    error_of(r).powi(2) + kinds.tx_common_error.powi(2),
                    1e-10,
                    combined_noise,
                )
            })
            .collect();
        let residual = (0..count)
            .map(|r| {
                OffsetFilter::new(
                    init_meas[r] - init_avg,
                    error_of(r).powi(2) + v_bc,
                    1e-10,
                    receiver,
                )
            })
            .collect();
        let sender_sched = OffsetFilter::new(
            init_avg,
            v_bc + kinds.tx_common_error.powi(2),
            1e-10,
            sender_sched_noise,
        );
        let up_delay = kinds.uplink_delay_steps.max(1);
        let down_delay = kinds.downlink_delay_steps.max(1);
        let mut uplink_queue = VecDeque::with_capacity(up_delay + 1);
        for _ in 0..up_delay {
            uplink_queue.push_back((0.0, vec![Some(init_avg); count]));
        }
        let mut downlink_queue = VecDeque::with_capacity(down_delay + 1);
        for _ in 0..down_delay {
            downlink_queue.push_back((0.0, init_avg, 0.0, v_bc + kinds.tx_common_error.powi(2)));
        }
        Self {
            kinds,
            weights,
            sender_sched_noise,
            sender_clk,
            rx_clks,
            own,
            residual,
            sender_sched,
            uplink_queue,
            downlink_queue,
            own_pos: init_meas.iter().map(|&x| (x, 0.0)).collect(),
            sched_pos: init_meas.iter().map(|&x| (x, 0.0)).collect(),
        }
    }

    fn step(
        &mut self,
        now_t: f64,
        interval: f64,
        record: bool,
        generator: &mut Generator,
        without: &mut ScheduleSums,
        with: &mut ScheduleSums,
    ) {
        let count = self.rx_clks.len();
        self.sender_clk.advance(interval, generator);
        for clk in &mut self.rx_clks {
            clk.advance(interval, generator);
        }
        let tx_common = self.kinds.tx_common_error * generator.normal();
        let truth: Vec<f64> = self
            .rx_clks
            .iter()
            .map(|c| self.sender_clk.phase - c.phase)
            .collect();
        let measured: Vec<f64> = (0..count)
            .map(|r| truth[r] + tx_common + self.error_of(r) * generator.normal())
            .collect();

        // Each receiver removes its own causal prior residual before reporting
        // to the sender, so arbitrary per-receiver boot epochs and crystal
        // frequency offsets never cause jumps when a report drops.
        let mut prior_res = Vec::with_capacity(count);
        for r in 0..count {
            self.residual[r].predict(interval);
            prior_res.push(self.residual[r].offset);
        }

        let reports: Vec<Option<f64>> = (0..count)
            .map(|r| {
                if generator.chance(self.kinds.report_drop_rate) {
                    None
                } else {
                    Some(measured[r] - prior_res[r])
                }
            })
            .collect();
        self.uplink_queue.push_back((now_t, reports));

        if let Some((rep_t, arrived)) = self.uplink_queue.pop_front() {
            let mut w_sum = 0.0;
            let mut val_sum = 0.0;
            for (r, &rep) in arrived.iter().enumerate() {
                if let Some(y) = rep {
                    w_sum += self.weights[r];
                    val_sum += self.weights[r] * y;
                }
            }
            if w_sum > 0.0 && rep_t >= self.sender_sched.last_time {
                let rep_var = 1.0 / w_sum + self.kinds.tx_common_error.powi(2);
                let _ = self.sender_sched.update_at(val_sum / w_sum, rep_t, rep_var);
            }
        }
        let (bc_off, bc_freq) = self.sender_sched.predict_at(now_t);
        let bc_var = self.sender_sched.predict_variance_at(now_t);
        self.downlink_queue
            .push_back((now_t, bc_off, bc_freq, bc_var));

        let (sched_t, sched_off, sched_freq, sched_var) = self
            .downlink_queue
            .pop_front()
            .unwrap_or((now_t, bc_off, bc_freq, bc_var));
        let dt_bc = (now_t - sched_t).max(0.0);
        let s_hat = sched_off + sched_freq * dt_bc;
        let extrap_var = sched_var
            + self.sender_sched_noise.white_variance_rate() * dt_bc
            + self.sender_sched_noise.walk_variance_rate() * dt_bc.powi(3) / 3.0;

        let mut own_errors = Vec::with_capacity(count);
        let mut own_sc = Vec::with_capacity(count);
        let mut sched_errors = Vec::with_capacity(count);
        let mut sched_sc = Vec::with_capacity(count);
        for r in 0..count {
            let own_var = self.error_of(r).powi(2) + self.kinds.tx_common_error.powi(2);
            self.own[r].predict(interval);
            self.own[r].update_zero_lag(measured[r], own_var);
            let prev_own_read = self.own_pos[r].1;
            self.own_pos[r] = step_regulator(
                self.own_pos[r],
                self.own[r].offset,
                self.own[r].frequency,
                interval,
                self.kinds.gain,
            );
            own_errors.push(self.own_pos[r].0 - truth[r]);
            own_sc.push((self.own_pos[r].1 - prev_own_read) / interval);

            let res_var = (own_var + extrap_var).max(1e-18);
            self.residual[r].update_zero_lag(measured[r] - s_hat, res_var);
            let est_off = s_hat + self.residual[r].offset;
            let est_freq = sched_freq + self.residual[r].frequency;
            let prev_sched_read = self.sched_pos[r].1;
            self.sched_pos[r] = step_regulator(
                self.sched_pos[r],
                est_off,
                est_freq,
                interval,
                self.kinds.gain,
            );
            sched_errors.push(self.sched_pos[r].0 - truth[r]);
            sched_sc.push((self.sched_pos[r].1 - prev_sched_read) / interval);
        }
        if record {
            without.add(&own_errors, self.kinds.first, &own_sc);
            with.add(&sched_errors, self.kinds.first, &sched_sc);
        }
    }
}

/// Compare independent star filters against a **causal sender-disciplined
/// timestamped schedule** across heterogeneous receivers.
///
/// Every filter is initialized from noisy step-0 measurements (never ground
/// truth) and operates strictly causally:
/// * Receivers send noisy measurements to the sender over delayed, lossy
///   uplinks (`uplink_delay_steps`, `report_drop_rate`).
/// * The sender updates a causal Kalman filter (`s_ref`, `s_ref'`) from
///   arrived uplink reports and embeds `(t_stamp, s_ref, s_ref')` in audio
///   headers delivered after `downlink_delay_steps`.
/// * Each receiver extrapolates the latest received broadcast `s_hat(t)` and
///   filters its causal residual `measured[r] - s_hat(t)` (never subtracting
///   any non-causal same-step average).
/// * Both independent and scheduled estimates drive `Regulation.law`, reporting
///   closed-loop spread, RMS latency tracking error, and RMS roughness.
#[must_use]
pub fn disciplined_schedule_comparison(
    kinds: HeterogeneousKinds,
    sender: FrequencyNoise,
    receiver: FrequencyNoise,
    interval: f64,
    steps: usize,
    seed: u64,
) -> (ScheduleMetrics, ScheduleMetrics) {
    let mut generator = Generator::new(seed);
    let mut sim = ScheduleSim::new(kinds, sender, receiver, &mut generator);
    let mut without = ScheduleSums::default();
    let mut with = ScheduleSums::default();
    for step in 0..steps {
        let now_t = as_float(step + 1) * interval;
        sim.step(
            now_t,
            interval,
            step >= steps / 10,
            &mut generator,
            &mut without,
            &mut with,
        );
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
    /// Measurement noise variance (must be positive), in `s^2`.
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

/// Compute the exact effective resistance (minimum unbiased linear estimator
/// variance for `phi[dst_node] - phi[src_node]` under Thomson's principle)
/// between `src_node` and `dst_node` on `edges`.
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

/// Exact variance of the BLUE common-mode (receiver-mean) offset estimate
/// `mean_r(-phi_hat[r])`: equals `(1 / R^2) * 1^T L_red^{-1} 1`, accounting
/// for cross-receiver estimation covariance induced by peer links.
#[must_use]
pub fn blue_common_variance(nodes: usize, edges: &[GraphEdge]) -> f64 {
    if nodes <= 1 {
        return 0.0;
    }
    let dim = nodes - 1;
    let inv_r = 1.0 / as_float(dim);
    let laplacian = build_reduced_laplacian(nodes, edges);
    let rhs = vec![inv_r; dim];
    let sol = solve_linear_system(laplacian, rhs);
    (sol.iter().sum::<f64>() * inv_r).max(1e-18)
}

/// Exact per-receiver variances of the BLUE differential offset estimates
/// `(-phi_hat[r]) - mean_s(-phi_hat[s])`: for receiver `r`, equals
/// `(e_r - (1/R) 1)^T L_red^{-1} (e_r - (1/R) 1)`.
#[must_use]
pub fn blue_diff_variances(nodes: usize, edges: &[GraphEdge]) -> Vec<f64> {
    if nodes <= 1 {
        return Vec::new();
    }
    let dim = nodes - 1;
    let inv_r = 1.0 / as_float(dim);
    let laplacian = build_reduced_laplacian(nodes, edges);
    (0..dim)
        .map(|r| {
            let mut vec_c = vec![-inv_r; dim];
            vec_c[r] += 1.0;
            let sol = solve_linear_system(laplacian.clone(), vec_c.clone());
            let var: f64 = vec_c.iter().zip(&sol).map(|(a, b)| a * b).sum();
            var.max(1e-18)
        })
        .collect()
}

/// Exact deterministic bias of the Graph-Laplacian BLUE for
/// `phi[dst_node] - phi[src_node]` under the static edge biases `edge.bias`
/// (`sum_e f_e^* alpha_e`, matching `Unisono.Solutions.Optimal.graph_estimator_bias`).
#[must_use]
pub fn blue_pair_bias(nodes: usize, edges: &[GraphEdge], src_node: usize, dst_node: usize) -> f64 {
    if nodes <= 1 || src_node == dst_node {
        return 0.0;
    }
    let biases: Vec<f64> = edges.iter().map(|e| e.bias).collect();
    let phi = solve_graph_blue(nodes, edges, &biases);
    phi[dst_node] - phi[src_node]
}

/// Dense Gaussian elimination with partial pivoting for small linear systems.
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
    /// Small positive common-mode gain `g_com_low` for bounded-latency
    /// low-latency peer control (`0 < g_com_low << g_diff`).
    pub g_com_low: f64,
    /// Differential-mode gain `g_diff` for both lip-sync and low-latency modes.
    pub g_diff: f64,
}

/// Side-by-side results comparing Star, Peer Lip-Sync, Peer Low-Latency
/// (bounded common mode), and unbounded Pure Consensus (`g_com = 0`) on the
/// same realization.
#[derive(Clone, Copy, Debug)]
pub struct PeerComparisonResult {
    /// Theoretical Star pairwise standard deviation `sqrt(R_eff(1, 2))`, in s.
    pub star_pair_std_theory: f64,
    /// Theoretical Peer pairwise standard deviation `sqrt(R_eff(1, 2))`, in s.
    pub peer_pair_std_theory: f64,
    /// Theoretical BLUE pairwise asymmetry bias `|sum f_e^* alpha_e|`, in s.
    pub peer_pair_bias_theory: f64,
    /// Independent Star controller outcome.
    pub star: Outcome,
    /// Peer Graph-Laplacian BLUE + two-gain modal lip-sync controller outcome.
    pub peer_lipsync: Outcome,
    /// Peer Graph-Laplacian BLUE + bounded-latency low-latency controller
    /// (`g_com_low > 0`) outcome.
    pub peer_lowlatency: Outcome,
    /// Peer Graph-Laplacian BLUE + unbounded pure consensus (`g_com = 0`)
    /// outcome (explicitly quantifying its unbounded common-mode latency
    /// drift).
    pub peer_unbounded_consensus: Outcome,
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

struct PeerSimState {
    star_filters: Vec<Option<OffsetFilter>>,
    peer_com_filter: OffsetFilter,
    peer_diff_filters: Vec<OffsetFilter>,
    star_pos: Vec<(f64, f64)>,
    lip_com: (f64, f64),
    lip_diff: Vec<(f64, f64)>,
    low_com: (f64, f64),
    low_diff: Vec<(f64, f64)>,
    unbounded_com_pos: f64,
    unbounded_diff: Vec<(f64, f64)>,
}

impl PeerSimState {
    fn new(
        config: &PeerComparisonConfig,
        init_edge_obs: &[f64],
        peer_com_var: f64,
        peer_diff_vars: &[f64],
    ) -> PeerSimState {
        let r_count = config.receivers.max(2);
        let nodes = r_count + 1;
        let combined = config.sender_noise.combine(config.receiver_noise);
        let com_noise = FrequencyNoise {
            h0_white: config.sender_noise.h0_white
                + config.receiver_noise.h0_white / as_float(r_count),
            h1_flicker: config.sender_noise.h1_flicker
                + config.receiver_noise.h1_flicker / as_float(r_count),
            h2_walk: config.sender_noise.h2_walk
                + config.receiver_noise.h2_walk / as_float(r_count),
        };

        // Initialize star filters strictly from noisy step-0 star edges;
        // receivers without any incident star edge remain `None`.
        let mut star_filters: Vec<Option<OffsetFilter>> = vec![None; r_count];
        let mut star_init_pos: Vec<f64> = vec![0.0; r_count];
        for (edge, &obs_val) in config.peer_edges.iter().zip(init_edge_obs) {
            let (idx, meas) = if edge.src == 0 && edge.dst >= 1 {
                (edge.dst - 1, -obs_val)
            } else if edge.dst == 0 && edge.src >= 1 {
                (edge.src - 1, obs_val)
            } else {
                continue;
            };
            match star_filters[idx].as_mut() {
                Some(filt) => filt.update_zero_lag(meas, edge.variance),
                None => {
                    star_filters[idx] =
                        Some(OffsetFilter::new(meas, edge.variance, 1e-10, combined));
                }
            }
            if let Some(filt) = star_filters[idx].as_ref() {
                star_init_pos[idx] = filt.offset;
            }
        }

        // Initialize peer filters strictly from noisy step-0 BLUE solution.
        let init_phi = solve_graph_blue(nodes, &config.peer_edges, init_edge_obs);
        let init_peer_offsets: Vec<f64> = (0..r_count).map(|r| -init_phi[r + 1]).collect();
        let init_mean = init_peer_offsets.iter().sum::<f64>() / as_float(r_count);

        PeerSimState {
            star_filters,
            peer_com_filter: OffsetFilter::new(init_mean, peer_com_var, 1e-10, com_noise),
            peer_diff_filters: (0..r_count)
                .map(|r| {
                    OffsetFilter::new(
                        init_peer_offsets[r] - init_mean,
                        peer_diff_vars[r],
                        1e-10,
                        config.receiver_noise,
                    )
                })
                .collect(),
            star_pos: star_init_pos.iter().map(|&x| (x, 0.0)).collect(),
            lip_com: (init_mean, 0.0),
            lip_diff: init_peer_offsets
                .iter()
                .map(|&x| (x - init_mean, 0.0))
                .collect(),
            low_com: (init_mean, 0.0),
            low_diff: init_peer_offsets
                .iter()
                .map(|&x| (x - init_mean, 0.0))
                .collect(),
            unbounded_com_pos: init_mean,
            unbounded_diff: init_peer_offsets
                .iter()
                .map(|&x| (x - init_mean, 0.0))
                .collect(),
        }
    }

    fn step(
        &mut self,
        config: &PeerComparisonConfig,
        clocks: &[ClockState],
        edge_obs: &[f64],
        peer_com_var: f64,
        peer_diff_vars: &[f64],
        hist: &mut PeerHistories,
    ) {
        let r_count = clocks.len() - 1;
        let nodes = clocks.len();
        let dt = config.interval;

        // Predict every star filter ONCE per step (even if multiple or
        // bidirectional star edges touch the same receiver).
        for filt in self.star_filters.iter_mut().flatten() {
            filt.predict(dt);
        }
        for (edge, &obs_val) in config.peer_edges.iter().zip(edge_obs) {
            if edge.src == 0
                && edge.dst >= 1
                && let Some(filt) = self.star_filters[edge.dst - 1].as_mut()
            {
                filt.update_zero_lag(-obs_val, edge.variance);
            } else if edge.dst == 0
                && edge.src >= 1
                && let Some(filt) = self.star_filters[edge.src - 1].as_mut()
            {
                filt.update_zero_lag(obs_val, edge.variance);
            }
        }

        let phi_hat = solve_graph_blue(nodes, &config.peer_edges, edge_obs);
        let peer_offsets: Vec<f64> = (0..r_count).map(|r| -phi_hat[r + 1]).collect();
        let mean_offset = peer_offsets.iter().sum::<f64>() / as_float(r_count);

        self.peer_com_filter.predict(dt);
        self.peer_com_filter
            .update_zero_lag(mean_offset, peer_com_var);
        self.lip_com = step_regulator(
            self.lip_com,
            self.peer_com_filter.offset,
            self.peer_com_filter.frequency,
            dt,
            config.g_com,
        );
        self.low_com = step_regulator(
            self.low_com,
            self.peer_com_filter.offset,
            self.peer_com_filter.frequency,
            dt,
            config.g_com_low,
        );

        for r in 0..r_count {
            if let Some(filt) = self.star_filters[r].as_ref() {
                self.star_pos[r] = step_regulator(
                    self.star_pos[r],
                    filt.offset,
                    filt.frequency,
                    dt,
                    config.g_diff,
                );
                hist.star[r].push(Some(self.star_pos[r].0));
            } else {
                hist.star[r].push(None);
            }
            hist.truth[r].push(clocks[0].phase - clocks[r + 1].phase);

            self.peer_diff_filters[r].predict(dt);
            self.peer_diff_filters[r]
                .update_zero_lag(peer_offsets[r] - mean_offset, peer_diff_vars[r]);
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
            hist.low[r].push(Some(self.low_com.0 + self.low_diff[r].0));

            self.unbounded_diff[r] = step_regulator(
                self.unbounded_diff[r],
                filt.offset,
                filt.frequency,
                dt,
                config.g_diff,
            );
            hist.unbounded[r].push(Some(self.unbounded_com_pos + self.unbounded_diff[r].0));
        }
    }
}

struct PeerHistories {
    star: Vec<Vec<Option<f64>>>,
    lip: Vec<Vec<Option<f64>>>,
    low: Vec<Vec<Option<f64>>>,
    unbounded: Vec<Vec<Option<f64>>>,
    truth: Vec<Vec<f64>>,
}

/// Simulate and compare Star vs Peer Graph-Laplacian BLUE + Modal Control on
/// the same oscillator trajectories and noisy edge measurements.
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
    let peer_bias = blue_pair_bias(nodes, &config.peer_edges, 1, 2).abs();
    let peer_com_var = blue_common_variance(nodes, &config.peer_edges);
    let peer_diff_vars = blue_diff_variances(nodes, &config.peer_edges);

    let mut generator = Generator::new(seed);
    let dt = config.interval;
    let mut clocks: Vec<ClockState> = (0..nodes)
        .map(|node| {
            if node == 0 {
                ClockState::new(0.0, 0.0, config.sender_noise, &mut generator)
            } else {
                let off = generator.uniform() - 0.5;
                let freq = 2e-5 * (generator.uniform() - 0.5);
                ClockState::new(off, freq, config.receiver_noise, &mut generator)
            }
        })
        .collect();

    let observe_edges = |clks: &[ClockState], gen_rng: &mut Generator| -> Vec<f64> {
        config
            .peer_edges
            .iter()
            .map(|e| {
                (clks[e.dst].phase - clks[e.src].phase)
                    + e.bias
                    + e.variance.sqrt() * gen_rng.normal()
            })
            .collect()
    };

    let init_obs = observe_edges(&clocks, &mut generator);
    let mut sim = PeerSimState::new(config, &init_obs, peer_com_var, &peer_diff_vars);
    let mut hist = PeerHistories {
        star: vec![Vec::with_capacity(config.steps); r_count],
        lip: vec![Vec::with_capacity(config.steps); r_count],
        low: vec![Vec::with_capacity(config.steps); r_count],
        unbounded: vec![Vec::with_capacity(config.steps); r_count],
        truth: vec![Vec::with_capacity(config.steps); r_count],
    };

    for _ in 0..config.steps {
        for clk in &mut clocks {
            clk.advance(dt, &mut generator);
        }
        let edge_obs = observe_edges(&clocks, &mut generator);
        sim.step(
            config,
            &clocks,
            &edge_obs,
            peer_com_var,
            &peer_diff_vars,
            &mut hist,
        );
    }

    let warmup = config.steps / 5;
    PeerComparisonResult {
        star_pair_std_theory: star_reff.sqrt(),
        peer_pair_std_theory: peer_reff.sqrt(),
        peer_pair_bias_theory: peer_bias,
        star: evaluate_outcome(&hist.star, &hist.truth, dt, warmup, 0.0, 0.0),
        peer_lipsync: evaluate_outcome(&hist.lip, &hist.truth, dt, warmup, 0.0, 0.0),
        peer_lowlatency: evaluate_outcome(&hist.low, &hist.truth, dt, warmup, 0.0, 0.0),
        peer_unbounded_consensus: evaluate_outcome(
            &hist.unbounded,
            &hist.truth,
            dt,
            warmup,
            0.0,
            0.0,
        ),
    }
}

/// Optimal playout margin for exponential pauses of rate `rate` and mean length
/// `mean`, minimizing linear latency, missed audio, and discontinuity rate over
/// `m >= 0` (matches `Unisono.Solutions.Optimal.margin_best_exponential_with_clicks`).
///
/// Returns `None` when `w_lat <= 0.0` (where no finite margin minimizes the
/// objective if missed audio or clicks are priced).
#[must_use]
pub fn hold_margin_with_clicks(
    rate: f64,
    mean: f64,
    w_lat: f64,
    w_missed: f64,
    w_click: f64,
) -> Option<f64> {
    if w_lat <= 0.0 {
        return None;
    }
    if rate <= 0.0 || mean <= 0.0 {
        return Some(0.0);
    }
    let effective_weight = w_missed + w_click / mean;
    if effective_weight <= 0.0 {
        return Some(0.0);
    }
    let ratio = rate * effective_weight / w_lat;
    Some(if ratio <= 1.0 { 0.0 } else { mean * ratio.ln() })
}

/// Optimal playout margin when discontinuities are unpriced (`w_click = 0`).
#[must_use]
pub fn hold_margin(rate: f64, mean: f64, price_ratio: f64) -> Option<f64> {
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
