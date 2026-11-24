// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `[ORACLE / MODEL BENCHMARK]` Offline analytical calculators, Graph-BLUE
//! variance/bias identities, per-cycle Lyapunov cost evaluators, and
//! floating-point reference estimators.
//!
//! Nothing in this module is a deployable protocol. Every function and type
//! here uses known true model parameters strictly to compute offline
//! analytical reference values (`multiCycleCost` per-cycle Lyapunov cost,
//! Graph-BLUE effective resistance, continuous-time Campbell pause cost
//! `J_buf`) and to cross-check the fixed-point implementations in
//! `unisono_core`. None of the per-cycle Lyapunov evaluators here is a
//! lower bound over all policies on the six canonical `Unisono.Spec.Objectives`.

use crate::clock::FrequencyNoise;
use crate::random::Generator;

/// Converts a `usize` count to `f64` for analytical formulas.
fn as_float(count: usize) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let value = count as f64;
    value
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Floating-point reference Kalman filter
/// for a relative clock offset whose rate follows a random walk.
///
/// The state is the offset `x` between two clocks and its fractional rate `r`.
/// Over duration `dt`, the offset grows by `r * dt` and the rate gains noise of
/// variance `walk * dt`. A measurement observes `x` plus zero-mean noise of
/// variance `noise`. Used only to validate fixed-point estimators in
/// `unisono_core`, never as a deployable protocol.
#[derive(Clone, Copy, Debug)]
pub struct OffsetKalman {
    walk: f64,
    noise: f64,
    offset: f64,
    rate: f64,
    /// Symmetric `2 x 2` covariance: `[pxx, pxr, prr]`.
    covariance: [f64; 3],
}

impl OffsetKalman {
    /// `[ORACLE / CENTRALIZED BENCHMARK]` Creates a filter initialized at
    /// `(offset, 0)` with initial variances `(offset_variance, rate_variance)`.
    #[must_use]
    pub fn new(
        walk: f64,
        noise: f64,
        offset: f64,
        offset_variance: f64,
        rate_variance: f64,
    ) -> OffsetKalman {
        OffsetKalman {
            walk,
            noise,
            offset,
            rate: 0.0,
            covariance: [offset_variance, 0.0, rate_variance],
        }
    }

    /// `[ORACLE / CENTRALIZED BENCHMARK]` Advances the filter state and
    /// covariance forward by `dt` seconds.
    pub fn predict(&mut self, dt: f64) {
        let [pxx, pxr, prr] = self.covariance;
        self.offset += self.rate * dt;
        self.covariance = [
            pxx + 2.0 * pxr * dt + prr * dt * dt + self.walk * dt.powi(3) / 3.0,
            pxr + prr * dt + self.walk * dt * dt / 2.0,
            prr + self.walk * dt,
        ];
    }

    /// `[ORACLE / CENTRALIZED BENCHMARK]` Incorporates a scalar offset
    /// measurement at the current time.
    pub fn update(&mut self, measured: f64) {
        let [pxx, pxr, prr] = self.covariance;
        let innovation = measured - self.offset;
        let spread = pxx + self.noise;
        let (gain_offset, gain_rate) = (pxx / spread, pxr / spread);
        self.offset += gain_offset * innovation;
        self.rate += gain_rate * innovation;
        self.covariance = [
            pxx - gain_offset * pxx,
            pxr - gain_offset * pxr,
            prr - gain_rate * pxr,
        ];
    }

    /// `[ORACLE / CENTRALIZED BENCHMARK]` Returns the estimated offset at the
    /// current time.
    #[must_use]
    pub fn offset(&self) -> f64 {
        self.offset
    }

    /// `[ORACLE / CENTRALIZED BENCHMARK]` Returns the estimated fractional rate.
    #[must_use]
    pub fn rate(&self) -> f64 {
        self.rate
    }
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Control law of
/// `Unisono.Model.Regulation.law` with dimensionless gain `g` in `(0, 1)`.
#[must_use]
pub fn law(g: f64, distance: f64, pace: f64) -> f64 {
    g * g / (2.0 - g) * distance - g * pace
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Effective quadratic position weight of a
/// decentralized star receiver with `receivers` speakers and weights
/// `(c_sync, c_track)` under uncorrelated cross-receiver errors:
/// `((R - 1) / R) * c_sync + c_track`.
#[must_use]
pub fn decentralized_star_weight(receivers: usize, c_sync: f64, c_track: f64) -> f64 {
    let count = as_float(receivers.max(1));
    ((count - 1.0) / count) * c_sync + c_track
}

/// `[ORACLE / MODEL BENCHMARK]` Per-cycle `Regulation.law` gain `g` in `(0, 1)`
/// minimizing the single-mode `multiCycleCost` quadratic objective for
/// position weight `c > 0`, inverting `g^4 / ((2 - g)^2 * (1 - g)) = c` by
/// bisection.
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

/// `[ORACLE / CENTRALIZED BENCHMARK]` Dimensionless per-cycle quadratic
/// position weight `(c_pos / c_rough) * cycle^4` converting continuous-time
/// objective weights `(c_pos, c_rough)` to the discrete cycle model with cycle
/// duration `cycle` seconds.
#[must_use]
pub fn cycle_position_weight(c_pos: f64, c_rough: f64, cycle: f64) -> f64 {
    if c_rough <= 0.0 || cycle <= 0.0 {
        return 0.0;
    }
    (c_pos / c_rough) * cycle.powi(4)
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Continuous-time
/// `[phase, -frequency * cycle]` innovation covariance matrix over one control
/// cycle of length `cycle` seconds for `FrequencyNoise`.
///
/// Because the pace state `v` tracks `read - expected_advance`, a positive
/// frequency increment `b` enters as `xi_2 = -b * cycle`, giving negative
/// cross-covariance `-(q_2 * cycle^2 / 2) * cycle`.
#[must_use]
pub fn cycle_clock_innovation_cov(noise: FrequencyNoise, cycle: f64) -> [[f64; 2]; 2] {
    let q0 = noise.white_variance_rate();
    let q2 = noise.walk_variance_rate();
    let c00 = q0 * cycle + q2 * cycle.powi(3) / 3.0;
    let c01 = -(q2 * cycle * cycle / 2.0) * cycle;
    let c11 = (q2 * cycle) * cycle * cycle;
    [[c00, c01], [c01, c11]]
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Exact continuous-time integrated
/// Brownian-motion process covariance `Q(dt)` for `(phase, frequency)` over
/// interval `dt >= 0` seconds.
#[must_use]
pub fn process_covariance(noise: FrequencyNoise, dt: f64) -> [[f64; 2]; 2] {
    let q0 = noise.white_variance_rate();
    let q2 = noise.walk_variance_rate();
    [
        [q0 * dt + q2 * dt * dt * dt / 3.0, q2 * dt * dt / 2.0],
        [q2 * dt * dt / 2.0, q2 * dt],
    ]
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Steady-state two-state Kalman gain
/// `[K_0, K_1]` for phase measurements of variance `meas_var` taken every
/// `meas_interval` seconds on a clock pair with combined noise `total_noise`.
#[must_use]
pub fn steady_state_kalman_gain(
    total_noise: FrequencyNoise,
    meas_interval: f64,
    meas_var: f64,
) -> [f64; 2] {
    let q = process_covariance(total_noise, meas_interval);
    let mut p00 = meas_var.max(1e-18);
    let mut p01 = 0.0_f64;
    let mut p11 = 1e-10_f64;
    for _ in 0..4_000 {
        let pred_00 =
            p00 + 2.0 * meas_interval * p01 + meas_interval * meas_interval * p11 + q[0][0];
        let pred_01 = p01 + meas_interval * p11 + q[0][1];
        let pred_11 = p11 + q[1][1];
        let s = (pred_00 + meas_var).max(1e-30);
        let k0 = pred_00 / s;
        let k1 = pred_01 / s;
        let np00 = (1.0 - k0) * (1.0 - k0) * pred_00 + k0 * k0 * meas_var;
        let np01 = (1.0 - k0) * (pred_01 - k1 * pred_00) + k0 * k1 * meas_var;
        let np11 = pred_11 - k1 * pred_01;
        let diff = (np00 - p00).abs() + (np01 - p01).abs() + (np11 - p11).abs();
        p00 = np00.max(0.0);
        p01 = np01;
        p11 = np11.max(0.0);
        if diff < 1e-28 * (p00 + p11 + 1e-30) {
            break;
        }
    }
    let pred_00 = p00 + 2.0 * meas_interval * p01 + meas_interval * meas_interval * p11 + q[0][0];
    let pred_01 = p01 + meas_interval * p11 + q[0][1];
    let s = (pred_00 + meas_var).max(1e-30);
    [pred_00 / s, pred_01 / s]
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Steady-state per-cycle quadratic cost
/// `E[c_pos * E_k^2 + w_k^2]` of applying `Regulation.law` with gain `gain` in
/// `(0, 1)` to a scalar mode driven by zero-mean i.i.d. innovations of
/// covariance `sigma`, computed by solving the exact `2 x 2` discrete Lyapunov
/// equation `P = A(g) P A(g)^T + sigma`.
#[must_use]
pub fn mode_lyapunov_cost(gain: f64, c_pos: f64, sigma: [[f64; 2]; 2]) -> f64 {
    let ke = gain * gain / (2.0 - gain);
    let a00 = 1.0 - ke;
    let a01 = -(1.0 - gain);
    let a10 = ke;
    let a11 = 1.0 - gain;

    let mat = vec![
        vec![1.0 - a00 * a00, -2.0 * a00 * a01, -a01 * a01],
        vec![-a00 * a10, 1.0 - (a00 * a11 + a01 * a10), -a01 * a11],
        vec![-a10 * a10, -2.0 * a10 * a11, 1.0 - a11 * a11],
    ];
    let rhs = vec![sigma[0][0], sigma[0][1], sigma[1][1]];
    let sol = solve_linear_system(mat, rhs);
    let (p00, p01, p11) = (sol[0], sol[1], sol[2]);
    (c_pos + ke * ke) * p00 - 2.0 * ke * gain * p01 + gain * gain * p11
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Steady-state per-cycle cost of a shared
/// scalar `Regulation.law` gain across `receivers` symmetric star speakers
/// under common sender innovation covariance `sigma_sender` and independent
/// per-receiver innovation covariance `sigma_receiver`.
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

/// `[ORACLE / MODEL BENCHMARK]` Numerical golden-section search over scalar
/// `Regulation.law` gains `g` in `(0, 1)` minimizing [`star_lyapunov_cost`]
/// in the per-cycle quadratic model.
#[must_use]
pub fn minimizing_shared_star_gain(
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

/// Solves the `4 x 4` discrete Lyapunov equation `P = A P A^T + Q` for
/// symmetric `P`.
fn solve_lyapunov_4x4(a: [[f64; 4]; 4], q: [[f64; 4]; 4]) -> [[f64; 4]; 4] {
    let pairs: [(usize, usize); 10] = [
        (0, 0),
        (0, 1),
        (0, 2),
        (0, 3),
        (1, 1),
        (1, 2),
        (1, 3),
        (2, 2),
        (2, 3),
        (3, 3),
    ];
    let idx = |r: usize, c: usize| -> usize {
        let (lo, hi) = if r <= c { (r, c) } else { (c, r) };
        match (lo, hi) {
            (0, 0) => 0,
            (0, 1) => 1,
            (0, 2) => 2,
            (0, 3) => 3,
            (1, 1) => 4,
            (1, 2) => 5,
            (1, 3) => 6,
            (2, 2) => 7,
            (2, 3) => 8,
            _ => 9,
        }
    };
    let mut mat = vec![vec![0.0_f64; 10]; 10];
    let mut rhs = vec![0.0_f64; 10];
    for (row, &(i, j)) in pairs.iter().enumerate() {
        mat[row][row] = 1.0;
        rhs[row] = q[i][j];
        for p in 0..4 {
            for r in 0..4 {
                mat[row][idx(p, r)] -= a[i][p] * a[j][r];
            }
        }
    }
    let sol = solve_linear_system(mat, rhs);
    let mut out = [[0.0_f64; 4]; 4];
    for (k, &(i, j)) in pairs.iter().enumerate() {
        out[i][j] = sol[k];
        out[j][i] = sol[k];
    }
    out
}

fn mat2_mul(a: [[f64; 2]; 2], b: [[f64; 2]; 2]) -> [[f64; 2]; 2] {
    [
        [
            a[0][0] * b[0][0] + a[0][1] * b[1][0],
            a[0][0] * b[0][1] + a[0][1] * b[1][1],
        ],
        [
            a[1][0] * b[0][0] + a[1][1] * b[1][0],
            a[1][0] * b[0][1] + a[1][1] * b[1][1],
        ],
    ]
}

fn mat2_pow(mut base: [[f64; 2]; 2], mut exp: usize) -> [[f64; 2]; 2] {
    let mut acc = [[1.0, 0.0], [0.0, 1.0]];
    while exp > 0 {
        if exp & 1 == 1 {
            acc = mat2_mul(acc, base);
        }
        base = mat2_mul(base, base);
        exp >>= 1;
    }
    acc
}

fn filtered_mode_lyapunov_cost(
    gain: f64,
    c_pos: f64,
    mode_noise: FrequencyNoise,
    mode_meas_var: f64,
    k_gain: [f64; 2],
    cycle: f64,
    meas_stride: usize,
) -> f64 {
    let m = meas_stride.max(1);
    let tm = as_float(m) * cycle;
    let ke = gain * gain / (2.0 - gain);
    let a_reg = [[1.0 - ke, -(1.0 - gain)], [ke, 1.0 - gain]];
    let a_m = mat2_pow(a_reg, m);
    let (k0, k1) = (k_gain[0], k_gain[1]);
    let (b0, b1) = (k0, -k1 * cycle);

    let a_sys = [
        [1.0 - k0, (1.0 - k0) * tm, 0.0, 0.0],
        [-k1, 1.0 - k1 * tm, 0.0, 0.0],
        [b0, b0 * tm, a_m[0][0], a_m[0][1]],
        [b1, b1 * tm, a_m[1][0], a_m[1][1]],
    ];
    let gw = [[1.0 - k0, 0.0], [-k1, 1.0], [b0, 0.0], [b1, 0.0]];
    let g_eta = [-k0, -k1, b0, b1];
    let q_tm = process_covariance(mode_noise, tm);
    let mut q_sys = [[0.0_f64; 4]; 4];
    for i in 0..4 {
        for j in 0..4 {
            let mut val = mode_meas_var * g_eta[i] * g_eta[j];
            for r in 0..2 {
                for c in 0..2 {
                    val += gw[i][r] * q_tm[r][c] * gw[j][c];
                }
            }
            q_sys[i][j] = val;
        }
    }
    let sigma = solve_lyapunov_4x4(a_sys, q_sys);

    let mut total = 0.0;
    let mut a_s = [[1.0, 0.0], [0.0, 1.0]];
    for s in 0..m {
        let tau = as_float(s) * cycle;
        let q_tau = process_covariance(mode_noise, tau);
        let c_vec = [1.0, tau, a_s[0][0], a_s[0][1]];
        let d_vec = [
            0.0,
            0.0,
            ke * a_s[0][0] - gain * a_s[1][0],
            ke * a_s[0][1] - gain * a_s[1][1],
        ];
        let mut e_sq = q_tau[0][0];
        let mut u_sq = 0.0;
        for i in 0..4 {
            for j in 0..4 {
                e_sq += c_vec[i] * sigma[i][j] * c_vec[j];
                u_sq += d_vec[i] * sigma[i][j] * d_vec[j];
            }
        }
        total += c_pos * e_sq + u_sq;
        a_s = mat2_mul(a_reg, a_s);
    }
    total / as_float(m)
}

/// `[ORACLE / MODEL BENCHMARK]` Configuration for the coupled Kalman-filter
/// plus `Regulation.law` star Lyapunov model
/// ([`filtered_star_lyapunov_cost`], [`minimizing_filtered_star_gain`]).
///
/// Evaluates one specific decentralized star design (steady-state 2-state
/// Kalman filter followed by `Regulation.law(gain)`) with known true noise
/// parameters; it is a model-specific reference, not a centralized lower bound.
#[derive(Clone, Copy, Debug)]
pub struct FilteredStarLyapunov {
    /// Number of star receivers `R >= 1`.
    pub receivers: usize,
    /// Per-cycle synchronization weight `c_sync`.
    pub c_sync: f64,
    /// Per-cycle tracking weight `c_track`.
    pub c_track: f64,
    /// Sender oscillator noise.
    pub sender_noise: FrequencyNoise,
    /// Per-receiver oscillator noise (identical across receivers).
    pub receiver_noise: FrequencyNoise,
    /// Phase measurement variance on each receiver's star link, in `s^2`.
    pub meas_var: f64,
    /// Control cycle duration `dt`, in seconds.
    pub cycle: f64,
    /// Number of control cycles per Kalman measurement update (`>= 1`).
    pub meas_stride: usize,
}

/// `[ORACLE / MODEL BENCHMARK]` Stationary per-cycle quadratic cost
/// `E[c_sync Var(e) + c_track mean(e^2) + mean(du^2)]` for one specific
/// decentralized star architecture (`R` symmetric receivers running a
/// steady-state 2-state Kalman filter followed by `Regulation.law(gain)` on
/// every cycle) given known true noise parameters.
#[must_use]
pub fn filtered_star_lyapunov_cost(cfg: FilteredStarLyapunov, gain: f64) -> f64 {
    let r = as_float(cfg.receivers.max(1));
    let tm = as_float(cfg.meas_stride.max(1)) * cfg.cycle;
    let total_noise = cfg.sender_noise.combine(cfg.receiver_noise);
    let k_gain = steady_state_kalman_gain(total_noise, tm, cfg.meas_var);
    let w_priv = ((r - 1.0) / r) * cfg.c_sync + cfg.c_track;
    let j_com = filtered_mode_lyapunov_cost(
        gain,
        cfg.c_track,
        cfg.sender_noise,
        0.0,
        k_gain,
        cfg.cycle,
        cfg.meas_stride,
    );
    let j_priv = filtered_mode_lyapunov_cost(
        gain,
        w_priv,
        cfg.receiver_noise,
        cfg.meas_var,
        k_gain,
        cfg.cycle,
        cfg.meas_stride,
    );
    j_com + j_priv
}

/// `[ORACLE / MODEL BENCHMARK]` Numerical golden-section search in log-gain
/// space for the scalar `Regulation.law` gain `g` in `(0, 1)` minimizing
/// [`filtered_star_lyapunov_cost`] for one specific decentralized filter +
/// regulator design with known true noise parameters.
#[must_use]
pub fn minimizing_filtered_star_gain(cfg: FilteredStarLyapunov) -> f64 {
    let phi = 0.5 * (5.0_f64.sqrt() - 1.0);
    let mut lo = (1e-5_f64).ln();
    let mut hi = (0.99_f64).ln();
    let mut x1 = hi - phi * (hi - lo);
    let mut x2 = lo + phi * (hi - lo);
    let mut f1 = filtered_star_lyapunov_cost(cfg, x1.exp());
    let mut f2 = filtered_star_lyapunov_cost(cfg, x2.exp());
    for _ in 0..90 {
        if f1 < f2 {
            hi = x2;
            x2 = x1;
            f2 = f1;
            x1 = hi - phi * (hi - lo);
            f1 = filtered_star_lyapunov_cost(cfg, x1.exp());
        } else {
            lo = x1;
            x1 = x2;
            f1 = f2;
            x2 = lo + phi * (hi - lo);
            f2 = filtered_star_lyapunov_cost(cfg, x2.exp());
        }
    }
    f64::midpoint(lo, hi).exp()
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Variance of the zero-delay
/// precision-weighted schedule residual `y_r - y_bar`, where
/// `y_bar = sum_j w_j y_j / sum_j w_j`, `w_j = 1 / sigma_j^2`, and
/// `bc_var = 1 / sum_j w_j`: equals `(rx_var - bc_var).max(1e-18)`.
#[must_use]
pub fn residual_measurement_variance(rx_var: f64, bc_var: f64) -> f64 {
    (rx_var - bc_var).max(1e-18)
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Directed weighted measurement edge
/// `(src -> dst)` observing `phase(dst) - phase(src)` with noise variance
/// `variance` and optional static one-way asymmetry bias `bias`.
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

/// Builds the reduced `(nodes - 1) x (nodes - 1)` weighted graph Laplacian
/// with host `0` grounded at zero.
fn build_reduced_laplacian(nodes: usize, edges: &[GraphEdge]) -> Vec<Vec<f64>> {
    let dim = nodes - 1;
    let mut laplacian = vec![vec![0.0_f64; dim]; dim];
    for edge in edges {
        let weight = 1.0 / edge.variance.max(1e-18);
        let src = edge.src;
        let dst = edge.dst;
        if src > 0 && src < nodes {
            laplacian[src - 1][src - 1] += weight;
        }
        if dst > 0 && dst < nodes {
            laplacian[dst - 1][dst - 1] += weight;
        }
        if src > 0 && dst > 0 && src < nodes && dst < nodes {
            laplacian[src - 1][dst - 1] -= weight;
            laplacian[dst - 1][src - 1] -= weight;
        }
    }
    laplacian
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

/// Private Graph-Laplacian BLUE solve used solely to compute the analytical
/// deterministic asymmetry bias [`blue_pair_bias`].
fn solve_graph_blue_internal(nodes: usize, edges: &[GraphEdge], obs: &[f64]) -> Vec<f64> {
    if nodes <= 1 {
        return vec![0.0; nodes];
    }
    let laplacian = build_reduced_laplacian(nodes, edges);
    let mut rhs = vec![0.0_f64; nodes - 1];
    for (edge, &meas) in edges.iter().zip(obs) {
        let weight = 1.0 / edge.variance.max(1e-18);
        if edge.src > 0 && edge.src < nodes {
            rhs[edge.src - 1] -= weight * meas;
        }
        if edge.dst > 0 && edge.dst < nodes {
            rhs[edge.dst - 1] += weight * meas;
        }
    }
    let sol = solve_linear_system(laplacian, rhs);
    let mut phi = Vec::with_capacity(nodes);
    phi.push(0.0);
    phi.extend(sol);
    phi
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Exact effective resistance (Thomson
/// minimum unbiased linear estimator variance for `phi[dst_node] - phi[src_node]`)
/// between `src_node` and `dst_node` on `edges`.
#[must_use]
pub fn effective_resistance(
    nodes: usize,
    edges: &[GraphEdge],
    src_node: usize,
    dst_node: usize,
) -> f64 {
    if nodes <= 1 || src_node == dst_node || src_node >= nodes || dst_node >= nodes {
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

/// `[ORACLE / CENTRALIZED BENCHMARK]` Exact variance of the BLUE common-mode
/// (receiver-mean) offset estimate `mean_r(-phi_hat[r])`:
/// `(1 / R^2) * 1^T L_red^{-1} 1`.
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

/// `[ORACLE / CENTRALIZED BENCHMARK]` Exact per-receiver variances of the BLUE
/// differential offset estimates `(-phi_hat[r]) - mean_s(-phi_hat[s])`:
/// `(e_r - (1 / R) 1)^T L_red^{-1} (e_r - (1 / R) 1)`.
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

/// `[ORACLE / CENTRALIZED BENCHMARK]` Exact deterministic bias of the
/// Graph-Laplacian BLUE for `phi[dst_node] - phi[src_node]` induced by the
/// static edge biases `edge.bias`.
#[must_use]
pub fn blue_pair_bias(nodes: usize, edges: &[GraphEdge], src_node: usize, dst_node: usize) -> f64 {
    if nodes <= 1 || src_node == dst_node || src_node >= nodes || dst_node >= nodes {
        return 0.0;
    }
    let biases: Vec<f64> = edges.iter().map(|e| e.bias).collect();
    let phi = solve_graph_blue_internal(nodes, edges, &biases);
    phi[dst_node] - phi[src_node]
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Event-driven block-request pause
/// simulator for pure exponential link pauses (zero drops, zero background
/// queueing jitter), returning `(missed_fraction, discontinuity_rate,
/// discontinuity_count)`.
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
    if pause_rate <= 0.0 || pause_length <= 0.0 || duration <= 0.0 || cycle <= 0.0 {
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
        let cutoff = paused_until - effective_margin;
        if cutoff > t_pause {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let k_start = (t_pause / cycle).ceil().max(0.0) as u64;
            let end_time = cutoff.min(duration);
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let k_end = if end_time > 0.0 {
                ((end_time / cycle) - 1e-12).floor().max(0.0) as u64
            } else {
                0
            };
            #[allow(clippy::cast_precision_loss)]
            let start_time = k_start as f64 * cycle;
            if k_start <= k_end && start_time < cutoff {
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

/// `[ORACLE / MODEL BENCHMARK]` Closed-form minimizer of the continuous-time
/// exponential-pause linear buffer cost `J_buf` (latency, missed audio, and
/// discontinuity rate over `m >= 0`) for Poisson exponential pauses of rate
/// `rate` and mean duration `mean`. Returns `None` when `w_lat <= 0.0`.
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

/// `[ORACLE / MODEL BENCHMARK]` Closed-form minimizer of `J_buf` when
/// discontinuities are unpriced (`w_click = 0`).
#[must_use]
pub fn hold_margin(rate: f64, mean: f64, price_ratio: f64) -> Option<f64> {
    hold_margin_with_clicks(rate, mean, price_ratio, 1.0, 0.0)
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Expected fraction of missed playback
/// under exponential pauses (Campbell's formula):
/// `rate * mean * exp(-margin / mean)`.
#[must_use]
pub fn campbell_fraction(rate: f64, mean: f64, margin: f64) -> f64 {
    if rate <= 0.0 || mean <= 0.0 {
        return 0.0;
    }
    rate * mean * (-margin / mean).exp()
}

/// `[ORACLE / CENTRALIZED BENCHMARK]` Expected discontinuity (click) rate per
/// second under exponential pauses: `rate * exp(-margin / mean)`.
#[must_use]
pub fn click_rate(rate: f64, mean: f64, margin: f64) -> f64 {
    if rate <= 0.0 || mean <= 0.0 {
        return 0.0;
    }
    rate * (-margin / mean).exp()
}

#[cfg(test)]
mod tests {
    use std::f64::consts::PI;

    use super::{
        FilteredStarLyapunov, GraphEdge, OffsetKalman, blue_common_variance, blue_diff_variances,
        blue_pair_bias, campbell_fraction, click_rate, cycle_clock_innovation_cov,
        cycle_position_weight, decentralized_star_weight, effective_resistance,
        filtered_star_lyapunov_cost, gain_for_weight, hold_margin, hold_margin_with_clicks, law,
        minimizing_filtered_star_gain, minimizing_shared_star_gain, mode_lyapunov_cost,
        process_covariance, pure_pause_block_metrics, residual_measurement_variance,
        star_lyapunov_cost, steady_state_kalman_gain,
    };
    use crate::clock::FrequencyNoise;
    use crate::random::Generator;

    #[test]
    fn offset_kalman_finds_a_line_through_noisy_measurements() {
        let mut filter = OffsetKalman::new(0.0, 1.0, 0.0, 1e6, 1e6);
        let mut generator = Generator::new(11);
        let (mut truth, rate, dt) = (5.0, 0.3, 0.1);
        for _ in 0..10_000 {
            truth += rate * dt;
            filter.predict(dt);
            filter.update(truth + generator.normal());
        }
        assert!(
            (filter.offset() - truth).abs() < 0.1,
            "offset error {}",
            filter.offset() - truth
        );
        assert!(
            (filter.rate() - rate).abs() < 1e-3,
            "rate error {}",
            filter.rate() - rate
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn lyapunov_and_minimizing_star_gains_match_analytical_benchmarks() {
        assert!((law(0.5, 1.0, 0.0) - (0.25 / 1.5)).abs() < 1e-12);
        let c_pos = cycle_position_weight(1e6, 1.0, 0.01);
        assert!((c_pos - 1e-2).abs() < 1e-15);

        let unit_walk = FrequencyNoise {
            h0_white: 0.0,
            h1_flicker: 0.0,
            h2_walk: 1.0 / (2.0 * PI * PI),
        };
        let q = process_covariance(unit_walk, 1.0);
        assert!((q[0][0] - 1.0 / 3.0).abs() < 1e-12);
        assert!((q[0][1] - 0.5).abs() < 1e-12);
        assert!((q[1][1] - 1.0).abs() < 1e-12);

        let cov = cycle_clock_innovation_cov(unit_walk, 1.0);
        assert!((cov[0][1] + 0.5).abs() < 1e-12);
        let lyap = mode_lyapunov_cost(0.3, 1.0, cov);
        assert!((lyap - 23.38).abs() < 0.25, "lyap={lyap}");

        let receivers = 4;
        let c_sync = 1.0e-5;
        let c_track = 1.0e-7;
        let dt = 0.01;
        let g_indep = gain_for_weight(decentralized_star_weight(receivers, c_sync, c_track));
        let g_track = gain_for_weight(c_track);
        let sigma_rx = cycle_clock_innovation_cov(FrequencyNoise::CONSUMER_QUARTZ, dt);
        let zero_cov = [[0.0, 0.0], [0.0, 0.0]];
        let g0 = minimizing_shared_star_gain(receivers, c_sync, c_track, zero_cov, sigma_rx);
        assert!((g0 - g_indep).abs() < 1e-4 * g_indep);

        let sigma_s = cycle_clock_innovation_cov(FrequencyNoise::WANDERING_QUARTZ, dt);
        let g_opt = minimizing_shared_star_gain(receivers, c_sync, c_track, sigma_s, sigma_rx);
        let j_opt = star_lyapunov_cost(receivers, c_sync, c_track, sigma_s, sigma_rx, g_opt);
        assert!(j_opt < star_lyapunov_cost(receivers, c_sync, c_track, sigma_s, sigma_rx, g_indep));
        // Finite-difference local minimality around `g_opt`.
        assert!(
            star_lyapunov_cost(receivers, c_sync, c_track, sigma_s, sigma_rx, g_opt * 0.9) > j_opt
        );
        assert!(
            star_lyapunov_cost(receivers, c_sync, c_track, sigma_s, sigma_rx, g_opt * 1.1) > j_opt
        );

        let total_noise = FrequencyNoise::WANDERING_QUARTZ.combine(FrequencyNoise::CONSUMER_QUARTZ);
        let meas_var = (10e-6_f64).powi(2);
        let k_ss = steady_state_kalman_gain(total_noise, 1.0, meas_var);
        assert!(k_ss[0] > 0.0 && k_ss[0] < 1.0 && k_ss[1] > 0.0);
        // Verify `k_ss` satisfies the steady-state 2x2 Lyapunov equation for the
        // posterior estimation error covariance `P = F_cl P F_cl^T + Q_cl` and
        // reproduces `k_ss = P_pred H^T / (P_pred[0][0] + R)`.
        let q1 = process_covariance(total_noise, 1.0);
        // Iterate posterior covariance to fixed point with fixed `k_ss` and verify
        // the minimizing gain for that covariance matches `k_ss`.
        let mut p = [[meas_var, 0.0], [0.0, 1e-12]];
        for _ in 0..2_000 {
            let p_pred_00 = p[0][0] + 2.0 * p[0][1] + p[1][1] + q1[0][0];
            let p_pred_01 = p[0][1] + p[1][1] + q1[0][1];
            let p_pred_11 = p[1][1] + q1[1][1];
            let np00 = (1.0 - k_ss[0]).powi(2) * p_pred_00 + k_ss[0].powi(2) * meas_var;
            let np01 =
                (1.0 - k_ss[0]) * (p_pred_01 - k_ss[1] * p_pred_00) + k_ss[0] * k_ss[1] * meas_var;
            let np11 =
                p_pred_11 - 2.0 * k_ss[1] * p_pred_01 + k_ss[1].powi(2) * (p_pred_00 + meas_var);
            p = [[np00, np01], [np01, np11]];
        }
        let pred_00 = p[0][0] + 2.0 * p[0][1] + p[1][1] + q1[0][0];
        let pred_01 = p[0][1] + p[1][1] + q1[0][1];
        let s_innov = pred_00 + meas_var;
        assert!((pred_00 / s_innov - k_ss[0]).abs() < 1e-12);
        assert!((pred_01 / s_innov - k_ss[1]).abs() < 1e-12);

        let cfg = FilteredStarLyapunov {
            receivers,
            c_sync,
            c_track,
            sender_noise: FrequencyNoise::WANDERING_QUARTZ,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            meas_var: (2.8e-6_f64).powi(2),
            cycle: dt,
            meas_stride: 100,
        };
        let g_filt = minimizing_filtered_star_gain(cfg);
        let j_filt = filtered_star_lyapunov_cost(cfg, g_filt);
        assert!(g_filt < g_track);
        assert!(j_filt < filtered_star_lyapunov_cost(cfg, g_track));
        // Finite-difference local minimality around `g_filt`.
        assert!(filtered_star_lyapunov_cost(cfg, g_filt * 0.9) > j_filt);
        assert!(filtered_star_lyapunov_cost(cfg, g_filt * 1.1) > j_filt);
        assert!(filtered_star_lyapunov_cost(cfg, g_filt * 0.99) > j_filt);
        assert!(filtered_star_lyapunov_cost(cfg, g_filt * 1.01) > j_filt);

        // Limiting case 1: for pure white FM (constant frequency, `walk = 0`),
        // noiseless stride-1 phase observation gives full state information, so
        // `filtered_star_lyapunov_cost` matches `star_lyapunov_cost` directly.
        let white_s = FrequencyNoise {
            h0_white: 1e-12,
            h1_flicker: 0.0,
            h2_walk: 0.0,
        };
        let white_r = FrequencyNoise {
            h0_white: 3e-13,
            h1_flicker: 0.0,
            h2_walk: 0.0,
        };
        let noiseless_white = FilteredStarLyapunov {
            receivers,
            c_sync,
            c_track,
            sender_noise: white_s,
            receiver_noise: white_r,
            meas_var: 1e-26,
            cycle: dt,
            meas_stride: 1,
        };
        let j_lim_white = filtered_star_lyapunov_cost(noiseless_white, 0.2);
        let j_direct_white = star_lyapunov_cost(
            receivers,
            c_sync,
            c_track,
            cycle_clock_innovation_cov(white_s, dt),
            cycle_clock_innovation_cov(white_r, dt),
            0.2,
        );
        assert!(
            (j_lim_white - j_direct_white).abs() < 1e-2 * j_direct_white,
            "pure white-FM noiseless stride-1 filtered cost ({j_lim_white}) should match direct Lyapunov cost ({j_direct_white})"
        );

        // Limiting case 2: with random-walk FM, phase-only observation cannot
        // observe instantaneous frequency directly, so even noiseless stride-1
        // filtered cost is strictly above full-state `star_lyapunov_cost`, and
        // cost increases monotonically with measurement variance and stride.
        let noiseless_rw = FilteredStarLyapunov {
            receivers,
            c_sync,
            c_track,
            sender_noise: FrequencyNoise::WANDERING_QUARTZ,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            meas_var: 1e-22,
            cycle: dt,
            meas_stride: 1,
        };
        let j_lim_rw = filtered_star_lyapunov_cost(noiseless_rw, 0.2);
        let j_direct_rw = star_lyapunov_cost(receivers, c_sync, c_track, sigma_s, sigma_rx, 0.2);
        let j_noisy_rw = filtered_star_lyapunov_cost(
            FilteredStarLyapunov {
                meas_var: (2.8e-6_f64).powi(2),
                ..noiseless_rw
            },
            0.2,
        );
        let j_strided_rw = filtered_star_lyapunov_cost(
            FilteredStarLyapunov {
                meas_var: (2.8e-6_f64).powi(2),
                meas_stride: 100,
                ..noiseless_rw
            },
            0.2,
        );
        assert!(j_lim_rw > j_direct_rw);
        assert!(j_noisy_rw > j_lim_rw);
        assert!(j_strided_rw > j_noisy_rw);

        let res_var = residual_measurement_variance(16e-12, 4e-12);
        assert!((res_var - 12e-12).abs() < 1e-24);
    }

    #[test]
    fn graph_blue_resistance_variances_and_asymmetry_bias_match_closed_forms() {
        let v = 1e-8;
        let mut k5 = Vec::new();
        for u in 0..5 {
            for w in (u + 1)..5 {
                k5.push(GraphEdge {
                    src: u,
                    dst: w,
                    variance: v,
                    bias: 0.0,
                });
            }
        }
        assert!((effective_resistance(5, &k5, 1, 2) - 2.0 * v / 5.0).abs() < 1e-20);
        assert!((blue_common_variance(5, &k5) - v / 4.0).abs() < 1e-20);
        for &dv in &blue_diff_variances(5, &k5) {
            assert!((dv - 3.0 * v / 20.0).abs() < 1e-20);
        }

        let vw = (150e-6_f64).powi(2);
        let vp = (5e-6_f64).powi(2);
        let tri = [
            GraphEdge {
                src: 0,
                dst: 1,
                variance: vw,
                bias: 750e-6,
            },
            GraphEdge {
                src: 0,
                dst: 2,
                variance: vw,
                bias: -750e-6,
            },
            GraphEdge {
                src: 1,
                dst: 2,
                variance: vp,
                bias: 0.0,
            },
        ];
        let expected_bias = 1_500e-6 * (vp / (2.0 * vw + vp));
        assert!((blue_pair_bias(3, &tri, 1, 2).abs() - expected_bias).abs() < 1e-12);
    }

    #[test]
    fn campbell_margin_and_pure_pause_metrics_agree() {
        assert!(hold_margin_with_clicks(0.05, 0.03, 0.0, 1.0, 0.0).is_none());
        let rate = 1.0 / 20.0;
        let mean = 30e-3;
        let m0 = hold_margin(rate, mean, 1e-3).expect("finite margin");
        let m1 = hold_margin_with_clicks(rate, mean, 1e-3, 1.0, 0.15).expect("finite margin");
        assert!(m1 > m0);

        let th_missed = campbell_fraction(rate, mean, m0);
        let th_clicks = click_rate(rate, mean, m0);
        let ratio = 0.01 / mean;
        let discrete_factor = (1.0 - (-ratio).exp()) / ratio;
        let (sim_missed, sim_clicks, events) =
            pure_pause_block_metrics(rate, mean, 0.01, 0.0, 1_000_000.0, m0, 11);
        assert!(events > 500);
        assert!((sim_missed - th_missed).abs() < 0.10 * th_missed);
        let expected_clicks = th_clicks * discrete_factor;
        assert!((sim_clicks - expected_clicks).abs() < 0.10 * expected_clicks);
    }
}
