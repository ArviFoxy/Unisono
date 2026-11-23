// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Fixed-point 2-state Joseph-form Kalman filter for relative clock offset and
//! fractional frequency drift.
//!
//! State anchoring: on the first valid observation (or after a clock step
//! exceeding `jump_ns`), `base_offset_ns` records the exact `i64` nanosecond
//! baseline offset. The filter tracks the small residual offset `theta_q16`
//! (in `Q16` nanoseconds) and relative fractional frequency `freq_q48` (in
//! `Q48` dimensionless units), preserving sub-nanosecond resolution even when
//! two hosts' monotonic clocks differ by decades.
//!
//! Unit-harmonized covariance representation (`i128` symmetric 2x2 matrix):
//! - `p00`: phase variance in `Q16 ns^2` (`1 ns^2 = 2^16`)
//! - `p01`: phase-frequency covariance in `Q48 ns` (`1 ns = 2^48`)
//! - `p11`: frequency variance in `Q80` dimensionless (`1 = 2^80`)
//!
//! Because adjacent scales step by exactly `2^32` per `1/ns`, prediction uses
//! exact integer shifts without dividing by `10^9`, and the stabilized Joseph
//! update preserves symmetry and non-negativity across the full dynamic range
//! from TCXO to wandering consumer quartz.

use crate::fixed::{div_floor_wide, root, saturate, saturating_mul_i128, scale_div_pow2};
use crate::relation::Line;

/// One second in nanoseconds.
const BILLION: i128 = 1_000_000_000;

/// `2^32` (unity in Q32).
const Q32_ONE: i128 = 4_294_967_296;

/// `2^48` (denominator of exported `Line` slopes so `freq_q48` exports with
/// zero slope quantization).
pub const LINE_RUN: i64 = 281_474_976_710_656;

/// Maximum prediction step in one call (`1000 s`), keeping all intermediate
/// products strictly within `i128`.
const MAX_DT_NS: i64 = 1_000_000_000_000;

/// Maximum residual phase variance `p00` in Q16 ns^2 (`(10 s)^2 * 2^16`),
/// well below `2^84`.
const MAX_P00: i128 = 6_553_600_000_000_000_000_000_000;

/// Maximum frequency variance `p11` in Q80 (`(10_000 ppm)^2 * 2^80`), well
/// below `2^68`.
const MAX_P11: i128 = 120_892_581_961_462_917_471;

/// Maximum magnitude of `p01` in Q48 ns (`sqrt(MAX_P00 * MAX_P11)`).
const MAX_P01: i128 = 28_147_497_671_065_600_000_000;

/// Maximum magnitude of Kalman frequency gain `k1` in Q64 (1/ns) (`2^48`),
/// ensuring `k1 * p00` and `k1 * innovation` never overflow `i128`.
const MAX_K1: i128 = 281_474_976_710_656;

/// Initial phase variance on anchor: `(10 ms)^2` in Q16 ns^2.
const INIT_P00: i128 = 6_553_600_000_000_000_000;

/// Initial frequency variance on anchor: `(200 ppm)^2` in Q80.
const INIT_P11: i128 = 48_357_032_784_585_168;

/// Maximum fractional frequency magnitude in Q48 (`5000 ppm`).
const MAX_FREQ_Q48: i64 = 1_407_374_883_553;

/// Default step threshold (`100 ms`) beyond which the filter re-anchors rather
/// than slewing across a clock reset.
pub const DEFAULT_JUMP_NS: i64 = 100_000_000;

/// IEEE Std 1139-2008 white-frequency (`q0 = h_0 / 2`) and random-walk
/// frequency (`q2 = 2 * pi^2 * h_{-2}`) process noise parameters for a pair of
/// clocks, in exact fixed-point units.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct NoisePrior {
    /// White-frequency phase variance rate `q0` in `Q16 ns^2 / s`.
    pub q0_q16_ns2_per_s: i128,
    /// Random-walk frequency variance rate `q2` in `Q80 / s`.
    pub q2_q80_per_s: i128,
}

impl NoisePrior {
    /// Single TCXO-grade oscillator (`h_0 = 2e-18 s`, `h_{-2} = 5e-20 Hz`).
    pub const TCXO: NoisePrior = NoisePrior {
        q0_q16_ns2_per_s: 65_536,
        q2_q80_per_s: 1_193_162,
    };

    /// Single consumer quartz oscillator (`h_0 = 2e-14 s`, `h_{-2} = 5e-16 Hz`).
    pub const CONSUMER_QUARTZ: NoisePrior = NoisePrior {
        q0_q16_ns2_per_s: 655_360_000,
        q2_q80_per_s: 11_931_619_590,
    };

    /// Single wandering consumer quartz oscillator (`100x` `h_{-2}`).
    pub const WANDERING_QUARTZ: NoisePrior = NoisePrior {
        q0_q16_ns2_per_s: 655_360_000,
        q2_q80_per_s: 1_193_161_958_986,
    };

    /// Sum of two independent oscillators' noise parameters.
    #[must_use]
    pub const fn combine(self, other: NoisePrior) -> NoisePrior {
        NoisePrior {
            q0_q16_ns2_per_s: self.q0_q16_ns2_per_s.saturating_add(other.q0_q16_ns2_per_s),
            q2_q80_per_s: self.q2_q80_per_s.saturating_add(other.q2_q80_per_s),
        }
    }

    /// Scales both noise rates by `num / den` (for example, `1 / R` for the
    /// common-mode average of `R` receivers).
    #[must_use]
    pub fn scale(self, num: i64, den: i64) -> NoisePrior {
        if num <= 0 || den <= 0 {
            return NoisePrior {
                q0_q16_ns2_per_s: 0,
                q2_q80_per_s: 0,
            };
        }
        let q0 = clamp_nonneg(self.q0_q16_ns2_per_s, MAX_P00);
        let q2 = clamp_nonneg(self.q2_q80_per_s, MAX_P11);
        NoisePrior {
            q0_q16_ns2_per_s: div_floor_wide(saturating_mul_i128(q0, num as i128), den as i128),
            q2_q80_per_s: div_floor_wide(saturating_mul_i128(q2, num as i128), den as i128),
        }
    }
}

/// Clamps `x` into `[0, hi]`.
fn clamp_nonneg(x: i128, hi: i128) -> i128 {
    if x < 0 {
        0
    } else if x > hi {
        hi
    } else {
        x
    }
}

/// Clamps `x` into `[-hi, hi]` for `hi >= 0`.
fn clamp_sym(x: i128, hi: i128) -> i128 {
    let lo = 0i128.wrapping_sub(hi);
    if x > hi {
        hi
    } else if x < lo {
        lo
    } else {
        x
    }
}

/// Clamps `x` into `[-hi, hi]` in `i64` for `hi >= 0`.
fn clamp_sym_i64(x: i64, hi: i64) -> i64 {
    let lo = 0i64.wrapping_sub(hi);
    if x > hi {
        hi
    } else if x < lo {
        lo
    } else {
        x
    }
}

/// Magnitude of `x` as non-negative `i128` (clamping `i128::MIN` to `i128::MAX`).
fn abs_i128(x: i128) -> i128 {
    if x == i128::MIN {
        i128::MAX
    } else if x < 0 {
        0i128.wrapping_sub(x)
    } else {
        x
    }
}

/// Computes `floor((a * b) / 2^shift)` safely for `shift <= 64` without
/// overflowing `i128` by splitting the wider operand when necessary.
fn mul_shr_safe(a: i128, b: i128, shift: u32) -> i128 {
    let shift = if shift > 64 { 64 } else { shift };
    if let Some(prod) = a.checked_mul(b) {
        return prod.wrapping_shr(shift);
    }
    // Split `a = hi * 2^shift + lo` when `a * b` would exceed `i128`.
    let hi = a.wrapping_shr(shift);
    let mask = if shift == 64 {
        18_446_744_073_709_551_615i128
    } else {
        1i128.wrapping_shl(shift).wrapping_sub(1)
    };
    let lo = a & mask;
    let t1 = saturating_mul_i128(hi, b);
    let t2 = if let Some(p) = lo.checked_mul(b) {
        p.wrapping_shr(shift)
    } else {
        let b_hi = b.wrapping_shr(shift);
        let b_lo = b & mask;
        let p1 = saturating_mul_i128(lo, b_hi);
        let p2 = saturating_mul_i128(lo, b_lo).wrapping_shr(shift);
        p1.saturating_add(p2)
    };
    t1.saturating_add(t2)
}

/// Enforces `p00 >= 0`, `p11 >= 0`, and `p01^2 <= p00 * p11` (up to fixed-point
/// precision) so the stored 2x2 covariance stays positive semidefinite.
fn enforce_psd(p00_in: i128, p01_in: i128, p11_in: i128) -> (i128, i128, i128) {
    let p00 = clamp_nonneg(p00_in, MAX_P00);
    let p11 = clamp_nonneg(p11_in, MAX_P11);
    let p01 = clamp_sym(p01_in, MAX_P01);
    if p00 == 0 || p11 == 0 {
        return (p00, 0, p11);
    }
    // Scale both diagonals down by 2^16 before multiplying so the product fits
    // easily inside `i128` (<= 2^(68 + 52) = 2^120), then multiply `root` back
    // by `2^16` to bound `|p01|`.
    let s0 = p00.wrapping_shr(16);
    let s1 = p11.wrapping_shr(16);
    let bound = if s0 > 0 && s1 > 0 {
        let prod = saturating_mul_i128(s0, s1);
        saturating_mul_i128(root(prod), 65_536)
    } else {
        // At least one diagonal is small (< 2^16): `p00 * p11` fits directly
        // when the other is <= 2^110, which always holds since MAX_P00 < 2^84.
        root(saturating_mul_i128(p00, p11))
    };
    (p00, clamp_sym(p01, bound), p11)
}

/// Fixed-point 2-state Joseph-form Kalman filter tracking relative clock offset
/// (`remote - local`) and relative fractional frequency drift.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct KalmanFilter {
    anchored: bool,
    base_offset_ns: i64,
    last_time_ns: i64,
    /// Residual phase offset relative to `base_offset_ns`, in Q16 ns.
    theta_q16: i64,
    /// Relative fractional frequency drift, in Q48.
    freq_q48: i64,
    /// Phase variance in Q16 ns^2 (`>= 0`).
    p00: i128,
    /// Phase-frequency covariance in Q48 ns.
    p01: i128,
    /// Frequency variance in Q80 (`>= 0`).
    p11: i128,
    /// Process noise prior.
    prior: NoisePrior,
    /// Step threshold in nanoseconds above which the filter re-anchors.
    jump_ns: i64,
}

impl KalmanFilter {
    /// Creates an unanchored filter with the given process noise prior and
    /// jump-reset threshold.
    #[must_use]
    pub fn new(prior: NoisePrior, jump_ns: i64) -> Self {
        KalmanFilter {
            anchored: false,
            base_offset_ns: 0,
            last_time_ns: 0,
            theta_q16: 0,
            freq_q48: 0,
            p00: INIT_P00,
            p01: 0,
            p11: INIT_P11,
            prior,
            jump_ns: if jump_ns < 0 { 0 } else { jump_ns },
        }
    }

    /// Resets the filter to unanchored while retaining `prior` and `jump_ns`.
    pub fn reset(&mut self) {
        self.anchored = false;
        self.base_offset_ns = 0;
        self.last_time_ns = 0;
        self.theta_q16 = 0;
        self.freq_q48 = 0;
        self.p00 = INIT_P00;
        self.p01 = 0;
        self.p11 = INIT_P11;
    }

    /// Updates the process noise prior without clearing state.
    pub fn set_prior(&mut self, prior: NoisePrior) {
        self.prior = prior;
    }

    /// Whether the filter has anchored on at least one observation.
    #[must_use]
    pub fn is_anchored(&self) -> bool {
        self.anchored
    }

    /// Local-clock timestamp of the stored posterior state, in nanoseconds.
    #[must_use]
    pub fn last_time_ns(&self) -> i64 {
        self.last_time_ns
    }

    /// Posterior fractional frequency drift in Q48 units.
    #[must_use]
    pub fn freq_q48(&self) -> i64 {
        self.freq_q48
    }

    /// Posterior phase variance in integer square nanoseconds (`>= 0`).
    #[must_use]
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    pub fn offset_variance_ns2(&self) -> u64 {
        let ns2 = clamp_nonneg(self.p00, MAX_P00).wrapping_shr(16);
        if ns2 > u64::MAX as i128 {
            u64::MAX
        } else {
            ns2 as u64
        }
    }

    /// Raw covariance entries `(p00_q16, p01_q48, p11_q80)` for diagnostics
    /// and proofs.
    #[must_use]
    pub fn covariance_raw(&self) -> (i128, i128, i128) {
        (self.p00, self.p01, self.p11)
    }

    /// Posterior frequency variance `p11` in Q80 dimensionless units.
    #[must_use]
    pub fn p11_q80(&self) -> i128 {
        self.p11
    }

    /// Posterior offset estimate at `last_time_ns`, in nanoseconds, without
    /// forward extrapolation.
    #[must_use]
    pub fn offset_ns(&self) -> Option<i64> {
        if !self.anchored {
            return None;
        }
        let whole_ns = div_floor_wide(self.theta_q16 as i128, 65_536);
        Some(saturate(
            (self.base_offset_ns as i128).saturating_add(whole_ns),
        ))
    }

    /// Shifts the filter's offset estimate cleanly by `delta_ns` without
    /// perturbing its frequency estimate or covariance (used for bumpless
    /// common/differential transfer when peer membership changes).
    pub fn shift_offset_ns(&mut self, delta_ns: i64) {
        if !self.anchored {
            return;
        }
        self.base_offset_ns = self.base_offset_ns.saturating_add(delta_ns);
    }

    /// Anchors the filter directly at `(time_ns, offset_ns)` with initial
    /// measurement variance `variance_ns2` and zero frequency estimate.
    fn anchor(&mut self, time_ns: i64, offset_ns: i64, variance_ns2: u64) {
        self.anchor_with_freq(time_ns, offset_ns, 0, variance_ns2);
    }

    /// Anchors the filter at `(time_ns, offset_ns)` while preserving a prior
    /// frequency estimate `freq_q48` (clamped to `±MAX_FREQ_Q48`).
    pub fn anchor_with_freq(
        &mut self,
        time_ns: i64,
        offset_ns: i64,
        freq_q48: i64,
        variance_ns2: u64,
    ) {
        let meas_q16 = clamp_nonneg((variance_ns2 as i128).wrapping_shl(16), MAX_P00);
        let init_p00 = if meas_q16 > 0 { meas_q16 } else { INIT_P00 };
        self.anchored = true;
        self.base_offset_ns = offset_ns;
        self.last_time_ns = time_ns;
        self.theta_q16 = 0;
        self.freq_q48 = clamp_sym_i64(freq_q48, MAX_FREQ_Q48);
        self.p00 = init_p00;
        self.p01 = 0;
        self.p11 = INIT_P11;
    }

    /// Recenters `base_offset_ns` whenever `|theta_q16|` grows past 1 second
    /// so `theta_q16` never approaches `i64` saturation on long runs.
    fn recenter(&mut self) {
        let whole_ns = self.theta_q16.wrapping_shr(16);
        let mag = if whole_ns == i64::MIN {
            i64::MAX
        } else if whole_ns < 0 {
            0i64.wrapping_sub(whole_ns)
        } else {
            whole_ns
        };
        if mag > 1_000_000_000 {
            self.base_offset_ns = self.base_offset_ns.saturating_add(whole_ns);
            self.theta_q16 = self.theta_q16.wrapping_sub(whole_ns.wrapping_shl(16));
        }
    }

    /// Advances the stored posterior forward by `dt_ns >= 0` using the exact
    /// integrated Brownian-motion covariance `Q(dt)`. For silences exceeding
    /// `MAX_DT_NS` (1000 s), advances `last_time_ns` and phase across the full
    /// `dt_ns` and saturates phase uncertainty to `MAX_P00` with zero
    /// phase-frequency correlation so the next measurement snaps cleanly.
    pub fn predict(&mut self, dt_ns: i64) {
        if !self.anchored || dt_ns <= 0 {
            return;
        }
        if dt_ns > MAX_DT_NS {
            let d_theta = mul_shr_safe(self.freq_q48 as i128, dt_ns as i128, 32);
            let d_whole = div_floor_wide(d_theta, 65_536);
            let d_frac = d_theta.wrapping_sub(saturating_mul_i128(d_whole, 65_536));
            self.base_offset_ns = saturate((self.base_offset_ns as i128).saturating_add(d_whole));
            self.theta_q16 = saturate((self.theta_q16 as i128).saturating_add(d_frac));
            self.last_time_ns = self.last_time_ns.saturating_add(dt_ns);
            let p11_floor = if self.p11 > INIT_P11 {
                self.p11
            } else {
                INIT_P11
            };
            let (fp00, fp01, fp11) = enforce_psd(MAX_P00, 0, p11_floor);
            self.p00 = fp00;
            self.p01 = fp01;
            self.p11 = fp11;
            self.recenter();
            return;
        }
        let dt128 = dt_ns as i128;
        // `Q48 * ns >> 32 = Q16 ns`.
        let d_theta = (self.freq_q48 as i128).wrapping_mul(dt128).wrapping_shr(32);
        self.theta_q16 = saturate((self.theta_q16 as i128).wrapping_add(d_theta));
        self.last_time_ns = self.last_time_ns.saturating_add(dt_ns);

        let (p00, p01, p11) = enforce_psd(self.p00, self.p01, self.p11);
        let q0_rate = clamp_nonneg(self.prior.q0_q16_ns2_per_s, MAX_P00);
        let q2_rate = clamp_nonneg(self.prior.q2_q80_per_s, MAX_P11);

        let q11 = div_floor_wide(saturating_mul_i128(q2_rate, dt128), BILLION);
        let q2_dt2 = mul_shr_safe(q11, dt128, 32);
        let q01 = q2_dt2.wrapping_shr(1);
        let q00_walk = div_floor_wide(mul_shr_safe(q2_dt2, dt128, 32), 3);
        let q00_white = div_floor_wide(saturating_mul_i128(q0_rate, dt128), BILLION);

        let p11_dt = mul_shr_safe(p11, dt128, 32);
        let p11_dt2 = mul_shr_safe(p11_dt, dt128, 32);
        let p01_dt = mul_shr_safe(p01, dt128, 32);

        let next_p00 = p00
            .saturating_add(saturating_mul_i128(p01_dt, 2))
            .saturating_add(p11_dt2)
            .saturating_add(q00_white)
            .saturating_add(q00_walk);
        let next_p01 = p01.saturating_add(p11_dt).saturating_add(q01);
        let next_p11 = p11.saturating_add(q11);

        let (fp00, fp01, fp11) = enforce_psd(next_p00, next_p01, next_p11);
        self.p00 = fp00;
        self.p01 = fp01;
        self.p11 = fp11;
        self.recenter();
    }

    /// Incorporates a measurement `offset_ns` stamped at `meas_time_ns` with
    /// variance `variance_ns2`. Returns `false` if `meas_time_ns` is older
    /// than `last_time_ns` (stale measurement ignored).
    pub fn update(&mut self, meas_time_ns: i64, offset_ns: i64, variance_ns2: u64) -> bool {
        let var_ns2 = if variance_ns2 == 0 { 1 } else { variance_ns2 };
        if !self.anchored {
            self.anchor(meas_time_ns, offset_ns, var_ns2);
            return true;
        }
        if meas_time_ns < self.last_time_ns {
            return false;
        }
        let dt = meas_time_ns.saturating_sub(self.last_time_ns);
        self.predict(dt);

        // Innovation in Q16 ns: `(offset_ns - base_offset_ns) * 2^16 - theta_q16`.
        let rel_ns = (offset_ns as i128).wrapping_sub(self.base_offset_ns as i128);
        let pred_ns = div_floor_wide(self.theta_q16 as i128, 65_536);
        let innov_whole = rel_ns.wrapping_sub(pred_ns);
        if self.jump_ns > 0 && abs_i128(innov_whole) > self.jump_ns as i128 {
            self.anchor(meas_time_ns, offset_ns, var_ns2);
            return true;
        }
        let innov_q16 = saturating_mul_i128(rel_ns, 65_536).saturating_sub(self.theta_q16 as i128);

        let (p00, p01, p11) = enforce_psd(self.p00, self.p01, self.p11);
        let meas_q16 = clamp_nonneg((var_ns2 as i128).wrapping_shl(16), MAX_P00);
        let meas_pos = if meas_q16 <= 0 { 1 } else { meas_q16 };
        let innov_var = p00.saturating_add(meas_pos);

        // Kalman gains: `k0` in Q32 (`0 <= k0 <= 2^32`), `k1` in Q64 (1/ns).
        let k0 = clamp_nonneg(scale_div_pow2(p00, 32, innov_var), Q32_ONE);
        let k1 = clamp_sym(scale_div_pow2(p01, 32, innov_var), MAX_K1);

        // State update: `k0` (Q32) * `innov_q16` >> 32 = Q16 ns;
        // `k1` (Q64/ns) * `innov_q16` >> 32 = Q48 dimensionless.
        let d_theta = mul_shr_safe(k0, innov_q16, 32);
        let d_freq = mul_shr_safe(k1, innov_q16, 32);
        self.theta_q16 = saturate((self.theta_q16 as i128).saturating_add(d_theta));
        self.freq_q48 = clamp_sym_i64(
            saturate((self.freq_q48 as i128).saturating_add(d_freq)),
            MAX_FREQ_Q48,
        );

        // Stabilized Joseph covariance update:
        // P+ = (I - K H) P (I - K H)^T + R K K^T.
        let one_m_k0 = Q32_ONE.wrapping_sub(k0);
        let a2 = mul_shr_safe(one_m_k0, one_m_k0, 32);
        let k02 = mul_shr_safe(k0, k0, 32);
        let next_p00 = mul_shr_safe(a2, p00, 32).saturating_add(mul_shr_safe(k02, meas_pos, 32));

        let k1_p00 = mul_shr_safe(k1, p00, 32);
        let k1_meas = mul_shr_safe(k1, meas_pos, 32);
        let next_p01 = mul_shr_safe(one_m_k0, p01.saturating_sub(k1_p00), 32)
            .saturating_add(mul_shr_safe(k0, k1_meas, 32));

        let k1_p01 = mul_shr_safe(k1, p01, 32);
        let k1sq_p00 = mul_shr_safe(k1, k1_p00, 32);
        let k1sq_meas = mul_shr_safe(k1, k1_meas, 32);
        let next_p11 = p11
            .saturating_sub(saturating_mul_i128(k1_p01, 2))
            .saturating_add(k1sq_p00)
            .saturating_add(k1sq_meas);

        let (fp00, fp01, fp11) = enforce_psd(next_p00, next_p01, next_p11);
        self.p00 = fp00;
        self.p01 = fp01;
        self.p11 = fp11;
        self.recenter();
        true
    }

    /// Read-only predicted offset (`remote - local`) at `time_ns` in
    /// nanoseconds, without mutating the stored posterior.
    #[must_use]
    pub fn predict_offset_ns(&self, time_ns: i64) -> Option<i64> {
        if !self.anchored {
            return None;
        }
        let dt = (time_ns as i128).wrapping_sub(self.last_time_ns as i128);
        let dt_clamped = clamp_sym(dt, MAX_DT_NS as i128);
        let d_theta = mul_shr_safe(self.freq_q48 as i128, dt_clamped, 32);
        let total_q16 = (self.theta_q16 as i128).saturating_add(d_theta);
        let total_ns =
            (self.base_offset_ns as i128).saturating_add(div_floor_wide(total_q16, 65_536));
        Some(saturate(total_ns))
    }

    /// Exports the current posterior as an exact integer [`Line`] over the
    /// local clock (`line.eval(local_ns)` estimates `remote_clock - local_clock`).
    #[must_use]
    pub fn to_line(&self) -> Option<Line> {
        if !self.anchored {
            return None;
        }
        let whole_ns = div_floor_wide(self.theta_q16 as i128, 65_536);
        let value = saturate((self.base_offset_ns as i128).saturating_add(whole_ns));
        Some(Line {
            time: self.last_time_ns,
            value,
            rise: self.freq_q48,
            run: LINE_RUN,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{DEFAULT_JUMP_NS, KalmanFilter, NoisePrior};

    #[test]
    fn tracks_constant_skew_and_is_shift_invariant_over_huge_offsets() {
        let prior = NoisePrior::CONSUMER_QUARTZ.combine(NoisePrior::CONSUMER_QUARTZ);
        let mut f_zero = KalmanFilter::new(prior, DEFAULT_JUMP_NS);
        let mut f_shifted = KalmanFilter::new(prior, DEFAULT_JUMP_NS);
        // 50-year baseline shift (approx 1.57e18 ns).
        let big_shift = 1_576_800_000_000_000_000i64;
        // True frequency skew: +25 ppm (25_000 ns / s).
        for step in 0..40i64 {
            let t = step * 1_000_000_000;
            let off = step * 25_000;
            assert!(f_zero.update(t, off, 100_000_000));
            assert!(f_shifted.update(t, off.saturating_add(big_shift), 100_000_000));
        }
        // Shift invariance: frequency and covariance match identically.
        assert_eq!(f_zero.freq_q48(), f_shifted.freq_q48());
        assert_eq!(f_zero.covariance_raw(), f_shifted.covariance_raw());

        // Predict 5 seconds ahead at t = 44 s -> true offset is 44 * 25_000 = 1_100_000 ns.
        let p0 = f_zero.predict_offset_ns(44_000_000_000).expect("anchored");
        let ps = f_shifted
            .predict_offset_ns(44_000_000_000)
            .expect("anchored");
        assert!((p0 - 1_100_000).abs() < 200, "p0={p0}");
        assert_eq!(ps - p0, big_shift);

        let line = f_zero.to_line().expect("line");
        assert!((line.eval(44_000_000_000) - p0).abs() <= 1);
    }

    #[test]
    #[allow(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        clippy::similar_names
    )]
    fn matches_float_joseph_kalman_to_nanosecond_precision() {
        let prior = NoisePrior::CONSUMER_QUARTZ.combine(NoisePrior::CONSUMER_QUARTZ);
        let mut kf = KalmanFilter::new(prior, DEFAULT_JUMP_NS);
        let dt = 1.0_f64;
        let q0 = 2.0 * (2e-14_f64 / 2.0);
        let q2 = 2.0 * (2.0 * core::f64::consts::PI * core::f64::consts::PI * 5e-16_f64);
        let meas_var_ns2 = 25_000_000u64; // (5 us)^2
        let meas_var_s2 = (meas_var_ns2 as f64) * 1e-18;

        let mut x0 = 0.0_f64;
        let mut x1 = 0.0_f64;
        let mut p00 = meas_var_s2;
        let mut p01 = 0.0_f64;
        let mut p11 = (200e-6_f64).powi(2);

        let noises_ns = [
            0i64, 3_200, -4_100, 1_500, -2_800, 5_100, -900, 2_200, -3_700, 800, 1_900, -4_500,
            2_700, -1_200, 3_900, -2_100, 600, -1_800, 4_200, -500,
        ];
        for (i, &n_ns) in noises_ns.iter().enumerate() {
            let t_ns = i64::try_from(i).unwrap_or(0) * 1_000_000_000;
            let meas_ns = i64::try_from(i).unwrap_or(0) * 12_000 + n_ns;
            kf.update(t_ns, meas_ns, meas_var_ns2);
            if i == 0 {
                x0 = (meas_ns as f64) * 1e-9;
            } else {
                x0 += x1 * dt;
                let np00 = p00 + 2.0 * p01 * dt + p11 * dt * dt + q0 * dt + q2 * dt.powi(3) / 3.0;
                let np01 = p01 + p11 * dt + q2 * dt * dt / 2.0;
                let np11 = p11 + q2 * dt;
                let s = np00 + meas_var_s2;
                let k0 = np00 / s;
                let k1 = np01 / s;
                let innov = (meas_ns as f64) * 1e-9 - x0;
                x0 += k0 * innov;
                x1 += k1 * innov;
                let a = 1.0 - k0;
                p00 = a * a * np00 + k0 * k0 * meas_var_s2;
                p01 = a * (np01 - k1 * np00) + k0 * k1 * meas_var_s2;
                p11 = np11 - 2.0 * k1 * np01 + k1 * k1 * (np00 + meas_var_s2);
            }
        }
        let fixed_ns = kf.predict_offset_ns(19_000_000_000).expect("anchored");
        let float_ns = (x0 * 1e9).round() as i64;
        assert!(
            (fixed_ns - float_ns).abs() <= 5,
            "fixed={fixed_ns} float={float_ns}"
        );
        let (rp00, rp01, rp11) = kf.covariance_raw();
        assert!(rp00 >= 0 && rp11 >= 0);
        // PSD check: `(rp01 >> 16)^2 <= (rp00 >> 16) * (rp11 >> 16)` (up to scale).
        assert!(rp01.abs() < 1i128 << 80);
    }

    #[test]
    fn reanchors_on_clock_jump_and_ignores_stale_timestamps() {
        let prior = NoisePrior::TCXO.combine(NoisePrior::TCXO);
        let mut kf = KalmanFilter::new(prior, DEFAULT_JUMP_NS);
        assert!(kf.update(1_000_000_000, 500, 25_000_000));
        // Stale timestamp rejected.
        assert!(!kf.update(900_000_000, 999_999, 25_000_000));
        // 500 ms jump triggers clean re-anchor.
        assert!(kf.update(2_000_000_000, 500_000_500, 25_000_000));
        assert_eq!(kf.predict_offset_ns(2_000_000_000), Some(500_000_500));
    }

    #[test]
    fn predict_and_update_after_long_silence_exceeding_1000s_stays_accurate() {
        // Defect 1: after a silence > 1000 s (e.g. 25 min or 1 hr), `predict`
        // must advance `last_time_ns` across the full gap and snap cleanly on
        // the first fresh measurement instead of falling behind by >17 ms.
        let prior = NoisePrior::CONSUMER_QUARTZ.combine(NoisePrior::CONSUMER_QUARTZ);
        let mut kf = KalmanFilter::new(prior, DEFAULT_JUMP_NS);
        let skew_ns_per_s = 35_000i64; // +35 ppm
        let var = 25_000_000u64; // (5 us)^2
        for sec in 0..20i64 {
            let t = sec * 1_000_000_000;
            assert!(kf.update(t, sec * skew_ns_per_s, var));
        }

        // 25-minute silence (1500 s > MAX_DT_NS = 1000 s), with +2 ppm rate shift.
        let t_25m = 1_520 * 1_000_000_000i64;
        let true_25m = 20 * skew_ns_per_s + 1_500 * (skew_ns_per_s + 2_000);
        assert!(kf.update(t_25m, true_25m, var));
        assert_eq!(kf.last_time_ns(), t_25m);
        let est_25m = kf.predict_offset_ns(t_25m).expect("anchored");
        assert!(
            (est_25m - true_25m).abs() < 5_000,
            "25m silence first-estimate error too large: err={} ns",
            est_25m - true_25m
        );

        // 1-hour silence (3600 s > MAX_DT_NS) with +15 ppm rate shift (54 ms < 100 ms jump).
        let t_1h = t_25m + 3_600 * 1_000_000_000i64;
        let true_1h = true_25m + 3_600 * (skew_ns_per_s + 17_000);
        assert!(kf.update(t_1h, true_1h, var));
        assert_eq!(kf.last_time_ns(), t_1h);
        let est_1h = kf.predict_offset_ns(t_1h).expect("anchored");
        assert!(
            (est_1h - true_1h).abs() < 5_000,
            "1h silence first-estimate error too large: err={} ns",
            est_1h - true_1h
        );
    }

    #[test]
    fn predict_includes_q2_off_diagonal_coupling() {
        // Catches mutation dropping `q01 = q2 * dt^2 / 2` from predicted `p01`.
        let prior = NoisePrior {
            q0_q16_ns2_per_s: 0,
            q2_q80_per_s: NoisePrior::WANDERING_QUARTZ.q2_q80_per_s,
        };
        let mut kf = KalmanFilter::new(prior, DEFAULT_JUMP_NS);
        kf.anchor_with_freq(0, 0, 0, 25_000_000);
        // Zero `p11` so the ONLY source of `p01` growth over 10 s is `q01 = q2 * dt^2 / 2`.
        kf.p11 = 0;
        kf.p01 = 0;
        let dt_ns = 10_000_000_000i64;
        kf.predict(dt_ns);
        let (_, p01, p11) = kf.covariance_raw();
        let expected_q11 = prior.q2_q80_per_s * 10;
        let expected_q01 = ((expected_q11 * i128::from(dt_ns)) >> 32) >> 1;
        assert_eq!(p11, expected_q11);
        assert_eq!(
            p01, expected_q01,
            "p01 must include q2*dt^2/2 coupling: got {p01}, expected {expected_q01}"
        );
        assert!(p01 > 0);
    }
}
