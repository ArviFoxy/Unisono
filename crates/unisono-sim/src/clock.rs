// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Simulated host and audio-device oscillators following IEEE Std 1139-2008
//! power-law frequency noise (white, `1/f` flicker, and random-walk frequency)
//! with optional scripted frequency steps.

use std::f64::consts::PI;

use unisono_core::kalman::NoisePrior;

use crate::random::Generator;
use crate::{TrueTime, nanos_to_seconds, seconds_to_nanos};

/// Step size of the forward-only [`Oscillator`] random walk, in nanoseconds.
const WALK_STEP: i64 = 10_000_000;

/// Grid spacing of [`Course`], in seconds (1 ms).
const COURSE_STEP_S: f64 = 1e-3;

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

/// Converts an index to `f64` for continuous-time grid calculations.
fn as_float(count: usize) -> f64 {
    #[allow(clippy::cast_precision_loss)]
    let value = count as f64;
    value
}

/// IEEE Std 1139-2008 power-law frequency noise of an oscillator.
///
/// The one-sided fractional-frequency power spectral density is
/// `h0_white + h1_flicker / f + h2_walk / f^2`, matching
/// `Unisono.Spec.Models.SecondOrder.ClockNoise`.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct FrequencyNoise {
    /// White frequency noise PSD coefficient `h_0` (seconds, i.e. `1/Hz`).
    /// Continuous-time phase diffusion variance rate is `h0_white / 2`.
    pub h0_white: f64,
    /// Flicker frequency noise PSD coefficient `h_{-1}` (dimensionless).
    /// Allan deviation floor is `sqrt(2 * ln(2) * h1_flicker)`.
    pub h1_flicker: f64,
    /// Random-walk frequency noise PSD coefficient `h_{-2}` (`Hz`).
    /// Continuous-time fractional-frequency diffusion variance rate is
    /// `2 * pi^2 * h2_walk`.
    pub h2_walk: f64,
}

impl FrequencyNoise {
    /// Ideal noiseless oscillator (`h_0 = h_{-1} = h_{-2} = 0`).
    pub const ZERO: FrequencyNoise = FrequencyNoise {
        h0_white: 0.0,
        h1_flicker: 0.0,
        h2_walk: 0.0,
    };

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
    /// 100 times larger than `CONSUMER_QUARTZ` (e.g., a thermally drifting
    /// portable device).
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

    /// Scales all noise power spectral density coefficients by `factor.max(0.0)`.
    #[must_use]
    pub fn scale(self, factor: f64) -> FrequencyNoise {
        let clamped = if factor.is_finite() {
            factor.max(0.0)
        } else {
            0.0
        };
        FrequencyNoise {
            h0_white: self.h0_white * clamped,
            h1_flicker: self.h1_flicker * clamped,
            h2_walk: self.h2_walk * clamped,
        }
    }

    /// Converts the white-frequency and random-walk parameters into the
    /// fixed-point [`unisono_core::kalman::NoisePrior`] units (`Q16 ns^2 / s`
    /// and `Q80 / s`).
    #[must_use]
    pub fn to_core_prior(self) -> NoisePrior {
        let q0_scaled = self.white_variance_rate().max(0.0) * 1e18 * 65_536.0;
        let q2_scaled = self.walk_variance_rate().max(0.0) * 2.0_f64.powi(80);
        #[allow(clippy::cast_possible_truncation)]
        let q0_q16_ns2_per_s = if q0_scaled.is_finite() {
            (q0_scaled.round() as i128).max(0)
        } else {
            0
        };
        #[allow(clippy::cast_possible_truncation)]
        let q2_q80_per_s = if q2_scaled.is_finite() {
            (q2_scaled.round() as i128).max(0)
        } else {
            0
        };
        NoisePrior {
            q0_q16_ns2_per_s,
            q2_q80_per_s,
        }
    }
}

/// Advances a 2-state `(phase, frequency)` clock by `dt >= 0` seconds using
/// exact continuous-time Cholesky sampling of the integrated Brownian-motion
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
    let df = (q2 * dt).max(0.0).sqrt() * z2;
    let cond_phase_var = (q0 * dt + q2 * dt * dt * dt / 12.0).max(0.0);
    let dphi = state.1 * dt + 0.5 * dt * df + cond_phase_var.sqrt() * z1;
    state.0 += dphi;
    state.1 += df;
}

/// Full simulated oscillator state including white frequency noise,
/// random-walk frequency noise, and optional `1/f` flicker frequency modes.
#[derive(Clone, Debug)]
pub struct ClockState {
    /// Phase error `C(t) - t`, in seconds.
    pub phase: f64,
    /// Random-walk plus baseline fractional frequency component.
    pub frequency: f64,
    /// Ornstein-Uhlenbeck fractional-frequency states synthesizing `h_{-1}/f`.
    flicker_modes: [f64; 8],
    noise: FrequencyNoise,
}

impl ClockState {
    /// Creates a clock state at `(phase, frequency)` with flicker modes drawn
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

    /// Advances the clock state by `dt >= 0` seconds.
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
                let u = omega * dt;
                let alpha = (-u).exp();
                let prev = *mode;

                // Exact joint transition of a 1D Ornstein-Uhlenbeck frequency
                // mode `f` and its phase integral `int_0^dt f(s) ds`.
                let (mean_scale, var_f, cov_fp, var_p) = if u < 1e-4 {
                    let ms = dt * (1.0 - 0.5 * u + u * u / 6.0);
                    let vf = mode_var * (2.0 * u * (1.0 - u + (2.0 / 3.0) * u * u));
                    let cfp = mode_var * dt * u * (1.0 - u + (7.0 / 12.0) * u * u);
                    let vp = mode_var * dt * dt * u * ((2.0 / 3.0) - 0.5 * u + 0.2 * u * u);
                    (ms, vf, cfp, vp)
                } else {
                    let ms = (1.0 - alpha) / omega;
                    let vf = mode_var * (1.0 - alpha * alpha).max(0.0);
                    let cfp = (mode_var / omega) * (1.0 - alpha).powi(2);
                    let vp = (mode_var / (omega * omega))
                        * (2.0 * u - 3.0 + 4.0 * alpha - alpha * alpha).max(0.0);
                    (ms, vf, cfp, vp)
                };

                let z1 = generator.normal();
                let z2 = generator.normal();
                let l00 = var_f.max(0.0).sqrt();
                let (freq_noise, phase_noise) = if l00 > 0.0 {
                    let l10 = cov_fp / l00;
                    let l11 = (var_p - l10 * l10).max(0.0).sqrt();
                    (l00 * z1, l10 * z1 + l11 * z2)
                } else {
                    (0.0, var_p.max(0.0).sqrt() * z2)
                };

                *mode = alpha * prev + freq_noise;
                flicker_phase += mean_scale * prev + phase_noise;
            }
            self.phase += flicker_phase;
        }
    }
}

/// Parameters of a simulated host clock or audio-device oscillator.
#[derive(Clone, Copy, Debug)]
pub struct OscillatorModel {
    /// Reading minus true time at `t = 0`, in seconds.
    pub offset: f64,
    /// Initial fractional frequency error: `1e-5` runs 10 ppm fast.
    pub frequency: f64,
    /// IEEE Std 1139-2008 frequency noise parameters (`h_0`, `h_{-1}`, `h_{-2}`).
    pub noise: FrequencyNoise,
}

impl OscillatorModel {
    /// Creates an ideal noiseless oscillator with zero frequency offset and
    /// initial phase `offset` in seconds.
    #[must_use]
    pub const fn ideal(offset: f64) -> OscillatorModel {
        OscillatorModel {
            offset,
            frequency: 0.0,
            noise: FrequencyNoise::ZERO,
        }
    }

    /// Creates an oscillator model from a fractional-frequency random-walk
    /// variance rate `walk_rate` (`q_2 = 2 * pi^2 * h_{-2}`, in `1/s`), with
    /// zero white and flicker frequency noise.
    #[must_use]
    pub fn from_walk_rate(offset: f64, frequency: f64, walk_rate: f64) -> OscillatorModel {
        OscillatorModel {
            offset,
            frequency,
            noise: FrequencyNoise {
                h0_white: 0.0,
                h1_flicker: 0.0,
                h2_walk: walk_rate.max(0.0) / (2.0 * PI * PI),
            },
        }
    }
}

/// Forward-only simulated oscillator stepping on a 10 ms random-walk grid.
///
/// It is read at non-decreasing true times, as used by `packets::OneWay`.
#[derive(Clone, Debug)]
pub struct Oscillator {
    generator: Generator,
    walk: f64,
    /// Reading minus true time at `at`, in seconds.
    offset: f64,
    frequency: f64,
    at: TrueTime,
    next_step: TrueTime,
}

impl Oscillator {
    /// Creates an oscillator that follows `model`, drawing its random walk from
    /// `generator`.
    #[must_use]
    pub fn new(model: OscillatorModel, generator: Generator) -> Oscillator {
        Oscillator {
            generator,
            walk: model.noise.walk_variance_rate().max(0.0),
            offset: model.offset,
            frequency: model.frequency,
            at: TrueTime::ZERO,
            next_step: TrueTime(WALK_STEP),
        }
    }

    fn advance(&mut self, to: TrueTime) {
        assert!(
            to >= self.at,
            "an oscillator is read at times that do not go backwards"
        );
        while self.next_step <= to {
            self.offset += self.frequency * nanos_to_seconds(self.next_step.0 - self.at.0);
            self.at = self.next_step;
            let deviation = (self.walk * nanos_to_seconds(WALK_STEP)).sqrt();
            self.frequency += deviation * self.generator.normal();
            self.next_step = TrueTime(self.next_step.0 + WALK_STEP);
        }
        self.offset += self.frequency * nanos_to_seconds(to.0 - self.at.0);
        self.at = to;
    }

    /// Reading minus true time at `at`, in seconds, without rounding.
    pub fn offset(&mut self, at: TrueTime) -> f64 {
        self.advance(at);
        self.offset
    }

    /// The reading at true time `at`, in nanoseconds.
    pub fn read(&mut self, at: TrueTime) -> i64 {
        at.0.saturating_add(seconds_to_nanos(self.offset(at)))
    }

    /// The fractional frequency at true time `at`.
    pub fn frequency(&mut self, at: TrueTime) -> f64 {
        self.advance(at);
        self.frequency
    }

    /// Changes the fractional frequency by dimensionless `change` at true time
    /// `at`.
    pub fn step_frequency(&mut self, at: TrueTime, change: f64) {
        self.advance(at);
        self.frequency += change;
    }
}

/// Stored grid sample of a [`Course`] at `t_k = k * COURSE_STEP_S`.
#[derive(Clone, Copy, Debug)]
struct ClockSample {
    /// Phase error `C(t_k) - t_k`, in seconds.
    phase: f64,
    /// Instantaneous total fractional frequency at `t_k`.
    total_freq: f64,
}

/// Random-access simulated oscillator trajectory backed by a lazy 1 ms grid of
/// IEEE 1139 [`ClockState`] samples with exact continuous piecewise-linear
/// phase interpolation and exact unquantized inversion.
///
/// Each grid increment clamps `dphi >= -0.5 * dt_s` so the clock reading
/// `C(t) = t + phase(t)` is continuous and strictly increasing everywhere
/// (matching `Unisono.Spec.Clock`).
#[derive(Clone, Debug)]
pub struct Course {
    state: ClockState,
    generator: Generator,
    samples: Vec<ClockSample>,
    /// Future frequency steps `(time_s, delta_frac)` not yet reached by the
    /// lazily generated grid.
    pending_steps: Vec<(f64, f64)>,
}

impl Course {
    /// Creates a course that follows `model`, drawing its oscillator noise from
    /// `generator`.
    #[must_use]
    pub fn new(model: OscillatorModel, mut generator: Generator) -> Course {
        let state = ClockState::new(model.offset, model.frequency, model.noise, &mut generator);
        let initial = ClockSample {
            phase: state.phase,
            total_freq: state.total_frequency(),
        };
        Course {
            state,
            generator,
            samples: vec![initial],
            pending_steps: Vec::new(),
        }
    }

    /// Schedules or applies a step change of `delta_ppm` parts per million to
    /// the oscillator's fractional frequency starting at true time `at`.
    pub fn step_frequency(&mut self, at: TrueTime, delta_ppm: f64) {
        if !delta_ppm.is_finite() {
            return;
        }
        let delta = delta_ppm * 1e-6;
        let step_s = at.seconds().max(0.0);
        let last_idx = self.samples.len() - 1;
        let grid_end_s = as_float(last_idx) * COURSE_STEP_S;
        if step_s > grid_end_s {
            self.pending_steps.push((step_s, delta));
            return;
        }
        self.state.frequency += delta;
        for idx in 0..self.samples.len() {
            let t_idx = as_float(idx) * COURSE_STEP_S;
            if t_idx + 1e-12 >= step_s {
                self.samples[idx].total_freq += delta;
            }
            if t_idx > step_s {
                self.samples[idx].phase += delta * (t_idx - step_s);
            }
            if idx > 0 {
                let min_phase = self.samples[idx - 1].phase - 0.5 * COURSE_STEP_S;
                if self.samples[idx].phase < min_phase {
                    self.samples[idx].phase = min_phase;
                }
            }
        }
        if let Some(last) = self.samples.last() {
            self.state.phase = last.phase;
        }
    }

    /// Extends the lazy 1 ms grid so `self.samples[target]` is populated.
    fn ensure_index(&mut self, target: usize) {
        while self.samples.len() <= target {
            let k = self.samples.len() - 1;
            let t_start = as_float(k) * COURSE_STEP_S;
            let t_end = as_float(k + 1) * COURSE_STEP_S;
            let prev_phase = self.samples[k].phase;

            self.state.advance(COURSE_STEP_S, &mut self.generator);

            if !self.pending_steps.is_empty() {
                let mut idx = 0;
                while idx < self.pending_steps.len() {
                    let (step_s, delta) = self.pending_steps[idx];
                    if step_s < t_end {
                        let remaining = (t_end - step_s.max(t_start)).clamp(0.0, COURSE_STEP_S);
                        if (step_s - t_start).abs() <= 1e-12 {
                            self.samples[k].total_freq += delta;
                        }
                        self.state.phase += delta * remaining;
                        self.state.frequency += delta;
                        self.pending_steps.swap_remove(idx);
                    } else {
                        idx += 1;
                    }
                }
            }

            // Guarantee strict monotonicity of `C(t) = t + phase(t)` with slope
            // at least `0.5` across every grid cell.
            let min_phase = prev_phase - 0.5 * COURSE_STEP_S;
            if self.state.phase < min_phase {
                self.state.phase = min_phase;
            }
            self.samples.push(ClockSample {
                phase: self.state.phase,
                total_freq: self.state.total_frequency(),
            });
        }
    }

    /// Returns whether grid reading `C(t_idx) < reading_s` without adding a
    /// large initial offset to `t_idx`.
    fn grid_reading_lt(&self, idx: usize, reading_s: f64) -> bool {
        as_float(idx) * COURSE_STEP_S < reading_s - self.samples[idx].phase
    }

    /// Returns whether grid reading `C(t_idx) <= reading_s` without adding a
    /// large initial offset to `t_idx`.
    fn grid_reading_le(&self, idx: usize, reading_s: f64) -> bool {
        as_float(idx) * COURSE_STEP_S <= reading_s - self.samples[idx].phase
    }

    /// Interpolated phase error `C(t) - t` at unquantized true time `t_s`
    /// seconds.
    pub fn phase_at(&mut self, t_s: f64) -> f64 {
        if !t_s.is_finite() {
            return 0.0;
        }
        if t_s < 0.0 {
            let slope = (1.0 + self.samples[0].total_freq).max(0.5);
            return self.samples[0].phase + (slope - 1.0) * t_s;
        }
        let pos = t_s / COURSE_STEP_S;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let index = pos.floor() as usize;
        self.ensure_index(index + 1);
        let frac = pos - as_float(index);
        let first_phase = self.samples[index].phase;
        let next_phase = self.samples[index + 1].phase;
        first_phase + frac * (next_phase - first_phase)
    }

    /// Reading minus true time at `at`, in seconds.
    pub fn offset(&mut self, at: TrueTime) -> f64 {
        self.phase_at(at.seconds())
    }

    /// Unquantized clock reading `C(t) = t + phase(t)` at true time `t_s`
    /// seconds.
    pub fn read_seconds(&mut self, t_s: f64) -> f64 {
        t_s + self.phase_at(t_s)
    }

    /// Clock reading at true time `at`, in seconds.
    pub fn seconds(&mut self, at: TrueTime) -> f64 {
        self.read_seconds(at.seconds())
    }

    /// Clock reading at true time `at`, in nanoseconds.
    pub fn read(&mut self, at: TrueTime) -> i64 {
        at.0.saturating_add(seconds_to_nanos(self.offset(at)))
    }

    /// Clock reading at true time `at`, in nanoseconds, perturbed by
    /// independent zero-mean Gaussian timestamp noise with standard deviation
    /// `std_s` seconds.
    pub fn read_noisy(&mut self, at: TrueTime, std_s: f64, generator: &mut Generator) -> i64 {
        let jitter = if std_s > 0.0 && std_s.is_finite() {
            std_s * generator.normal()
        } else {
            0.0
        };
        at.0.saturating_add(seconds_to_nanos(self.offset(at) + jitter))
    }

    /// Instantaneous total fractional frequency (including flicker modes and
    /// any frequency steps) at true time `at`.
    pub fn frequency_at(&mut self, at: TrueTime) -> f64 {
        let t_s = at.seconds();
        if !t_s.is_finite() || t_s <= 0.0 {
            self.ensure_index(1);
            return self.samples[0].total_freq;
        }
        let pos = t_s / COURSE_STEP_S;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let index = pos.floor() as usize;
        self.ensure_index(index + 1);
        self.samples[index].total_freq
    }

    /// Instantaneous total fractional frequency at true time `at`.
    pub fn frequency(&mut self, at: TrueTime) -> f64 {
        self.frequency_at(at)
    }

    /// Exact unquantized true time (in seconds) at which this clock shows
    /// `reading_s` seconds, inverting the piecewise-linear trajectory
    /// `C(t) = t + phase(t)`.
    pub fn when_seconds(&mut self, reading_s: f64) -> f64 {
        if !reading_s.is_finite() {
            return reading_s;
        }
        if reading_s < self.samples[0].phase {
            let slope = (1.0 + self.samples[0].total_freq).max(0.5);
            return (reading_s - self.samples[0].phase) / slope;
        }
        self.ensure_index(1);
        while self.grid_reading_lt(self.samples.len() - 1, reading_s) {
            let last_idx = self.samples.len() - 1;
            let deficit =
                (reading_s - self.samples[last_idx].phase) - as_float(last_idx) * COURSE_STEP_S;
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let extra = (deficit / COURSE_STEP_S).ceil().max(1.0) as usize;
            self.ensure_index(last_idx.saturating_add(extra));
        }
        let mut lo = 0_usize;
        let mut hi = self.samples.len() - 1;
        while lo + 1 < hi {
            let mid = lo.midpoint(hi);
            if self.grid_reading_le(mid, reading_s) {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        let delta_r = (reading_s - self.samples[lo].phase) - as_float(lo) * COURSE_STEP_S;
        let span = COURSE_STEP_S + (self.samples[hi].phase - self.samples[lo].phase);
        let frac = if span > 0.0 {
            (delta_r / span).clamp(0.0, 1.0)
        } else {
            0.0
        };
        (as_float(lo) + frac) * COURSE_STEP_S
    }

    /// True time (rounded to nanoseconds) at which this clock shows `reading_s`
    /// seconds.
    pub fn when(&mut self, reading_s: f64) -> TrueTime {
        TrueTime::from_seconds(self.when_seconds(reading_s))
    }
}

#[cfg(test)]
mod tests {
    use unisono_core::kalman::NoisePrior;

    use super::{Course, FrequencyNoise, Oscillator, OscillatorModel};
    use crate::TrueTime;
    use crate::random::Generator;

    #[test]
    fn to_core_prior_matches_core_noise_priors() {
        assert_eq!(FrequencyNoise::TCXO.to_core_prior(), NoisePrior::TCXO);
        assert_eq!(
            FrequencyNoise::CONSUMER_QUARTZ.to_core_prior(),
            NoisePrior::CONSUMER_QUARTZ
        );
        assert_eq!(
            FrequencyNoise::WANDERING_QUARTZ.to_core_prior(),
            NoisePrior::WANDERING_QUARTZ
        );
        assert_eq!(
            FrequencyNoise::ZERO.to_core_prior(),
            NoisePrior {
                q0_q16_ns2_per_s: 0,
                q2_q80_per_s: 0,
            }
        );
        let combined = FrequencyNoise::CONSUMER_QUARTZ.combine(FrequencyNoise::CONSUMER_QUARTZ);
        let scaled = FrequencyNoise::CONSUMER_QUARTZ.scale(2.0);
        assert!((combined.h0_white - scaled.h0_white).abs() < 1e-30);
        assert!((combined.h2_walk - scaled.h2_walk).abs() < 1e-30);
    }

    #[test]
    fn a_steady_oscillator_gains_its_frequency_times_the_elapsed_time() {
        let model = OscillatorModel::from_walk_rate(0.25, 20e-6, 0.0);
        let mut clock = Oscillator::new(model, Generator::new(1));
        assert_eq!(clock.read(TrueTime::ZERO), 250_000_000);
        // After 1000 s it has gained 20 ms.
        assert_eq!(
            clock.read(TrueTime::from_seconds(1_000.0)),
            1_000_000_000_000 + 250_000_000 + 20_000_000
        );
    }

    #[test]
    fn a_frequency_step_changes_the_rate_from_then_on() {
        let model = OscillatorModel::ideal(0.0);
        let mut clock = Oscillator::new(model, Generator::new(1));
        clock.step_frequency(TrueTime::from_seconds(10.0), 1e-6);
        let gained = clock.offset(TrueTime::from_seconds(110.0));
        assert!((gained - 100e-6).abs() < 1e-12, "gained {gained}");
    }

    /// A random walk of variance `walk` per second has a frequency with
    /// variance `walk * t` after `t` seconds. Over 400 oscillators the sample
    /// variance is within a quarter of that except with negligible probability.
    #[test]
    fn the_frequency_walks_with_the_stated_variance() {
        let (walk, seconds) = (1e-18, 100.0);
        let parent = Generator::new(3);
        let squares: f64 = (0..400)
            .map(|i| {
                let model = OscillatorModel::from_walk_rate(0.0, 0.0, walk);
                Oscillator::new(model, parent.fork(i))
                    .frequency(TrueTime::from_seconds(seconds))
                    .powi(2)
            })
            .sum();
        let ratio = squares / 400.0 / (walk * seconds);
        assert!((0.75..1.25).contains(&ratio), "variance ratio {ratio}");
    }

    #[test]
    #[should_panic(expected = "do not go backwards")]
    fn reading_at_an_earlier_time_is_refused() {
        let model = OscillatorModel::ideal(0.0);
        let mut clock = Oscillator::new(model, Generator::new(1));
        clock.read(TrueTime(100));
        clock.read(TrueTime(99));
    }

    #[test]
    fn a_course_is_read_in_any_order_and_inverted() {
        let model = OscillatorModel::from_walk_rate(3_600.0, 50e-6, 1e-16);
        let mut course = Course::new(model, Generator::new(3));
        let late = course.read(TrueTime::from_seconds(100.0));
        let early = course.read(TrueTime::from_seconds(1.0));
        // Reading an earlier time afterwards changes nothing about a later one.
        assert_eq!(course.read(TrueTime::from_seconds(100.0)), late);
        assert!(late - early > 99_000_000_000);
        // The reading is 50 parts per million fast: after a second, 50 microseconds.
        let gained = early - course.read(TrueTime::ZERO) - 1_000_000_000;
        assert!((gained - 50_000).abs() < 50, "gained {gained}");
        // The time at which it shows a reading is the time it was read at.
        let reading = course.seconds(TrueTime::from_seconds(42.5));
        let found = course.when(reading);
        assert!((found.0 - 42_500_000_000).abs() <= 1, "found {found:?}");
    }

    #[test]
    fn course_is_strictly_monotonic_even_under_extreme_noise_and_negative_steps() {
        let extreme = OscillatorModel {
            offset: -10.0,
            frequency: -0.9,
            noise: FrequencyNoise {
                h0_white: 1e-4,
                h1_flicker: 1e-2,
                h2_walk: 1e-2,
            },
        };
        let mut course = Course::new(extreme, Generator::new(17));
        course.step_frequency(TrueTime::from_seconds(0.5), -900_000.0);
        let mut prev = course.read_seconds(-0.2);
        for step in 0..2_500_i32 {
            let t = -0.199 + f64::from(step) * 0.000_7;
            let curr = course.read_seconds(t);
            assert!(
                curr > prev,
                "course not strictly increasing at t={t}: prev={prev}, curr={curr}"
            );
            prev = curr;
        }
    }

    #[test]
    fn course_when_seconds_roundtrips_read_seconds_accurately() {
        let model = OscillatorModel {
            offset: 86_400.0,
            frequency: -37e-6,
            noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        };
        let mut course = Course::new(model, Generator::new(29));
        course.step_frequency(TrueTime::from_seconds(5.0), 40.0);
        let probe_times = [
            -0.012_345,
            0.0,
            1.0 / 48_000.0,
            17.0 / 48_000.0,
            0.001_5,
            4.999_75,
            5.0,
            5.000_25,
            12.345_678_9,
        ];
        for t in probe_times {
            let reading = course.read_seconds(t);
            let recovered = course.when_seconds(reading);
            assert!(
                (recovered - t).abs() < 1e-10,
                "roundtrip mismatch at t={t}: reading={reading}, recovered={recovered}"
            );
        }
    }

    #[test]
    fn course_step_frequency_and_read_noisy_behave_as_modeled() {
        let mut scheduled = Course::new(OscillatorModel::ideal(0.0), Generator::new(5));
        scheduled.step_frequency(TrueTime::from_seconds(10.0), 25.0);
        assert!(scheduled.frequency_at(TrueTime::from_seconds(5.0)).abs() < 1e-15);
        assert!((scheduled.frequency_at(TrueTime::from_seconds(10.0)) - 25e-6).abs() < 1e-15);
        assert!((scheduled.offset(TrueTime::from_seconds(20.0)) - 250e-6).abs() < 1e-12);

        // Retroactive step after grid generation produces the same trajectory.
        let mut retroactive = Course::new(OscillatorModel::ideal(0.0), Generator::new(5));
        let _ = retroactive.offset(TrueTime::from_seconds(20.0));
        retroactive.step_frequency(TrueTime::from_seconds(10.0), 25.0);
        assert!((retroactive.offset(TrueTime::from_seconds(20.0)) - 250e-6).abs() < 1e-12);
        assert!((retroactive.offset(TrueTime::from_seconds(30.0)) - 500e-6).abs() < 1e-12);

        // Noisy readings match zero-mean Gaussian variance `std_s^2`.
        let mut rng = Generator::new(91);
        let std_s = 10e-6;
        let samples = 20_000_i32;
        let at = TrueTime::from_seconds(1.0);
        let exact = scheduled.read(at);
        let mut sq_sum = 0.0;
        for _ in 0..samples {
            let noisy = scheduled.read_noisy(at, std_s, &mut rng);
            #[allow(clippy::cast_precision_loss)]
            let err_s = (noisy - exact) as f64 * 1e-9;
            sq_sum += err_s * err_s;
        }
        let sample_std = (sq_sum / f64::from(samples)).sqrt();
        assert!(
            (sample_std - std_s).abs() < 0.05 * std_s,
            "noisy std {sample_std} vs {std_s}"
        );
    }
}
