// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The filter that gives a stream's value between its frames.
//!
//! The value at a position is a weighted sum of the frames around it. The
//! weights are those of the ideal interpolation, `sin(pi t) / (pi t)` for a
//! frame at distance `t`, cut to a finite length by a Kaiser window. They
//! are tabulated for a number of evenly spaced fractions of a frame, and the
//! weights for a fraction between two of those are interpolated linearly.

use std::f64::consts::PI;

/// The weights of the frames around a position, for every fraction of a frame.
#[derive(Clone, Debug)]
pub struct Filter {
    taps: usize,
    phase_bits: u32,
    beta: f64,
    /// `(1 << phase_bits) + 1` rows of `taps` weights. Row `j` is for the
    /// fraction `j / (1 << phase_bits)`; the last row is for the next frame.
    table: Box<[f32]>,
}

impl Filter {
    /// The highest frequency, in hertz, that [`Filter::for_rate`] keeps.
    pub const HIGHEST_KEPT_HERTZ: f64 = 20_000.0;

    /// The error, in decibels below a sinusoid in the kept band, that
    /// [`Filter::for_rate`] designs for.
    pub const ERROR_DECIBELS: f64 = 110.0;

    /// The number of tabulated fractions of a frame, as a power of two.
    pub const PHASE_BITS: u32 = 10;

    /// The filter for a stream of `rate` frames per second.
    ///
    /// It keeps frequencies up to [`Filter::HIGHEST_KEPT_HERTZ`], or up to
    /// the same share of the rate as at 44 100 frames per second when the
    /// rate is lower than that, with the error [`Filter::ERROR_DECIBELS`].
    #[must_use]
    pub fn for_rate(rate: u32) -> Filter {
        let share = Filter::HIGHEST_KEPT_HERTZ / 44_100.0;
        let kept = (Filter::HIGHEST_KEPT_HERTZ / f64::from(rate.max(1))).min(share);
        Filter::design(kept, Filter::ERROR_DECIBELS)
    }

    /// The shortest filter whose error for a sinusoid of at most `kept`
    /// cycles per frame is about `error` decibels below that sinusoid.
    ///
    /// The error of an interpolated sinusoid of frequency `f` consists of
    /// its images at `1 - f`, `1 + f`, and so on, so the filter must pass
    /// frequencies up to `kept` and stop those from `1 - kept` on. A sinc
    /// shaped by a Kaiser window changes from one to the other in a band
    /// around one half whose half-width is `sqrt(beta^2 + pi^2) / (pi *
    /// taps)`, and stops by `beta / 0.1102 + 8.7` decibels (Kaiser's
    /// empirical formula). The two nearest images can add, which costs 6
    /// decibels, and one more is allowed for the rest. The number of taps
    /// follows, rounded up to a multiple of eight, and the window then takes
    /// the largest `beta` that still fits the band.
    ///
    /// `kept` is brought into 0.05 to 0.49 and `error` into 60 to 130, and
    /// the number of taps is at least 16. Within those ranges it is at most
    /// 464.
    #[must_use]
    pub fn design(kept: f64, error: f64) -> Filter {
        let kept = if kept.is_nan() {
            0.05
        } else {
            kept.clamp(0.05, 0.49)
        };
        let error = if error.is_nan() {
            60.0
        } else {
            error.clamp(60.0, 130.0)
        };
        let half_width = 0.5 - kept;
        let beta = 0.1102 * (error + 7.0 - 8.7);
        let needed = (beta * beta + PI * PI).sqrt() / (PI * half_width);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        // between 16 and 1024 after the clamp
        let taps = ((needed / 8.0).ceil() * 8.0).clamp(16.0, 1024.0) as usize;
        #[allow(clippy::cast_precision_loss)] // at most 1024
        let reach = PI * taps as f64 * half_width;
        let widest = (reach * reach - PI * PI).max(0.0).sqrt();
        Filter::kaiser(taps, widest.min(16.0), Filter::PHASE_BITS)
    }

    /// The filter of `taps` weights shaped by the Kaiser window of parameter
    /// `beta`, tabulated at `1 << phase_bits` fractions of a frame.
    ///
    /// `taps` is made even and brought into 2 to 1024, `beta` into 0 to 30
    /// and `phase_bits` into 1 to 16.
    #[must_use]
    pub fn kaiser(taps: usize, beta: f64, phase_bits: u32) -> Filter {
        let taps = (taps.clamp(2, 1024) / 2) * 2;
        let beta = if beta.is_nan() {
            0.0
        } else {
            beta.clamp(0.0, 30.0)
        };
        let phase_bits = phase_bits.clamp(1, 16);
        let phases = 1usize << phase_bits;
        let mut table = vec![0.0f32; (phases + 1) * taps].into_boxed_slice();
        let mut row = vec![0.0f64; taps];
        // The weights for the fraction `1 - x` are those for `x` in reverse
        // order. Only half the rows are computed and the others are copies,
        // so the table has this symmetry exactly.
        for phase in 0..=phases / 2 {
            exact_row(taps, beta, phase, phases, &mut row);
            let mirrored = phases - phase;
            for (tap, weight) in row.iter().enumerate() {
                #[allow(clippy::cast_possible_truncation)] // rounding to f32 is intended
                let weight = *weight as f32;
                if let Some(slot) = table.get_mut(phase * taps + tap) {
                    *slot = weight;
                }
                if let Some(slot) = table.get_mut(mirrored * taps + (taps - 1 - tap)) {
                    *slot = weight;
                }
            }
        }
        Filter {
            taps,
            phase_bits,
            beta,
            table,
        }
    }

    /// The number of frames that give the value at one position.
    #[must_use]
    pub fn taps(&self) -> usize {
        self.taps
    }

    /// The parameter of the Kaiser window.
    #[must_use]
    pub fn beta(&self) -> f64 {
        self.beta
    }

    /// The number of tabulated fractions of a frame.
    #[must_use]
    pub fn phases(&self) -> usize {
        1 << self.phase_bits
    }

    /// The number of frames before the frame of a position that its value
    /// depends on: `taps / 2 - 1`.
    #[must_use]
    pub fn before(&self) -> usize {
        self.taps / 2 - 1
    }

    /// The number of frames after the frame of a position that its value
    /// depends on: `taps / 2`. The value at a position can be computed once
    /// the frame this far ahead of it is there, so this is the delay that
    /// the filter adds to playback, the same for every frequency.
    #[must_use]
    pub fn ahead(&self) -> usize {
        self.taps / 2
    }

    /// Writes the weights for the position `fraction * 2^-64` frames beyond
    /// a frame `n` into `row`: element `i` is the weight of the frame
    /// `n - before() + i`. `row` should have [`Filter::taps`] elements.
    ///
    /// The weights are those of the two nearest tabulated fractions,
    /// interpolated linearly. Of the fraction, the first [`Filter::phases`]
    /// (as a power of two) binary digits select the pair and the next 24 are
    /// the weight between them; further digits are not used.
    pub fn coefficients(&self, fraction: u64, row: &mut [f32]) {
        // At most 16 digits, so this fits a usize on every platform.
        #[allow(clippy::cast_possible_truncation)]
        let phase = (fraction >> (64 - self.phase_bits)) as usize;
        // 24 digits, which an f32 holds exactly.
        #[allow(clippy::cast_precision_loss)]
        let between = ((fraction << self.phase_bits) >> 40) as f32 * (1.0 / 16_777_216.0);
        let from = phase * self.taps;
        let (Some(lower), Some(upper)) = (
            self.table.get(from..from + self.taps),
            self.table.get(from + self.taps..from + 2 * self.taps),
        ) else {
            return;
        };
        for ((weight, a), b) in row.iter_mut().zip(lower).zip(upper) {
            *weight = a + between * (b - a);
        }
    }
}

/// The weights for the fraction `phase / phases` in double precision, scaled
/// so that they add up to one.
///
/// Without the scaling a constant input would come out with a gain that
/// depends on the fraction, by about the amount the filter lets through at
/// the sample rate and its multiples.
fn exact_row(taps: usize, beta: f64, phase: usize, phases: usize, row: &mut [f64]) {
    #![allow(clippy::cast_precision_loss)] // counts of taps and phases are small
    let before = taps / 2 - 1;
    if phase == 0 {
        // A position on a frame is that frame: sin(pi k) is zero at every
        // other frame, exactly.
        for (tap, weight) in row.iter_mut().enumerate() {
            *weight = if tap == before { 1.0 } else { 0.0 };
        }
        return;
    }
    let fraction = phase as f64 / phases as f64;
    let half = taps as f64 / 2.0;
    // sin(pi (k - x)) = -(-1)^k sin(pi x) for a whole k.
    let sine = (PI * fraction).sin();
    let scale = bessel_i0(beta);
    let mut sum = 0.0;
    for (tap, weight) in row.iter_mut().enumerate() {
        let frames = tap as f64 - before as f64;
        let distance = frames - fraction;
        let sign = if (tap + before).is_multiple_of(2) {
            -1.0
        } else {
            1.0
        };
        let ideal = sign * sine / (PI * distance);
        let across = distance / half;
        let window = bessel_i0(beta * (1.0 - across * across).max(0.0).sqrt()) / scale;
        *weight = ideal * window;
        sum += *weight;
    }
    for weight in row.iter_mut() {
        *weight /= sum;
    }
}

/// The modified Bessel function of the first kind and order zero, by its
/// power series: the sum over `k` of `((x / 2)^k / k!)^2`.
fn bessel_i0(x: f64) -> f64 {
    let quarter = x * x / 4.0;
    let mut term = 1.0;
    let mut sum = 1.0;
    // For x up to 30 the terms fall below the last digit of the sum well
    // before the 200th.
    for k in 1..200 {
        let k = f64::from(k);
        term *= quarter / (k * k);
        sum += term;
        if term < sum * 1e-17 {
            break;
        }
    }
    sum
}

#[cfg(test)]
mod tests {
    use super::{Filter, bessel_i0};

    /// Reference values from the tables of Abramowitz and Stegun.
    #[test]
    fn the_bessel_function_has_its_tabulated_values() {
        for (x, expected) in [
            (0.0, 1.0),
            (1.0, 1.266_065_877_752_008),
            (5.0, 27.239_871_823_604_44),
            (10.0, 2_815.716_628_466_254),
        ] {
            let value = bessel_i0(x);
            assert!(
                ((value - expected) / expected).abs() < 1e-13,
                "I0({x}) = {value}"
            );
        }
    }

    /// The rule for the number of taps, at the two common rates.
    #[test]
    fn the_design_follows_its_rule() {
        let at_44100 = Filter::for_rate(44_100);
        assert_eq!((at_44100.taps(), at_44100.ahead()), (88, 44));
        let at_48000 = Filter::for_rate(48_000);
        assert_eq!((at_48000.taps(), at_48000.ahead()), (48, 24));
        assert_eq!(at_48000.before(), 23);
        assert_eq!(at_48000.phases(), 1024);
    }

    #[test]
    fn odd_parameters_are_brought_into_range() {
        let filter = Filter::kaiser(7, f64::NAN, 40);
        assert_eq!((filter.taps(), filter.phases()), (6, 1 << 16));
        assert_eq!(Filter::kaiser(0, 5.0, 0).taps(), 2);
        assert_eq!(Filter::design(f64::NAN, f64::NAN).taps(), 16);
        // The narrowest band and the smallest error that are accepted:
        // beta = 0.1102 * (130 + 7 - 8.7) = 14.14, and
        // sqrt(14.14^2 + pi^2) / (pi * 0.01) = 461.03, rounded up to 464.
        assert_eq!(Filter::design(0.5, 200.0).taps(), 464);
        assert_eq!(Filter::for_rate(0).taps(), 88);
    }
}
