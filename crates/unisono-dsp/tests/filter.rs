// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! What the interpolation filter does to a sinusoid, computed from its
//! weights.

#![allow(clippy::cast_precision_loss)] // small counts and 64-bit fractions as f64

use std::f64::consts::PI;

use unisono_dsp::Filter;

/// The fraction of a frame `numerator / denominator` in units of 2^-64.
fn fraction(numerator: u64, denominator: u64) -> u64 {
    u64::try_from((u128::from(numerator) << 64) / u128::from(denominator)).expect("below one")
}

fn weights(filter: &Filter, fraction: u64) -> Vec<f32> {
    let mut row = vec![0.0f32; filter.taps()];
    filter.coefficients(fraction, &mut row);
    row
}

/// The size of the error of the value that the filter gives a sinusoid of
/// unit amplitude and `frequency` cycles per frame, at a position
/// `fraction * 2^-64` frames beyond a frame.
///
/// With the frame of the position as frame 0 and the phase of the sinusoid
/// zero at the position, the frame `k` holds `exp(2 pi i f (k - x))`, where
/// `f` is the frequency and `x` the fraction of a frame, and the true value
/// at the position is 1.
fn error_for_sinusoid(filter: &Filter, frequency: f64, fraction: u64) -> f64 {
    let beyond = fraction as f64 / 2f64.powi(64);
    let (mut real, mut imaginary) = (-1.0, 0.0);
    for (tap, weight) in weights(filter, fraction).iter().enumerate() {
        let frames = tap as f64 - filter.before() as f64 - beyond;
        let angle = 2.0 * PI * frequency * frames;
        real += f64::from(*weight) * angle.cos();
        imaginary += f64::from(*weight) * angle.sin();
    }
    real.hypot(imaginary)
}

/// The largest error for sinusoids up to `kept` cycles per frame, over
/// fractions on the table, half-way between two table entries (where the
/// linear interpolation of the weights is worst) and elsewhere.
fn largest_error(filter: &Filter, kept: f64) -> f64 {
    let phases = filter.phases() as u64;
    let mut largest = 0.0f64;
    for step in 0..96u64 {
        // A spread of table entries, each with three places after it.
        let entry = (step * 104_729) % phases;
        for (numerator, denominator) in [(0, 1), (1, 2), (3, 10), (9, 10)] {
            let at = fraction(entry * denominator + numerator, phases * denominator);
            for point in 0..=64 {
                let frequency = kept * f64::from(point) / 64.0;
                largest = largest.max(error_for_sinusoid(filter, frequency, at));
            }
        }
    }
    largest
}

fn decibels(ratio: f64) -> f64 {
    20.0 * ratio.log10()
}

/// The filter's gain at `frequency` cycles per frame as a filter in
/// continuous time, from its weights at 32 evenly spaced fractions. This is
/// what it lets through of an image at that frequency.
fn gain(filter: &Filter, frequency: f64) -> f64 {
    let (mut real, mut imaginary) = (0.0, 0.0);
    for phase in 0..32u64 {
        let beyond = phase as f64 / 32.0;
        for (tap, weight) in weights(filter, fraction(phase, 32)).iter().enumerate() {
            let frames = tap as f64 - filter.before() as f64 - beyond;
            let angle = -2.0 * PI * frequency * frames;
            real += f64::from(*weight) * angle.cos();
            imaginary += f64::from(*weight) * angle.sin();
        }
    }
    real.hypot(imaginary) / 32.0
}

/// Detects a filter that does not meet what it was designed for: too few
/// taps, a wrong window, too few tabulated fractions, or weights that are
/// misplaced by a tap.
#[test]
fn a_sinusoid_in_the_kept_band_has_the_designed_error_at_most() {
    for rate in [32_000u32, 44_100, 48_000, 88_200, 96_000, 176_400, 192_000] {
        let filter = Filter::for_rate(rate);
        let kept = (20_000.0 / f64::from(rate)).min(20_000.0 / 44_100.0);
        let error = decibels(largest_error(&filter, kept));
        assert!(
            error <= -Filter::ERROR_DECIBELS,
            "{rate} frames per second: {error:.1} dB with {} taps",
            filter.taps()
        );
    }
}

/// The figures stated in the crate's documentation for the two common
/// rates. A change of the design that moves them fails here, so that the
/// documentation is changed with it.
#[test]
fn the_documented_figures_hold() {
    for (rate, taps, error, ripple, stop) in [
        (44_100u32, 88, -114.0, 1e-5, -120.0),
        (48_000, 48, -111.5, 2e-5, -117.5),
    ] {
        let filter = Filter::for_rate(rate);
        let kept = 20_000.0 / f64::from(rate);
        assert_eq!(filter.taps(), taps);
        let measured = decibels(largest_error(&filter, kept));
        assert!(measured <= error, "{rate}: error {measured:.2} dB");
        let mut largest_ripple = 0.0f64;
        for point in 0..=200 {
            let level = decibels(gain(&filter, kept * f64::from(point) / 200.0));
            largest_ripple = largest_ripple.max(level.abs());
        }
        assert!(
            largest_ripple <= ripple,
            "{rate}: ripple {largest_ripple:e} dB"
        );
        // The images of the kept band lie from `1 - kept` on.
        let mut largest_stop = f64::NEG_INFINITY;
        for point in 0..=2000 {
            let frequency = 1.0 - kept + (8.0 - (1.0 - kept)) * f64::from(point) / 2000.0;
            largest_stop = largest_stop.max(decibels(gain(&filter, frequency)));
        }
        assert!(
            largest_stop <= stop,
            "{rate}: stopband {largest_stop:.2} dB"
        );
    }
}

/// Detects weights that do not add up to one, which would give a constant
/// input a gain that changes with the fraction. At a tabulated fraction each
/// weight is its exact value rounded once to single precision, so the sum
/// can differ from one by at most 2^-24 of the sum of the weights' sizes.
#[test]
fn the_tabulated_weights_add_up_to_one() {
    for rate in [44_100u32, 48_000] {
        let filter = Filter::for_rate(rate);
        let phases = filter.phases() as u64;
        for entry in 0..phases {
            let row = weights(&filter, fraction(entry, phases));
            let sum: f64 = row.iter().map(|weight| f64::from(*weight)).sum();
            let size: f64 = row.iter().map(|weight| f64::from(weight.abs())).sum();
            assert!(
                (sum - 1.0).abs() <= size * 2f64.powi(-24),
                "{rate} frames per second, entry {entry}: sum {sum}"
            );
        }
    }
}

/// A position on a frame must give that frame and nothing of the others, so
/// that a stream played at its own rate and on its own frames is unchanged.
#[test]
fn a_position_on_a_frame_takes_only_that_frame() {
    let filter = Filter::for_rate(48_000);
    let row = weights(&filter, 0);
    for (tap, weight) in row.iter().enumerate() {
        let expected = if tap == filter.before() { 1.0 } else { 0.0 };
        assert_eq!(weight.to_bits(), f32::to_bits(expected), "tap {tap}");
    }
}

/// Detects a filter that is not symmetric about the position, which would
/// shift the output in time by an amount that depends on frequency.
#[test]
fn the_weights_before_and_after_a_position_mirror_each_other() {
    let filter = Filter::for_rate(44_100);
    let phases = filter.phases() as u64;
    for entry in 1..phases {
        let row = weights(&filter, fraction(entry, phases));
        let mut mirrored = weights(&filter, fraction(phases - entry, phases));
        mirrored.reverse();
        assert_eq!(row, mirrored, "entry {entry}");
    }
}
