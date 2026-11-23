// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Overflow-safe fixed-point arithmetic helpers (floor division, saturation,
//! and right-shifted multiplication [`mul_shift`]).

/// The largest shift that [`mul_shift`] applies.
pub const MAX_SHIFT: u32 = 64;

/// Returns `x` limited to the range of `i64`.
#[must_use]
pub fn saturate(x: i128) -> i64 {
    if x > i64::MAX as i128 {
        i64::MAX
    } else if x < i64::MIN as i128 {
        i64::MIN
    } else {
        // In range, so the cast keeps the value.
        #[allow(clippy::cast_possible_truncation)]
        let narrow = x as i64;
        narrow
    }
}

/// Returns `a * b / 2^shift`, rounded to the nearest integer and limited to
/// the range of `i64`.
///
/// A value halfway between two integers is rounded toward positive infinity.
/// A `shift` above [`MAX_SHIFT`] counts as `MAX_SHIFT`.
#[must_use]
pub fn mul_shift(a: i64, b: i64, shift: u32) -> i64 {
    let shift = if shift > MAX_SHIFT { MAX_SHIFT } else { shift };
    // The product of two 64-bit numbers is at most 2^126 in magnitude and half
    // a unit of the result is at most 2^63, so neither operation wraps.
    let product = (a as i128).wrapping_mul(b as i128);
    let half = if shift == 0 {
        0
    } else {
        1i128.wrapping_shl(shift.wrapping_sub(1))
    };
    saturate(product.wrapping_add(half).wrapping_shr(shift))
}

/// Returns `a / b` rounded toward negative infinity, for a positive `b`.
///
/// For a `b` that is not positive the result is 0.
#[must_use]
pub fn div_floor(a: i128, b: i64) -> i128 {
    div_floor_wide(a, b as i128)
}

/// Returns `a / b` rounded toward negative infinity, for a positive `b` of
/// any size.
///
/// For a `b` that is not positive the result is 0.
#[must_use]
pub fn div_floor_wide(a: i128, b: i128) -> i128 {
    if b <= 0 {
        return 0;
    }
    // The divisor is positive, so neither operation can fail.
    let (Some(quotient), Some(remainder)) = (a.checked_div(b), a.checked_rem(b)) else {
        return 0;
    };
    if remainder < 0 {
        quotient.wrapping_sub(1)
    } else {
        quotient
    }
}

/// Returns the Euclidean remainder of `a` divided by `b`, in `0..b`, or
/// `None` when `b` is zero.
#[must_use]
pub fn rem_euclid_wide(a: i128, b: usize) -> Option<usize> {
    if b == 0 {
        return None;
    }
    let divisor = b as i128;
    let Some(remainder) = a.checked_rem(divisor) else {
        return None;
    };
    let non_negative = if remainder < 0 {
        remainder.wrapping_add(divisor)
    } else {
        remainder
    };
    // `non_negative` is in `0..b`, so it fits `usize`.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let place = non_negative as usize;
    Some(place)
}

/// The largest power of four that an `i128` holds: 2^126.
const LARGEST_POWER_OF_FOUR: i128 = 85_070_591_730_234_615_865_843_651_857_942_052_864;

/// Returns the square root of `x`, rounded down: the largest integer whose
/// square is at most `x`.
///
/// For a negative `x` the result is 0.
#[must_use]
pub fn root(x: i128) -> i128 {
    if x <= 0 {
        return 0;
    }
    // One bit of the root in each round, from the highest. `rest` is `x`
    // less the square of the bits found so far, and `found` holds those
    // bits, moved up so that a bit to try can be added to twice their value.
    let mut rest = x;
    let mut found: i128 = 0;
    let mut bit = LARGEST_POWER_OF_FOUR;
    let mut round = 0u32;
    while round < 64 {
        let trial = found.wrapping_add(bit);
        found = found.wrapping_shr(1);
        if rest >= trial {
            rest = rest.wrapping_sub(trial);
            found = found.wrapping_add(bit);
        }
        bit = bit.wrapping_shr(2);
        round = round.saturating_add(1);
    }
    found
}

/// Returns `a * b`, saturated to the range of `i128`.
#[must_use]
pub fn saturating_mul_i128(a: i128, b: i128) -> i128 {
    match a.checked_mul(b) {
        Some(prod) => prod,
        None => {
            if (a < 0) == (b < 0) {
                i128::MAX
            } else {
                i128::MIN
            }
        }
    }
}

/// Returns `a * b`, saturated to the range of `i64`.
#[must_use]
pub fn saturating_mul_i64(a: i64, b: i64) -> i64 {
    saturate((a as i128).wrapping_mul(b as i128))
}

/// Returns `floor((num * 2^shift) / den)`, saturated to the range of `i128`,
/// for a positive `den`.
///
/// For a `den` that is not positive the result is `0`. A `shift` above
/// [`MAX_SHIFT`] counts as [`MAX_SHIFT`]. Because the quotient and remainder
/// are split before scaling, no intermediate product can overflow `i128` even
/// at extreme inputs.
#[must_use]
pub fn scale_div_pow2(num: i128, shift: u32, den: i128) -> i128 {
    if den <= 0 {
        return 0;
    }
    let shift = if shift > MAX_SHIFT { MAX_SHIFT } else { shift };
    let (Some(tq), Some(tr)) = (num.checked_div(den), num.checked_rem(den)) else {
        return 0;
    };
    let (q, mut rem) = if tr < 0 {
        (tq.wrapping_sub(1), tr.wrapping_add(den))
    } else {
        (tq, tr)
    };
    let max_q = i128::MAX.wrapping_shr(shift);
    let min_q = i128::MIN.wrapping_shr(shift);
    if q > max_q {
        return i128::MAX;
    }
    if q < min_q {
        return i128::MIN;
    }
    // `0 <= rem < den` throughout: `frac` accumulates `floor(rem * 2^shift / den)`.
    let mut frac = 0i128;
    let mut bit = 0u32;
    while bit < shift {
        frac = frac.wrapping_shl(1);
        let half_up = den.wrapping_sub(rem);
        if rem >= half_up {
            rem = rem.wrapping_sub(half_up);
            frac = frac.wrapping_add(1);
        } else {
            rem = rem.wrapping_add(rem);
        }
        bit = bit.saturating_add(1);
    }
    // `min_q <= q <= max_q` and `0 <= frac < 2^shift`, so neither operation wraps.
    q.wrapping_shl(shift).wrapping_add(frac)
}

#[cfg(test)]
mod tests {
    use super::{
        MAX_SHIFT, div_floor, div_floor_wide, mul_shift, rem_euclid_wide, root, saturate,
        scale_div_pow2,
    };

    #[test]
    fn rem_euclid_wide_maps_negative_and_extreme_values_into_range() {
        assert_eq!(rem_euclid_wide(0, 0), None);
        assert_eq!(rem_euclid_wide(-3, 3), Some(0));
        assert_eq!(rem_euclid_wide(-2, 3), Some(1));
        assert_eq!(rem_euclid_wide(-1, 3), Some(2));
        assert_eq!(rem_euclid_wide(0, 3), Some(0));
        assert_eq!(rem_euclid_wide(1, 3), Some(1));
        assert_eq!(rem_euclid_wide(i128::MIN, 3), Some(1));
        assert_eq!(rem_euclid_wide(i128::MAX, 3), Some(1));
    }

    #[test]
    fn root_is_the_largest_integer_whose_square_fits() {
        assert_eq!(
            (root(-5), root(0), root(1), root(2), root(3), root(4)),
            (0, 0, 1, 1, 1, 2)
        );
        // Around squares of every size, and at the largest number.
        for bits in 1..63u32 {
            for base in [
                (1i128 << bits) - 1,
                1i128 << bits,
                (1i128 << bits) + 12_345 % (1i128 << bits),
            ] {
                let square = base * base;
                assert_eq!(root(square), base);
                assert_eq!(root(square - 1), base - 1);
                assert_eq!(root(square + 2 * base), base);
                assert_eq!(root(square + 2 * base + 1), base + 1);
            }
        }
        let largest = root(i128::MAX);
        assert_eq!(largest, 13_043_817_825_332_782_212);
        assert!(largest.checked_mul(largest).is_some());
        assert!((largest + 1).checked_mul(largest + 1).is_none());
    }

    #[test]
    fn div_floor_rounds_toward_negative_infinity() {
        assert_eq!(div_floor(7, 2), 3);
        assert_eq!(div_floor(-7, 2), -4);
        assert_eq!(div_floor(-8, 2), -4);
        assert_eq!(div_floor(0, 5), 0);
        assert_eq!(div_floor(-1, 1_000_000), -1);
        assert_eq!(div_floor(i128::MIN, 1), i128::MIN);
        assert_eq!(
            div_floor(i128::MAX, i64::MAX),
            i128::MAX / i128::from(i64::MAX)
        );
    }

    #[test]
    fn div_floor_by_a_divisor_that_is_not_positive_is_zero() {
        assert_eq!(div_floor(100, 0), 0);
        assert_eq!(div_floor(100, -3), 0);
    }

    #[test]
    fn saturate_keeps_values_in_range_and_limits_the_rest() {
        assert_eq!(saturate(0), 0);
        assert_eq!(saturate(-5), -5);
        assert_eq!(saturate(i64::MAX as i128), i64::MAX);
        assert_eq!(saturate(i64::MAX as i128 + 1), i64::MAX);
        assert_eq!(saturate(i64::MIN as i128), i64::MIN);
        assert_eq!(saturate(i64::MIN as i128 - 1), i64::MIN);
    }

    #[test]
    fn mul_shift_rounds_to_nearest_with_ties_upward() {
        // 3 * 5 / 4 = 3.75
        assert_eq!(mul_shift(3, 5, 2), 4);
        // 3 * 3 / 4 = 2.25
        assert_eq!(mul_shift(3, 3, 2), 2);
        // 5 / 2 = 2.5 and -5 / 2 = -2.5: both ties go up.
        assert_eq!(mul_shift(5, 1, 1), 3);
        assert_eq!(mul_shift(-5, 1, 1), -2);
        // -15 / 4 = -3.75 and -9 / 4 = -2.25
        assert_eq!(mul_shift(-3, 5, 2), -4);
        assert_eq!(mul_shift(-3, 3, 2), -2);
    }

    #[test]
    fn mul_shift_without_shift_is_the_limited_product() {
        assert_eq!(mul_shift(7, -6, 0), -42);
        assert_eq!(mul_shift(i64::MAX, 2, 0), i64::MAX);
        assert_eq!(mul_shift(i64::MIN, 2, 0), i64::MIN);
        assert_eq!(mul_shift(i64::MIN, -1, 0), i64::MAX);
    }

    #[test]
    fn mul_shift_at_the_extremes_of_its_arguments() {
        // (2^63 - 1)^2 = 2^126 - 2^64 + 1, and that over 2^64 is 2^62 - 1 + 2^-64.
        assert_eq!(mul_shift(i64::MAX, i64::MAX, 64), (1 << 62) - 1);
        // (-2^63)^2 / 2^64 = 2^62 exactly.
        assert_eq!(mul_shift(i64::MIN, i64::MIN, 64), 1 << 62);
        // (-2^63)^2 / 2^63 = 2^63 is one above the largest value.
        assert_eq!(mul_shift(i64::MIN, i64::MIN, 63), i64::MAX);
        assert_eq!(mul_shift(i64::MIN, i64::MAX, 63), -i64::MAX);
    }

    #[test]
    fn mul_shift_treats_a_larger_shift_as_the_largest() {
        let expected = mul_shift(i64::MAX, i64::MIN, MAX_SHIFT);
        assert_eq!(mul_shift(i64::MAX, i64::MIN, MAX_SHIFT + 1), expected);
        assert_eq!(mul_shift(i64::MAX, i64::MIN, u32::MAX), expected);
    }

    #[test]
    fn div_floor_wide_rounds_toward_negative_infinity() {
        let big = 1i128 << 100;
        assert_eq!(div_floor_wide(7 * big + 5, big), 7);
        assert_eq!(div_floor_wide(-7 * big - 5, big), -8);
        assert_eq!(div_floor_wide(-8 * big, big), -8);
        assert_eq!(div_floor_wide(5, 0), 0);
        assert_eq!(div_floor_wide(5, -3), 0);
    }

    #[test]
    fn scale_div_pow2_is_exact_without_intermediate_overflow() {
        assert_eq!(scale_div_pow2(1, 32, 2), 1 << 31);
        assert_eq!(scale_div_pow2(1, 32, 3), (1i128 << 32) / 3);
        // Negative values round toward negative infinity.
        assert_eq!(scale_div_pow2(-1, 32, 3), -((1i128 << 32) / 3) - 1);
        assert_eq!(scale_div_pow2(-1, 32, 2), -(1i128 << 31));
        assert_eq!(scale_div_pow2(5, 32, 0), 0);
        assert_eq!(scale_div_pow2(5, 32, -4), 0);
        // Huge denominators near `i128::MAX` never overflow `2 * rem`.
        let huge_even = i128::MAX - 7;
        assert_eq!(
            scale_div_pow2(huge_even - 1, 64, huge_even),
            (1i128 << 64) - 1
        );
        assert_eq!(scale_div_pow2(huge_even / 2, 64, huge_even), 1i128 << 63);
        let huge_odd = i128::MAX - 6;
        assert_eq!(
            scale_div_pow2(huge_odd / 2, 64, huge_odd),
            (1i128 << 63) - 1
        );
        assert_eq!(scale_div_pow2(i128::MIN, 0, 1), i128::MIN);
        assert_eq!(scale_div_pow2(i128::MAX, 1, 1), i128::MAX);
        assert_eq!(scale_div_pow2(i128::MIN, 1, 1), i128::MIN);
        // Saturation at exact `max_q` / `min_q`.
        let max_q = i128::MAX >> 64;
        assert_eq!(scale_div_pow2(max_q, 64, 1), max_q << 64);
        assert_eq!(scale_div_pow2(max_q + 1, 64, 1), i128::MAX);
    }
}
