// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Fixed-point arithmetic.
//!
//! A fixed-point number is an integer that stands for a multiple of a
//! negative power of two: with 48 fractional bits, the integer `n` stands for
//! `n / 2^48`. Multiplying two such numbers gives a product with twice the
//! fractional bits, which [`mul_shift`] brings back.

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

#[cfg(test)]
mod tests {
    use super::{MAX_SHIFT, mul_shift, saturate};

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
}
