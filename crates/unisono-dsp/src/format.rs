// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Wire PCM sample encoding and decoding (little-endian signed 16-bit and
//! 24-bit integers <-> normalized `f32` in `[-1.0, 1.0)`).
//!
//! Both integer widths map losslessly into `f32` (`v / 2^(b - 1)`), so
//! decode -> encode round-trips bit-for-bit. Encoding rounds ties to even and
//! clamps out-of-range floats without dither.

/// Reads signed 16-bit samples from `bytes` into `samples`, and returns how
/// many: the number of whole samples in `bytes`, or the length of `samples`
/// when that is less.
pub fn from_signed16(bytes: &[u8], samples: &mut [f32]) -> usize {
    let mut read = 0;
    for (pair, sample) in bytes.as_chunks::<2>().0.iter().zip(samples.iter_mut()) {
        *sample = f32::from(i16::from_le_bytes(*pair)) * (1.0 / 32_768.0);
        read += 1;
    }
    read
}

/// Reads signed 24-bit samples of three bytes each from `bytes` into
/// `samples`, and returns how many: the number of whole samples in `bytes`,
/// or the length of `samples` when that is less.
pub fn from_signed24(bytes: &[u8], samples: &mut [f32]) -> usize {
    let mut read = 0;
    for (triple, sample) in bytes.as_chunks::<3>().0.iter().zip(samples.iter_mut()) {
        let [low, middle, high] = *triple;
        // The three bytes are the upper three of a 32-bit number, whose
        // shift to the right then carries the sign down.
        let value = i32::from_le_bytes([0, low, middle, high]) >> 8;
        #[allow(clippy::cast_precision_loss)] // 24 digits, which an f32 holds exactly
        let value = value as f32;
        *sample = value * (1.0 / 8_388_608.0);
        read += 1;
    }
    read
}

/// Writes `samples` into `bytes` as signed 16-bit samples, and returns how
/// many: the length of `samples`, or the number of whole samples that fit
/// `bytes` when that is less. A sample that is not a number is written as
/// zero.
pub fn to_signed16(samples: &[f32], bytes: &mut [u8]) -> usize {
    let mut written = 0;
    for (sample, pair) in samples.iter().zip(bytes.as_chunks_mut::<2>().0.iter_mut()) {
        let value = whole(*sample, 32_768.0, -32_768.0, 32_767.0);
        // Within the range of an i16 after the clamp.
        *pair = i16::try_from(value).unwrap_or(0).to_le_bytes();
        written += 1;
    }
    written
}

/// Writes `samples` into `bytes` as signed 24-bit samples of three bytes
/// each, and returns how many: the length of `samples`, or the number of
/// whole samples that fit `bytes` when that is less. A sample that is not a
/// number is written as zero.
pub fn to_signed24(samples: &[f32], bytes: &mut [u8]) -> usize {
    let mut written = 0;
    for (sample, triple) in samples.iter().zip(bytes.as_chunks_mut::<3>().0.iter_mut()) {
        let [low, middle, high, _] =
            whole(*sample, 8_388_608.0, -8_388_608.0, 8_388_607.0).to_le_bytes();
        *triple = [low, middle, high];
        written += 1;
    }
    written
}

/// `sample * scale` as the nearest whole number from `lowest` to `highest`.
fn whole(sample: f32, scale: f32, lowest: f32, highest: f32) -> i32 {
    // The scale is a power of two, so the product is exact.
    let scaled = (sample * scale).round_ties_even().clamp(lowest, highest);
    // A whole number within 24 digits after the clamp; what is not a number
    // becomes zero.
    #[allow(clippy::cast_possible_truncation)]
    let value = scaled as i32;
    value
}

#[cfg(test)]
mod tests {
    use super::{from_signed16, from_signed24, to_signed16, to_signed24};

    /// Detects a wrong byte order, a wrong scale and a lost sign.
    #[test]
    fn bytes_are_read_least_significant_first_with_their_sign() {
        let mut samples = [0.0f32; 4];
        assert_eq!(
            from_signed16(
                &[0x00, 0x80, 0xff, 0x7f, 0x00, 0x01, 0xff, 0xff],
                &mut samples
            ),
            4
        );
        assert_eq!(
            samples,
            [-1.0, 32_767.0 / 32_768.0, 256.0 / 32_768.0, -1.0 / 32_768.0]
        );
        assert_eq!(
            from_signed24(
                &[
                    0x00, 0x00, 0x80, 0xff, 0xff, 0x7f, 0x00, 0x01, 0x00, 0xff, 0xff, 0xff
                ],
                &mut samples
            ),
            4
        );
        assert_eq!(
            samples,
            [
                -1.0,
                8_388_607.0 / 8_388_608.0,
                256.0 / 8_388_608.0,
                -1.0 / 8_388_608.0
            ]
        );
    }

    /// Every 16-bit and every 24-bit sample must survive being read and
    /// written again, or audio that is only passed on would be changed.
    #[test]
    fn every_sample_is_returned_by_reading_and_writing_it() {
        let mut samples = [0.0f32; 1];
        for value in i16::MIN..=i16::MAX {
            let bytes = value.to_le_bytes();
            let mut back = [0u8; 2];
            assert_eq!(from_signed16(&bytes, &mut samples), 1);
            assert_eq!(to_signed16(&samples, &mut back), 1);
            assert_eq!(back, bytes, "{value}");
        }
        // 256 blocks of 65 536 samples, to keep the test short.
        let mut bytes = vec![0u8; 3 * 65_536];
        let mut back = vec![0u8; 3 * 65_536];
        let mut samples = vec![0.0f32; 65_536];
        for high in 0..=u8::MAX {
            for (low, triple) in (0..=u16::MAX).zip(bytes.as_chunks_mut::<3>().0.iter_mut()) {
                let [low, middle] = low.to_le_bytes();
                *triple = [low, middle, high];
            }
            assert_eq!(from_signed24(&bytes, &mut samples), 65_536);
            assert_eq!(to_signed24(&samples, &mut back), 65_536);
            assert!(back == bytes, "high byte {high}");
        }
    }

    /// Detects values outside the range wrapping around to the other end,
    /// which would turn a slightly too loud sample into a full-scale click.
    #[test]
    fn values_outside_the_range_go_to_its_nearest_end() {
        let samples = [
            1.0,
            2.0,
            f32::INFINITY,
            -1.0,
            -2.0,
            f32::NEG_INFINITY,
            f32::NAN,
        ];
        let mut bytes = [0u8; 14];
        assert_eq!(to_signed16(&samples, &mut bytes), 7);
        let words: Vec<i16> = bytes
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| i16::from_le_bytes(*pair))
            .collect();
        assert_eq!(
            words,
            [32_767, 32_767, 32_767, -32_768, -32_768, -32_768, 0]
        );
        let mut bytes = [0u8; 21];
        assert_eq!(to_signed24(&samples, &mut bytes), 7);
        let words: Vec<i32> = bytes
            .as_chunks::<3>()
            .0
            .iter()
            .map(|triple| i32::from_le_bytes([0, triple[0], triple[1], triple[2]]) >> 8)
            .collect();
        assert_eq!(
            words,
            [
                8_388_607, 8_388_607, 8_388_607, -8_388_608, -8_388_608, -8_388_608, 0
            ]
        );
    }

    /// Detects rounding toward zero or away from it: a value half-way
    /// between two whole numbers goes to the even one.
    #[test]
    fn values_between_two_whole_numbers_go_to_the_nearest() {
        let samples = [0.5, 1.5, 2.5, -0.5, -1.5, 0.49, 0.51, -0.51].map(|x: f32| x / 32_768.0);
        let mut bytes = [0u8; 16];
        assert_eq!(to_signed16(&samples, &mut bytes), 8);
        let words: Vec<i16> = bytes
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| i16::from_le_bytes(*pair))
            .collect();
        assert_eq!(words, [0, 2, 2, 0, -2, 0, 1, -1]);
    }

    #[test]
    fn only_whole_samples_that_fit_are_converted() {
        let mut samples = [9.0f32; 3];
        assert_eq!(from_signed16(&[1, 0, 2, 0, 3], &mut samples), 2);
        assert_eq!(samples[2].to_bits(), 9.0f32.to_bits());
        assert_eq!(from_signed24(&[0; 12], &mut samples), 3);
        assert_eq!(from_signed24(&[0; 2], &mut samples), 0);
        let mut bytes = [7u8; 5];
        assert_eq!(to_signed16(&[0.0; 4], &mut bytes), 2);
        assert_eq!(bytes, [0, 0, 0, 0, 7]);
        assert_eq!(to_signed24(&[0.0; 4], &mut bytes), 1);
        assert_eq!(to_signed16(&[], &mut bytes), 0);
    }
}
