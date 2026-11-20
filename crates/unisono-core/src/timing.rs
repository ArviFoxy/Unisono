// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! When frames are due: from readings of clocks to positions in the stream.
//!
//! A frame is due when the sender's clock reads the frame's capture time plus
//! the level. A receiver turns a reading of its own clock into a reading of
//! the sender's with its estimate of the relation between the two, and that
//! into the position in the stream that is due then.

use crate::fixed::{div_floor, saturate};
use crate::relation::Line;

/// The number of nanoseconds in a second, and of parts in a billion.
const BILLION: i64 = 1_000_000_000;

/// A position in a stream: the index of a frame and a fraction of a frame
/// beyond it, in units of 2^-64 frame.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Position {
    /// The index of the last frame at or before the position.
    pub frame: u64,
    /// The distance from that frame to the position, in units of 2^-64
    /// frame.
    pub fraction: u64,
}

/// When the frames of a timeline are due, as a packet says it.
///
/// The frame `index` was captured at `capture` on the sender's clock, and
/// the frames after it follow at `rate` frames per second, faster by `drift`
/// parts per billion. A frame is due at its capture time plus the level,
/// which is `level` for the frame `index` and grows by `level_slope`
/// nanoseconds per second of stream.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Schedule {
    /// The index of a frame.
    pub index: u64,
    /// When that frame was captured.
    pub capture: i64,
    /// Frames per second.
    pub rate: u32,
    /// How much faster than `rate` the capture device runs against the
    /// sender's clock, in parts per billion.
    pub drift: i32,
    /// The latency that every receiver holds for that frame.
    pub level: i64,
    /// How the level changes, in nanoseconds per second of stream.
    pub level_slope: i32,
}

/// The reading of the sender's clock when the receiver's clock reads `time`.
///
/// `line` is the receiver's estimate of its clock minus the sender's, over
/// the sender's clock; it lies above the true difference by the smallest
/// delay of a packet, of which `path` is the receiver's estimate.
#[must_use]
pub fn sender_time(line: &Line, path: i64, time: i64) -> i64 {
    // The sender's reading `s` satisfies `s + line(s) = time + path`. With
    // `line(s) = value + rise / run * (s - line.time)` that is
    // `(s - line.time) * (run + rise) = (time + path - value - line.time) * run`.
    // Sums of four and of two 64-bit numbers: no wrapping.
    let ahead = saturate(
        (time as i128)
            .wrapping_add(path as i128)
            .wrapping_sub(line.value as i128)
            .wrapping_sub(line.time as i128),
    );
    let scale = saturate((line.run as i128).wrapping_add(line.rise as i128));
    let scaled = if scale > 0 {
        // A product of two 64-bit numbers: no wrapping.
        div_floor((ahead as i128).wrapping_mul(line.run as i128), scale)
    } else {
        // A slope of minus one or below relates no two clocks.
        ahead as i128
    };
    saturate((line.time as i128).wrapping_add(scaled))
}

/// The position in the stream that is due when the sender's clock reads
/// `time`, to 2^-32 frame. `None` when that is before frame 0 of the
/// timeline or beyond its last index, and when the schedule's drift or the
/// slope of its level is minus one or below, which is no rate.
#[must_use]
pub fn due(schedule: &Schedule, time: i64) -> Option<Position> {
    // Frames per nanosecond are `rate * pace / (BILLION * stretch)`.
    let pace = (BILLION as i128).wrapping_add(schedule.drift as i128);
    let stretch = (BILLION as i128).wrapping_add(schedule.level_slope as i128);
    if pace <= 0 || stretch <= 0 {
        return None;
    }
    let elapsed = saturate(
        (time as i128)
            .wrapping_sub(schedule.capture as i128)
            .wrapping_sub(schedule.level as i128),
    );
    // Below 2^32 * 2^32, and below 2^30 * 2^32: no wrapping, and the second
    // fits 64 bits.
    let frames_per = (schedule.rate as i128).wrapping_mul(pace);
    let divisor = saturate((BILLION as i128).wrapping_mul(stretch));
    // Below 2^63 * 2^64: no wrapping.
    let product = (elapsed as i128).wrapping_mul(frames_per);
    let whole = div_floor(product, divisor);
    // The remainder is below the divisor, so 32 more bits fit.
    let rest = product.wrapping_sub(whole.wrapping_mul(divisor as i128));
    let fraction = div_floor(rest.wrapping_shl(32), divisor);
    let frame = (schedule.index as i128).wrapping_add(whole);
    if frame < 0 || frame > u64::MAX as i128 {
        return None;
    }
    // Both are in range: the frame was checked, the fraction is below 2^32.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let position = Position {
        frame: frame as u64,
        fraction: (fraction as u64).wrapping_shl(32),
    };
    Some(position)
}

/// The distance from `from` to `to` in units of 2^-32 frame, limited to the
/// range of `i64`.
#[must_use]
pub fn distance(from: Position, to: Position) -> i64 {
    let frames = (to.frame as i128).wrapping_sub(from.frame as i128);
    let fractions =
        (to.fraction.wrapping_shr(32) as i128).wrapping_sub(from.fraction.wrapping_shr(32) as i128);
    // A difference of 64-bit numbers with 32 more bits: no wrapping.
    saturate(frames.wrapping_shl(32).wrapping_add(fractions))
}

/// The position `frames` output frames after `start`, when each output frame
/// is one frame and `step` units of 2^-64 frame after the one before. It
/// stops at the largest index.
#[must_use]
pub fn advance(start: Position, frames: u32, step: i64) -> Position {
    // 2^64 and a product of a 32-bit and a 64-bit number: no wrapping.
    let moved = (start.fraction as i128).wrapping_add((frames as i128).wrapping_mul(step as i128));
    let carry = moved.wrapping_shr(64);
    // A step is at least minus half a frame, so the frame does not go down.
    let frame = (start.frame as i128)
        .wrapping_add(frames as i128)
        .wrapping_add(carry);
    if frame > u64::MAX as i128 {
        return Position {
            frame: u64::MAX,
            fraction: u64::MAX,
        };
    }
    // The frame is in range, and the fraction is the low 64 bits.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let position = Position {
        frame: frame as u64,
        fraction: moved as u64,
    };
    position
}

#[cfg(test)]
mod tests {
    use super::{Position, Schedule, advance, distance, due, sender_time};
    use crate::relation::Line;

    fn schedule() -> Schedule {
        Schedule {
            index: 4_800,
            capture: 1_000_000_000,
            rate: 48_000,
            drift: 0,
            level: 20_000_000,
            level_slope: 0,
        }
    }

    #[test]
    fn the_sender_s_reading_solves_the_line() {
        // The receiver's clock is 5 ms ahead at sender time 0 and gains 100
        // microseconds per second.
        let line = Line {
            time: 0,
            value: 5_000_000,
            rise: 100_000,
            run: 1_000_000_000,
        };
        for sender in [0i64, 1, 999_999_999, 12_345_678_901, -7_000_000_000] {
            let receiver = sender + line.eval(sender);
            let found = sender_time(&line, 0, receiver);
            assert!((found - sender).abs() <= 1, "{sender} gave {found}");
        }
        // The line lies above the true difference by the delay of the path.
        assert_eq!(sender_time(&line, 250_000, 5_000_000 - 250_000), 0);
    }

    #[test]
    fn clocks_far_apart_are_related_exactly() {
        // A difference of an hour and a slope of 100 parts per million: a
        // first guess that ignores the slope would be wrong by 360 ms.
        let line = Line {
            time: 50_000_000_000,
            value: 3_600_000_000_000,
            rise: 100_000,
            run: 1_000_000_000,
        };
        let sender = 60_000_000_000i64;
        let receiver = sender + line.eval(sender);
        assert!((sender_time(&line, 0, receiver) - sender).abs() <= 1);
    }

    #[test]
    fn a_frame_is_due_at_its_capture_time_plus_the_level() {
        let schedule = schedule();
        let at = |time| due(&schedule, time).expect("in the timeline");
        assert_eq!(
            at(1_020_000_000),
            Position {
                frame: 4_800,
                fraction: 0
            }
        );
        // A second later, a second of frames further on.
        assert_eq!(at(2_020_000_000).frame, 52_800);
        // Half a frame is 10,416 and two thirds nanoseconds; after 10,417
        // the position is just beyond the middle between two frames.
        let half = at(1_020_000_000 + 10_417);
        assert_eq!(half.frame, 4_800);
        assert!(half.fraction > 1 << 63 && half.fraction < (1 << 63) + (1 << 50));
    }

    #[test]
    fn nothing_is_due_before_the_first_frame() {
        let schedule = schedule();
        // Frame 0 was captured a tenth of a second before frame 4,800.
        assert_eq!(due(&schedule, 920_000_000).map(|p| p.frame), Some(0));
        assert_eq!(due(&schedule, 919_999_000), None);
    }

    #[test]
    fn drift_and_a_moving_level_change_the_pace() {
        let mut schedule = schedule();
        schedule.drift = 1_000_000;
        // A device that runs a thousandth fast captures 48,048 frames a second.
        let later = due(&schedule, 2_020_000_000).expect("in the timeline");
        assert_eq!(later.frame, 4_800 + 48_048);
        schedule.drift = 0;
        schedule.level_slope = 1_000_000;
        // A level that grows by a millisecond per second of stream: a second
        // of stream takes 1.001 seconds, so after a second 47,952 frames and
        // a bit are due.
        let later = due(&schedule, 2_020_000_000).expect("in the timeline");
        assert_eq!(later.frame, 4_800 + 47_952);
        schedule.level_slope = -1_000_000_000;
        assert_eq!(due(&schedule, 2_020_000_000), None);
    }

    #[test]
    fn distance_and_advance_agree() {
        let start = Position {
            frame: 1_000,
            fraction: 3 << 62,
        };
        // 256 frames at a step a millionth above one.
        let step = (1i64 << 44) + 12_345;
        let end = advance(start, 256, step);
        // The same in units of 2^-64 frame from frame 0.
        let units =
            (1_000u128 << 64) + (3u128 << 62) + 256 * ((1u128 << 64) + (1u128 << 44) + 12_345);
        assert_eq!(u128::from(end.frame), units >> 64);
        assert_eq!(u128::from(end.fraction), units & u128::from(u64::MAX));
        // The distance drops the low 32 bits of each fraction.
        let expected = (units >> 32) - ((1_000u128 << 32) + (3u128 << 30));
        assert_eq!(u128::try_from(distance(start, end)), Ok(expected));
        assert_eq!(distance(end, start), -distance(start, end));
    }

    #[test]
    fn a_step_below_one_frame_moves_forward_more_slowly() {
        let first = Position {
            frame: 0,
            fraction: 0,
        };
        // The smallest step is half a frame.
        assert_eq!(
            advance(first, 3, i64::MIN),
            Position {
                frame: 1,
                fraction: 1 << 63
            }
        );
    }

    #[test]
    fn advancing_stops_at_the_largest_index() {
        let last = Position {
            frame: u64::MAX,
            fraction: 5,
        };
        assert_eq!(advance(last, 10, 0).frame, u64::MAX);
    }
}
