// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Positions in a stream and the step between two of them, as exact numbers.
//!
//! A position has 64 binary digits after the point, and a step is added to
//! it as an integer, so a sum of any number of steps is exact: the position
//! after a day of output is the first position plus the sum of the steps, to
//! the last digit.

/// A position in a stream: the index of a frame and a fraction of a frame
/// beyond it, in units of 2^-64 frame.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Position {
    frame: u64,
    fraction: u64,
}

impl Position {
    /// The position `fraction * 2^-64` frames beyond the frame `frame`.
    #[must_use]
    pub const fn new(frame: u64, fraction: u64) -> Position {
        Position { frame, fraction }
    }

    /// The position of the frame `frame` itself.
    #[must_use]
    pub const fn at_frame(frame: u64) -> Position {
        Position { frame, fraction: 0 }
    }

    /// The index of the last frame at or before the position.
    #[must_use]
    pub const fn frame(self) -> u64 {
        self.frame
    }

    /// The distance from that frame to the position, in units of 2^-64 frame.
    #[must_use]
    pub const fn fraction(self) -> u64 {
        self.fraction
    }

    /// The position as a count of units of 2^-64 frame.
    pub(crate) const fn units(self) -> u128 {
        ((self.frame as u128) << 64) | self.fraction as u128
    }

    /// The position that is `units` units of 2^-64 frame from frame 0.
    #[allow(clippy::cast_possible_truncation)] // the two halves are taken apart on purpose
    pub(crate) const fn from_units(units: u128) -> Position {
        Position {
            frame: (units >> 64) as u64,
            fraction: units as u64,
        }
    }

    /// The position `frames` steps of size `step` further on: the position
    /// of the output frame that follows `frames` output frames at that step.
    /// `None` when it lies beyond the largest position.
    #[must_use]
    pub fn advance(self, step: Step, frames: u64) -> Option<Position> {
        let distance = step.units().checked_mul(u128::from(frames))?;
        let units = self.units().checked_add(distance)?;
        Some(Position::from_units(units))
    }
}

/// The distance in input frames from one output frame to the next: one frame
/// plus an offset in units of 2^-64 frame.
///
/// One part per billion is about 1.8e10 units, so a rate correction is
/// represented far more finely than any clock can be measured. A positive
/// offset reads the input faster than the output is produced, a negative one
/// slower. The offset is at most [`Step::LARGEST_OFFSET`] either way, because
/// the filter is made for steps near one.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Step {
    offset: i64,
}

impl Step {
    /// The largest offset either way: 2^-8 frame per frame, which is 0.39 %.
    pub const LARGEST_OFFSET: i64 = 1 << 56;

    /// One input frame for every output frame.
    pub const UNITY: Step = Step { offset: 0 };

    /// The step of one frame plus `offset` units of 2^-64 frame, or `None`
    /// when the offset is beyond [`Step::LARGEST_OFFSET`] either way.
    #[must_use]
    pub const fn new(offset: i64) -> Option<Step> {
        if offset > Step::LARGEST_OFFSET || offset < -Step::LARGEST_OFFSET {
            None
        } else {
            Some(Step { offset })
        }
    }

    /// The step of one frame plus `offset` units of 2^-64 frame, with the
    /// offset brought to the nearest permitted one.
    #[must_use]
    pub fn clamped(offset: i64) -> Step {
        Step {
            offset: offset.clamp(-Step::LARGEST_OFFSET, Step::LARGEST_OFFSET),
        }
    }

    /// The step that is `parts` parts per billion more than one frame,
    /// rounded to the nearest unit and brought to the nearest permitted
    /// offset.
    #[must_use]
    pub fn from_parts_per_billion(parts: i64) -> Step {
        const BILLION: i128 = 1_000_000_000;
        // Beyond this the result is clamped anyway, and the product below
        // stays far from the range of its type.
        let parts = i128::from(parts.clamp(-4_000_000, 4_000_000));
        let offset = ((parts << 64) + BILLION / 2).div_euclid(BILLION);
        Step::clamped(i64::try_from(offset).unwrap_or(if offset < 0 { i64::MIN } else { i64::MAX }))
    }

    /// The offset from one frame, in units of 2^-64 frame.
    #[must_use]
    pub const fn offset(self) -> i64 {
        self.offset
    }

    /// The whole step in units of 2^-64 frame.
    pub(crate) const fn units(self) -> u128 {
        // The offset is far smaller than one frame, so the sum is positive.
        ((1i128 << 64) + self.offset as i128).cast_unsigned()
    }
}

#[cfg(test)]
mod tests {
    use super::{Position, Step};

    #[test]
    fn a_step_beyond_the_limit_is_refused_or_clamped() {
        assert!(Step::new(Step::LARGEST_OFFSET).is_some());
        assert!(Step::new(-Step::LARGEST_OFFSET).is_some());
        assert!(Step::new(Step::LARGEST_OFFSET + 1).is_none());
        assert!(Step::new(-Step::LARGEST_OFFSET - 1).is_none());
        assert_eq!(Step::clamped(i64::MAX).offset(), Step::LARGEST_OFFSET);
        assert_eq!(Step::clamped(i64::MIN).offset(), -Step::LARGEST_OFFSET);
        assert_eq!(
            Step::from_parts_per_billion(i64::MAX).offset(),
            Step::LARGEST_OFFSET
        );
        assert_eq!(
            Step::from_parts_per_billion(i64::MIN).offset(),
            -Step::LARGEST_OFFSET
        );
    }

    /// Parts per billion are converted by an exact rational: `p` parts are
    /// `p * 2^64 / 10^9` units, to the nearest unit.
    #[test]
    fn parts_per_billion_are_rounded_to_the_nearest_unit() {
        for parts in [-3_906_250i64, -1_000_000, -1, 0, 1, 7, 1_000_000, 3_906_250] {
            let offset = i128::from(Step::from_parts_per_billion(parts).offset());
            let exact_times_billion = i128::from(parts) << 64;
            let error_times_billion = offset * 1_000_000_000 - exact_times_billion;
            assert!(
                error_times_billion.abs() * 2 <= 1_000_000_000,
                "{parts} parts per billion gave {offset} units"
            );
        }
        // 3 906 250 parts per billion are exactly 2^-8.
        assert_eq!(
            Step::from_parts_per_billion(3_906_250).offset(),
            Step::LARGEST_OFFSET
        );
    }

    /// Advancing in one call or frame by frame gives the same position, and
    /// that position is the product computed in whole numbers.
    #[test]
    fn advancing_is_exact_and_additive() {
        let step = Step::from_parts_per_billion(-123_457);
        let start = Position::new(41, 0xdead_beef_0123_4567);
        let mut walked = start;
        for _ in 0..10_000 {
            walked = walked.advance(step, 1).expect("in range");
        }
        assert_eq!(start.advance(step, 10_000), Some(walked));
        let offset = i128::from(step.offset());
        let expected = (41i128 << 64) + 0xdead_beef_0123_4567 + 10_000 * ((1i128 << 64) + offset);
        assert_eq!(
            walked,
            Position::new(
                u64::try_from(expected >> 64).expect("in range"),
                u64::try_from(expected & i128::from(u64::MAX)).expect("in range")
            )
        );
    }

    #[test]
    fn a_position_beyond_the_largest_does_not_exist() {
        let last = Position::new(u64::MAX, u64::MAX);
        assert_eq!(last.advance(Step::UNITY, 0), Some(last));
        assert_eq!(last.advance(Step::UNITY, 1), None);
        assert_eq!(Position::at_frame(5).advance(Step::UNITY, u64::MAX), None);
        assert_eq!(
            Position::at_frame(5).advance(Step::UNITY, u64::MAX - 5),
            Some(Position::at_frame(u64::MAX))
        );
    }

    #[test]
    fn positions_are_ordered_as_numbers() {
        assert!(Position::new(3, u64::MAX) < Position::new(4, 0));
        assert!(Position::new(4, 1) > Position::new(4, 0));
    }
}
