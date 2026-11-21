// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The regulator: where in the stream a receiver reads, cycle by cycle of its
//! device.
//!
//! The schedule says which position of the stream is due at the start and at
//! the end of a cycle. The regulator keeps the position at which the
//! receiver actually reads, and the pace at which it read in the cycle
//! before. Before a cycle it knows two distances:
//!
//! - `behind`, by which the position is behind the schedule;
//! - `ahead`, by which the cycle would read further than the schedule
//!   advances over it, if it kept the pace of the cycle before.
//!
//! The cycle then reads
//!
//! ```text
//! d^2 ahead + a^2 d behind
//! ```
//!
//! further than the schedule advances, where `a` is the gain per second
//! times the length of the cycle and `d`, between 0 and 1, is the smaller
//! root of `d + 1/d = (a^2 + sqrt(a^4 + 16)) / 2`. Of all ways to choose the
//! pace of each cycle from what is known before it, this one makes the sum
//! over the cycles of `a^4 behind^2` and the squared change of the pace
//! smallest, whether the schedule holds still or is revised between the
//! cycles in ways that cannot be foreseen (`docs/model.md`). `a^4` is the
//! weight of the timing error against the weight of a change of the pace:
//! the gain per second is the fourth root of the first over the second.
//!
//! A schedule whose own pace changes is followed in the same way: the pace
//! that was read is held against the new schedule, and the difference
//! shrinks by `d^2` in each cycle.
//!
//! The pace as a whole stays within a limit. A distance too large for that
//! is not played away: the position jumps to the schedule.
//!
//! A jump can go back. That replays nothing, because the frames that a
//! receiver has given to its device are behind its playhead and are not
//! given again: until the position reaches the playhead the receiver plays
//! silence.

use crate::fixed::{div_floor, div_floor_wide, root, saturate};
use crate::timing::{Position, Step, advance, distance};

/// The number of nanoseconds in a second, and of parts in a billion.
const BILLION: i64 = 1_000_000_000;

/// The largest gain of one cycle, in units of 2^-32: one.
const LARGEST_GAIN: i128 = 4_294_967_296;

/// Sixteen, in units of 2^-64: 2^68.
const SIXTEEN: i128 = 295_147_905_179_352_825_856;

/// The longest cycle that the gain is computed for, in nanoseconds: 2^40.
const LONGEST_CYCLE: i64 = 1_099_511_627_776;

/// The largest limit of the pace, in parts per billion: three in a thousand.
const LARGEST_LIMIT: u32 = 3_000_000;

/// One frame in the units of a step, which are 2^-64 frame: 2^64.
const FRAME: i128 = 18_446_744_073_709_551_616;

/// One frame in the units of a correction, which are 2^-48 frame: 2^48.
const FRAME_IN_CORRECTIONS: i128 = 281_474_976_710_656;

/// What a number is multiplied by to give it 16 more fractional bits: 2^16.
const SIXTEEN_BITS: i128 = 65_536;

/// The settings of a regulator.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Regulation {
    /// How fast a distance to the schedule is removed: the gain per second,
    /// in units of 2^-16.
    pub gain: u32,
    /// By how much the pace may differ from one frame of the stream for each
    /// frame of the device, in parts per billion. A limit above three in a
    /// thousand counts as three in a thousand: the resampler takes steps
    /// within four in a thousand of one frame.
    pub limit: u32,
    /// The distance to the schedule, in frames, beyond which the position
    /// jumps or waits instead of the pace changing.
    pub jump: u32,
}

/// What a receiver plays in one cycle of its device.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Plan {
    /// The number of output frames taken from the stream. It is zero when
    /// nothing is due, and the cycle is silent then.
    pub frames: u32,
    /// The position in the stream of the first of them.
    pub start: Position,
    /// Each further output frame is taken this step after the one before.
    pub step: Step,
    /// Whether the position jumped to the schedule at the start of this
    /// cycle, so that the cycle does not go on where the one before ended.
    pub jumped: bool,
}

/// The two numbers of the law for a cycle.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
struct Gains {
    /// What the distance `ahead` is multiplied by, in units of 2^-32: the
    /// square of `d`.
    ahead: i128,
    /// What the distance `behind` is multiplied by, in units of 2^-48:
    /// `a^2 d`.
    behind: i128,
}

/// The regulator of one receiver.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Player {
    regulation: Regulation,
    /// Whether a position is held.
    running: bool,
    /// The position of the next output frame.
    position: Position,
    /// The pace of the cycle before: the offset of its step, in units of
    /// 2^-64 frame for each output frame.
    pace: i64,
    /// The slope of the level in the cycle before, in nanoseconds per
    /// second of stream.
    slope: i32,
}

impl Player {
    /// A regulator that holds no position yet.
    #[must_use]
    pub fn new(regulation: Regulation) -> Self {
        Player {
            regulation,
            running: false,
            position: Position {
                frame: 0,
                fraction: 0,
            },
            pace: 0,
            slope: 0,
        }
    }

    /// Forgets the position, as at the start of a timeline. The next cycle
    /// starts at the schedule.
    pub fn stop(&mut self) {
        self.running = false;
        self.pace = 0;
        self.slope = 0;
    }

    /// The position of the next output frame, if one is held.
    #[must_use]
    pub fn position(&self) -> Option<Position> {
        if self.running {
            Some(self.position)
        } else {
            None
        }
    }

    /// The gain of a cycle of `duration` nanoseconds, in units of 2^-32.
    fn gain(&self, duration: i64) -> i128 {
        let span = if duration < 0 {
            0
        } else if duration > LONGEST_CYCLE {
            LONGEST_CYCLE
        } else {
            duration
        };
        // 32 bits, 40 bits and 16 bits: no wrapping.
        let scaled = (self.regulation.gain as i128)
            .wrapping_mul(span as i128)
            .wrapping_shl(16);
        let gain = div_floor(scaled, BILLION);
        if gain > LARGEST_GAIN {
            LARGEST_GAIN
        } else {
            gain
        }
    }

    /// The gains of the law for a cycle of `duration` nanoseconds.
    ///
    /// With `a` the gain of the cycle, `y = (a^2 + sqrt(a^4 + 16)) / 2` is
    /// the sum of `d` and its inverse, so `d = (y - sqrt(y^2 - 4)) / 2`, and
    /// `y^2 - 4 = a^2 y`, which is taken in place of the difference of two
    /// numbers that are nearly equal for a small `a`.
    fn gains(&self, duration: i64) -> Gains {
        let gain = self.gain(duration);
        // `a^2` in units of 2^-64, at most 2^64, and in units of 2^-32.
        let square = gain.wrapping_mul(gain);
        let coarse = square.wrapping_shr(32);
        // The square root of `a^4 + 16`, then `y`, both in units of 2^-32
        // and below 2^35. Next to 16, `a^4` needs no more than those units.
        let wide = root(coarse.wrapping_mul(coarse).wrapping_add(SIXTEEN));
        let sum = coarse.wrapping_add(wide).wrapping_shr(1);
        // The square root of `a^2 y`, of at most 99 bits, in units of 2^-48:
        // for a small `a` it is small, and `d` is one less half of it.
        let spread = root(square.wrapping_mul(sum));
        // `d` in units of 2^-48, at most 2^48.
        let modulus = sum.wrapping_shl(16).wrapping_sub(spread).wrapping_shr(1);
        // Products of at most 97 and 113 bits: nothing wraps.
        Gains {
            ahead: modulus.wrapping_mul(modulus).wrapping_shr(64),
            behind: square.wrapping_mul(modulus).wrapping_shr(64),
        }
    }

    /// How much further than the schedule advances a cycle of `frames`
    /// output frames would read at the pace of the cycle before, when the
    /// schedule advances by `scheduled` units of 2^-32 frame over it and its
    /// level changes by `slope` nanoseconds per second of stream; in units
    /// of 2^-48 frame.
    ///
    /// The slope of the level is announced with the frames it applies to, so
    /// a change of it is no revision of the schedule. The pace of the cycle
    /// before is therefore first carried over to the new slope: a second of
    /// stream takes a second and the slope, and the pace is the inverse of
    /// that.
    fn ahead(&self, frames: u32, scheduled: i64, slope: i32) -> i64 {
        // 32 bits and 49, 32 bits and 64, 64 bits and 16: no wrapping.
        let read = (frames as i128)
            .wrapping_mul(FRAME_IN_CORRECTIONS)
            .wrapping_add(
                (frames as i128)
                    .wrapping_mul(self.pace as i128)
                    .wrapping_shr(16),
            );
        let before = (BILLION as i128).wrapping_add(self.slope as i128);
        let now = (BILLION as i128).wrapping_add(slope as i128);
        let carried = if before > 0 && now > 0 {
            // 82 bits and 32: no wrapping.
            div_floor_wide(read.wrapping_mul(before), now)
        } else {
            read
        };
        saturate(carried.wrapping_sub((scheduled as i128).wrapping_mul(SIXTEEN_BITS)))
    }

    /// How much further than the schedule advances the next cycle, of
    /// `duration` nanoseconds, is to read, in units of 2^-48 frame: when the
    /// position is `behind` the schedule by that many units of 2^-32 frame,
    /// and the cycle would read `ahead` units of 2^-48 frame further than the
    /// schedule advances at the pace of the cycle before.
    fn regulate(&self, behind: i64, ahead: i64, duration: i64) -> i64 {
        let gains = self.gains(duration);
        // Numbers of at most 33 and 64 bits, and of 49 and 64 bits: no
        // product wraps.
        let kept = gains.ahead.wrapping_mul(ahead as i128).wrapping_shr(32);
        let added = gains.behind.wrapping_mul(behind as i128).wrapping_shr(32);
        saturate(kept.wrapping_add(added))
    }

    /// The largest step either way: the limit of the pace, in units of 2^-64
    /// frame for each output frame.
    fn reach(&self) -> i128 {
        let limit = if self.regulation.limit > LARGEST_LIMIT {
            LARGEST_LIMIT
        } else {
            self.regulation.limit
        };
        // 22 bits and 65: no wrapping.
        div_floor((limit as i128).wrapping_mul(FRAME), BILLION)
    }

    /// The step of a cycle of `frames` output frames that is to read `wanted`
    /// units of 2^-48 frame further than the schedule advances over it, which
    /// is by `scheduled` units of 2^-32 frame: the step that does so, brought
    /// within the limit of the pace.
    fn step(&self, wanted: i64, frames: u32, scheduled: i64) -> Step {
        let reach = self.reach();
        // How much further than one frame for each output frame the cycle is
        // to read, in units of 2^-48 frame. 64 bits and 16, 64 bits, 32 bits
        // and 49, and then 16 more: no wrapping.
        let beyond = (scheduled as i128)
            .wrapping_mul(SIXTEEN_BITS)
            .wrapping_add(wanted as i128)
            .wrapping_sub((frames as i128).wrapping_mul(FRAME_IN_CORRECTIONS));
        let step = div_floor(beyond.wrapping_mul(SIXTEEN_BITS), frames as i64);
        let limited = if step > reach {
            saturate(reach)
        } else if step < 0i128.wrapping_sub(reach) {
            saturate(0i128.wrapping_sub(reach))
        } else {
            saturate(step)
        };
        Step::clamped(limited)
    }

    /// Plays `frames` output frames from the position on, when the schedule
    /// advances by `scheduled` over them and the position is `behind` it,
    /// both in units of 2^-32 frame, and the cycle would read `ahead` units
    /// of 2^-48 frame further than the schedule advances at the pace of the
    /// cycle before.
    fn play(
        &mut self,
        frames: u32,
        scheduled: i64,
        behind: i64,
        ahead: i64,
        duration: i64,
    ) -> (Position, Step) {
        let start = self.position;
        let step = self.step(self.regulate(behind, ahead, duration), frames, scheduled);
        // The pace that is kept is that of the step taken, and not of the
        // step that was wanted: beyond the limit the two differ, and the
        // distance to the schedule changes by the first.
        self.pace = step.offset();
        self.position = advance(start, frames, step.offset());
        (start, step)
    }

    /// Whether the position is to jump to the schedule, from which it is
    /// `behind` by that many units of 2^-32 frame: when none is held, and
    /// when the distance either way is beyond the setting.
    fn jumps(&self, behind: i64) -> bool {
        if !self.running {
            return true;
        }
        // 32 bits and 32 more: no wrapping.
        let jump = (self.regulation.jump as i128).wrapping_shl(32);
        let wide = behind as i128;
        wide > jump || wide < 0i128.wrapping_sub(jump)
    }

    /// Plans one cycle of the device, of `frames` output frames that take
    /// `duration` nanoseconds. `now` is the position that is due when the
    /// cycle's first output frame leaves the device, and `then` the position
    /// due when the frame after its last one does. `slope` is the slope of
    /// the schedule's level, in nanoseconds per second of stream.
    pub fn cycle(
        &mut self,
        now: Position,
        then: Position,
        frames: u32,
        duration: i64,
        slope: i32,
    ) -> Plan {
        let scheduled = distance(now, then);
        if frames == 0 || scheduled <= 0 {
            // A schedule that stands still or runs backwards gives nothing
            // to play.
            return Plan {
                frames: 0,
                start: self.position,
                step: Step::UNITY,
                jumped: false,
            };
        }
        let behind = distance(self.position, now);
        let jumped = self.jumps(behind);
        // After a jump the position is on the schedule, and the pace of the
        // cycle before counts as the schedule's.
        let (behind, ahead) = if jumped {
            self.running = true;
            self.position = now;
            (0, 0)
        } else {
            (behind, self.ahead(frames, scheduled, slope))
        };
        self.slope = slope;
        let (start, step) = self.play(frames, scheduled, behind, ahead, duration);
        Plan {
            frames,
            start,
            step,
            jumped,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Plan, Player, Regulation};
    use crate::timing::{Position, Step, advance, distance};

    /// A regulator with a gain of four per second, a limit of a thousandth
    /// and a jump beyond 240 frames.
    fn player() -> Player {
        Player::new(Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: 240,
        })
    }

    const FRAMES: u32 = 256;
    /// 256 frames at 48,000 frames per second, in nanoseconds.
    const DURATION: i64 = 5_333_333;

    fn at(frame: u64) -> Position {
        Position { frame, fraction: 0 }
    }

    /// The step that makes 256 output frames cover `1 + parts / 10^9` times
    /// as many frames of the stream, to the nearest unit.
    fn step_for(parts: i64) -> i64 {
        i64::try_from((i128::from(parts) << 64) / 1_000_000_000).unwrap_or(0)
    }

    /// Runs cycles against a schedule that starts at `start` and advances
    /// with `step` for each output frame, and returns the distance behind
    /// the schedule, in units of 2^-32 frame, before each cycle, and the
    /// plans.
    fn run(
        player: &mut Player,
        start: Position,
        step: i64,
        cycles: usize,
    ) -> (Vec<i64>, Vec<Plan>) {
        let mut now = start;
        let mut behind = Vec::new();
        let mut plans = Vec::new();
        for _ in 0..cycles {
            let then = advance(now, FRAMES, step);
            if let Some(position) = player.position() {
                behind.push(distance(position, now));
            }
            plans.push(player.cycle(now, then, FRAMES, DURATION, 0));
            now = then;
        }
        (behind, plans)
    }

    use std::vec::Vec;

    /// The numbers of the law for the gain `a` of a cycle, in floating
    /// point: `d^2` and `a^2 d`, where `d + 1/d = (a^2 + sqrt(a^4 + 16)) / 2`.
    fn law(a: f64) -> (f64, f64) {
        let sum = f64::midpoint(a * a, (a.powi(4) + 16.0).sqrt());
        let modulus = (sum - (sum * sum - 4.0).sqrt()) / 2.0;
        (modulus * modulus, a * a * modulus)
    }

    #[test]
    fn the_gains_are_those_of_the_law() {
        // A gain of four per second and cycles from a tenth of a millisecond
        // to a quarter of a second: `a` from 0.0004 to 1, where it is held.
        for duration in [
            100_000i64,
            1_000_000,
            5_333_333,
            21_333_333,
            100_000_000,
            250_000_000,
            900_000_000,
        ] {
            #[allow(clippy::cast_precision_loss)]
            let a = (4.0 * duration as f64 * 1e-9).min(1.0);
            let (ahead, behind) = law(a);
            let gains = player().gains(duration);
            #[allow(clippy::cast_precision_loss)]
            let (found_ahead, found_behind) = (
                gains.ahead as f64 / 4_294_967_296.0,
                gains.behind as f64 / 281_474_976_710_656.0,
            );
            assert!(
                (found_ahead - ahead).abs() < 1e-8,
                "{duration}: {found_ahead} against {ahead}"
            );
            // The gain of the cycle itself is known to 2^-32, which is a
            // millionth of the smallest of these.
            assert!(
                (found_behind - behind).abs() < 3e-6 * behind + 1e-14,
                "{duration}: {found_behind} against {behind}"
            );
        }
        // Without a gain nothing is corrected: the pace is kept as it is.
        let still = Player::new(Regulation {
            gain: 0,
            limit: 1_000_000,
            jump: 240,
        })
        .gains(DURATION);
        assert_eq!((still.ahead, still.behind), (1 << 32, 0));
    }

    /// Runs `cycles` cycles against a schedule that goes on from `start`
    /// with `step` for each output frame, telling the regulator that the
    /// level's slope is `slope`, and returns where the schedule is after
    /// them, the distance behind it before each cycle and the plans.
    fn go_on(
        player: &mut Player,
        start: Position,
        step: i64,
        slope: i32,
        cycles: usize,
    ) -> (Position, Vec<i64>, Vec<Plan>) {
        let mut now = start;
        let mut behind = Vec::new();
        let mut plans = Vec::new();
        for _ in 0..cycles {
            let then = advance(now, FRAMES, step);
            if let Some(position) = player.position() {
                behind.push(distance(position, now));
            }
            plans.push(player.cycle(now, then, FRAMES, DURATION, slope));
            now = then;
        }
        (now, behind, plans)
    }

    /// The pace of a schedule whose level rises by half a millisecond each
    /// second: a second of stream takes 1.0005 seconds.
    const RISING: i64 = -499_750;

    #[test]
    fn a_change_of_the_level_s_slope_is_followed_at_once() {
        let mut player = player();
        let (start, _, _) = go_on(&mut player, at(5_000), 0, 0, 100);
        // The level begins to rise, and the packets say so.
        let (_, behind, plans) = go_on(&mut player, start, step_for(RISING), 500_000, 400);
        // The first cycle already reads at the schedule's new pace...
        assert!((plans[0].step.offset() - step_for(RISING)).abs() < step_for(1_000));
        // ...so the position stays on the schedule: within a thousandth of
        // a frame, where following the new pace by and by leaves it more
        // than a frame off (the test below).
        let worst = behind.iter().map(|b| b.abs()).max().unwrap_or(0);
        assert!(worst < (1 << 32) / 1_000, "worst distance {worst}");
    }

    #[test]
    fn a_revision_of_the_schedule_s_pace_is_followed_by_and_by() {
        let mut player = player();
        let (start, _, _) = go_on(&mut player, at(5_000), 0, 0, 100);
        // The schedule turns out to run at another pace, which nothing
        // announced: the slope of the level is as before.
        let (_, behind, plans) = go_on(&mut player, start, step_for(RISING), 0, 1_500);
        // The first cycle moves the pace by the fraction `1 - d^2` of the
        // revision, which is 0.0297 for this gain and cycle, and no change
        // of the pace from one cycle to the next is larger than that.
        let (keep, _) = law(4.0 * 5.333_333e-3);
        #[allow(clippy::cast_precision_loss)]
        let first = plans[0].step.offset() as f64 / step_for(RISING) as f64;
        assert!(
            (first - (1.0 - keep)).abs() < 1e-4,
            "{first} against {}",
            1.0 - keep
        );
        let roughest = plans
            .windows(2)
            .map(|pair| (pair[1].step.offset() - pair[0].step.offset()).abs())
            .max()
            .unwrap_or(0);
        assert!(roughest <= plans[0].step.offset().abs(), "{roughest}");
        // The position falls behind the new schedule by more than a frame
        // on the way, and is back on it in the end.
        let worst = behind.iter().map(|b| b.abs()).max().unwrap_or(0);
        assert!(worst > 1 << 32, "worst distance {worst}");
        let late = behind[1_400..].iter().map(|b| b.abs()).max().unwrap_or(0);
        assert!(late < (1 << 32) / 1_000, "left in the end: {late}");
        let last = plans.last().expect("plans");
        assert!((last.step.offset() - step_for(RISING)).abs() < step_for(100));
    }

    #[test]
    fn the_first_cycle_starts_on_the_schedule() {
        let mut player = player();
        assert_eq!(player.position(), None);
        let plan = player.cycle(at(1_000), at(1_256), FRAMES, DURATION, 0);
        assert_eq!(
            plan,
            Plan {
                frames: FRAMES,
                start: at(1_000),
                step: Step::UNITY,
                jumped: true
            }
        );
        assert_eq!(player.position(), Some(at(1_256)));
    }

    #[test]
    fn a_schedule_at_another_pace_is_followed_without_an_error() {
        // 100 parts per million fast: the first cycle takes the pace of the
        // schedule, and it is kept, so no error has to build up before the
        // position follows. A law without a memory of the pace would stay
        // behind by the scheduled excess of a cycle, 0.0256 frame, times two
        // over the gain: 1.7 frames.
        let mut player = player();
        let (behind, plans) = run(&mut player, at(5_000), step_for(100_000), 2_000);
        let worst = behind.iter().map(|b| b.abs()).max().unwrap_or(0);
        // A unit is 2^-32 frame. The schedule's advance over a cycle is
        // known to one unit, so it seems to change by a unit now and then,
        // and the law follows such a change by the fraction 0.03 in each
        // cycle: the distance stays within a few tens of units.
        assert!(worst <= 64, "worst distance {worst}");
        let last = plans.last().expect("plans");
        assert!((last.step.offset() - step_for(100_000)).abs() < 1 << 30);
    }

    #[test]
    fn a_distance_below_the_jump_is_played_away_smoothly() {
        let mut player = player();
        player.cycle(at(10_000), at(10_256), FRAMES, DURATION, 0);
        // The schedule is found to be a hundred frames further on.
        let (behind, plans) = run(&mut player, at(10_356), 0, 3_000);
        assert_eq!(behind[0], 100 << 32);
        assert!(plans.iter().all(|plan| !plan.jumped));
        // The distance never overshoots by more than a twentieth, and is
        // gone after sixteen seconds.
        let lowest = behind.iter().min().copied().unwrap_or(0);
        assert!(lowest > -(100 << 32) / 20, "overshoot {lowest}");
        let late = behind[2_900..].iter().map(|b| b.abs()).max().unwrap_or(0);
        assert!(
            late < (1 << 32) / 1_000,
            "left after sixteen seconds: {late}"
        );
        // The pace stays within a thousandth. From one cycle to the next it
        // changes by at most the squared gain of a cycle times the distance:
        // (4 per second * 5.33 ms)^2 * 100 frames, spread over 256 frames,
        // which is 178 parts per million.
        let limit = step_for(1_000_000);
        assert!(plans.iter().all(|plan| plan.step.offset().abs() <= limit));
        let roughest = plans
            .windows(2)
            .map(|pair| (pair[1].step.offset() - pair[0].step.offset()).abs())
            .max()
            .unwrap_or(0);
        assert!(
            roughest <= step_for(178_000),
            "largest change of pace {roughest}"
        );
        // It is the limit that holds the pace for most of the way: a cycle
        // removes a quarter of a frame.
        assert!(limit - plans[150].step.offset() < 1 << 16);
        assert!(behind[300] < 30 << 32 && behind[300] > 20 << 32);
    }

    #[test]
    fn a_distance_beyond_the_jump_is_jumped_either_way() {
        let mut player = player();
        player.cycle(at(10_000), at(10_256), FRAMES, DURATION, 0);
        let plan = player.cycle(at(10_256 + 241), at(10_512 + 241), FRAMES, DURATION, 0);
        assert_eq!(
            (plan.start, plan.step, plan.jumped),
            (at(10_497), Step::UNITY, true)
        );
        // Back as well: what was played already is behind the receiver's
        // playhead and is not played again.
        let plan = player.cycle(at(9_000), at(9_256), FRAMES, DURATION, 0);
        assert_eq!((plan.start, plan.jumped), (at(9_000), true));
        // Exactly at the jump the pace does the work.
        let mut player = self::player();
        player.cycle(at(10_000), at(10_256), FRAMES, DURATION, 0);
        let plan = player.cycle(at(10_256 + 240), at(10_512 + 240), FRAMES, DURATION, 0);
        assert_eq!((plan.start, plan.jumped), (at(10_256), false));
        assert!(plan.step.offset() > 0);
    }

    #[test]
    fn a_schedule_that_does_not_advance_gives_silence() {
        let mut player = player();
        assert_eq!(
            player.cycle(at(500), at(500), FRAMES, DURATION, 0).frames,
            0
        );
        assert_eq!(
            player.cycle(at(500), at(400), FRAMES, DURATION, 0).frames,
            0
        );
        assert_eq!(player.cycle(at(500), at(756), 0, DURATION, 0).frames, 0);
        assert_eq!(player.position(), None);
    }

    #[test]
    fn after_a_stop_the_next_cycle_starts_on_the_schedule() {
        let mut player = player();
        player.cycle(at(10_000), at(10_256), FRAMES, DURATION, 0);
        player.stop();
        let plan = player.cycle(at(77), at(333), FRAMES, DURATION, 0);
        assert_eq!(plan.start, at(77));
    }

    #[test]
    fn a_pace_of_the_schedule_beyond_the_limit_is_held_at_the_limit() {
        // The schedule runs two thousandths fast, the limit is one.
        let mut player = player();
        let (_, plans) = run(&mut player, at(0), step_for(2_000_000), 50);
        let limit = step_for(1_000_000);
        assert!(
            plans
                .iter()
                .all(|plan| (plan.step.offset() - limit).abs() <= 1 << 20)
        );
    }

    #[test]
    fn the_pace_stays_within_the_limit_whatever_the_schedule_does() {
        // Over a cycle the schedule can advance by far more than the cycle's
        // frames, as when the device stalled, or by far less.
        let limit = step_for(1_000_000);
        for (frames, scheduled) in [
            (FRAMES, 1),
            (FRAMES, 100),
            (FRAMES, 100_000),
            (FRAMES, 10_000_000_000),
            (1, 1 << 40),
            (u32::MAX, 3),
            (u32::MAX, 1 << 62),
        ] {
            let mut player = player();
            let plan = player.cycle(at(1_000), at(1_000 + scheduled), frames, DURATION, 0);
            assert!(
                plan.step.offset().abs() <= limit,
                "{frames} frames over {scheduled}: step {}",
                plan.step.offset()
            );
            // The position moves by the frames at that pace and no further.
            assert_eq!(
                player.position(),
                Some(advance(plan.start, frames, plan.step.offset()))
            );
        }
    }

    #[test]
    fn at_the_limit_the_correction_is_what_was_read_and_does_not_build_up() {
        // The schedule runs two thousandths fast for a while and then at the
        // nominal pace. The limit is one thousandth, so the position falls
        // behind, and then catches up at the limit without going past the
        // schedule by more than the regulator does from rest.
        let mut player = player();
        let (_, _) = run(&mut player, at(0), step_for(2_000_000), 400);
        let position = player.position().unwrap_or(at(0));
        let now = advance(at(0), FRAMES * 400, step_for(2_000_000));
        let fallen = distance(position, now);
        assert!(fallen > 100 << 32 && fallen < 103 << 32, "{fallen}");
        let (behind, plans) = run(&mut player, now, 0, 3_000);
        assert!(plans.iter().all(|plan| !plan.jumped));
        let lowest = behind.iter().copied().min().unwrap_or(0);
        // From rest the regulator goes past by less than a twentieth.
        assert!(lowest > -(fallen / 20), "{lowest}");
        assert!(behind.last().copied().unwrap_or(i64::MAX).abs() < 1 << 20);
    }
}
