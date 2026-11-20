// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The regulator: where in the stream a receiver reads, cycle by cycle of its
//! device.
//!
//! The schedule says which position of the stream is due at the start and at
//! the end of a cycle. The regulator keeps the position at which the
//! receiver actually reads. It reads at the schedule's pace plus a
//! correction, and steers the correction so that the distance to the
//! schedule goes to zero smoothly: with `behind` the distance by which the
//! position is behind the schedule, the correction `v` of one cycle follows
//!
//! ```text
//! v' = (1 - sqrt(2) a) v + a^2 behind,        behind' = behind - v',
//! ```
//!
//! where `a` is the gain per second times the length of the cycle. The pace
//! as a whole, scheduled and corrected, stays within a limit. A distance too
//! large for that is not played away: the position jumps to the schedule.
//!
//! A jump can go back. That replays nothing, because the frames that a
//! receiver has given to its device are behind its playhead and are not
//! given again: until the position reaches the playhead the receiver plays
//! silence.

use crate::fixed::{div_floor, saturate};
use crate::timing::{Position, advance, distance};

/// The number of nanoseconds in a second, and of parts in a billion.
const BILLION: i64 = 1_000_000_000;

/// The square root of two, in units of 2^-32.
const ROOT_TWO: i128 = 6_074_001_000;

/// The largest gain of one cycle, in units of 2^-32: one half.
const LARGEST_GAIN: i128 = 2_147_483_648;

/// The longest cycle that the gain is computed for, in nanoseconds: 2^40.
const LONGEST_CYCLE: i64 = 1_099_511_627_776;

/// The largest limit of the pace, in parts per billion: three in a thousand.
const LARGEST_LIMIT: u32 = 3_000_000;

/// The settings of a regulator.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub struct Regulation {
    /// How fast a distance to the schedule is removed: the gain per second,
    /// in units of 2^-16.
    pub gain: u32,
    /// By how much the pace may differ from one frame of the stream for each
    /// frame of the device, in parts per billion.
    pub limit: u32,
    /// The distance to the schedule, in frames, beyond which the position
    /// jumps or waits instead of the pace changing.
    pub jump: u32,
}

/// What a receiver plays in one cycle of its device.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub struct Plan {
    /// The number of output frames taken from the stream. It is zero when
    /// nothing is due, and the cycle is silent then.
    pub frames: u32,
    /// The position in the stream of the first of them.
    pub start: Position,
    /// Each further output frame is taken one frame and this many units of
    /// 2^-64 frame after the one before.
    pub step: i64,
    /// Whether the position jumped to the schedule at the start of this
    /// cycle, so that the cycle does not go on where the one before ended.
    pub jumped: bool,
}

/// The regulator of one receiver.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub struct Player {
    regulation: Regulation,
    /// Whether a position is held.
    running: bool,
    /// The position of the next output frame.
    position: Position,
    /// How much further than scheduled a cycle reads, in units of 2^-48
    /// frame.
    correction: i64,
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
            correction: 0,
        }
    }

    /// Forgets the position, as at the start of a timeline. The next cycle
    /// starts at the schedule.
    pub fn stop(&mut self) {
        self.running = false;
        self.correction = 0;
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

    /// The correction of the next cycle, of `duration` nanoseconds, when the
    /// position is `behind` the schedule, in units of 2^-32 frame.
    fn regulate(&self, behind: i64, duration: i64) -> i64 {
        let gain = self.gain(duration);
        // Numbers of at most 32, 34 and 64 bits: no product wraps.
        let damping = gain.wrapping_mul(ROOT_TWO).wrapping_shr(32);
        let pull = gain.wrapping_mul(gain).wrapping_shr(16);
        let lost = damping
            .wrapping_mul(self.correction as i128)
            .wrapping_shr(32);
        let added = pull.wrapping_mul(behind as i128).wrapping_shr(32);
        saturate(
            (self.correction as i128)
                .wrapping_sub(lost)
                .wrapping_add(added),
        )
    }

    /// `correction` brought to where the pace of a cycle of `frames` output
    /// frames, over which the schedule advances by `scheduled` units of
    /// 2^-32 frame, is within the limit.
    fn limited(&self, correction: i64, frames: u32, scheduled: i64) -> i64 {
        let limit = if self.regulation.limit > LARGEST_LIMIT {
            LARGEST_LIMIT
        } else {
            self.regulation.limit
        };
        // 32 and 48 bits, then 22 more: no wrapping.
        let even = (frames as i128).wrapping_shl(48);
        let band = div_floor(even.wrapping_mul(limit as i128), BILLION);
        let schedule = (scheduled as i128).wrapping_shl(16);
        let low = even.wrapping_sub(band).wrapping_sub(schedule);
        let high = even.wrapping_add(band).wrapping_sub(schedule);
        let wide = correction as i128;
        if wide < low {
            saturate(low)
        } else if wide > high {
            saturate(high)
        } else {
            correction
        }
    }

    /// Plays `frames` output frames from the position on, when the schedule
    /// advances by `scheduled` over them and the position is `behind` it,
    /// both in units of 2^-32 frame.
    fn play(&mut self, frames: u32, scheduled: i64, behind: i64, duration: i64) -> (Position, i64) {
        let start = self.position;
        let correction = self.limited(self.regulate(behind, duration), frames, scheduled);
        self.correction = correction;
        // How much further than one frame for each output frame the cycle
        // reads, in units of 2^-48 frame; within the limit, so 16 more bits
        // fit.
        let beyond = (scheduled as i128)
            .wrapping_shl(16)
            .wrapping_add(correction as i128)
            .wrapping_sub((frames as i128).wrapping_shl(48));
        let step = saturate(div_floor(beyond.wrapping_shl(16), frames as i64));
        self.position = advance(start, frames, step);
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
    /// due when the frame after its last one does.
    pub fn cycle(&mut self, now: Position, then: Position, frames: u32, duration: i64) -> Plan {
        let scheduled = distance(now, then);
        if frames == 0 || scheduled <= 0 {
            // A schedule that stands still or runs backwards gives nothing
            // to play.
            return Plan {
                frames: 0,
                start: self.position,
                step: 0,
                jumped: false,
            };
        }
        let behind = distance(self.position, now);
        let jumped = self.jumps(behind);
        if jumped {
            self.running = true;
            self.position = now;
            self.correction = 0;
        }
        let (start, step) = self.play(frames, scheduled, if jumped { 0 } else { behind }, duration);
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
    use crate::timing::{Position, advance, distance};

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
            plans.push(player.cycle(now, then, FRAMES, DURATION));
            now = then;
        }
        (behind, plans)
    }

    use std::vec::Vec;

    #[test]
    fn the_first_cycle_starts_on_the_schedule() {
        let mut player = player();
        assert_eq!(player.position(), None);
        let plan = player.cycle(at(1_000), at(1_256), FRAMES, DURATION);
        assert_eq!(
            plan,
            Plan {
                frames: FRAMES,
                start: at(1_000),
                step: 0,
                jumped: true
            }
        );
        assert_eq!(player.position(), Some(at(1_256)));
    }

    #[test]
    fn a_schedule_at_another_pace_is_followed_without_an_error() {
        // 100 parts per million fast: the pace is fed forward, so no error
        // has to build up before the position follows.
        let mut player = player();
        let (behind, plans) = run(&mut player, at(5_000), step_for(100_000), 2_000);
        let worst = behind.iter().map(|b| b.abs()).max().unwrap_or(0);
        // A unit is 2^-32 frame; the schedule itself is known to one unit.
        assert!(worst <= 4, "worst distance {worst}");
        let last = plans.last().expect("plans");
        assert!((last.step - step_for(100_000)).abs() < 1 << 30);
    }

    #[test]
    fn a_distance_below_the_jump_is_played_away_smoothly() {
        let mut player = player();
        player.cycle(at(10_000), at(10_256), FRAMES, DURATION);
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
        assert!(plans.iter().all(|plan| plan.step.abs() <= limit));
        let roughest = plans
            .windows(2)
            .map(|pair| (pair[1].step - pair[0].step).abs())
            .max()
            .unwrap_or(0);
        assert!(
            roughest <= step_for(178_000),
            "largest change of pace {roughest}"
        );
        // It is the limit that holds the pace for most of the way: a cycle
        // removes a quarter of a frame.
        assert!(limit - plans[150].step < 1 << 16);
        assert!(behind[300] < 30 << 32 && behind[300] > 20 << 32);
    }

    #[test]
    fn a_distance_beyond_the_jump_is_jumped_either_way() {
        let mut player = player();
        player.cycle(at(10_000), at(10_256), FRAMES, DURATION);
        let plan = player.cycle(at(10_256 + 241), at(10_512 + 241), FRAMES, DURATION);
        assert_eq!((plan.start, plan.step, plan.jumped), (at(10_497), 0, true));
        // Back as well: what was played already is behind the receiver's
        // playhead and is not played again.
        let plan = player.cycle(at(9_000), at(9_256), FRAMES, DURATION);
        assert_eq!((plan.start, plan.jumped), (at(9_000), true));
        // Exactly at the jump the pace does the work.
        let mut player = self::player();
        player.cycle(at(10_000), at(10_256), FRAMES, DURATION);
        let plan = player.cycle(at(10_256 + 240), at(10_512 + 240), FRAMES, DURATION);
        assert_eq!((plan.start, plan.jumped), (at(10_256), false));
        assert!(plan.step > 0);
    }

    #[test]
    fn a_schedule_that_does_not_advance_gives_silence() {
        let mut player = player();
        assert_eq!(player.cycle(at(500), at(500), FRAMES, DURATION).frames, 0);
        assert_eq!(player.cycle(at(500), at(400), FRAMES, DURATION).frames, 0);
        assert_eq!(player.cycle(at(500), at(756), 0, DURATION).frames, 0);
        assert_eq!(player.position(), None);
    }

    #[test]
    fn after_a_stop_the_next_cycle_starts_on_the_schedule() {
        let mut player = player();
        player.cycle(at(10_000), at(10_256), FRAMES, DURATION);
        player.stop();
        let plan = player.cycle(at(77), at(333), FRAMES, DURATION);
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
                .all(|plan| (plan.step - limit).abs() <= 1 << 20)
        );
    }
}
