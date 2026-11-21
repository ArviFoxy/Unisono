// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The choice of the level from the needs that receivers report.
//!
//! The level is the latency that every receiver holds. A frame is played at
//! a receiver when the level is at least what the frame needed there, and
//! the group of receivers plays it when the level is at least the largest
//! need over the receivers. Each receiver reports, for each stretch of the
//! index, the largest need of a frame in it, and the sender keeps the largest
//! over the receivers: `y`, the need of the group in that stretch. A stretch
//! is `D` seconds long, the window of the sender's clock estimate.
//!
//! # What a stretch costs
//!
//! Held at a level `l`, a stretch whose need is `y`, after a stretch whose
//! need was `p`, costs
//!
//! ```text
//! c(l; p, y) = w_gap [p <= l < y] + w_miss min((y - l)+, D).
//! ```
//!
//! The first term counts a gap where one starts: the stretch is missed from
//! its start, since `y > l`, and the stretch before was not. The second is
//! the time of the frames that are missed: the frames of a stretch need less
//! the later they were captured, since they waited less for the pause that
//! delayed them, so of a stretch with `y > l` about `min(y - l, D)` seconds
//! are missed. A level held at `l` then costs, per second,
//!
//! ```text
//! J(l) = w_lat l + w_tgt (l - L0)^2 + (the mean of c(l; p, y)) / D,
//! ```
//!
//! with `L0` a level aimed at and the `w` weights.
//!
//! # What is expected of the next stretch
//!
//! The mean is over what the next stretch will be, given the `m` stretches
//! seen. Nothing sets the next stretch apart from those seen, so, for needs
//! that are all different, it has the largest need of the `m + 1` with the
//! probability `1 / (m + 1)`. The mean is taken accordingly: with that
//! probability the next stretch needs more than any that was seen, and
//! starts a gap if its need is above the level; otherwise it is one of the
//! stretches seen, each as likely as the others. The mean cost of the next
//! stretch is then
//!
//! ```text
//! (c1(l) + the sum of c(l; p, y) over the stretches seen) / (m + 1),
//! ```
//!
//! where `c1(l)` is the mean cost of a stretch that needs more than any
//! seen. The level that makes `J` smallest with this mean is the best
//! decision that the evidence and the law of such a stretch allow. A group
//! with little evidence gets high rates at low levels, and so a high level,
//! which comes down as stretches without large needs are seen: after the
//! time `T` of evidence, a need above all that were seen is expected about
//! once in `T`.
//!
//! How far above the largest need `M` seen the need of such a stretch lies
//! is not something the stretches seen can say. It is taken from a law fixed
//! beforehand: the need exceeds `x`, for `x` above `M`, with the probability
//! `((S + M) / (S + x))^2`. This is the law `(1 + x / S)^-2` of a need
//! about which nothing is known, given that it is above `M`. `S` is 20 ms:
//! the need of a stretch is the time that packets and the cycles of the
//! devices take, milliseconds to tens of milliseconds, and at times a pause
//! of a link, tens to hundreds. The law has no variance, and under it a new
//! largest need lies above the last by `S + M` on average: pauses are taken
//! to have no typical size. These numbers are about links and devices in
//! general and are not fitted to anything.
//!
//! # Moving
//!
//! The level moves only when the cost saved, over the time that the evidence
//! covers, exceeds the cost of a move. This rule is not derived: it takes the
//! time that the evidence covers as the time for which what was seen will go
//! on.

// Counts of stretches, and levels in nanoseconds, are far below 2^52, where
// an `f64` holds every integer exactly.
#![allow(clippy::cast_precision_loss)]

use unisono_core::packet::{RECENT, Recent, UNKNOWN_NEED};

/// The weights of the cost of a level.
#[derive(Clone, Copy, Debug)]
pub struct Weights {
    /// The cost per second of each second of level.
    pub latency: f64,
    /// The level aimed at, in nanoseconds.
    pub target: i64,
    /// The cost per second of each square second that the level is away
    /// from the one aimed at.
    pub off_target: f64,
    /// The cost of one gap of the group.
    pub gap: f64,
    /// The cost per second of missing every frame; a fraction of the frames
    /// missed costs that fraction of it.
    pub missed: f64,
    /// The cost of moving the level.
    pub moving: f64,
}

/// What the choice of the level is set up with.
#[derive(Clone, Copy, Debug)]
pub struct Choice {
    /// The weights of the cost.
    pub weights: Weights,
    /// How many stretches the evidence covers at most.
    pub history: usize,
    /// How fast the level moves, in nanoseconds per second of stream.
    pub slope: i32,
}

/// The scale of the law of a need about which nothing is known, in seconds:
/// such a need exceeds `x` with the probability `(1 + x / PRIOR_SCALE)^-2`.
const PRIOR_SCALE: f64 = 0.02;

/// How many levels are tried besides the needs that were seen.
const LEVELS: usize = 256;

/// The highest level that is chosen, in seconds.
const CEILING: f64 = 2.0;

/// The probability that a need exceeds `level`, for a need that is larger
/// than `largest`, the largest that was seen.
fn exceeds_beyond(level: f64, largest: f64) -> f64 {
    if level <= largest {
        1.0
    } else {
        let ratio = (PRIOR_SCALE + largest) / (PRIOR_SCALE + level);
        ratio * ratio
    }
}

/// The mean time that a stretch of `stretch` seconds misses at `level`, for
/// a stretch whose need is larger than `largest`: the integral of
/// [`exceeds_beyond`] from the level to the level and the stretch.
fn missed_beyond(level: f64, stretch: f64, largest: f64) -> f64 {
    let end = level + stretch;
    // Up to the largest need seen the probability is one.
    let surely = (end.min(largest) - level).max(0.0);
    let from = level.max(largest);
    let scale = PRIOR_SCALE + largest;
    let perhaps = if end > from {
        scale * scale * (1.0 / (PRIOR_SCALE + from) - 1.0 / (PRIOR_SCALE + end))
    } else {
        0.0
    };
    surely + perhaps
}

/// The needs of the group by stretch, and the choice of the level from them.
pub struct Chooser {
    choice: Choice,
    /// The length of a stretch, in seconds.
    stretch: f64,
    /// The timeline that reports are taken in for.
    timeline: Option<u64>,
    /// The number that stretch 0 of that timeline has here. The stretches of
    /// the timelines before keep theirs, so that the evidence about the
    /// links outlives a new start of the sender.
    base: u64,
    /// The newest stretch that a report gave, by its number here.
    newest: u64,
    /// The stretch and the largest need, in seconds, of stretch `i` at
    /// place `i % history`.
    kept: Vec<Option<(u64, f64)>>,
    // Room for the evidence, made once so that a choice allocates nothing.
    sorted: Vec<f64>,
    sums: Vec<f64>,
    starts: Vec<f64>,
    ends: Vec<f64>,
}

impl Chooser {
    /// A chooser for stretches of `window` frames at `rate` frames per
    /// second.
    #[must_use]
    pub fn new(choice: Choice, window: u32, rate: u32) -> Chooser {
        let history = choice.history.max(RECENT + 1);
        Chooser {
            choice: Choice { history, ..choice },
            stretch: f64::from(window) / f64::from(rate.max(1)),
            timeline: None,
            base: 0,
            newest: 0,
            kept: vec![None; history],
            sorted: Vec::with_capacity(history),
            sums: Vec::with_capacity(history + 1),
            starts: Vec::with_capacity(history),
            ends: Vec::with_capacity(history),
        }
    }

    /// How fast the level moves, in nanoseconds per second of stream.
    #[must_use]
    pub fn slope(&self) -> i32 {
        self.choice.slope
    }

    /// Takes in the needs that a report on `timeline` carried. A timeline
    /// other than the one before follows on from the stretches of that one,
    /// which are kept: they tell of the same links.
    pub fn observe(&mut self, timeline: u64, recent: &Recent) {
        if self.timeline != Some(timeline) {
            self.timeline = Some(timeline);
            if self.kept.iter().any(Option::is_some) {
                self.base = self.newest.saturating_add(1);
            }
        }
        let count = usize::from(recent.count).min(RECENT);
        for (back, &need) in recent.needs.iter().take(count).enumerate() {
            let Some(stretch) = recent.newest.checked_sub(back as u64) else {
                break;
            };
            if need != UNKNOWN_NEED {
                self.take(self.base.saturating_add(stretch), f64::from(need) * 1e-6);
            }
        }
    }

    /// Takes in that stretch `stretch` needed `need` seconds at one
    /// receiver.
    fn take(&mut self, stretch: u64, need: f64) {
        let length = self.kept.len() as u64;
        if stretch.saturating_add(length) <= self.newest {
            return;
        }
        self.newest = self.newest.max(stretch);
        let Some(slot) = usize::try_from(stretch % length)
            .ok()
            .and_then(|place| self.kept.get_mut(place))
        else {
            return;
        };
        *slot = match *slot {
            Some((held, largest)) if held == stretch => Some((stretch, largest.max(need))),
            _ => Some((stretch, need)),
        };
    }

    /// The level to move to from `current`, in nanoseconds, if the evidence
    /// says that moving is worth its cost.
    pub fn choose(&mut self, current: i64) -> Option<i64> {
        let weights = self.choice.weights;
        let evidence = self.gather()?;
        let current = current as f64 * 1e-9;
        let cost_now = evidence.cost(current, &weights);
        let (best, cost_best) = evidence
            .levels(&weights)
            .map(|level| (level, evidence.cost(level, &weights)))
            .fold((current, cost_now), |a, b| if b.1 < a.1 { b } else { a });
        let saving = (cost_now - cost_best) * evidence.time();
        if saving > weights.moving {
            // Within the range of `i64`: at most the ceiling.
            #[allow(clippy::cast_possible_truncation)]
            Some((best * 1e9).round() as i64)
        } else {
            None
        }
    }

    /// The stretches that no report will give again as evidence; `None` if
    /// there are none.
    fn gather(&mut self) -> Option<Evidence<'_>> {
        self.sorted.clear();
        self.starts.clear();
        self.ends.clear();
        let length = self.kept.len() as u64;
        let last = self.newest.checked_sub(RECENT as u64)?;
        let first = (self.newest + 1).saturating_sub(length);
        // The need before a stretch that is not known counts as none.
        let mut before = f64::NEG_INFINITY;
        for stretch in first..=last {
            let need = usize::try_from(stretch % length)
                .ok()
                .and_then(|place| self.kept.get(place))
                .and_then(|slot| *slot)
                .filter(|(held, _)| *held == stretch)
                .map(|(_, need)| need);
            if let Some(need) = need {
                self.sorted.push(need);
                // A level in `[before, need)` is exceeded from this stretch
                // on and not in the one before: a gap starts.
                if need > before {
                    self.starts.push(before);
                    self.ends.push(need);
                }
            }
            before = need.unwrap_or(f64::NEG_INFINITY);
        }
        if self.sorted.is_empty() {
            return None;
        }
        self.sorted.sort_by(f64::total_cmp);
        self.starts.sort_by(f64::total_cmp);
        self.ends.sort_by(f64::total_cmp);
        self.sums.clear();
        self.sums.push(0.0);
        let mut sum = 0.0;
        for need in &self.sorted {
            sum += need;
            self.sums.push(sum);
        }
        Some(Evidence {
            sorted: &self.sorted,
            sums: &self.sums,
            starts: &self.starts,
            ends: &self.ends,
            stretch: self.stretch,
        })
    }
}

/// The needs of the stretches that were seen, and what a level is expected
/// to cost given them.
struct Evidence<'a> {
    /// The needs, in seconds, smallest first; at least one.
    sorted: &'a [f64],
    /// `sums[i]` is the sum of the `i` smallest needs.
    sums: &'a [f64],
    /// The levels from which on, and up to which, a gap starts at a stretch:
    /// each sorted on its own.
    starts: &'a [f64],
    ends: &'a [f64],
    /// The length of a stretch, in seconds.
    stretch: f64,
}

impl Evidence<'_> {
    /// The time that the evidence covers, in seconds.
    fn time(&self) -> f64 {
        self.sorted.len() as f64 * self.stretch
    }

    /// The number of stretches seen at which a gap starts at `level`.
    fn starts_at(&self, level: f64) -> f64 {
        let started = self.starts.partition_point(|start| *start <= level);
        let ended = self.ends.partition_point(|end| *end <= level);
        started.saturating_sub(ended) as f64
    }

    /// The time of the frames that the stretches seen miss at `level`, in
    /// seconds: `min(need - level, D)` for each stretch above the level.
    fn missed_at(&self, level: f64) -> f64 {
        let lower = above(self.sorted, level);
        let upper = above(self.sorted, level + self.stretch);
        let partly = self.sums[upper] - self.sums[lower] - (upper - lower) as f64 * level;
        let wholly = (self.sorted.len() - upper) as f64 * self.stretch;
        partly + wholly
    }

    /// The rate of gaps of the group per second, and the fraction of frames
    /// it misses, that are expected at `level`: the means over the next
    /// stretch, which is one of the stretches seen or, as likely as each of
    /// them, one that needs more than all of them.
    fn rates(&self, level: f64) -> (f64, f64) {
        let weight = (self.sorted.len() as f64 + 1.0) * self.stretch;
        let largest = self.sorted[self.sorted.len() - 1].max(0.0);
        let gaps = self.starts_at(level) + exceeds_beyond(level, largest);
        let missed = self.missed_at(level) + missed_beyond(level, self.stretch, largest);
        (gaps / weight, missed / weight)
    }

    /// The cost per second that holding `level` is expected to have.
    fn cost(&self, level: f64, weights: &Weights) -> f64 {
        let (gaps, missed) = self.rates(level);
        let off = level - weights.target as f64 * 1e-9;
        weights.latency * level
            + weights.off_target * off * off
            + weights.gap * gaps
            + weights.missed * missed
    }

    /// The levels that are tried. The expected cost falls only where the
    /// level passes a need that was seen, or smoothly above the largest of
    /// them, so these are the needs that were seen, the level aimed at, and
    /// levels from the smallest need to the highest level, closer together
    /// near the needs.
    fn levels(&self, weights: &Weights) -> impl Iterator<Item = f64> + '_ {
        let lowest = self.sorted[0].clamp(0.0, CEILING);
        let span = CEILING - lowest;
        let spread = (0..LEVELS).map(move |i| {
            let part = i as f64 / (LEVELS - 1) as f64;
            lowest + span * part * part
        });
        let target = (weights.target as f64 * 1e-9).clamp(0.0, CEILING);
        self.sorted
            .iter()
            .map(|need| need.clamp(0.0, CEILING))
            .chain(spread)
            .chain(std::iter::once(target))
    }
}

/// The index of the first need in `sorted` that is larger than `level`.
fn above(sorted: &[f64], level: f64) -> usize {
    sorted.partition_point(|need| *need <= level)
}

#[cfg(test)]
mod tests {
    use unisono_core::packet::{RECENT, Recent, UNKNOWN_NEED};

    use super::{Choice, Chooser, Weights};

    /// A millisecond of level costs one per second, a gap as much as a
    /// millisecond of level held for ten minutes, and so do ten milliseconds
    /// of frames missed in that time; a move costs as much as a millisecond
    /// held for a minute.
    const WEIGHTS: Weights = Weights {
        latency: 1_000.0,
        target: 0,
        off_target: 0.0,
        gap: 600.0,
        missed: 60_000.0,
        moving: 60.0,
    };

    /// Two minutes of stretches of 50 ms as evidence.
    const CHOICE: Choice = Choice {
        weights: WEIGHTS,
        history: 2_400,
        slope: 1_000_000,
    };

    /// Numbers from a fixed seed, evenly between 0 and 1.
    struct Numbers(u64);

    impl Numbers {
        fn next(&mut self) -> f64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 >> 11) as f64 / (1u64 << 53) as f64
        }
    }

    /// A group's need in each of `count` stretches of 50 ms, in seconds: two
    /// milliseconds of path, a jitter of a third of a millisecond on
    /// average, and, every `every` seconds on average, a pause of 10 to 80
    /// milliseconds that the stretch it falls into needs.
    fn needs(numbers: &mut Numbers, count: usize, every: f64) -> Vec<f64> {
        let mut needs = Vec::with_capacity(count);
        let mut carried: f64 = 0.0;
        for _ in 0..count {
            let jitter = -0.000_333 * (1.0 - numbers.next()).ln();
            if numbers.next() < 0.05 / every {
                carried = carried.max(0.01 + 0.07 * numbers.next());
            }
            needs.push(0.002 + jitter + carried);
            // A pause longer than a stretch carries into the next one, less
            // the length of the stretch.
            carried = (carried - 0.05).max(0.0);
        }
        needs
    }

    /// What `needs` cost at `level`, counted.
    fn counted_cost(needs: &[f64], level: f64, weights: &Weights) -> f64 {
        let time = needs.len() as f64 * 0.05;
        let mut gaps = 0.0;
        let mut missed = 0.0;
        let mut before = f64::NEG_INFINITY;
        for &need in needs {
            if need > level {
                missed += (need - level).min(0.05);
                if before <= level {
                    gaps += 1.0;
                }
            }
            before = need;
        }
        weights.latency * level + weights.gap * gaps / time + weights.missed * missed / time
    }

    /// Hands `needs` to `chooser` as one receiver's reports on `timeline`,
    /// a report every four stretches.
    // A need of the test is a fraction of a second: a few thousand
    // microseconds.
    #[allow(clippy::cast_possible_truncation)]
    fn report(chooser: &mut Chooser, timeline: u64, first: u64, needs: &[f64]) {
        for (i, _) in needs.iter().enumerate().skip(3).step_by(4) {
            let mut recent = Recent::NONE;
            recent.newest = first + i as u64;
            recent.count = u8::try_from(RECENT).unwrap();
            for back in 0..RECENT {
                recent.needs[back] = i
                    .checked_sub(back)
                    .map_or(UNKNOWN_NEED, |at| (needs[at] * 1e6).ceil() as i32);
            }
            chooser.observe(timeline, &recent);
        }
    }

    /// The level that a chooser with `weights` takes after `seen`, from a
    /// level of 20 ms, in seconds.
    fn chosen(weights: Weights, seen: &[f64]) -> f64 {
        let choice = Choice {
            weights,
            history: seen.len(),
            ..CHOICE
        };
        let mut chooser = Chooser::new(choice, 2_400, 48_000);
        report(&mut chooser, 7, 0, seen);
        chooser
            .choose(20_000_000)
            .map_or(0.02, |level| level as f64 * 1e-9)
    }

    #[test]
    fn the_chosen_level_costs_about_as_little_as_the_best_held_level() {
        let mut numbers = Numbers(0x2545_f491_4f6c_dd1d);
        // A gap costs as much as a millisecond of level held for one, ten
        // and a hundred minutes, and the frames missed in proportion. With
        // the first two, the chosen level costs at most a fifth more than
        // the best level held, which only hindsight gives. With the third a
        // single large need in the evidence, or none, is no ground to expect
        // few of them, and the level is held higher than hindsight would:
        // at most twice the cost.
        for (gap, bound) in [(60.0, 1.2), (600.0, 1.2), (6_000.0, 2.0)] {
            let weights = Weights {
                gap,
                missed: gap * 100.0,
                ..WEIGHTS
            };
            for every in [5.0, 30.0, 300.0] {
                for minutes in [2usize, 10] {
                    let level = chosen(weights, &needs(&mut numbers, minutes * 1_200, every));
                    // On stretches that the chooser has not seen.
                    let fresh = needs(&mut numbers, 40_000, every);
                    let best = (0..400)
                        .map(|i| counted_cost(&fresh, f64::from(i) * 0.000_25, &weights))
                        .fold(f64::INFINITY, f64::min);
                    let cost = counted_cost(&fresh, level, &weights);
                    assert!(
                        cost <= best * bound,
                        "a gap at {gap}, pauses every {every} s, {minutes} minutes seen: \
                         level {level}, cost {cost}, best {best}"
                    );
                }
            }
        }
    }

    #[test]
    fn the_level_stays_without_evidence_and_rises_with_pauses() {
        let mut numbers = Numbers(0x9e37_79b9_7f4a_7c15);
        let mut chooser = Chooser::new(CHOICE, 2_400, 48_000);
        assert_eq!(chooser.choose(20_000_000), None);
        // A quiet link brings the level down from 20 ms...
        let quiet = needs(&mut numbers, 2_400, 1e9);
        report(&mut chooser, 7, 0, &quiet);
        let low = chooser.choose(20_000_000).expect("the level falls");
        assert!(low < 10_000_000, "{low}");
        // ...and pauses bring it up again.
        let paused = needs(&mut numbers, 2_400, 5.0);
        report(&mut chooser, 7, 2_400, &paused);
        let high = chooser.choose(low).expect("the level rises");
        assert!(high > 40_000_000, "{high}");
    }

    #[test]
    fn little_evidence_holds_the_level_higher_than_much_of_the_same_kind() {
        let mut numbers = Numbers(0x0123_4567_89ab_cdef);
        let quiet = needs(&mut numbers, 12_000, 1e9);
        // Without a cost of moving, the level is the best one for what was
        // seen: after five seconds, after a minute and after ten.
        let weights = Weights {
            moving: 0.0,
            ..WEIGHTS
        };
        let few = chosen(weights, &quiet[..100]);
        let more = chosen(weights, &quiet[..1_200]);
        let many = chosen(weights, &quiet);
        assert!(few > more && more > many, "{few} {more} {many}");
        // The needs are all below 7 ms. After five seconds a larger need is
        // expected about once in five seconds, and the level is twice that.
        assert!(few > 0.014 && many < 0.008, "{few} {many}");
    }

    #[test]
    fn the_evidence_outlives_a_new_timeline_of_the_sender() {
        let mut numbers = Numbers(0x1234_5678_9abc_def1);
        let mut chooser = Chooser::new(CHOICE, 2_400, 48_000);
        let paused = needs(&mut numbers, 2_400, 5.0);
        report(&mut chooser, 7, 0, &paused);
        // The sender starts again: the index counts from zero in a timeline
        // of another number, over the same links.
        let quiet = needs(&mut numbers, 20, 1e9);
        report(&mut chooser, 8, 0, &quiet);
        let level = chooser.choose(2_000_000).expect("the level rises");
        assert!(level > 40_000_000, "{level}");
    }
}
