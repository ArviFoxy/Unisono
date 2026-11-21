// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The choice of the             .map(|level| (level, evidence.cost(level, &weights))) from the needs that receivers report.
//!
//! The level is the latency that every receiver holds. A frame is played at
//! a receiver when the level is at least what the frame needed there, and
//! the group of receivers plays it when the level is at least the largest
//! need over the receivers. Each receiver reports, for each stretch of the
//! index, the largest need of a frame in it, and the sender keeps the largest
//! over the receivers: `y`, the need of the group in that stretch. A stretch
//! is `D` seconds long, the window of the sender's clock estimate.
//!
//! A level `l`, held, costs per second
//!
//! ```text
//! J(l) = w_lat l + w_tgt (l - L0)^2 + w_gap G(l) + w_miss F(l),
//! ```
//!
//! where `G(l)` is the rate of gaps of the group, per second, `F(l)` the
//! fraction of frames that the group misses, `L0` the level aimed at, and
//! the `w` are weights. Both rates are estimated from the stretches of the
//! last minutes:
//!
//! - A stretch is missed from its start when `y > l`. A gap is a run of such
//!   stretches, so `G(l)` counts the stretches with `y > l` whose stretch
//!   before has not.
//! - The frames of a stretch need less the later they were captured, since
//!   they waited less for the pause that delayed them to end; so a stretch
//!   with `y > l` misses about `min(y - l, D)` seconds of frames, and
//!   `F(l)` is the mean of that over the stretches, divided by `D`.
//!
//! Below a threshold `u`, the need that the eleventh largest stretch has,
//! both are counted. Above it there are few stretches to count, and the
//! tail is estimated: the excess `z = y - u` of a stretch above `u` is taken
//! as exponential with an unknown rate that has a gamma prior with shape
//! `a0` and rate `b0`. After `n` excesses that add up to `Z`, the predictive
//! probability that an excess is larger than `x` is
//! `(b / (b + x))^a` with `a = a0 + n` and `b = b0 + Z`, a Lomax tail: a
//! group with little evidence gets a heavy tail, and so a high level. The
//! probability that a stretch exceeds `u` has a uniform prior.
//!
//! The level moves only when the cost saved, over the time that the
//! evidence covers, exceeds the cost of a move.

// Counts of stretches, and levels in nanoseconds, are far below 2^52, where
// an `f64` holds every integer exactly.
#![allow(clippy::cast_precision_loss)]

use unisono_core::packet::{RECENT, Recent, UNKNOWN_NEED};

/// The weights of the cost of a level, and the prior for the tail.
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
    /// How many stretches the evidence must cover before the level is
    /// chosen.
    pub least: usize,
    /// How fast the level moves, in nanoseconds per second of stream.
    pub slope: i32,
}

/// The shape of the gamma prior on the rate of the excesses of the tail: the
/// prior counts as much as one excess.
const PRIOR_SHAPE: f64 = 1.0;

/// The rate of that prior, in seconds: a median excess of about three
/// milliseconds, between the jitter of a wired link, below a millisecond,
/// and the pauses of a wireless one, tens of milliseconds.
const PRIOR_RATE: f64 = 0.002;

/// How many stretches lie above the threshold of the tail.
const ABOVE: usize = 10;

/// How many levels are tried.
const LEVELS: usize = 400;

/// The probability of a stretch beyond the highest level tried.
const HIGHEST: f64 = 1e-7;

/// The highest level that is chosen, in seconds.
const CEILING: f64 = 2.0;

/// The needs of the group by stretch, and the choice of the level from them.
pub struct Chooser {
    choice: Choice,
    /// The length of a stretch, in seconds.
    stretch: f64,
    /// The timeline whose stretches are kept.
    timeline: Option<u64>,
    /// The newest stretch that a report gave.
    newest: u64,
    /// The stretch and the largest need, in seconds, of stretch `i` at
    /// place `i % history`.
    kept: Vec<Option<(u64, f64)>>,
    // Room for the evidence, made once so that a choice allocates nothing.
    needs: Vec<f64>,
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
            newest: 0,
            kept: vec![None; history],
            needs: Vec::with_capacity(history),
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

    /// Takes in the needs that a report on `timeline` carried. The stretches
    /// of another timeline than before are dropped.
    pub fn observe(&mut self, timeline: u64, recent: &Recent) {
        if self.timeline != Some(timeline) {
            self.timeline = Some(timeline);
            self.newest = 0;
            self.kept.fill(None);
        }
        let count = usize::from(recent.count).min(RECENT);
        for (back, &need) in recent.needs.iter().take(count).enumerate() {
            let Some(stretch) = recent.newest.checked_sub(back as u64) else {
                break;
            };
            if need != UNKNOWN_NEED {
                self.take(stretch, f64::from(need) * 1e-6);
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
            .levels()
            .map(|level| (level, evidence.cost(level, &weights)))
            .fold((current, cost_now), |a, b| if b.1 < a.1 { b } else { a });
        let saving = (cost_now - cost_best) * evidence.time;
        if saving > weights.moving {
            // Within the range of `i64`: at most the ceiling.
            #[allow(clippy::cast_possible_truncation)]
            Some((best * 1e9).round() as i64)
        } else {
            None
        }
    }

    /// The stretches that no report will give again, oldest first, as
    /// evidence; `None` if there are too few.
    fn gather(&mut self) -> Option<Evidence<'_>> {
        self.needs.clear();
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
                self.needs.push(need);
                // A level in `[before, need)` is exceeded from this stretch
                // on and not in the one before: a gap starts.
                if need > before {
                    self.starts.push(before);
                    self.ends.push(need);
                }
            }
            before = need.unwrap_or(f64::NEG_INFINITY);
        }
        if self.needs.len() < self.choice.least.max(ABOVE + 2) {
            return None;
        }
        self.sorted.clear();
        self.sorted.extend_from_slice(&self.needs);
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
        Some(Evidence::new(
            &self.sorted,
            &self.sums,
            &self.starts,
            &self.ends,
            self.stretch,
        ))
    }
}

/// The needs of the stretches of the evidence, and the estimates of the
/// rates of gaps and of missed frames that they give.
struct Evidence<'a> {
    /// The needs, in seconds, smallest first.
    sorted: &'a [f64],
    /// `sums[i]` is the sum of the `i` smallest needs.
    sums: &'a [f64],
    /// The levels from which on, and up to which, a gap starts at a stretch:
    /// each sorted on its own.
    starts: &'a [f64],
    ends: &'a [f64],
    /// The length of a stretch, in seconds.
    stretch: f64,
    /// The time that the evidence covers, in seconds.
    time: f64,
    /// The threshold of the tail.
    threshold: f64,
    /// The probability that a stretch exceeds the threshold.
    beyond: f64,
    /// The shape and the scale of the predictive tail of the excesses.
    shape: f64,
    scale: f64,
    /// The fraction of the stretches above the threshold that start a gap.
    starting: f64,
}

impl<'a> Evidence<'a> {
    fn new(
        sorted: &'a [f64],
        sums: &'a [f64],
        starts: &'a [f64],
        ends: &'a [f64],
        stretch: f64,
    ) -> Self {
        let count = sorted.len();
        let threshold = sorted[count - 1 - ABOVE];
        let above = count - above_index(sorted, threshold);
        let excess = sums[count] - sums[count - above] - above as f64 * threshold;
        let mut evidence = Evidence {
            sorted,
            sums,
            starts,
            ends,
            stretch,
            time: count as f64 * stretch,
            threshold,
            beyond: (above as f64 + 1.0) / (count as f64 + 2.0),
            shape: PRIOR_SHAPE + above as f64,
            scale: PRIOR_RATE + excess,
            starting: 1.0,
        };
        evidence.starting = (evidence.starts_above(threshold) + 1.0) / (above as f64 + 1.0);
        evidence
    }

    /// The number of stretches at which a gap starts for a level `level`.
    fn starts_above(&self, level: f64) -> f64 {
        let started = self.starts.partition_point(|start| *start <= level);
        let ended = self.ends.partition_point(|end| *end <= level);
        started.saturating_sub(ended) as f64
    }

    /// The probability that the excess of a stretch above the threshold is
    /// larger than `excess`, given that there is one.
    fn tail(&self, excess: f64) -> f64 {
        (self.scale / (self.scale + excess)).powf(self.shape)
    }

    /// The integral of [`Evidence::tail`] from `from` to `from + length`.
    fn tail_integral(&self, from: f64, length: f64) -> f64 {
        let (a, b) = (self.shape, self.scale);
        if (a - 1.0).abs() < 1e-9 {
            b * ((b + from + length) / (b + from)).ln()
        } else {
            (self.tail(from) * (b + from) - self.tail(from + length) * (b + from + length))
                / (a - 1.0)
        }
    }

    /// The rate of gaps of the group per second, and the fraction of frames
    /// it misses, at `level`.
    fn rates(&self, level: f64) -> (f64, f64) {
        let count = self.sorted.len() as f64;
        if level < self.threshold {
            let gaps = self.starts_above(level) / self.time;
            // Each stretch above the level misses `min(need - level, D)`.
            let lower = above_index(self.sorted, level);
            let upper = above_index(self.sorted, level + self.stretch);
            let partly = self.sums[upper] - self.sums[lower] - (upper - lower) as f64 * level;
            let wholly = (self.sorted.len() - upper) as f64 * self.stretch;
            (gaps, (partly + wholly) / (count * self.stretch))
        } else {
            let excess = level - self.threshold;
            let exceeded = self.beyond * self.tail(excess);
            let gaps = self.starting * exceeded / self.stretch;
            let missed = self.beyond * self.tail_integral(excess, self.stretch) / self.stretch;
            (gaps, missed)
        }
    }

    /// The cost per second of holding `level`.
    fn cost(&self, level: f64, weights: &Weights) -> f64 {
        let (gaps, missed) = self.rates(level);
        let off = level - weights.target as f64 * 1e-9;
        weights.latency * level
            + weights.off_target * off * off
            + weights.gap * gaps
            + weights.missed * missed
    }

    /// The levels that are tried: evenly spaced from the smallest need to
    /// where a stretch exceeds the level with a negligible probability.
    fn levels(&self) -> impl Iterator<Item = f64> + '_ {
        let lowest = self.sorted[0].max(0.0);
        // Where `beyond * tail(x)` falls to `HIGHEST`.
        let reach = self.scale * ((self.beyond / HIGHEST).powf(1.0 / self.shape) - 1.0);
        let highest = (self.threshold + reach).clamp(lowest, CEILING);
        let step = (highest - lowest) / (LEVELS - 1) as f64;
        (0..LEVELS).map(move |i| lowest + step * i as f64)
    }
}

/// The index of the first need in `sorted` that is larger than `level`.
fn above_index(sorted: &[f64], level: f64) -> usize {
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

    /// Two minutes of stretches of 50 ms as evidence, at least five seconds.
    const CHOICE: Choice = Choice {
        weights: WEIGHTS,
        history: 2_400,
        least: 100,
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

    /// Hands `needs` to `chooser` as one receiver's reports, a report every
    /// four stretches.
    // A need of the test is a fraction of a second: a few thousand
    // microseconds.
    #[allow(clippy::cast_possible_truncation)]
    fn report(chooser: &mut Chooser, first: u64, needs: &[f64]) {
        for (i, _) in needs.iter().enumerate().skip(3).step_by(4) {
            let mut recent = Recent::NONE;
            recent.newest = first + i as u64;
            recent.count = u8::try_from(RECENT).unwrap();
            for back in 0..RECENT {
                recent.needs[back] = i
                    .checked_sub(back)
                    .map_or(UNKNOWN_NEED, |at| (needs[at] * 1e6).ceil() as i32);
            }
            chooser.observe(7, &recent);
        }
    }

    #[test]
    fn the_chosen_level_costs_about_as_little_as_the_best_held_level() {
        let mut numbers = Numbers(0x2545_f491_4f6c_dd1d);
        let weights = WEIGHTS;
        for every in [5.0, 30.0, 300.0] {
            let mut chooser = Chooser::new(CHOICE, 2_400, 48_000);
            let seen = needs(&mut numbers, 2_400, every);
            report(&mut chooser, 0, &seen);
            let chosen = chooser
                .choose(20_000_000)
                .map_or(0.02, |level| level as f64 * 1e-9);
            // On stretches that the chooser has not seen.
            let fresh = needs(&mut numbers, 40_000, every);
            let best = (0..2_000)
                .map(|i| counted_cost(&fresh, f64::from(i) * 0.000_05, &weights))
                .fold(f64::INFINITY, f64::min);
            let cost = counted_cost(&fresh, chosen, &weights);
            assert!(
                cost <= best * 1.25,
                "pauses every {every} s: level {chosen}, cost {cost}, best {best}"
            );
        }
    }

    #[test]
    fn the_level_stays_without_evidence_and_rises_with_pauses() {
        let mut numbers = Numbers(0x9e37_79b9_7f4a_7c15);
        let mut chooser = Chooser::new(CHOICE, 2_400, 48_000);
        assert_eq!(chooser.choose(20_000_000), None);
        let few = needs(&mut numbers, 50, 1e9);
        report(&mut chooser, 0, &few);
        assert_eq!(chooser.choose(20_000_000), None);
        // A quiet link brings the level down from 20 ms...
        let quiet = needs(&mut numbers, 2_400, 1e9);
        report(&mut chooser, 50, &quiet);
        let low = chooser.choose(20_000_000).expect("the level falls");
        assert!(low < 10_000_000, "{low}");
        // ...and pauses bring it up again.
        let paused = needs(&mut numbers, 2_400, 5.0);
        report(&mut chooser, 2_450, &paused);
        let high = chooser.choose(low).expect("the level rises");
        assert!(high > 40_000_000, "{high}");
    }
}
