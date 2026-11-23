// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Sender-side adaptive playout latency (`level`) controller.
//!
//! All receivers share a single playout latency `l`. A frame plays cleanly at
//! a receiver when `l` is at least that frame's required latency (`need`), and
//! across the whole group when `l` is at least the maximum need across all
//! receivers. Receivers report per-window maximum needs, and the sender takes
//! the group-wide maximum `y` for each window of duration `D` seconds (the
//! sender clock-estimator window).
//!
//! # Per-Window Cost Model
//!
//! At playout latency `l`, a window with group need `y` following a previous
//! window with group need `p` incurs cost:
//!
//! ```text
//! c(l; p, y) = w_gap * 1[p <= l < y] + w_miss * min((y - l)+, D).
//! ```
//!
//! The first term charges a discontinuity whenever a gap opens (`y > l` after
//! `p <= l`). The second term approximates missed duration: frames captured
//! later within a pause wait less, so a window with `y > l` misses roughly
//! `min(y - l, D)` seconds. The expected steady-state cost rate per second is:
//!
//! ```text
//! J(l) = w_lat * l + w_tgt * (l - L0)^2 + E[c(l; p, y)] / D,
//! ```
//!
//! where `L0` is the target latency and `w_lat`, `w_tgt`, `w_gap`, `w_miss`
//! are the objective weights.
//!
//! # Exchangeable Tail Prediction
//!
//! Given `m` observed windows, under exchangeability the next window exceeds
//! the running maximum `M` with probability `1 / (m + 1)` and otherwise draws
//! uniformly from the observed empirical pairs `(p, y)`:
//!
//! ```text
//! E[c(l; p, y)] = (c_tail(l) + sum_{observed} c(l; p, y)) / (m + 1).
//! ```
//!
//! Early in a session (small `m`), the `1 / (m + 1)` tail probability keeps
//! `l` conservative; as clean windows accumulate over duration `T`, `l`
//! lowers automatically. Exceedances above `M` follow the Pareto tail
//! `P(Y > x | Y > M) = ((S + M) / (S + x))^2` with scale `S = 20 ms`,
//! capturing heavy-tailed link pauses without assuming a finite tail variance.
//!
//! # Optimization
//!
//! Candidate latencies are integer nanoseconds in `[0, max_level]`. `J(l)` is
//! piecewise smooth with breakpoints only at observed needs `y` and `y - D`.
//! On each interval between adjacent breakpoints, `J(l)` is convex and its
//! minimum lies at an endpoint or at the unique zero-crossing of its
//! derivative (found by bisection).
//!
//! # Hysteresis (Move Rule)
//!
//! Changing the latency incurs a one-time ramp cost `c` and saves `s` per
//! second while the current delay regime persists. Under a non-informative
//! regime-duration prior over evidence duration `T`, the probability that the
//! regime persists for at least `t` more seconds is `T / (T + t)`, so the
//! transition has > 50% probability of breaking even iff `s * T > c`.
//!
//! # Calibration Checks
//!
//! [`Checks`] tracks online diagnostics for the three modeling assumptions:
//! empirical record-high rate (`~ 1 / (m + 1)`), PIT uniformity of exceedances
//! under the Pareto tail (`mean ~ 0.5`), and whether chosen levels hold for
//! longer than the evidence duration `T` half the time.

// Counts of stretches, and levels in nanoseconds, are far below 2^52, where
// an `f64` holds every integer exactly.
#![allow(clippy::cast_precision_loss)]

use unisono_core::packet::{RECENT, Recent, UNKNOWN_NEED};

use crate::InvalidSettings;

/// Maximum magnitude of `Choice::slope`, in nanoseconds per second of stream,
/// matching the core packet format's pace limit so both `+slope` and `-slope`
/// are valid on the wire.
pub const MAX_SLOPE: i32 = 999_999_999;

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

impl Weights {
    /// Validates that all cost weights are finite and non-negative and the
    /// target level lies within `[0, CEILING]`.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidSettings`] when any weight is non-finite or negative,
    /// or `target` is out of range.
    pub fn validate(&self) -> Result<(), InvalidSettings> {
        let valid_weight = |w: f64| w.is_finite() && w >= 0.0;
        if !valid_weight(self.latency) {
            return Err(InvalidSettings::new(
                "latency weight must be finite and non-negative",
            ));
        }
        if !(0..=CEILING).contains(&self.target) {
            return Err(InvalidSettings::new(
                "target level must be between 0 and 2 seconds",
            ));
        }
        if !valid_weight(self.off_target) {
            return Err(InvalidSettings::new(
                "off-target weight must be finite and non-negative",
            ));
        }
        if !valid_weight(self.gap) {
            return Err(InvalidSettings::new(
                "gap weight must be finite and non-negative",
            ));
        }
        if !valid_weight(self.missed) {
            return Err(InvalidSettings::new(
                "missed-frame weight must be finite and non-negative",
            ));
        }
        if !valid_weight(self.moving) {
            return Err(InvalidSettings::new(
                "moving weight must be finite and non-negative",
            ));
        }
        Ok(())
    }
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

impl Choice {
    /// Validates the weights, history length, and level-ramp slope.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidSettings`] when weights are invalid, `history` is
    /// zero, or `slope` is not in `1..=MAX_SLOPE`.
    pub fn validate(&self) -> Result<(), InvalidSettings> {
        self.weights.validate()?;
        if self.history == 0 {
            return Err(InvalidSettings::new("choice history must be at least 1"));
        }
        if self.slope <= 0 || self.slope > MAX_SLOPE {
            return Err(InvalidSettings::new(
                "choice slope must be between 1 and 999_999_999 ns/s",
            ));
        }
        Ok(())
    }
}

/// What the stretches seen say about the assumptions that the choice of the
/// level rests on, counted since the chooser was made.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Checks {
    /// Stretches that were held against the stretches before them.
    pub stretches: u64,
    /// Of those, the stretches that needed more than every stretch before
    /// them that the evidence held.
    pub largest: u64,
    /// How many of them are expected when nothing sets a stretch apart from
    /// those before it: `1 / (m + 1)` for each stretch held against `m`
    /// others, added up.
    pub expected: f64,
    /// For each stretch counted in `largest`, the probability that the law
    /// of such a need gave to a need as large as its own or larger, added
    /// up: half of `largest` when the law holds.
    pub beyond: f64,
    /// Levels chosen that another choice has replaced.
    pub replaced: u64,
    /// Of those, the levels that were held for longer than the time of the
    /// evidence they were chosen from: half of them when the needs keep
    /// their law as the rule for moving takes them to.
    pub outlasted: u64,
}

/// How many stretches are held against those before them at one time; a
/// chooser that was not asked for longer leaves the rest out.
const CHECKED_AT_ONCE: u64 = 64;

/// The scale of the law of a need about which nothing is known, in seconds:
/// such a need exceeds `x` with the probability `(1 + x / PRIOR_SCALE)^-2`.
const PRIOR_SCALE: f64 = 0.02;

/// The highest level that is chosen, in nanoseconds: two seconds.
const CEILING: i64 = 2_000_000_000;

/// A number of nanoseconds in seconds. Levels and needs are whole numbers
/// of nanoseconds, and every one of them becomes a number of seconds here,
/// so that equal ones stay equal.
fn seconds(nanoseconds: i64) -> f64 {
    nanoseconds as f64 * 1e-9
}

/// A number of seconds in nanoseconds, rounded.
// Within the range of `i64`: levels and needs are seconds at most.
#[allow(clippy::cast_possible_truncation)]
fn nanoseconds(seconds: f64) -> i64 {
    (seconds * 1e9).round() as i64
}

/// Where a level lies against the largest need that was seen, which decides
/// what a stretch that needs more than all seen is expected to cost there.
#[derive(Clone, Copy)]
enum Range {
    /// More than a stretch below it: such a stretch is missed whole.
    FarBelow,
    /// Below it by less than a stretch.
    Below,
    /// Above it.
    Above,
}

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
    points: Vec<i64>,
    checks: Checks,
    /// The newest stretch that was held against those before it.
    checked: Option<u64>,
    /// The newest stretch when the level was last chosen, and the time of
    /// the evidence it was chosen from, in seconds.
    chosen: Option<(u64, f64)>,
}

impl Chooser {
    /// A chooser for stretches of `window` frames at `rate` frames per
    /// second.
    #[must_use]
    pub fn new(choice: Choice, window: u32, rate: u32) -> Chooser {
        let history = choice.history.max(RECENT + 1);
        Chooser {
            choice: Choice { history, ..choice },
            stretch: f64::from(window.max(1)) / f64::from(rate.max(1)),
            timeline: None,
            base: 0,
            newest: 0,
            kept: vec![None; history],
            sorted: Vec::with_capacity(history),
            sums: Vec::with_capacity(history + 1),
            starts: Vec::with_capacity(history),
            ends: Vec::with_capacity(history),
            points: Vec::with_capacity(2 * history + 2),
            checks: Checks::default(),
            checked: None,
            chosen: None,
        }
    }

    /// What the stretches seen say about the assumptions.
    #[must_use]
    pub fn checks(&self) -> Checks {
        self.checks
    }

    /// How fast the level moves, in nanoseconds per second of stream.
    #[must_use]
    pub fn slope(&self) -> i32 {
        self.choice.slope
    }

    /// Takes in the needs that a report on `timeline` carried, ignoring the
    /// record if its `newest` stretch exceeds `max_stretch` (which no honest
    /// receiver can have seen on `timeline`).
    pub fn observe_up_to(&mut self, timeline: u64, recent: &Recent, max_stretch: u64) {
        if recent.newest > max_stretch {
            return;
        }
        self.observe(timeline, recent);
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
                self.take(
                    self.base.saturating_add(stretch),
                    seconds(i64::from(need) * 1_000),
                );
            }
        }
    }

    /// Takes in that stretch `stretch` needed `need` seconds at one
    /// receiver.
    fn take(&mut self, stretch: u64, need: f64) {
        if !need.is_finite() {
            return;
        }
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
        if weights.validate().is_err() || !self.stretch.is_finite() || self.stretch <= 0.0 {
            return None;
        }
        self.check();
        let mut evidence = self.gather()?;
        let cost_now = evidence.cost(seconds(current), &weights);
        let (best, cost_best) = evidence.best(&weights);
        let time = evidence.time();
        if (cost_now - cost_best) * time <= weights.moving {
            return None;
        }
        if let Some((stretch, covered)) = self.chosen {
            self.checks.replaced += 1;
            if self.newest.saturating_sub(stretch) as f64 * self.stretch > covered {
                self.checks.outlasted += 1;
            }
        }
        self.chosen = Some((self.newest, time));
        Some(best)
    }

    /// The largest need of stretch `stretch`, if it is kept.
    fn need(&self, stretch: u64) -> Option<f64> {
        let length = self.kept.len() as u64;
        usize::try_from(stretch % length)
            .ok()
            .and_then(|place| self.kept.get(place))
            .and_then(|slot| *slot)
            .filter(|(held, _)| *held == stretch)
            .map(|(_, need)| need)
    }

    /// Holds each stretch that no report will give again, and that was not
    /// held before, against the kept stretches before it.
    fn check(&mut self) {
        let Some(last) = self.newest.checked_sub(RECENT as u64) else {
            return;
        };
        if let Some(done) = self.checked
            && done >= last
        {
            return;
        }
        let length = self.kept.len() as u64;
        let oldest = self.newest.saturating_sub(length - 1);
        let from = match self.checked {
            Some(done) => done
                .saturating_add(1)
                .max(last.saturating_sub(CHECKED_AT_ONCE - 1)),
            None => last,
        }
        .max(oldest);
        let mut others = 0u64;
        let mut largest = f64::NEG_INFINITY;
        for before in oldest..from {
            if let Some(other) = self.need(before) {
                others += 1;
                largest = largest.max(other);
            }
        }
        for stretch in from..=last {
            if let Some(need) = self.need(stretch) {
                if others > 0 {
                    self.checks.stretches += 1;
                    self.checks.expected += 1.0 / (others as f64 + 1.0);
                    if need > largest {
                        self.checks.largest += 1;
                        self.checks.beyond += exceeds_beyond(need, largest.max(0.0));
                    }
                }
                others += 1;
                largest = largest.max(need);
            }
        }
        self.checked = Some(last);
    }

    /// The stretches that no report will give again as evidence; `None` if
    /// there are none.
    fn gather(&mut self) -> Option<Evidence<'_>> {
        self.sorted.clear();
        self.starts.clear();
        self.ends.clear();
        let length = self.kept.len() as u64;
        let last = self.newest.checked_sub(RECENT as u64)?;
        let first = self.newest.saturating_sub(length - 1);
        // The need before a stretch that is not known counts as none.
        let mut before = f64::NEG_INFINITY;
        for stretch in first..=last {
            let need = self.need(stretch);
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
        self.sorted.sort_unstable_by(f64::total_cmp);
        self.starts.sort_unstable_by(f64::total_cmp);
        self.ends.sort_unstable_by(f64::total_cmp);
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
            points: &mut self.points,
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
    /// Room for the levels at which the cost changes its form.
    points: &'a mut Vec<i64>,
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
        let off = level - seconds(weights.target);
        weights.latency * level
            + weights.off_target * off * off
            + weights.gap * gaps
            + weights.missed * missed
    }

    /// The largest need that was seen, or zero if all were below it.
    fn largest(&self) -> f64 {
        self.sorted[self.sorted.len() - 1].max(0.0)
    }

    /// The derivative of the expected cost by the level, at `level`, between
    /// two neighbouring levels at which the cost changes its form: where
    /// `partly` of the stretches seen are missed in part, and the level lies
    /// in `range`.
    fn slope(&self, level: f64, partly: f64, range: Range, weights: &Weights) -> f64 {
        let weight = (self.sorted.len() as f64 + 1.0) * self.stretch;
        let scale = PRIOR_SCALE + self.largest();
        let near = PRIOR_SCALE + level;
        let far = near + self.stretch;
        // The derivatives of `exceeds_beyond` and of `missed_beyond`.
        let (gaps, missed) = match range {
            Range::FarBelow => (0.0, 0.0),
            Range::Below => (0.0, (scale / far).powi(2) - 1.0),
            Range::Above => (
                -2.0 * scale * scale / (near * near * near),
                (scale / far).powi(2) - (scale / near).powi(2),
            ),
        };
        let off = level - seconds(weights.target);
        weights.latency
            + 2.0 * weights.off_target * off
            + (weights.gap * gaps + weights.missed * (missed - partly)) / weight
    }

    /// The level strictly between `low` and `high` at which the expected
    /// cost has a minimum, if it has one there; in seconds. `low` and `high`
    /// are two neighbouring levels at which the cost changes its form.
    fn turn(&self, low: f64, high: f64, weights: &Weights) -> Option<f64> {
        let middle = f64::midpoint(low, high);
        let largest = self.largest();
        let range = if middle > largest {
            Range::Above
        } else if middle + self.stretch > largest {
            Range::Below
        } else {
            Range::FarBelow
        };
        let partly =
            (above(self.sorted, middle + self.stretch) - above(self.sorted, middle)) as f64;
        let slope = |level: f64| self.slope(level, partly, range, weights);
        if slope(high) <= 0.0 {
            // The cost falls up to the upper level, or has no minimum
            // before it.
            return None;
        }
        let mut from = low;
        if slope(low) >= 0.0 {
            // Far below the largest need and above it, the cost is convex:
            // it rises from the lower level on. Within a stretch below the
            // largest need it is the derivative that is convex, and it can
            // fall below zero and come back. It is least where the second
            // derivative is zero, which only a level aimed at allows.
            let Range::Below = range else {
                return None;
            };
            if weights.off_target <= 0.0 {
                return None;
            }
            let weight = (self.sorted.len() as f64 + 1.0) * self.stretch;
            let scale = PRIOR_SCALE + largest;
            let least = (weights.missed * scale * scale / (weight * weights.off_target)).cbrt()
                - PRIOR_SCALE
                - self.stretch;
            if !(least > low && least < high) || slope(least) >= 0.0 {
                return None;
            }
            from = least;
        }
        // The derivative is negative at `from` and positive at `high`, and
        // passes zero once between them.
        let mut to = high;
        for _ in 0..64 {
            let half = f64::midpoint(from, to);
            if slope(half) < 0.0 {
                from = half;
            } else {
                to = half;
            }
        }
        Some(to)
    }

    /// The level between zero and the ceiling at which the expected cost is
    /// least, in nanoseconds, and that cost.
    fn best(&mut self, weights: &Weights) -> (i64, f64) {
        // The levels at which the cost changes its form: the needs that were
        // seen and a stretch below each.
        self.points.clear();
        self.points.extend([0, CEILING]);
        for need in self.sorted {
            for point in [nanoseconds(*need), nanoseconds(*need - self.stretch)] {
                if point > 0 && point < CEILING {
                    self.points.push(point);
                }
            }
        }
        self.points.sort_unstable();
        self.points.dedup();
        let mut best = (0, f64::INFINITY);
        let mut consider = |level: i64| {
            let cost = self.cost(seconds(level), weights);
            if cost < best.1 {
                best = (level, cost);
            }
        };
        for (at, &low) in self.points.iter().enumerate() {
            consider(low);
            let Some(&high) = self.points.get(at + 1) else {
                break;
            };
            if high - 1 > low {
                consider(high - 1);
            }
            if let Some(turn) = self.turn(seconds(low), seconds(high), weights) {
                // The cost is least at one of the two levels around it.
                // Within the range of `i64`: below the ceiling.
                #[allow(clippy::cast_possible_truncation)]
                let below = (turn * 1e9).floor() as i64;
                for level in [below, below + 1] {
                    if level > low && level < high {
                        consider(level);
                    }
                }
            }
        }
        best
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
    fn no_level_costs_less_than_the_one_found() {
        let mut numbers = Numbers(0x6a09_e667_f3bc_c908);
        for (gap, target, off_target) in [
            (60.0, 0, 0.0),
            (6_000.0, 0, 0.0),
            (600.0, 30_000_000, 2e6),
            (6.0, 60_000_000, 5e7),
            (600.0, 40_000_000, 3e5),
        ] {
            let weights = Weights {
                gap,
                missed: gap * 100.0,
                target,
                off_target,
                ..WEIGHTS
            };
            for (count, every) in [(40, 1.0), (300, 5.0), (300, 1e9), (1_200, 30.0)] {
                let seen = needs(&mut numbers, count, every);
                let choice = Choice {
                    weights,
                    history: count,
                    ..CHOICE
                };
                let mut chooser = Chooser::new(choice, 2_400, 48_000);
                report(&mut chooser, 7, 0, &seen);
                let mut evidence = chooser.gather().expect("evidence");
                let (level, cost) = evidence.best(&weights);
                assert!(
                    (cost - evidence.cost(super::seconds(level), &weights)).abs() <= 1e-9,
                    "{level}"
                );
                // Every level that is a multiple of 5 microseconds, and the
                // levels around each need that was seen and a stretch below
                // it.
                let mut least = (0..=400_000)
                    .map(|i| evidence.cost(super::seconds(i * 5_000), &weights))
                    .fold(f64::INFINITY, f64::min);
                for need in evidence.sorted {
                    for point in [*need, *need - 0.05] {
                        for off in -2..=2 {
                            let near = super::nanoseconds(point) + off;
                            if (0..=super::CEILING).contains(&near) {
                                least = least.min(evidence.cost(super::seconds(near), &weights));
                            }
                        }
                    }
                }
                assert!(
                    cost <= least + 1e-9 * least.abs(),
                    "a gap at {gap}, aimed at {target} with {off_target}, {count} stretches \
                     with pauses every {every} s: level {level} costs {cost}, another {least}"
                );
            }
        }
    }

    #[test]
    fn a_level_just_below_a_need_joins_two_gaps() {
        // Again and again a stretch that needs 50 ms, one that needs 30 ms
        // and one that needs 40 ms, among stretches that need 5 ms. At
        // 30 ms the second of them is played, and two gaps start; a
        // nanosecond below, the three are one gap. Gaps are priced so that
        // this is the least cost of all levels.
        let pattern = [0.005, 0.05, 0.03, 0.04];
        let seen: Vec<f64> = (0..2_000)
            .map(|i| pattern.get(i % 20).copied().unwrap_or(0.005))
            .collect();
        let weights = Weights {
            gap: 5.0,
            missed: 400.0,
            moving: 0.0,
            ..WEIGHTS
        };
        let level = chosen(weights, &seen);
        assert!(level > 0.0299 && level < 0.0301, "{level}");
        assert_eq!(super::nanoseconds(level) % 1_000, 999, "{level}");
    }

    #[test]
    fn stretches_that_need_more_than_all_before_them_come_as_often_as_expected() {
        let mut numbers = Numbers(0x3c6e_f372_fe94_f82b);
        // Needs that nothing sets apart from each other: the same jitter in
        // every stretch.
        let quiet = needs(&mut numbers, 20_000, 1e9);
        let mut chooser = Chooser::new(CHOICE, 2_400, 48_000);
        for (part, some) in quiet.chunks(20).enumerate() {
            report(&mut chooser, 7, part as u64 * 20, some);
            let _ = chooser.choose(20_000_000);
        }
        let checks = chooser.checks();
        assert!(checks.stretches > 19_000, "{checks:?}");
        // About one stretch in the number of stretches kept, and within what
        // chance allows of the number expected.
        assert!(
            checks.expected > 10.0 && checks.expected < 40.0,
            "{checks:?}"
        );
        let off = (checks.largest as f64 - checks.expected).abs();
        assert!(off <= 4.0 * checks.expected.sqrt(), "{checks:?}");
        // Each of them counts between nothing and one.
        assert!(
            checks.beyond > 0.0 && checks.beyond <= checks.largest as f64,
            "{checks:?}"
        );
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

    #[test]
    fn observe_up_to_rejects_future_stretch_and_u64_max_does_not_overflow() {
        let mut chooser = Chooser::new(CHOICE, 2_400, 48_000);
        let mut spoofed = Recent::NONE;
        spoofed.count = 1;
        spoofed.newest = u64::MAX;
        spoofed.needs[0] = 5_000;
        chooser.observe_up_to(7, &spoofed, 100);
        assert_eq!(chooser.choose(20_000_000), None);

        // Even if `newest == u64::MAX` is observed directly, `choose()` must
        // not overflow `newest + 1` or `done + 1`.
        chooser.observe(7, &spoofed);
        let _ = chooser.choose(20_000_000);
        let _ = chooser.choose(20_000_000);
    }

    #[test]
    fn weights_and_choice_validation_reject_nan_negative_and_bad_slope() {
        assert!(CHOICE.validate().is_ok());
        assert!(
            Weights {
                latency: f64::NAN,
                ..WEIGHTS
            }
            .validate()
            .is_err()
        );
        assert!(
            Weights {
                gap: -1.0,
                ..WEIGHTS
            }
            .validate()
            .is_err()
        );
        assert!(
            Weights {
                target: -1,
                ..WEIGHTS
            }
            .validate()
            .is_err()
        );
        assert!(Choice { slope: 0, ..CHOICE }.validate().is_err());
        assert!(
            Choice {
                slope: -5,
                ..CHOICE
            }
            .validate()
            .is_err()
        );
        assert!(
            Choice {
                slope: 1_000_000_000,
                ..CHOICE
            }
            .validate()
            .is_err()
        );
        assert!(
            Choice {
                history: 0,
                ..CHOICE
            }
            .validate()
            .is_err()
        );

        // A chooser constructed directly with NaN weights or window 0 does not
        // panic and returns None.
        let mut bad = Chooser::new(
            Choice {
                weights: Weights {
                    latency: f64::NAN,
                    ..WEIGHTS
                },
                ..CHOICE
            },
            0,
            48_000,
        );
        let mut recent = Recent::NONE;
        recent.count = 1;
        recent.newest = 20;
        recent.needs[0] = 5_000;
        bad.observe(1, &recent);
        assert_eq!(bad.choose(20_000_000), None);
    }

    #[test]
    fn check_is_idempotent_when_called_repeatedly_without_new_stretches() {
        let mut numbers = Numbers(0xdead_beef_cafe_babe);
        let quiet = needs(&mut numbers, 80, 1e9);
        let mut chooser = Chooser::new(CHOICE, 2_400, 48_000);
        report(&mut chooser, 7, 0, &quiet);
        let level = chooser.choose(20_000_000).unwrap_or(20_000_000);
        let first = chooser.checks();
        assert_eq!(chooser.choose(level), None);
        assert_eq!(chooser.checks(), first);
    }
}
