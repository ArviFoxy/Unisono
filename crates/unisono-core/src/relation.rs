// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The relation between two clocks, from packets in one direction.
//!
//! Each packet gives a [`Sample`]: the sender's clock when the packet left,
//! and the receiver's clock at arrival minus that. The second number is the
//! offset between the two clocks plus the packet's delay, and a delay is never
//! negative. All samples therefore lie on or above the true relation shifted
//! by the smallest delay, and the estimate is the highest line that lies on or
//! below every recent sample.
//!
//! All arithmetic here is exact: times and values are integers, and the
//! geometry compares products of their differences.

use crate::fixed::{div_floor, saturate};

/// One packet's contribution: a time on the sender's clock and a value, both
/// in nanoseconds. The value is a reading of the receiver's clock minus the
/// reading `time` of the sender's.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Sample {
    /// The sender's clock when the packet left.
    pub time: i64,
    /// The receiver's clock at arrival, minus `time`.
    pub value: i64,
}

/// A line: its value at a time, and its slope as a quotient `rise / run`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Line {
    /// A time at which the line's value is `value`.
    pub time: i64,
    /// The line's value at `time`.
    pub value: i64,
    /// The change of the value over a time of `run`.
    pub rise: i64,
    /// The time over which the value changes by `rise`; positive.
    pub run: i64,
}

impl Line {
    /// The line's value at `time`, rounded toward negative infinity and
    /// limited to the range of `i64`.
    #[must_use]
    pub fn eval(&self, time: i64) -> i64 {
        let elapsed = time.saturating_sub(self.time);
        // Two 64-bit numbers: the product cannot wrap.
        let product = (self.rise as i128).wrapping_mul(elapsed as i128);
        let change = div_floor(product, self.run);
        saturate((self.value as i128).saturating_add(change))
    }
}

/// How sample `c` lies relative to the line from sample `a` to sample `b`:
/// positive when `c` is above the line, zero when on it, negative when below.
/// `a` is taken to be earlier than `b`.
fn side(a: Sample, b: Sample, c: Sample) -> i128 {
    let run = b.time.saturating_sub(a.time);
    let rise = b.value.saturating_sub(a.value);
    let across = c.time.saturating_sub(a.time);
    let up = c.value.saturating_sub(a.value);
    // Each product is of two 64-bit numbers and cannot wrap; their difference
    // can exceed 128 bits by one, and saturating keeps its sign.
    let left = (run as i128).wrapping_mul(up as i128);
    let right = (rise as i128).wrapping_mul(across as i128);
    left.saturating_sub(right)
}

/// An estimator of the relation between two clocks, which remembers up to `M`
/// samples.
///
/// Packets are grouped into windows by the caller, for instance by their
/// index in the stream. From each window the estimator keeps the one sample
/// that lies lowest against its current line. Kept samples older than `span`
/// are forgotten. After every window the estimate is the line under all kept
/// samples that is highest at the middle of the time they cover.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub struct Estimator<const M: usize> {
    /// The kept samples, oldest first, in the first `len` places.
    kept: [Sample; M],
    len: usize,
    /// How long a kept sample is remembered, on the sender's clock.
    span: i64,
    /// The window that `lowest` belongs to.
    window: u64,
    /// The lowest sample of the current window so far, with its height above
    /// the line.
    lowest: Option<(Sample, i64)>,
    line: Option<Line>,
}

impl<const M: usize> Estimator<M> {
    /// An estimator that has seen nothing and remembers samples for `span`
    /// nanoseconds.
    #[must_use]
    pub fn new(span: i64) -> Self {
        Estimator {
            kept: [Sample { time: 0, value: 0 }; M],
            len: 0,
            span,
            window: 0,
            lowest: None,
            line: None,
        }
    }

    /// The current estimate, once a sample has been kept.
    #[must_use]
    pub fn line(&self) -> Option<Line> {
        self.line
    }

    /// The number of samples kept.
    #[must_use]
    pub fn kept(&self) -> usize {
        self.len
    }

    /// The kept sample at `index`, counted from the oldest.
    fn sample(&self, index: usize) -> Option<Sample> {
        if index >= self.len {
            return None;
        }
        match self.kept.get(index) {
            Some(sample) => Some(*sample),
            None => None,
        }
    }

    /// The kept sample whose index is at `position` of `hull`.
    fn hull_sample(&self, hull: &[usize; M], position: usize) -> Option<Sample> {
        match hull.get(position) {
            Some(index) => self.sample(*index),
            None => None,
        }
    }

    /// Puts `sample` at `index` of the room for kept samples, and says
    /// whether there is such a place.
    fn put(&mut self, index: usize, sample: Sample) -> bool {
        match self.kept.get_mut(index) {
            Some(place) => {
                *place = sample;
                true
            }
            None => false,
        }
    }

    /// Takes in the sample of one packet of window `window`.
    ///
    /// A window ends when a sample of another window is given, or when
    /// [`Estimator::end_window`] is called.
    pub fn observe(&mut self, window: u64, sample: Sample) {
        if window != self.window {
            self.end_window();
            self.window = window;
        }
        let height = match self.line {
            Some(line) => sample.value.saturating_sub(line.eval(sample.time)),
            None => sample.value,
        };
        let lower = match self.lowest {
            Some((_, lowest)) => height < lowest,
            None => true,
        };
        if lower {
            self.lowest = Some((sample, height));
        }
    }

    /// Ends the current window: its lowest sample is kept, old samples are
    /// forgotten and the line is fitted again.
    pub fn end_window(&mut self) {
        if let Some((sample, _)) = self.lowest.take() {
            self.keep(sample);
            self.forget_before(sample.time.saturating_sub(self.span));
            self.fit();
        }
    }

    /// Appends `sample` to the kept samples, whose times increase.
    ///
    /// A sample that is not later than the last kept one is left out when it
    /// is older by no more than the span: packets can overtake each other.
    /// When it is older by more, what is kept does not belong to the clock
    /// the sample was stamped with, and everything kept is dropped. A count
    /// of kept samples that exceeds the room for them cannot arise from
    /// samples; it is treated the same way.
    fn keep(&mut self, sample: Sample) {
        if self.len > M {
            self.len = 0;
            self.line = None;
        }
        let last = match self.len.checked_sub(1) {
            Some(index) => self.sample(index),
            None => None,
        };
        if let Some(last) = last
            && sample.time <= last.time
        {
            if last.time.saturating_sub(sample.time) <= self.span {
                return;
            }
            self.len = 0;
            self.line = None;
        }
        if self.len >= M {
            self.drop_oldest(1);
        }
        if self.put(self.len, sample) {
            self.len = self.len.saturating_add(1);
        }
    }

    /// Forgets the kept samples with a time before `time`.
    fn forget_before(&mut self, time: i64) {
        let mut old = 0usize;
        while old < self.len {
            match self.sample(old) {
                Some(sample) if sample.time < time => old = old.saturating_add(1),
                _ => break,
            }
        }
        self.drop_oldest(old);
    }

    /// Removes the `count` oldest kept samples.
    fn drop_oldest(&mut self, count: usize) {
        if count == 0 {
            return;
        }
        let mut to = 0usize;
        let mut from = count;
        while from < self.len {
            if let Some(sample) = self.sample(from) {
                self.put(to, sample);
            }
            to = to.saturating_add(1);
            from = from.saturating_add(1);
        }
        self.len = to;
    }

    /// Fits the line to the kept samples.
    fn fit(&mut self) {
        let (Some(first), Some(last)) = (self.sample(0), self.sample(self.len.saturating_sub(1)))
        else {
            self.line = None;
            return;
        };
        if self.len == 1 {
            // One sample fixes a value and no slope: keep the slope there was.
            let (rise, run) = match self.line {
                Some(line) => (line.rise, line.run),
                None => (0, 1),
            };
            self.line = Some(Line {
                time: first.time,
                value: first.value,
                rise,
                run,
            });
            return;
        }
        let half = div_floor(last.time.saturating_sub(first.time) as i128, 2);
        let middle = first.time.saturating_add(saturate(half));
        if let Some((from, to)) = self.bridge(middle)
            && self.is_under(from, to)
        {
            self.line = Some(Line {
                time: from.time,
                value: from.value,
                rise: to.value.saturating_sub(from.value),
                run: to.time.saturating_sub(from.time),
            });
        }
    }

    /// The two kept samples through which the highest line under all kept
    /// samples at time `middle` passes: an edge of their lower convex hull
    /// with `middle` between its ends.
    fn bridge(&self, middle: i64) -> Option<(Sample, Sample)> {
        // The lower hull, by Andrew's monotone chain: indices of kept samples.
        let mut hull = [0usize; M];
        let mut size = 0usize;
        let mut next = 0usize;
        while next < self.len {
            let Some(candidate) = self.sample(next) else {
                break;
            };
            // Remove the hull's last sample while it is on or above the line
            // from the one before it to the candidate.
            while size >= 2 {
                let before = self.hull_sample(&hull, size.saturating_sub(2));
                let end = self.hull_sample(&hull, size.saturating_sub(1));
                match (before, end) {
                    (Some(a), Some(b)) if side(a, candidate, b) >= 0 => {
                        size = size.saturating_sub(1);
                    }
                    _ => break,
                }
            }
            if let Some(place) = hull.get_mut(size) {
                *place = next;
                size = size.saturating_add(1);
            }
            next = next.saturating_add(1);
        }
        // The edge that has `middle` between its ends.
        let mut edge = 0usize;
        while edge.saturating_add(1) < size {
            if let Some(from) = self.hull_sample(&hull, edge)
                && let Some(to) = self.hull_sample(&hull, edge.saturating_add(1))
                && from.time <= middle
                && middle <= to.time
                && from.time < to.time
            {
                return Some((from, to));
            }
            edge = edge.saturating_add(1);
        }
        None
    }

    /// Whether no kept sample lies below the line from `from` to `to`.
    fn is_under(&self, from: Sample, to: Sample) -> bool {
        let mut index = 0usize;
        while index < self.len {
            if let Some(sample) = self.sample(index)
                && side(from, to, sample) < 0
            {
                return false;
            }
            index = index.saturating_add(1);
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use super::{Estimator, Line, Sample, side};

    fn sample(time: i64, value: i64) -> Sample {
        Sample { time, value }
    }

    /// Gives each sample its own window.
    fn feed<const M: usize>(estimator: &mut Estimator<M>, samples: &[Sample]) {
        for (window, &s) in (1u64..).zip(samples) {
            estimator.observe(window, s);
        }
        estimator.end_window();
    }

    #[test]
    fn a_line_is_evaluated_with_rounding_downward() {
        let line = Line {
            time: 100,
            value: 7,
            rise: 1,
            run: 3,
        };
        assert_eq!(line.eval(100), 7);
        assert_eq!(line.eval(103), 8);
        assert_eq!(line.eval(104), 8);
        // One third of -1 is rounded down to -1.
        assert_eq!(line.eval(99), 6);
        assert_eq!(line.eval(97), 6);
    }

    #[test]
    fn side_tells_above_from_below() {
        let (a, b) = (sample(0, 0), sample(10, 10));
        assert!(side(a, b, sample(5, 6)) > 0);
        assert_eq!(side(a, b, sample(5, 5)), 0);
        assert!(side(a, b, sample(5, 4)) < 0);
        assert!(side(a, b, sample(20, 19)) < 0);
    }

    #[test]
    fn samples_on_a_line_give_that_line() {
        let mut estimator = Estimator::<8>::new(1_000_000);
        let samples: Vec<Sample> = (0..6).map(|k| sample(k * 100, 50 + k * 3)).collect();
        feed(&mut estimator, &samples);
        let line = estimator.line().expect("a line");
        for s in &samples {
            assert_eq!(line.eval(s.time), s.value);
        }
        assert_eq!(line.eval(1000), 80);
    }

    #[test]
    fn delayed_samples_do_not_move_the_line() {
        // The relation is value = 1000 + time / 100. Half of the samples carry a delay.
        let mut estimator = Estimator::<16>::new(1_000_000);
        let delays = [0, 700, 0, 0, 90_000, 3, 0, 12_000, 0, 0, 450, 0];
        let samples: Vec<Sample> = delays
            .iter()
            .zip(0i64..)
            .map(|(&delay, k)| sample(k * 1000, 1000 + k * 10 + delay))
            .collect();
        feed(&mut estimator, &samples);
        let line = estimator.line().expect("a line");
        for k in 0..20 {
            assert_eq!(line.eval(k * 1000), 1000 + k * 10, "at sample time {k}");
        }
    }

    #[test]
    fn the_lowest_sample_of_each_window_is_the_one_kept() {
        let mut estimator = Estimator::<8>::new(1_000_000);
        // Two windows of three packets; the undelayed ones are (10, 100) and (40, 130).
        for (window, s) in [
            (1, sample(0, 500)),
            (1, sample(10, 100)),
            (1, sample(20, 300)),
            (2, sample(30, 900)),
            (2, sample(40, 130)),
            (2, sample(50, 141)),
        ] {
            estimator.observe(window, s);
        }
        estimator.end_window();
        assert_eq!(estimator.kept(), 2);
        let line = estimator.line().expect("a line");
        assert_eq!((line.eval(10), line.eval(40)), (100, 130));
    }

    #[test]
    fn selection_within_a_window_is_against_the_line_and_not_the_raw_value() {
        // A steep relation: value falls by 100 per unit of time.
        let mut estimator = Estimator::<8>::new(1_000_000);
        feed(&mut estimator, &[sample(0, 10_000), sample(10, 9_000)]);
        // In the next window the later packet has the smaller value but was
        // delayed by 50; the earlier one was not delayed.
        estimator.observe(7, sample(20, 8_000));
        estimator.observe(7, sample(21, 7_950));
        estimator.end_window();
        let line = estimator.line().expect("a line");
        assert_eq!(line.eval(20), 8_000);
        assert_eq!(line.eval(21), 7_900);
    }

    #[test]
    fn samples_older_than_the_span_are_forgotten() {
        let mut estimator = Estimator::<8>::new(250);
        // An early sample far below the later ones would hold the line down.
        feed(
            &mut estimator,
            &[
                sample(0, 0),
                sample(100, 1_000),
                sample(200, 1_000),
                sample(300, 1_000),
            ],
        );
        assert_eq!(estimator.kept(), 3);
        let line = estimator.line().expect("a line");
        assert_eq!(line.eval(300), 1_000);
        assert_eq!(line.eval(400), 1_000);
    }

    #[test]
    fn a_full_memory_drops_its_oldest_sample() {
        let mut estimator = Estimator::<4>::new(1_000_000);
        let samples: Vec<Sample> = (0..10).map(|k| sample(k * 10, k * k)).collect();
        feed(&mut estimator, &samples);
        assert_eq!(estimator.kept(), 4);
        // Kept: times 60, 70, 80, 90 with values 36, 49, 64, 81, a convex
        // curve. The middle time is 75, between the samples at 70 and 80.
        let line = estimator.line().expect("a line");
        assert_eq!((line.eval(70), line.eval(80)), (49, 64));
    }

    #[test]
    fn a_time_far_in_the_past_starts_the_memory_anew() {
        let mut estimator = Estimator::<8>::new(500);
        feed(
            &mut estimator,
            &[sample(1000, 5), sample(2000, 6), sample(3000, 7)],
        );
        // More than the span before the last kept sample: another clock.
        feed(&mut estimator, &[sample(10, 900)]);
        assert_eq!(estimator.kept(), 1);
        assert_eq!(estimator.line().expect("a line").eval(10), 900);
    }

    #[test]
    fn a_sample_that_was_overtaken_is_left_out() {
        let mut estimator = Estimator::<8>::new(5_000);
        feed(
            &mut estimator,
            &[sample(1000, 5), sample(2000, 6), sample(3000, 7)],
        );
        let before = estimator.line();
        // Within the span before the last kept sample: a packet that came late.
        feed(&mut estimator, &[sample(2500, -900)]);
        assert_eq!(estimator.kept(), 3);
        assert_eq!(estimator.line(), before);
    }

    #[test]
    fn an_impossible_count_of_kept_samples_is_dropped_at_once() {
        let mut estimator = Estimator::<4>::new(1_000_000);
        estimator.len = usize::MAX;
        feed(&mut estimator, &[sample(10, 1), sample(20, 2)]);
        assert_eq!(estimator.kept(), 2);
        assert_eq!(estimator.line().expect("a line").eval(20), 2);
    }

    /// The fitted line against every pair of samples: it must lie under all
    /// kept samples, and no line through two samples on either side of the
    /// middle time that also lies under all of them may be higher there.
    #[test]
    fn the_line_is_under_all_samples_and_highest_in_the_middle() {
        // A small generator of numbers, the same on every run.
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut draw = |bound: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) % bound
        };
        for _ in 0..500 {
            let count = 2 + usize::try_from(draw(14)).unwrap_or(0);
            let mut time = 0i64;
            let samples: Vec<Sample> = (0..count)
                .map(|_| {
                    time += 1 + i64::try_from(draw(1000)).unwrap_or(0);
                    sample(time, i64::try_from(draw(5000)).unwrap_or(0) - 2500)
                })
                .collect();
            let mut estimator = Estimator::<16>::new(i64::MAX);
            feed(&mut estimator, &samples);
            let line = estimator.line().expect("a line");
            let (first, last) = (samples[0], samples[count - 1]);
            let middle = first.time + (last.time - first.time) / 2;
            let from = samples
                .iter()
                .find(|s| s.time == line.time)
                .copied()
                .expect("the line starts at a sample");
            let to = sample(from.time + line.run, from.value + line.rise);
            assert!(samples.contains(&to), "the line ends at a sample");
            assert!(
                from.time <= middle && middle <= to.time,
                "the middle is between the line's two samples"
            );
            for s in &samples {
                assert!(side(from, to, *s) >= 0, "a sample lies below the line");
            }
        }
    }
}
