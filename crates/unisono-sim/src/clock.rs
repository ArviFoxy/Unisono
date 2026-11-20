// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Simulated oscillators.
//!
//! An oscillator runs fast or slow by its fractional frequency, and that
//! frequency wanders: a random walk, plus changes a test puts in by hand.

use crate::random::Generator;
use crate::{TrueTime, nanos_to_seconds, seconds_to_nanos};

/// How often the random walk of the frequency takes a step, in nanoseconds.
const WALK_STEP: i64 = 10_000_000;

/// What an oscillator is like.
#[derive(Clone, Copy, Debug)]
pub struct OscillatorModel {
    /// Reading minus true time at the start, in seconds.
    pub offset: f64,
    /// Fractional frequency at the start: 1e-5 runs 10 parts per million fast.
    pub frequency: f64,
    /// Variance that the random walk adds to the fractional frequency per second.
    pub walk: f64,
}

/// A simulated oscillator.
///
/// It is read at true times that do not go backwards, as a simulation does.
#[derive(Clone, Debug)]
pub struct Oscillator {
    generator: Generator,
    walk: f64,
    /// Reading minus true time at `at`, in seconds.
    offset: f64,
    frequency: f64,
    at: TrueTime,
    next_step: TrueTime,
}

impl Oscillator {
    /// An oscillator that follows `model`, drawing its random walk from `generator`.
    #[must_use]
    pub fn new(model: OscillatorModel, generator: Generator) -> Oscillator {
        Oscillator {
            generator,
            walk: model.walk,
            offset: model.offset,
            frequency: model.frequency,
            at: TrueTime::ZERO,
            next_step: TrueTime(WALK_STEP),
        }
    }

    fn advance(&mut self, to: TrueTime) {
        assert!(
            to >= self.at,
            "an oscillator is read at times that do not go backwards"
        );
        while self.next_step <= to {
            self.offset += self.frequency * nanos_to_seconds(self.next_step.0 - self.at.0);
            self.at = self.next_step;
            let deviation = (self.walk * nanos_to_seconds(WALK_STEP)).sqrt();
            self.frequency += deviation * self.generator.normal();
            self.next_step = TrueTime(self.next_step.0 + WALK_STEP);
        }
        self.offset += self.frequency * nanos_to_seconds(to.0 - self.at.0);
        self.at = to;
    }

    /// Reading minus true time at `at`, in seconds, without rounding.
    pub fn offset(&mut self, at: TrueTime) -> f64 {
        self.advance(at);
        self.offset
    }

    /// The reading at true time `at`, in nanoseconds.
    pub fn read(&mut self, at: TrueTime) -> i64 {
        at.0.saturating_add(seconds_to_nanos(self.offset(at)))
    }

    /// The fractional frequency at true time `at`.
    pub fn frequency(&mut self, at: TrueTime) -> f64 {
        self.advance(at);
        self.frequency
    }

    /// Changes the fractional frequency by `change` at true time `at`.
    pub fn step_frequency(&mut self, at: TrueTime, change: f64) {
        self.advance(at);
        self.frequency += change;
    }
}

/// An oscillator whose whole course is kept, so that it can be read at any
/// true time, earlier or later than the last, and asked when it shows a given
/// reading.
///
/// A device that counts frames is such an oscillator too: its count is its
/// reading in seconds times its nominal rate.
#[derive(Clone, Debug)]
pub struct Course {
    generator: Generator,
    walk: f64,
    /// Reading minus true time, and fractional frequency, at every multiple
    /// of the walk's step, as far as the course has been drawn.
    steps: Vec<(f64, f64)>,
}

impl Course {
    /// A course that follows `model`, drawing its random walk from `generator`.
    #[must_use]
    pub fn new(model: OscillatorModel, generator: Generator) -> Course {
        Course {
            generator,
            walk: model.walk,
            steps: vec![(model.offset, model.frequency)],
        }
    }

    /// The step at or before `at`, drawing the course that far.
    fn step(&mut self, at: TrueTime) -> (usize, f64) {
        let nanos = at.0.max(0);
        let index = usize::try_from(nanos / WALK_STEP).unwrap_or(usize::MAX - 1);
        let step_seconds = nanos_to_seconds(WALK_STEP);
        while self.steps.len() <= index {
            let (offset, frequency) = self.steps.last().copied().unwrap_or((0.0, 0.0));
            let deviation = (self.walk * step_seconds).sqrt();
            self.steps.push((
                offset + frequency * step_seconds,
                frequency + deviation * self.generator.normal(),
            ));
        }
        // An index below 2^53 is exact as a float.
        #[allow(clippy::cast_precision_loss)]
        let into = nanos_to_seconds(nanos) - index as f64 * step_seconds;
        (index, into)
    }

    /// Reading minus true time at `at`, in seconds.
    pub fn offset(&mut self, at: TrueTime) -> f64 {
        let (index, into) = self.step(at);
        let (offset, frequency) = self.steps.get(index).copied().unwrap_or((0.0, 0.0));
        offset + frequency * into
    }

    /// The reading at true time `at`, in seconds.
    pub fn seconds(&mut self, at: TrueTime) -> f64 {
        at.seconds() + self.offset(at)
    }

    /// The reading at true time `at`, in nanoseconds.
    pub fn read(&mut self, at: TrueTime) -> i64 {
        at.0.saturating_add(seconds_to_nanos(self.offset(at)))
    }

    /// The fractional frequency at true time `at`.
    pub fn frequency(&mut self, at: TrueTime) -> f64 {
        let (index, _) = self.step(at);
        self.steps.get(index).map_or(0.0, |step| step.1)
    }

    /// The true time at which the reading is `reading` seconds.
    pub fn when(&mut self, reading: f64) -> TrueTime {
        // The reading runs within a few parts in ten thousand of true time,
        // so each round brings the error down by that factor.
        let mut at = TrueTime::from_seconds(reading);
        for _ in 0..6 {
            at = TrueTime::from_seconds(reading - self.offset(at));
        }
        at
    }
}

#[cfg(test)]
mod tests {
    use super::{Course, Oscillator, OscillatorModel};
    use crate::TrueTime;
    use crate::random::Generator;

    #[test]
    fn a_steady_oscillator_gains_its_frequency_times_the_elapsed_time() {
        let model = OscillatorModel {
            offset: 0.25,
            frequency: 20e-6,
            walk: 0.0,
        };
        let mut clock = Oscillator::new(model, Generator::new(1));
        assert_eq!(clock.read(TrueTime::ZERO), 250_000_000);
        // After 1000 s it has gained 20 ms.
        assert_eq!(
            clock.read(TrueTime::from_seconds(1000.0)),
            1_000_000_000_000 + 250_000_000 + 20_000_000
        );
    }

    #[test]
    fn a_frequency_step_changes_the_rate_from_then_on() {
        let model = OscillatorModel {
            offset: 0.0,
            frequency: 0.0,
            walk: 0.0,
        };
        let mut clock = Oscillator::new(model, Generator::new(1));
        clock.step_frequency(TrueTime::from_seconds(10.0), 1e-6);
        let gained = clock.offset(TrueTime::from_seconds(110.0));
        assert!((gained - 100e-6).abs() < 1e-12, "gained {gained}");
    }

    /// A random walk of variance `walk` per second has a frequency with
    /// variance `walk * t` after `t` seconds. Over 400 oscillators the sample
    /// variance is within a quarter of that except with negligible probability.
    #[test]
    fn the_frequency_walks_with_the_stated_variance() {
        let (walk, seconds) = (1e-18, 100.0);
        let parent = Generator::new(3);
        let squares: f64 = (0..400)
            .map(|i| {
                let model = OscillatorModel {
                    offset: 0.0,
                    frequency: 0.0,
                    walk,
                };
                Oscillator::new(model, parent.fork(i))
                    .frequency(TrueTime::from_seconds(seconds))
                    .powi(2)
            })
            .sum();
        let ratio = squares / 400.0 / (walk * seconds);
        assert!((0.75..1.25).contains(&ratio), "variance ratio {ratio}");
    }

    #[test]
    #[should_panic(expected = "do not go backwards")]
    fn reading_at_an_earlier_time_is_refused() {
        let model = OscillatorModel {
            offset: 0.0,
            frequency: 0.0,
            walk: 0.0,
        };
        let mut clock = Oscillator::new(model, Generator::new(1));
        clock.read(TrueTime(100));
        clock.read(TrueTime(99));
    }

    #[test]
    fn a_course_is_read_in_any_order_and_inverted() {
        let model = OscillatorModel {
            offset: 3_600.0,
            frequency: 50e-6,
            walk: 1e-16,
        };
        let mut course = Course::new(model, Generator::new(3));
        let late = course.read(TrueTime::from_seconds(100.0));
        let early = course.read(TrueTime::from_seconds(1.0));
        // Reading an earlier time afterwards changes nothing about a later one.
        assert_eq!(course.read(TrueTime::from_seconds(100.0)), late);
        assert!(late - early > 99_000_000_000);
        // The reading is 50 parts per million fast: after a second, 50 microseconds.
        let gained = early - course.read(TrueTime::ZERO) - 1_000_000_000;
        assert!((gained - 50_000).abs() < 50, "gained {gained}");
        // The time at which it shows a reading is the time it was read at.
        let reading = course.seconds(TrueTime::from_seconds(42.5));
        let found = course.when(reading);
        assert!((found.0 - 42_500_000_000).abs() <= 1, "found {found:?}");
    }
}
