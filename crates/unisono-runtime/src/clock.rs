// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The host's clocks.
//!
//! Every time in unisono is a reading of the host's **raw clock**: the
//! monotonic clock that no time service adjusts (`CLOCK_MONOTONIC_RAW`). The
//! kernel stamps packets with the **system clock** (`CLOCK_REALTIME`), which
//! a time service slews and sometimes steps, so the two run apart by tens of
//! parts per million and a relation between them measured once is wrong by
//! a hundred microseconds a few seconds later. A [`Tracker`] therefore
//! measures the relation again and again, and converts a stamp of the system
//! clock only with a measurement that is recent.
//!
//! A measurement reads the raw clock, the system clock, and the raw clock
//! again. The system clock was read somewhere between the two raw readings,
//! so taking the middle is wrong by at most half the time between them.
//!
//! # What a conversion assumes
//!
//! Between a measurement and the stamp that is converted with it, the rate
//! of the system clock against the raw clock changes by at most
//! [`RATE_CHANGE`], and where the rate has not been measured yet it is at
//! most [`LARGEST_RATE`] in size. The kernel slews the system clock by at
//! most 500 parts per million for a frequency correction and as much again
//! for a correction of the time, which gives both numbers. A step of the
//! system clock between a stamp and the next measurement is outside what a
//! conversion can know; the tracker notices the step at that measurement and
//! forgets the rate.

use std::sync::atomic::{AtomicI64, Ordering};

/// The number of nanoseconds in a second.
const SECOND: i64 = 1_000_000_000;

/// The largest change of the rate of the system clock against the raw clock
/// that a conversion allows for, in parts per billion.
pub const RATE_CHANGE: i64 = 500_000;

/// The largest rate of the system clock against the raw clock that a
/// conversion allows for where it has not measured the rate, in parts per
/// billion.
pub const LARGEST_RATE: i64 = 1_000_000;

/// How far apart two measurements are, at the least, for a rate to be taken
/// from them, in nanoseconds.
const SHORTEST_BASELINE: i64 = 20_000_000;

/// How far back the older of the two measurements for the rate is kept, in
/// nanoseconds: between this and twice this.
const BASELINE: i64 = 500_000_000;

/// Reads a clock, in nanoseconds. Zero if the system refuses, which it does
/// for no clock that [`supported`] accepts.
fn read(clock: libc::clockid_t) -> i64 {
    // SAFETY: an all-zero timespec is a valid value of the type; some
    // targets give it padding fields that cannot be named.
    let mut time: libc::timespec = unsafe { std::mem::zeroed() };
    // SAFETY: `time` is a valid place for one timespec and lives through the
    // call, which writes nothing else.
    let result = unsafe { libc::clock_gettime(clock, &raw mut time) };
    if result != 0 {
        return 0;
    }
    // The fields are 32 bits wide on some targets and 64 on others.
    #[allow(clippy::useless_conversion)]
    let (seconds, nanos) = (i64::from(time.tv_sec), i64::from(time.tv_nsec));
    seconds.saturating_mul(SECOND).saturating_add(nanos)
}

/// How far this process moves the host's raw clock, in nanoseconds.
static OFFSET: AtomicI64 = AtomicI64::new(0);

/// How much faster this process lets the host's raw clock run, in parts per
/// billion.
static SKEW: AtomicI64 = AtomicI64::new(0);

/// Gives this process a raw clock of its own: from now on [`raw`] reads the
/// host's raw clock `r` as `r + offset + r * skew / 10^9`.
///
/// This is for tests that run several processes on one host, which would
/// otherwise share one clock: each process can be given an offset and a rate
/// as a host of its own would have. Everything in unisono that reads the
/// raw clock, kernel stamps of packets included, which are converted to it,
/// then sees the clock of the process. A program sets it once, before it
/// reads a clock.
pub fn shift(offset: i64, skew: i64) {
    OFFSET.store(offset, Ordering::Relaxed);
    SKEW.store(skew, Ordering::Relaxed);
}

/// The raw clock now, in nanoseconds: the host's, moved as [`shift`] says.
#[must_use]
pub fn raw() -> i64 {
    let host = read(libc::CLOCK_MONOTONIC_RAW);
    let offset = OFFSET.load(Ordering::Relaxed);
    let skew = SKEW.load(Ordering::Relaxed);
    if offset == 0 && skew == 0 {
        return host;
    }
    // A 64-bit time times a skew of 64 bits: below 2^127.
    let gained = i128::from(host) * i128::from(skew) / i128::from(SECOND);
    let moved = i128::from(host) + i128::from(offset) + gained;
    i64::try_from(moved).unwrap_or(if moved < 0 { i64::MIN } else { i64::MAX })
}

/// The system clock now, in nanoseconds.
#[must_use]
pub fn system() -> i64 {
    read(libc::CLOCK_REALTIME)
}

/// The monotonic clock now, in nanoseconds: the clock that audio systems
/// give their times in, which a time service slews.
#[must_use]
pub fn monotonic() -> i64 {
    read(libc::CLOCK_MONOTONIC)
}

/// A clock that a [`Tracker`] relates to the raw clock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Other {
    /// The system clock, which the kernel stamps packets with.
    System,
    /// The monotonic clock, which audio systems give their times in.
    Monotonic,
}

impl Other {
    fn read(self) -> i64 {
        match self {
            Other::System => system(),
            Other::Monotonic => monotonic(),
        }
    }
}

/// Whether this host has both clocks.
#[must_use]
pub fn supported() -> bool {
    raw() != 0 && system() != 0
}

/// One measurement of the system clock against the raw clock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reading {
    /// The raw clock at the measurement: the middle of the two readings
    /// around the reading of the system clock.
    pub raw: i64,
    /// The system clock minus the raw clock then.
    pub offset: i64,
    /// Half the time between the two readings of the raw clock, rounded up:
    /// `offset` is within this of the truth.
    pub error: i64,
}

/// Measures the system clock against the raw clock `tries` times, at least
/// once, and returns the measurement with the smallest error.
#[must_use]
pub fn measure(tries: u32) -> Reading {
    measure_of(Other::System, tries)
}

/// Measures `other` against the raw clock `tries` times, at least once, and
/// returns the measurement with the smallest error.
#[must_use]
pub fn measure_of(other: Other, tries: u32) -> Reading {
    let mut best = once(other);
    for _ in 1..tries {
        let reading = once(other);
        if reading.error < best.error {
            best = reading;
        }
    }
    best
}

fn once(other: Other) -> Reading {
    let before = raw();
    let between = other.read();
    let after = raw();
    let width = after.saturating_sub(before).max(0);
    let middle = before.saturating_add(width / 2);
    Reading {
        raw: middle,
        offset: between.saturating_sub(middle),
        error: width.saturating_add(1) / 2,
    }
}

/// A time on the raw clock that a stamp of the system clock was converted
/// to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Converted {
    /// The reading of the raw clock, in nanoseconds.
    pub time: i64,
    /// How far `time` may be from the truth either way, in nanoseconds,
    /// under the assumptions of this module.
    pub error: i64,
}

/// Why a stamp was not converted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unconverted {
    /// The relation between the clocks has not been measured.
    Unmeasured,
    /// The stamp is further from the latest measurement than the tracker
    /// allows, by this many nanoseconds in all.
    TooOld(i64),
}

/// The relation between another clock and the raw clock, kept current: the
/// system clock, unless the tracker is made for another.
#[derive(Clone, Copy, Debug)]
pub struct Tracker {
    /// The clock that is related to the raw clock.
    other: Other,
    longest_age: i64,
    /// The older measurement that the rate is taken from.
    base: Option<Reading>,
    /// The measurement that becomes the base next.
    following: Option<Reading>,
    latest: Option<Reading>,
}

/// `value * numerator / denominator`, rounded toward zero and limited to the
/// range of `i64`; zero for a denominator of zero.
fn scale(value: i64, numerator: i64, denominator: i64) -> i64 {
    if denominator == 0 {
        return 0;
    }
    let wide = i128::from(value) * i128::from(numerator) / i128::from(denominator);
    i64::try_from(wide).unwrap_or(if wide < 0 { i64::MIN } else { i64::MAX })
}

impl Tracker {
    /// A tracker that has measured nothing and converts no stamp that is
    /// further than `longest_age` nanoseconds from its latest measurement.
    #[must_use]
    pub const fn new(longest_age: i64) -> Tracker {
        Tracker::of(Other::System, longest_age)
    }

    /// A tracker of `other` against the raw clock, which has measured
    /// nothing and converts no time that is further than `longest_age`
    /// nanoseconds from its latest measurement.
    #[must_use]
    pub const fn of(other: Other, longest_age: i64) -> Tracker {
        Tracker {
            other,
            longest_age,
            base: None,
            following: None,
            latest: None,
        }
    }

    /// The latest measurement.
    #[must_use]
    pub fn latest(&self) -> Option<Reading> {
        self.latest
    }

    /// The two measurements that the rate is taken from, if they are far
    /// enough apart.
    fn pair(&self) -> Option<(Reading, Reading)> {
        let (base, latest) = (self.base?, self.latest?);
        (latest.raw.saturating_sub(base.raw) >= SHORTEST_BASELINE).then_some((base, latest))
    }

    /// The rate of the system clock against the raw clock, in parts per
    /// billion, once two measurements far enough apart give one.
    #[must_use]
    pub fn rate(&self) -> Option<i64> {
        let (base, latest) = self.pair()?;
        Some(scale(
            latest.offset.saturating_sub(base.offset),
            SECOND,
            latest.raw.saturating_sub(base.raw),
        ))
    }

    /// Takes in a measurement that is later than the ones before it.
    pub fn take(&mut self, reading: Reading) {
        if let Some(latest) = self.latest {
            let elapsed = reading.raw.saturating_sub(latest.raw);
            let expected =
                latest
                    .offset
                    .saturating_add(scale(elapsed, self.rate().unwrap_or(0), SECOND));
            let allowed = reading
                .error
                .saturating_add(latest.error)
                .saturating_add(scale(elapsed.saturating_abs(), LARGEST_RATE, SECOND));
            let stepped = reading.offset.saturating_sub(expected).saturating_abs() > allowed;
            if stepped || elapsed < 0 {
                // The system clock was set, or the readings are out of
                // order: what was measured before says nothing now.
                self.base = None;
                self.following = None;
            }
        }
        match (self.base, self.following) {
            (None, _) => self.base = Some(reading),
            (Some(base), None) => {
                if reading.raw.saturating_sub(base.raw) >= BASELINE {
                    self.following = Some(reading);
                }
            }
            (Some(_), Some(following)) => {
                if reading.raw.saturating_sub(following.raw) >= BASELINE {
                    self.base = Some(following);
                    self.following = Some(reading);
                }
            }
        }
        self.latest = Some(reading);
    }

    /// Measures the clocks now and takes the measurement in.
    pub fn refresh(&mut self) -> Reading {
        let reading = measure_of(self.other, 2);
        self.take(reading);
        reading
    }

    /// Measures the clocks if the latest measurement is more than `age`
    /// nanoseconds before `now`, a reading of the raw clock.
    pub fn refresh_if_older(&mut self, now: i64, age: i64) {
        let due = self
            .latest
            .is_none_or(|latest| now.saturating_sub(latest.raw) > age);
        if due {
            self.refresh();
        }
    }

    /// Converts a stamp of the system clock to the raw clock.
    ///
    /// # Errors
    ///
    /// When nothing has been measured, and when the stamp is further from the
    /// latest measurement than this tracker allows.
    pub fn to_raw(&self, system: i64) -> Result<Converted, Unconverted> {
        let latest = self.latest.ok_or(Unconverted::Unmeasured)?;
        // With `offset(r)` the offset at raw time `r`, the stamp `s` was
        // taken at the `r` with `s = r + offset(r)`. For a constant rate
        // `rise / run` from the latest measurement on, that is
        // `r - latest.raw = (s - latest.offset - latest.raw) * run / (run + rise)`.
        let naive = system
            .saturating_sub(latest.offset)
            .saturating_sub(latest.raw);
        let (since, rate_error) = match self.pair() {
            Some((base, _)) => {
                let run = latest.raw.saturating_sub(base.raw);
                let rise = latest.offset.saturating_sub(base.offset);
                let unsure = scale(base.error.saturating_add(latest.error), SECOND, run);
                (
                    scale(naive, run, run.saturating_add(rise)),
                    RATE_CHANGE.saturating_add(unsure),
                )
            }
            None => (naive, LARGEST_RATE),
        };
        let age = since.saturating_abs();
        if age > self.longest_age {
            return Err(Unconverted::TooOld(age));
        }
        Ok(Converted {
            time: latest.raw.saturating_add(since),
            error: latest
                .error
                .saturating_add(scale(age, rate_error, SECOND))
                .saturating_add(1),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Converted, Reading, Tracker, Unconverted, measure, raw, supported, system};

    const MILLISECOND: i64 = 1_000_000;

    fn reading(raw: i64, offset: i64) -> Reading {
        Reading {
            raw,
            offset,
            error: 10,
        }
    }

    #[test]
    fn the_clocks_are_there_and_the_raw_clock_does_not_run_backwards() {
        assert!(supported());
        let first = raw();
        let second = raw();
        assert!(second >= first);
        // The system clock is after the year 2020.
        assert!(system() > 1_577_836_800 * 1_000_000_000);
    }

    #[test]
    fn a_stamp_is_not_converted_before_anything_is_measured() {
        let tracker = Tracker::new(MILLISECOND);
        assert_eq!(tracker.to_raw(5), Err(Unconverted::Unmeasured));
    }

    #[test]
    fn one_measurement_converts_by_its_offset_with_the_largest_rate_as_error() {
        let mut tracker = Tracker::new(10 * MILLISECOND);
        tracker.take(reading(1_000_000_000, 7_000));
        // A stamp a millisecond after the measurement: a part per thousand
        // of a millisecond is a microsecond.
        assert_eq!(
            tracker.to_raw(1_000_000_000 + 7_000 + MILLISECOND),
            Ok(Converted {
                time: 1_000_000_000 + MILLISECOND,
                error: 10 + 1_000 + 1
            })
        );
        assert_eq!(tracker.rate(), None);
    }

    #[test]
    fn two_measurements_give_the_rate_and_a_stamp_is_converted_along_it() {
        // The system clock gains 50 microseconds a second: 50,000 parts per
        // billion.
        let mut tracker = Tracker::new(100 * MILLISECOND);
        tracker.take(reading(0, 1_000_000));
        tracker.take(reading(1_000_000_000, 1_050_000));
        assert_eq!(tracker.rate(), Some(50_000));
        // The raw time 20 ms after the second measurement: the offset has
        // grown by one more microsecond there.
        let truth = 1_020_000_000;
        let stamp = truth + 1_050_000 + 1_000;
        let converted = tracker.to_raw(stamp).expect("recent enough");
        assert!((converted.time - truth).abs() <= 1, "{converted:?}");
        // 20 ms at 500 parts per million of allowed change is 10
        // microseconds; the rate itself is known to 20 ns in a second.
        assert!(
            converted.error >= 10_000 && converted.error < 10_100,
            "{converted:?}"
        );
        // Without the rate the conversion would be a microsecond off.
        assert!((stamp - 1_050_000 - truth).abs() >= 1_000);
    }

    #[test]
    fn a_stamp_too_far_from_the_latest_measurement_is_refused() {
        let mut tracker = Tracker::new(MILLISECOND);
        tracker.take(reading(1_000_000_000, 0));
        assert!(tracker.to_raw(1_000_000_000 + MILLISECOND).is_ok());
        assert_eq!(
            tracker.to_raw(1_000_000_000 + MILLISECOND + 1),
            Err(Unconverted::TooOld(MILLISECOND + 1))
        );
        // A stamp before the measurement counts the same way.
        assert_eq!(
            tracker.to_raw(1_000_000_000 - 2 * MILLISECOND),
            Err(Unconverted::TooOld(2 * MILLISECOND))
        );
    }

    #[test]
    fn a_step_of_the_system_clock_makes_the_rate_unknown_again() {
        let mut tracker = Tracker::new(100 * MILLISECOND);
        tracker.take(reading(0, 0));
        tracker.take(reading(1_000_000_000, 50_000));
        assert_eq!(tracker.rate(), Some(50_000));
        // A second later the offset is ten seconds larger: nothing but a
        // step does that.
        tracker.take(reading(2_000_000_000, 10_000_000_000));
        assert_eq!(tracker.rate(), None);
        let converted = tracker
            .to_raw(2_000_000_000 + 10_000_000_000)
            .expect("at the measurement");
        assert_eq!(converted.time, 2_000_000_000);
    }

    #[test]
    fn the_rate_is_taken_over_at_least_half_a_second_once_that_much_has_passed() {
        // Measurements every millisecond with errors of 10 ns: a rate taken
        // from neighbours would be unsure by 20 parts per million.
        let mut tracker = Tracker::new(100 * MILLISECOND);
        for step in 0..3_000i64 {
            tracker.take(reading(step * MILLISECOND, step * 30));
        }
        // 30 ns a millisecond is 30,000 parts per billion.
        assert_eq!(tracker.rate(), Some(30_000));
        let at = 2_999 * MILLISECOND;
        let converted = tracker.to_raw(at + 2_999 * 30).expect("at the measurement");
        // At the measurement itself the error is that of the measurement.
        assert_eq!((converted.time, converted.error), (at, 11));
    }

    #[test]
    fn a_conversion_agrees_with_reading_the_clocks_directly() {
        // The system clock is read between two readings of the raw clock,
        // so its conversion lies between them, give or take the error the
        // tracker states. The tracker's measurement is a few milliseconds
        // old, or more when the host is busy.
        let longest_age = 50 * MILLISECOND;
        let mut tracker = Tracker::new(longest_age);
        let mut errors = Vec::new();
        for round in 0..300u64 {
            let measured = tracker.refresh();
            std::thread::sleep(std::time::Duration::from_micros(round % 4 * 1_000));
            let before = raw();
            let stamp = system();
            let after = raw();
            match tracker.to_raw(stamp) {
                Ok(converted) => {
                    assert!(
                        converted.time + converted.error >= before
                            && converted.time - converted.error <= after,
                        "round {round}: {converted:?} is not within {before}..{after}"
                    );
                    errors.push(converted.error);
                }
                // A conversion is refused only when this thread was kept
                // from running for nearly the longest age.
                Err(refusal) => assert!(
                    after - measured.raw > longest_age - MILLISECOND,
                    "round {round}: {refusal:?} after {} ns",
                    after - measured.raw
                ),
            }
        }
        // Up to three milliseconds at a part per thousand are three
        // microseconds. A busy host makes some rounds worse, not most.
        errors.sort_unstable();
        let middle = errors.get(errors.len() / 2).copied().unwrap_or(i64::MAX);
        assert!(middle < 20_000, "middle stated error {middle}");
    }

    #[test]
    fn a_measurement_states_an_error_of_at_most_a_tenth_of_a_millisecond() {
        // The best of many: an interruption between the readings would have
        // to hit every one of them.
        let reading = measure(50);
        assert!(reading.error < 100_000, "error {}", reading.error);
    }
}
