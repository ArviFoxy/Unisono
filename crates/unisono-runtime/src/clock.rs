// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The host's clocks.
//!
//! Every time in unisono is a reading of the host's **raw clock**: the
//! monotonic clock that no time service adjusts (`CLOCK_MONOTONIC_RAW`). The
//! kernel stamps packets with the **system clock** (`CLOCK_REALTIME`), which
//! a time service slews and sometimes steps, and audio systems stamp cycles
//! with the **monotonic clock** (`CLOCK_MONOTONIC`), which a time service
//! slews. All three run apart by tens of parts per million, so a relation
//! measured once is wrong by a hundred microseconds a few seconds later. A
//! [`Tracker`] therefore measures the relation again and again, and converts a
//! stamp of its clock only with a measurement that is recent.
//!
//! Each clock domain has its own nanosecond type ([`RawNs`], [`SystemNs`],
//! [`MonotonicNs`]) and [`Tracker`] is parameterized by the clock it tracks
//! ([`System`] or [`Monotonic`]), so stamps of one clock cannot be converted
//! with a tracker of another.
//!
//! A measurement reads the raw clock, the other clock, and the raw clock
//! again. The other clock was read somewhere between the two raw readings, so
//! taking the middle is wrong by at most half the time between them.
//!
//! # What a conversion assumes
//!
//! Between a measurement and the stamp that is converted with it, the rate
//! of the tracked clock against the raw clock changes by at most
//! [`RATE_CHANGE`], and where the rate has not been measured yet it is at
//! most [`LARGEST_RATE`] in size. The kernel slews the system clock by at
//! most 500 parts per million for a frequency correction and as much again
//! for a correction of the time, which gives both numbers. A step of the
//! system clock between a stamp and the next measurement is outside what a
//! conversion can know; the tracker notices the step at that measurement and
//! forgets the rate.

use std::marker::PhantomData;
use std::sync::atomic::{AtomicI64, Ordering};

/// The number of nanoseconds in a second.
const SECOND: i64 = 1_000_000_000;

/// The largest change of the rate of a tracked clock against the raw clock
/// that a conversion allows for, in parts per billion.
pub const RATE_CHANGE: i64 = 500_000;

/// The largest rate of a tracked clock against the raw clock that a
/// conversion allows for where it has not measured the rate, in parts per
/// billion.
pub const LARGEST_RATE: i64 = 1_000_000;

/// How far apart two measurements are, at the least, for a rate to be taken
/// from them, in nanoseconds.
const SHORTEST_BASELINE: i64 = 20_000_000;

/// How far back the older of the two measurements for the rate is kept, in
/// nanoseconds: between this and twice this.
const BASELINE: i64 = 500_000_000;

/// A timestamp on the host's raw monotonic clock (`CLOCK_MONOTONIC_RAW`),
/// moved by [`shift`], in nanoseconds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RawNs(pub i64);

impl RawNs {
    /// The underlying count of nanoseconds.
    #[must_use]
    pub const fn as_i64(self) -> i64 {
        self.0
    }
}

/// A timestamp on the host's system clock (`CLOCK_REALTIME`), in nanoseconds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SystemNs(pub i64);

impl SystemNs {
    /// The underlying count of nanoseconds.
    #[must_use]
    pub const fn as_i64(self) -> i64 {
        self.0
    }
}

/// A timestamp on the host's monotonic clock (`CLOCK_MONOTONIC`), in
/// nanoseconds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MonotonicNs(pub i64);

impl MonotonicNs {
    /// The underlying count of nanoseconds.
    #[must_use]
    pub const fn as_i64(self) -> i64 {
        self.0
    }
}

/// A clock that a [`Tracker`] can relate to the raw clock.
pub trait Clock: Copy {
    /// The typed nanosecond reading of this clock.
    type Instant: Copy;

    /// Reads this clock now.
    fn read() -> Self::Instant;

    /// The reading as nanoseconds.
    fn to_i64(instant: Self::Instant) -> i64;

    /// Wraps nanoseconds as a reading of this clock.
    fn from_i64(nanos: i64) -> Self::Instant;
}

/// Marker for the system clock (`CLOCK_REALTIME`), which the kernel stamps
/// packets with.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct System;

impl Clock for System {
    type Instant = SystemNs;

    fn read() -> SystemNs {
        system_ns()
    }

    fn to_i64(instant: SystemNs) -> i64 {
        instant.0
    }

    fn from_i64(nanos: i64) -> SystemNs {
        SystemNs(nanos)
    }
}

/// Marker for the monotonic clock (`CLOCK_MONOTONIC`), which audio systems
/// give their times in.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Monotonic;

impl Clock for Monotonic {
    type Instant = MonotonicNs;

    fn read() -> MonotonicNs {
        monotonic_ns()
    }

    fn to_i64(instant: MonotonicNs) -> i64 {
        instant.0
    }

    fn from_i64(nanos: i64) -> MonotonicNs {
        MonotonicNs(nanos)
    }
}

/// Saturates a 128-bit integer to `i64`.
fn saturate(wide: i128) -> i64 {
    i64::try_from(wide).unwrap_or(if wide < 0 { i64::MIN } else { i64::MAX })
}

/// Reads a clock, in nanoseconds, or `None` if the system refuses.
fn try_read(clock: libc::clockid_t) -> Option<i64> {
    // SAFETY: an all-zero timespec is a valid value of the type; some
    // targets give it padding fields that cannot be named.
    let mut time: libc::timespec = unsafe { std::mem::zeroed() };
    // SAFETY: `time` is a valid place for one timespec and lives through the
    // call, which writes nothing else.
    let result = unsafe { libc::clock_gettime(clock, &raw mut time) };
    if result != 0 {
        return None;
    }
    // The fields are 32 bits wide on some targets and 64 on others.
    #[allow(clippy::useless_conversion)]
    let (seconds, nanos) = (i64::from(time.tv_sec), i64::from(time.tv_nsec));
    Some(seconds.saturating_mul(SECOND).saturating_add(nanos))
}

/// Reads a clock, in nanoseconds. Zero if the system refuses, which it does
/// for no clock that [`supported`] accepts.
fn read(clock: libc::clockid_t) -> i64 {
    try_read(clock).unwrap_or(0)
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

/// The raw clock now: the host's, moved as [`shift`] says.
#[must_use]
pub fn raw_ns() -> RawNs {
    let host = read(libc::CLOCK_MONOTONIC_RAW);
    let offset = OFFSET.load(Ordering::Relaxed);
    let skew = SKEW.load(Ordering::Relaxed);
    if offset == 0 && skew == 0 {
        return RawNs(host);
    }
    // A 64-bit time times a skew of 64 bits: below 2^127.
    let gained = i128::from(host) * i128::from(skew) / i128::from(SECOND);
    let moved = i128::from(host) + i128::from(offset) + gained;
    RawNs(saturate(moved))
}

/// The raw clock now, in nanoseconds: the host's, moved as [`shift`] says.
#[must_use]
pub fn raw() -> i64 {
    raw_ns().as_i64()
}

/// The system clock now.
#[must_use]
pub fn system_ns() -> SystemNs {
    SystemNs(read(libc::CLOCK_REALTIME))
}

/// The system clock now, in nanoseconds.
#[must_use]
pub fn system() -> i64 {
    system_ns().as_i64()
}

/// The monotonic clock now: the clock that audio systems give their times in,
/// which a time service slews.
#[must_use]
pub fn monotonic_ns() -> MonotonicNs {
    MonotonicNs(read(libc::CLOCK_MONOTONIC))
}

/// The monotonic clock now, in nanoseconds: the clock that audio systems
/// give their times in, which a time service slews.
#[must_use]
pub fn monotonic() -> i64 {
    monotonic_ns().as_i64()
}

/// Whether this host has the clocks unisono needs.
#[must_use]
pub fn supported() -> bool {
    try_read(libc::CLOCK_MONOTONIC_RAW).is_some()
        && try_read(libc::CLOCK_REALTIME).is_some()
        && try_read(libc::CLOCK_MONOTONIC).is_some()
}

/// One measurement of clock `C` against the raw clock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reading<C: Clock = System> {
    /// The raw clock at the measurement: the middle of the two readings
    /// around the reading of clock `C`.
    pub raw: RawNs,
    /// Clock `C` minus the raw clock then, in nanoseconds.
    pub offset: i64,
    /// Half the time between the two readings of the raw clock, rounded up:
    /// `offset` is within this of the truth.
    pub error: i64,
    clock: PhantomData<C>,
}

impl<C: Clock> Reading<C> {
    /// Constructs a reading of clock `C` against the raw clock.
    #[must_use]
    pub const fn new(raw: RawNs, offset: i64, error: i64) -> Reading<C> {
        Reading {
            raw,
            offset,
            error,
            clock: PhantomData,
        }
    }
}

/// Measures the system clock against the raw clock `tries` times, at least
/// once, and returns the measurement with the smallest error.
#[must_use]
pub fn measure(tries: u32) -> Reading<System> {
    measure_of::<System>(tries)
}

/// Measures clock `C` against the raw clock `tries` times, at least once, and
/// returns the measurement with the smallest error.
#[must_use]
pub fn measure_of<C: Clock>(tries: u32) -> Reading<C> {
    let mut best = once::<C>();
    for _ in 1..tries {
        let reading = once::<C>();
        if reading.error < best.error {
            best = reading;
        }
    }
    best
}

fn once<C: Clock>() -> Reading<C> {
    let before = raw_ns().as_i64();
    let between = C::to_i64(C::read());
    let after = raw_ns().as_i64();
    let width = (i128::from(after) - i128::from(before)).max(0);
    let middle = i128::from(before) + width / 2;
    let offset = i128::from(between) - middle;
    let error = (width + 1) / 2;
    Reading::new(RawNs(saturate(middle)), saturate(offset), saturate(error))
}

/// A time on the raw clock that a stamp of a tracked clock was converted to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Converted {
    /// The reading of the raw clock, in nanoseconds.
    pub time: RawNs,
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

/// The relation between clock `C` and the raw clock, kept current: the
/// system clock by default.
#[derive(Clone, Copy, Debug)]
pub struct Tracker<C: Clock = System> {
    longest_age: i64,
    /// The older measurement that the rate is taken from.
    base: Option<Reading<C>>,
    /// The measurement that becomes the base next.
    following: Option<Reading<C>>,
    latest: Option<Reading<C>>,
}

/// `value * numerator / denominator`, rounded toward zero and limited to the
/// range of `i64`; zero for a denominator of zero.
fn scale(value: i64, numerator: i64, denominator: i64) -> i64 {
    if denominator == 0 {
        return 0;
    }
    saturate(i128::from(value) * i128::from(numerator) / i128::from(denominator))
}

/// `value * numerator / denominator` in `i128`, rounded toward zero, avoiding
/// overflow even when `value` and `numerator` are both near `i64::MAX`.
fn scale_wide(value: i128, numerator: i128, denominator: i128) -> i128 {
    if denominator == 0 {
        return 0;
    }
    if let Some(product) = value.checked_mul(numerator) {
        product / denominator
    } else {
        let whole = (value / denominator).saturating_mul(numerator);
        let rem = (value % denominator)
            .checked_mul(numerator)
            .map_or(0, |p| p / denominator);
        whole.saturating_add(rem)
    }
}

impl Tracker<System> {
    /// A tracker of the system clock against the raw clock.
    #[must_use]
    pub const fn system(longest_age: i64) -> Tracker<System> {
        Tracker::new(longest_age)
    }
}

impl Tracker<Monotonic> {
    /// A tracker of the monotonic clock against the raw clock.
    #[must_use]
    pub const fn monotonic(longest_age: i64) -> Tracker<Monotonic> {
        Tracker::new(longest_age)
    }
}

impl<C: Clock> Tracker<C> {
    /// A tracker of clock `C` against the raw clock that has measured nothing
    /// and converts no stamp further than `longest_age` nanoseconds from its
    /// latest measurement.
    #[must_use]
    pub const fn new(longest_age: i64) -> Tracker<C> {
        Tracker {
            longest_age,
            base: None,
            following: None,
            latest: None,
        }
    }

    /// The latest measurement.
    #[must_use]
    pub fn latest(&self) -> Option<Reading<C>> {
        self.latest
    }

    /// The two measurements that the rate is taken from, if they are far
    /// enough apart.
    fn pair(&self) -> Option<(Reading<C>, Reading<C>)> {
        let (base, latest) = (self.base?, self.latest?);
        let span = i128::from(latest.raw.as_i64()) - i128::from(base.raw.as_i64());
        (span >= i128::from(SHORTEST_BASELINE)).then_some((base, latest))
    }

    /// The rate of clock `C` against the raw clock, in parts per billion,
    /// once two measurements far enough apart give one.
    #[must_use]
    pub fn rate(&self) -> Option<i64> {
        let (base, latest) = self.pair()?;
        let rise = i128::from(latest.offset) - i128::from(base.offset);
        let run = i128::from(latest.raw.as_i64()) - i128::from(base.raw.as_i64());
        Some(saturate(scale_wide(rise, i128::from(SECOND), run)))
    }

    /// Takes in a measurement that is later than the ones before it.
    pub fn take(&mut self, reading: Reading<C>) {
        if let Some(latest) = self.latest {
            let elapsed = i128::from(reading.raw.as_i64()) - i128::from(latest.raw.as_i64());
            let expected = i128::from(latest.offset)
                + scale_wide(
                    elapsed,
                    i128::from(self.rate().unwrap_or(0)),
                    i128::from(SECOND),
                );
            let allowed = i128::from(reading.error.max(0))
                + i128::from(latest.error.max(0))
                + scale_wide(elapsed.abs(), i128::from(LARGEST_RATE), i128::from(SECOND));
            let stepped = (i128::from(reading.offset) - expected).abs() > allowed;
            if stepped || elapsed < 0 {
                // The tracked clock was set, or the readings are out of
                // order: what was measured before says nothing now.
                self.base = None;
                self.following = None;
            }
        }
        match (self.base, self.following) {
            (None, _) => self.base = Some(reading),
            (Some(base), None) => {
                if i128::from(reading.raw.as_i64()) - i128::from(base.raw.as_i64())
                    >= i128::from(BASELINE)
                {
                    self.following = Some(reading);
                }
            }
            (Some(_), Some(following)) => {
                if i128::from(reading.raw.as_i64()) - i128::from(following.raw.as_i64())
                    >= i128::from(BASELINE)
                {
                    self.base = Some(following);
                    self.following = Some(reading);
                }
            }
        }
        self.latest = Some(reading);
    }

    /// Measures the clocks now and takes the measurement in.
    pub fn refresh(&mut self) -> Reading<C> {
        let reading = measure_of::<C>(2);
        self.take(reading);
        reading
    }

    /// Measures the clocks if the latest measurement is more than `age`
    /// nanoseconds before `now`, a reading of the raw clock.
    pub fn refresh_if_older(&mut self, now: RawNs, age: i64) {
        let due = self.latest.is_none_or(|latest| {
            i128::from(now.as_i64()) - i128::from(latest.raw.as_i64()) > i128::from(age)
        });
        if due {
            self.refresh();
        }
    }

    /// Converts a stamp of clock `C` to the raw clock.
    ///
    /// # Errors
    ///
    /// When nothing has been measured, and when the stamp is further from the
    /// latest measurement than this tracker allows.
    pub fn to_raw(&self, stamp: C::Instant) -> Result<Converted, Unconverted> {
        let latest = self.latest.ok_or(Unconverted::Unmeasured)?;
        // With `offset(r)` the offset at raw time `r`, the stamp `s` was
        // taken at the `r` with `s = r + offset(r)`. For a constant rate
        // `rise / run` from the latest measurement on, that is
        // `r - latest.raw = (s - latest.offset - latest.raw) * run / (run + rise)`.
        let naive = i128::from(C::to_i64(stamp))
            - i128::from(latest.offset)
            - i128::from(latest.raw.as_i64());
        let (since, rate_error) = match self.pair() {
            Some((base, _)) => {
                let run = i128::from(latest.raw.as_i64()) - i128::from(base.raw.as_i64());
                let rise = i128::from(latest.offset) - i128::from(base.offset);
                let denom = run + rise;
                if run > 0 && denom > 0 {
                    let error_sum = i128::from(base.error.max(0)) + i128::from(latest.error.max(0));
                    let unsure = saturate(scale_wide(error_sum, i128::from(SECOND), run));
                    (
                        scale_wide(naive, run, denom),
                        RATE_CHANGE.saturating_add(unsure),
                    )
                } else {
                    (naive, LARGEST_RATE)
                }
            }
            None => (naive, LARGEST_RATE),
        };
        let age_wide = since.unsigned_abs();
        let age = i64::try_from(age_wide).unwrap_or(i64::MAX);
        if self.longest_age < 0 || age_wide > u128::from(self.longest_age.unsigned_abs()) {
            return Err(Unconverted::TooOld(age));
        }
        Ok(Converted {
            time: RawNs(saturate(i128::from(latest.raw.as_i64()) + since)),
            error: latest
                .error
                .max(0)
                .saturating_add(scale(age, rate_error, SECOND))
                .saturating_add(1),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Converted, Monotonic, MonotonicNs, RawNs, Reading, System, SystemNs, Tracker, Unconverted,
        measure, monotonic_ns, raw, raw_ns, supported, system, system_ns,
    };

    const MILLISECOND: i64 = 1_000_000;

    fn reading(raw: i64, offset: i64) -> Reading<System> {
        Reading::new(RawNs(raw), offset, 10)
    }

    #[test]
    fn the_clocks_are_there_and_the_raw_clock_does_not_run_backwards() {
        assert!(supported());
        let first = raw();
        let second = raw();
        assert!(second >= first);
        // The system clock is after the year 2020.
        assert!(system() > 1_577_836_800 * 1_000_000_000);
        assert!(monotonic_ns().as_i64() >= 0);
    }

    #[test]
    fn a_stamp_is_not_converted_before_anything_is_measured() {
        let tracker = Tracker::<System>::new(MILLISECOND);
        assert_eq!(tracker.to_raw(SystemNs(5)), Err(Unconverted::Unmeasured));
    }

    #[test]
    fn one_measurement_converts_by_its_offset_with_the_largest_rate_as_error() {
        let mut tracker = Tracker::system(10 * MILLISECOND);
        tracker.take(reading(1_000_000_000, 7_000));
        // A stamp a millisecond after the measurement: a part per thousand
        // of a millisecond is a microsecond.
        assert_eq!(
            tracker.to_raw(SystemNs(1_000_000_000 + 7_000 + MILLISECOND)),
            Ok(Converted {
                time: RawNs(1_000_000_000 + MILLISECOND),
                error: 10 + 1_000 + 1
            })
        );
        assert_eq!(tracker.rate(), None);
    }

    #[test]
    fn two_measurements_give_the_rate_and_a_stamp_is_converted_along_it() {
        // The system clock gains 50 microseconds a second: 50,000 parts per
        // billion.
        let mut tracker = Tracker::system(100 * MILLISECOND);
        tracker.take(reading(0, 1_000_000));
        tracker.take(reading(1_000_000_000, 1_050_000));
        assert_eq!(tracker.rate(), Some(50_000));
        // The raw time 20 ms after the second measurement: the offset has
        // grown by one more microsecond there.
        let truth = 1_020_000_000;
        let stamp = truth + 1_050_000 + 1_000;
        let converted = tracker.to_raw(SystemNs(stamp)).expect("recent enough");
        assert!(
            (converted.time.as_i64() - truth).abs() <= 1,
            "{converted:?}"
        );
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
        let mut tracker = Tracker::system(MILLISECOND);
        tracker.take(reading(1_000_000_000, 0));
        assert!(
            tracker
                .to_raw(SystemNs(1_000_000_000 + MILLISECOND))
                .is_ok()
        );
        assert_eq!(
            tracker.to_raw(SystemNs(1_000_000_000 + MILLISECOND + 1)),
            Err(Unconverted::TooOld(MILLISECOND + 1))
        );
        // A stamp before the measurement counts the same way.
        assert_eq!(
            tracker.to_raw(SystemNs(1_000_000_000 - 2 * MILLISECOND)),
            Err(Unconverted::TooOld(2 * MILLISECOND))
        );
    }

    #[test]
    fn a_step_of_the_system_clock_makes_the_rate_unknown_again() {
        let mut tracker = Tracker::system(100 * MILLISECOND);
        tracker.take(reading(0, 0));
        tracker.take(reading(1_000_000_000, 50_000));
        assert_eq!(tracker.rate(), Some(50_000));
        // A second later the offset is ten seconds larger: nothing but a
        // step does that.
        tracker.take(reading(2_000_000_000, 10_000_000_000));
        assert_eq!(tracker.rate(), None);
        let converted = tracker
            .to_raw(SystemNs(2_000_000_000 + 10_000_000_000))
            .expect("at the measurement");
        assert_eq!(converted.time, RawNs(2_000_000_000));
    }

    #[test]
    fn the_rate_is_taken_over_at_least_half_a_second_once_that_much_has_passed() {
        // Measurements every millisecond with errors of 10 ns: a rate taken
        // from neighbours would be unsure by 20 parts per million.
        let mut tracker = Tracker::system(100 * MILLISECOND);
        for step in 0..3_000i64 {
            tracker.take(reading(step * MILLISECOND, step * 30));
        }
        // 30 ns a millisecond is 30,000 parts per billion.
        assert_eq!(tracker.rate(), Some(30_000));
        let at = 2_999 * MILLISECOND;
        let converted = tracker
            .to_raw(SystemNs(at + 2_999 * 30))
            .expect("at the measurement");
        // At the measurement itself the error is that of the measurement.
        assert_eq!((converted.time, converted.error), (RawNs(at), 11));
    }

    #[test]
    fn degenerate_rate_and_extreme_offsets_do_not_bypass_age_limit() {
        // Even if crafted readings have `run + rise <= 0`, an old stamp must
        // never collapse to age 0.
        let mut tracker = Tracker::<Monotonic>::monotonic(MILLISECOND);
        tracker.take(Reading::new(RawNs(0), 0, 100_000_000));
        tracker.take(Reading::new(RawNs(50_000_000), -50_000_000, 100_000_000));
        assert_eq!(
            tracker.to_raw(MonotonicNs(10 * MILLISECOND)),
            Err(Unconverted::TooOld(10 * MILLISECOND))
        );

        // Extreme offset + raw time must not saturate `naive` to an accepted age.
        let mut wide = Tracker::system(MILLISECOND);
        wide.take(Reading::new(RawNs(i64::MAX - 100), -100, 10));
        assert_eq!(
            wide.to_raw(SystemNs(i64::MIN)),
            Err(Unconverted::TooOld(i64::MAX))
        );
    }

    #[test]
    fn a_conversion_agrees_with_reading_the_clocks_directly() {
        // The system clock is read between two readings of the raw clock,
        // so its conversion lies between them, give or take the error the
        // tracker states. The tracker's measurement is a few milliseconds
        // old, or more when the host is busy.
        let longest_age = 50 * MILLISECOND;
        let mut tracker = Tracker::system(longest_age);
        let mut errors = Vec::new();
        for round in 0..300u64 {
            let measured = tracker.refresh();
            std::thread::sleep(std::time::Duration::from_micros(round % 4 * 1_000));
            let before = raw_ns();
            let stamp = system_ns();
            let after = raw_ns();
            match tracker.to_raw(stamp) {
                Ok(converted) => {
                    assert!(
                        converted.time.as_i64() + converted.error >= before.as_i64()
                            && converted.time.as_i64() - converted.error <= after.as_i64(),
                        "round {round}: {converted:?} is not within {before:?}..{after:?}"
                    );
                    errors.push(converted.error);
                }
                // A conversion is refused only when this thread was kept
                // from running for nearly the longest age.
                Err(refusal) => assert!(
                    after.as_i64() - measured.raw.as_i64() > longest_age - MILLISECOND,
                    "round {round}: {refusal:?} after {} ns",
                    after.as_i64() - measured.raw.as_i64()
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
