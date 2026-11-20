// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The relation between a device's count of frames and the host's clock.
//!
//! An audio system reports, cycle by cycle, a position of its device and the
//! reading of the host's clock that belongs to it. A report can be early or
//! late, so the relation is the line that fits the last reports best: the
//! one with the smallest sum of squared distances to them. It says when a
//! frame leaves the device, and how long a cycle takes.
//!
//! The sums are whole numbers and exact. Positions are taken relative to the
//! newest report, and times relative to what the nominal rate gives, so that
//! the numbers stay small.

use crate::fixed::{div_floor, div_floor_wide, saturate};

/// The number of nanoseconds in a second.
const BILLION: i128 = 1_000_000_000;

/// The largest distance in frames, and the largest departure from the
/// nominal rate in nanoseconds, that enter the sums: 2^32. Beyond them a
/// report is taken at the bound, so that no sum can exceed its range.
const REACH: i128 = 4_294_967_296;

/// One report of a device.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub struct Reading {
    /// A position of the device, in frames.
    pub position: u64,
    /// The reading of the host's clock that belongs to it, in nanoseconds.
    pub time: i64,
}

/// The sums that the line is computed from, over the kept reports: with `x`
/// the distance of a report from the newest in frames, and `y` its time
/// beyond what the nominal rate gives for that distance, in nanoseconds.
#[derive(Clone, Copy)]
struct Sums {
    count: i128,
    x: i128,
    y: i128,
    xx: i128,
    xy: i128,
}

/// The fitted line of a device, from its last `W` reports.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub struct Device<const W: usize> {
    readings: [Reading; W],
    /// How many of the places hold a report.
    len: usize,
    /// The place that the next report is written to.
    next: usize,
    /// The nominal rate, in frames per second.
    rate: u32,
}

/// `value` brought within [`REACH`] either way.
fn within(value: i128) -> i128 {
    if value > REACH {
        REACH
    } else if value < 0i128.wrapping_sub(REACH) {
        0i128.wrapping_sub(REACH)
    } else {
        value
    }
}

impl<const W: usize> Device<W> {
    /// A device of `rate` frames per second of which nothing is known yet.
    #[must_use]
    pub fn new(rate: u32) -> Self {
        Device {
            readings: [Reading {
                position: 0,
                time: 0,
            }; W],
            len: 0,
            next: 0,
            rate,
        }
    }

    /// The number of reports the line is fitted to.
    #[must_use]
    pub fn kept(&self) -> usize {
        if self.len > W { W } else { self.len }
    }

    /// The report at `place`, if that place exists.
    fn at(&self, place: usize) -> Option<Reading> {
        match self.readings.get(place) {
            Some(reading) => Some(*reading),
            None => None,
        }
    }

    /// The newest report, if there is one.
    fn newest(&self) -> Option<Reading> {
        if self.len == 0 {
            return None;
        }
        // The place before the next one, around the ring.
        let place = if self.next == 0 {
            W.saturating_sub(1)
        } else {
            self.next.saturating_sub(1)
        };
        self.at(place)
    }

    /// What the nominal rate gives for a distance of `frames`, in
    /// nanoseconds.
    fn nominal(&self, frames: i128) -> i128 {
        // At most 2^33 times 2^30: no wrapping.
        div_floor(frames.wrapping_mul(BILLION), self.rate as i64)
    }

    /// Whether a report shows that the device started anew: it is not after
    /// the newest report, in position or in time.
    fn restarted(&self, position: u64, time: i64) -> bool {
        match self.newest() {
            Some(newest) => position <= newest.position || time <= newest.time,
            None => false,
        }
    }

    /// Takes in a report. When it shows that the device started anew, what
    /// was known is dropped first.
    pub fn observe(&mut self, position: u64, time: i64) {
        if self.restarted(position, time) {
            self.len = 0;
            self.next = 0;
        }
        if let Some(place) = self.readings.get_mut(self.next) {
            *place = Reading { position, time };
        }
        self.next = self.next.saturating_add(1).checked_rem(W).unwrap_or(0);
        if self.len < W {
            self.len = self.len.saturating_add(1);
        }
    }

    /// The sums over the kept reports, relative to `newest`.
    fn sums(&self, newest: Reading) -> Sums {
        let mut sums = Sums {
            count: 0,
            x: 0,
            y: 0,
            xx: 0,
            xy: 0,
        };
        let kept = self.kept();
        let mut place = 0usize;
        while place < kept {
            if let Some(reading) = self.at(place) {
                sums = self.add(sums, newest, reading);
            }
            place = place.saturating_add(1);
        }
        sums
    }

    /// `sums` with one more report.
    fn add(&self, sums: Sums, newest: Reading, reading: Reading) -> Sums {
        // Differences of 64-bit numbers, then numbers within 2^32 and
        // products of two of them, summed over at most 2^64 places: nothing
        // wraps.
        let x = within((reading.position as i128).wrapping_sub(newest.position as i128));
        let elapsed = (reading.time as i128).wrapping_sub(newest.time as i128);
        let y = within(elapsed.wrapping_sub(self.nominal(x)));
        Sums {
            count: sums.count.wrapping_add(1),
            x: sums.x.wrapping_add(x),
            y: sums.y.wrapping_add(y),
            xx: sums.xx.wrapping_add(x.wrapping_mul(x)),
            xy: sums.xy.wrapping_add(x.wrapping_mul(y)),
        }
    }

    /// The reading of the host's clock that belongs to `position`, by the
    /// line that fits the kept reports best. With one report, or reports of
    /// one position only, the line has the nominal rate. `None` before the
    /// first report.
    #[must_use]
    pub fn when(&self, position: u64) -> Option<i64> {
        let Some(newest) = self.newest() else {
            return None;
        };
        let sums = self.sums(newest);
        if sums.count <= 0 {
            return None;
        }
        let ahead = within((position as i128).wrapping_sub(newest.position as i128));
        // With the reports of up to 2^8 cycles: sums of x and y below 2^40,
        // of their products below 2^72, the two parts below 2^81, and the
        // numerator below 2^123.
        let spread = sums
            .count
            .wrapping_mul(sums.xx)
            .wrapping_sub(sums.x.wrapping_mul(sums.x));
        let beyond = if spread > 0 {
            let tilt = sums
                .count
                .wrapping_mul(sums.xy)
                .wrapping_sub(sums.x.wrapping_mul(sums.y));
            let lever = sums.count.wrapping_mul(ahead).wrapping_sub(sums.x);
            div_floor_wide(
                sums.y
                    .wrapping_mul(spread)
                    .wrapping_add(tilt.wrapping_mul(lever)),
                sums.count.wrapping_mul(spread),
            )
        } else {
            div_floor_wide(sums.y, sums.count)
        };
        Some(saturate(
            (newest.time as i128)
                .wrapping_add(self.nominal(ahead))
                .wrapping_add(beyond),
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use super::Device;

    /// Reports of a device whose frame `p` belongs to the time
    /// `offset + p * period / 1000` nanoseconds, every 256 frames, each
    /// moved by the error that `error` gives for its number.
    fn reports(
        count: u64,
        offset: i64,
        period_thousandths: i64,
        error: impl Fn(u64) -> i64,
    ) -> Vec<(u64, i64)> {
        (0..count)
            .map(|number| {
                let position = 1_000_000 + number * 256;
                let exact =
                    offset + i64::try_from(position).unwrap_or(0) * period_thousandths / 1_000;
                (position, exact + error(number))
            })
            .collect()
    }

    #[test]
    fn exact_reports_give_their_line() {
        // 48,000 frames a second nominally; this device takes 20,835.417
        // nanoseconds for a frame, which is 100 parts per million slow.
        let mut device = Device::<64>::new(48_000);
        assert_eq!(device.when(5), None);
        for (position, time) in reports(64, 7_000_000_000, 20_835_417, |_| 0) {
            device.observe(position, time);
        }
        let at = |position: u64| device.when(position).expect("a line");
        let exact = |position: i64| 7_000_000_000 + position * 20_835_417 / 1_000;
        // On a report, between two, and three cycles ahead of the newest.
        for position in [
            1_000_000 + 63 * 256,
            1_000_000 + 10 * 256 + 100,
            1_000_000 + 66 * 256,
        ] {
            let error = at(position) - exact(i64::try_from(position).unwrap_or(0));
            assert!(error.abs() <= 1, "position {position}: {error}");
        }
        // A cycle of 256 frames takes 5,333,867 nanoseconds on this device.
        let cycle = at(1_000_000 + 64 * 256) - at(1_000_000 + 63 * 256);
        assert!((cycle - 5_333_867).abs() <= 1, "cycle {cycle}");
    }

    #[test]
    fn errors_of_either_sign_average_out() {
        // Errors of up to 20 microseconds either way, from a fixed sequence.
        let error = |number: u64| {
            let mixed = number.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 40;
            i64::try_from(mixed % 40_001).unwrap_or(0) - 20_000
        };
        let mut device = Device::<64>::new(48_000);
        let all = reports(64, 0, 20_833_333, error);
        for (position, time) in &all {
            device.observe(*position, *time);
        }
        // The same fit in floating point: the line through the mean with
        // the slope of least squares.
        #[allow(clippy::cast_precision_loss)]
        let (xs, ys): (Vec<f64>, Vec<f64>) = all
            .iter()
            .map(|(position, time)| (*position as f64, *time as f64))
            .unzip();
        let n = 64.0;
        let mean_x = xs.iter().sum::<f64>() / n;
        let mean_y = ys.iter().sum::<f64>() / n;
        let slope = xs
            .iter()
            .zip(&ys)
            .map(|(x, y)| (x - mean_x) * (y - mean_y))
            .sum::<f64>()
            / xs.iter().map(|x| (x - mean_x) * (x - mean_x)).sum::<f64>();
        for position in [1_000_000u64, 1_000_000 + 40 * 256, 1_000_000 + 70 * 256] {
            #[allow(clippy::cast_precision_loss)]
            let reference = mean_y + slope * (position as f64 - mean_x);
            #[allow(clippy::cast_precision_loss)]
            let found = device.when(position).expect("a line") as f64;
            assert!(
                (found - reference).abs() < 2.0,
                "position {position}: {found} against {reference}"
            );
        }
        // The fit is much nearer the truth than a single report: within 8
        // microseconds at the newest report, where one report can be off by 20.
        let newest = 1_000_000 + 63 * 256;
        let truth = i64::try_from(newest).unwrap_or(0) * 20_833_333 / 1_000;
        let off = device.when(newest).expect("a line") - truth;
        assert!(off.abs() < 8_000, "off by {off}");
    }

    #[test]
    fn one_report_gives_the_nominal_rate() {
        let mut device = Device::<8>::new(48_000);
        device.observe(1_000, 5_000_000);
        assert_eq!(device.when(1_000), Some(5_000_000));
        assert_eq!(device.when(49_000), Some(1_005_000_000));
        assert_eq!(device.when(0), Some(5_000_000 - 20_833_334));
    }

    #[test]
    fn only_the_last_reports_count() {
        // Sixteen reports of one line, then eight of a line 3 ms later:
        // with room for eight, only the later line is left.
        let mut device = Device::<8>::new(48_000);
        for (position, time) in reports(16, 0, 20_833_333, |_| 0) {
            device.observe(position, time);
        }
        for (position, time) in reports(24, 3_000_000, 20_833_333, |_| 0)
            .into_iter()
            .skip(16)
        {
            device.observe(position, time);
        }
        assert_eq!(device.kept(), 8);
        let position = 1_000_000 + 23 * 256;
        let expected = 3_000_000 + i64::try_from(position).unwrap_or(0) * 20_833_333 / 1_000;
        let found = device.when(position).expect("a line");
        assert!((found - expected).abs() <= 1, "{found} against {expected}");
    }

    #[test]
    fn a_report_that_goes_back_starts_anew() {
        let mut device = Device::<8>::new(48_000);
        for (position, time) in reports(8, 0, 20_833_333, |_| 0) {
            device.observe(position, time);
        }
        // The device was restarted: its count begins again.
        device.observe(256, 900_000_000_000);
        assert_eq!(device.kept(), 1);
        assert_eq!(device.when(256), Some(900_000_000_000));
        // A time that goes back does the same.
        device.observe(512, 5);
        assert_eq!(device.kept(), 1);
    }

    #[test]
    fn wild_states_and_reports_give_a_result() {
        let mut device = Device::<4>::new(0);
        device.observe(0, i64::MIN);
        device.observe(u64::MAX, i64::MAX);
        assert!(device.when(u64::MAX / 2).is_some());
        let mut device = Device::<0>::new(48_000);
        device.observe(5, 5);
        assert_eq!(device.when(5), None);
        let mut device = Device::<4>::new(48_000);
        device.observe(5, 5);
        device.len = 99;
        device.next = 77;
        device.observe(6, 6);
        assert!(device.kept() <= 4);
        assert!(device.when(7).is_some());
    }
}
