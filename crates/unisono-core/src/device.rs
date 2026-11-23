// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Ordinary least-squares regression mapping audio device frame counts to
//! host clock timestamps.
//!
//! Fits a line through recent `(frame_position, host_time_ns)` callback
//! reports using exact integer sums anchored at the newest sample and nominal
//! frame spacing so accumulators stay bounded and jitter-smoothed.

use crate::fixed::{div_floor, div_floor_wide, saturate};

/// The number of nanoseconds in a second.
const BILLION: i128 = 1_000_000_000;

/// The largest distance in frames, and the largest departure from the
/// nominal rate in nanoseconds, that enter the sums: 2^28. Beyond them a
/// report is taken at the bound, so that no sum or product in [`Device::when`]
/// can exceed `i128`.
const REACH: i128 = 268_435_456;

/// The largest number of reports that enter the sums: 2^12. Together with
/// [`REACH`], every intermediate value in [`Device::when`] stays below 2^123
/// for any `W`.
const MAX_KEPT: usize = 4_096;

/// One report of a device.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
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
#[cfg_attr(not(translating), derive(Debug))]
pub struct Device<const W: usize> {
    readings: [Reading; W],
    /// How many of the places hold a report.
    len: usize,
    /// The place that the next report is written to.
    next: usize,
    /// The nominal rate, in frames per second.
    rate: u32,
    /// A report that lies off the line, set aside until the next report
    /// shows whether the device's timing made a step or the report was
    /// wrong.
    aside: Option<Reading>,
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
            aside: None,
        }
    }

    /// The number of reports this device keeps at most: `W`, capped at
    /// [`MAX_KEPT`] so that the sums never wrap.
    fn capacity() -> usize {
        if W > MAX_KEPT { MAX_KEPT } else { W }
    }

    /// The number of reports the line is fitted to.
    #[must_use]
    pub fn kept(&self) -> usize {
        let cap = Self::capacity();
        if self.len > cap { cap } else { self.len }
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
        let cap = Self::capacity();
        if self.len == 0 || cap == 0 {
            return None;
        }
        // The place before the next one, around the ring of size `cap`.
        let place = if self.next == 0 || self.next > cap {
            cap.saturating_sub(1)
        } else {
            self.next.saturating_sub(1)
        };
        self.at(place)
    }

    /// What the nominal rate gives for a distance of `frames`, in
    /// nanoseconds.
    fn nominal(&self, frames: i128) -> i128 {
        // At most 2^28 times 10^9: below 2^58, no wrapping.
        div_floor(frames.wrapping_mul(BILLION), self.rate as i64)
    }

    /// Whether a report at `position` after the report `last` shows that the
    /// device started anew: its position is not after that of `last`, or it
    /// is further on than [`REACH`] frames.
    fn restarted(last: Reading, position: u64) -> bool {
        position <= last.position || (position as i128).wrapping_sub(last.position as i128) > REACH
    }

    /// Writes a report as the newest of the kept ones.
    fn push(&mut self, reading: Reading) {
        let cap = Self::capacity();
        if self.len > cap {
            self.len = cap;
        }
        if cap == 0 {
            return;
        }
        if self.next >= cap {
            self.next = 0;
        }
        if let Some(place) = self.readings.get_mut(self.next) {
            *place = reading;
        }
        let next = self.next.saturating_add(1);
        self.next = if next >= cap { 0 } else { next };
        if self.len < cap {
            self.len = self.len.saturating_add(1);
        }
    }

    /// Drops what was known and keeps `reading` alone.
    fn start(&mut self, reading: Reading) {
        self.len = 0;
        self.next = 0;
        self.aside = None;
        self.push(reading);
    }

    /// Whether `later` lies where the nominal rate puts it after `earlier`:
    /// the time between the two is that of the frames between them at the
    /// nominal rate, to within half of it. A device that leaves out a cycle
    /// or stands still for one is off by a whole such time. Two reports that
    /// are each wrong by less than a quarter of it are never apart by more.
    fn follows(&self, earlier: Reading, later: Reading) -> bool {
        let frames = within((later.position as i128).wrapping_sub(earlier.position as i128));
        // Differences of 64-bit numbers: no wrapping. The nominal time is
        // below 2^58, so its negation does not wrap either.
        let between = self.nominal(frames);
        let elapsed = (later.time as i128).wrapping_sub(earlier.time as i128);
        let off = elapsed.wrapping_sub(between);
        let allowed = between.wrapping_shr(1);
        off <= allowed && off >= 0i128.wrapping_sub(allowed)
    }

    /// Moves the time of every kept report by `by` nanoseconds.
    fn shift(&mut self, by: i128) {
        let kept = self.kept();
        let mut place = 0usize;
        while place < kept {
            if let Some(reading) = self.at(place) {
                let moved = Reading {
                    position: reading.position,
                    // A 64-bit number and a difference of two: no wrapping.
                    time: saturate((reading.time as i128).wrapping_add(by)),
                };
                if let Some(slot) = self.readings.get_mut(place) {
                    *slot = moved;
                }
            }
            place = place.saturating_add(1);
        }
    }

    /// How far `reading` is from where the line puts it, or `otherwise` when
    /// there is no line.
    fn off(&self, reading: Reading, otherwise: i128) -> i128 {
        match self.when(reading.position) {
            // A difference of 64-bit numbers: no wrapping.
            Some(expected) => (reading.time as i128).wrapping_sub(expected as i128),
            None => otherwise,
        }
    }

    /// Takes in a step of the device's timing, which the two reports
    /// `earlier` and `report` show: the first does not lie where the kept
    /// reports put it, and the second lies where the first puts it. The kept
    /// reports are moved by the step, so that the line goes on through the
    /// two reports with the rate that it had. The step is taken as the mean
    /// of how far the two are from the line.
    fn step(&mut self, earlier: Reading, report: Reading) {
        let second = self.off(report, 0);
        let first = self.off(earlier, second);
        // The sum of two differences of 64-bit numbers: no wrapping.
        self.shift(first.wrapping_add(second).wrapping_shr(1));
        self.aside = None;
        self.push(earlier);
        self.push(report);
    }

    /// Takes in a report.
    ///
    /// A report that lies where the nominal rate puts it after the report
    /// before, within half the time of the frames between them, is kept. One
    /// that does not is set aside for one report. If the next report lies
    /// where the one set aside puts it, the device's timing made a step: it
    /// left frames out or stood still. The kept reports are then moved by
    /// the step and the two are kept, so the line keeps its rate. If the
    /// next report lies where the kept reports put it, the one set aside
    /// was wrong and is dropped. If it does neither, the line is not to be
    /// trusted, and it starts anew at that report. A report whose position
    /// does not go on from the last one starts the line anew as well.
    ///
    /// So of any two reports in a row the second is kept, whatever the
    /// device held before.
    pub fn observe(&mut self, position: u64, time: i64) {
        let report = Reading { position, time };
        let Some(newest) = self.newest() else {
            self.start(report);
            return;
        };
        let Some(earlier) = self.aside else {
            if Self::restarted(newest, position) {
                self.start(report);
            } else if self.follows(newest, report) {
                self.push(report);
            } else {
                self.aside = Some(report);
            }
            return;
        };
        if !Self::restarted(earlier, position) && self.follows(earlier, report) {
            self.step(earlier, report);
        } else if !Self::restarted(newest, position) && self.follows(newest, report) {
            self.aside = None;
            self.push(report);
        } else {
            self.start(report);
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
        // Differences of 64-bit numbers clamped within `REACH` (2^28), summed
        // over at most `MAX_KEPT` (2^12) places: nothing wraps in `i128`.
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

    /// Computes `(newest, sums, spread, tilt)` once for the kept reports.
    fn fit(&self) -> Option<(Reading, Sums, i128, i128)> {
        let Some(newest) = self.newest() else {
            return None;
        };
        let sums = self.sums(newest);
        if sums.count <= 0 {
            return None;
        }
        let spread = sums
            .count
            .wrapping_mul(sums.xx)
            .wrapping_sub(sums.x.wrapping_mul(sums.x));
        let tilt = if spread > 0 {
            sums.count
                .wrapping_mul(sums.xy)
                .wrapping_sub(sums.x.wrapping_mul(sums.y))
        } else {
            0
        };
        Some((newest, sums, spread, tilt))
    }

    /// Evaluates the fitted line at `position` from precomputed `sums`,
    /// `spread`, and `tilt`.
    fn eval_at(&self, newest: Reading, sums: Sums, spread: i128, tilt: i128, position: u64) -> i64 {
        let ahead = within((position as i128).wrapping_sub(newest.position as i128));
        // With at most 2^12 reports and each value within 2^28: sums of x and
        // y are at most 2^40, sums of products at most 2^68, spread and tilt
        // at most 2^81, and the numerator below 2^123. No operation wraps.
        let beyond = if spread > 0 {
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
        saturate(
            (newest.time as i128)
                .wrapping_add(self.nominal(ahead))
                .wrapping_add(beyond),
        )
    }

    /// The reading of the host's clock that belongs to `position`, by the
    /// line that fits the kept reports best. With one report, or reports of
    /// one position only, the line has the nominal rate. `None` before the
    /// first report.
    #[must_use]
    pub fn when(&self, position: u64) -> Option<i64> {
        let Some((newest, sums, spread, tilt)) = self.fit() else {
            return None;
        };
        Some(self.eval_at(newest, sums, spread, tilt, position))
    }

    /// The fitted start time in nanoseconds and cycle duration in units of
    /// 2^-16 nanosecond for a cycle of `frames` frames beginning at
    /// `position`, computed in a single pass over the kept reports.
    ///
    /// Returning the cycle duration with 16 fractional bits lets a caller
    /// carry the sub-nanosecond remainder from one cycle to the next so that
    /// whole-nanosecond cycle lengths are unbiased on average. Returns `None`
    /// before the first report.
    #[must_use]
    pub fn when_cycle(&self, position: u64, frames: u32) -> Option<(i64, i64)> {
        let Some((newest, sums, spread, tilt)) = self.fit() else {
            return None;
        };
        let start = self.eval_at(newest, sums, spread, tilt, position);
        let span = within(frames as i128);
        // `span <= 2^28`, so `span_q16 <= 2^44`: `span_q16 * BILLION < 2^74`
        // and `|span_q16 * tilt| <= 2^44 * 2^81 = 2^125`, so no operation
        // wraps in `i128`.
        let span_q16 = span.wrapping_shl(16);
        let nominal_q16 = div_floor(span_q16.wrapping_mul(BILLION), self.rate as i64);
        let beyond_q16 = if spread > 0 {
            div_floor_wide(span_q16.wrapping_mul(tilt), spread)
        } else {
            0
        };
        let duration_q16 = saturate(nominal_q16.wrapping_add(beyond_q16));
        Some((start, duration_q16))
    }
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use super::{Device, Reading};

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
    fn reports_that_scatter_by_less_than_a_quarter_of_a_cycle_are_all_kept() {
        // 256 frames take 5.3 ms; the reports are up to 1.3 ms off either
        // way, so two in a row are up to 2.6 ms apart from where they belong.
        let mut device = Device::<64>::new(48_000);
        let error =
            |number: u64| [1_300_000i64, -1_300_000, 300_000, -1_200_000][(number % 4) as usize];
        for (position, time) in reports(64, 0, 20_833_333, error) {
            device.observe(position, time);
        }
        assert_eq!(device.kept(), 64);
        assert_eq!(device.aside, None);
    }

    #[test]
    fn a_report_far_off_the_line_is_left_out() {
        let mut device = Device::<64>::new(48_000);
        let all = reports(40, 7_000_000_000, 20_835_417, |number| {
            // One report says a time 4 ms late, more than half a cycle.
            if number == 20 { 4_000_000 } else { 0 }
        });
        for (position, time) in &all {
            device.observe(*position, *time);
        }
        // It was set aside, and dropped when the next report lay on the line.
        assert_eq!(device.kept(), 39);
        assert_eq!(device.aside, None);
        // The line is that of the other reports, to the rounding of the
        // times they were given in.
        let (position, time) = all[39];
        assert!(
            device
                .when(position)
                .is_some_and(|at| (at - time).abs() <= 1)
        );
        let (position, time) = all[20];
        let exact = time - 4_000_000;
        assert!(
            device
                .when(position)
                .is_some_and(|at| (at - exact).abs() <= 1)
        );
    }

    #[test]
    fn a_device_that_stands_still_for_a_cycle_keeps_its_rate() {
        // 100 parts per million slow. After 32 reports the device stands
        // still for the time of one cycle, so every later report is that
        // much later.
        let stood = 5_333_867;
        let mut device = Device::<64>::new(48_000);
        let all = reports(40, 7_000_000_000, 20_835_417, |number| {
            if number >= 32 { stood } else { 0 }
        });
        for (position, time) in all.iter().take(33) {
            device.observe(*position, *time);
        }
        // The first report after the step is set aside: the line is as it
        // was.
        assert_eq!(device.kept(), 32);
        let before = all[32].1 - stood;
        assert!(
            device
                .when(all[32].0)
                .is_some_and(|at| (at - before).abs() <= 1)
        );
        // The second shows the step. All reports are kept, moved by it, so
        // the line has the rate it had: it gives the time of a frame ten
        // cycles on to the nanosecond.
        device.observe(all[33].0, all[33].1);
        assert_eq!(device.kept(), 34);
        assert_eq!(device.aside, None);
        let ahead = all[33].0 + 2_560;
        let expected =
            7_000_000_000 + stood + i64::try_from(ahead).unwrap_or(0) * 20_835_417 / 1_000;
        let found = device.when(ahead).expect("a line");
        assert!((found - expected).abs() <= 1, "{found} against {expected}");
    }

    #[test]
    fn of_two_reports_in_a_row_the_second_is_kept() {
        // Whatever the device holds and whatever the reports say: a report
        // is kept or set aside, and no two in a row are set aside.
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut device = Device::<8>::new(48_000);
        let mut was_set_aside = false;
        let mut position = 0u64;
        for _ in 0..20_000 {
            position = match next() % 16 {
                0 => next() >> (next() % 64),
                _ => position.wrapping_add(1 + next() % 1_000),
            };
            #[allow(clippy::cast_possible_wrap)]
            let time = (next() >> (next() % 64)) as i64;
            device.observe(position, time);
            let report = Reading { position, time };
            let kept = device.newest() == Some(report) && device.aside.is_none();
            let set_aside = device.aside == Some(report);
            assert!(kept || set_aside);
            assert!(!(set_aside && was_set_aside));
            was_set_aside = set_aside;
        }
    }

    #[test]
    fn a_large_window_does_not_wrap_the_sums() {
        // 512 reports with a 100 ppm slow device and 256-frame cycles would
        // wrap `i128` if `REACH` were 2^32 with adversarial spans; even with a
        // window larger than `MAX_KEPT`, the fit stays accurate and bounded.
        let mut device = Device::<5_000>::new(48_000);
        for (position, time) in reports(4_200, 1_000_000_000, 20_835_417, |_| 0) {
            device.observe(position, time);
        }
        assert_eq!(device.kept(), 4_096);
        let last = 1_000_000 + 4_199 * 256;
        let expected = 1_000_000_000 + i64::try_from(last).unwrap_or(0) * 20_835_417 / 1_000;
        let found = device.when(last).expect("a line");
        assert!((found - expected).abs() <= 2, "{found} against {expected}");
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
        assert!(device.when_cycle(7, u32::MAX).is_some());
    }

    #[test]
    fn when_cycle_matches_when_and_tracks_subnanosecond_duration() {
        // 50,000 frames/s nominally, running 1,000 ppm fast: 250 frames take
        // 4,995,004.995005 ns.
        let mut device = Device::<64>::new(50_000);
        assert_eq!(device.when_cycle(0, 250), None);
        let at =
            |position: u64| i64::try_from(u128::from(position) * 20_000_000 / 1_001).unwrap_or(0);
        device.observe(0, at(0));
        assert_eq!(device.when_cycle(0, 250), Some((0, 5_000_000 << 16)));
        let mut carried = 0i128;
        let mut sum = 0i64;
        for cycle in 1..=1_000u64 {
            let position = cycle * 250;
            device.observe(position, at(position));
            let (start, duration_q16) = device.when_cycle(position, 250).expect("a line");
            assert_eq!(Some(start), device.when(position));
            let exact = i128::from(duration_q16) + carried;
            carried = exact & 0xffff;
            let duration = i64::try_from(exact >> 16).unwrap_or(i64::MAX);
            assert!(
                (duration - 4_995_005).abs() <= 1,
                "cycle {cycle}: {duration}"
            );
            sum += duration;
        }
        assert!((sum - 4_995_004_995).abs() <= 40, "sum {sum}");
    }

    #[test]
    fn single_forward_jumped_outlier_does_not_wipe_kept_reports() {
        let mut device = Device::<16>::new(48_000);
        for cycle in 0..8u64 {
            let pos = cycle * 256;
            let time = i64::try_from(pos * 1_000_000_000 / 48_000).unwrap_or(0);
            device.observe(pos, time);
        }
        assert_eq!(device.kept(), 8);
        // One bogus forward-jumped position outlier is set aside.
        device.observe(1_000_000, 100_000_000);
        assert_eq!(device.kept(), 8);
        // Next valid report follows the last kept reading, dropping the outlier.
        let next_pos = 8 * 256;
        let next_time = i64::try_from(next_pos * 1_000_000_000 / 48_000).unwrap_or(0);
        device.observe(next_pos, next_time);
        assert_eq!(device.kept(), 9);
    }
}
