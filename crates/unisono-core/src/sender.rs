// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The sender of a stream: which index the next frame has, and what the
//! header of the next packet says.

use crate::fixed::{div_floor, saturate};
use crate::packet::{Audio, Echo, FLAG_STAMPED, Format, Report};

/// What stays the same in every packet of a stream until the sender changes
/// it.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Settings {
    /// Which stream of the sender this is.
    pub stream: u16,
    /// Frames per second.
    pub rate: u32,
    /// The number of channels.
    pub channels: u8,
    /// How a sample is written.
    pub format: Format,
    /// How long a receiver remembers samples for its estimate of the
    /// sender's clock, in milliseconds.
    pub span: u32,
    /// The number of frames that make up one window of that estimate.
    pub window: u32,
    /// Identifies the sender's clock instance: changes when the host reboots,
    /// stays constant across capture-device restarts on the same host.
    pub clock: u32,
}

/// The sender of a stream.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Sender {
    settings: Settings,
    /// The timeline that the indices count in.
    timeline: u64,
    /// The index of the next frame.
    next: u64,
    /// The frame index at which the latency equals `level_base`.
    level_index: u64,
    /// The latency held at `level_index`, in nanoseconds, and how it
    /// changes, in nanoseconds per second of stream.
    level_base: i64,
    level_slope: i32,
    /// Whether the departure of a packet of this timeline is known.
    stamped: bool,
    /// The index of the first frame of that packet, and when it left.
    stamped_index: u64,
    stamped_departure: i64,
}

impl Sender {
    /// A sender at the start of `timeline`, whose receivers hold a latency
    /// of `level` nanoseconds.
    #[must_use]
    pub fn new(settings: Settings, timeline: u64, level: i64) -> Self {
        Sender {
            settings,
            timeline,
            next: 0,
            level_index: 0,
            level_base: level,
            level_slope: 0,
            stamped: false,
            stamped_index: 0,
            stamped_departure: 0,
        }
    }

    /// The timeline that the indices count in.
    #[must_use]
    pub fn timeline(&self) -> u64 {
        self.timeline
    }

    /// The index of the next frame.
    #[must_use]
    pub fn next(&self) -> u64 {
        self.next
    }

    /// The latency held for the next frame, in nanoseconds, advancing
    /// `level_base` along `level_slope` from `level_index` to `next`.
    #[must_use]
    pub fn current_level(&self) -> i64 {
        let elapsed = self.next.saturating_sub(self.level_index);
        // At most 2^64 times 2^31: no wrapping.
        let delta = div_floor(
            (elapsed as i128).wrapping_mul(self.level_slope as i128),
            self.settings.rate as i64,
        );
        // `|level_base| <= 2^63` and `|delta| <= 2^95`: no wrapping.
        saturate((self.level_base as i128).wrapping_add(delta))
    }

    /// Sets the latency that every receiver holds starting at the next frame,
    /// in nanoseconds, and how it changes, in nanoseconds per second of
    /// stream.
    pub fn level(&mut self, level: i64, slope: i32) {
        self.level_index = self.next;
        self.level_base = level;
        self.level_slope = slope;
    }

    /// The header of the next packet: `frames` frames, the first captured
    /// at `capture` on the sender's clock by a device that runs `drift`
    /// parts per billion faster than the rate. The frames follow those of
    /// the packet before without a break.
    pub fn packet(&mut self, frames: u16, capture: i64, drift: i32) -> Audio {
        let index = self.next;
        let level = self.current_level();
        self.next = self.next.saturating_add(frames as u64);
        Audio {
            stream: self.settings.stream,
            timeline: self.timeline,
            index,
            capture,
            drift,
            rate: self.settings.rate,
            frames,
            channels: self.settings.channels,
            format: self.settings.format,
            level,
            level_slope: self.level_slope,
            span: self.settings.span,
            window: self.settings.window,
            flags: if self.stamped { FLAG_STAMPED } else { 0 },
            protection: 0,
            stamped_index: self.stamped_index,
            stamped_departure: self.stamped_departure,
            clock: self.settings.clock,
        }
    }

    /// Takes in that the packet of `timeline` whose first frame has `index`
    /// left at `departure`. Later packets carry the departure of the packet
    /// furthest on whose departure is known. A departure of another
    /// timeline, or of a packet that was not sent, is left out.
    pub fn departed(&mut self, timeline: u64, index: u64, departure: i64) {
        if timeline != self.timeline || index >= self.next {
            return;
        }
        if self.stamped && index < self.stamped_index {
            return;
        }
        self.stamped = true;
        self.stamped_index = index;
        self.stamped_departure = departure;
    }

    /// The answer to a report of a receiver that arrived when the sender's
    /// clock read `arrival` and whose answer leaves at `departure`. A report
    /// for another stream gets none.
    #[must_use]
    pub fn answer(&self, report: &Report, arrival: i64, departure: i64) -> Option<Echo> {
        if report.stream != self.settings.stream {
            return None;
        }
        Some(Echo {
            stream: report.stream,
            receiver: report.receiver,
            sequence: report.sequence,
            arrival,
            departure,
        })
    }

    /// Starts another timeline, for instance because the capture device
    /// started anew. Its number is `timeline`, or one more than the number
    /// of the timeline before if that is larger, so that receivers follow it
    /// at once.
    pub fn restart(&mut self, timeline: u64) {
        let level = self.current_level();
        let after = self.timeline.saturating_add(1);
        self.timeline = if timeline > after { timeline } else { after };
        self.next = 0;
        self.level_index = 0;
        self.level_base = level;
        self.stamped = false;
    }
}

#[cfg(test)]
mod tests {
    use super::{Sender, Settings};
    use crate::packet::{Echo, FLAG_STAMPED, Format, Report};

    fn sender() -> Sender {
        let settings = Settings {
            stream: 3,
            rate: 48_000,
            channels: 2,
            format: Format::Signed24,
            span: 11_000,
            window: 15_360,
            clock: 1,
        };
        Sender::new(settings, 100, 20_000_000)
    }

    #[test]
    fn packets_follow_each_other_without_a_break() {
        let mut sender = sender();
        let first = sender.packet(240, 1_000, 0);
        let second = sender.packet(100, 2_000, 0);
        let third = sender.packet(240, 3_000, -5);
        assert_eq!((first.index, second.index, third.index), (0, 240, 340));
        assert_eq!(sender.next(), 580);
        assert_eq!((third.timeline, third.stream, third.drift), (100, 3, -5));
        assert_eq!((third.level, third.capture), (20_000_000, 3_000));
    }

    #[test]
    fn a_packet_carries_the_latest_known_departure() {
        let mut sender = sender();
        assert_eq!(sender.packet(240, 0, 0).flags & FLAG_STAMPED, 0);
        sender.packet(240, 0, 0);
        sender.departed(100, 240, 7_000);
        // The stamp of the packet before arrives after the later one's.
        sender.departed(100, 0, 2_000);
        let header = sender.packet(240, 0, 0);
        assert_eq!(header.flags & FLAG_STAMPED, FLAG_STAMPED);
        assert_eq!(
            (header.stamped_index, header.stamped_departure),
            (240, 7_000)
        );
    }

    #[test]
    fn a_departure_that_is_not_of_this_timeline_is_left_out() {
        let mut sender = sender();
        sender.packet(240, 0, 0);
        sender.departed(99, 0, 2_000);
        // A packet that was never sent.
        sender.departed(100, 240, 2_000);
        assert_eq!(sender.packet(240, 0, 0).flags & FLAG_STAMPED, 0);
    }

    #[test]
    fn a_restart_gives_a_later_timeline_that_starts_at_zero() {
        let mut sender = sender();
        sender.packet(240, 0, 0);
        sender.departed(100, 0, 1);
        sender.restart(50);
        assert_eq!((sender.timeline(), sender.next()), (101, 0));
        assert_eq!(sender.packet(240, 0, 0).flags & FLAG_STAMPED, 0);
        sender.restart(5_000);
        assert_eq!(sender.timeline(), 5_000);
    }

    #[test]
    fn the_level_of_later_packets_advances_along_its_slope() {
        let mut s = sender();
        s.level(30_000_000, 1_000_000);
        let first = s.packet(240, 0, 0);
        let second = s.packet(240, 5_000_000, 0);
        let third = s.packet(240, 10_000_000, 0);
        assert_eq!((first.level, first.level_slope), (30_000_000, 1_000_000));
        assert_eq!((second.level, second.level_slope), (30_005_000, 1_000_000));
        assert_eq!((third.level, third.level_slope), (30_010_000, 1_000_000));
        // Over a full second (200 packets of 240 frames) there is no cumulative
        // rounding drift even for slopes that do not divide the sample rate.
        let mut s = sender();
        s.level(20_000_000, -100_000);
        for _ in 0..200 {
            s.packet(240, 0, 0);
        }
        assert_eq!(s.current_level(), 19_900_000);
        // A restart keeps the ramped level rather than snapping back.
        s.restart(200);
        let after = s.packet(240, 0, 0);
        assert_eq!((after.level, after.level_slope), (19_900_000, -100_000));
        let next = s.packet(240, 5_000_000, 0);
        assert_eq!(next.level, 19_899_500);
    }

    #[test]
    fn consecutive_ramped_packets_agree_on_the_schedule() {
        use crate::timing::{Schedule, distance, due};
        let mut sender = sender();
        sender.level(20_000_000, 500_000);
        let a = sender.packet(240, 1_000_000_000, 0);
        let b = sender.packet(240, 1_005_000_000, 0);
        let sa = Schedule {
            index: a.index,
            capture: a.capture,
            rate: a.rate,
            drift: a.drift,
            level: a.level,
            level_slope: a.level_slope,
        };
        let sb = Schedule {
            index: b.index,
            capture: b.capture,
            rate: b.rate,
            drift: b.drift,
            level: b.level,
            level_slope: b.level_slope,
        };
        // At any time during the ramp, both packets compute the same due
        // position to within one unit of 2^-32 frame.
        for offset in [25_000_000i64, 30_000_000, 100_000_000] {
            let t = 1_000_000_000 + offset;
            let pa = due(&sa, t).expect("in timeline");
            let pb = due(&sb, t).expect("in timeline");
            assert!(
                distance(pa, pb).abs() <= 1,
                "offset {offset}: pa={pa:?}, pb={pb:?}"
            );
        }
    }

    #[test]
    fn a_report_is_answered_with_its_arrival() {
        let sender = sender();
        let report = Report {
            stream: 3,
            timeline: 100,
            receiver: 42,
            sequence: 7,
        };
        assert_eq!(
            sender.answer(&report, 123_456, 123_900),
            Some(Echo {
                stream: 3,
                receiver: 42,
                sequence: 7,
                arrival: 123_456,
                departure: 123_900,
            })
        );
        let other = Report {
            stream: 4,
            ..report
        };
        assert_eq!(sender.answer(&other, 123_456, 123_900), None);
    }
}
