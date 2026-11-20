// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The receiver of a stream: which timeline it follows, which frames it
//! holds, and which frame its device gets next.
//!
//! There is no session. A receiver follows one timeline at a time and takes
//! up another when a packet of a later timeline arrives, or when the one it
//! follows has been silent for a while. Whatever state it is in, packets of a
//! timeline that keep arriving are therefore followed after that while at
//! the latest.
//!
//! The frames of the timeline pass the receiver's **playhead** once and in
//! order: the playhead is the index of the next frame for the device, it
//! only moves forward, and every index it passes is reported exactly once,
//! as held, as absent, or as skipped.

use crate::arrivals::Arrivals;
use crate::packet::{Audio, FLAG_STAMPED};
use crate::presence::{Marked, Presence};
use crate::relation::{Estimator, Line, Sample};

/// The number of nanoseconds in a millisecond.
const MILLISECOND: i64 = 1_000_000;

/// What a receiver did with a packet.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub struct Heard {
    /// The packet is of a timeline that the receiver does not follow, and
    /// nothing was done with it.
    pub ignored: bool,
    /// The receiver began to follow the packet's timeline with this packet.
    pub adopted: bool,
    /// What became of the packet's frames.
    pub marked: Marked,
}

/// A run of frames at the playhead that are all held or all absent.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub struct Segment {
    /// The index of the first frame of the run.
    pub first: u64,
    /// The number of frames in the run.
    pub frames: u32,
    /// Whether the frames are held. Absent frames are to be concealed.
    pub held: bool,
}

/// When the frames of a timeline are due, as the latest packet says it.
///
/// The frame `index` was captured at `capture` on the sender's clock, and
/// the frames after it follow at `rate` frames per second, faster by `drift`
/// parts per billion. A frame is due at its capture time plus the level.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub struct Schedule {
    /// The index of a frame.
    pub index: u64,
    /// When that frame was captured.
    pub capture: i64,
    /// Frames per second.
    pub rate: u32,
    /// How much faster than `rate` the capture device runs against the
    /// sender's clock, in parts per billion.
    pub drift: i32,
    /// The latency that every receiver holds for that frame.
    pub level: i64,
    /// How the level changes, in nanoseconds per second of stream.
    pub level_slope: i32,
}

/// The receiver of a stream.
///
/// It holds up to `64 * N` frames ahead of the playhead, remembers `M`
/// samples for its estimate of the sender's clock, and keeps the arrivals of
/// the last `K` packets.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub struct Receiver<const N: usize, const M: usize, const K: usize> {
    /// Whether a timeline is followed.
    following: bool,
    /// The timeline that is followed.
    timeline: u64,
    /// The receiver's clock when a packet of the followed timeline last
    /// arrived.
    heard: i64,
    /// How long the followed timeline is silent before any other is taken
    /// up, in nanoseconds.
    silence: i64,
    /// The largest slope of the estimate of the sender's clock, in
    /// nanoseconds per second.
    limit: i64,
    presence: Presence<N>,
    clock: Estimator<M>,
    arrivals: Arrivals<K>,
    schedule: Option<Schedule>,
}

/// How long a receiver remembers samples of the sender's clock, in
/// nanoseconds, as a header gives it.
fn span_of(header: &Audio) -> i64 {
    // A 32-bit number of milliseconds: no wrapping.
    (header.span as i64).wrapping_mul(MILLISECOND)
}

impl<const N: usize, const M: usize, const K: usize> Receiver<N, M, K> {
    /// A receiver that follows no timeline yet. It takes up another timeline
    /// than the one it follows after `silence` nanoseconds without a packet,
    /// and holds the slope of its estimate of the sender's clock within
    /// `limit` nanoseconds per second.
    #[must_use]
    pub fn new(silence: i64, limit: i64) -> Self {
        Receiver {
            following: false,
            timeline: 0,
            heard: 0,
            silence,
            limit,
            presence: Presence::new(),
            clock: Estimator::new(0, limit),
            arrivals: Arrivals::new(),
            schedule: None,
        }
    }

    /// The timeline that is followed, if any.
    #[must_use]
    pub fn timeline(&self) -> Option<u64> {
        if self.following {
            Some(self.timeline)
        } else {
            None
        }
    }

    /// The index of the next frame for the device.
    #[must_use]
    pub fn playhead(&self) -> u64 {
        self.presence.base()
    }

    /// Whether there is room for the frame at `index`: the caller keeps the
    /// samples of exactly these frames.
    #[must_use]
    pub fn covers(&self, index: u64) -> bool {
        self.following && self.presence.covers(index)
    }

    /// The estimate of the receiver's clock minus the sender's clock, as a
    /// line over the sender's clock, once there is one.
    #[must_use]
    pub fn clock(&self) -> Option<Line> {
        self.clock.line()
    }

    /// When the frames of the followed timeline are due, once a packet has
    /// said it.
    #[must_use]
    pub fn schedule(&self) -> Option<Schedule> {
        self.schedule
    }

    /// Whether a packet of `timeline` that arrives at `arrival` makes the
    /// receiver follow that timeline instead of what it follows now.
    fn adopts(&self, timeline: u64, arrival: i64) -> bool {
        if !self.following {
            return true;
        }
        if timeline == self.timeline {
            return false;
        }
        timeline > self.timeline || arrival.saturating_sub(self.heard) >= self.silence
    }

    /// Begins to follow the timeline of `header`, with nothing held and
    /// nothing known about the sender's clock.
    fn adopt(&mut self, header: &Audio) {
        self.following = true;
        self.timeline = header.timeline;
        self.presence.restart(header.index);
        self.clock = Estimator::new(span_of(header), self.limit);
        self.arrivals = Arrivals::new();
        self.schedule = None;
    }

    /// When the earlier packet arrived whose departure `header` carries, if
    /// it carries one and that arrival is still kept.
    fn stamped_arrival(&self, header: &Audio) -> Option<i64> {
        if header.flags & FLAG_STAMPED == 0 {
            return None;
        }
        self.arrivals.find(header.stamped_index)
    }

    /// Gives the estimate of the sender's clock the sample of the earlier
    /// packet whose departure `header` carries and which arrived at
    /// `arrived`.
    fn sample(&mut self, header: &Audio, arrived: i64) {
        let sample = Sample {
            time: header.stamped_departure,
            value: arrived.saturating_sub(header.stamped_departure),
        };
        // A window of no frames makes every packet a window.
        let window = header
            .stamped_index
            .checked_div(header.window as u64)
            .unwrap_or(header.stamped_index);
        self.clock.observe(window, sample);
    }

    /// Takes from a packet of the followed timeline what it says about the
    /// sender's clock, and keeps its arrival for a later packet to refer to.
    fn measure(&mut self, header: &Audio, arrival: i64) {
        self.clock.remember(span_of(header));
        if let Some(arrived) = self.stamped_arrival(header) {
            self.sample(header, arrived);
        }
        self.arrivals.record(header.index, arrival);
    }

    /// Keeps what `header` says about when frames are due, unless a packet
    /// further on in the timeline has said it already.
    fn note(&mut self, header: &Audio) {
        let newer = match self.schedule {
            Some(schedule) => header.index >= schedule.index,
            None => true,
        };
        if newer {
            self.schedule = Some(Schedule {
                index: header.index,
                capture: header.capture,
                rate: header.rate,
                drift: header.drift,
                level: header.level,
                level_slope: header.level_slope,
            });
        }
    }

    /// Takes in a packet of the followed timeline.
    fn accept(&mut self, header: &Audio, arrival: i64, adopted: bool) -> Heard {
        self.heard = arrival;
        self.measure(header, arrival);
        self.note(header);
        let marked = self.presence.mark(header.index, header.frames as u32);
        Heard {
            ignored: false,
            adopted,
            marked,
        }
    }

    /// Takes in the packet with `header` that arrived when the receiver's
    /// clock read `arrival`, and says what was done with it.
    pub fn packet(&mut self, header: &Audio, arrival: i64) -> Heard {
        // The clock is not behind the last arrival; a record that says so is
        // wrong, and is put right here so that silence is noticed.
        if self.heard > arrival {
            self.heard = arrival;
        }
        let adopted = self.adopts(header.timeline, arrival);
        if adopted {
            self.adopt(header);
        } else if header.timeline != self.timeline {
            return Heard {
                ignored: true,
                adopted: false,
                marked: Marked {
                    stored: 0,
                    duplicate: 0,
                    late: 0,
                    early: 0,
                },
            };
        }
        self.accept(header, arrival, adopted)
    }

    /// Moves the playhead forward by `frames`.
    fn pass(&mut self, frames: u32) {
        let base = self.presence.base();
        self.presence.advance(base.saturating_add(frames as u64));
    }

    /// Takes the next run of frames for the device: up to `limit` frames
    /// from the playhead on that are all held or all absent. The playhead
    /// moves past them. Without a timeline the run is empty.
    pub fn take(&mut self, limit: u32) -> Segment {
        let first = self.presence.base();
        if !self.following {
            return Segment {
                first,
                frames: 0,
                held: false,
            };
        }
        let run = self.presence.run(first, limit);
        if run > 0 {
            self.pass(run);
            return Segment {
                first,
                frames: run,
                held: true,
            };
        }
        let gap = self.presence.gap(first, limit);
        self.pass(gap);
        Segment {
            first,
            frames: gap,
            held: false,
        }
    }

    /// Moves the playhead forward to `to` without giving the frames before
    /// it to the device, and returns how many frames that skips. A `to` that
    /// is not ahead of the playhead skips nothing: the playhead never moves
    /// back.
    pub fn skip(&mut self, to: u64) -> u64 {
        let base = self.presence.base();
        if !self.following || to <= base {
            return 0;
        }
        self.presence.advance(to);
        to.wrapping_sub(base)
    }
}

#[cfg(test)]
mod tests {
    use super::{Heard, Receiver, Segment};
    use crate::packet::{Audio, FLAG_STAMPED, Format};
    use crate::presence::Marked;

    const SILENCE: i64 = 1_000_000_000;

    fn header(timeline: u64, index: u64, frames: u16) -> Audio {
        Audio {
            stream: 1,
            timeline,
            index,
            capture: 0,
            drift: 0,
            rate: 48_000,
            frames,
            channels: 2,
            format: Format::Signed16,
            level: 20_000_000,
            level_slope: 0,
            span: 11_000,
            window: 480,
            flags: 0,
            protection: 0,
            stamped_index: 0,
            stamped_departure: 0,
        }
    }

    fn stored(frames: u32) -> Marked {
        Marked {
            stored: frames,
            ..Marked::default()
        }
    }

    fn receiver() -> Receiver<4, 8, 4> {
        Receiver::new(SILENCE, 200_000)
    }

    #[test]
    fn the_first_packet_starts_a_timeline_at_its_index() {
        let mut receiver = receiver();
        assert_eq!(receiver.timeline(), None);
        assert_eq!(receiver.take(10).frames, 0);
        let heard = receiver.packet(&header(7, 4_800, 10), 0);
        assert_eq!(
            heard,
            Heard {
                ignored: false,
                adopted: true,
                marked: stored(10)
            }
        );
        assert_eq!(receiver.timeline(), Some(7));
        assert_eq!(receiver.playhead(), 4_800);
        assert!(receiver.covers(4_800) && !receiver.covers(4_799));
    }

    #[test]
    fn frames_pass_the_playhead_once_and_in_order() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        // The second packet is lost; the third arrives.
        receiver.packet(&header(7, 20, 10), 1);
        let mut segments = [Segment {
            first: 0,
            frames: 0,
            held: false,
        }; 4];
        for segment in &mut segments {
            *segment = receiver.take(16);
        }
        let expected = [
            (0, 10, true),
            (10, 10, false),
            (20, 10, true),
            (30, 16, false),
        ];
        for (segment, (first, frames, held)) in segments.iter().zip(expected) {
            assert_eq!(
                *segment,
                Segment {
                    first,
                    frames,
                    held
                }
            );
        }
        assert_eq!(receiver.playhead(), 46);
        // The lost packet arrives after its frames were due.
        let heard = receiver.packet(&header(7, 10, 10), 2);
        assert_eq!(
            heard.marked,
            Marked {
                late: 10,
                ..Marked::default()
            }
        );
    }

    #[test]
    fn a_run_is_cut_at_the_limit() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        assert_eq!(receiver.take(4).frames, 4);
        assert_eq!(receiver.take(0).frames, 0);
        assert_eq!(receiver.playhead(), 4);
    }

    #[test]
    fn a_skip_moves_the_playhead_forward_only() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        assert_eq!(receiver.skip(6), 6);
        assert_eq!(receiver.skip(3), 0);
        assert_eq!(receiver.playhead(), 6);
        assert_eq!(receiver.take(16).frames, 4);
    }

    #[test]
    fn a_later_timeline_is_followed_at_once_and_an_earlier_one_is_ignored() {
        let mut receiver = receiver();
        receiver.packet(&header(7, 0, 10), 0);
        let heard = receiver.packet(&header(9, 100, 10), 1);
        assert!(heard.adopted && !heard.ignored);
        assert_eq!((receiver.timeline(), receiver.playhead()), (Some(9), 100));
        // A packet of the old timeline that was still under way.
        let heard = receiver.packet(&header(7, 10, 10), 2);
        assert!(heard.ignored && !heard.adopted);
        assert_eq!(receiver.timeline(), Some(9));
    }

    #[test]
    fn an_earlier_timeline_is_followed_once_the_other_is_silent() {
        let mut receiver = receiver();
        receiver.packet(&header(9, 0, 10), 0);
        assert!(receiver.packet(&header(7, 0, 10), SILENCE - 1).ignored);
        let heard = receiver.packet(&header(7, 10, 10), SILENCE);
        assert!(heard.adopted);
        assert_eq!((receiver.timeline(), receiver.playhead()), (Some(7), 10));
    }

    #[test]
    fn a_record_of_the_last_arrival_that_lies_ahead_does_not_block_another_timeline() {
        let mut receiver = receiver();
        receiver.packet(&header(9, 0, 10), 0);
        receiver.heard = i64::MAX;
        assert!(receiver.packet(&header(7, 0, 10), 5).ignored);
        assert!(receiver.packet(&header(7, 10, 10), 5 + SILENCE).adopted);
    }

    #[test]
    fn stamps_of_earlier_packets_give_the_sender_s_clock() {
        // The receiver's clock is 5 ms ahead of the sender's, and every
        // packet takes 100 microseconds.
        let mut receiver = receiver();
        let period = 10_000_000i64;
        for packet in 0..200u64 {
            let departure = i64::try_from(packet).unwrap_or(0) * period;
            let mut header = header(7, packet * 480, 480);
            if packet > 0 {
                header.flags = FLAG_STAMPED;
                header.stamped_index = (packet - 1) * 480;
                header.stamped_departure = departure - period;
            }
            receiver.packet(&header, departure + 5_000_000 + 100_000);
        }
        let line = receiver.clock().expect("a line after many windows");
        assert_eq!(line.eval(1_000_000_000), 5_100_000);
    }

    #[test]
    fn the_schedule_is_the_one_of_the_packet_furthest_on() {
        let mut receiver = receiver();
        let mut first = header(7, 100, 10);
        first.capture = 1_000;
        let mut earlier = header(7, 90, 10);
        earlier.capture = 500;
        receiver.packet(&first, 0);
        receiver.packet(&earlier, 1);
        let schedule = receiver.schedule().expect("a schedule after a packet");
        assert_eq!((schedule.index, schedule.capture), (100, 1_000));
    }
}
