// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! What a receiver asks the sender to send again.
//!
//! The packets of a timeline follow each other without a break, so a packet
//! whose first frame lies beyond the frame after the last one that arrived
//! says that the frames between are missing: lost, or overtaken and still
//! on their way. The network thread of a receiver asks for them at once, and
//! again every ten milliseconds until they have arrived or it is too late
//! for them. In simulation (`unisono_sim::protection`) this costs less than
//! any copy or code sent in advance wherever packets are lost, and adds to
//! the stream only what was lost.
//!
//! It is too late for a frame once the level has passed since it was found
//! missing: a frame is due the level after it was captured, and it was
//! captured before the packet that showed it missing. For the same reason
//! frames further back than the level are not asked for when a packet shows
//! a long run missing.
//!
//! A packet that is sent again arrives late, and what its frames needed is
//! measured as for any packet. So the sender's choice of the level takes in
//! what the repairs need, and holds the level high enough for them when
//! that costs less than the gaps they close.

use unisono_core::packet::{Audio, PROTECTION_ON_REQUEST};

/// How many runs of missing frames are followed at a time. An outage leaves
/// one; a ninth takes the place of the one found longest ago.
const RUNS: usize = 8;

/// How long after a request the same frames are asked for again, in
/// nanoseconds: ten milliseconds.
const AGAIN: i64 = 10_000_000;

/// A run of frames that are missing.
#[derive(Clone, Copy, Debug)]
struct Run {
    first: u64,
    frames: u64,
    /// When the run was found, on the receiver's clock.
    found: i64,
    /// When it was last asked for.
    asked: Option<i64>,
    /// For how long after it was found it is worth asking for, in
    /// nanoseconds.
    patience: i64,
}

/// A request that is due: frames of a timeline to ask for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Wanted {
    /// The timeline of the frames.
    pub timeline: u64,
    /// The first of them.
    pub first: u64,
    /// How many there are.
    pub frames: u64,
}

/// The frames of a stream that a receiver misses and asks for.
#[derive(Clone, Copy, Debug)]
pub struct Asking {
    /// The timeline of the packets that arrive, once one has.
    timeline: Option<u64>,
    /// The frame after the last one of the packets that arrived.
    next: u64,
    runs: [Option<Run>; RUNS],
}

impl Default for Asking {
    fn default() -> Asking {
        Asking::new()
    }
}

impl Asking {
    /// Nothing has arrived, and nothing is missing.
    #[must_use]
    pub fn new() -> Asking {
        Asking {
            timeline: None,
            next: 0,
            runs: [None; RUNS],
        }
    }

    /// Takes in that the packet with `header` arrived at `time` on the
    /// receiver's clock.
    pub fn arrived(&mut self, header: &Audio, time: i64) {
        if header.protection != PROTECTION_ON_REQUEST {
            // The sender of this stream sends nothing again.
            *self = Asking::new();
            return;
        }
        let end = header.index.saturating_add(u64::from(header.frames));
        if self.timeline != Some(header.timeline) {
            *self = Asking::new();
            self.timeline = Some(header.timeline);
            self.next = end;
            return;
        }
        if header.index > self.next {
            // The frames that the level reaches back to from this packet.
            let patience = header.level.max(0);
            let reach =
                u64::try_from(i128::from(patience) * i128::from(header.rate) / 1_000_000_000)
                    .unwrap_or(0);
            let first = self.next.max(header.index.saturating_sub(reach));
            if header.index > first {
                self.open(Run {
                    first,
                    frames: header.index - first,
                    found: time,
                    asked: None,
                    patience,
                });
            }
        } else if header.index < self.next {
            self.fill(header.index, end);
        }
        self.next = self.next.max(end);
    }

    /// Follows `run`, in a free place or in the place of the run found
    /// longest ago.
    fn open(&mut self, run: Run) {
        let free = self.runs.iter().position(Option::is_none);
        let oldest = self
            .runs
            .iter()
            .enumerate()
            .min_by_key(|(_, kept)| kept.map_or(i64::MIN, |kept| kept.found))
            .map(|(place, _)| place);
        if let Some(slot) = free.or(oldest).and_then(|place| self.runs.get_mut(place)) {
            *slot = Some(run);
        }
    }

    /// Takes in that the frames from `from` up to `to` arrived: a run that
    /// they begin or end is that much shorter.
    fn fill(&mut self, from: u64, to: u64) {
        for slot in &mut self.runs {
            let Some(run) = slot else {
                continue;
            };
            let end = run.first.saturating_add(run.frames);
            if from <= run.first && to > run.first {
                let covered = to.min(end) - run.first;
                run.first += covered;
                run.frames -= covered;
            } else if from > run.first && from < end && to >= end {
                run.frames = from - run.first;
            }
            if run.frames == 0 {
                *slot = None;
            }
        }
    }

    /// The next request that is due at `now` on the receiver's clock, if
    /// one is; it then counts as asked at `now`. Runs for which it is too
    /// late are given up.
    pub fn due(&mut self, now: i64) -> Option<Wanted> {
        let timeline = self.timeline?;
        for slot in &mut self.runs {
            let Some(run) = slot else {
                continue;
            };
            if now.saturating_sub(run.found) > run.patience {
                *slot = None;
                continue;
            }
            if run
                .asked
                .is_none_or(|asked| now.saturating_sub(asked) >= AGAIN)
            {
                run.asked = Some(now);
                return Some(Wanted {
                    timeline,
                    first: run.first,
                    frames: run.frames,
                });
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use unisono_core::packet::{Audio, Format, PROTECTION_ON_REQUEST};

    use super::{Asking, Wanted};

    /// The header of a packet of 240 frames from `index` on, of a stream at
    /// 48 kHz whose level is 30 ms.
    fn packet(index: u64) -> Audio {
        Audio {
            stream: 1,
            timeline: 7,
            index,
            capture: 0,
            rate: 48_000,
            frames: 240,
            channels: 2,
            format: Format::Signed24,
            level: 30_000_000,
            level_slope: 0,
            span: 2_000,
            window: 2_400,
            flags: 0,
            protection: PROTECTION_ON_REQUEST,
            stamped_index: 0,
            stamped_departure: 0,
            drift: 0,
            clock: 1,
        }
    }

    fn wanted(first: u64, frames: u64) -> Wanted {
        Wanted {
            timeline: 7,
            first,
            frames,
        }
    }

    #[test]
    fn packets_in_order_leave_nothing_to_ask_for() {
        let mut asking = Asking::new();
        for k in 0..100 {
            asking.arrived(&packet(k * 240), i64::try_from(k).unwrap() * 5_000_000);
            assert_eq!(asking.due(i64::try_from(k).unwrap() * 5_000_000), None);
        }
    }

    #[test]
    fn missing_frames_are_asked_for_at_once_and_again_until_they_arrive() {
        let mut asking = Asking::new();
        asking.arrived(&packet(0), 0);
        // Three packets are lost.
        asking.arrived(&packet(960), 20_000_000);
        assert_eq!(asking.due(20_000_000), Some(wanted(240, 720)));
        assert_eq!(asking.due(20_000_000), None);
        assert_eq!(asking.due(29_000_000), None);
        assert_eq!(asking.due(30_000_000), Some(wanted(240, 720)));
        // The first of them arrives, then the last.
        asking.arrived(&packet(240), 31_000_000);
        asking.arrived(&packet(720), 32_000_000);
        assert_eq!(asking.due(40_000_000), Some(wanted(480, 240)));
        asking.arrived(&packet(480), 41_000_000);
        assert_eq!(asking.due(60_000_000), None);
    }

    #[test]
    fn frames_are_given_up_when_it_is_too_late_for_them() {
        let mut asking = Asking::new();
        asking.arrived(&packet(0), 0);
        asking.arrived(&packet(480), 10_000_000);
        assert_eq!(asking.due(10_000_000), Some(wanted(240, 240)));
        // The level is 30 ms: after that the frames are past.
        assert_eq!(asking.due(41_000_000), None);
        assert_eq!(asking.due(60_000_000), None);
    }

    #[test]
    fn a_long_run_is_asked_for_only_as_far_back_as_the_level_reaches() {
        let mut asking = Asking::new();
        asking.arrived(&packet(0), 0);
        // A second of frames is missing; 30 ms are 1440 frames.
        asking.arrived(&packet(48_240), 1_000_000_000);
        assert_eq!(asking.due(1_000_000_000), Some(wanted(46_800, 1_440)));
    }

    #[test]
    fn another_timeline_and_a_stream_without_protection_ask_for_nothing() {
        let mut asking = Asking::new();
        asking.arrived(&packet(0), 0);
        let other = Audio {
            timeline: 8,
            ..packet(9_600)
        };
        asking.arrived(&other, 10_000_000);
        assert_eq!(asking.due(10_000_000), None);
        let bare = Audio {
            protection: 0,
            ..packet(96_000)
        };
        asking.arrived(&bare, 20_000_000);
        assert_eq!(asking.due(20_000_000), None);
    }
}
