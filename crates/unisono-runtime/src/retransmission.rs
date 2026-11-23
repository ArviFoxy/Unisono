// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Receiver-side missing-frame tracking and retransmission scheduling.
//!
//! Packets within a timeline carry contiguous frame indices, so an incoming
//! packet with `header.index > next` exposes a gap of missing or reordered
//! frames. The receiver network thread requests those ranges immediately and
//! retries every 10 ms until the missing frames arrive or the stream playout
//! latency (`header.level`) has elapsed since the gap was detected.
//!
//! Ranges older than `header.level` relative to the triggering packet are
//! clipped at insertion because they would already be past their playout
//! deadline. Retransmitted packets are measured through the same need
//! accounting as original packets, so the adaptive level controller accounts
//! for repair latency automatically.

use unisono_core::packet::{Audio, PROTECTION_ON_REQUEST};

/// Maximum number of concurrent missing-frame gaps tracked. When full, a new
/// gap evicts the oldest active entry.
const RUNS: usize = 8;

/// Minimum retry interval for a missing-frame range, in nanoseconds (10 ms).
const RETRY_INTERVAL_NS: i64 = 10_000_000;

/// A contiguous range of missing frames.
#[derive(Clone, Copy, Debug)]
struct Gap {
    first: u64,
    frames: u64,
    /// Receiver raw-clock timestamp (ns) when this gap was first detected.
    detected_at: i64,
    /// Receiver raw-clock timestamp (ns) of the most recent retransmit request.
    last_requested: Option<i64>,
    /// Maximum time (ns) after `detected_at` during which retries remain useful.
    patience_ns: i64,
}

/// A retransmission request ready to send to the sender.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RetransmitRequest {
    /// Timeline identifier of the missing frames.
    pub timeline: u64,
    /// First missing frame index.
    pub first: u64,
    /// Number of contiguous missing frames.
    pub frames: u64,
}

/// Tracks missing frame ranges on the receiver network thread and schedules
/// periodic retransmission requests without heap allocation.
#[derive(Clone, Copy, Debug)]
pub struct RetransmissionTracker {
    /// Active timeline identifier once at least one protected packet arrives.
    timeline: Option<u64>,
    /// Highest frame index seen plus one (next expected contiguous frame).
    next: u64,
    gaps: [Option<Gap>; RUNS],
}

impl Default for RetransmissionTracker {
    fn default() -> RetransmissionTracker {
        RetransmissionTracker::new()
    }
}

impl RetransmissionTracker {
    /// Creates an empty tracker with no active timeline or gaps.
    #[must_use]
    pub fn new() -> RetransmissionTracker {
        RetransmissionTracker {
            timeline: None,
            next: 0,
            gaps: [None; RUNS],
        }
    }

    /// Records the arrival of an audio packet at receiver clock timestamp
    /// `time` (ns), opening new missing-frame gaps or filling existing ones.
    pub fn arrived(&mut self, header: &Audio, time: i64) {
        if header.protection != PROTECTION_ON_REQUEST {
            // Retransmission is disabled on this stream.
            *self = RetransmissionTracker::new();
            return;
        }
        let end = header.index.saturating_add(u64::from(header.frames));
        if self.timeline != Some(header.timeline) {
            *self = RetransmissionTracker::new();
            self.timeline = Some(header.timeline);
            self.next = end;
            return;
        }
        if header.index > self.next {
            // Clip the gap to the frames that fall within the playout latency window.
            let patience_ns = header.level.max(0);
            let reach =
                u64::try_from(i128::from(patience_ns) * i128::from(header.rate) / 1_000_000_000)
                    .unwrap_or(u64::MAX);
            let first = self.next.max(header.index.saturating_sub(reach));
            if header.index > first {
                self.insert(Gap {
                    first,
                    frames: header.index - first,
                    detected_at: time,
                    last_requested: None,
                    patience_ns,
                });
            }
        } else if header.index < self.next {
            self.fill(header.index, end);
        }
        self.next = self.next.max(end);
    }

    /// Inserts `gap` into a free slot, evicting the oldest slot if full.
    fn insert(&mut self, gap: Gap) {
        let free = self.gaps.iter().position(Option::is_none);
        let oldest = self
            .gaps
            .iter()
            .enumerate()
            .min_by_key(|(_, slot)| slot.map_or(i64::MIN, |g| g.detected_at))
            .map(|(idx, _)| idx);
        if let Some(slot) = free.or(oldest).and_then(|idx| self.gaps.get_mut(idx)) {
            *slot = Some(gap);
        }
    }

    /// Removes the arriving range `[from, to)` from all tracked gaps: trimming
    /// prefix/suffix overlaps, clearing fully covered gaps, and splitting
    /// interior overlaps into two separate gaps.
    fn fill(&mut self, from: u64, to: u64) {
        if to <= from {
            return;
        }
        let mut splits: [Option<Gap>; RUNS] = [None; RUNS];
        let mut split_count = 0usize;
        for slot in &mut self.gaps {
            let Some(gap) = slot else {
                continue;
            };
            let end = gap.first.saturating_add(gap.frames);
            if to <= gap.first || from >= end {
                continue;
            }
            if from <= gap.first && to >= end {
                *slot = None;
            } else if from <= gap.first {
                let covered = to - gap.first;
                gap.first += covered;
                gap.frames -= covered;
            } else if to >= end {
                gap.frames = from - gap.first;
            } else {
                let suffix = Gap {
                    first: to,
                    frames: end - to,
                    detected_at: gap.detected_at,
                    last_requested: gap.last_requested,
                    patience_ns: gap.patience_ns,
                };
                gap.frames = from - gap.first;
                if let Some(target) = splits.get_mut(split_count) {
                    *target = Some(suffix);
                    split_count += 1;
                }
            }
        }
        for suffix in splits.into_iter().take(split_count).flatten() {
            self.insert(suffix);
        }
    }

    /// Returns nanoseconds until the next retransmission request becomes due
    /// at `now`, `Some(0)` if one is due immediately, or `None` if no active
    /// gap remains.
    #[must_use]
    pub fn next_due(&self, now: i64) -> Option<i64> {
        self.timeline?;
        let mut earliest: Option<i64> = None;
        for gap in self.gaps.iter().flatten() {
            if now.saturating_sub(gap.detected_at) > gap.patience_ns {
                continue;
            }
            let wait = match gap.last_requested {
                None => 0,
                Some(last) => RETRY_INTERVAL_NS
                    .saturating_sub(now.saturating_sub(last))
                    .max(0),
            };
            earliest = Some(earliest.map_or(wait, |best| best.min(wait)));
        }
        earliest
    }

    /// Returns the next due retransmission request at receiver clock `now`
    /// (ns) and marks it requested, dropping any gaps whose patience window
    /// has expired.
    pub fn due(&mut self, now: i64) -> Option<RetransmitRequest> {
        let timeline = self.timeline?;
        for slot in &mut self.gaps {
            let Some(gap) = slot else {
                continue;
            };
            if now.saturating_sub(gap.detected_at) > gap.patience_ns {
                *slot = None;
                continue;
            }
            if gap
                .last_requested
                .is_none_or(|last| now.saturating_sub(last) >= RETRY_INTERVAL_NS)
            {
                gap.last_requested = Some(now);
                return Some(RetransmitRequest {
                    timeline,
                    first: gap.first,
                    frames: gap.frames,
                });
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use unisono_core::packet::{Audio, Format, PROTECTION_ON_REQUEST};

    use super::{RetransmissionTracker, RetransmitRequest};

    /// Builds a 240-frame 48 kHz packet header with 30 ms playout level.
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

    fn request(first: u64, frames: u64) -> RetransmitRequest {
        RetransmitRequest {
            timeline: 7,
            first,
            frames,
        }
    }

    #[test]
    fn in_order_packets_produce_no_requests() {
        let mut tracker = RetransmissionTracker::new();
        for k in 0..100 {
            tracker.arrived(&packet(k * 240), i64::try_from(k).unwrap() * 5_000_000);
            assert_eq!(tracker.due(i64::try_from(k).unwrap() * 5_000_000), None);
        }
    }

    #[test]
    fn missing_frames_requested_immediately_and_retried_until_filled() {
        let mut tracker = RetransmissionTracker::new();
        tracker.arrived(&packet(0), 0);
        // Drop three packets: [240..960).
        tracker.arrived(&packet(960), 20_000_000);
        assert_eq!(tracker.due(20_000_000), Some(request(240, 720)));
        assert_eq!(tracker.due(20_000_000), None);
        assert_eq!(tracker.due(29_000_000), None);
        assert_eq!(tracker.due(30_000_000), Some(request(240, 720)));
        // Prefix and suffix packets arrive; only the middle packet remains.
        tracker.arrived(&packet(240), 31_000_000);
        tracker.arrived(&packet(720), 32_000_000);
        assert_eq!(tracker.due(40_000_000), Some(request(480, 240)));
        tracker.arrived(&packet(480), 41_000_000);
        assert_eq!(tracker.due(60_000_000), None);
    }

    #[test]
    fn expired_gaps_are_dropped() {
        let mut tracker = RetransmissionTracker::new();
        tracker.arrived(&packet(0), 0);
        tracker.arrived(&packet(480), 10_000_000);
        assert_eq!(tracker.due(10_000_000), Some(request(240, 240)));
        // Playout level is 30 ms; at 41 ms the gap has expired.
        assert_eq!(tracker.due(41_000_000), None);
        assert_eq!(tracker.due(60_000_000), None);
    }

    #[test]
    fn long_gap_clipped_to_playout_window() {
        let mut tracker = RetransmissionTracker::new();
        tracker.arrived(&packet(0), 0);
        // 1 s gap; 30 ms at 48 kHz is 1,440 frames.
        tracker.arrived(&packet(48_240), 1_000_000_000);
        assert_eq!(tracker.due(1_000_000_000), Some(request(46_800, 1_440)));
    }

    #[test]
    fn arbitrary_arrival_order_only_requests_missing_frames() {
        // Fuzz randomized reordering, loss, duplication, index jumps, and
        // backwards timestamps: every request must stay strictly within the
        // observed timeline bounds and start on a frame that never arrived.
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut draw = |bound: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % bound
        };
        let mut tracker = RetransmissionTracker::new();
        let mut arrived = std::collections::BTreeSet::new();
        let mut furthest = 0u64;
        let mut place = 0u64;
        for step in 0..20_000i64 {
            place = match draw(20) {
                0 => place.saturating_sub(draw(40)),
                1 => place + draw(60),
                2 => place + 2,
                _ => place + 1,
            };
            let index = place * 240;
            tracker.arrived(
                &packet(index),
                step * 5_000_000 - i64::try_from(draw(3)).unwrap(),
            );
            arrived.insert(index);
            furthest = furthest.max(index + 240);
            while let Some(req) = tracker.due(step * 5_000_000) {
                assert_eq!(req.timeline, 7);
                assert!(req.frames > 0, "{req:?}");
                assert!(req.first + req.frames <= furthest, "{req:?}");
                assert!(!arrived.contains(&req.first), "{req:?} at step {step}");
            }
        }
    }

    #[test]
    fn timeline_change_or_unprotected_stream_clears_state() {
        let mut tracker = RetransmissionTracker::new();
        tracker.arrived(&packet(0), 0);
        let other = Audio {
            timeline: 8,
            ..packet(9_600)
        };
        tracker.arrived(&other, 10_000_000);
        assert_eq!(tracker.due(10_000_000), None);
        let bare = Audio {
            protection: 0,
            ..packet(96_000)
        };
        tracker.arrived(&bare, 20_000_000);
        assert_eq!(tracker.due(20_000_000), None);
    }

    #[test]
    fn interior_packet_splits_gap_into_prefix_and_suffix() {
        let mut tracker = RetransmissionTracker::new();
        tracker.arrived(&packet(0), 0);
        // Packets at 240, 480, 720 are missing.
        tracker.arrived(&packet(960), 20_000_000);
        assert_eq!(tracker.next_due(20_000_000), Some(0));
        assert_eq!(tracker.due(20_000_000), Some(request(240, 720)));
        assert_eq!(tracker.next_due(23_000_000), Some(7_000_000));
        // Middle packet [480..720) arrives first.
        tracker.arrived(&packet(480), 25_000_000);
        // Both [240..480) and [720..960) are re-requested at 30 ms, but NOT [480..720).
        let mut requests = Vec::new();
        while let Some(req) = tracker.due(30_000_000) {
            requests.push(req);
        }
        assert_eq!(requests, vec![request(240, 240), request(720, 240)]);
        // Filling both remaining halves clears all active gaps.
        tracker.arrived(&packet(240), 31_000_000);
        tracker.arrived(&packet(720), 32_000_000);
        assert_eq!(tracker.next_due(32_000_000), None);
        assert_eq!(tracker.due(40_000_000), None);
    }

    #[test]
    fn huge_patience_times_rate_saturates_reach_instead_of_dropping_gap() {
        let mut tracker = RetransmissionTracker::new();
        let huge = Audio {
            rate: 192_000,
            level: i64::MAX,
            ..packet(0)
        };
        tracker.arrived(&huge, 0);
        tracker.arrived(&Audio { index: 960, ..huge }, 20_000_000);
        assert_eq!(tracker.due(20_000_000), Some(request(240, 720)));
    }
}
