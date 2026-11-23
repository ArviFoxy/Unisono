// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Integration tests covering sender restart scenarios (same clock vs. new
//! clock, timeline changes) and receiver clock-estimation recovery bounds.

use unisono_core::packet::{Audio, FLAG_STAMPED, Format};
use unisono_core::player::Regulation;
use unisono_core::receiver::{Heard, Receiver, Settings};

/// Frames in a packet, and the time between packets at 48,000 frames a
/// second.
const PACKET: u64 = 240;
const PERIOD: i64 = 5_000_000;
/// How long a packet is under way.
const DELAY: i64 = 300_000;
/// After how long without a frame at or ahead of the playhead a receiver
/// starts anew.
const SILENCE: i64 = 1_000_000_000;
/// For how long the estimate remembers samples.
const SPAN: i64 = 2_000_000_000;
/// The largest error of the estimate that counts as knowing the clock.
const CLOSE: i64 = 1_000;

/// One run of a sender.
#[derive(Clone, Copy)]
struct Run {
    timeline: u64,
    clock: u32,
    /// The index of its first frame.
    first: u64,
    /// The reading of its clock when its first packet leaves.
    start: i64,
    /// What the receiver's clock reads more than the sender's.
    offset: i64,
}

impl Run {
    /// When packet `k` leaves, on the sender's clock.
    fn departure(&self, k: u64) -> i64 {
        self.start + i64::try_from(k).unwrap_or(0) * PERIOD
    }

    /// When packet `k` arrives, on the receiver's clock.
    fn arrival(&self, k: u64) -> i64 {
        self.departure(k) + self.offset + DELAY
    }

    /// The header of packet `k`, which carries when the packet before it
    /// left.
    fn header(&self, k: u64) -> Audio {
        let index = self.first + k * PACKET;
        Audio {
            stream: 1,
            timeline: self.timeline,
            index,
            capture: self.departure(k) - PERIOD,
            drift: 0,
            rate: 48_000,
            frames: 240,
            channels: 2,
            format: Format::Signed24,
            level: 20_000_000,
            level_slope: 0,
            span: 2_000,
            window: 2_400,
            flags: if k == 0 { 0 } else { FLAG_STAMPED },
            protection: 0,
            stamped_index: index.saturating_sub(PACKET),
            stamped_departure: if k == 0 { 0 } else { self.departure(k - 1) },
            clock: self.clock,
        }
    }
}

type Listener = Receiver<64, 64, 8>;

fn receiver() -> Listener {
    Receiver::new(Settings {
        stream: 1,
        identity: 1,
        silence: SILENCE,
        limit: 200_000,
        regulation: Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: 240,
        },
    })
}

/// Hands the packets `from..to` of `run` to the receiver and returns what
/// it said about each.
fn feed(receiver: &mut Listener, run: &Run, from: u64, to: u64) -> Vec<Heard> {
    (from..to)
        .map(|k| receiver.packet(&run.header(k), run.arrival(k)))
        .collect()
}

/// How far the receiver's estimate of the clock of `run` is from the truth
/// when packet `k` has arrived, or `None` when it has no estimate.
fn error(receiver: &Listener, run: &Run, k: u64) -> Option<i64> {
    let line = receiver.clock()?;
    Some(line.eval(run.departure(k)) - (run.offset + DELAY))
}

/// The first run of every case: five seconds from a large index.
fn first_run() -> Run {
    Run {
        timeline: 7,
        clock: 5,
        first: 1_000_000_000,
        start: 50_000_000_000,
        offset: 3_600_000_000_000,
    }
}

/// A receiver that has followed the first run, and when the run's last
/// packet arrived.
fn after_the_first_run() -> (Listener, i64) {
    let run = first_run();
    let mut receiver = receiver();
    feed(&mut receiver, &run, 0, 1_000);
    assert!(error(&receiver, &run, 999).is_some_and(|e| e.abs() < CLOSE));
    (receiver, run.arrival(999))
}

/// A second run that begins one millisecond after the first one's last
/// arrival, on a clock that reads `start` then.
fn second_run(ended: i64, timeline: u64, clock: u32, first: u64, start: i64) -> Run {
    Run {
        timeline,
        clock,
        first,
        start,
        offset: ended + 1_000_000 - DELAY - start,
    }
}

/// The number of packets in `time`.
fn packets_in(time: i64) -> u64 {
    u64::try_from(time / PERIOD).unwrap_or(0)
}

#[test]
fn the_same_timeline_from_index_zero_on_a_clock_that_began_anew() {
    let (mut receiver, ended) = after_the_first_run();
    let run = second_run(ended, 7, 5, 0, 0);
    // The frames are all behind the playhead: after the time of silence the
    // receiver starts anew at them.
    let within = packets_in(SILENCE) + 2;
    let heard = feed(&mut receiver, &run, 0, within);
    assert!(heard.iter().any(|heard| heard.restarted));
    // Two windows of packets later it knows the clock.
    feed(&mut receiver, &run, within, within + 30);
    let found = error(&receiver, &run, within + 29);
    assert!(found.is_some_and(|e| e.abs() < CLOSE), "{found:?}");
}

#[test]
fn the_same_timeline_from_index_zero_on_the_same_clock() {
    let (mut receiver, ended) = after_the_first_run();
    let first = first_run();
    // The clock went on: it reads what it did, a millisecond later.
    let start = first.departure(999) + 1_000_000;
    let run = second_run(ended, 7, 5, 0, start);
    assert_eq!(run.offset, first.offset);
    // The estimate is right all the way through.
    let mut restarted = false;
    for k in 0..packets_in(SILENCE) + 40 {
        restarted |= receiver.packet(&run.header(k), run.arrival(k)).restarted;
        let found = error(&receiver, &run, k);
        assert!(found.is_some_and(|e| e.abs() < CLOSE), "{k}: {found:?}");
    }
    // And the receiver holds frames of the second run.
    assert!(restarted);
    assert_eq!(receiver.timeline(), Some(7));
    assert!(receiver.playhead() < first.first);
}

#[test]
fn the_same_timeline_from_index_zero_on_a_clock_that_reads_a_little_less() {
    let (mut receiver, ended) = after_the_first_run();
    let first = first_run();
    // One second less than at the end of the first run: within the span,
    // where a sample could come from a packet that was overtaken.
    let start = first.departure(999) - 1_000_000_000;
    let run = second_run(ended, 7, 5, 0, start);
    // After the time of silence the receiver starts anew, and after the
    // span the samples of the first run are forgotten.
    let within = packets_in(SILENCE + SPAN) + 40;
    feed(&mut receiver, &run, 0, within);
    let found = error(&receiver, &run, within - 1);
    assert!(found.is_some_and(|e| e.abs() < CLOSE), "{found:?}");
}

#[test]
fn a_later_timeline_on_the_same_clock_keeps_the_estimate() {
    let (mut receiver, ended) = after_the_first_run();
    let first = first_run();
    let start = first.departure(999) + 1_000_000;
    let run = second_run(ended, 8, 5, 0, start);
    let heard = feed(&mut receiver, &run, 0, 2);
    // The second packet of the timeline makes the receiver follow it.
    assert!(heard[0].ignored && heard[1].adopted);
    // It knows the clock at once, and goes on knowing it.
    for k in 2..60 {
        receiver.packet(&run.header(k), run.arrival(k));
        let found = error(&receiver, &run, k);
        assert!(found.is_some_and(|e| e.abs() < CLOSE), "{k}: {found:?}");
    }
}

#[test]
fn a_later_timeline_on_another_clock_learns_it_anew() {
    let (mut receiver, ended) = after_the_first_run();
    let run = second_run(ended, 8, 6, 0, 0);
    let heard = feed(&mut receiver, &run, 0, 2);
    assert!(heard[0].ignored && heard[1].adopted);
    // Nothing of the first run's clock is left.
    assert_eq!(error(&receiver, &run, 1), None);
    feed(&mut receiver, &run, 2, 32);
    let found = error(&receiver, &run, 31);
    assert!(found.is_some_and(|e| e.abs() < CLOSE), "{found:?}");
}

#[test]
fn another_sender_with_the_same_identifiers_is_known_within_the_span() {
    // A second host sends with the timeline and the clock identifier of the
    // first, which a receiver cannot tell apart from the first sender
    // starting again. Its clock reads far more than the first one's.
    let (mut receiver, ended) = after_the_first_run();
    let run = second_run(ended, 7, 5, 0, 900_000_000_000);
    let within = packets_in(SILENCE + SPAN) + 40;
    feed(&mut receiver, &run, 0, within);
    let found = error(&receiver, &run, within - 1);
    assert!(found.is_some_and(|e| e.abs() < CLOSE), "{found:?}");
}
