// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Ways of protecting a stream against lost packets, held against each
//! other.
//!
//! A sender sends a packet every `period` seconds over a path that loses
//! packets in outages: for a time, nothing that is sent in either direction
//! arrives. A way of protecting the stream gives a packet that was lost a
//! second way to the receiver, and the question for each way is when the
//! frames of each packet are at the receiver, by whichever way comes first.
//! That time, less the time the packet was sent, is what the packet needs of
//! the level, and from the needs of all packets follows what the stream
//! costs at the best level (`evaluate`): latency, gaps and missed frames, as
//! the sender's choice of the level counts them. What a way sends on top of
//! the stream is reported beside it.
//!
//! The model leaves out what no way of protecting can change: a pause that
//! holds packets back and then delivers them delays the repairs as it delays
//! the packets.

use crate::random::Generator;

/// A path in both directions. Durations are in seconds.
#[derive(Clone, Copy, Debug)]
pub struct Path {
    /// The smallest delay in either direction.
    pub minimum: f64,
    /// The mean of the delay above that.
    pub excess: f64,
    /// Outages per second.
    pub outage_rate: f64,
    /// The mean length of an outage.
    pub outage_length: f64,
    /// The probability that a packet sent outside an outage is lost on its
    /// own.
    pub stray: f64,
}

/// The outages of one run of a path, and its delays.
pub struct Run {
    path: Path,
    /// The outages, each from its start to its end, in order, not
    /// overlapping.
    outages: Vec<(f64, f64)>,
    /// Latest simulated time already covered by `outages`.
    horizon: f64,
    /// Last drawn outage arrival time.
    outage_cursor: f64,
    /// Pending outage start already drawn beyond `horizon`.
    next_outage: Option<f64>,
    generator: Generator,
}

impl Run {
    /// A run of `path` of `seconds` seconds.
    ///
    /// Degenerate or non-finite parameters (`seconds` non-finite, `outage_rate`
    /// non-finite or `<= 0.0`, or `outage_length` non-finite or `< 0.0`) are
    /// treated defensively as producing no outages rather than looping.
    #[must_use]
    pub fn new(path: Path, seconds: f64, generator: Generator) -> Run {
        let horizon = if seconds.is_finite() {
            seconds.max(0.0) + 10.0
        } else {
            10.0
        };
        let mut run = Run {
            path,
            outages: Vec::new(),
            horizon: 0.0,
            outage_cursor: 0.0,
            next_outage: None,
            generator,
        };
        run.extend_outages(horizon);
        run
    }

    /// Generates any outages up to `until`, guarding against non-finite or
    /// extreme parameters that would otherwise fail to advance time.
    fn extend_outages(&mut self, until: f64) {
        if !(until.is_finite()
            && self.path.outage_rate.is_finite()
            && self.path.outage_rate > 0.0
            && self.path.outage_length.is_finite()
            && self.path.outage_length >= 0.0)
        {
            if until.is_finite() {
                self.horizon = self.horizon.max(until);
            }
            return;
        }
        let mean_gap = 1.0 / self.path.outage_rate;
        if !(mean_gap.is_finite() && mean_gap > 0.0) {
            self.horizon = self.horizon.max(until);
            return;
        }
        loop {
            let start = if let Some(start) = self.next_outage {
                start
            } else {
                let step = self.generator.exponential(mean_gap);
                let next = self.outage_cursor + step;
                if !(next.is_finite() && next > self.outage_cursor) {
                    break;
                }
                self.outage_cursor = next;
                next
            };
            if start > until {
                self.next_outage = Some(start);
                break;
            }
            self.next_outage = None;
            let end = start + self.generator.exponential(self.path.outage_length);
            match self.outages.last_mut() {
                Some(last) if last.1 >= start => last.1 = last.1.max(end),
                _ => self.outages.push((start, end)),
            }
        }
        self.horizon = self.horizon.max(until);
    }

    /// Whether an outage is on at `time`.
    #[must_use]
    pub fn out(&self, time: f64) -> bool {
        let after = self.outages.partition_point(|outage| outage.0 <= time);
        after
            .checked_sub(1)
            .and_then(|at| self.outages.get(at))
            .is_some_and(|outage| time < outage.1)
    }

    /// When a packet sent at `sent` arrives, if it does.
    pub fn deliver(&mut self, sent: f64) -> Option<f64> {
        if sent.is_finite() && sent > self.horizon {
            self.extend_outages(sent + 10.0);
        }
        let delay = self.path.minimum + self.generator.exponential(self.path.excess);
        if self.out(sent) || self.generator.chance(self.path.stray) {
            None
        } else {
            Some(sent + delay)
        }
    }
}

/// A way of protecting a stream.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Scheme {
    /// Nothing: a packet that is lost is missing.
    None,
    /// Every packet is sent again `delay` seconds later.
    Copy {
        /// How long after the packet its copy is sent.
        delay: f64,
    },
    /// After every `data` packets, `parity` packets from which any `parity`
    /// of the block's packets that are lost can be worked out, sent `delay`
    /// seconds after the last packet of the block. With one parity packet
    /// this is the sum of the block's packets; with more, a Reed-Solomon
    /// code.
    Block {
        /// Packets of the stream in a block.
        data: usize,
        /// Packets added to a block.
        parity: usize,
        /// How long after the block the added packets are sent.
        delay: f64,
    },
    /// A code for bursts: with every packet travels as much again as
    /// `burst / wait` of a packet. Requires `0 < burst <= wait`; a run of up
    /// to `burst` lost packets is repaired when it is preceded by a guard
    /// space of `wait` received packets and every packet needed up through
    /// `wait` places after the burst arrives, completing each lost packet
    /// when the packet `wait` places after it arrives. No code repairs bursts
    /// of that length within that wait with less added.
    Burst {
        /// The longest run of lost packets that is repaired.
        burst: usize,
        /// How many packets after a lost one its repair is complete (and the
        /// required guard space before a burst).
        wait: usize,
    },
    /// The receiver asks for a packet that it finds missing when a later
    /// one arrives, and asks again every `again` seconds until it has it or
    /// `patience` seconds have passed; the sender sends the packet again
    /// when it is asked.
    Request {
        /// How long the receiver waits before it asks again.
        again: f64,
        /// How long it goes on asking.
        patience: f64,
        /// The probability that a request is lost on its own, besides what
        /// the path loses: a way back that is worse than the way there.
        unheard: f64,
    },
}

/// What a run of a scheme gave.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// For each packet, how long after it was sent its frames were at the
    /// receiver; infinite for a packet that never was.
    pub needs: Vec<f64>,
    /// How many packets' worth was sent on top of the stream, for each
    /// packet of the stream.
    pub added: f64,
}

/// Runs `scheme` over `run` for `packets` packets sent `period` apart.
///
/// Degenerate scheme parameters (`Block { data: 0, .. }`, `Burst` with
/// `burst == 0`, `wait == 0`, or `burst > wait`, or `Request` with negative
/// or non-finite `patience`) apply no repair rather than panicking or looping.
// Counts of packets are far below 2^52.
#[allow(clippy::cast_precision_loss)]
#[must_use]
pub fn simulate(scheme: Scheme, run: &mut Run, packets: usize, period: f64) -> Outcome {
    let sent = |index: usize| index as f64 * period;
    let arrivals: Vec<Option<f64>> = (0..packets).map(|i| run.deliver(sent(i))).collect();
    let direct = |index: usize| arrivals.get(index).copied().flatten();
    let mut needs: Vec<f64> = (0..packets)
        .map(|i| direct(i).map_or(f64::INFINITY, |arrival| arrival - sent(i)))
        .collect();
    let mut added = 0.0;
    match scheme {
        Scheme::None => {}
        Scheme::Copy { delay } => {
            for (index, need) in needs.iter_mut().enumerate() {
                if let Some(arrival) = run.deliver(sent(index) + delay) {
                    *need = need.min(arrival - sent(index));
                }
            }
            added = packets as f64;
        }
        Scheme::Block {
            data,
            parity,
            delay,
        } => {
            if let Some(blocks) = packets.checked_div(data) {
                for block in 0..blocks {
                    let first = block * data;
                    let after = sent(first + data - 1) + delay;
                    let mut there: Vec<f64> = (first..first + data).filter_map(direct).collect();
                    there.extend((0..parity).filter_map(|_| run.deliver(after)));
                    added += parity as f64;
                    // Any `data` packets of the block give all of it: at the
                    // time the last of the earliest `data` arrives.
                    there.sort_by(f64::total_cmp);
                    if let Some(&complete) = there.get(data - 1) {
                        for (index, need) in needs.iter_mut().enumerate().skip(first).take(data) {
                            *need = need.min(complete - sent(index));
                        }
                    }
                }
            }
        }
        Scheme::Burst { burst, wait } => {
            if burst > 0 && wait > 0 && burst <= wait {
                let mut index = 0;
                while index < packets {
                    if direct(index).is_some() {
                        index += 1;
                        continue;
                    }
                    // A run of lost packets from `index` on.
                    let mut end = index;
                    while end < packets && direct(end).is_none() {
                        end += 1;
                    }
                    // Repaired when the burst is within `burst`, has a guard
                    // space of `wait` received packets before it, and every
                    // packet needed up through `(end - 1) + wait` arrives.
                    let pre_clear =
                        (index.saturating_sub(wait)..index).all(|i| direct(i).is_some());
                    let post_clear = (end..=end - 1 + wait).all(|i| direct(i).is_some());
                    if end - index <= burst && pre_clear && post_clear {
                        for (lost, need) in needs.iter_mut().enumerate().take(end).skip(index) {
                            let complete = (end..=lost + wait)
                                .filter_map(direct)
                                .fold(f64::NEG_INFINITY, f64::max);
                            if complete.is_finite() {
                                *need = need.min(complete - sent(lost));
                            }
                        }
                    }
                    index = end;
                }
            }
            if wait > 0 {
                added = packets as f64 * burst as f64 / wait as f64;
            }
        }
        Scheme::Request {
            again,
            patience,
            unheard,
        } => {
            added = simulate_request(run, &arrivals, period, again, patience, unheard, &mut needs);
        }
    }
    Outcome {
        needs,
        added: added / packets.max(1) as f64,
    }
}

/// Simulates causal retransmission requests for lost packets in `arrivals`,
/// updating `needs` and returning the total overhead in packets.
#[allow(clippy::cast_precision_loss)]
fn simulate_request(
    run: &mut Run,
    arrivals: &[Option<f64>],
    period: f64,
    again: f64,
    patience: f64,
    unheard: f64,
    needs: &mut [f64],
) -> f64 {
    if !(patience.is_finite() && patience >= 0.0) {
        return 0.0;
    }
    let packets = arrivals.len();
    // The time of the first arrival of a later packet, for each packet: when
    // the receiver can find it missing.
    let mut found = vec![f64::INFINITY; packets];
    let mut earliest = f64::INFINITY;
    for index in (0..packets).rev() {
        found[index] = earliest;
        if let Some(arrival) = arrivals[index] {
            earliest = earliest.min(arrival);
        }
    }
    let mut added = 0.0;
    for index in 0..packets {
        if arrivals[index].is_some() || !found[index].is_finite() {
            continue;
        }
        let mut asked = found[index];
        let mut earliest_repair = f64::INFINITY;
        // Causally keep asking until a repair has actually arrived or patience
        // runs out (do not peek ahead at in-flight replies that have not yet
        // reached the receiver).
        while asked - found[index] <= patience && asked < earliest_repair {
            // The request, and the packet sent again on its arrival.
            added += 0.1;
            let heard = run.deliver(asked);
            if let Some(heard) = heard.filter(|_| !run.generator.chance(unheard)) {
                added += 1.0;
                if let Some(arrival) = run.deliver(heard) {
                    earliest_repair = earliest_repair.min(arrival);
                }
            }
            if !(again.is_finite() && again > 0.0) {
                break;
            }
            let next = asked + again;
            if !(next.is_finite() && next > asked) {
                break;
            }
            asked = next;
        }
        if earliest_repair.is_finite() {
            needs[index] = needs[index].min(earliest_repair - index as f64 * period);
        }
    }
    added
}

/// What a stream costs per second at its best level, and what it is like
/// there.
#[derive(Clone, Copy, Debug)]
pub struct Verdict {
    /// The level at which the cost is least, in seconds.
    pub level: f64,
    /// That cost per second.
    pub cost: f64,
    /// Gaps per second at that level.
    pub gaps: f64,
    /// The fraction of the frames that are missed at that level.
    pub missed: f64,
}

/// The cost per second of a stream whose packets, sent `period` apart, need
/// `needs`, at the level in whole milliseconds up to `highest` seconds that
/// makes it least: `latency` for each second of level, `gap` for each gap,
/// and `missed` for each second of frames missed.
///
/// Degenerate inputs are handled defensively: empty `needs` or non-finite /
/// non-positive `period` return an all-zero [`Verdict`]; `NaN` or negative
/// `highest` returns infinite cost; infinite `highest` evaluates up to the
/// whole millisecond ceiling of the largest finite need.
// Counts of packets are far below 2^52.
#[allow(clippy::cast_precision_loss)]
#[must_use]
pub fn evaluate(
    needs: &[f64],
    period: f64,
    highest: f64,
    latency: f64,
    gap: f64,
    missed: f64,
) -> Verdict {
    if needs.is_empty() || !(period.is_finite() && period > 0.0) {
        return Verdict {
            level: 0.0,
            cost: 0.0,
            gaps: 0.0,
            missed: 0.0,
        };
    }
    let time = needs.len() as f64 * period;
    let mut best = Verdict {
        level: 0.0,
        cost: f64::INFINITY,
        gaps: 0.0,
        missed: 0.0,
    };
    if highest.is_nan() || highest < 0.0 {
        return best;
    }
    let steps = if highest.is_finite() {
        (highest * 1_000.0 + 1e-9).floor()
    } else {
        let largest = needs
            .iter()
            .copied()
            .filter(|need| need.is_finite())
            .fold(0.0_f64, f64::max);
        (largest * 1_000.0).ceil()
    };
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let max_step = steps.clamp(0.0, f64::from(u32::MAX)) as u32;
    // The packets that are late at the level, by their place in the stream:
    // fewer and fewer as the level rises.
    let mut late: Vec<(usize, f64)> = needs.iter().copied().enumerate().collect();
    for step in 0..=max_step {
        let level = f64::from(step) * 0.001;
        late.retain(|&(_, need)| need > level);
        let mut gaps = 0.0;
        let mut before: Option<usize> = None;
        for &(place, _) in &late {
            let continuation = before.is_some_and(|prev| prev + 1 == place);
            if !continuation {
                gaps += 1.0;
            }
            before = Some(place);
        }
        let lost = late.len() as f64;
        let cost = latency * level + (gap * gaps + missed * lost * period) / time;
        if cost < best.cost {
            best = Verdict {
                level,
                cost,
                gaps: gaps / time,
                missed: lost / needs.len() as f64,
            };
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::{Path, Run, Scheme, evaluate, simulate};
    use crate::random::Generator;

    const PATH: Path = Path {
        minimum: 1e-3,
        excess: 0.5e-3,
        outage_rate: 0.5,
        outage_length: 0.02,
        stray: 0.0,
    };

    #[test]
    fn without_protection_what_an_outage_takes_is_missing() {
        let mut run = Run::new(PATH, 100.0, Generator::new(1));
        let outcome = simulate(Scheme::None, &mut run, 20_000, 0.005);
        let lost = outcome
            .needs
            .iter()
            .filter(|need| need.is_infinite())
            .count();
        // Outages take about a hundredth of the time.
        assert!((100..400).contains(&lost), "{lost}");
        assert!(outcome.added <= 0.0);
    }

    #[test]
    fn a_copy_sent_after_the_outage_repairs_it() {
        let mut run = Run::new(PATH, 100.0, Generator::new(2));
        let outcome = simulate(Scheme::Copy { delay: 0.2 }, &mut run, 20_000, 0.005);
        let lost = outcome
            .needs
            .iter()
            .filter(|need| need.is_infinite())
            .count();
        // A copy is lost with its packet only when an outage lasts 200 ms,
        // or another one meets it.
        assert!(lost < 10, "{lost}");
        let verdict = evaluate(&outcome.needs, 0.005, 0.5, 1_000.0, 600.0, 60_000.0);
        assert!(verdict.level > 0.19 && verdict.level < 0.22, "{verdict:?}");
    }

    #[test]
    fn a_request_brings_a_lost_packet_soon_after_the_outage() {
        let mut run = Run::new(PATH, 100.0, Generator::new(3));
        let scheme = Scheme::Request {
            again: 0.01,
            patience: 0.5,
            unheard: 0.0,
        };
        let outcome = simulate(scheme, &mut run, 20_000, 0.005);
        let lost = outcome
            .needs
            .iter()
            .filter(|need| need.is_infinite())
            .count();
        assert!(lost < 10, "{lost}");
        // About one packet in a hundred is sent again.
        assert!(
            outcome.added > 0.003 && outcome.added < 0.03,
            "{}",
            outcome.added
        );
    }

    #[test]
    fn evaluate_counts_gap_at_packet_zero_handles_empty_and_includes_highest_boundary() {
        let empty = evaluate(&[], 0.005, 0.5, 1_000.0, 600.0, 60_000.0);
        assert_eq!(empty.cost, 0.0);
        assert_eq!(empty.gaps, 0.0);
        assert_eq!(empty.missed, 0.0);

        // Packet 0 late alone must count as 1 gap (previously missed because
        // `None == 0usize.checked_sub(1)`).
        let at_zero = evaluate(&[f64::INFINITY, 0.001], 0.005, 0.01, 0.0, 600.0, 0.0);
        assert!(
            (at_zero.gaps - 100.0).abs() < 1e-6,
            "1 gap in 0.01s = 100 gaps/s, got {:?}",
            at_zero.gaps
        );

        // In binary64, `9.0 * 0.001 > 0.009` and `0.057 * 1000.0 < 57.0`, so
        // both boundary steps must still be evaluated and save packets just
        // below the boundary.
        let at_9ms = evaluate(&[0.0085; 20], 0.005, 0.009, 1.0, 10_000.0, 10_000.0);
        assert!(
            (at_9ms.level - 0.009).abs() < 1e-9 && at_9ms.missed == 0.0,
            "expected 9 ms level to be evaluated, got {at_9ms:?}"
        );
        let at_57ms = evaluate(&[0.0565; 20], 0.005, 0.057, 1.0, 10_000.0, 10_000.0);
        assert!(
            (at_57ms.level - 0.057).abs() < 1e-9 && at_57ms.missed == 0.0,
            "expected 57 ms level to be evaluated, got {at_57ms:?}"
        );

        // With `highest = +inf`, the ceiling millisecond covering the largest
        // finite need (8.5 ms -> 9 ms) must be evaluated.
        let unbounded = evaluate(&[0.0085; 20], 0.005, f64::INFINITY, 1.0, 10_000.0, 10_000.0);
        assert!(
            (unbounded.level - 0.009).abs() < 1e-9 && unbounded.missed == 0.0,
            "expected unbounded evaluation to cover 8.5 ms at 9 ms, got {unbounded:?}"
        );
    }

    #[test]
    fn degenerate_parameters_do_not_panic_or_loop_forever() {
        let inf_rate = Path {
            outage_rate: f64::INFINITY,
            ..PATH
        };
        let mut run = Run::new(inf_rate, 1.0, Generator::new(10));
        let block = simulate(
            Scheme::Block {
                data: 0,
                parity: 2,
                delay: 0.01,
            },
            &mut run,
            10,
            0.005,
        );
        assert_eq!(block.needs.len(), 10);

        let mut run = Run::new(PATH, 1.0, Generator::new(11));
        let req = simulate(
            Scheme::Request {
                again: 0.0,
                patience: 1.0,
                unheard: 0.0,
            },
            &mut run,
            50,
            0.005,
        );
        assert_eq!(req.needs.len(), 50);

        let mut run = Run::new(PATH, 1.0, Generator::new(12));
        let bad_burst = simulate(Scheme::Burst { burst: 8, wait: 4 }, &mut run, 50, 0.005);
        assert_eq!(bad_burst.needs.len(), 50);
    }

    #[test]
    fn request_sends_causal_retries_while_rtt_exceeds_retry_interval() {
        // Long RTT (minimum 25 ms each way -> 50 ms RTT) with retry every 10 ms:
        // receiver cannot know the first request succeeded until 50 ms later,
        // so it must emit multiple requests before the first repair arrives.
        let slow_path = Path {
            minimum: 0.025,
            excess: 0.0,
            outage_rate: 0.0,
            outage_length: 0.0,
            stray: 0.05,
        };
        let mut run = Run::new(slow_path, 10.0, Generator::new(7));
        let outcome = simulate(
            Scheme::Request {
                again: 0.01,
                patience: 0.5,
                unheard: 0.0,
            },
            &mut run,
            1_000,
            0.005,
        );
        // Each lost packet causes ~5 requests (0, 10, 20, 30, 40 ms) before
        // the first repair arrives at ~50 ms -> ~5 * 1.1 = 5.5 added per lost
        // packet * 0.05 loss ~= 0.275 (much higher than non-causal ~0.055).
        assert!(
            outcome.added > 0.15,
            "expected causal retries while repair is in flight, added={}",
            outcome.added
        );
    }
}
