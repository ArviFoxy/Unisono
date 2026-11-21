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
    generator: Generator,
}

impl Run {
    /// A run of `path` of `seconds` seconds.
    #[must_use]
    pub fn new(path: Path, seconds: f64, mut generator: Generator) -> Run {
        let mut outages: Vec<(f64, f64)> = Vec::new();
        let mut time = 0.0;
        if path.outage_rate > 0.0 {
            loop {
                time += generator.exponential(1.0 / path.outage_rate);
                // Repairs are sent after the stream ends as well.
                if time > seconds + 10.0 {
                    break;
                }
                let end = time + generator.exponential(path.outage_length);
                match outages.last_mut() {
                    Some(last) if last.1 >= time => last.1 = last.1.max(end),
                    _ => outages.push((time, end)),
                }
            }
        }
        Run {
            path,
            outages,
            generator,
        }
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
    /// `burst / wait` of a packet, and a run of up to `burst` lost packets
    /// is worked out from the `wait` packets that follow its start, each
    /// lost packet when the packet `wait` places after it arrives. No code
    /// repairs bursts of that length within that wait with less added.
    Burst {
        /// The longest run of lost packets that is repaired.
        burst: usize,
        /// How many packets after a lost one its repair is complete.
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
            for block in 0..packets / data.max(1) {
                let first = block * data;
                let after = sent(first + data - 1) + delay;
                let mut there: Vec<f64> = (first..first + data).filter_map(direct).collect();
                there.extend((0..parity).filter_map(|_| run.deliver(after)));
                added += parity as f64;
                // Any `data` packets of the block give all of it: at the
                // time the last of the earliest `data` arrives.
                there.sort_by(f64::total_cmp);
                if let Some(&complete) = there.get(data.saturating_sub(1)) {
                    for (index, need) in needs.iter_mut().enumerate().skip(first).take(data) {
                        *need = need.min(complete - sent(index));
                    }
                }
            }
        }
        Scheme::Burst { burst, wait } => {
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
                // It is repaired if it is short enough and the packets that
                // follow it, up to `wait` after its start, all arrive.
                let clear = (end..=index + wait).all(|i| direct(i).is_some());
                if end - index <= burst && clear {
                    for (lost, need) in needs.iter_mut().enumerate().take(end).skip(index) {
                        if let Some(arrival) = direct(lost + wait) {
                            *need = arrival - sent(lost);
                        }
                    }
                }
                index = end;
            }
            added = packets as f64 * burst as f64 / wait.max(1) as f64;
        }
        Scheme::Request {
            again,
            patience,
            unheard,
        } => {
            // The time of the first arrival of a later packet, for each
            // packet: when the receiver can find it missing.
            let mut found = vec![f64::INFINITY; packets];
            let mut earliest = f64::INFINITY;
            for index in (0..packets).rev() {
                found[index] = earliest;
                if let Some(arrival) = direct(index) {
                    earliest = earliest.min(arrival);
                }
            }
            for index in 0..packets {
                if direct(index).is_some() || !found[index].is_finite() {
                    continue;
                }
                let mut asked = found[index];
                while asked - found[index] <= patience {
                    // The request, and the packet sent again on its arrival.
                    added += 0.1;
                    let heard = run.deliver(asked);
                    if let Some(heard) = heard.filter(|_| !run.generator.chance(unheard)) {
                        added += 1.0;
                        if let Some(arrival) = run.deliver(heard) {
                            needs[index] = arrival - sent(index);
                            break;
                        }
                    }
                    asked += again;
                }
            }
        }
    }
    Outcome {
        needs,
        added: added / packets.max(1) as f64,
    }
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
    let time = needs.len() as f64 * period;
    let mut best = Verdict {
        level: 0.0,
        cost: f64::INFINITY,
        gaps: 0.0,
        missed: 0.0,
    };
    // The packets that are late at the level, by their place in the stream:
    // fewer and fewer as the level rises.
    let mut late: Vec<(usize, f64)> = needs.iter().copied().enumerate().collect();
    let mut step = 0u32;
    loop {
        let level = f64::from(step) * 0.001;
        if level > highest {
            break;
        }
        late.retain(|&(_, need)| need > level);
        let mut gaps = 0.0;
        let mut before = None;
        for &(place, _) in &late {
            if before != place.checked_sub(1) {
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
                missed: lost / needs.len().max(1) as f64,
            };
        }
        step += 1;
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
}
