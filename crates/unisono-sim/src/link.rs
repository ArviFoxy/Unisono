// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Simulated links in one direction.
//!
//! A packet's delay is the link's smallest delay plus an excess that is never
//! negative. Most packets pass with a small excess; some meet a queue and a
//! larger one. Now and then the link pauses: nothing arrives until the pause
//! ends, and then everything held back arrives at once.

use crate::TrueTime;
use crate::random::Generator;

/// What a link is like. Durations are in seconds.
#[derive(Clone, Copy, Debug)]
pub struct LinkModel {
    /// The smallest delay of the path.
    pub minimum: f64,
    /// Mean excess of a packet that meets no queue.
    pub clear_excess: f64,
    /// Probability that a packet meets a queue.
    pub queued: f64,
    /// Mean excess of a packet that meets a queue.
    pub queued_excess: f64,
    /// Pauses per second.
    pub pause_rate: f64,
    /// Mean length of a pause.
    pub pause_length: f64,
}

/// A simulated link in one direction.
///
/// Packets are sent at true times that do not go backwards, and arrive in the
/// order they were sent.
#[derive(Clone, Debug)]
pub struct Link {
    model: LinkModel,
    generator: Generator,
    last_arrival: TrueTime,
    next_pause: TrueTime,
    paused_until: TrueTime,
}

impl Link {
    /// A link that follows `model`, drawing its delays from `generator`.
    #[must_use]
    pub fn new(model: LinkModel, mut generator: Generator) -> Link {
        let next_pause = Link::draw_pause_start(&model, &mut generator, TrueTime::ZERO);
        Link {
            model,
            generator,
            last_arrival: TrueTime::ZERO,
            next_pause,
            paused_until: TrueTime::ZERO,
        }
    }

    fn draw_pause_start(model: &LinkModel, generator: &mut Generator, after: TrueTime) -> TrueTime {
        if model.pause_rate > 0.0 {
            after.plus_seconds(generator.exponential(1.0 / model.pause_rate))
        } else {
            TrueTime(i64::MAX)
        }
    }

    /// The true time at which a packet sent at `sent` arrives.
    pub fn arrival(&mut self, sent: TrueTime) -> TrueTime {
        while self.next_pause <= sent {
            let length = self.generator.exponential(self.model.pause_length);
            self.paused_until = self.paused_until.max(self.next_pause.plus_seconds(length));
            self.next_pause =
                Link::draw_pause_start(&self.model, &mut self.generator, self.next_pause);
        }
        let excess = if self.generator.chance(self.model.queued) {
            self.generator.exponential(self.model.queued_excess)
        } else {
            self.generator.exponential(self.model.clear_excess)
        };
        let unhindered = sent.plus_seconds(self.model.minimum + excess);
        let arrival = unhindered.max(self.paused_until).max(self.last_arrival);
        self.last_arrival = arrival;
        arrival
    }
}

#[cfg(test)]
mod tests {
    use super::{Link, LinkModel};
    use crate::TrueTime;
    use crate::random::Generator;

    const MODEL: LinkModel = LinkModel {
        minimum: 100e-6,
        clear_excess: 5e-6,
        queued: 0.1,
        queued_excess: 200e-6,
        pause_rate: 0.0,
        pause_length: 0.0,
    };

    #[test]
    fn no_packet_is_faster_than_the_smallest_delay_and_order_is_kept() {
        let mut link = Link::new(MODEL, Generator::new(5));
        let mut previous = TrueTime::ZERO;
        for k in 0..10_000 {
            let sent = TrueTime(k * 1_000_000);
            let arrival = link.arrival(sent);
            assert!(arrival.0 - sent.0 >= 100_000, "delay below the minimum");
            assert!(arrival >= previous, "arrivals out of order");
            previous = arrival;
        }
    }

    /// The mean excess is 0.9 * 5 us + 0.1 * 200 us = 24.5 us; over 100,000
    /// packets sent far enough apart not to queue behind each other, the
    /// sample mean is within 1 us of that.
    #[test]
    fn the_mean_excess_is_the_mixture_of_the_two_kinds() {
        let mut link = Link::new(MODEL, Generator::new(6));
        let n = 100_000;
        let total: i64 = (0..n)
            .map(|k| link.arrival(TrueTime(k * 10_000_000)).0 - k * 10_000_000 - 100_000)
            .sum();
        #[allow(clippy::cast_precision_loss)]
        let mean = total as f64 / n as f64 * 1e-9;
        assert!((mean - 24.5e-6).abs() < 1e-6, "mean excess {mean}");
    }

    #[test]
    fn a_pause_holds_packets_back_and_releases_them_together() {
        let model = LinkModel {
            pause_rate: 1.0,
            pause_length: 0.05,
            ..MODEL
        };
        let mut link = Link::new(model, Generator::new(7));
        // One packet per millisecond for 20 s: about 20 pauses of about 50 ms.
        let arrivals: Vec<(i64, i64)> = (0..20_000)
            .map(|k| (k * 1_000_000, link.arrival(TrueTime(k * 1_000_000)).0))
            .collect();
        let longest = arrivals
            .iter()
            .map(|(sent, arrival)| arrival - sent)
            .max()
            .unwrap_or(0);
        assert!(
            longest > 20_000_000,
            "no pause was felt: longest delay {longest} ns"
        );
        let together = arrivals
            .windows(2)
            .filter(|pair| pair[0].1 == pair[1].1)
            .count();
        assert!(
            together > 100,
            "held packets did not arrive together: {together}"
        );
    }
}
