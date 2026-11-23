// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Simulated packet stream generator between a sender and receiver.

use crate::assumptions::OneWayAssumptions;
use crate::clock::{Oscillator, OscillatorModel};
use crate::link::Link;
use crate::random::Generator;
use crate::{TrueTime, seconds_to_nanos};

/// One packet, as its two ends stamp it, with what a test may know besides.
#[derive(Clone, Copy, Debug)]
pub struct Packet {
    /// The packet's number, from 0.
    pub number: u64,
    /// The sender's clock when the packet left, in nanoseconds.
    pub sent: i64,
    /// The receiver's clock when it arrived, in nanoseconds.
    pub received: i64,
    /// What `received - sent` would have been had the packet met no excess
    /// delay, in nanoseconds: the relation that an estimator is after.
    pub undelayed: f64,
    /// The true time at which the packet left.
    pub left: TrueTime,
}

/// A sender, a receiver with clocks of their own, and the link between them.
#[derive(Clone, Debug)]
pub struct OneWay {
    sender: Oscillator,
    receiver: Oscillator,
    /// A second copy of the receiver's oscillator. An oscillator is read at
    /// times that do not go back, and a late packet is followed by questions
    /// about earlier times; the copy answers those.
    receiver_earliest: Oscillator,
    link: Link,
    minimum: f64,
    period: i64,
    number: u64,
}

impl OneWay {
    /// A sender and a receiver under `assumptions`. The two clocks start far
    /// apart and run at rates tens of parts per million apart.
    #[must_use]
    pub fn new(assumptions: &OneWayAssumptions, generator: &Generator) -> OneWay {
        let walk = assumptions.frequency_walk;
        let receiver = Oscillator::new(
            OscillatorModel::from_walk_rate(-7.0, -18e-6, walk),
            generator.fork(2),
        );
        OneWay {
            sender: Oscillator::new(
                OscillatorModel::from_walk_rate(12.0, 31e-6, walk),
                generator.fork(1),
            ),
            receiver_earliest: receiver.clone(),
            receiver,
            link: Link::new(assumptions.link, generator.fork(3)),
            minimum: assumptions.link.minimum,
            period: seconds_to_nanos(1.0 / assumptions.packet_rate),
            number: 0,
        }
    }

    /// Changes the sender's fractional frequency by `change` from the next packet on.
    pub fn step_sender_frequency(&mut self, change: f64) {
        let now = self.next_departure();
        self.sender.step_frequency(now, change);
    }

    fn next_departure(&self) -> TrueTime {
        let number = i64::try_from(self.number).unwrap_or(i64::MAX);
        TrueTime(number.saturating_mul(self.period))
    }

    /// Sends the next packet.
    pub fn send(&mut self) -> Packet {
        let left = self.next_departure();
        let sender_offset = self.sender.offset(left);
        let sent = self.sender.read(left);
        // The receiver's clock at the earliest possible arrival gives the
        // relation without excess delay; it is read before the real arrival.
        let earliest = left.plus_seconds(self.minimum);
        let undelayed =
            (self.minimum + self.receiver_earliest.offset(earliest) - sender_offset) * 1e9;
        let arrival = self.link.arrival(left);
        let received = self.receiver.read(arrival);
        let packet = Packet {
            number: self.number,
            sent,
            received,
            undelayed,
            left,
        };
        self.number += 1;
        packet
    }
}

#[cfg(test)]
mod tests {
    use super::OneWay;
    use crate::assumptions::WIRED_CALM;
    use crate::random::Generator;

    #[test]
    fn no_packet_shows_less_than_the_undelayed_relation() {
        let mut path = OneWay::new(&WIRED_CALM, &Generator::new(9));
        let mut closest = f64::MAX;
        for _ in 0..20_000 {
            let packet = path.send();
            #[allow(clippy::cast_precision_loss)]
            let excess = (packet.received - packet.sent) as f64 - packet.undelayed;
            // Stamps are whole nanoseconds, so allow one for rounding.
            assert!(excess > -1.5, "a packet arrived early by {excess} ns");
            closest = closest.min(excess);
        }
        assert!(
            closest < 100.0,
            "no packet came near the undelayed relation: {closest} ns"
        );
    }
}
