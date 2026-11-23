// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Fixed-size ring buffer recording recent packet arrival timestamps keyed by
//! sequence or frame index, used to pair deferred TX timestamps with prior RX
//! arrivals.

/// The arrival of one packet.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
struct Arrival {
    /// Whether this place holds an arrival.
    used: bool,
    /// The index of the packet's first frame.
    index: u64,
    /// The receiver's clock when the packet arrived.
    time: i64,
}

/// The arrivals of the last `K` packets.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Arrivals<const K: usize> {
    places: [Arrival; K],
    /// The place that the next arrival is written to.
    next: usize,
}

impl<const K: usize> Default for Arrivals<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const K: usize> Arrivals<K> {
    /// No arrivals.
    #[must_use]
    pub fn new() -> Self {
        Arrivals {
            places: [Arrival {
                used: false,
                index: 0,
                time: 0,
            }; K],
            next: 0,
        }
    }

    /// The arrival at `place`, or an unused one if there is no such place.
    fn at(&self, place: usize) -> Arrival {
        match self.places.get(place) {
            Some(arrival) => *arrival,
            None => Arrival {
                used: false,
                index: 0,
                time: 0,
            },
        }
    }

    /// When the packet whose first frame has `index` arrived, if that is
    /// still kept.
    #[must_use]
    pub fn find(&self, index: u64) -> Option<i64> {
        let mut found = None;
        let mut place = 0usize;
        while place < K {
            let arrival = self.at(place);
            if arrival.used && arrival.index == index {
                found = Some(arrival.time);
                break;
            }
            place = place.saturating_add(1);
        }
        found
    }

    /// Keeps the arrival at `time` of the packet whose first frame has
    /// `index`, in place of the oldest kept arrival. If an arrival of that
    /// packet is kept already, it stays: a copy of a packet arrives after
    /// the packet, and the earlier arrival is the one with less delay.
    pub fn record(&mut self, index: u64, time: i64) {
        if self.find(index).is_some() {
            return;
        }
        if let Some(arrival) = self.places.get_mut(self.next) {
            *arrival = Arrival {
                used: true,
                index,
                time,
            };
        }
        self.next = self.next.saturating_add(1).checked_rem(K).unwrap_or(0);
    }
}

#[cfg(test)]
mod tests {
    use super::Arrivals;

    #[test]
    fn an_arrival_is_found_by_the_index_of_its_packet() {
        let mut arrivals = Arrivals::<4>::new();
        assert_eq!(arrivals.find(0), None);
        arrivals.record(0, 1_000);
        arrivals.record(240, 6_000);
        assert_eq!(arrivals.find(0), Some(1_000));
        assert_eq!(arrivals.find(240), Some(6_000));
        assert_eq!(arrivals.find(480), None);
    }

    #[test]
    fn the_oldest_arrival_makes_room_for_a_new_one() {
        let mut arrivals = Arrivals::<2>::new();
        arrivals.record(10, 1);
        arrivals.record(20, 2);
        arrivals.record(30, 3);
        assert_eq!(arrivals.find(10), None);
        assert_eq!(arrivals.find(20), Some(2));
        assert_eq!(arrivals.find(30), Some(3));
    }

    #[test]
    fn a_copy_of_a_packet_does_not_replace_its_first_arrival() {
        let mut arrivals = Arrivals::<2>::new();
        arrivals.record(10, 1);
        arrivals.record(10, 5);
        assert_eq!(arrivals.find(10), Some(1));
        // The copy took no place either.
        arrivals.record(20, 2);
        assert_eq!(arrivals.find(10), Some(1));
    }

    #[test]
    fn no_places_keep_nothing() {
        let mut arrivals = Arrivals::<0>::new();
        arrivals.record(10, 1);
        assert_eq!(arrivals.find(10), None);
    }

    #[test]
    fn a_wrong_next_place_is_put_right_by_the_next_arrival() {
        let mut arrivals = Arrivals::<2>::new();
        arrivals.next = 77;
        arrivals.record(10, 1);
        assert!(arrivals.next < 2);
        arrivals.record(20, 2);
        assert_eq!(arrivals.find(20), Some(2));
    }
}
