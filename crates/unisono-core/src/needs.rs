// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The latency that the frames of a stream needed at a receiver, by stretch
//! of the index.
//!
//! A frame needs the latency at which it would have been there in time: from
//! its capture to its arrival, on the sender's clock, and the time that the
//! receiver needs it before it leaves the device. The level, the latency
//! that every receiver holds, has to be at least that for the frame to be
//! played. The index is cut into stretches of a set number of frames, the
//! same for every receiver of a stream, and of each stretch the largest need
//! is kept, for the last `S` stretches. The sender takes the largest over its
//! receivers for each stretch and chooses the level from that.
//!
//! A stretch older than the kept ones is left out, unless it is older by far,
//! by `2 S` stretches or more before the newest: then the index has started
//! again, and what was kept is dropped. So whatever it holds, the record
//! follows a stream again from the first stretch that is not among the `S`
//! just passed.

use crate::packet::{RECENT, Recent, UNKNOWN_NEED};

/// The largest need of one stretch.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
struct Place {
    /// Whether the place holds a need.
    held: bool,
    /// The stretch it belongs to.
    stretch: u64,
    /// The largest need of a frame of that stretch, in nanoseconds.
    need: i64,
}

/// The largest needs of the last `S` stretches.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Needs<const S: usize> {
    /// The stretch of place `i` is `i` more than a multiple of `S`.
    places: [Place; S],
    /// The newest stretch that a need was taken in for.
    newest: u64,
}

impl<const S: usize> Default for Needs<S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const S: usize> Needs<S> {
    /// No needs yet.
    #[must_use]
    pub fn new() -> Self {
        Needs {
            places: [Place {
                held: false,
                stretch: 0,
                need: 0,
            }; S],
            newest: 0,
        }
    }

    /// Drops every need.
    pub fn clear(&mut self) {
        let mut place = 0usize;
        while place < S {
            if let Some(slot) = self.places.get_mut(place) {
                slot.held = false;
            }
            place = place.saturating_add(1);
        }
    }

    /// Whether any place holds a need.
    fn held_any(&self) -> bool {
        let mut place = 0usize;
        while place < S {
            if let Some(slot) = self.places.get(place)
                && slot.held
            {
                return true;
            }
            place = place.saturating_add(1);
        }
        false
    }

    /// Whether `stretch` is among the kept ones or after them: not older than
    /// the newest by `S` or more.
    fn kept(&self, stretch: u64) -> bool {
        (stretch as u128).wrapping_add(S as u128) > self.newest as u128
    }

    /// Takes in that a frame of `stretch` needed `need` nanoseconds.
    pub fn observe(&mut self, stretch: u64, need: i64) {
        let far =
            (stretch as u128).wrapping_add((S as u128).wrapping_mul(2)) <= self.newest as u128;
        if !self.held_any() || far {
            self.clear();
            self.newest = stretch;
        } else if !self.kept(stretch) {
            return;
        } else if stretch > self.newest {
            self.newest = stretch;
        }
        self.put(stretch, need);
    }

    /// Takes `need` into the place of `stretch`.
    fn put(&mut self, stretch: u64, need: i64) {
        // The place is below `S`, so it is a `usize`.
        let Some(place) = stretch.checked_rem(S as u64) else {
            return;
        };
        #[allow(clippy::cast_possible_truncation)]
        let Some(slot) = self.places.get_mut(place as usize) else {
            return;
        };
        if slot.held && slot.stretch == stretch {
            if need > slot.need {
                slot.need = need;
            }
        } else {
            *slot = Place {
                held: true,
                stretch,
                need,
            };
        }
    }

    /// The newest stretch that a need was taken in for, if one was.
    #[must_use]
    pub fn newest(&self) -> Option<u64> {
        if self.held_any() {
            Some(self.newest)
        } else {
            None
        }
    }

    /// The largest need of `stretch`, if it is kept.
    #[must_use]
    pub fn get(&self, stretch: u64) -> Option<i64> {
        if !self.kept(stretch) || stretch > self.newest {
            return None;
        }
        let Some(place) = stretch.checked_rem(S as u64) else {
            return None;
        };
        #[allow(clippy::cast_possible_truncation)]
        let Some(slot) = self.places.get(place as usize) else {
            return None;
        };
        if slot.held && slot.stretch == stretch {
            Some(slot.need)
        } else {
            None
        }
    }

    /// The largest needs of the newest stretches, newest first, as a report
    /// carries them: at most [`RECENT`] stretches, and none before stretch 0.
    #[must_use]
    pub fn recent(&self) -> Recent {
        let mut recent = Recent::NONE;
        if !self.held_any() {
            return recent;
        }
        recent.newest = self.newest;
        let mut back = 0usize;
        while back < RECENT && back < S && (back as u64) <= self.newest {
            let stretch = self.newest.wrapping_sub(back as u64);
            if let Some(slot) = recent.needs.get_mut(back) {
                *slot = match self.get(stretch) {
                    Some(need) => microseconds(need),
                    None => UNKNOWN_NEED,
                };
            }
            back = back.saturating_add(1);
            // `back` is at most `RECENT`, which fits a byte.
            #[allow(clippy::cast_possible_truncation)]
            {
                recent.count = back as u8;
            }
        }
        recent
    }
}

/// `need` nanoseconds in whole microseconds, rounded up, within the range of
/// a known need.
fn microseconds(need: i64) -> i32 {
    // Division truncates towards zero, which rounds a negative need up.
    let Some(whole) = need.checked_div(1000) else {
        return UNKNOWN_NEED.saturating_add(1);
    };
    // `whole` times 1000 is no further from zero than `need`: no wrapping.
    let rest = need.wrapping_sub(whole.wrapping_mul(1000));
    let up = if rest > 0 {
        whole.saturating_add(1)
    } else {
        whole
    };
    if up > i32::MAX as i64 {
        i32::MAX
    } else if up <= UNKNOWN_NEED as i64 {
        UNKNOWN_NEED.saturating_add(1)
    } else {
        // Within the range of `i32`, as just checked.
        #[allow(clippy::cast_possible_truncation)]
        let small = up as i32;
        small
    }
}

#[cfg(test)]
mod tests {
    use super::Needs;
    use crate::packet::{RECENT, Recent, UNKNOWN_NEED};

    #[test]
    fn each_stretch_keeps_its_largest_need() {
        let mut needs = Needs::<4>::new();
        assert_eq!(needs.newest(), None);
        needs.observe(10, 5);
        needs.observe(10, 9);
        needs.observe(10, 7);
        needs.observe(11, 3);
        assert_eq!(
            (needs.get(10), needs.get(11), needs.newest()),
            (Some(9), Some(3), Some(11))
        );
        // A stretch that was not seen has no need.
        needs.observe(13, 1);
        assert_eq!(needs.get(12), None);
    }

    #[test]
    fn old_stretches_are_forgotten_and_a_new_start_drops_all() {
        let mut needs = Needs::<4>::new();
        for stretch in 0..10 {
            needs.observe(stretch, 100 + i64::try_from(stretch).unwrap_or(0));
        }
        // Stretches 6 to 9 are kept.
        assert_eq!((needs.get(5), needs.get(6)), (None, Some(106)));
        // A stretch just passed is left out.
        needs.observe(4, 1_000);
        assert_eq!(needs.get(4), None);
        // The index started again.
        needs.observe(0, 50);
        assert_eq!(
            (needs.newest(), needs.get(0), needs.get(9)),
            (Some(0), Some(50), None)
        );
    }

    #[test]
    fn the_newest_stretches_go_into_a_report_in_microseconds() {
        let mut needs = Needs::<16>::new();
        assert_eq!(needs.recent(), Recent::NONE);
        needs.observe(2, 1_500);
        needs.observe(4, -1_500);
        needs.observe(5, 3_000_000_000_000);
        let recent = needs.recent();
        assert_eq!((recent.newest, recent.count), (5, 6));
        assert_eq!(
            recent.needs[..6],
            [i32::MAX, -1, UNKNOWN_NEED, 2, UNKNOWN_NEED, UNKNOWN_NEED]
        );
        for stretch in 6..40 {
            needs.observe(stretch, 1_000);
        }
        assert_eq!(
            (needs.recent().newest, needs.recent().count),
            (39, u8::try_from(RECENT).unwrap())
        );
    }

    #[test]
    fn stretches_at_u64_max_are_kept_without_saturation_wrap() {
        let mut needs = Needs::<4>::new();
        needs.observe(u64::MAX, 100);
        assert_eq!(needs.get(u64::MAX), Some(100));
        needs.observe(u64::MAX, 50);
        assert_eq!(needs.get(u64::MAX), Some(100));
        assert_eq!(needs.recent().newest, u64::MAX);
        assert_eq!(needs.recent().needs[0], 1);
    }
}
