// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Which frames of a stream a receiver holds.
//!
//! A receiver keeps the samples of a stretch of the stream in a ring, each
//! frame at the place its index gives it. This module keeps the other half of
//! that buffer: one bit for each index of the stretch, set when the frame has
//! arrived. Presence is a property of each index by itself, so the order in
//! which packets arrive, and whether one arrives twice, makes no difference.

/// What became of the frames of one packet.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Marked {
    /// Frames that are now held and were not before.
    pub stored: u32,
    /// Frames that were held already.
    pub duplicate: u32,
    /// Frames before the stretch: their time has passed.
    pub late: u32,
    /// Frames beyond the stretch: there is no room for them yet.
    pub early: u32,
}

/// One bit for each of `64 * N` consecutive indices, from `base` on.
///
/// The bit of an index is at a place that depends on the index alone, so
/// moving the stretch forward moves no bits.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub struct Presence<const N: usize> {
    words: [u64; N],
    base: u64,
}

impl<const N: usize> Default for Presence<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Presence<N> {
    /// A stretch that starts at index 0 and holds nothing.
    #[must_use]
    pub fn new() -> Self {
        Presence {
            words: [0; N],
            base: 0,
        }
    }

    /// The first index of the stretch.
    #[must_use]
    pub fn base(&self) -> u64 {
        self.base
    }

    /// The number of indices in the stretch.
    #[must_use]
    pub fn width(&self) -> u64 {
        // An array has fewer than 2^58 places of eight bytes, so no wrapping.
        (N as u64).wrapping_mul(64)
    }

    /// Whether `index` lies in the stretch.
    fn covers(&self, index: u64) -> bool {
        index >= self.base && index.wrapping_sub(self.base) < self.width()
    }

    /// The word that holds the bit of `index`, and the bit's mask in it.
    /// `None` when there are no words.
    fn place(index: u64) -> Option<(usize, u64)> {
        let Some(word) = (index / 64).checked_rem(N as u64) else {
            return None;
        };
        // The remainder is below 64, and `word` is below the length of an array.
        #[allow(clippy::cast_possible_truncation)]
        let (word, bit) = (word as usize, (index % 64) as u32);
        Some((word, 1u64.wrapping_shl(bit)))
    }

    /// Whether the frame at `index` is held.
    #[must_use]
    pub fn held(&self, index: u64) -> bool {
        if !self.covers(index) {
            return false;
        }
        let Some((word, mask)) = Self::place(index) else {
            return false;
        };
        match self.words.get(word) {
            Some(bits) => *bits & mask != 0,
            None => false,
        }
    }

    /// Sets or clears the bit of `index`, and returns whether it was set.
    fn put(&mut self, index: u64, held: bool) -> bool {
        let Some((word, mask)) = Self::place(index) else {
            return false;
        };
        match self.words.get_mut(word) {
            Some(bits) => {
                let was = *bits & mask != 0;
                *bits = if held { *bits | mask } else { *bits & !mask };
                was
            }
            None => false,
        }
    }

    /// Records the arrival of `frames` frames from index `first` on, and
    /// says what became of them.
    pub fn mark(&mut self, first: u64, frames: u32) -> Marked {
        let mut marked = Marked {
            stored: 0,
            duplicate: 0,
            late: 0,
            early: 0,
        };
        let mut done = 0u32;
        while done < frames {
            // Past the largest index there is no frame; such a packet is
            // counted as beyond the stretch.
            let index = first.checked_add(done as u64);
            match index {
                Some(index) if self.covers(index) => {
                    if self.put(index, true) {
                        marked.duplicate = marked.duplicate.saturating_add(1);
                    } else {
                        marked.stored = marked.stored.saturating_add(1);
                    }
                }
                Some(index) if index < self.base => {
                    marked.late = marked.late.saturating_add(1);
                }
                _ => marked.early = marked.early.saturating_add(1),
            }
            done = done.saturating_add(1);
        }
        marked
    }

    /// Moves the start of the stretch forward to `to`, and forgets the
    /// frames before it. A `to` that is not ahead of the start does nothing.
    pub fn advance(&mut self, to: u64) {
        if to <= self.base {
            return;
        }
        if to.wrapping_sub(self.base) >= self.width() {
            // Everything held is behind the new start.
            let mut word = 0usize;
            while word < N {
                if let Some(bits) = self.words.get_mut(word) {
                    *bits = 0;
                }
                word = word.saturating_add(1);
            }
        } else {
            let mut index = self.base;
            while index < to {
                self.put(index, false);
                index = index.saturating_add(1);
            }
        }
        self.base = to;
    }

    /// The number of frames held without a break from index `from` on, up to
    /// `limit`.
    #[must_use]
    pub fn run(&self, from: u64, limit: u32) -> u32 {
        let mut count = 0u32;
        while count < limit {
            let held = match from.checked_add(count as u64) {
                Some(index) => self.held(index),
                None => false,
            };
            if !held {
                break;
            }
            count = count.saturating_add(1);
        }
        count
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{Marked, Presence};

    #[test]
    fn a_new_stretch_holds_nothing() {
        let presence = Presence::<4>::new();
        assert_eq!((presence.base(), presence.width()), (0, 256));
        assert!(!presence.held(0));
        assert_eq!(presence.run(0, 10), 0);
    }

    #[test]
    fn marked_frames_are_held_and_counted_once() {
        let mut presence = Presence::<4>::new();
        assert_eq!(
            presence.mark(10, 5),
            Marked {
                stored: 5,
                ..Marked::default()
            }
        );
        assert!(presence.held(10) && presence.held(14));
        assert!(!presence.held(9) && !presence.held(15));
        // The same packet again, and one that overlaps it.
        assert_eq!(
            presence.mark(10, 5),
            Marked {
                duplicate: 5,
                ..Marked::default()
            }
        );
        assert_eq!(
            presence.mark(13, 4),
            Marked {
                stored: 2,
                duplicate: 2,
                ..Marked::default()
            }
        );
        assert_eq!(presence.run(10, 100), 7);
    }

    #[test]
    fn frames_outside_the_stretch_are_told_apart() {
        let mut presence = Presence::<1>::new();
        presence.advance(100);
        // The stretch is 100..164: three frames before it, two in it, one beyond.
        assert_eq!(
            presence.mark(97, 5),
            Marked {
                stored: 2,
                late: 3,
                ..Marked::default()
            }
        );
        assert_eq!(
            presence.mark(163, 2),
            Marked {
                stored: 1,
                early: 1,
                ..Marked::default()
            }
        );
        assert_eq!(
            presence.mark(u64::MAX, 2),
            Marked {
                early: 2,
                ..Marked::default()
            }
        );
    }

    #[test]
    fn advancing_forgets_what_is_behind_and_keeps_the_rest() {
        let mut presence = Presence::<2>::new();
        presence.mark(0, 100);
        presence.advance(40);
        assert_eq!(presence.base(), 40);
        assert!(!presence.held(39) && presence.held(40) && presence.held(99));
        // The place of index 0 is the place of index 128, which must be free again.
        assert!(!presence.held(128));
        assert_eq!(
            presence.mark(128, 1),
            Marked {
                stored: 1,
                ..Marked::default()
            }
        );
        // Backwards does nothing.
        presence.advance(10);
        assert_eq!(presence.base(), 40);
    }

    #[test]
    fn advancing_past_everything_empties_the_stretch() {
        let mut presence = Presence::<2>::new();
        presence.mark(5, 100);
        presence.advance(5_000);
        assert_eq!(presence.base(), 5_000);
        assert_eq!(presence.run(5_000, 128), 0);
        assert_eq!(
            presence.mark(5_000, 128),
            Marked {
                stored: 128,
                ..Marked::default()
            }
        );
    }

    #[test]
    fn a_stretch_without_words_holds_nothing_and_never_fails() {
        let mut presence = Presence::<0>::new();
        assert_eq!(
            presence.mark(0, 3),
            Marked {
                early: 3,
                ..Marked::default()
            }
        );
        presence.advance(10);
        assert!(!presence.held(10));
    }

    /// Against a plain set of indices: after any sequence of packets and
    /// advances, exactly the indices of the set that lie in the stretch are
    /// held, and every packet's counts are what the set gives.
    #[test]
    fn it_agrees_with_a_set_of_indices() {
        let mut state = 0x2545_f491_4f6c_dd1du64;
        let mut draw = |bound: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) % bound
        };
        let mut presence = Presence::<3>::new();
        let mut set = BTreeSet::new();
        let mut base = 0u64;
        for _ in 0..3_000 {
            if draw(4) == 0 {
                let to = base + draw(120);
                presence.advance(to);
                base = base.max(to);
                set.retain(|&index| index >= base);
            } else {
                let first = (base + draw(260)).saturating_sub(30);
                let frames = u32::try_from(draw(40)).unwrap_or(0);
                let mut expected = Marked::default();
                for index in first..first + u64::from(frames) {
                    if index < base {
                        expected.late += 1;
                    } else if index >= base + 192 {
                        expected.early += 1;
                    } else if set.insert(index) {
                        expected.stored += 1;
                    } else {
                        expected.duplicate += 1;
                    }
                }
                assert_eq!(presence.mark(first, frames), expected);
            }
            for index in base.saturating_sub(5)..base + 200 {
                assert_eq!(
                    presence.held(index),
                    set.contains(&index),
                    "index {index}, base {base}"
                );
            }
        }
    }
}
