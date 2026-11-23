// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Sliding-window minimum-RTT tracker for legacy report/echo path delay.
//!
//! Each echo pairs a receiver report departure timestamp with the sender
//! arrival timestamp; combining that with the current one-way clock relation
//! yields an RTT estimate ([`round_trip`]) that is re-evaluated on demand as
//! the clock estimate improves.
//!
//! Retains the minimum-RTT echo per bucket over the last `R` fixed-duration
//! windows. Buckets older than `R` windows are ignored; an echo older than
//! `2 * R` windows triggers a reset to recover from receiver clock resets.

use crate::fixed::{div_floor, rem_euclid_wide, saturate};
use crate::relation::Line;

/// One answer: when its report left, on the receiver's clock, and when it
/// arrived, on the sender's.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Answer {
    /// When the report left, on the receiver's clock.
    pub departure: i64,
    /// When it arrived, on the sender's clock.
    pub arrival: i64,
}

/// The time there and back of the report of `answer`, with `forward` the
/// estimate of the receiver's clock minus the sender's from audio packets.
/// The answer says the sender's clock minus the receiver's, plus the time
/// the report took back; `forward` says the receiver's minus the sender's,
/// plus the shortest time from the sender. At the same moment the clocks
/// cancel.
#[must_use]
pub fn round_trip(forward: &Line, answer: Answer) -> i64 {
    // Sums and differences of 64-bit numbers: no wrapping.
    let back = (answer.arrival as i128).wrapping_sub(answer.departure as i128);
    saturate((forward.eval(answer.arrival) as i128).wrapping_add(back))
}

/// The answer kept for one window.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
struct Place {
    /// Whether the place holds an answer.
    held: bool,
    /// The window it belongs to.
    window: i64,
    /// The answer.
    answer: Answer,
}

/// The answers with the shortest times there and back, of the last `R`
/// windows of time.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Answers<const R: usize> {
    /// The window of place `i` is `i` more than a multiple of `R`.
    places: [Place; R],
    /// The newest window that an answer was taken in for.
    newest: i64,
    /// The length of a window, in nanoseconds; at least one.
    length: i64,
}

impl<const R: usize> Answers<R> {
    /// No answers yet, with windows of `length` nanoseconds.
    #[must_use]
    pub fn new(length: i64) -> Self {
        Answers {
            places: [Place {
                held: false,
                window: 0,
                answer: Answer {
                    departure: 0,
                    arrival: 0,
                },
            }; R],
            newest: 0,
            length: if length < 1 { 1 } else { length },
        }
    }

    /// Drops every answer.
    pub fn clear(&mut self) {
        let mut place = 0usize;
        while place < R {
            if let Some(slot) = self.places.get_mut(place) {
                slot.held = false;
            }
            place = place.saturating_add(1);
        }
    }

    /// Takes in `answer`, with `forward` the estimate of the clocks now.
    pub fn observe(&mut self, answer: Answer, forward: &Line) {
        let window = saturate(div_floor(answer.departure as i128, self.length));
        let restart = self.restarts(window);
        if !restart && self.passed(window) {
            return;
        }
        if restart {
            self.clear();
            self.newest = window;
        } else if window > self.newest {
            self.newest = window;
        }
        self.put(window, answer, forward);
    }

    /// Whether an answer of `window` starts anew: nothing is kept, or the
    /// window is older than the newest by `2 R` windows or more.
    fn restarts(&self, window: i64) -> bool {
        // Two counts of windows below 2^64 each: no wrapping.
        let far = (self.newest as i128).wrapping_sub((R as i128).wrapping_mul(2));
        !self.held_any() || (window as i128) <= far
    }

    /// Whether `window` is older than the windows that are kept.
    fn passed(&self, window: i64) -> bool {
        (window as i128) < self.oldest()
    }

    /// The oldest window that is kept with the newest one.
    fn oldest(&self) -> i128 {
        // A 64-bit number and a count below 2^64: no wrapping.
        (self.newest as i128)
            .wrapping_sub(R as i128)
            .wrapping_add(1)
    }

    /// Takes `answer` into the place of `window`, if it went faster there and
    /// back than the one there, as `forward` says.
    fn put(&mut self, window: i64, answer: Answer, forward: &Line) {
        let Some(place) = rem_euclid_wide(window as i128, R) else {
            return;
        };
        let Some(slot) = self.places.get_mut(place) else {
            return;
        };
        let faster = !slot.held
            || slot.window != window
            || round_trip(forward, answer) < round_trip(forward, slot.answer);
        if faster {
            *slot = Place {
                held: true,
                window,
                answer,
            };
        }
    }

    /// Whether any place holds an answer.
    fn held_any(&self) -> bool {
        let mut place = 0usize;
        while place < R {
            if let Some(slot) = self.places.get(place)
                && slot.held
            {
                return true;
            }
            place = place.saturating_add(1);
        }
        false
    }

    /// The shortest time there and back of the answers of the windows that
    /// are kept, as `forward` says now. `None` when none is kept.
    #[must_use]
    pub fn shortest(&self, forward: &Line) -> Option<i64> {
        let oldest = self.oldest();
        let mut shortest: Option<i64> = None;
        let mut place = 0usize;
        while place < R {
            if let Some(slot) = self.places.get(place)
                && slot.held
                && (slot.window as i128) >= oldest
                && slot.window <= self.newest
            {
                let time = round_trip(forward, slot.answer);
                shortest = match shortest {
                    Some(value) if value <= time => Some(value),
                    _ => Some(time),
                };
            }
            place = place.saturating_add(1);
        }
        shortest
    }
}

#[cfg(test)]
mod tests {
    use super::{Answer, Answers};
    use crate::relation::Line;

    /// The receiver's clock equals the sender's: the time there and back of
    /// an answer is its arrival less its departure, plus `forward` at it.
    const FLAT: Line = Line {
        time: 0,
        value: 100,
        rise: 0,
        run: 1,
    };

    fn answer(departure: i64, back: i64) -> Answer {
        Answer {
            departure,
            arrival: departure + back,
        }
    }

    #[test]
    fn the_shortest_of_the_kept_windows_is_given() {
        let mut answers = Answers::<4>::new(10);
        assert_eq!(answers.shortest(&FLAT), None);
        answers.observe(answer(3, 50), &FLAT);
        answers.observe(answer(7, 40), &FLAT);
        answers.observe(answer(15, 45), &FLAT);
        assert_eq!(answers.shortest(&FLAT), Some(140));
        // Windows 0 to 3 are kept; window 4 pushes out window 0.
        answers.observe(answer(25, 60), &FLAT);
        answers.observe(answer(35, 55), &FLAT);
        assert_eq!(answers.shortest(&FLAT), Some(140));
        answers.observe(answer(41, 70), &FLAT);
        assert_eq!(answers.shortest(&FLAT), Some(145));
    }

    #[test]
    fn the_times_are_those_of_the_estimate_as_it_is_now() {
        let mut answers = Answers::<4>::new(10);
        answers.observe(answer(3, 50), &FLAT);
        // A better estimate says the path from the sender is shorter.
        let better = Line { value: 90, ..FLAT };
        assert_eq!(answers.shortest(&better), Some(140));
    }

    #[test]
    fn an_answer_of_a_window_that_has_passed_is_left_out() {
        let mut answers = Answers::<4>::new(10);
        answers.observe(answer(55, 30), &FLAT);
        answers.observe(answer(12, 1), &FLAT);
        assert_eq!(answers.shortest(&FLAT), Some(130));
        answers.observe(answer(31, 2), &FLAT);
        assert_eq!(answers.shortest(&FLAT), Some(102));
    }

    #[test]
    fn a_clock_that_started_again_drops_what_was_kept() {
        let mut answers = Answers::<4>::new(10);
        answers.observe(answer(1_000, 5), &FLAT);
        answers.observe(answer(3, 80), &FLAT);
        assert_eq!(answers.shortest(&FLAT), Some(180));
        let mut wild = Answers::<4>::new(-7);
        wild.observe(answer(i64::MAX - 5, 1), &FLAT);
        wild.observe(answer(i64::MIN, 9), &FLAT);
        assert_eq!(wild.shortest(&FLAT), Some(109));
    }

    #[test]
    fn negative_windows_do_not_collide_for_non_power_of_two_capacity() {
        let mut answers = Answers::<3>::new(10);
        // Window -1 and window 0 are both among the 3 kept windows [-2, 0].
        answers.observe(answer(-5, 10), &FLAT);
        answers.observe(answer(5, 50), &FLAT);
        assert_eq!(answers.shortest(&FLAT), Some(110));
    }
}
