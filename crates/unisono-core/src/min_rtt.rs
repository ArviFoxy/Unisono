// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Deduplicated sliding-window minimum-RTT selector for 4-timestamp clock
//! exchanges.
//!
//! Each completed 4-timestamp exchange `(t1, t2, t3, t4)` yields an exact
//! integer round-trip time `(t4 - t1) - (t3 - t2)`, an offset estimate
//! `((t2 - t1) + (t3 - t4)) / 2` (remote clock minus local clock), and a
//! local-clock midpoint `t1 + (t4 - t1) / 2`.
//!
//! Retaining the last `W` valid exchanges in a non-blocking ring buffer avoids
//! stalling on dropped UDP packets. Every `stride` received exchanges (and on
//! the first valid exchange for immediate startup lock), the selector finds the
//! minimum-RTT exchange in the window, estimates measurement variance online
//! from the median excess RTT above that minimum (clamped above a fixed
//! conservative floor), and emits it at most once by enforcing strictly
//! increasing emitted exchange identifiers.

use crate::fixed::{div_floor, div_floor_wide, rem_euclid_wide, saturate};

/// Length of each running-minimum RTT window, in nanoseconds (8 seconds).
const MIN_RTT_WINDOW_NS: i64 = 8_000_000_000;

/// Number of running-minimum RTT windows kept (8 windows = 56–64 seconds).
const MIN_RTT_WINDOWS: usize = 8;

/// Maximum excess RTT squared into the variance calculation, in nanoseconds
/// (`1 s`), keeping `med * med <= 10^18` well within `i128` and `u64`.
const MAX_EXCESS_NS: i64 = 1_000_000_000;

/// Maximum measurement variance returned, in square nanoseconds (`(1 s)^2`).
const MAX_VAR_NS2: u64 = 1_000_000_000_000_000_000;

/// Default conservative variance floor, in square nanoseconds (`(5 us)^2`).
pub const DEFAULT_VARIANCE_FLOOR_NS2: u64 = 25_000_000;

/// Default initial online variance prior, in square nanoseconds (`(100 us)^2`).
pub const DEFAULT_INITIAL_VARIANCE_NS2: u64 = 10_000_000_000;

/// One completed 4-timestamp NTP-style clock exchange.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Exchange {
    /// Monotonic exchange identifier (e.g., report or peer-probe sequence).
    pub id: u64,
    /// Local clock when the request left (`T1`), in nanoseconds.
    pub t1: i64,
    /// Remote clock when the request arrived (`T2`), in nanoseconds.
    pub t2: i64,
    /// Remote clock when the reply left (`T3`), in nanoseconds.
    pub t3: i64,
    /// Local clock when the reply arrived (`T4`), in nanoseconds.
    pub t4: i64,
}

/// Decoded timing sample of a single valid 4-timestamp exchange.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Sampled {
    /// Exchange identifier.
    pub id: u64,
    /// Local-clock midpoint `t1 + floor((t4 - t1) / 2)`, in nanoseconds.
    pub midpoint_ns: i64,
    /// Estimated offset `remote_clock - local_clock`, in nanoseconds.
    pub offset_ns: i64,
    /// Non-negative round-trip time `(t4 - t1) - (t3 - t2)`, in nanoseconds.
    pub rtt_ns: i64,
}

/// A deduplicated minimum-RTT measurement ready for the Kalman filter.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Measurement {
    /// Exchange identifier of the selected minimum-RTT exchange.
    pub id: u64,
    /// Local-clock midpoint of the selected exchange, in nanoseconds.
    pub midpoint_ns: i64,
    /// Estimated offset `remote_clock - local_clock`, in nanoseconds.
    pub offset_ns: i64,
    /// Round-trip time of the selected exchange, in nanoseconds.
    pub rtt_ns: i64,
    /// Estimated measurement variance of `offset_ns`, in square nanoseconds.
    pub variance_ns2: u64,
}

/// Computes the exact integer midpoint, offset, and round-trip time of a
/// 4-timestamp exchange. Returns `None` if the remote processing time
/// `t3 - t2` or the round-trip time `(t4 - t1) - (t3 - t2)` is negative.
#[must_use]
pub fn ntp_exchange(ex: Exchange) -> Option<Sampled> {
    let leg = (ex.t4 as i128).wrapping_sub(ex.t1 as i128);
    let proc_t = (ex.t3 as i128).wrapping_sub(ex.t2 as i128);
    if proc_t < 0 {
        return None;
    }
    let rtt = leg.wrapping_sub(proc_t);
    if rtt < 0 {
        return None;
    }
    let d1 = (ex.t2 as i128).wrapping_sub(ex.t1 as i128);
    let d2 = (ex.t3 as i128).wrapping_sub(ex.t4 as i128);
    let offset = div_floor_wide(d1.wrapping_add(d2), 2);
    let midpoint = (ex.t1 as i128).wrapping_add(div_floor_wide(leg, 2));
    Some(Sampled {
        id: ex.id,
        midpoint_ns: saturate(midpoint),
        offset_ns: saturate(offset),
        rtt_ns: saturate(rtt),
    })
}

/// One kept exchange inside the sliding window.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
struct Slot {
    used: bool,
    sample: Sampled,
}

impl Slot {
    const EMPTY: Slot = Slot {
        used: false,
        sample: Sampled {
            id: 0,
            midpoint_ns: 0,
            offset_ns: 0,
            rtt_ns: 0,
        },
    };
}

/// One window of the running-minimum RTT tracker.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
struct RttWindow {
    held: bool,
    window: i64,
    rtt_ns: i64,
}

impl RttWindow {
    const EMPTY: RttWindow = RttWindow {
        held: false,
        window: 0,
        rtt_ns: 0,
    };
}

/// Reads `slice[idx]` with default `0`.
fn get_i64(slice: &[i64], idx: usize) -> i64 {
    match slice.get(idx) {
        Some(v) => *v,
        None => 0,
    }
}

/// Writes `val` to `slice[idx]` when in bounds.
fn set_i64(slice: &mut [i64], idx: usize, val: i64) {
    if let Some(dst) = slice.get_mut(idx) {
        *dst = val;
    }
}

/// Clamps an `i128` variance into `[floor, MAX_VAR_NS2]` as `u64`.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn clamp_var(val: i128, floor: u64) -> u64 {
    let clamped_low = if val < floor as i128 {
        floor as i128
    } else {
        val
    };
    let bounded = if clamped_low > MAX_VAR_NS2 as i128 {
        MAX_VAR_NS2 as i128
    } else {
        clamped_low
    };
    bounded as u64
}

/// Non-blocking, deduplicated sliding-window minimum-RTT selector with online
/// measurement-variance estimation and windowed running-minimum path tracking.
#[derive(Clone, Copy)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct SlidingMinRtt<const W: usize> {
    slots: [Slot; W],
    len: usize,
    next: usize,
    stride: usize,
    seen: u64,
    has_emitted: bool,
    last_emitted_id: u64,
    has_ewma: bool,
    ewma_var_ns2: u64,
    initial_var_ns2: u64,
    floor_var_ns2: u64,
    min_windows: [RttWindow; MIN_RTT_WINDOWS],
    newest_window: i64,
    has_min_window: bool,
}

impl<const W: usize> SlidingMinRtt<W> {
    /// Creates a new selector keeping the last `W` valid exchanges, emitting
    /// on the first exchange and every `stride` arrivals thereafter, with the
    /// given initial and floor measurement variances (in square nanoseconds).
    #[must_use]
    pub fn new(stride: usize, initial_var_ns2: u64, floor_var_ns2: u64) -> Self {
        let floor = if floor_var_ns2 == 0 {
            1
        } else if floor_var_ns2 > MAX_VAR_NS2 {
            MAX_VAR_NS2
        } else {
            floor_var_ns2
        };
        let initial = if initial_var_ns2 < floor {
            floor
        } else if initial_var_ns2 > MAX_VAR_NS2 {
            MAX_VAR_NS2
        } else {
            initial_var_ns2
        };
        SlidingMinRtt {
            slots: [Slot::EMPTY; W],
            len: 0,
            next: 0,
            stride: if stride == 0 { 1 } else { stride },
            seen: 0,
            has_emitted: false,
            last_emitted_id: 0,
            has_ewma: false,
            ewma_var_ns2: initial,
            initial_var_ns2: initial,
            floor_var_ns2: floor,
            min_windows: [RttWindow::EMPTY; MIN_RTT_WINDOWS],
            newest_window: 0,
            has_min_window: false,
        }
    }

    /// Resets all kept exchanges and variance state while keeping settings.
    pub fn reset(&mut self) {
        let mut i = 0usize;
        while i < W {
            if let Some(slot) = self.slots.get_mut(i) {
                *slot = Slot::EMPTY;
            }
            i = i.saturating_add(1);
        }
        self.len = 0;
        self.next = 0;
        self.seen = 0;
        self.has_emitted = false;
        self.last_emitted_id = 0;
        self.has_ewma = false;
        self.ewma_var_ns2 = self.initial_var_ns2;
        self.clear_min_windows();
    }

    /// Drops all running-minimum RTT windows.
    fn clear_min_windows(&mut self) {
        let mut i = 0usize;
        while i < MIN_RTT_WINDOWS {
            if let Some(w) = self.min_windows.get_mut(i) {
                *w = RttWindow::EMPTY;
            }
            i = i.saturating_add(1);
        }
        self.newest_window = 0;
        self.has_min_window = false;
    }

    /// Updates the windowed running-minimum RTT tracker with one valid sample.
    fn record_min_rtt(&mut self, midpoint_ns: i64, rtt_ns: i64) {
        let win = saturate(div_floor(midpoint_ns as i128, MIN_RTT_WINDOW_NS));
        let oldest = (self.newest_window as i128)
            .wrapping_sub(MIN_RTT_WINDOWS as i128)
            .wrapping_add(1);
        let far =
            (self.newest_window as i128).wrapping_sub((MIN_RTT_WINDOWS as i128).wrapping_mul(2));
        let restart = !self.has_min_window || (win as i128) <= far;
        if !restart && (win as i128) < oldest {
            return;
        }
        if restart {
            self.clear_min_windows();
            self.newest_window = win;
            self.has_min_window = true;
        } else if win > self.newest_window {
            self.newest_window = win;
        }
        let Some(place) = rem_euclid_wide(win as i128, MIN_RTT_WINDOWS) else {
            return;
        };
        if let Some(slot) = self.min_windows.get_mut(place) {
            let faster = !slot.held || slot.window != win || rtt_ns < slot.rtt_ns;
            if faster {
                *slot = RttWindow {
                    held: true,
                    window: win,
                    rtt_ns,
                };
            }
        }
    }

    /// The shortest RTT observed in the kept running-minimum windows, if any.
    #[must_use]
    pub fn min_rtt_ns(&self) -> Option<i64> {
        if !self.has_min_window {
            return None;
        }
        let oldest = (self.newest_window as i128)
            .wrapping_sub(MIN_RTT_WINDOWS as i128)
            .wrapping_add(1);
        let mut best: Option<i64> = None;
        let mut i = 0usize;
        while i < MIN_RTT_WINDOWS {
            if let Some(slot) = self.min_windows.get(i)
                && slot.held
                && (slot.window as i128) >= oldest
                && slot.window <= self.newest_window
            {
                best = match best {
                    Some(prev) if prev <= slot.rtt_ns => Some(prev),
                    _ => Some(slot.rtt_ns),
                };
            }
            i = i.saturating_add(1);
        }
        best
    }

    /// Causal half-RTT one-way path delay estimate (`min_rtt / 2`), in
    /// nanoseconds, or `0` before any valid exchange arrives.
    #[must_use]
    pub fn path_ns(&self) -> i64 {
        match self.min_rtt_ns() {
            Some(rtt) if rtt > 0 => rtt.wrapping_shr(1),
            _ => 0,
        }
    }

    /// Current smoothed online measurement variance estimate, in square
    /// nanoseconds (always at least `floor_var_ns2`).
    #[must_use]
    pub fn variance_ns2(&self) -> u64 {
        if self.ewma_var_ns2 < self.floor_var_ns2 {
            self.floor_var_ns2
        } else {
            self.ewma_var_ns2
        }
    }

    /// Number of valid exchanges currently kept in the sliding window (`<= W`).
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether no exchanges have been kept yet.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The highest exchange identifier emitted so far, if any.
    #[must_use]
    pub fn last_emitted_id(&self) -> Option<u64> {
        if self.has_emitted {
            Some(self.last_emitted_id)
        } else {
            None
        }
    }

    /// Finds the minimum-RTT sample among the kept slots, breaking ties in
    /// favor of the largest exchange identifier.
    fn best_in_window(&self) -> Option<Sampled> {
        let limit = if self.len < W { self.len } else { W };
        let mut best: Option<Sampled> = None;
        let mut i = 0usize;
        while i < limit {
            if let Some(slot) = self.slots.get(i)
                && slot.used
            {
                let pick = match best {
                    None => true,
                    Some(cur) => {
                        slot.sample.rtt_ns < cur.rtt_ns
                            || (slot.sample.rtt_ns == cur.rtt_ns && slot.sample.id > cur.id)
                    }
                };
                if pick {
                    best = Some(slot.sample);
                }
            }
            i = i.saturating_add(1);
        }
        best
    }

    /// Updates the online measurement-variance EWMA from the median excess RTT
    /// above `best_rtt_ns` across the kept window.
    fn update_variance(&mut self, best_rtt_ns: i64) -> u64 {
        let limit = if self.len < W { self.len } else { W };
        if limit < 2 {
            return self.variance_ns2();
        }
        let mut excesses = [0i64; W];
        let mut count = 0usize;
        let mut i = 0usize;
        while i < limit {
            if let Some(slot) = self.slots.get(i)
                && slot.used
            {
                let diff = slot.sample.rtt_ns.saturating_sub(best_rtt_ns);
                let clamped = if diff < 0 {
                    0
                } else if diff > MAX_EXCESS_NS {
                    MAX_EXCESS_NS
                } else {
                    diff
                };
                if let Some(dst) = excesses.get_mut(count) {
                    *dst = clamped;
                    count = count.saturating_add(1);
                }
            }
            i = i.saturating_add(1);
        }
        if count < 4 {
            return self.variance_ns2();
        }
        // Insertion sort on `excesses[..count]`.
        let mut a = 1usize;
        while a < count {
            let key = get_i64(&excesses, a);
            let mut b = a;
            while b > 0 {
                let prev_idx = b.wrapping_sub(1);
                let prev = get_i64(&excesses, prev_idx);
                if prev > key {
                    set_i64(&mut excesses, b, prev);
                    b = prev_idx;
                } else {
                    break;
                }
            }
            set_i64(&mut excesses, b, key);
            a = a.saturating_add(1);
        }
        let mid = count.wrapping_shr(1);
        let med = get_i64(&excesses, mid);
        let med_sq = (med as i128).wrapping_mul(med as i128);
        let denom = (count as i128).wrapping_mul(4);
        let raw_var = div_floor_wide(med_sq, denom);
        let smoothed = if self.has_ewma {
            let blended = (self.ewma_var_ns2 as i128)
                .wrapping_mul(17)
                .wrapping_add(raw_var.wrapping_mul(3));
            div_floor_wide(blended, 20)
        } else {
            raw_var
        };
        let clamped = clamp_var(smoothed, self.floor_var_ns2);
        self.has_ewma = true;
        self.ewma_var_ns2 = clamped;
        clamped
    }

    /// Takes in one completed 4-timestamp exchange. Returns a deduplicated
    /// minimum-RTT [`Measurement`] on the first valid exchange and every
    /// `stride` arrivals thereafter whenever a newer window minimum exists.
    pub fn observe(&mut self, ex: Exchange) -> Option<Measurement> {
        if W == 0 {
            return None;
        }
        let Some(sampled) = ntp_exchange(ex) else {
            return None;
        };
        let place = if self.next < W { self.next } else { 0 };
        if let Some(slot) = self.slots.get_mut(place) {
            *slot = Slot {
                used: true,
                sample: sampled,
            };
        }
        self.next = place.saturating_add(1).checked_rem(W).unwrap_or(0);
        if self.len < W {
            self.len = self.len.saturating_add(1);
        }
        self.record_min_rtt(sampled.midpoint_ns, sampled.rtt_ns);
        self.seen = self.seen.saturating_add(1);

        let stride = if self.stride == 0 { 1 } else { self.stride };
        let on_stride =
            self.seen >= (stride as u64) && self.seen.checked_rem(stride as u64).unwrap_or(1) == 0;
        if self.has_emitted && !on_stride {
            return None;
        }
        let Some(best) = self.best_in_window() else {
            return None;
        };
        let variance_ns2 = self.update_variance(best.rtt_ns);
        if self.has_emitted && best.id <= self.last_emitted_id {
            return None;
        }
        self.has_emitted = true;
        self.last_emitted_id = best.id;
        Some(Measurement {
            id: best.id,
            midpoint_ns: best.midpoint_ns,
            offset_ns: best.offset_ns,
            rtt_ns: best.rtt_ns,
            variance_ns2,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{
        DEFAULT_INITIAL_VARIANCE_NS2, DEFAULT_VARIANCE_FLOOR_NS2, Exchange, SlidingMinRtt,
        ntp_exchange,
    };

    #[test]
    fn ntp_exchange_computes_exact_offset_and_rejects_negative_rtt() {
        // Remote clock is +1000 ns ahead of local, 200 ns each way, 50 ns proc.
        let ex = Exchange {
            id: 1,
            t1: 100,
            t2: 1_300,
            t3: 1_350,
            t4: 550,
        };
        let s = ntp_exchange(ex).expect("valid");
        assert_eq!(s.rtt_ns, 400);
        assert_eq!(s.offset_ns, 1_000);
        assert_eq!(s.midpoint_ns, 325);

        // Negative processing time or negative RTT is rejected.
        assert_eq!(ntp_exchange(Exchange { t3: 1_299, ..ex }), None);
        assert_eq!(ntp_exchange(Exchange { t4: 100, ..ex }), None);
    }

    #[test]
    fn sliding_min_rtt_deduplicates_and_respects_floor() {
        let mut sel =
            SlidingMinRtt::<8>::new(4, DEFAULT_INITIAL_VARIANCE_NS2, DEFAULT_VARIANCE_FLOOR_NS2);
        // Exchange 1 locks immediately on startup.
        let m1 = sel
            .observe(Exchange {
                id: 1,
                t1: 0,
                t2: 100_000,
                t3: 100_000,
                t4: 200_000,
            })
            .expect("first exchange emits");
        assert_eq!(m1.id, 1);
        assert_eq!(m1.rtt_ns, 200_000);
        assert!(m1.variance_ns2 >= DEFAULT_VARIANCE_FLOOR_NS2);

        // Exchanges 2..=4 have worse RTT than exchange 1, so stride 4 must NOT
        // re-emit exchange 1 (monotonic deduplication).
        for i in 2..=4u64 {
            let t1 = i64::try_from(i).unwrap_or(0) * 1_000_000_000;
            let res = sel.observe(Exchange {
                id: i,
                t1,
                t2: t1 + 300_000,
                t3: t1 + 300_000,
                t4: t1 + 600_000,
            });
            assert_eq!(res, None, "exchange 1 must not be emitted twice");
        }
        // Exchange 8 has a fresh low RTT and emits cleanly.
        for i in 5..=8u64 {
            let t1 = i64::try_from(i).unwrap_or(0) * 1_000_000_000;
            let rtt = if i == 7 { 180_000 } else { 500_000 };
            let res = sel.observe(Exchange {
                id: i,
                t1,
                t2: t1 + rtt / 2,
                t3: t1 + rtt / 2,
                t4: t1 + rtt,
            });
            if i == 8 {
                let m = res.expect("stride 8 emits id 7");
                assert_eq!(m.id, 7);
                assert_eq!(m.rtt_ns, 180_000);
                assert!(m.variance_ns2 >= DEFAULT_VARIANCE_FLOOR_NS2);
            } else {
                assert_eq!(res, None);
            }
        }
        assert_eq!(sel.path_ns(), 90_000);
    }
}
