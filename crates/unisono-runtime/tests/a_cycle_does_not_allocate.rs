// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Taking in a packet and playing a cycle allocate and free no memory, also
//! when packets are lost and when the position jumps.
//!
//! This file is a test program of its own, because it replaces the
//! allocator of the whole program by one that counts.

mod common;

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};

use common::{CHANNELS, Line, Listener, ramp, settings};
use unisono_dsp::Parameters;
use unisono_runtime::software::{Device, Output};

thread_local! {
    /// Whether the allocator counts the calls of this thread.
    static COUNTED: Cell<bool> = const { Cell::new(false) };
}

/// Calls to the allocator from threads that are counted.
static CALLS: AtomicU64 = AtomicU64::new(0);

/// The system's allocator, with a count of the calls to it.
struct Counting;

impl Counting {
    fn count() {
        if COUNTED.try_with(Cell::get).unwrap_or(false) {
            CALLS.fetch_add(1, Ordering::Relaxed);
        }
    }
}

// SAFETY: every call is handed to the system's allocator with the arguments
// it came with, and the count touches no memory that the allocator manages.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        Self::count();
        // SAFETY: the caller keeps the contract of `alloc`.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        Self::count();
        // SAFETY: the caller keeps the contract of `dealloc`.
        unsafe { System.dealloc(pointer, layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        Self::count();
        // SAFETY: the caller keeps the contract of `realloc`.
        unsafe { System.realloc(pointer, layout, size) }
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

/// The number of calls to the allocator that `work` makes on this thread.
fn calls_during(work: impl FnOnce()) -> u64 {
    let before = CALLS.load(Ordering::Relaxed);
    COUNTED.set(true);
    work();
    COUNTED.set(false);
    CALLS.load(Ordering::Relaxed) - before
}

/// Half a second of a stream with lost packets and with a change of the
/// level that makes the receiver jump: every call that takes in a packet and
/// every cycle of the device is counted.
#[test]
fn packets_and_cycles_call_the_allocator_never() {
    const RATE: u32 = 50_000;
    let mut line = Line::new(RATE, 250, 30_000_000, ramp);
    // Everything that the test itself allocates is made before the count.
    let mut packets = Vec::new();
    for number in 0..100u64 {
        if number == 60 {
            line.sender.level(20_000_000, 0);
        }
        packets.push(line.send());
    }
    let mut listener = Listener::new(&settings(RATE, Parameters::for_rate(RATE)));
    listener.path(line.delay);
    let device = Device {
        rate: RATE,
        channels: CHANNELS,
        cycle: 100,
        drift: 150_000,
        start: line.offset,
        lead: 4_000_000,
        hidden: 0,
    };
    let mut output = Output::new(device, 30_000);

    let lost = [40, 41, 77];
    let mut calls = 0;
    let mut played = 0;
    for sent in &packets {
        while output.due() < sent.arrival {
            calls += calls_during(|| output.cycle(&mut listener));
            played += 1;
        }
        if !lost.contains(&sent.number) {
            calls += calls_during(|| {
                listener.packet(&sent.header, &sent.payload, sent.arrival);
            });
        }
    }
    assert_eq!(calls, 0);

    // The count was of something: cycles played from the stream, frames
    // were concealed, and the position jumped at the start and at the
    // change of the level.
    let totals = listener.totals();
    assert_eq!(totals.cycles, played);
    assert!(totals.played > 15_000, "played {}", totals.played);
    assert_eq!(totals.concealed, 750);
    assert_eq!(totals.jumps, 2);
    assert_eq!(output.unrecorded(), 0);
}
