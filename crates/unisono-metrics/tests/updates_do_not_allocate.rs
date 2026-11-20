// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Updating a series, and cloning or dropping a handle, allocates and frees
//! no memory.
//!
//! This file is a test program of its own, because it replaces the
//! allocator of the whole program by one that counts.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::hint::black_box;
use std::sync::atomic::{AtomicU64, Ordering};

use unisono_metrics::Registry;

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

#[test]
fn updates_and_handles_leave_the_allocator_alone() {
    let mut registry = Registry::new();
    let family = registry
        .counter_family("events_total", "Events.", &["kind"])
        .unwrap();
    let events = registry.counter(family, &["a"]).unwrap();
    let family = registry.gauge_family("level", "Level.", &[]).unwrap();
    let level = registry.gauge(family, &[]).unwrap();
    let family = registry.float_gauge_family("ratio", "Ratio.", &[]).unwrap();
    let ratio = registry.float_gauge(family, &[]).unwrap();
    let family = registry
        .histogram_family("sizes", "Sizes.", &["kind"], &[10, 20, 30], 10)
        .unwrap();
    let sizes = registry.histogram(family, &["a"]).unwrap();

    // The count works: it sees an allocation and the matching release.
    assert_eq!(calls_during(|| drop(black_box(Box::new(1u64)))), 2);

    let calls = calls_during(|| {
        for round in 0..1_000 {
            events.increment();
            events.add(3);
            level.set(round);
            level.add(-1);
            ratio.set(0.5);
            sizes.observe(round % 50);
            sizes.observe_units(1.5);
            sizes.observe_units(f64::NAN);
            black_box((events.get(), level.get(), ratio.get()));
        }
        // A thread may clone the handles it was given and drop them again.
        drop(black_box((
            events.clone(),
            level.clone(),
            ratio.clone(),
            sizes.clone(),
        )));
    });
    assert_eq!(calls, 0);

    // The registry holds every series, so the last handle of a thread frees
    // nothing either.
    assert_eq!(calls_during(|| drop((events, level, ratio, sizes))), 0);
    drop(registry);
}
