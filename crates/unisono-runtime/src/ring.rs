// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A ring between two threads, without locks.
//!
//! One thread puts items in and one other thread takes them out, in the
//! order they were put in. Neither ever waits for the other: putting into a
//! full ring and taking from an empty one return at once, and each call is a
//! fixed number of steps. The ring allocates its places when it is made and
//! nothing afterwards, so a thread that may not wait can use either end.
//!
//! # How it works
//!
//! Two counters count the items ever put in and ever taken out. The producer
//! alone writes the first and the consumer alone the second; each reads the
//! other's to see how full the ring is, and keeps its own in a field of its
//! end as well, so that it never reads what only it writes. An item is
//! written to its place before the counter that makes it visible is stored,
//! and it is read before the counter that frees its place is stored, so the
//! two threads never use one place at the same time.

use std::mem::MaybeUninit;

#[cfg(loom)]
use loom::cell::UnsafeCell;
#[cfg(loom)]
use loom::sync::Arc;
#[cfg(loom)]
use loom::sync::atomic::{AtomicUsize, Ordering};
#[cfg(not(loom))]
use std::cell::UnsafeCell;
#[cfg(not(loom))]
use std::sync::Arc;
#[cfg(not(loom))]
use std::sync::atomic::{AtomicUsize, Ordering};

/// A counter on a cache line of its own, so that the two threads do not slow
/// each other down by writing to neighbouring memory.
#[repr(align(64))]
struct Counter(AtomicUsize);

/// One place of the ring.
struct Place<T>(UnsafeCell<MaybeUninit<T>>);

impl<T> Place<T> {
    fn empty() -> Place<T> {
        Place(UnsafeCell::new(MaybeUninit::uninit()))
    }

    /// Writes an item into the place.
    ///
    /// # Safety
    ///
    /// No other thread reads or writes this place during the call, and the
    /// place holds no item.
    #[cfg(not(loom))]
    unsafe fn put(&self, item: T) {
        // SAFETY: by the caller's promise nothing else uses the place, so the
        // pointer may be written through.
        unsafe { (*self.0.get()).write(item) };
    }

    /// Takes the item out of the place.
    ///
    /// # Safety
    ///
    /// No other thread reads or writes this place during the call, and the
    /// place holds an item, which the caller now owns.
    #[cfg(not(loom))]
    unsafe fn take(&self) -> T {
        // SAFETY: by the caller's promise nothing else uses the place and it
        // holds an item.
        unsafe { (*self.0.get()).assume_init_read() }
    }

    /// Writes an item into the place.
    ///
    /// # Safety
    ///
    /// As for the version without loom.
    #[cfg(loom)]
    unsafe fn put(&self, item: T) {
        self.0.with_mut(|place| {
            // SAFETY: by the caller's promise nothing else uses the place.
            unsafe { (*place).write(item) };
        });
    }

    /// Takes the item out of the place.
    ///
    /// # Safety
    ///
    /// As for the version without loom.
    #[cfg(loom)]
    unsafe fn take(&self) -> T {
        // SAFETY: by the caller's promise nothing else uses the place and it
        // holds an item.
        self.0.with(|place| unsafe { (*place).assume_init_read() })
    }
}

struct Shared<T> {
    places: Box<[Place<T>]>,
    /// The number of places minus one; the number of places is a power of
    /// two, so a counter and this give a place.
    mask: usize,
    /// How many items were ever put in. Written by the producer only.
    put: Counter,
    /// How many items were ever taken out. Written by the consumer only.
    taken: Counter,
}

// SAFETY: the two ends hand items from one thread to the other, which is what
// `T: Send` allows; the places are only ever used by one thread at a time, as
// the module's description says.
unsafe impl<T: Send> Send for Shared<T> {}
// SAFETY: as above; the shared parts are the atomic counters and the places,
// each of which one thread at a time uses.
unsafe impl<T: Send> Sync for Shared<T> {}

impl<T> Drop for Shared<T> {
    fn drop(&mut self) {
        // Both ends are gone, so the items still inside are dropped here.
        let put = self.put.0.load(Ordering::Relaxed);
        let mut taken = self.taken.0.load(Ordering::Relaxed);
        while taken != put {
            if let Some(place) = self.places.get(taken & self.mask) {
                // SAFETY: no other thread exists that could use the place,
                // and every place between the two counters holds an item.
                drop(unsafe { place.take() });
            }
            taken = taken.wrapping_add(1);
        }
    }
}

/// The end of a ring that items are put into.
pub struct Producer<T> {
    shared: Arc<Shared<T>>,
    /// How many items were ever put in: what the shared counter holds.
    put: usize,
}

/// The end of a ring that items are taken from.
pub struct Consumer<T> {
    shared: Arc<Shared<T>>,
    /// How many items were ever taken out: what the shared counter holds.
    taken: usize,
}

/// A ring with room for at least `room` items, and at least one, as its two
/// ends. The room is the next power of two.
#[must_use]
pub fn ring<T: Send>(room: usize) -> (Producer<T>, Consumer<T>) {
    let places = room.max(1).next_power_of_two();
    let shared = Arc::new(Shared {
        places: (0..places).map(|_| Place::empty()).collect(),
        mask: places - 1,
        put: Counter(AtomicUsize::new(0)),
        taken: Counter(AtomicUsize::new(0)),
    });
    (
        Producer {
            shared: Arc::clone(&shared),
            put: 0,
        },
        Consumer { shared, taken: 0 },
    )
}

impl<T: Send> Producer<T> {
    /// The number of items the ring has room for.
    #[must_use]
    pub fn room(&self) -> usize {
        self.shared.places.len()
    }

    /// Puts an item in, or gives it back if the ring is full.
    ///
    /// # Errors
    ///
    /// The item, when the ring is full.
    pub fn put(&mut self, item: T) -> Result<(), T> {
        let shared = &*self.shared;
        let taken = shared.taken.0.load(Ordering::Acquire);
        if self.put.wrapping_sub(taken) >= shared.places.len() {
            return Err(item);
        }
        let Some(place) = shared.places.get(self.put & shared.mask) else {
            return Err(item);
        };
        // SAFETY: the place is not among the ones between `taken` and `put`,
        // which are the only ones the consumer reads, and this is the only
        // producer. It holds no item: whatever was here was taken before
        // `taken` passed it.
        unsafe { place.put(item) };
        self.put = self.put.wrapping_add(1);
        shared.put.0.store(self.put, Ordering::Release);
        Ok(())
    }
}

impl<T: Send> Consumer<T> {
    /// Takes the oldest item out, if there is one.
    pub fn take(&mut self) -> Option<T> {
        let shared = &*self.shared;
        let put = shared.put.0.load(Ordering::Acquire);
        if self.taken == put {
            return None;
        }
        let place = shared.places.get(self.taken & shared.mask)?;
        // SAFETY: the place is between `taken` and `put`, so the producer
        // wrote an item to it before storing `put` and does not use it again
        // until `taken` has passed it; this is the only consumer.
        let item = unsafe { place.take() };
        self.taken = self.taken.wrapping_add(1);
        shared.taken.0.store(self.taken, Ordering::Release);
        Some(item)
    }

    /// The number of items waiting, which may have grown by the time it is
    /// used.
    #[must_use]
    pub fn waiting(&self) -> usize {
        let put = self.shared.put.0.load(Ordering::Acquire);
        put.wrapping_sub(self.taken)
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::ring;

    #[test]
    fn items_come_out_in_the_order_they_went_in() {
        let (mut producer, mut consumer) = ring::<u32>(4);
        assert_eq!(consumer.take(), None);
        for item in 0..4 {
            assert_eq!(producer.put(item), Ok(()));
        }
        assert_eq!(consumer.waiting(), 4);
        for item in 0..4 {
            assert_eq!(consumer.take(), Some(item));
        }
        assert_eq!(consumer.take(), None);
    }

    #[test]
    fn a_full_ring_gives_the_item_back_and_keeps_what_it_holds() {
        let (mut producer, mut consumer) = ring::<u32>(3);
        // Room for three is rounded up to four.
        assert_eq!(producer.room(), 4);
        for item in 0..4 {
            assert_eq!(producer.put(item), Ok(()));
        }
        assert_eq!(producer.put(99), Err(99));
        assert_eq!(consumer.take(), Some(0));
        assert_eq!(producer.put(4), Ok(()));
        let rest: Vec<u32> = std::iter::from_fn(|| consumer.take()).collect();
        assert_eq!(rest, [1, 2, 3, 4]);
    }

    #[test]
    fn the_places_are_used_again_many_times_over() {
        // Far more items than places, so every place is written and read
        // again and again, with the ring at every fill level.
        let (mut producer, mut consumer) = ring::<u64>(8);
        let mut next_in = 0u64;
        let mut next_out = 0u64;
        for round in 0..10_000u64 {
            for _ in 0..round % 9 {
                if producer.put(next_in).is_ok() {
                    next_in += 1;
                }
            }
            for _ in 0..(round / 3) % 9 {
                if let Some(item) = consumer.take() {
                    assert_eq!(item, next_out);
                    next_out += 1;
                }
            }
        }
        assert!(next_out > 20_000);
    }

    /// Counts how many of it are alive.
    struct Counted(Arc<AtomicUsize>);

    impl Counted {
        fn new(alive: &Arc<AtomicUsize>) -> Counted {
            alive.fetch_add(1, Ordering::SeqCst);
            Counted(Arc::clone(alive))
        }
    }

    impl Drop for Counted {
        fn drop(&mut self) {
            self.0.fetch_sub(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn items_left_in_a_ring_are_dropped_with_it_and_none_twice() {
        let alive = Arc::new(AtomicUsize::new(0));
        let (mut producer, mut consumer) = ring::<Counted>(4);
        for _ in 0..4 {
            assert!(producer.put(Counted::new(&alive)).is_ok());
        }
        drop(consumer.take());
        assert_eq!(alive.load(Ordering::SeqCst), 3);
        // A refused item comes back and is dropped by the caller.
        assert!(producer.put(Counted::new(&alive)).is_ok());
        assert!(producer.put(Counted::new(&alive)).is_err());
        assert_eq!(alive.load(Ordering::SeqCst), 4);
        drop(producer);
        assert_eq!(alive.load(Ordering::SeqCst), 4);
        drop(consumer);
        assert_eq!(alive.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn two_threads_pass_a_million_items_without_loss_or_reordering() {
        const ITEMS: u64 = 1_000_000;
        let (mut producer, mut consumer) = ring::<[u64; 4]>(64);
        let sender = std::thread::spawn(move || {
            let mut item = 0u64;
            while item < ITEMS {
                // Four copies of the number: a torn item would show as
                // copies that differ.
                if producer.put([item; 4]).is_ok() {
                    item += 1;
                } else {
                    std::thread::yield_now();
                }
            }
        });
        let mut expected = 0u64;
        while expected < ITEMS {
            match consumer.take() {
                Some(item) => {
                    assert_eq!(item, [expected; 4]);
                    expected += 1;
                }
                None => std::thread::yield_now(),
            }
        }
        sender.join().expect("the producer does not panic");
        assert_eq!(consumer.take(), None);
    }
}

/// The ring under every interleaving of its two threads that loom explores.
/// Run with `RUSTFLAGS="--cfg loom"`.
#[cfg(all(test, loom))]
mod interleavings {
    use loom::thread;

    use super::ring;

    #[test]
    fn what_goes_in_comes_out_once_and_in_order() {
        loom::model(|| {
            let (mut producer, mut consumer) = ring::<u32>(2);
            let sender = thread::spawn(move || {
                let mut refused = 0;
                for item in 0..3 {
                    if producer.put(item).is_err() {
                        refused += 1;
                    }
                }
                refused
            });
            let mut seen = Vec::new();
            for _ in 0..3 {
                if let Some(item) = consumer.take() {
                    seen.push(item);
                }
            }
            let refused = sender.join().unwrap();
            while let Some(item) = consumer.take() {
                seen.push(item);
            }
            // The items that were accepted come out, each once, in order.
            assert_eq!(seen.len() + refused, 3);
            assert!(seen.windows(2).all(|pair| pair[0] < pair[1]));
            // The ring has two places, so at most one of three is refused
            // when the consumer takes none in time, and the first two never.
            assert!(refused <= 1);
            assert!(seen.starts_with(&[0, 1]));
        });
    }

    #[test]
    fn items_left_inside_are_dropped_with_the_ring() {
        loom::model(|| {
            let alive = loom::sync::Arc::new(());
            let (mut producer, mut consumer) = ring::<loom::sync::Arc<()>>(2);
            let handed = loom::sync::Arc::clone(&alive);
            let sender = thread::spawn(move || {
                let _ = producer.put(loom::sync::Arc::clone(&handed));
                let _ = producer.put(handed);
            });
            let taken = consumer.take();
            sender.join().unwrap();
            drop(taken);
            drop(consumer);
            // Both ends are gone: every copy that went in is dropped.
            assert_eq!(loom::sync::Arc::strong_count(&alive), 1);
        });
    }
}
