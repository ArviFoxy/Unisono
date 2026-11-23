// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Lock-free monotonic `u64` counter.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

/// A handle to one counter of a registry: a number that only grows.
///
/// Every clone of the handle updates the same counter.
#[derive(Clone, Debug)]
pub struct Counter(Arc<AtomicU64>);

impl Counter {
    pub(crate) fn new() -> Self {
        Counter(Arc::new(AtomicU64::new(0)))
    }

    /// Adds one.
    pub fn increment(&self) {
        self.add(1);
    }

    /// Adds `amount`. The counter wraps to zero after `u64::MAX`.
    pub fn add(&self, amount: u64) {
        self.0.fetch_add(amount, Ordering::Relaxed);
    }

    /// The current value.
    #[must_use]
    pub fn get(&self) -> u64 {
        self.0.load(Ordering::Relaxed)
    }
}
