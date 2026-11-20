// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Numbers that go up and down.

use std::sync::Arc;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};

/// A handle to one integer gauge of a registry: a whole number that is set,
/// or moved up and down.
///
/// Every clone of the handle updates the same gauge.
#[derive(Clone, Debug)]
pub struct Gauge(Arc<AtomicI64>);

impl Gauge {
    pub(crate) fn new() -> Self {
        Gauge(Arc::new(AtomicI64::new(0)))
    }

    /// Replaces the value.
    pub fn set(&self, value: i64) {
        self.0.store(value, Ordering::Relaxed);
    }

    /// Adds `amount`, which may be negative. The value wraps beyond the
    /// range of `i64`.
    pub fn add(&self, amount: i64) {
        self.0.fetch_add(amount, Ordering::Relaxed);
    }

    /// The current value.
    #[must_use]
    pub fn get(&self) -> i64 {
        self.0.load(Ordering::Relaxed)
    }
}

/// A handle to one floating-point gauge of a registry.
///
/// The value can only be replaced: adding to a floating-point number takes a
/// loop of compare-and-exchange operations whose length has no bound, so
/// there is no such operation. A thread that needs a running total keeps it
/// itself and sets the gauge to it. Every clone of the handle updates the
/// same gauge.
#[derive(Clone, Debug)]
pub struct FloatGauge(Arc<AtomicU64>);

impl FloatGauge {
    pub(crate) fn new() -> Self {
        FloatGauge(Arc::new(AtomicU64::new(0f64.to_bits())))
    }

    /// Replaces the value. Infinities and NaN are kept and exported as such.
    pub fn set(&self, value: f64) {
        self.0.store(value.to_bits(), Ordering::Relaxed);
    }

    /// The current value.
    #[must_use]
    pub fn get(&self) -> f64 {
        f64::from_bits(self.0.load(Ordering::Relaxed))
    }
}
