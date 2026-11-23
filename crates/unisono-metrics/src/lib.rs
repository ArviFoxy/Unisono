// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Lock-free real-time-safe Prometheus counters, gauges, and histograms.
//!
//! [`Registry`] owns metric families (name, help, type, label schema) and
//! allocates series during setup, returning cloneable atomic handles
//! ([`Counter`], [`Gauge`], [`FloatGauge`], [`Histogram`]) for worker and
//! real-time threads.
//!
//! ```
//! use unisono_metrics::Registry;
//!
//! let mut registry = Registry::new();
//! let packets = registry.counter_family(
//!     "packets_total",
//!     "Received packets by disposition.",
//!     &["outcome"],
//! )?;
//! let accepted = registry.counter(packets, &["accepted"])?;
//! // Durations are observed in nanoseconds and exported in seconds.
//! let delays = registry.histogram_family(
//!     "delay_seconds",
//!     "Packet transit delay.",
//!     &[],
//!     &[100_000, 1_000_000, 10_000_000],
//!     1_000_000_000,
//! )?;
//! let delay = registry.histogram(delays, &[])?;
//!
//! accepted.increment();
//! delay.observe(250_000);
//!
//! let mut text = String::new();
//! registry.write_text(&mut text)?;
//! assert!(text.contains("packets_total{outcome=\"accepted\"} 1\n"));
//! assert!(text.contains("delay_seconds_bucket{le=\"0.001\"} 1\n"));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! # Real-Time Update Guarantees
//!
//! Updating through a handle performs no locks, allocations, or syscalls,
//! using one 64-bit atomic operation for counters/gauges and two for
//! histograms (plus binary search over static bucket bounds). On x86-64 and
//! ARMv8.1+ (LSE), these compile to single atomic instructions; on older ARM
//! targets they use LL/SC loops (lock-free, never blocked by exporters).
//!
//! # Concurrent Export Semantics
//!
//! [`Registry::write_text`] emits families and series in registration order
//! using lock-free single-pass atomic loads:
//!
//! - Within a histogram export, cumulative bucket counts are non-decreasing
//!   and `_count` matches the `+Inf` bucket (derived from the same read).
//! - Each gauge reflects a single atomic value (no torn reads).
//! - Across sequentially ordered exports, counters, histogram buckets, and
//!   `_count` never decrease (absent `u64::MAX` wraparound).
//! - Updates ordered before `write_text` begins are always visible; updates
//!   ordered after it returns are absent; quiescent exports are exact.
//! - Concurrent updates may appear partially across `_bucket`/`_sum` or across
//!   separate series.
//!
//! # Numeric Representation
//!
//! Counters (`u64`) and integer gauges (`i64`) format exactly; floating-point
//! gauges use shortest round-trip formatting (`NaN`, `+Inf`, `-Inf`).
//! Histograms accumulate integer steps and divide by the family scale factor
//! only during formatting, keeping sums order-independent and free of
//! floating-point drift.

#![forbid(unsafe_code)]

// Every atomic operation in this crate uses the relaxed ordering. Each
// guarantee above is about one number by itself, or about numbers that one
// export read once each; none needs two different numbers to be seen in the
// order in which they were written. For one number, the language gives the
// relaxed ordering what the guarantees use: all writes to it are in one
// order, and a read that comes after a write or another read, in the
// program's order, sees no earlier state than that write or read.

mod counter;
mod gauge;
mod histogram;
mod registry;
mod text;

pub use counter::Counter;
pub use gauge::{FloatGauge, Gauge};
pub use histogram::Histogram;
pub use registry::{
    CounterFamily, FloatGaugeFamily, GaugeFamily, HistogramFamily, RegistrationError, Registry,
};

/// The value of the HTTP `Content-Type` header for the text that
/// [`Registry::write_text`] writes.
pub const CONTENT_TYPE: &str = "text/plain; version=0.0.4; charset=utf-8";
