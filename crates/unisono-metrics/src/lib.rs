// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Counters, gauges and histograms that a real-time thread can update, and
//! their export in the Prometheus text format.
//!
//! A [`Registry`] owns metric families. A family has a name, a help text, a
//! type and a list of label names, and each of its series has one value for
//! every label name. Registering a family or a series allocates memory, so a
//! program does it before it starts its real-time work, or later on a thread
//! that may wait. Registering a series gives a handle to it: a [`Counter`],
//! a [`Gauge`], a [`FloatGauge`] or a [`Histogram`]. The threads that do the
//! work hold handles. Cloning a handle increments a reference count, and
//! every clone updates the same series.
//!
//! ```
//! use unisono_metrics::Registry;
//!
//! let mut registry = Registry::new();
//! let packets = registry.counter_family(
//!     "packets_total",
//!     "Packets received, by what became of them.",
//!     &["outcome"],
//! )?;
//! let accepted = registry.counter(packets, &["accepted"])?;
//! // Durations are observed in nanoseconds and exported in seconds.
//! let delays = registry.histogram_family(
//!     "delay_seconds",
//!     "Time a packet took.",
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
//! # Updating a series
//!
//! An update through a handle takes no lock, allocates and frees no memory,
//! makes no system call, and performs a fixed number of atomic operations on
//! 64-bit numbers: one for a counter or a gauge, and two for a histogram,
//! which first finds the bucket by bisection of its bounds. Any number of
//! threads may update the same series.
//!
//! How long one atomic operation takes depends on the processor. On x86-64,
//! and on 64-bit ARM processors that have the atomic instructions of version
//! 8.1 of the architecture, replacing a value and adding to a value are one
//! instruction each. On other ARM processors adding is a short loop: it
//! reads the number, adds, and writes the result on the condition that
//! nothing has written to the number in between. On 32-bit ARM, replacing a
//! 64-bit value is the same loop without the addition. A thread repeats the
//! loop when another thread's write to the same number went through in
//! between, or when the thread itself was interrupted in between. So some
//! update always completes, and an export, which only reads, never makes an
//! update repeat; but nothing bounds how often one thread repeats while
//! other threads keep writing to the same number.
//!
//! # What the export guarantees
//!
//! [`Registry::write_text`] writes the families in the order in which they
//! were registered, and the series of a family in that order as well. It
//! takes no lock and reads every number once, so it may run while other
//! threads update. A reader of the text may rely on the following.
//!
//! - **Within one export of a histogram**, the bucket lines never decrease
//!   from one bound to the next, and the `_count` line has the number of the
//!   `+Inf` bucket line. Both lines are computed from the same numbers read
//!   once.
//! - **A gauge line** has a value that the gauge had at one moment, never a
//!   mixture of two values.
//! - **From one export to a later one**, a counter does not decrease, and no
//!   bucket line and no `_count` line of a histogram decreases. "Later"
//!   means that the earlier export had returned before the later one
//!   started, as the program can tell: on the same thread, or on threads
//!   that hand the registry over through a lock, a channel or a join. This
//!   holds as long as no counter and no bucket passes `u64::MAX`.
//! - **An update that had returned before the export started**, in the same
//!   sense, is in the text. An update that starts after the export has
//!   returned is not. When no update runs during an export, the text is
//!   exact.
//!
//! An update that runs during an export may be in the text or not, and one
//! observation of a histogram may be in the bucket and count lines without
//! being in the `_sum` line, or the reverse. Different series are read at
//! different moments, so numbers of two series in one text need not belong
//! to the same instant.
//!
//! # Numbers
//!
//! A counter is a `u64` and an integer gauge an `i64`; both are written in
//! full, without rounding. A floating-point gauge is written with the fewest
//! digits that give the same `f64` back, or as `NaN`, `+Inf` or `-Inf`.
//!
//! A histogram counts whole numbers of steps, and its family states how many
//! steps make one unit of the exported value. The bucket bounds and the sum
//! are kept in steps and divided by that number when they are written. The
//! sum of a histogram is therefore exact: it does not depend on the order in
//! which threads add to it, and it has no rounding error until it is
//! divided for the text.

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
