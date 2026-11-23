// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Lock-free fixed-bucket histogram with exact integer sum accumulation.

use std::fmt::{self, Write};
use std::sync::Arc;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};

use crate::text::{Braced, Number};

/// The buckets that all histograms of one family share.
#[derive(Debug, PartialEq)]
pub(crate) struct Buckets {
    /// The upper bound of each bucket but the last, in steps.
    bounds: Box<[i64]>,
    /// The number of steps in one unit of the exported value.
    steps_per_unit: u64,
}

impl Buckets {
    /// `None` when there are no steps in a unit, or when the bounds do not
    /// increase strictly as they are exported. Two bounds that differ in
    /// steps can be the same exported number when they are beyond 2^53.
    pub(crate) fn new(bounds: &[i64], steps_per_unit: u64) -> Option<Self> {
        let buckets = Buckets {
            bounds: bounds.into(),
            steps_per_unit,
        };
        let increasing = bounds
            .iter()
            .zip(bounds.iter().skip(1))
            .all(|(lower, upper)| buckets.exported(*lower) < buckets.exported(*upper));
        (steps_per_unit > 0 && increasing).then_some(buckets)
    }

    /// A number of steps in the exported unit. The division is rounded
    /// correctly, so a bound of 5 steps at 100 steps per unit is the number
    /// that `0.05` denotes.
    #[allow(clippy::cast_precision_loss)]
    fn exported(&self, steps: i64) -> f64 {
        steps as f64 / self.steps_per_unit as f64
    }
}

/// The numbers of one histogram.
#[derive(Debug)]
struct Cells {
    buckets: Arc<Buckets>,
    /// The number of observations in each bucket by itself, not cumulative.
    /// There is one more bucket than there are bounds: the last holds the
    /// values above every bound.
    counts: Box<[AtomicU64]>,
    /// The sum of the observed values, in steps.
    sum: AtomicI64,
}

/// A handle to one histogram of a registry.
///
/// A histogram counts whole numbers of steps. Its family fixes how many
/// steps make one unit of the exported value, and the upper bounds of the
/// buckets in steps: a histogram of durations in seconds that is given
/// nanoseconds has 1 000 000 000 steps per unit. Every clone of the handle
/// updates the same histogram.
#[derive(Clone, Debug)]
pub struct Histogram(Arc<Cells>);

impl Histogram {
    pub(crate) fn new(buckets: &Arc<Buckets>) -> Self {
        let counts = (0..=buckets.bounds.len())
            .map(|_| AtomicU64::new(0))
            .collect();
        Histogram(Arc::new(Cells {
            buckets: Arc::clone(buckets),
            counts,
            sum: AtomicI64::new(0),
        }))
    }

    /// Records one value, given in steps.
    ///
    /// The value is counted in the first bucket whose bound it does not
    /// exceed, and added to the sum. The sum wraps beyond the range of
    /// `i64`.
    pub fn observe(&self, steps: i64) {
        let bucket = self
            .0
            .buckets
            .bounds
            .partition_point(|bound| *bound < steps);
        self.count(bucket);
        self.0.sum.fetch_add(steps, Ordering::Relaxed);
    }

    /// Records one value, given in the exported unit.
    ///
    /// The value is rounded to the nearest whole number of steps, halves
    /// away from zero, and a value beyond the range of `i64` steps to the
    /// nearest end of that range; then it is recorded as [`observe`] does. A
    /// NaN is counted above every bound and adds nothing to the sum.
    ///
    /// [`observe`]: Histogram::observe
    pub fn observe_units(&self, value: f64) {
        if value.is_nan() {
            self.count(self.0.buckets.bounds.len());
        } else {
            // A conversion from floating point saturates.
            #[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)]
            let steps = (value * self.0.buckets.steps_per_unit as f64).round() as i64;
            self.observe(steps);
        }
    }

    /// Adds one to the count of a bucket.
    fn count(&self, bucket: usize) {
        // There is one more count than there are bounds, so the place exists
        // for every result of the search.
        if let Some(count) = self.0.counts.get(bucket) {
            count.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Writes the sample lines of this histogram.
    ///
    /// `labels` are the labels of the series as a sample line carries them,
    /// without braces. Every count is read once, and each line is computed
    /// from the counts read: so the bucket lines never decrease from one to
    /// the next, and the count line is the last bucket line's number.
    pub(crate) fn write<W: Write>(&self, out: &mut W, name: &str, labels: &str) -> fmt::Result {
        let Some((above, within)) = self.0.counts.split_last() else {
            return Ok(());
        };
        let buckets = &self.0.buckets;
        let separator = if labels.is_empty() { "" } else { "," };
        let mut cumulative = 0u64;
        for (bound, count) in buckets.bounds.iter().zip(within) {
            cumulative = cumulative.saturating_add(count.load(Ordering::Relaxed));
            let bound = Number(buckets.exported(*bound));
            writeln!(
                out,
                "{name}_bucket{{{labels}{separator}le=\"{bound}\"}} {cumulative}"
            )?;
        }
        cumulative = cumulative.saturating_add(above.load(Ordering::Relaxed));
        writeln!(
            out,
            "{name}_bucket{{{labels}{separator}le=\"+Inf\"}} {cumulative}"
        )?;
        let sum = Number(buckets.exported(self.0.sum.load(Ordering::Relaxed)));
        let labels = Braced(labels);
        writeln!(out, "{name}_sum{labels} {sum}")?;
        writeln!(out, "{name}_count{labels} {cumulative}")
    }
}
