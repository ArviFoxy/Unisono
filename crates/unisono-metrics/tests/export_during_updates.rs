// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! What a reader of the exported text may rely on while threads update.
//!
//! Several threads update a counter, two gauges and a histogram without
//! pause while another thread exports. Every export must keep what the
//! crate's documentation promises, and the export after the threads have
//! stopped must be exactly what they say they did.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::thread;

use unisono_metrics::Registry;

const UPDATERS: usize = 4;
const EXPORTS: usize = 2_000;
/// The observed values run from 0 to 39, so nothing lies above the last
/// bound: the last two bucket lines are equal whenever no update is under
/// way, and an export that catches an update half done shows there.
const BOUNDS: [i64; 4] = [10, 20, 30, 100];
/// The two values that the updating threads give the floating-point gauge,
/// each with its text. They differ in both halves of their 64 bits.
const RATIOS: [(f64, &str); 2] = [(1.5, "1.5"), (-22_500_000_000.0, "-22500000000")];

/// What one updating thread did.
#[derive(Default)]
struct Tally {
    /// Observations in each bucket by itself; the last is above every bound.
    buckets: [u64; BOUNDS.len() + 1],
    sum: i64,
    count: u64,
}

impl Tally {
    fn record(&mut self, value: i64) {
        let bucket = BOUNDS
            .iter()
            .position(|bound| value <= *bound)
            .unwrap_or(BOUNDS.len());
        self.buckets[bucket] += 1;
        self.sum += value;
        self.count += 1;
    }
}

/// The numbers of one exported text.
struct Export {
    events: u64,
    level: i64,
    ratio: String,
    /// The bucket lines in the order of the text: the bound as written, and
    /// the count.
    buckets: Vec<(String, u64)>,
    sum: String,
    count: u64,
}

/// Tells the updating threads to stop when it is dropped. The exporting
/// thread holds it, so the threads also stop when an assertion fails there;
/// the test would otherwise wait for them without end.
struct StopsUpdaters<'a>(&'a AtomicBool);

impl Drop for StopsUpdaters<'_> {
    fn drop(&mut self) {
        self.0.store(true, Ordering::Relaxed);
    }
}

/// The value of the sample line that begins with `start`.
fn value<'t>(text: &'t str, start: &str) -> &'t str {
    text.lines()
        .find_map(|line| line.strip_prefix(start)?.strip_prefix(' '))
        .unwrap_or_else(|| panic!("no line that begins with {start:?} in:\n{text}"))
}

fn whole<T: std::str::FromStr>(digits: &str) -> T {
    digits
        .parse()
        .unwrap_or_else(|_| panic!("{digits:?} is not a whole number"))
}

fn read(text: &str) -> Export {
    let buckets = text
        .lines()
        .filter_map(|line| line.strip_prefix("sizes_bucket{le=\""))
        .map(|rest| {
            let (bound, count) = rest
                .split_once("\"} ")
                .unwrap_or_else(|| panic!("a bucket line ends unexpectedly: {rest:?}"));
            (bound.to_owned(), whole(count))
        })
        .collect();
    Export {
        events: whole(value(text, "events_total")),
        level: whole(value(text, "level")),
        ratio: value(text, "ratio").to_owned(),
        buckets,
        sum: value(text, "sizes_sum").to_owned(),
        count: whole(value(text, "sizes_count")),
    }
}

#[test]
fn every_export_keeps_its_guarantees_while_threads_update() {
    let mut registry = Registry::new();
    let family = registry
        .counter_family("events_total", "Events.", &[])
        .unwrap();
    let events = registry.counter(family, &[]).unwrap();
    let family = registry.gauge_family("level", "Level.", &[]).unwrap();
    let level = registry.gauge(family, &[]).unwrap();
    let family = registry.float_gauge_family("ratio", "Ratio.", &[]).unwrap();
    let ratio = registry.float_gauge(family, &[]).unwrap();
    let family = registry
        .histogram_family("sizes", "Sizes.", &[], &BOUNDS, 1)
        .unwrap();
    let sizes = registry.histogram(family, &[]).unwrap();

    let stop = AtomicBool::new(false);
    let started = AtomicUsize::new(0);
    let tallies: Vec<Tally> = thread::scope(|scope| {
        let updaters: Vec<_> = (0..UPDATERS)
            .map(|updater| {
                let (events, level, ratio, sizes) =
                    (events.clone(), level.clone(), ratio.clone(), sizes.clone());
                let (stop, started) = (&stop, &started);
                scope.spawn(move || {
                    let mut tally = Tally::default();
                    let mut value = i64::try_from(updater).unwrap();
                    loop {
                        // Runs through every value from 0 to 39.
                        value = (value + 7) % 40;
                        sizes.observe(value);
                        events.increment();
                        level.set(value);
                        ratio.set(RATIOS[usize::from(value % 2 == 0)].0);
                        tally.record(value);
                        if tally.count == 1 {
                            started.fetch_add(1, Ordering::SeqCst);
                        }
                        if stop.load(Ordering::Relaxed) {
                            return tally;
                        }
                    }
                })
            })
            .collect();

        let stops_updaters = StopsUpdaters(&stop);

        // Every thread has updated every series before the first export.
        while started.load(Ordering::SeqCst) < UPDATERS {
            thread::yield_now();
        }
        let mut earlier: Option<Export> = None;
        let mut text = String::new();
        for _ in 0..EXPORTS {
            text.clear();
            registry.write_text(&mut text).unwrap();
            let export = read(&text);

            // Within one export: the buckets are those of the family, in
            // increasing order of their bounds; they never decrease from one
            // to the next; and the count is the last bucket.
            let bounds: Vec<&str> = export.buckets.iter().map(|(bound, _)| &**bound).collect();
            assert_eq!(bounds, ["10", "20", "30", "100", "+Inf"], "in:\n{text}");
            let counts: Vec<u64> = export.buckets.iter().map(|(_, count)| *count).collect();
            assert!(counts.is_sorted(), "buckets decrease in:\n{text}");
            assert_eq!(counts.last(), Some(&export.count), "in:\n{text}");

            // A gauge shows a value that some thread gave it, whole.
            assert!((0..40).contains(&export.level), "in:\n{text}");
            assert!(
                RATIOS.iter().any(|(_, text)| export.ratio == *text),
                "in:\n{text}"
            );

            // From one export to the next: nothing that counts decreases.
            if let Some(earlier) = &earlier {
                assert!(earlier.events <= export.events, "the counter decreased");
                assert!(earlier.count <= export.count, "the count decreased");
                for ((_, before), (bound, now)) in earlier.buckets.iter().zip(&export.buckets) {
                    assert!(before <= now, "bucket {bound} decreased");
                }
            }
            earlier = Some(export);
            thread::yield_now();
        }

        drop(stops_updaters);
        updaters
            .into_iter()
            .map(|updater| updater.join().unwrap())
            .collect()
    });

    // Every update has returned, so the text is exact.
    let mut text = String::new();
    registry.write_text(&mut text).unwrap();
    let export = read(&text);
    let count: u64 = tallies.iter().map(|tally| tally.count).sum();
    let sum: i64 = tallies.iter().map(|tally| tally.sum).sum();
    let mut cumulative = 0;
    let buckets: Vec<u64> = (0..=BOUNDS.len())
        .map(|bucket| {
            cumulative += tallies
                .iter()
                .map(|tally| tally.buckets[bucket])
                .sum::<u64>();
            cumulative
        })
        .collect();
    assert_eq!(export.events, count);
    assert_eq!(export.count, count);
    assert_eq!(
        export.buckets.iter().map(|(_, n)| *n).collect::<Vec<_>>(),
        buckets
    );
    assert_eq!(export.sum, sum.to_string());
}
