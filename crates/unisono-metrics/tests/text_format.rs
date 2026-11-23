// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Conformance tests validating Prometheus text exposition format 0.0.4
//! against hand-written expected outputs.

use std::io;

use unisono_metrics::{RegistrationError, Registry};

type Outcome = Result<(), Box<dyn std::error::Error>>;

fn text(registry: &Registry) -> String {
    let mut text = String::new();
    registry
        .write_text(&mut text)
        .expect("writing to a string does not fail");
    text
}

/// A sample line without labels has no braces, and the comment lines come
/// before it.
#[test]
fn a_counter_without_labels() -> Outcome {
    let mut registry = Registry::new();
    let family = registry.counter_family("requests_total", "Requests served.", &[])?;
    let requests = registry.counter(family, &[])?;
    requests.add(2);
    requests.increment();
    assert_eq!(
        text(&registry),
        "# HELP requests_total Requests served.\n\
         # TYPE requests_total counter\n\
         requests_total 3\n"
    );
    Ok(())
}

/// All lines of a family form one group, whatever the order in which the
/// series of different families were registered, and each family has its
/// comment lines once.
#[test]
fn the_lines_of_a_family_stay_together() -> Outcome {
    let mut registry = Registry::new();
    let packets = registry.counter_family("packets_total", "Packets.", &["stream", "outcome"])?;
    let level = registry.gauge_family("level_frames", "Frames held.", &["stream"])?;
    let played = registry.counter(packets, &["1", "played"])?;
    let level_of_one = registry.gauge(level, &["1"])?;
    let late = registry.counter(packets, &["1", "late"])?;
    let level_of_two = registry.gauge(level, &["2"])?;
    played.add(40);
    late.add(2);
    level_of_one.set(480);
    level_of_two.set(-7);
    assert_eq!(
        text(&registry),
        "# HELP packets_total Packets.\n\
         # TYPE packets_total counter\n\
         packets_total{stream=\"1\",outcome=\"played\"} 40\n\
         packets_total{stream=\"1\",outcome=\"late\"} 2\n\
         # HELP level_frames Frames held.\n\
         # TYPE level_frames gauge\n\
         level_frames{stream=\"1\"} 480\n\
         level_frames{stream=\"2\"} -7\n"
    );
    Ok(())
}

/// A help text escapes the backslash and the line feed and leaves the
/// double quote alone; a label value escapes all three.
#[test]
fn help_texts_and_label_values_are_escaped() -> Outcome {
    let mut registry = Registry::new();
    let family = registry.counter_family(
        "file_errors_total",
        "Errors by \"path\":\nC:\\DIR and others.",
        &["path", "error"],
    )?;
    registry
        .counter(
            family,
            &["C:\\DIR\\FILE.TXT", "Cannot find file:\n\"FILE.TXT\""],
        )?
        .increment();
    assert_eq!(
        text(&registry),
        concat!(
            "# HELP file_errors_total Errors by \"path\":\\nC:\\\\DIR and others.\n",
            "# TYPE file_errors_total counter\n",
            "file_errors_total{path=\"C:\\\\DIR\\\\FILE.TXT\",",
            "error=\"Cannot find file:\\n\\\"FILE.TXT\\\"\"} 1\n",
        )
    );
    Ok(())
}

/// A histogram writes cumulative buckets in increasing order of their
/// bounds, a bucket `+Inf`, the sum and the count. A value equal to a bound
/// belongs to that bound's bucket, because the label means "less than or
/// equal".
#[test]
fn a_histogram() -> Outcome {
    let mut registry = Registry::new();
    // Hundredths of a second.
    let family = registry.histogram_family(
        "request_duration_seconds",
        "Time to serve a request.",
        &[],
        &[5, 10, 100],
        100,
    )?;
    let duration = registry.histogram(family, &[])?;
    for hundredths in [3, 5, 7, 50, 250] {
        duration.observe(hundredths);
    }
    assert_eq!(
        text(&registry),
        "# HELP request_duration_seconds Time to serve a request.\n\
         # TYPE request_duration_seconds histogram\n\
         request_duration_seconds_bucket{le=\"0.05\"} 2\n\
         request_duration_seconds_bucket{le=\"0.1\"} 3\n\
         request_duration_seconds_bucket{le=\"1\"} 4\n\
         request_duration_seconds_bucket{le=\"+Inf\"} 5\n\
         request_duration_seconds_sum 3.15\n\
         request_duration_seconds_count 5\n"
    );
    Ok(())
}

/// The labels of a histogram's series are on every one of its lines, and
/// each series has its own counts.
#[test]
fn a_histogram_with_labels() -> Outcome {
    let mut registry = Registry::new();
    let family = registry.histogram_family(
        "delay_seconds",
        "Delay.",
        &["link"],
        &[1_000_000],
        1_000_000_000,
    )?;
    let wired = registry.histogram(family, &["wired"])?;
    let wireless = registry.histogram(family, &["wireless"])?;
    wired.observe(200_000);
    wireless.observe(2_500_000);
    wireless.observe(-500_000);
    assert_eq!(
        text(&registry),
        "# HELP delay_seconds Delay.\n\
         # TYPE delay_seconds histogram\n\
         delay_seconds_bucket{link=\"wired\",le=\"0.001\"} 1\n\
         delay_seconds_bucket{link=\"wired\",le=\"+Inf\"} 1\n\
         delay_seconds_sum{link=\"wired\"} 0.0002\n\
         delay_seconds_count{link=\"wired\"} 1\n\
         delay_seconds_bucket{link=\"wireless\",le=\"0.001\"} 1\n\
         delay_seconds_bucket{link=\"wireless\",le=\"+Inf\"} 2\n\
         delay_seconds_sum{link=\"wireless\"} 0.002\n\
         delay_seconds_count{link=\"wireless\"} 2\n"
    );
    Ok(())
}

/// A value given in the exported unit is rounded to whole steps, and a NaN
/// is counted above every bound without changing the sum.
#[test]
fn values_in_the_exported_unit() -> Outcome {
    let mut registry = Registry::new();
    let family = registry.histogram_family("size_metres", "Size.", &[], &[10, 20], 10)?;
    let size = registry.histogram(family, &[])?;
    size.observe_units(0.96); // 10 steps: in the first bucket
    size.observe_units(1.04); // 10 steps as well
    size.observe_units(1.06); // 11 steps: in the second bucket
    size.observe_units(-0.25); // halves away from zero: -3 steps
    size.observe_units(f64::NAN);
    assert_eq!(
        text(&registry),
        "# HELP size_metres Size.\n\
         # TYPE size_metres histogram\n\
         size_metres_bucket{le=\"1\"} 3\n\
         size_metres_bucket{le=\"2\"} 4\n\
         size_metres_bucket{le=\"+Inf\"} 5\n\
         size_metres_sum 2.8\n\
         size_metres_count 5\n"
    );
    Ok(())
}

/// A floating-point gauge writes the three values that are not numbers the
/// way the format names them, and other values so that reading the text
/// gives the same number.
#[test]
fn floating_point_values() -> Outcome {
    let mut registry = Registry::new();
    let family = registry.float_gauge_family("drift_ratio", "Drift.", &["case"])?;
    let cases = [
        ("unset", None),
        ("small", Some(-0.000_012_5)),
        ("whole", Some(3.0)),
        ("tenth", Some(0.1)),
        ("above", Some(f64::INFINITY)),
        ("below", Some(f64::NEG_INFINITY)),
        ("nothing", Some(f64::NAN)),
    ];
    for (case, value) in cases {
        let gauge = registry.float_gauge(family, &[case])?;
        if let Some(value) = value {
            gauge.set(value);
        }
    }
    assert_eq!(
        text(&registry),
        "# HELP drift_ratio Drift.\n\
         # TYPE drift_ratio gauge\n\
         drift_ratio{case=\"unset\"} 0\n\
         drift_ratio{case=\"small\"} -0.0000125\n\
         drift_ratio{case=\"whole\"} 3\n\
         drift_ratio{case=\"tenth\"} 0.1\n\
         drift_ratio{case=\"above\"} +Inf\n\
         drift_ratio{case=\"below\"} -Inf\n\
         drift_ratio{case=\"nothing\"} NaN\n"
    );
    Ok(())
}

/// Counters and integer gauges are written in full: a number beyond 2^53
/// keeps its last digits.
#[test]
fn whole_numbers_are_written_in_full() -> Outcome {
    let mut registry = Registry::new();
    let counters = registry.counter_family("frames_total", "Frames.", &[])?;
    let gauges = registry.gauge_family("offset_nanoseconds", "Offset.", &[])?;
    registry.counter(counters, &[])?.add(u64::MAX);
    registry.gauge(gauges, &[])?.set(i64::MIN);
    assert_eq!(
        text(&registry),
        "# HELP frames_total Frames.\n\
         # TYPE frames_total counter\n\
         frames_total 18446744073709551615\n\
         # HELP offset_nanoseconds Offset.\n\
         # TYPE offset_nanoseconds gauge\n\
         offset_nanoseconds -9223372036854775808\n"
    );
    Ok(())
}

/// Asking twice for the same family and the same label values gives the
/// same series: the text has one line for it, with the updates of both
/// handles. Two lines with one name and the same labels would be invalid.
#[test]
fn a_series_is_registered_once() -> Outcome {
    let mut registry = Registry::new();
    let first = registry.counter_family("events_total", "Events.", &["kind"])?;
    let second = registry.counter_family("events_total", "Events.", &["kind"])?;
    assert_eq!(first, second);
    let one = registry.counter(first, &["a\"b"])?;
    let other = registry.counter(second, &["a\"b"])?;
    one.add(5);
    other.add(6);
    one.clone().increment();
    assert_eq!(
        text(&registry),
        "# HELP events_total Events.\n\
         # TYPE events_total counter\n\
         events_total{kind=\"a\\\"b\"} 12\n"
    );
    Ok(())
}

/// Names that the format cannot carry are refused, and so is a label name
/// that the format or Prometheus uses itself.
#[test]
fn invalid_names_are_refused() {
    let mut registry = Registry::new();
    for name in ["", "9lives", "with-dash", "with space", "caf\u{e9}", "a{b}"] {
        assert_eq!(
            registry.counter_family(name, "Help.", &[]),
            Err(RegistrationError::MetricName),
            "metric name {name:?}"
        );
    }
    assert!(registry.counter_family("a:b_c9", "Help.", &[]).is_ok());
    for label in ["", "9", "a:b", "a-b", "__name"] {
        assert_eq!(
            registry.gauge_family("level", "Help.", &["stream", label]),
            Err(RegistrationError::LabelName),
            "label name {label:?}"
        );
    }
    assert_eq!(
        registry.gauge_family("level", "Help.", &["stream", "stream"]),
        Err(RegistrationError::LabelName)
    );
    assert_eq!(
        registry.histogram_family("delay", "Help.", &["le"], &[1], 1),
        Err(RegistrationError::LabelName)
    );
    // `le` means nothing special outside a histogram.
    assert!(
        registry
            .gauge_family("level", "Help.", &["le", "_x1"])
            .is_ok()
    );
}

/// A histogram writes lines under its name with `_bucket`, `_sum` and
/// `_count` appended, so no other family may have one of those names, in
/// whichever order the two are registered.
#[test]
fn names_that_would_collide_are_refused() -> Outcome {
    let mut registry = Registry::new();
    registry.histogram_family("delay", "Help.", &[], &[1], 1)?;
    for name in ["delay_bucket", "delay_sum", "delay_count"] {
        assert_eq!(
            registry.counter_family(name, "Help.", &[]),
            Err(RegistrationError::NameTaken),
            "{name}"
        );
    }
    registry.counter_family("jitter_count", "Help.", &[])?;
    assert_eq!(
        registry.histogram_family("jitter", "Help.", &[], &[1], 1),
        Err(RegistrationError::NameTaken)
    );
    registry.histogram_family("jitter_other", "Help.", &[], &[1], 1)?;
    Ok(())
}

/// A name cannot be registered again with another meaning: the text would
/// carry two types or two help texts for one name.
#[test]
fn a_family_cannot_be_redefined() -> Outcome {
    let mut registry = Registry::new();
    registry.counter_family("events_total", "Events.", &["kind"])?;
    assert_eq!(
        registry.gauge_family("events_total", "Events.", &["kind"]),
        Err(RegistrationError::Conflict)
    );
    assert_eq!(
        registry.counter_family("events_total", "Other.", &["kind"]),
        Err(RegistrationError::Conflict)
    );
    assert_eq!(
        registry.counter_family("events_total", "Events.", &["kind", "more"]),
        Err(RegistrationError::Conflict)
    );
    registry.histogram_family("delay", "Help.", &[], &[1, 2], 10)?;
    assert_eq!(
        registry.histogram_family("delay", "Help.", &[], &[1, 3], 10),
        Err(RegistrationError::Conflict)
    );
    assert_eq!(
        registry.histogram_family("delay", "Help.", &[], &[1, 2], 100),
        Err(RegistrationError::Conflict)
    );
    Ok(())
}

/// Bounds must increase strictly as exported: equal bounds would give two
/// lines with the same labels, and so would two large bounds that become
/// the same floating-point number.
#[test]
fn buckets_that_cannot_be_exported_are_refused() {
    let mut registry = Registry::new();
    let refused = Err(RegistrationError::Buckets);
    assert_eq!(
        registry.histogram_family("a", "Help.", &[], &[1, 1], 1),
        refused
    );
    assert_eq!(
        registry.histogram_family("a", "Help.", &[], &[2, 1], 1),
        refused
    );
    assert_eq!(
        registry.histogram_family("a", "Help.", &[], &[1, 2], 0),
        refused
    );
    // 2^53 and 2^53 + 1 are the same `f64`.
    assert_eq!(
        registry.histogram_family(
            "a",
            "Help.",
            &[],
            &[9_007_199_254_740_992, 9_007_199_254_740_993],
            1
        ),
        refused
    );
    assert!(registry.histogram_family("a", "Help.", &[], &[], 1).is_ok());
}

/// A series needs one value for each label name of its family, and a family
/// of one registry is not accepted by another registry that has no such
/// family.
#[test]
fn series_that_do_not_fit_their_family_are_refused() -> Outcome {
    let mut registry = Registry::new();
    let family = registry.counter_family("events_total", "Events.", &["kind"])?;
    assert_eq!(
        registry.counter(family, &[]).map(|_| ()),
        Err(RegistrationError::LabelCount)
    );
    assert_eq!(
        registry.counter(family, &["a", "b"]).map(|_| ()),
        Err(RegistrationError::LabelCount)
    );
    let mut empty = Registry::new();
    assert_eq!(
        empty.counter(family, &["a"]).map(|_| ()),
        Err(RegistrationError::UnknownFamily)
    );
    let mut other = Registry::new();
    other.gauge_family("level", "Level.", &["kind"])?;
    assert_eq!(
        other.counter(family, &["a"]).map(|_| ()),
        Err(RegistrationError::UnknownFamily)
    );
    // A refused series leaves nothing behind.
    assert_eq!(text(&other), "# HELP level Level.\n# TYPE level gauge\n");
    Ok(())
}

/// A writer of bytes that accepts a limited number of bytes.
struct Limited {
    written: Vec<u8>,
    room: usize,
}

impl io::Write for Limited {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > self.room {
            return Err(io::Error::new(io::ErrorKind::StorageFull, "no room"));
        }
        self.room -= bytes.len();
        self.written.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The bytes written are the text, and an error of the writer reaches the
/// caller as that error.
#[test]
fn writing_bytes() -> Outcome {
    let mut registry = Registry::new();
    let family = registry.counter_family("events_total", "Events.", &["kind"])?;
    registry.counter(family, &["a"])?.add(7);

    let mut enough = Limited {
        written: Vec::new(),
        room: 1_000,
    };
    registry.write_text_io(&mut enough)?;
    assert_eq!(String::from_utf8(enough.written)?, text(&registry));

    let mut short = Limited {
        written: Vec::new(),
        room: 20,
    };
    let error = registry
        .write_text_io(&mut short)
        .expect_err("the writer has no room for the text");
    assert_eq!(error.kind(), io::ErrorKind::StorageFull);
    Ok(())
}

/// The registry and the handles can be given to other threads, and shared
/// between them. This fails to compile when a change takes that away.
#[test]
fn handles_and_registry_cross_threads() {
    fn crosses_threads<T: Send + Sync>() {}
    crosses_threads::<Registry>();
    crosses_threads::<unisono_metrics::Counter>();
    crosses_threads::<unisono_metrics::Gauge>();
    crosses_threads::<unisono_metrics::FloatGauge>();
    crosses_threads::<unisono_metrics::Histogram>();
}
