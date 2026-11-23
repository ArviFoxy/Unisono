// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! PipeWire integration tests against the null sink `unisono-test-sink`
//! started by `tools/pipewire-test.sh`. Marked `#[ignore]` by default because
//! they require that test instance.
//!
//! Plays a frame-index ramp into the sink, captures it back through a second
//! stream, and cross-checks PipeWire's reported positions and timestamps.

use std::sync::{Arc, Mutex};
use std::time::Duration;

use unisono_pipewire::{Settings, capture, play};
use unisono_runtime::audio::{Capture, Playback};

const RATE: u32 = 48_000;

/// One cycle as a stream saw it: the position and time it was given, and
/// the frames.
#[derive(Clone, Debug)]
struct Cycle {
    position: u64,
    time: i64,
    first: Option<f32>,
    frames: usize,
}

/// A playback that plays a ramp and keeps its cycles.
struct Ramp {
    next: u64,
    cycles: Arc<Mutex<Vec<Cycle>>>,
}

impl Playback for Ramp {
    fn channels(&self) -> usize {
        2
    }

    fn cycle(&mut self, frames: &mut [f32], position: u64, time: i64) {
        let count = frames.len() / 2;
        for frame in frames.as_chunks_mut::<2>().0 {
            // The ramp starts again after 2^23 frames, three minutes.
            #[allow(clippy::cast_precision_loss)]
            let value = ((self.next % 8_388_608) + 1) as f32 / 8_388_608.0;
            frame[0] = value;
            frame[1] = -value;
            self.next += 1;
        }
        if let Ok(mut cycles) = self.cycles.lock() {
            cycles.push(Cycle {
                position,
                time,
                first: frames.first().copied(),
                frames: count,
            });
        }
    }
}

/// A capture that keeps its cycles.
struct Record {
    cycles: Arc<Mutex<Vec<Cycle>>>,
}

impl Capture for Record {
    fn channels(&self) -> usize {
        2
    }

    fn cycle(&mut self, frames: &[f32], position: u64, time: i64) {
        if let Ok(mut cycles) = self.cycles.lock() {
            cycles.push(Cycle {
                position,
                time,
                first: frames.first().copied(),
                frames: frames.len() / 2,
            });
        }
    }
}

fn settings(name: &str, monitor: bool, cycle: u32) -> Settings {
    Settings {
        name: name.into(),
        rate: RATE,
        channels: 2,
        target: Some("unisono-test-sink".into()),
        monitor,
        largest_cycle: 8_192,
        cycle,
    }
}

fn verify_roundtrip(cycle: u32) {
    let played = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::new(Mutex::new(Vec::new()));
    let playing = play(
        Ramp {
            next: 0,
            cycles: Arc::clone(&played),
        },
        settings("unisono-test-play", false, cycle),
    )
    .expect("a playback stream");
    let capturing = capture(
        Record {
            cycles: Arc::clone(&recorded),
        },
        settings("unisono-test-capture", true, cycle),
    )
    .expect("a capture stream");
    std::thread::sleep(Duration::from_secs(3));
    capturing.stop().expect("stopping capture stream");
    playing.stop().expect("stopping playback stream");

    let played = played.lock().expect("the played cycles").clone();
    let recorded = recorded.lock().expect("the recorded cycles").clone();
    let min_cycles = (50 * 256 / cycle as usize).max(15);
    assert!(
        played.len() > min_cycles,
        "{} cycles played (expected > {min_cycles})",
        played.len()
    );
    assert!(
        recorded.len() > min_cycles,
        "{} cycles recorded (expected > {min_cycles})",
        recorded.len()
    );

    // Each stream's positions go on without a break, and its times follow
    // them at the rate.
    for cycles in [&played, &recorded] {
        let settled = &cycles[cycles.len() / 4..];
        for pair in settled.windows(2) {
            assert_eq!(
                pair[1].position,
                pair[0].position + pair[0].frames as u64,
                "{pair:?}"
            );
        }
        let (first, last) = (&settled[0], &settled[settled.len() - 1]);
        #[allow(clippy::cast_precision_loss)]
        let expected = (last.position - first.position) as f64 * 1e9 / f64::from(RATE);
        #[allow(clippy::cast_precision_loss)]
        let elapsed = (last.time - first.time) as f64;
        assert!(
            (elapsed - expected).abs() < 1e6,
            "{elapsed} ns for {expected}"
        );
    }

    // A frame of the ramp is captured at the time it is played. A played
    // cycle says when its first frame plays; a recorded cycle whose first
    // sample is a frame of the ramp says when that frame was captured.
    let mut differences = Vec::new();
    for cycle_rec in &recorded[recorded.len() / 4..] {
        let Some(value) = cycle_rec.first.filter(|value| *value > 0.0) else {
            continue;
        };
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let frame = (f64::from(value) * 8_388_608.0).round() as u64 - 1;
        // The played cycle that holds that frame, and when the frame played.
        let mut start = 0u64;
        for played_cycle in &played {
            let end = start + played_cycle.frames as u64;
            if (start..end).contains(&frame) {
                #[allow(clippy::cast_precision_loss)]
                let when =
                    played_cycle.time as f64 + (frame - start) as f64 * 1e9 / f64::from(RATE);
                #[allow(clippy::cast_precision_loss)]
                differences.push(cycle_rec.time as f64 - when);
                break;
            }
            start = end;
        }
    }
    let min_matched = (20 * 256 / cycle as usize).max(10);
    assert!(
        differences.len() > min_matched,
        "{} frames found again (expected > {min_matched})",
        differences.len()
    );
    differences.sort_by(f64::total_cmp);
    let median = differences[differences.len() / 2];
    println!(
        "cycle {cycle}: captured minus played: median {median} ns, from {} to {}",
        differences[0],
        differences[differences.len() - 1]
    );
    assert!(median.abs() < 2e6, "median {median} ns");
}

#[test]
#[ignore = "needs the PipeWire instance of tools/pipewire-test.sh"]
fn a_ramp_played_into_a_sink_is_captured_with_the_times_it_was_played() {
    verify_roundtrip(256);
}

#[test]
#[ignore = "needs the PipeWire instance of tools/pipewire-test.sh"]
fn larger_quantum_and_drop_teardown_work_cleanly() {
    verify_roundtrip(1_024);
    // Dropping a `Running` handle without calling `.stop()` joins cleanly.
    let cycles = Arc::new(Mutex::new(Vec::new()));
    {
        let _playing = play(
            Ramp {
                next: 0,
                cycles: Arc::clone(&cycles),
            },
            settings("unisono-test-drop", false, 512),
        )
        .expect("a playback stream");
        std::thread::sleep(Duration::from_millis(200));
    }
    assert!(!cycles.lock().expect("cycles").is_empty());
}
