// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Streams through a running PipeWire, which `tools/pipewire-test.sh` starts
//! with a sink named `unisono-test-sink` that plays to nothing. The tests are
//! ignored unless they are asked for, because they need that instance.
//!
//! A playback stream plays a ramp, whose sample says which frame it is, into
//! the sink, and a capture stream records what the sink plays. The positions
//! and times that PipeWire reports to both are held against each other.

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

fn settings(name: &str, monitor: bool) -> Settings {
    Settings {
        name: name.into(),
        rate: RATE,
        channels: 2,
        target: Some("unisono-test-sink".into()),
        monitor,
        largest_cycle: 8_192,
        cycle: 256,
    }
}

#[test]
#[ignore = "needs the PipeWire instance of tools/pipewire-test.sh"]
fn a_ramp_played_into_a_sink_is_captured_with_the_times_it_was_played() {
    let played = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::new(Mutex::new(Vec::new()));
    let playing = play(
        Ramp {
            next: 0,
            cycles: Arc::clone(&played),
        },
        settings("unisono-test-play", false),
    )
    .expect("a playback stream");
    let capturing = capture(
        Record {
            cycles: Arc::clone(&recorded),
        },
        settings("unisono-test-capture", true),
    )
    .expect("a capture stream");
    std::thread::sleep(Duration::from_secs(3));
    capturing.stop();
    playing.stop();

    let played = played.lock().expect("the played cycles").clone();
    let recorded = recorded.lock().expect("the recorded cycles").clone();
    assert!(played.len() > 50, "{} cycles played", played.len());
    assert!(recorded.len() > 50, "{} cycles recorded", recorded.len());

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
    for cycle in &recorded[recorded.len() / 4..] {
        let Some(value) = cycle.first.filter(|value| *value > 0.0) else {
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
                differences.push(cycle.time as f64 - when);
                break;
            }
            start = end;
        }
    }
    assert!(
        differences.len() > 20,
        "{} frames found again",
        differences.len()
    );
    differences.sort_by(f64::total_cmp);
    let median = differences[differences.len() / 2];
    println!(
        "captured minus played: median {median} ns, from {} to {}",
        differences[0],
        differences[differences.len() - 1]
    );
    assert!(median.abs() < 2e6, "median {median} ns");
}
