// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! An ALSA device that is PipeWire's device for ALSA programs, in the
//! instance that `tools/alsa-test.sh` starts with a sink named
//! `unisono-test-sink` that plays to nothing. The tests are ignored unless
//! they are asked for, because they need that instance.
//!
//! A ramp, whose sample says which frame it is, is played on the ALSA
//! device, and a PipeWire stream records what the sink plays. Then the
//! other way: a PipeWire stream plays the ramp into the sink and the ALSA
//! device captures what the sink plays.

use std::sync::{Arc, Mutex};
use std::time::Duration;

use unisono_alsa::Settings;
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

/// The ALSA device that plays to the sink or captures what it plays.
fn device() -> Settings {
    Settings {
        device: "pipewire:NODE=unisono-test-sink".into(),
        rate: RATE,
        channels: 2,
        cycle: 256,
        cycles: 4,
    }
}

/// A PipeWire stream at the sink; `monitor` for one that captures what the
/// sink plays.
fn stream(name: &str, monitor: bool) -> unisono_pipewire::Settings {
    unisono_pipewire::Settings {
        name: name.into(),
        rate: RATE,
        channels: 2,
        target: Some("unisono-test-sink".into()),
        monitor,
        largest_cycle: 8_192,
        cycle: 256,
    }
}

/// Holds the cycles of a stream that played a ramp against those of a
/// stream that recorded it: each stream's positions go on without a break
/// and its times follow them at the rate, the frames recorded are those
/// played, in order, and a frame is recorded within `bound` nanoseconds of
/// when it was played.
fn hold(played: &[Cycle], recorded: &[Cycle], bound: f64) {
    assert!(played.len() > 50, "{} cycles played", played.len());
    assert!(recorded.len() > 50, "{} cycles recorded", recorded.len());
    for cycles in [played, recorded] {
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
            (elapsed - expected).abs() < 5e6,
            "{elapsed} ns for {expected}"
        );
    }
    // The frames recorded follow each other as they were played.
    let frame = |cycle: &Cycle| {
        cycle.first.filter(|value| *value > 0.0).map(|value| {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let frame = (f64::from(value) * 8_388_608.0).round() as u64 - 1;
            frame
        })
    };
    let settled = &recorded[recorded.len() / 4..];
    for pair in settled.windows(2) {
        if let (Some(first), Some(second)) = (frame(&pair[0]), frame(&pair[1])) {
            assert_eq!(second, first + pair[0].frames as u64, "{pair:?}");
        }
    }
    let mut differences = Vec::new();
    for cycle in settled {
        let Some(frame) = frame(cycle) else {
            continue;
        };
        let mut start = 0u64;
        for played_cycle in played {
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
    assert!(median.abs() < bound, "median {median} ns");
}

#[test]
#[ignore = "needs the PipeWire instance of tools/alsa-test.sh"]
fn a_ramp_played_on_the_device_is_what_the_sink_plays() {
    let played = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::new(Mutex::new(Vec::new()));
    let playing = unisono_alsa::play(
        Ramp {
            next: 0,
            cycles: Arc::clone(&played),
        },
        &device(),
    )
    .expect("an ALSA device that plays");
    let capturing = unisono_pipewire::capture(
        Record {
            cycles: Arc::clone(&recorded),
        },
        stream("unisono-test-capture", true),
    )
    .expect("a capture stream");
    std::thread::sleep(Duration::from_secs(3));
    capturing.stop();
    playing.stop();
    let played = played.lock().expect("the played cycles").clone();
    let recorded = recorded.lock().expect("the recorded cycles").clone();
    hold(&played, &recorded, 500e3);
}

#[test]
#[ignore = "needs the PipeWire instance of tools/alsa-test.sh"]
fn what_the_sink_plays_is_captured_on_the_device() {
    let played = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::new(Mutex::new(Vec::new()));
    let playing = unisono_pipewire::play(
        Ramp {
            next: 0,
            cycles: Arc::clone(&played),
        },
        stream("unisono-test-play", false),
    )
    .expect("a playback stream");
    let capturing = unisono_alsa::capture(
        Record {
            cycles: Arc::clone(&recorded),
        },
        &device(),
    )
    .expect("an ALSA device that captures");
    std::thread::sleep(Duration::from_secs(3));
    capturing.stop();
    playing.stop();
    let played = played.lock().expect("the played cycles").clone();
    let recorded = recorded.lock().expect("the recorded cycles").clone();
    hold(&played, &recorded, 500e3);
}

#[test]
#[ignore = "needs the PipeWire instance of tools/alsa-test.sh"]
fn alsa_device_reports_cycle_and_realtime_and_restarts_cleanly_on_drop() {
    for round in 0..2 {
        let cycles = Arc::new(Mutex::new(Vec::new()));
        let running = unisono_alsa::play(
            Ramp {
                next: 0,
                cycles: Arc::clone(&cycles),
            },
            &device(),
        )
        .expect("an ALSA playback device");
        assert!(running.cycle() > 0, "round {round}: negotiated cycle");
        // Deterministic after the startup handshake (never races).
        let _ = running.realtime();
        std::thread::sleep(Duration::from_millis(250));
        // Drop without calling `.stop()` must stop and join cleanly.
        drop(running);
        assert!(
            !cycles.lock().expect("cycles").is_empty(),
            "round {round}: expected playback cycles"
        );
    }
}
