// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The program through PipeWire: a sender that captures a ramp with its
//! software device, a receiver that plays on PipeWire into the sink of
//! `tools/pipewire-test.sh`, and a stream that records what the sink plays,
//! with the times that PipeWire gives it. A frame of the ramp says when it
//! was captured, so each recorded frame says how long after its capture the
//! sink played it: the latency, which is to be the level.
//!
//! The test is ignored unless it is asked for: it needs that PipeWire
//! instance and the program built with PipeWire, at the path that the
//! variable `UNISONO_PROGRAM` of the environment gives.

use std::io::{BufRead, BufReader};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use unisono_pipewire::{Settings, capture};
use unisono_runtime::audio::Capture;
use unisono_runtime::software::Device;

/// The level that the sender announces: 30 ms.
const LEVEL: f64 = 30e6;

/// A cycle that the recording stream was given: when its first frame was
/// captured from the sink, and the frames' first samples.
struct Cycle {
    time: i64,
    samples: Vec<f32>,
}

/// Keeps the cycles of what the sink plays.
struct Record {
    cycles: Arc<Mutex<Vec<Cycle>>>,
}

impl Capture for Record {
    fn channels(&self) -> usize {
        2
    }

    fn cycle(&mut self, frames: &[f32], _: u64, time: i64) {
        if let Ok(mut cycles) = self.cycles.lock() {
            cycles.push(Cycle {
                time,
                samples: frames
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|frame| frame[0])
                    .collect(),
            });
        }
    }
}

/// Starts the program with `arguments` and returns it with the word at
/// place `word` of the first line it writes.
fn start(arguments: &[&str], word: usize) -> (Child, String) {
    let program = std::env::var("UNISONO_PROGRAM").expect("the path of the program");
    let mut child = Command::new(program)
        .args(arguments)
        .stdout(Stdio::piped())
        .spawn()
        .expect("the program starts");
    let mut line = String::new();
    let mut lines = BufReader::new(child.stdout.take().expect("its output"));
    lines.read_line(&mut line).expect("its first line");
    let found = line
        .split_whitespace()
        .nth(word)
        .unwrap_or_else(|| panic!("the program said `{line}`"))
        .to_owned();
    child.stdout = Some(lines.into_inner());
    (child, found)
}

#[test]
#[ignore = "needs the PipeWire instance of tools/pipewire-test.sh and the program"]
fn the_program_plays_through_pipewire_a_level_after_the_capture() {
    // "listening ADDRESS"
    let (mut receiver, address) = start(
        &[
            "receive",
            "--listen",
            "127.0.0.1:0",
            "--audio",
            "pipewire",
            "--device",
            "unisono-test-sink",
            "--seconds",
            "9",
        ],
        1,
    );
    // "capture start S rate R drift D cycle C"
    let (mut sender, began) = start(
        &[
            "send",
            "--to",
            &address,
            "--signal",
            "ramp",
            "--level",
            "30",
            "--level-choice",
            "off",
            "--seconds",
            "8",
        ],
        2,
    );
    let began: i64 = began.parse().expect("the start of the capture");
    let recorded = Arc::new(Mutex::new(Vec::new()));
    let recording = capture(
        Record {
            cycles: Arc::clone(&recorded),
        },
        Settings {
            name: "unisono-test-record".into(),
            rate: 48_000,
            channels: 2,
            target: Some("unisono-test-sink".into()),
            monitor: true,
            largest_cycle: 8_192,
            cycle: 256,
        },
    )
    .expect("a capture stream");
    std::thread::sleep(Duration::from_secs(7));
    recording.stop();
    assert!(sender.wait().expect("the sender ends").success());
    assert!(receiver.wait().expect("the receiver ends").success());

    // The sender's capture device, as the program makes it.
    let device = Device {
        rate: 48_000,
        channels: 2,
        cycle: 256,
        drift: 0,
        start: began,
        lead: 1_000_000,
        hidden: 0,
    };
    let recorded = recorded.lock().expect("the recorded cycles");
    // How far from the level the latency of each frame is, in nanoseconds,
    // of the frames recorded from four seconds after the capture began.
    let mut errors = Vec::new();
    for cycle in recorded.iter() {
        if cycle.time < began + 4_000_000_000 {
            continue;
        }
        for (place, sample) in cycle.samples.iter().enumerate() {
            if *sample <= 0.0 {
                continue;
            }
            // The frame of the ramp, which the resampler gives between two
            // of the frames that were captured.
            let position = f64::from(*sample) * 8_388_608.0 - 1.0;
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let whole = position.floor() as u64;
            let (before, after) = (device.captured(whole), device.captured(whole + 1));
            #[allow(clippy::cast_precision_loss)]
            let taken = before as f64 + (after - before) as f64 * position.fract();
            #[allow(clippy::cast_precision_loss)]
            let played = cycle.time as f64 + place as f64 * 1e9 / 48_000.0;
            errors.push(played - taken - LEVEL);
        }
    }
    assert!(
        errors.len() > 100_000,
        "{} frames of the ramp",
        errors.len()
    );
    errors.sort_by(f64::total_cmp);
    let (low, median, high) = (
        errors[errors.len() / 50],
        errors[errors.len() / 2],
        errors[errors.len() * 49 / 50],
    );
    println!("latency less the level: {low} ns, {median} ns, {high} ns");
    assert!(low > -50e3 && high < 50e3, "from {low} to {high} ns");
}
