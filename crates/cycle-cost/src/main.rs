// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Worst-case instruction-count budget verifier and wall-clock microbenchmark
//! for `unisono` real-time entry points.
//!
//! Each benchmark drives a stream to its worst-case state and measures a
//! single device cycle or packet-ingestion call. Deterministic instruction
//! counts are checked against fixed upper bounds (~25% headroom for toolchain
//! and CPU variance); wall-clock times are reported for diagnostics only.

mod count;
mod scene;

use std::process::ExitCode;
use std::time::Instant;

use scene::Scene;

/// One call to measure: how the stream is brought to its state, and the
/// call.
struct Case {
    name: &'static str,
    /// The most instructions the call may execute.
    budget: u64,
    prepare: fn() -> Scene,
    call: fn(&mut Scene),
}

/// The cases. A stream of 48,000 frames a second in two channels, packets of
/// 240 frames, cycles of 256 frames, a receiver with room for 4,096 frames
/// and 64 samples of the sender's clock.
const CASES: &[Case] = &[
    Case {
        name: "a cycle whose frames are all held",
        budget: 570_000,
        prepare: || Scene::running(|_| false),
        call: Scene::cycle,
    },
    Case {
        name: "a cycle in which a gap begins",
        budget: 1_710_000,
        prepare: || Scene::at_first_concealed(),
        call: Scene::cycle,
    },
    Case {
        name: "a cycle inside a gap",
        budget: 720_000,
        prepare: || {
            let mut scene = Scene::at_first_concealed();
            scene.cycle();
            scene
        },
        call: Scene::cycle,
    },
    Case {
        name: "a packet",
        budget: 110_000,
        prepare: || Scene::running(|_| false),
        call: Scene::packet,
    },
    Case {
        name: "a packet that ends a window of the clock estimate, with a full memory",
        budget: 120_000,
        prepare: Scene::before_window_end,
        call: Scene::packet,
    },
    Case {
        name: "a report of a device and two questions to its line",
        budget: 13_500,
        prepare: || Scene::running(|_| false),
        call: Scene::device,
    },
];

/// The median time of the call of a case over `runs` runs, in nanoseconds.
fn time(case: &Case, runs: usize) -> u128 {
    let mut times: Vec<u128> = (0..runs)
        .map(|_| {
            let mut scene = (case.prepare)();
            let start = Instant::now();
            (case.call)(&mut scene);
            start.elapsed().as_nanos()
        })
        .collect();
    times.sort_unstable();
    times.get(runs / 2).copied().unwrap_or(0)
}

fn main() -> ExitCode {
    let mut within = true;
    println!(
        "{:>12} {:>12} {:>10}  case",
        "instructions", "budget", "time"
    );
    for case in CASES {
        let mut scene = (case.prepare)();
        let counted = match count::instructions(&mut || (case.call)(&mut scene)) {
            Ok(counted) => counted,
            Err(error) => {
                eprintln!("cannot count instructions: {error}");
                return ExitCode::from(2);
            }
        };
        let nanos = time(case, 25);
        println!(
            "{counted:>12} {:>12} {:>7} us  {}",
            case.budget,
            nanos / 1_000,
            case.name
        );
        if case.budget > 0 && counted > case.budget {
            within = false;
        }
    }
    if within {
        ExitCode::SUCCESS
    } else {
        eprintln!("a case executes more instructions than its budget");
        ExitCode::FAILURE
    }
}
