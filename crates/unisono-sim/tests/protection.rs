// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Which way of protecting a stream against lost packets suits which path.
//!
//! Each way is run over the same outages of a path, and what the stream
//! then costs at its best level is held against the others, with the
//! weights that the program takes when none are given: a gap costs as much
//! as a millisecond of level held for ten minutes, and a millisecond of
//! frames missed as much as a millisecond of level held for one minute.

use unisono_sim::protection::{Path, Run, Scheme, Verdict, evaluate, simulate};
use unisono_sim::random::Generator;

/// A packet every 5 ms.
const PERIOD: f64 = 0.005;

/// The schemes that are compared, with a name for each.
fn schemes() -> Vec<(&'static str, Scheme)> {
    let request = |unheard| Scheme::Request {
        again: 0.01,
        patience: 0.5,
        unheard,
    };
    let copy = |delay| Scheme::Copy { delay };
    let block = |data, parity, delay| Scheme::Block {
        data,
        parity,
        delay,
    };
    let burst = |burst, wait| Scheme::Burst { burst, wait };
    vec![
        ("nothing", Scheme::None),
        ("copy after 20 ms", copy(0.02)),
        ("copy after 40 ms", copy(0.04)),
        ("copy after 80 ms", copy(0.08)),
        ("sum of 4", block(4, 1, 0.0)),
        ("4 and 2, at once", block(4, 2, 0.0)),
        ("4 and 4, after 40 ms", block(4, 4, 0.04)),
        ("8 and 8, after 80 ms", block(8, 8, 0.08)),
        ("bursts of 4 in 8", burst(4, 8)),
        ("bursts of 4 in 16", burst(4, 16)),
        ("bursts of 8 in 16", burst(8, 16)),
        ("bursts of 16 in 32", burst(16, 32)),
        ("asked for again", request(0.0)),
        ("asked, half unheard", request(0.5)),
    ]
}

/// What each scheme gives on `path` over `seconds` seconds: its name, what
/// it adds for each packet of the stream, and the verdict.
fn compare(path: Path, seconds: f64, seed: u64) -> Vec<(&'static str, f64, Verdict)> {
    // A count of packets, far below 2^32.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let packets = (seconds / PERIOD) as usize;
    schemes()
        .into_iter()
        .map(|(name, scheme)| {
            // The same outages for every scheme.
            let mut run = Run::new(path, seconds, Generator::new(seed));
            let outcome = simulate(scheme, &mut run, packets, PERIOD);
            let verdict = evaluate(&outcome.needs, PERIOD, 0.4, 1_000.0, 600.0, 60_000.0);
            (name, outcome.added, verdict)
        })
        .collect()
}

fn show(title: &str, results: &[(&'static str, f64, Verdict)]) {
    println!("{title}");
    for (name, added, verdict) in results {
        println!(
            "  {name:<22} adds {:>5.1}%  level {:>3.0} ms  cost {:>7.2}  gaps {:>6.2}/min  missed {:.4}%",
            added * 100.0,
            verdict.level * 1e3,
            verdict.cost,
            verdict.gaps * 60.0,
            verdict.missed * 100.0
        );
    }
}

/// The cost of the scheme called `name` among `results`.
fn cost(results: &[(&'static str, f64, Verdict)], name: &str) -> f64 {
    results
        .iter()
        .find(|(found, _, _)| *found == name)
        .map_or(f64::NAN, |(_, _, verdict)| verdict.cost)
}

#[test]
fn asking_again_costs_least_wherever_packets_are_lost() {
    // A wired path loses one packet in ten million and has no outages.
    let wired = Path {
        minimum: 100e-6,
        excess: 100e-6,
        outage_rate: 0.0,
        outage_length: 0.0,
        stray: 1e-7,
    };
    // A wireless path: outages of 19 ms on average, the length of the
    // bursts of loss seen on such a link, and one packet in ten thousand
    // lost on its own.
    let wireless = Path {
        minimum: 1e-3,
        excess: 1.5e-3,
        outage_rate: 0.1,
        outage_length: 0.019,
        stray: 1e-4,
    };
    let busy = Path {
        outage_rate: 0.5,
        ..wireless
    };
    let long = Path {
        outage_rate: 1.0 / 30.0,
        outage_length: 0.1,
        ..wireless
    };

    let results = compare(wired, 1_800.0, 11);
    show("wired", &results);
    // Nothing is lost, and nothing is gained.
    let nothing = cost(&results, "nothing");
    for (name, _, verdict) in &results {
        assert!(verdict.cost >= nothing, "{name} on the wired path");
    }

    for (title, path, seconds, seed) in [
        (
            "wireless: an outage of 19 ms every 10 s",
            wireless,
            1_800.0,
            12,
        ),
        ("wireless: an outage of 19 ms every 2 s", busy, 1_800.0, 13),
        (
            "wireless: an outage of 100 ms every 30 s",
            long,
            3_600.0,
            14,
        ),
    ] {
        let results = compare(path, seconds, seed);
        show(title, &results);
        let asked = cost(&results, "asked for again");
        let unheard = cost(&results, "asked, half unheard");
        for (name, added, verdict) in &results {
            if name.starts_with("asked") {
                // A hundredth or two of the stream is sent again.
                assert!(*added < 0.03, "{name} on {title} adds {added}");
            } else {
                // No code and no copy costs less, though each adds a
                // quarter of the stream or more. When half of the requests
                // are lost on the way back, the best of them costs less,
                // but not by much: asking then costs at most a third more.
                assert!(verdict.cost >= asked, "{name} on {title}");
                assert!(verdict.cost * 4.0 >= unheard * 3.0, "{name} on {title}");
            }
        }
        assert!(asked < 0.75 * cost(&results, "nothing"), "{title}");
    }
}
