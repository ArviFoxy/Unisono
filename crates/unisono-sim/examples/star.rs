// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Prints the numbers of `docs/star-optimum.tex`: the baseline against the
//! best estimate with the law, synchronization with and without the
//! sender's broadcast, and the latency level from the holds.
//!
//! Run with `cargo run --release -p unisono-sim --example star`.

use unisono_sim::link::LinkModel;
use unisono_sim::star::{
    Comparison, FrequencyNoise, Kinds, ReceiverSetting, broadcast_comparison, campbell_fraction,
    compare, hold_margin, late_fraction,
};

/// A switched wired link with little other traffic.
const WIRED: LinkModel = LinkModel {
    minimum: 100e-6,
    clear_excess: 5e-6,
    queued: 0.1,
    queued_excess: 200e-6,
    pause_rate: 0.0,
    pause_length: 0.0,
    overtaken: 0.0,
    overtaken_excess: 0.0,
};

/// A wireless link whose medium is busy half of the time and which holds
/// everything for about 30 ms every 20 seconds.
const WIRELESS: LinkModel = LinkModel {
    minimum: 1e-3,
    clear_excess: 300e-6,
    queued: 0.5,
    queued_excess: 3e-3,
    pause_rate: 1.0 / 20.0,
    pause_length: 30e-3,
    overtaken: 0.0,
    overtaken_excess: 0.0,
};

/// A quartz oscillator: white frequency noise of `2e-18` per hertz, an Allan
/// deviation of `1e-9` at one second, and a frequency random walk of
/// `1e-18` per second.
const QUARTZ: FrequencyNoise = FrequencyNoise {
    white: 2e-18,
    walk: 1e-18,
};

/// An oscillator whose frequency wanders a hundred times faster, as one that
/// heats and cools does.
const WANDERING: FrequencyNoise = FrequencyNoise {
    white: 2e-18,
    walk: 1e-16,
};

fn wired() -> ReceiverSetting {
    ReceiverSetting {
        link: WIRED,
        clock: QUARTZ,
        measurement_variance: (3e-6_f64).powi(2),
    }
}

fn wireless() -> ReceiverSetting {
    ReceiverSetting {
        link: WIRELESS,
        clock: QUARTZ,
        measurement_variance: (150e-6_f64).powi(2),
    }
}

fn comparison(receivers: Vec<ReceiverSetting>) -> Comparison {
    Comparison {
        cycle: 0.01,
        period: 0.25,
        group: 8,
        duration: 600.0,
        warmup: 60.0,
        slew: 1e-3,
        gain: 0.05,
        sender: QUARTZ,
        receivers,
    }
}

fn main() {
    println!("baseline against the best estimate with the law (microseconds, parts per million)");
    println!(
        "setting          | spread base  best | error base  best | speed rms base  best | speed max base  best"
    );
    let settings = [
        ("two wired", vec![wired(), wired()]),
        ("two wireless", vec![wireless(), wireless()]),
        (
            "three wired, two wireless",
            vec![wired(), wired(), wired(), wireless(), wireless()],
        ),
    ];
    for (name, receivers) in settings {
        let (base, best) = compare(&comparison(receivers), 7);
        println!(
            "{name:28} | {:9.1} {:7.2} | {:9.1} {:7.2} | {:9.1} {:9.3} | {:9.1} {:9.3}",
            base.spread * 1e6,
            best.spread * 1e6,
            base.error * 1e6,
            best.error * 1e6,
            base.speed_change * 1e6,
            best.speed_change * 1e6,
            base.largest_speed_change * 1e6,
            best.largest_speed_change * 1e6,
        );
    }

    println!();
    println!(
        "synchronization of three wired and two wireless receivers, second-order model (microseconds)"
    );
    println!(
        "sender's clock | all: own  broadcast | wired pairs: own  broadcast | mixed pairs: own  broadcast"
    );
    let kinds = Kinds {
        first: 3,
        second: 2,
        first_error: 3e-6,
        second_error: 150e-6,
    };
    for (name, sender) in [("quartz", QUARTZ), ("wandering", WANDERING)] {
        let (own, shared) = broadcast_comparison(kinds, sender, QUARTZ, 2.0, 200_000, 11);
        println!(
            "{name:14} | {:8.2} {:8.2} | {:8.2} {:8.2} | {:8.2} {:8.2}",
            own.all * 1e6,
            shared.all * 1e6,
            own.first_kind * 1e6,
            shared.first_kind * 1e6,
            own.mixed * 1e6,
            shared.mixed * 1e6,
        );
    }

    println!();
    println!("latency margin from the holds: one hold of 30 ms on average every 20 s");
    println!("price ratio | margin (ms) | late fraction: Campbell  simulated");
    for ratio in [1e-2, 1e-3, 1e-4] {
        let margin = hold_margin(WIRELESS.pause_rate, WIRELESS.pause_length, ratio);
        let predicted = campbell_fraction(WIRELESS.pause_rate, WIRELESS.pause_length, margin);
        // The link releases what it held all at once when a hold ends, so a
        // packet sent during a hold is late by what remains of the hold.
        let simulated = late_fraction(WIRELESS, 0.01, 200_000.0, margin, 3);
        println!(
            "{ratio:11.0e} | {:11.1} | {:18.2e} {:10.2e}",
            margin * 1e3,
            predicted,
            simulated
        );
    }
}
