// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Checks of the simulation of receivers that exchange messages only with
//! the sender, against the statements of `docs/star-optimum.tex`.

use unisono_sim::link::LinkModel;
use unisono_sim::star::{
    Comparison, FrequencyNoise, Kinds, OffsetFilter, ReceiverSetting, broadcast_comparison,
    campbell_fraction, compare, late_fraction,
};

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

const QUARTZ: FrequencyNoise = FrequencyNoise {
    white: 2e-18,
    walk: 1e-18,
};

/// The best estimate with the law synchronizes a mix of wired and wireless
/// receivers several times better than the baseline, and changes the speed
/// far less. Fails if the front end, the filter or the law stops working.
#[test]
fn best_estimate_beats_the_baseline() {
    let wired = ReceiverSetting {
        link: WIRED,
        clock: QUARTZ,
        measurement_variance: (3e-6_f64).powi(2),
    };
    let wireless = ReceiverSetting {
        link: WIRELESS,
        clock: QUARTZ,
        measurement_variance: (150e-6_f64).powi(2),
    };
    let setting = Comparison {
        cycle: 0.01,
        period: 0.25,
        group: 8,
        duration: 600.0,
        warmup: 120.0,
        slew: 1e-3,
        gain: 0.05,
        sender: QUARTZ,
        receivers: vec![wired, wired, wireless],
    };
    let (base, best) = compare(&setting, 7);
    assert!(best.spread * 5.0 < base.spread, "{best:?} against {base:?}");
    assert!(best.error * 5.0 < base.error, "{best:?} against {base:?}");
    assert!(
        best.largest_speed_change * 100.0 < base.largest_speed_change,
        "{best:?} against {base:?}"
    );
}

/// With the broadcast, the sender's clock does not enter the spread: the
/// spreads are the same for a quartz sender and for one whose frequency
/// wanders a hundred times faster. Without it, the wandering sender widens
/// the spread. Fails if the cancellation identity stops holding.
#[test]
fn the_broadcast_cancels_the_senders_clock() {
    let kinds = Kinds {
        first: 3,
        second: 2,
        first_error: 3e-6,
        second_error: 150e-6,
    };
    let wandering = FrequencyNoise {
        white: 2e-18,
        walk: 1e-16,
    };
    let (own_quartz, shared_quartz) = broadcast_comparison(kinds, QUARTZ, QUARTZ, 2.0, 50_000, 11);
    let (own_wandering, shared_wandering) =
        broadcast_comparison(kinds, wandering, QUARTZ, 2.0, 50_000, 11);
    assert!((shared_quartz.all - shared_wandering.all).abs() < 1e-3 * shared_quartz.all);
    assert!(own_wandering.all > 1.2 * own_quartz.all);
    assert!(shared_wandering.all < own_wandering.all);
}

/// The fraction of a stream's packets that a link with exponential holds
/// makes late by more than the margin is Campbell's `rate * mean *
/// exp(-margin / mean)`. Fails if the hold model or the level rule's cost is
/// wrong.
#[test]
fn late_packets_follow_campbell() {
    let margin = 48e-3;
    let predicted = campbell_fraction(WIRELESS.pause_rate, WIRELESS.pause_length, margin);
    let simulated = late_fraction(WIRELESS, 0.01, 50_000.0, margin, 3);
    assert!(
        (simulated - predicted).abs() < 0.2 * predicted,
        "simulated {simulated}, predicted {predicted}"
    );
}

/// The Kalman filter's steady state for a random walk measured with white
/// noise has the closed form that `Unisono.Solutions.Star.Spectral` checks:
/// the estimate errs with variance `r (1 - a)`, where `a` is the root in
/// `(0, 1)` of `a² - (2 + q / r) a + 1 = 0`. Fails if the filter's
/// equations are wrong.
#[test]
fn the_filter_reaches_the_closed_form() {
    let step_variance = 4e-12;
    let measurement_variance = 9e-12;
    let noise = FrequencyNoise {
        white: 2.0 * step_variance,
        walk: 0.0,
    };
    let mut filter = OffsetFilter::new(0.0, 1.0, 0.0, noise);
    for _ in 0..1000 {
        filter.predict(1.0);
        filter.update(0.0, 0.0, measurement_variance);
    }
    let s = step_variance / measurement_variance;
    let a = 1.0 + s / 2.0 - (s + (s / 2.0) * (s / 2.0)).sqrt();
    let closed = measurement_variance * (1.0 - a);
    assert!(
        (filter.offset_variance() - closed).abs() < 1e-9 * closed,
        "{} against {closed}",
        filter.offset_variance()
    );
}
