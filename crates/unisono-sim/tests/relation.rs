// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The estimator of a clock relation against simulated senders, receivers
//! and links.
//!
//! Each test names the assumptions it runs under and a largest error it
//! accepts. For each such bound a second test shows that an estimator with a
//! plausible defect exceeds it, so that the bound is known to be able to fail.

use unisono_core::relation::{Estimator, Sample};
use unisono_sim::assumptions::{OneWayAssumptions, WIRED_BUSY, WIRED_CALM, WIRELESS};
use unisono_sim::packets::{OneWay, Packet};
use unisono_sim::random::Generator;

/// Packets per window, and how long samples are remembered: 64 packets are
/// 85 ms at 750 packets a second, and 128 windows of them are 11 s.
const WINDOW: u64 = 64;
const SPAN: i64 = 11_000_000_000;

/// The largest slope the estimate may take: 200 parts per million, twice what
/// an oscillator may be off by.
const LIMIT: i64 = 200_000;

/// What an estimator under test does with a packet: it returns its estimate
/// of the undelayed relation at the packet's time, once it has one.
trait UnderTest {
    fn packet(&mut self, packet: &Packet) -> Option<i64>;
}

/// The estimator of the core, as it is meant to be used.
struct Core(Estimator<128>);

impl UnderTest for Core {
    fn packet(&mut self, packet: &Packet) -> Option<i64> {
        let sample = Sample {
            time: packet.sent,
            value: packet.received - packet.sent,
        };
        self.0.observe(packet.number / WINDOW, sample);
        self.0.line().map(|line| line.eval(packet.sent))
    }
}

/// The same estimator fed the first packet of every window instead of the
/// lowest: what a mistake in the selection would do.
struct FirstOfWindow(Estimator<128>);

impl UnderTest for FirstOfWindow {
    fn packet(&mut self, packet: &Packet) -> Option<i64> {
        if packet.number.is_multiple_of(WINDOW) {
            let sample = Sample {
                time: packet.sent,
                value: packet.received - packet.sent,
            };
            self.0.observe(packet.number / WINDOW, sample);
        }
        self.0.line().map(|line| line.eval(packet.sent))
    }
}

/// The same estimator fed the mean of every window instead of its lowest
/// packet: what treating a delay as an error of either sign would do.
struct MeanOfWindow {
    estimator: Estimator<128>,
    sum: i64,
}

impl UnderTest for MeanOfWindow {
    fn packet(&mut self, packet: &Packet) -> Option<i64> {
        self.sum += packet.received - packet.sent;
        if (packet.number + 1).is_multiple_of(WINDOW) {
            let mean = self.sum / i64::try_from(WINDOW).unwrap_or(1);
            self.estimator.observe(
                packet.number / WINDOW,
                Sample {
                    time: packet.sent,
                    value: mean,
                },
            );
            self.sum = 0;
        }
        self.estimator.line().map(|line| line.eval(packet.sent))
    }
}

/// The largest error of `estimator`, in nanoseconds, over `seconds` of
/// packets, not counting the first 30 s. `disturb` may act on the path before
/// each packet.
fn largest_error(
    assumptions: &OneWayAssumptions,
    seed: u64,
    seconds: f64,
    estimator: &mut dyn UnderTest,
    disturb: &mut dyn FnMut(&mut OneWay, u64),
) -> f64 {
    let mut path = OneWay::new(assumptions, &Generator::new(seed));
    let mut largest = 0.0f64;
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let packets = (seconds * assumptions.packet_rate) as u64;
    for number in 0..packets {
        disturb(&mut path, number);
        let packet = path.send();
        if let Some(estimate) = estimator.packet(&packet)
            && packet.left.seconds() > 30.0
        {
            #[allow(clippy::cast_precision_loss)]
            let error = estimate as f64 - packet.undelayed;
            largest = largest.max(error.abs());
        }
    }
    largest
}

fn undisturbed(_: &mut OneWay, _: u64) {}

fn core() -> Core {
    Core(Estimator::new(SPAN, LIMIT))
}

#[test]
fn on_a_calm_wired_link_the_error_stays_under_a_microsecond() {
    let error = largest_error(&WIRED_CALM, 1, 600.0, &mut core(), &mut undisturbed);
    assert!(error < 1_000.0, "largest error {error} ns");
}

#[test]
fn the_calm_wired_bound_fails_for_an_estimator_that_averages() {
    let mut defective = MeanOfWindow {
        estimator: Estimator::new(SPAN, LIMIT),
        sum: 0,
    };
    let error = largest_error(&WIRED_CALM, 1, 600.0, &mut defective, &mut undisturbed);
    assert!(
        error > 1_000.0,
        "the defect went unnoticed: largest error {error} ns"
    );
}

#[test]
fn a_step_of_the_senders_frequency_keeps_the_error_under_a_microsecond() {
    // One part per million, five minutes in.
    let mut step = |path: &mut OneWay, number: u64| {
        if number == 300 * 750 {
            path.step_sender_frequency(1e-6);
        }
    };
    let error = largest_error(&WIRED_CALM, 2, 600.0, &mut core(), &mut step);
    assert!(error < 1_000.0, "largest error {error} ns");
}

#[test]
fn on_a_busy_wired_link_the_error_stays_under_three_microseconds() {
    let error = largest_error(&WIRED_BUSY, 3, 600.0, &mut core(), &mut undisturbed);
    assert!(error < 3_000.0, "largest error {error} ns");
}

#[test]
fn on_a_wireless_link_with_pauses_the_error_stays_under_fifty_microseconds() {
    let error = largest_error(&WIRELESS, 4, 1800.0, &mut core(), &mut undisturbed);
    assert!(error < 50_000.0, "largest error {error} ns");
}

#[test]
fn the_wireless_bound_fails_for_an_estimator_that_does_not_select() {
    let mut defective = FirstOfWindow(Estimator::new(SPAN, LIMIT));
    let error = largest_error(&WIRELESS, 4, 1800.0, &mut defective, &mut undisturbed);
    assert!(
        error > 50_000.0,
        "the defect went unnoticed: largest error {error} ns"
    );
}
