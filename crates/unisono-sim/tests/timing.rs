// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Playback timing of receivers against a simulated sender, links, clocks
//! and devices.
//!
//! Clocks differ by hours and by tens of parts per million, devices by up to
//! 120 parts per million from their hosts' clocks, and all of them wander.
//! Each test names the assumptions about the links it runs under and the
//! largest timing error it accepts. Two tests seed a fault and show that the
//! error then leaves the bound.
//!
//! What these tests assume besides the links: stamps of departure and
//! arrival are exact, every receiver knows the true time of its device's
//! cycles on its own clock, and, except where a test says otherwise, the
//! smallest delay of its link. They show that the estimate of the sender's
//! clock, the schedule and the regulator fit together; they do not show what
//! a real device and a real network allow.

use unisono_core::player::Regulation;
use unisono_sim::TrueTime;
use unisono_sim::assumptions::{WIRED_BUSY, WIRED_CALM, WIRELESS};
use unisono_sim::clock::OscillatorModel;
use unisono_sim::link::LinkModel;
use unisono_sim::random::Generator;
use unisono_sim::stream::{
    CycleLength, HostModel, PathDelay, ReceiverModel, Scene, SenderModel, Trace,
};

fn oscillator(offset: f64, parts_per_million: f64, walk: f64) -> OscillatorModel {
    OscillatorModel {
        offset,
        frequency: parts_per_million * 1e-6,
        walk,
    }
}

fn sender(walk: f64, level_ms: i64) -> SenderModel {
    SenderModel {
        clock: oscillator(1_000.0, 20.0, walk),
        device: oscillator(0.0, -35.0, walk),
        rate: 48_000,
        packet_frames: 240,
        level: level_ms * 1_000_000,
        send_delay: 50e-6,
        span: 11_000,
        window: 15_360,
    }
}

fn receiver(host: usize, device_ppm: f64, walk: f64) -> ReceiverModel {
    ReceiverModel {
        host,
        device: oscillator(0.0, device_ppm, walk),
        cycle_frames: 256,
        lead: 8e-3,
        regulation: Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: 240,
        },
        silence: 1_000_000_000,
        slope_limit: 200_000,
        path: PathDelay::Told,
        cycle_length: CycleLength::Measured,
    }
}

fn hosts(link: LinkModel, walk: f64) -> Vec<HostModel> {
    [(5_000.0, -40.0), (-7_200.0, 15.0), (86_400.0, 60.0)]
        .iter()
        .map(|(offset, ppm)| HostModel {
            clock: oscillator(*offset, *ppm, walk),
            link,
            back: link,
        })
        .collect()
}

/// The largest size of the timing error after `from` seconds, in seconds.
fn worst(trace: &Trace, from: f64) -> f64 {
    trace
        .errors
        .iter()
        .filter(|(at, _)| *at >= from)
        .map(|(_, error)| error.abs())
        .fold(0.0, f64::max)
}

/// The largest difference between the timing errors of two receivers after
/// `from` seconds, in seconds: each error of the first against the error of
/// the second that is nearest in time.
fn apart(first: &Trace, second: &Trace, from: f64) -> f64 {
    let mut largest = 0.0f64;
    let mut index = 0;
    for (at, error) in first.errors.iter().filter(|(at, _)| *at >= from) {
        while index + 1 < second.errors.len() && second.errors[index + 1].0 <= *at {
            index += 1;
        }
        if let Some((_, other)) = second.errors.get(index) {
            largest = largest.max((error - other).abs());
        }
    }
    largest
}

/// A scene of four receivers on three hosts, the last two on one host, with
/// links and wander as `assumptions` says.
fn scene(
    assumptions: &unisono_sim::assumptions::OneWayAssumptions,
    level_ms: i64,
    change: impl Fn(&mut [ReceiverModel; 4]),
) -> Scene {
    let walk = assumptions.frequency_walk;
    let mut receivers = [
        receiver(0, 80.0, walk),
        receiver(1, -120.0, walk),
        receiver(2, 10.0, walk),
        receiver(2, -60.0, walk),
    ];
    change(&mut receivers);
    Scene::new(
        sender(walk, level_ms),
        &hosts(assumptions.link, walk),
        &receivers,
        &Generator::new(11),
    )
}

/// The largest timing error of any receiver, and the largest difference
/// between any two, after `from` seconds.
fn worst_and_apart(scene: &Scene, from: f64) -> (f64, f64) {
    let traces = scene.traces();
    let mut worst_of_all = 0.0f64;
    let mut apart_of_all = 0.0f64;
    for (number, trace) in traces.iter().enumerate() {
        worst_of_all = worst_of_all.max(worst(trace, from));
        for other in traces.iter().skip(number + 1) {
            apart_of_all = apart_of_all.max(apart(trace, other, from));
        }
    }
    (worst_of_all, apart_of_all)
}

const MICROSECOND: f64 = 1e-6;

/// The bound for a calm wired link, which the tests with a seeded fault use
/// too.
const CALM_BOUND: f64 = 0.25 * MICROSECOND;

#[test]
fn on_a_calm_wired_link_receivers_play_within_a_quarter_microsecond() {
    let mut scene = scene(&WIRED_CALM, 20, |_| {});
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < CALM_BOUND, "worst {worst}");
    assert!(apart < CALM_BOUND, "apart {apart}");
    for trace in scene.traces() {
        // One jump, at the start; and after the first packets no frame is
        // missing when it is due.
        assert_eq!(trace.jumps.len(), 1);
        assert!(trace.absent < 1_000, "absent {}", trace.absent);
    }
}

#[test]
fn on_a_busy_wired_link_receivers_play_within_a_microsecond_and_a_half() {
    let mut scene = scene(&WIRED_BUSY, 60, |_| {});
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 1.5 * MICROSECOND, "worst {worst}");
    assert!(apart < 1.5 * MICROSECOND, "apart {apart}");
}

#[test]
fn on_a_wireless_link_with_pauses_receivers_play_within_twenty_five_microseconds() {
    let mut scene = scene(&WIRELESS, 60, |_| {});
    scene.run(TrueTime::from_seconds(120.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 25.0 * MICROSECOND, "worst {worst}");
    assert!(apart < 25.0 * MICROSECOND, "apart {apart}");
}

#[test]
fn receivers_on_one_host_play_within_fifty_nanoseconds_of_each_other() {
    // They have the same estimate of the sender's clock, so only their
    // devices and regulators differ.
    let mut scene = scene(&WIRED_BUSY, 60, |_| {});
    scene.run(TrueTime::from_seconds(60.0));
    let traces = scene.traces();
    let together = apart(traces[2], traces[3], 5.0);
    assert!(together < 0.05 * MICROSECOND, "apart {together}");
}

#[test]
fn timing_is_close_from_the_first_sound_on() {
    // Before the second window of packets the slope of the sender's clock
    // is not known, and the error is the drift over a third of a second.
    let mut scene = scene(&WIRED_CALM, 20, |_| {});
    scene.run(TrueTime::from_seconds(30.0));
    for trace in scene.traces() {
        let first = trace.errors.first().map_or(f64::MAX, |(at, _)| *at);
        assert!(first < 0.5, "first sound at {first}");
    }
    let (from_the_start, _) = worst_and_apart(&scene, 0.0);
    assert!(from_the_start < 100.0 * MICROSECOND, "{from_the_start}");
    let (after_two_seconds, _) = worst_and_apart(&scene, 2.0);
    assert!(after_two_seconds < 2.0 * MICROSECOND, "{after_two_seconds}");
}

#[test]
fn a_receiver_that_takes_its_device_to_run_at_the_nominal_rate_leaves_the_bound() {
    // The schedule's pace is then wrong by the device's 120 parts per
    // million against its host, and the regulator is left with the error
    // sqrt(2) * 120e-6 / (4 per second), which is 42 microseconds.
    let mut scene = scene(&WIRED_CALM, 20, |receivers| {
        receivers[0].cycle_length = CycleLength::Nominal;
    });
    scene.run(TrueTime::from_seconds(60.0));
    let traces = scene.traces();
    let faulty = worst(traces[0], 20.0);
    assert!(faulty > 100.0 * CALM_BOUND, "worst {faulty}");
    assert!(
        (faulty - 42.4 * MICROSECOND).abs() < 2.0 * MICROSECOND,
        "worst {faulty}"
    );
    // The others are untouched.
    assert!(worst(traces[1], 20.0) < CALM_BOUND);
}

#[test]
fn a_receiver_that_does_not_know_its_link_s_delay_plays_late_by_it() {
    // The estimate of the sender's clock holds the smallest delay of the
    // link, 100 microseconds here, which only an exchange in both
    // directions reveals.
    let mut scene = scene(&WIRED_CALM, 20, |receivers| {
        receivers[1].path = PathDelay::Unknown;
    });
    scene.run(TrueTime::from_seconds(60.0));
    let traces = scene.traces();
    let late = traces[1]
        .errors
        .iter()
        .filter(|(at, _)| *at >= 20.0)
        .map(|(_, error)| *error)
        .fold(f64::MAX, f64::min);
    assert!(late > 100.0 * MICROSECOND - CALM_BOUND, "error {late}");
    assert!(worst(traces[1], 20.0) < 100.0 * MICROSECOND + CALM_BOUND);
    assert!(worst(traces[0], 20.0) < CALM_BOUND);
}

/// The largest timing error between `from` and `to` seconds.
fn worst_between(trace: &Trace, from: f64, to: f64) -> f64 {
    trace
        .errors
        .iter()
        .filter(|(at, _)| *at >= from && *at < to)
        .map(|(_, error)| error.abs())
        .fold(0.0, f64::max)
}

/// How long after `after` seconds the receiver next played a frame.
fn silent_for(trace: &Trace, after: f64) -> f64 {
    trace
        .errors
        .iter()
        .find(|(at, _)| *at > after)
        .map_or(f64::MAX, |(at, _)| at - after)
}

#[test]
fn restarts_of_the_sender_and_of_a_receiver_are_followed() {
    let mut scene = scene(&WIRED_CALM, 20, |_| {});
    scene.run(TrueTime::from_seconds(40.0));
    scene.restart_sender();
    scene.run(TrueTime::from_seconds(70.0));
    scene.restart_receiver(1);
    scene.run(TrueTime::from_seconds(100.0));
    for receiver in 0..4 {
        assert_eq!(scene.followed(receiver), Some(1_001));
    }
    let traces = scene.traces();
    for (number, trace) in traces.iter().enumerate() {
        // Before the restart, and from twenty seconds after it, the timing
        // is within the bound; sound is back within a second.
        assert!(worst_between(trace, 20.0, 40.0) < CALM_BOUND);
        let back = silent_for(trace, 40.05);
        assert!(
            back < 1.0,
            "receiver {number} silent for {back} s after the sender's restart"
        );
        if number == 1 {
            assert!(worst_between(trace, 60.0, 70.0) < CALM_BOUND);
            let back = silent_for(trace, 70.0);
            assert!(back < 1.0, "silent for {back} s after its own restart");
            assert!(worst_between(trace, 90.0, 100.0) < CALM_BOUND);
        } else {
            let after = worst_between(trace, 60.0, 100.0);
            assert!(after < CALM_BOUND, "receiver {number}: {after}");
        }
    }
}

/// A scene in which every receiver finds the delay of its link from
/// reports, twenty a second.
fn measuring(assumptions: &unisono_sim::assumptions::OneWayAssumptions, level_ms: i64) -> Scene {
    scene(assumptions, level_ms, |receivers| {
        for receiver in receivers.iter_mut() {
            receiver.path = PathDelay::Measured(50_000_000);
        }
    })
}

#[test]
fn receivers_that_measure_their_links_play_within_a_microsecond_on_a_calm_wired_link() {
    let mut scene = measuring(&WIRED_CALM, 20);
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < MICROSECOND, "worst {worst}");
    assert!(apart < MICROSECOND, "apart {apart}");
    for receiver in 0..4 {
        // The link's smallest delay is 100 microseconds each way.
        let delay = scene.delay(receiver).unwrap_or(0);
        assert!((delay - 100_000).abs() < 1_000, "delay {delay}");
    }
}

#[test]
fn receivers_that_measure_their_links_play_within_twelve_microseconds_on_a_busy_wired_link() {
    let mut scene = measuring(&WIRED_BUSY, 60);
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 12.0 * MICROSECOND, "worst {worst}");
    assert!(apart < 12.0 * MICROSECOND, "apart {apart}");
}

#[test]
fn receivers_that_measure_their_links_play_within_150_microseconds_on_a_wireless_link() {
    let mut scene = measuring(&WIRELESS, 60);
    scene.run(TrueTime::from_seconds(120.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 150.0 * MICROSECOND, "worst {worst}");
    assert!(apart < 150.0 * MICROSECOND, "apart {apart}");
}

#[test]
fn a_link_that_is_slower_one_way_shifts_playback_by_half_the_difference() {
    // 100 microseconds from the sender and 300 back: the receiver takes
    // half of 400 for the way from the sender, and plays 100 early. Nothing
    // that the two parties can measure tells this from clocks that differ.
    let walk = WIRED_CALM.frequency_walk;
    let mut slow_back = WIRED_CALM.link;
    slow_back.minimum = 300e-6;
    let mut models = hosts(WIRED_CALM.link, walk);
    models[0].back = slow_back;
    let mut receivers = [receiver(0, 80.0, walk), receiver(1, -120.0, walk)];
    for receiver in &mut receivers {
        receiver.path = PathDelay::Measured(50_000_000);
    }
    let mut scene = Scene::new(sender(walk, 20), &models, &receivers, &Generator::new(11));
    scene.run(TrueTime::from_seconds(60.0));
    let traces = scene.traces();
    let errors: Vec<f64> = traces[0]
        .errors
        .iter()
        .filter(|(at, _)| *at >= 20.0)
        .map(|(_, error)| *error)
        .collect();
    let earliest = errors.iter().copied().fold(f64::MAX, f64::min);
    let latest = errors.iter().copied().fold(f64::MIN, f64::max);
    assert!(earliest > -101.0 * MICROSECOND, "earliest {earliest}");
    assert!(latest < -99.0 * MICROSECOND, "latest {latest}");
    // The receiver on a link that is the same both ways is on time.
    assert!(worst(traces[1], 20.0) < MICROSECOND);
}

/// A scene in which every receiver fits the line of its device to reports
/// that are off by up to `error` nanoseconds either way.
fn fitting(error: i64) -> Scene {
    scene(&WIRED_CALM, 20, |receivers| {
        for receiver in receivers.iter_mut() {
            receiver.cycle_length = CycleLength::Fitted(error);
        }
    })
}

#[test]
fn reports_of_a_device_that_are_off_either_way_average_out() {
    // The line is fitted to 64 reports. For errors spread evenly within 20
    // microseconds, the fit at the newest report has a standard deviation
    // of 2 * (20 / sqrt 3) / sqrt 64, which is 2.9 microseconds; the bound
    // is four of them, and a single report can be off by 20.
    let mut scene = fitting(20_000);
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 12.0 * MICROSECOND, "worst {worst}");
    assert!(apart < 20.0 * MICROSECOND, "apart {apart}");
    // With reports twenty times better, so is the timing.
    let mut scene = fitting(1_000);
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, _) = worst_and_apart(&scene, 20.0);
    assert!(worst < 0.6 * MICROSECOND + CALM_BOUND, "worst {worst}");
}
