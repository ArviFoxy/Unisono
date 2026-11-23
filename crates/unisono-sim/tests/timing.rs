// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! End-to-end playback timing accuracy tests under large clock offsets,
//! oscillator drift (up to 120 ppm), and link jitter, paired with
//! fault-injection controls.
//!
//! Runs the shipped [`unisono_runtime`] SPSC-ring pipelines (`CaptureEnd`,
//! `SenderNetBridge`, `ReceiverNetBridge`, `ShippedAudio`) over real
//! serialized UDP wire bytes via [`unisono_sim::scene::Scene`], decoding
//! playback timing directly from rendered PCM output.

use unisono_core::player::Regulation;
use unisono_runtime::receive::Reporting;
use unisono_sim::TrueTime;
use unisono_sim::assumptions::{WIRED_BUSY, WIRED_CALM, WIRELESS};
use unisono_sim::clock::OscillatorModel;
use unisono_sim::link::LinkModel;
use unisono_sim::random::Generator;
use unisono_sim::scene::{
    CycleLength, HostConfig, PathDelay, ReceiverConfig, Scene, SceneConfig, SenderConfig, Trace,
};

fn oscillator(offset: f64, parts_per_million: f64, walk: f64) -> OscillatorModel {
    OscillatorModel::from_walk_rate(offset, parts_per_million * 1e-6, walk)
}

fn sender(walk: f64, level_ms: i64) -> SenderConfig {
    let mut cfg = SenderConfig::standard(
        oscillator(1_000.0, 20.0, walk),
        oscillator(0.0, -35.0, walk),
        level_ms * 1_000_000,
    )
    .with_fixed_level()
    .without_protection();
    cfg.send_delay_s = 50e-6;
    cfg.span_ms = 11_000;
    cfg.window_frames = 15_360;
    cfg
}

fn receiver(host: usize, identity: u64, device_ppm: f64, walk: f64) -> ReceiverConfig {
    let mut cfg = ReceiverConfig::hull(host, identity, oscillator(0.0, device_ppm, walk));
    cfg.cycle_frames = 256;
    cfg.lead_s = 8e-3;
    cfg.regulation = Regulation {
        gain: 4 << 16,
        limit: 1_000_000,
        jump: 240,
    };
    cfg.silence_ns = 1_000_000_000;
    cfg.slope_limit = 200_000;
    cfg.path = PathDelay::Told;
    cfg.cycle_length = CycleLength::Measured;
    cfg.stands_still = None;
    cfg
}

fn hosts(link: LinkModel, walk: f64) -> Vec<HostConfig> {
    [(5_000.0, -40.0), (-7_200.0, 15.0), (86_400.0, 60.0)]
        .iter()
        .map(|(offset, ppm)| HostConfig::new(oscillator(*offset, *ppm, walk), link, link))
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
    change: impl Fn(&mut [ReceiverConfig; 4]),
) -> Scene {
    let walk = assumptions.frequency_walk;
    let mut receivers = [
        receiver(0, 1, 80.0, walk),
        receiver(1, 2, -120.0, walk),
        receiver(2, 3, 10.0, walk),
        receiver(2, 4, -60.0, walk),
    ];
    change(&mut receivers);
    let cfg = SceneConfig::new(
        sender(walk, level_ms),
        hosts(assumptions.link, walk),
        receivers.to_vec(),
    );
    Scene::new(cfg, &Generator::new(11))
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

fn steady_reporting(period_ns: i64) -> Reporting {
    Reporting {
        at_start: period_ns,
        start: 0,
        after: period_ns,
    }
}

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
fn packets_that_overtake_each_other_do_not_disturb_the_estimate() {
    let mut assumptions = WIRED_BUSY;
    assumptions.link.overtaken = 0.05;
    assumptions.link.overtaken_excess = 10e-3;
    let mut scene = scene(&assumptions, 60, |_| {});
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 1.5 * MICROSECOND, "worst {worst}");
    assert!(apart < 1.5 * MICROSECOND, "apart {apart}");
}

#[test]
fn receivers_on_one_host_play_within_fifty_nanoseconds_of_each_other() {
    let mut scene = scene(&WIRED_BUSY, 60, |_| {});
    scene.run(TrueTime::from_seconds(60.0));
    let traces = scene.traces();
    let together = apart(traces[2], traces[3], 5.0);
    assert!(together < 0.05 * MICROSECOND, "apart {together}");
}

#[test]
fn timing_is_close_from_the_first_sound_on() {
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

/// Receivers that measure their paths with five reports a second.
fn measuring(assumptions: &unisono_sim::assumptions::OneWayAssumptions, level_ms: i64) -> Scene {
    scene(assumptions, level_ms, |receivers| {
        for receiver in receivers.iter_mut() {
            receiver.path = PathDelay::Measured(steady_reporting(200_000_000));
        }
    })
}

#[test]
fn receivers_that_measure_their_links_play_within_half_a_microsecond_on_a_calm_wired_link() {
    let mut scene = measuring(&WIRED_CALM, 20);
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 0.5 * MICROSECOND, "worst {worst}");
    assert!(apart < 0.5 * MICROSECOND, "apart {apart}");
    for receiver in 0..4 {
        let delay = scene.delay(receiver).unwrap_or(0);
        assert!((delay - 100_000).abs() < 1_000, "delay {delay}");
    }
}

#[test]
fn receivers_that_measure_their_links_play_within_four_microseconds_on_a_busy_wired_link() {
    let mut scene = measuring(&WIRED_BUSY, 60);
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 4.0 * MICROSECOND, "worst {worst}");
    assert!(apart < 4.0 * MICROSECOND, "apart {apart}");
}

#[test]
fn receivers_that_measure_their_links_play_within_60_microseconds_on_a_wireless_link() {
    let mut scene = measuring(&WIRELESS, 60);
    scene.run(TrueTime::from_seconds(120.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 60.0 * MICROSECOND, "worst {worst}");
    assert!(apart < 60.0 * MICROSECOND, "apart {apart}");
}

#[test]
fn a_link_that_is_slower_one_way_shifts_playback_by_half_the_difference() {
    let walk = WIRED_CALM.frequency_walk;
    let mut slow_back = WIRED_CALM.link;
    slow_back.minimum = 300e-6;
    let mut models = hosts(WIRED_CALM.link, walk);
    models[0].to_sender = slow_back;
    let mut receivers = [receiver(0, 1, 80.0, walk), receiver(1, 2, -120.0, walk)];
    for receiver in &mut receivers {
        receiver.path = PathDelay::Measured(steady_reporting(50_000_000));
    }
    let cfg = SceneConfig::new(sender(walk, 20), models, receivers.to_vec());
    let mut scene = Scene::new(cfg, &Generator::new(11));
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
    assert!(worst(traces[1], 20.0) < MICROSECOND);
}

fn fitting(error: i64) -> Scene {
    scene(&WIRED_CALM, 20, |receivers| {
        for receiver in receivers.iter_mut() {
            receiver.cycle_length = CycleLength::Fitted(error);
        }
    })
}

#[test]
fn a_device_that_stands_still_for_a_cycle_is_followed_two_cycles_later() {
    let cycle = 256.0 / 48_000.0;
    let mut scene = scene(&WIRED_CALM, 20, |receivers| {
        for receiver in receivers.iter_mut() {
            receiver.cycle_length = CycleLength::Fitted(20_000);
        }
        receivers[0].stands_still = Some((5_625, cycle));
    });
    scene.run(TrueTime::from_seconds(60.0));
    let traces = scene.traces();
    let stood = traces[0]
        .errors
        .iter()
        .map(|(at, _)| *at)
        .find(|at| *at >= 30.0)
        .expect("cycles after the device stood still");
    let after = worst(traces[0], stood + 2.5 * cycle);
    assert!(after < 32.0 * MICROSECOND, "after {after}");
    let later = worst(traces[0], stood + 70.0 * cycle);
    assert!(later < 12.0 * MICROSECOND, "later {later}");
    for trace in traces.iter().skip(1) {
        assert!(worst(trace, 20.0) < 12.0 * MICROSECOND);
    }
}

#[test]
fn reports_of_a_device_that_are_off_either_way_average_out() {
    let mut scene = fitting(20_000);
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, apart) = worst_and_apart(&scene, 20.0);
    assert!(worst < 12.0 * MICROSECOND, "worst {worst}");
    assert!(apart < 20.0 * MICROSECOND, "apart {apart}");
    let mut scene = fitting(1_000);
    scene.run(TrueTime::from_seconds(60.0));
    let (worst, _) = worst_and_apart(&scene, 20.0);
    assert!(worst < 0.6 * MICROSECOND + CALM_BOUND, "worst {worst}");
}
