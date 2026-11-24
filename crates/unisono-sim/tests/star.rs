// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Production protocol evaluation and regression tests driven through
//! [`unisono_sim::scene::Scene`] (shipped `CaptureEnd`, `SenderNetBridge`,
//! `ReceiverNetBridge`, `ShippedAudio` over real SPSC rings and serialized UDP
//! wire datagrams, scored strictly from rendered PCM via `ProbeDecoder`),
//! cross-checked against canonical `Unisono.Spec.Objectives` and offline
//! `[ORACLE / MODEL BENCHMARK]` references.

use unisono_core::kalman::NoisePrior;
use unisono_core::player::ModalRegulation;
use unisono_core::sync::WEIGHT_UNITY_Q16;
use unisono_runtime::receive::{Reporting, SyncMode};
use unisono_sim::TrueTime;
use unisono_sim::clock::{FrequencyNoise, OscillatorModel};
use unisono_sim::link::{LinkModel, SharedContentionModel};
use unisono_sim::objectives::{ObjectiveReport, ObjectiveWeights, quantiles};
use unisono_sim::oracle;
use unisono_sim::random::Generator;
use unisono_sim::scene::{
    CycleLength, HostConfig, PathDelay, ReceiverConfig, Scene, SceneConfig, SenderConfig,
};

const LIPSYNC_WEIGHTS: ObjectiveWeights = ObjectiveWeights {
    sync: 1e6,
    latency: 0.0,
    tracking: 1e4,
    roughness: 1e2,
    missed: 1e2,
    discontinuities: 1e3,
};

const LOW_LATENCY_WEIGHTS: ObjectiveWeights = ObjectiveWeights {
    sync: 1e6,
    latency: 10.0,
    tracking: 0.0,
    roughness: 1e2,
    missed: 1e2,
    discontinuities: 1e3,
};

/// Wires a full peer mesh among `receivers` (every distinct pair).
fn wire_full_peer_mesh(receivers: &mut [ReceiverConfig], peer_weight_q16: u32) {
    let count = receivers.len();
    for (idx, rx) in receivers.iter_mut().enumerate() {
        rx.peers = (0..count)
            .filter(|&other| other != idx)
            .map(|other| (other, peer_weight_q16))
            .collect();
    }
}

/// Builds a 2-host / 2-speaker scenario using only shipped CLI-expressible
/// `NoisePrior` presets (`TCXO`, `CONSUMER_QUARTZ`, `WANDERING_QUARTZ`).
#[allow(clippy::too_many_arguments)]
fn build_two_speaker_scene(
    mode: SyncMode,
    with_peers: bool,
    sender_link: LinkModel,
    sender_asymmetry_s: f64,
    peer_link: LinkModel,
    sender_noise: FrequencyNoise,
    receiver_noise: FrequencyNoise,
    sender_prior: NoisePrior,
    local_prior: NoisePrior,
    sender_weight_q16: u32,
    variance_floor_ns2: u64,
    modal_reg: Option<ModalRegulation>,
    level_ns: i64,
    window: (f64, f64),
) -> SceneConfig {
    let sender = SenderConfig::standard(
        OscillatorModel {
            offset: 12.0,
            frequency: 15e-6,
            noise: sender_noise,
        },
        OscillatorModel {
            offset: 0.0,
            frequency: -10e-6,
            noise: sender_noise,
        },
        level_ns,
    )
    .with_fixed_level();

    let mut link0_fwd = sender_link;
    let mut link0_rev = sender_link;
    link0_fwd.minimum += sender_asymmetry_s.max(0.0);
    link0_rev.minimum += (-sender_asymmetry_s).max(0.0);

    let mut link1_fwd = sender_link;
    let mut link1_rev = sender_link;
    link1_fwd.minimum += (-sender_asymmetry_s).max(0.0);
    link1_rev.minimum += sender_asymmetry_s.max(0.0);

    let hosts = vec![
        HostConfig::new(
            OscillatorModel {
                offset: -5.0,
                frequency: -20e-6,
                noise: receiver_noise,
            },
            link0_fwd,
            link0_rev,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: 30.0,
                frequency: 25e-6,
                noise: receiver_noise,
            },
            link1_fwd,
            link1_rev,
        ),
    ];

    let make_rx = |host: usize, id: u64, dev_ppm: f64| {
        let dev = OscillatorModel {
            offset: 0.0,
            frequency: dev_ppm * 1e-6,
            noise: receiver_noise,
        };
        let mut rx = match mode {
            SyncMode::Peer => ReceiverConfig::peer(host, id, dev),
            SyncMode::Hull => ReceiverConfig::hull(host, id, dev),
        };
        rx.sync_settings.sender_prior = sender_prior;
        rx.sync_settings.local_prior = local_prior;
        rx.sync_settings.variance_floor_ns2 = variance_floor_ns2;
        rx.sender_weight_q16 = sender_weight_q16;
        if mode == SyncMode::Peer {
            rx.modal_regulation = modal_reg.or(rx.modal_regulation);
        }
        rx.path = PathDelay::Measured(Reporting::USUAL);
        rx
    };

    let mut receivers = vec![make_rx(0, 1, 30.0), make_rx(1, 2, -40.0)];
    if mode == SyncMode::Peer && with_peers {
        wire_full_peer_mesh(&mut receivers, WEIGHT_UNITY_Q16);
    }

    let mut cfg = SceneConfig::new(sender, hosts, receivers);
    cfg.peer_link = peer_link;
    cfg.objective_window = Some(window);
    cfg.objective_weights = LIPSYNC_WEIGHTS;
    cfg.record_trace = false;
    cfg
}

fn run_report(cfg: SceneConfig, duration_s: f64, seed: u64) -> ObjectiveReport {
    let mut scene = Scene::new(cfg, &Generator::new(seed));
    scene.run(TrueTime::from_seconds(duration_s));
    scene.finish_objectives().expect("objective report")
}

#[test]
fn ideal_constant_world_attains_near_zero_objectives_with_paired_fault_control() {
    let build_ideal = |with_peers: bool, fault_hidden_dac_s: f64| {
        let sender = SenderConfig::standard(
            OscillatorModel::ideal(10.0),
            OscillatorModel::ideal(0.0),
            20_000_000,
        )
        .with_fixed_level();
        let hosts = vec![
            HostConfig::new(
                OscillatorModel::ideal(-5.0),
                LinkModel::IDEAL,
                LinkModel::IDEAL,
            ),
            HostConfig::new(
                OscillatorModel::ideal(25.0),
                LinkModel::IDEAL,
                LinkModel::IDEAL,
            ),
        ];
        let mut receivers = vec![
            ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
        ];
        receivers[1].hidden_latency_s = fault_hidden_dac_s;
        for rx in &mut receivers {
            rx.sync_settings.sender_prior = NoisePrior::TCXO;
            rx.sync_settings.local_prior = NoisePrior::TCXO;
            rx.path = PathDelay::Measured(Reporting::USUAL);
        }
        if with_peers {
            wire_full_peer_mesh(&mut receivers, WEIGHT_UNITY_Q16);
        }
        let mut cfg = SceneConfig::new(sender, hosts, receivers);
        cfg.peer_link = LinkModel::IDEAL;
        cfg.objective_window = Some((4.0, 10.0));
        cfg.objective_weights = LIPSYNC_WEIGHTS;
        cfg.record_trace = false;
        cfg
    };

    for &with_peers in &[false, true] {
        let report = run_report(build_ideal(with_peers, 0.0), 10.5, 1);
        assert!(
            report.sync_rms_us < 0.05,
            "with_peers={with_peers}: sync_rms_us={}",
            report.sync_rms_us
        );
        assert!(
            report.tracking_s2.sqrt() * 1e6 < 0.5,
            "with_peers={with_peers}: tracking_rms_us={}",
            report.tracking_s2.sqrt() * 1e6
        );
        assert!(
            report.roughness_per_s2 < 1e-6,
            "with_peers={with_peers}: roughness={}",
            report.roughness_per_s2
        );
        assert_eq!(report.missed_per_s, 0.0);
        assert_eq!(report.discontinuities_per_s, 0.0);
    }

    // Paired fault-injection control: 100 us uncalibrated DAC latency on
    // speaker 1 shifts playback 1:1 (50 us RMS spread across 2 speakers) and
    // must break the ideal sync bound.
    let faulty = run_report(build_ideal(true, 100e-6), 10.5, 1);
    assert!(
        (faulty.sync_rms_us - 50.0).abs() < 1.0,
        "paired hidden DAC fault should produce ~50 us sync RMS, got {}",
        faulty.sync_rms_us
    );
}

#[test]
fn black_box_pcm_scoring_tracks_responder_send_latency_and_device_jitter() {
    let build = |sender_reply_send_s: f64, peer_reply_send_s: f64, device_jitter_ns: i64| {
        let sender = SenderConfig::standard(
            OscillatorModel::ideal(3.0),
            OscillatorModel::ideal(0.0),
            20_000_000,
        )
        .with_fixed_level()
        .with_reply_latency(5e-6, sender_reply_send_s);
        let hosts = vec![
            HostConfig::new(
                OscillatorModel::ideal(-2.0),
                LinkModel::IDEAL,
                LinkModel::IDEAL,
            )
            .with_reply_latency(5e-6, peer_reply_send_s),
            HostConfig::new(
                OscillatorModel::ideal(7.0),
                LinkModel::IDEAL,
                LinkModel::IDEAL,
            )
            .with_reply_latency(5e-6, peer_reply_send_s),
        ];
        let mut receivers = vec![
            ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
        ];
        wire_full_peer_mesh(&mut receivers, WEIGHT_UNITY_Q16);
        for rx in &mut receivers {
            rx.cycle_length = if device_jitter_ns > 0 {
                CycleLength::Fitted(device_jitter_ns)
            } else {
                CycleLength::Measured
            };
            rx.record_pcm = true;
        }
        let mut cfg = SceneConfig::new(sender, hosts, receivers);
        cfg.peer_link = LinkModel::IDEAL;
        cfg.objective_window = Some((3.0, 6.0));
        cfg.objective_weights = LIPSYNC_WEIGHTS;
        cfg.record_trace = false;
        let mut scene = Scene::new(cfg, &Generator::new(19));
        scene.run(TrueTime::from_seconds(6.2));
        scene
    };

    let clean = build(0.0, 0.0, 0);
    assert!(clean.sync_snapshot(0).is_some_and(|s| s.peer_active));
    assert!(clean.sync_snapshot(1).is_some_and(|s| s.peer_active));
    for sp in 0..2 {
        let full_cycles = clean
            .recorded_cycles(sp)
            .iter()
            .filter(|c| c.out_start_s >= 3.0 && c.decoded.iter().all(Option::is_some))
            .count();
        assert!(
            full_cycles > 500,
            "speaker {sp}: expected >500 fully decoded cycles, got {full_cycles}"
        );
    }
    let clean_rep = clean.finish_objectives().expect("clean report");
    assert!(clean_rep.tracking_s2.sqrt() * 1e6 < 0.5);

    // Paired fault control 1: 60 us sender post-T3 send latency shifts both
    // sender edges by half (30 us) into tracking while preserving 0 us sync.
    let sender_biased = build(60e-6, 0.0, 0)
        .finish_objectives()
        .expect("sender biased");
    let sender_trk_us = sender_biased.tracking_s2.sqrt() * 1e6;
    assert!(
        (sender_trk_us - 30.0).abs() < 1.5,
        "60 us sender reply send latency should induce ~30 us tracking shift, got {sender_trk_us:.2} us"
    );
    assert!(sender_biased.sync_rms_us < 0.5);

    // Paired fault control 2: 60 us post-T3 send latency on sender AND both
    // peer hosts adds a symmetric 3-node BLUE shift of 10 us (total ~40 us)
    // while ±5 us device timestamp jitter stays under 1 us sync RMS.
    let all_biased = build(60e-6, 60e-6, 5_000)
        .finish_objectives()
        .expect("all biased");
    let all_trk_us = all_biased.tracking_s2.sqrt() * 1e6;
    assert!(
        (all_trk_us - 40.0).abs() < 2.0,
        "60 us sender+peer reply send latency should induce ~40 us tracking shift, got {all_trk_us:.2} us"
    );
    assert!(
        all_biased.sync_rms_us < 1.0,
        "symmetric reply send latency + +/-5 us device jitter should keep sync < 1 us, got {:.2} us",
        all_biased.sync_rms_us
    );
}

#[test]
fn wireless_wandering_sender_to_wired_peers_reduces_sync_error_dramatically() {
    let mut star_syncs = Vec::new();
    let mut peer_syncs = Vec::new();
    for seed in 101..104 {
        // Both runs use the shipped CLI default `CONSUMER_QUARTZ` prior (no
        // copying of the simulated wandering oscillator into the prior) over
        // the post-transient window [40 s, 60 s).
        let star_cfg = build_two_speaker_scene(
            SyncMode::Peer,
            false,
            LinkModel::WIRELESS,
            0.0,
            LinkModel::WIRED_CALM,
            FrequencyNoise::WANDERING_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            NoisePrior::CONSUMER_QUARTZ,
            NoisePrior::CONSUMER_QUARTZ,
            WEIGHT_UNITY_Q16,
            25_000_000,
            None,
            80_000_000,
            (40.0, 60.0),
        );
        let peer_cfg = build_two_speaker_scene(
            SyncMode::Peer,
            true,
            LinkModel::WIRELESS,
            0.0,
            LinkModel::WIRED_CALM,
            FrequencyNoise::WANDERING_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            NoisePrior::CONSUMER_QUARTZ,
            NoisePrior::CONSUMER_QUARTZ,
            WEIGHT_UNITY_Q16,
            25_000_000,
            None,
            80_000_000,
            (40.0, 60.0),
        );
        star_syncs.push(run_report(star_cfg, 60.5, seed).sync_rms_us);
        peer_syncs.push(run_report(peer_cfg, 60.5, seed).sync_rms_us);
    }
    let star_med = quantiles(&star_syncs).median;
    let peer_med = quantiles(&peer_syncs).median;
    assert!(
        peer_med * 3.0 < star_med,
        "peer median ({peer_med:.2} us) should beat star median ({star_med:.2} us) by >3x"
    );
    assert!(
        peer_med < 20.0,
        "wired peer sync median ({peer_med:.2} us) should stay under 20 us"
    );
}

#[test]
fn static_asymmetry_shows_sender_link_weight_gain_and_peer_link_weight_failure() {
    let asym_s = 1_000e-6; // +1000 us fwd / 0 rev on one side, opposite on the other
    let run_sender_asym = |with_peers: bool, sender_w: u32| {
        run_report(
            build_two_speaker_scene(
                SyncMode::Peer,
                with_peers,
                LinkModel::WIRED_CALM,
                asym_s,
                LinkModel::WIRED_CALM,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                NoisePrior::CONSUMER_QUARTZ,
                NoisePrior::CONSUMER_QUARTZ,
                sender_w,
                25_000_000,
                None,
                30_000_000,
                (8.0, 18.0),
            ),
            18.5,
            42,
        )
    };

    let star_rep = run_sender_asym(false, WEIGHT_UNITY_Q16);
    let peer_equal = run_sender_asym(true, WEIGHT_UNITY_Q16);
    let peer_weighted = run_sender_asym(true, 3_277); // --link-weight 0.05

    // 1. Sender-link asymmetry: Star suffers full ~500 us RMS bias; Peer cuts
    //    it by ~3x at equal weight and downweighting the sender link cuts it
    //    further.
    assert!(
        star_rep.sync_rms_us > 450.0,
        "star should exhibit asymmetry floor: {}",
        star_rep.sync_rms_us
    );
    assert!(
        peer_equal.sync_rms_us < star_rep.sync_rms_us * 0.5,
        "equal-weight peer ({:.1} us) should reduce star bias ({:.1} us)",
        peer_equal.sync_rms_us,
        star_rep.sync_rms_us
    );
    assert!(
        peer_weighted.sync_rms_us < peer_equal.sync_rms_us * 0.35,
        "weighted peer ({:.1} us) should beat equal-weight peer ({:.1} us)",
        peer_weighted.sync_rms_us,
        peer_equal.sync_rms_us
    );

    // 2. Paired opposite-side failure case (peer-link asymmetry instead of
    //    sender-link asymmetry): Star is immune, equal-weight Peer degrades,
    //    and `--link-weight 0.05` amplifies the error > 40x over Star.
    let run_peer_asym = |with_peers: bool, sender_w: u32| {
        let mut cfg = build_two_speaker_scene(
            SyncMode::Peer,
            with_peers,
            LinkModel::WIRED_CALM,
            0.0,
            LinkModel::WIRED_CALM,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            NoisePrior::CONSUMER_QUARTZ,
            NoisePrior::CONSUMER_QUARTZ,
            sender_w,
            25_000_000,
            None,
            30_000_000,
            (8.0, 18.0),
        );
        let mut slow_peer = LinkModel::WIRED_CALM;
        slow_peer.minimum += asym_s;
        cfg.link_overrides.push((1, 2, slow_peer));
        run_report(cfg, 18.5, 42)
    };

    let peer_asym_star = run_peer_asym(false, WEIGHT_UNITY_Q16);
    let peer_asym_equal = run_peer_asym(true, WEIGHT_UNITY_Q16);
    let peer_asym_weighted = run_peer_asym(true, 3_277);
    assert!(
        peer_asym_star.sync_rms_us < 5.0,
        "star should be unaffected by peer-link asymmetry: {:.2} us",
        peer_asym_star.sync_rms_us
    );
    assert!(
        peer_asym_equal.sync_rms_us > 100.0,
        "peer-link asymmetry should bias equal-weight peer: {:.2} us",
        peer_asym_equal.sync_rms_us
    );
    assert!(
        peer_asym_weighted.sync_rms_us > peer_asym_equal.sync_rms_us
            && peer_asym_weighted.sync_rms_us > 40.0 * peer_asym_star.sync_rms_us,
        "downweighting sender link under peer-link asymmetry ({:.1} us) must worsen spread vs equal ({:.1} us) and Star ({:.2} us)",
        peer_asym_weighted.sync_rms_us,
        peer_asym_equal.sync_rms_us,
        peer_asym_star.sync_rms_us
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn three_host_four_speaker_colocated_and_shared_ap_contention_scenarios_sync_cleanly() {
    // 3-host / 4-speaker wired LAN (two speakers co-located on host 2).
    let sender = SenderConfig::standard(
        OscillatorModel {
            offset: 50.0,
            frequency: 10e-6,
            noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        },
        OscillatorModel {
            offset: 0.0,
            frequency: -15e-6,
            noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        },
        30_000_000,
    )
    .with_fixed_level();
    let hosts = vec![
        HostConfig::new(
            OscillatorModel {
                offset: -10.0,
                frequency: 20e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            LinkModel::WIRED_CALM,
            LinkModel::WIRED_CALM,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: 100.0,
                frequency: -25e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            LinkModel::WIRED_CALM,
            LinkModel::WIRED_CALM,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: -500.0,
                frequency: 5e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            LinkModel::WIRED_CALM,
            LinkModel::WIRED_CALM,
        ),
    ];
    let build_wired = |fault_hidden_dac_s: f64| {
        let mut receivers = vec![
            ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(2, 3, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(2, 4, OscillatorModel::ideal(0.0)),
        ];
        receivers[0].hidden_latency_s = fault_hidden_dac_s;
        wire_full_peer_mesh(&mut receivers, WEIGHT_UNITY_Q16);
        let mut cfg = SceneConfig::new(sender.clone(), hosts.clone(), receivers);
        cfg.objective_window = Some((6.0, 14.0));
        cfg.objective_weights = LIPSYNC_WEIGHTS;
        cfg.record_trace = false;
        cfg
    };

    let wired_rep = run_report(build_wired(0.0), 14.5, 77);
    assert!(
        wired_rep.sync_rms_us < 10.0,
        "3-host/4-speaker wired sync_rms_us={}",
        wired_rep.sync_rms_us
    );
    assert_eq!(wired_rep.missed_per_s, 0.0);
    assert_eq!(wired_rep.discontinuities_per_s, 0.0);

    // Paired fault-injection control: 100 us uncalibrated DAC delay on speaker
    // 0 breaks the < 10 us wired bound.
    let wired_fault = run_report(build_wired(100e-6), 14.5, 77);
    assert!(
        wired_fault.sync_rms_us > 35.0,
        "paired hidden DAC fault should exceed 35 us RMS, got {}",
        wired_fault.sync_rms_us
    );

    // 2 wired + 2 wireless hosts with shared AP contention.
    let mixed_hosts = vec![
        HostConfig::new(
            OscillatorModel {
                offset: -20.0,
                frequency: 15e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            LinkModel::WIRED_CALM,
            LinkModel::WIRED_CALM,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: 40.0,
                frequency: -15e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            LinkModel::WIRED_CALM,
            LinkModel::WIRED_CALM,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: -100.0,
                frequency: 30e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            LinkModel::WIRELESS,
            LinkModel::WIRELESS,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: 200.0,
                frequency: -30e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            LinkModel::WIRELESS,
            LinkModel::WIRELESS,
        ),
    ];
    let mut mixed_sender = sender;
    mixed_sender.level_ns = 90_000_000;
    let build_mixed = |with_peers: bool| {
        let mut mixed_rx = vec![
            ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(2, 3, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(3, 4, OscillatorModel::ideal(0.0)),
        ];
        if with_peers {
            wire_full_peer_mesh(&mut mixed_rx, WEIGHT_UNITY_Q16);
        }
        let mut mixed_cfg = SceneConfig::new(mixed_sender.clone(), mixed_hosts.clone(), mixed_rx);
        mixed_cfg.contention = Some(SharedContentionModel::uniform(
            5,
            10e-6,
            10e-6,
            500e-6,
            vec![false, false, false, true, true],
        ));
        mixed_cfg.objective_window = Some((12.0, 22.0));
        mixed_cfg.objective_weights = LIPSYNC_WEIGHTS;
        mixed_cfg.record_trace = false;
        mixed_cfg
    };
    let mixed_star = run_report(build_mixed(false), 22.5, 88);
    let mixed_peer = run_report(build_mixed(true), 22.5, 88);
    assert!(
        mixed_peer.sync_rms_us < 100.0 && mixed_peer.sync_rms_us < mixed_star.sync_rms_us,
        "2 wired + 2 wireless shared-AP: peer ({:.2} us) should stay under 100 us and beat star ({:.2} us)",
        mixed_peer.sync_rms_us,
        mixed_star.sync_rms_us
    );
}

#[test]
fn solo_bursty_wireless_shipped_retransmission_and_chooser_reduce_misses() {
    let build = |protect: bool| {
        // `SenderConfig::standard` uses exact shipped defaults (`kept = 256`,
        // `Choice::shipped_default` with `slope = 500 us/s <= 1000 us/s`).
        let mut sender = SenderConfig::standard(
            OscillatorModel {
                offset: 10.0,
                frequency: 15e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            OscillatorModel::ideal(0.0),
            30_000_000,
        );
        if !protect {
            sender = sender.with_fixed_level().without_protection();
        }
        let hosts = vec![HostConfig::new(
            OscillatorModel {
                offset: -15.0,
                frequency: -20e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            LinkModel::WIRELESS_BURSTY,
            LinkModel::WIRELESS,
        )];
        let mut rx = ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0));
        rx.modal_regulation = Some(ModalRegulation::low_latency(1_000_000, 240));
        let mut cfg = SceneConfig::new(sender, hosts, vec![rx]);
        cfg.objective_window = Some((5.0, 25.0));
        cfg.objective_weights = LOW_LATENCY_WEIGHTS;
        cfg.record_trace = false;
        let mut scene = Scene::new(cfg, &Generator::new(55));
        scene.run(TrueTime::from_seconds(26.0));
        scene
    };

    let unprotected = build(false);
    let protected = build(true);

    assert!(
        protected.network_counts(0).expect("rx counts").requests > 0,
        "protected wireless receiver should issue retransmission requests"
    );
    assert!(
        protected.sender_counts().again > 0,
        "protected wireless sender should retransmit requested packets"
    );
    let unprot_rep = unprotected.finish_objectives().expect("unprot report");
    let prot_rep = protected.finish_objectives().expect("prot report");
    assert!(
        prot_rep.missed_per_s < unprot_rep.missed_per_s,
        "shipped retransmission + adaptive level ({:.1} missed/s) should beat unprotected ({:.1} missed/s)",
        prot_rep.missed_per_s,
        unprot_rep.missed_per_s
    );
}

#[test]
fn dynamic_fault_recovery_speaker_restart_sender_reboot_and_peer_partition() {
    let mut cfg = build_two_speaker_scene(
        SyncMode::Peer,
        true,
        LinkModel::WIRED_CALM,
        0.0,
        LinkModel::WIRED_CALM,
        FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        NoisePrior::CONSUMER_QUARTZ,
        NoisePrior::CONSUMER_QUARTZ,
        WEIGHT_UNITY_Q16,
        25_000_000,
        None,
        30_000_000,
        (2.0, 44.0),
    );
    cfg.record_trace = true;
    let mut scene = Scene::new(cfg, &Generator::new(66));

    // Phase 1: Initial convergence with active peers.
    scene.run(TrueTime::from_seconds(7.0));
    assert!(scene.sync_snapshot(0).is_some_and(|s| s.peer_active));
    assert!(scene.sync_snapshot(1).is_some_and(|s| s.peer_active));

    // Phase 2: Partition the direct peer link -> graceful fallback to Star after 5s timeout.
    scene.set_link_partitioned(1, 2, true);
    scene.set_link_partitioned(2, 1, true);
    scene.run(TrueTime::from_seconds(14.0));
    assert!(
        scene.sync_snapshot(0).is_some_and(|s| !s.peer_active),
        "speaker 0 should expire partitioned peer and fall back to star"
    );
    assert!(
        scene.sync_snapshot(1).is_some_and(|s| !s.peer_active),
        "speaker 1 should expire partitioned peer and fall back to star"
    );

    // Phase 3: Heal peer partition -> bumpless rejoin to Peer mode.
    let jumps_before_heal: Vec<usize> = scene.traces().iter().map(|t| t.jumps.len()).collect();
    scene.set_link_partitioned(1, 2, false);
    scene.set_link_partitioned(2, 1, false);
    scene.run(TrueTime::from_seconds(19.0));
    assert!(scene.sync_snapshot(0).is_some_and(|s| s.peer_active));
    assert!(scene.sync_snapshot(1).is_some_and(|s| s.peer_active));
    for (sp, &before) in jumps_before_heal.iter().enumerate() {
        assert_eq!(
            scene.traces()[sp].jumps.len(),
            before,
            "healing peer partition should rejoin bumplessly without jumps on speaker {sp}"
        );
    }

    // Phase 4: Speaker 1 restarts -> rejoins peer group cleanly.
    scene.restart_receiver(1);
    scene.run(TrueTime::from_seconds(26.0));
    assert!(scene.sync_snapshot(1).is_some_and(|s| s.peer_active));

    // Phase 5: Sender host reboots with a massive clock jump (+500 s) and new clock_id.
    scene.reboot_sender(512.0, -35.0);
    scene.run(TrueTime::from_seconds(35.0));
    assert_eq!(scene.followed(0), Some(1_001));
    assert_eq!(scene.followed(1), Some(1_001));
    assert!(scene.sync_snapshot(0).is_some_and(|s| s.peer_active));
    assert!(scene.sync_snapshot(1).is_some_and(|s| s.peer_active));

    // Phase 6: Step host 1 clock frequency by +25 ppm -> tracks cleanly.
    scene.step_host_frequency(1, 25.0);
    scene.run(TrueTime::from_seconds(44.0));
    assert!(
        scene
            .sync_snapshot(0)
            .is_some_and(|s| s.valid && s.peer_active)
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn cli_prior_variance_floor_and_modal_gain_sweeps_stay_stable() {
    // CLI `--sender-clock-prior` / `--clock-prior` combinations (only real
    // CLI-expressible presets: tcxo, consumer, wandering).
    for &(label, sender_prior, local_prior) in &[
        ("tcxo/tcxo", NoisePrior::TCXO, NoisePrior::TCXO),
        (
            "consumer/consumer",
            NoisePrior::CONSUMER_QUARTZ,
            NoisePrior::CONSUMER_QUARTZ,
        ),
        (
            "wandering/wandering",
            NoisePrior::WANDERING_QUARTZ,
            NoisePrior::WANDERING_QUARTZ,
        ),
        (
            "wandering/consumer",
            NoisePrior::WANDERING_QUARTZ,
            NoisePrior::CONSUMER_QUARTZ,
        ),
        (
            "tcxo/wandering",
            NoisePrior::TCXO,
            NoisePrior::WANDERING_QUARTZ,
        ),
    ] {
        let rep = run_report(
            build_two_speaker_scene(
                SyncMode::Peer,
                true,
                LinkModel::WIRED_CALM,
                0.0,
                LinkModel::WIRED_CALM,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                sender_prior,
                local_prior,
                WEIGHT_UNITY_Q16,
                25_000_000,
                None,
                30_000_000,
                (6.0, 14.0),
            ),
            14.5,
            31,
        );
        assert!(
            rep.sync_rms_us < 25.0 && rep.discontinuities_per_s == 0.0,
            "priors {label}: sync_rms_us={}, disc={}",
            rep.sync_rms_us,
            rep.discontinuities_per_s
        );
    }

    // Variance floor sweep: (1 us)^2 .. (100 us)^2.
    for &floor in &[1_000_000u64, 25_000_000, 10_000_000_000] {
        let rep = run_report(
            build_two_speaker_scene(
                SyncMode::Peer,
                true,
                LinkModel::WIRED_CALM,
                0.0,
                LinkModel::WIRED_CALM,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                NoisePrior::CONSUMER_QUARTZ,
                NoisePrior::CONSUMER_QUARTZ,
                WEIGHT_UNITY_Q16,
                floor,
                None,
                30_000_000,
                (6.0, 14.0),
            ),
            14.5,
            32,
        );
        assert!(
            rep.sync_rms_us < 30.0 && rep.discontinuities_per_s == 0.0,
            "variance floor {floor}: sync_rms_us={}",
            rep.sync_rms_us
        );
    }

    // Modal gain presets: lipsync vs low-latency vs zero common gain.
    let zero_com = ModalRegulation {
        star_gain: 4 << 16,
        common_gain: 0,
        diff_gain: 4 << 16,
        limit: 1_000_000,
        jump: 240,
    };
    for &(modal, bound_us) in &[
        (ModalRegulation::lipsync(1_000_000, 240), 15.0),
        (ModalRegulation::low_latency(1_000_000, 240), 25.0),
        (zero_com, 25.0),
    ] {
        let rep = run_report(
            build_two_speaker_scene(
                SyncMode::Peer,
                true,
                LinkModel::WIRED_CALM,
                0.0,
                LinkModel::WIRED_CALM,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                NoisePrior::CONSUMER_QUARTZ,
                NoisePrior::CONSUMER_QUARTZ,
                WEIGHT_UNITY_Q16,
                25_000_000,
                Some(modal),
                30_000_000,
                (6.0, 14.0),
            ),
            14.5,
            33,
        );
        assert!(
            rep.sync_rms_us < bound_us && rep.discontinuities_per_s == 0.0,
            "modal {modal:?}: sync_rms_us={}",
            rep.sync_rms_us
        );
    }

    // Paired fault-injection control: injecting 100 us of uncalibrated DAC
    // latency breaks every wired sweep bound above.
    let mut faulty_cfg = build_two_speaker_scene(
        SyncMode::Peer,
        true,
        LinkModel::WIRED_CALM,
        0.0,
        LinkModel::WIRED_CALM,
        FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        NoisePrior::CONSUMER_QUARTZ,
        NoisePrior::CONSUMER_QUARTZ,
        WEIGHT_UNITY_Q16,
        25_000_000,
        None,
        30_000_000,
        (6.0, 14.0),
    );
    faulty_cfg.receivers[1].hidden_latency_s = 100e-6;
    let faulty_rep = run_report(faulty_cfg, 14.5, 33);
    assert!(
        faulty_rep.sync_rms_us > 40.0,
        "paired 100 us uncalibrated DAC fault must break sweep bounds, got {:.2} us",
        faulty_rep.sync_rms_us
    );
}

#[test]
fn oracle_analytical_benchmarks_agree_with_closed_form_and_local_minimality() {
    // [ORACLE / CENTRALIZED BENCHMARK] Graph-BLUE effective resistance on K_3:
    // symmetric variance sigma^2 gives R_eff(1, 2) = 2/3 * sigma^2 vs star 2 * sigma^2 (3x).
    let sigma2 = 1e-10;
    let star_edges = [
        oracle::GraphEdge {
            src: 0,
            dst: 1,
            variance: sigma2,
            bias: 0.0,
        },
        oracle::GraphEdge {
            src: 0,
            dst: 2,
            variance: sigma2,
            bias: 0.0,
        },
    ];
    let k3_edges = [
        star_edges[0],
        star_edges[1],
        oracle::GraphEdge {
            src: 1,
            dst: 2,
            variance: sigma2,
            bias: 0.0,
        },
    ];
    let r_star = oracle::effective_resistance(3, &star_edges, 1, 2);
    let r_k3 = oracle::effective_resistance(3, &k3_edges, 1, 2);
    assert!((r_star / r_k3 - 3.0).abs() < 1e-12);

    // [ORACLE / MODEL BENCHMARK] Filtered star Lyapunov gain minimizes the
    // model's per-cycle cost locally against finite perturbations.
    let cycle = 256.0 / 48_000.0;
    let model = oracle::FilteredStarLyapunov {
        receivers: 3,
        c_sync: oracle::cycle_position_weight(1e6, 1e2, cycle),
        c_track: oracle::cycle_position_weight(1e4, 1e2, cycle),
        cycle,
        meas_stride: 47,
        sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
        receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
        meas_var: 25e-12,
    };
    let gain = oracle::minimizing_filtered_star_gain(model);
    let cost = oracle::filtered_star_lyapunov_cost(model, gain);
    assert!(gain > 0.0 && gain < 1.0 && cost.is_finite() && cost > 0.0);
    assert!(
        oracle::filtered_star_lyapunov_cost(model, gain * 0.9) > cost,
        "g* should beat 0.9 * g*"
    );
    assert!(
        oracle::filtered_star_lyapunov_cost(model, gain * 1.1) > cost,
        "g* should beat 1.1 * g*"
    );
    assert!(
        oracle::filtered_star_lyapunov_cost(model, gain * 0.99) > cost,
        "g* should beat 0.99 * g*"
    );
    assert!(
        oracle::filtered_star_lyapunov_cost(model, gain * 1.01) > cost,
        "g* should beat 1.01 * g*"
    );
}
