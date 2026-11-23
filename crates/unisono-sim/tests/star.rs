// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Production protocol verification and multi-topology evaluation tests driven
//! through [`unisono_sim::scene::Scene`] (exact `SenderNetEngine`,
//! `ReceiverNetEngine`, `ReceiverPlayback`, `ReportSchedule`, and real
//! serialized UDP wire datagrams), cross-checked against canonical
//! `Unisono.Spec.Objectives` and `[ORACLE / CENTRALIZED BENCHMARK]` bounds.

use unisono_core::kalman::NoisePrior;
use unisono_core::player::ModalRegulation;
use unisono_core::sync::WEIGHT_UNITY_Q16;
use unisono_runtime::level::{Choice, Weights as LevelWeights};
use unisono_runtime::receive::{Reporting, SyncMode};
use unisono_sim::TrueTime;
use unisono_sim::clock::{FrequencyNoise, OscillatorModel};
use unisono_sim::link::{LinkModel, SharedContentionModel};
use unisono_sim::objectives::{ObjectiveReport, ObjectiveWeights, quantiles};
use unisono_sim::oracle;
use unisono_sim::random::Generator;
use unisono_sim::scene::{
    AudioMode, HostConfig, PathDelay, ReceiverConfig, Scene, SceneConfig, SenderConfig, SignalMode,
    decode_ramp_position,
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

/// Builds a 3-host / 2-speaker wired scenario (`Hull`, `Star`, or `Peer`).
#[allow(clippy::too_many_arguments)]
fn build_two_speaker_scene(
    mode: SyncMode,
    with_peers: bool,
    sender_link: LinkModel,
    sender_asymmetry_s: f64,
    peer_link: LinkModel,
    sender_noise: FrequencyNoise,
    receiver_noise: FrequencyNoise,
    sender_weight_q16: u32,
    prior_scale: f64,
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
    );

    let mut link0_fwd = sender_link;
    let mut link0_rev = sender_link;
    link0_fwd.minimum += sender_asymmetry_s.max(0.0);
    link0_rev.minimum += (-sender_asymmetry_s).max(0.0);

    let mut link1_fwd = sender_link;
    let mut link1_rev = sender_link;
    link1_fwd.minimum += (-sender_asymmetry_s).max(0.0);
    link1_rev.minimum += sender_asymmetry_s.max(0.0);

    let hosts = vec![
        HostConfig {
            clock: OscillatorModel {
                offset: -5.0,
                frequency: -20e-6,
                noise: receiver_noise,
            },
            from_sender: link0_fwd,
            to_sender: link0_rev,
        },
        HostConfig {
            clock: OscillatorModel {
                offset: 30.0,
                frequency: 25e-6,
                noise: receiver_noise,
            },
            from_sender: link1_fwd,
            to_sender: link1_rev,
        },
    ];

    let sender_prior = if sender_noise == FrequencyNoise::ZERO {
        NoisePrior::TCXO
    } else {
        sender_noise.scale(prior_scale).to_core_prior()
    };
    let local_prior = if receiver_noise == FrequencyNoise::ZERO {
        NoisePrior::TCXO
    } else {
        receiver_noise.scale(prior_scale).to_core_prior()
    };

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
    cfg
}

fn run_report(cfg: SceneConfig, duration_s: f64, seed: u64) -> ObjectiveReport {
    let mut scene = Scene::new(cfg, &Generator::new(seed));
    scene.run(TrueTime::from_seconds(duration_s));
    scene.finish_objectives().expect("objective report")
}

#[test]
fn ideal_constant_world_attains_near_zero_objectives_in_peer_and_star() {
    for &with_peers in &[false, true] {
        let sender = SenderConfig::standard(
            OscillatorModel::ideal(10.0),
            OscillatorModel::ideal(0.0),
            20_000_000,
        );
        let hosts = vec![
            HostConfig {
                clock: OscillatorModel::ideal(-5.0),
                from_sender: LinkModel::IDEAL,
                to_sender: LinkModel::IDEAL,
            },
            HostConfig {
                clock: OscillatorModel::ideal(25.0),
                from_sender: LinkModel::IDEAL,
                to_sender: LinkModel::IDEAL,
            },
        ];
        let mut receivers = vec![
            ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
        ];
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
        cfg.objective_window = Some((4.0, 12.0));
        cfg.objective_weights = LIPSYNC_WEIGHTS;

        let report = run_report(cfg, 12.5, 1);
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
            report.roughness_per_s2 < 1e-10,
            "with_peers={with_peers}: roughness={}",
            report.roughness_per_s2
        );
        assert_eq!(report.missed_per_s, 0.0);
        assert_eq!(report.discontinuities_per_s, 0.0);
    }
}

#[test]
fn full_dsp_ramp_with_peer_sync_matches_fast_core_and_recovers_sub_milliframe_positions() {
    let build = |audio_mode: AudioMode| {
        let mut sender = SenderConfig::standard(
            OscillatorModel::ideal(3.0),
            OscillatorModel::ideal(0.0),
            20_000_000,
        );
        sender.signal = SignalMode::Ramp;
        let hosts = vec![
            HostConfig {
                clock: OscillatorModel::ideal(-2.0),
                from_sender: LinkModel::IDEAL,
                to_sender: LinkModel::IDEAL,
            },
            HostConfig {
                clock: OscillatorModel::ideal(7.0),
                from_sender: LinkModel::IDEAL,
                to_sender: LinkModel::IDEAL,
            },
        ];
        let mut receivers = vec![
            ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
        ];
        wire_full_peer_mesh(&mut receivers, WEIGHT_UNITY_Q16);
        for rx in &mut receivers {
            rx.audio_mode = audio_mode;
            rx.record_pcm = audio_mode == AudioMode::FullDsp;
        }
        let mut cfg = SceneConfig::new(sender, hosts, receivers);
        cfg.peer_link = LinkModel::IDEAL;
        cfg.objective_window = Some((1.0, 2.0));
        cfg.objective_weights = LIPSYNC_WEIGHTS;
        let mut scene = Scene::new(cfg, &Generator::new(19));
        scene.run(TrueTime::from_seconds(2.1));
        scene
    };

    let fast = build(AudioMode::FastCore);
    let full = build(AudioMode::FullDsp);

    assert!(
        full.sync_snapshot(0).is_some_and(|s| s.peer_active),
        "peer sync should engage on speaker 0"
    );
    assert!(
        full.sync_snapshot(1).is_some_and(|s| s.peer_active),
        "peer sync should engage on speaker 1"
    );

    for sp in 0..2 {
        let mut checked = 0usize;
        let mut max_err = 0.0_f64;
        for cycle in full.recorded_cycles(sp) {
            if cycle.out_start_s < 1.0 || cycle.plan.frames == 0 {
                continue;
            }
            for (i, &sample) in cycle.channel0.iter().enumerate() {
                if i >= cycle.plan.frames as usize {
                    break;
                }
                let Some(pos) = cycle.plan.start.advance(cycle.plan.step, i as u64) else {
                    continue;
                };
                #[allow(clippy::cast_precision_loss)]
                let expected =
                    pos.frame() as f64 + pos.fraction() as f64 / 18_446_744_073_709_551_616.0;
                if let Some(decoded) = decode_ramp_position(sample, expected, 40.0) {
                    max_err = max_err.max((decoded - expected).abs());
                    checked += 1;
                }
            }
        }
        assert!(checked > 20_000, "speaker {sp}: checked={checked}");
        assert!(max_err < 1e-3, "speaker {sp}: max_err={max_err}");
    }

    let fast_rep = fast.finish_objectives().expect("fast report");
    let full_rep = full.finish_objectives().expect("full report");
    assert!((fast_rep.sync_s2 - full_rep.sync_s2).abs() < 1e-18);
    assert!((fast_rep.roughness_per_s2 - full_rep.roughness_per_s2).abs() < 1e-18);
}

#[test]
fn wireless_wandering_sender_to_wired_peers_reduces_sync_error_dramatically() {
    let mut star_syncs = Vec::new();
    let mut peer_syncs = Vec::new();
    for seed in 101..106 {
        let star_cfg = build_two_speaker_scene(
            SyncMode::Peer,
            false,
            LinkModel::WIRELESS,
            0.0,
            LinkModel::WIRED_CALM,
            FrequencyNoise::WANDERING_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            WEIGHT_UNITY_Q16,
            1.0,
            25_000_000,
            None,
            80_000_000,
            (8.0, 24.0),
        );
        let peer_cfg = build_two_speaker_scene(
            SyncMode::Peer,
            true,
            LinkModel::WIRELESS,
            0.0,
            LinkModel::WIRED_CALM,
            FrequencyNoise::WANDERING_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            WEIGHT_UNITY_Q16,
            1.0,
            25_000_000,
            None,
            80_000_000,
            (8.0, 24.0),
        );
        star_syncs.push(run_report(star_cfg, 25.0, seed).sync_rms_us);
        peer_syncs.push(run_report(peer_cfg, 25.0, seed).sync_rms_us);
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
fn asymmetric_sender_links_show_star_bias_and_peer_link_weight_mitigation() {
    let asym_s = 1_000e-6; // +1000 us fwd / 0 rev on host 0, opposite on host 1 -> 1000 us pairwise spread
    let star_rep = run_report(
        build_two_speaker_scene(
            SyncMode::Peer,
            false,
            LinkModel::WIRED_CALM,
            asym_s,
            LinkModel::WIRED_CALM,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            WEIGHT_UNITY_Q16,
            1.0,
            25_000_000,
            None,
            30_000_000,
            (8.0, 20.0),
        ),
        21.0,
        42,
    );
    let peer_equal = run_report(
        build_two_speaker_scene(
            SyncMode::Peer,
            true,
            LinkModel::WIRED_CALM,
            asym_s,
            LinkModel::WIRED_CALM,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            WEIGHT_UNITY_Q16,
            1.0,
            25_000_000,
            None,
            30_000_000,
            (8.0, 20.0),
        ),
        21.0,
        42,
    );
    // Downweight asymmetric sender link (`weight = 0.05` -> 3277 in Q16).
    let peer_weighted = run_report(
        build_two_speaker_scene(
            SyncMode::Peer,
            true,
            LinkModel::WIRED_CALM,
            asym_s,
            LinkModel::WIRED_CALM,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            3_277,
            1.0,
            25_000_000,
            None,
            30_000_000,
            (8.0, 20.0),
        ),
        21.0,
        42,
    );

    // Star suffers full ~500 us RMS (= 1000 us / 2) bias on ±1000 us asymmetry.
    assert!(
        star_rep.sync_rms_us > 450.0,
        "star should exhibit asymmetry floor: {}",
        star_rep.sync_rms_us
    );
    // Equal-weight peer BLUE cuts asymmetry bias by ~3x on a symmetric triangle.
    assert!(
        peer_equal.sync_rms_us < star_rep.sync_rms_us * 0.5,
        "equal-weight peer ({:.1} us) should strongly reduce star bias ({:.1} us)",
        peer_equal.sync_rms_us,
        star_rep.sync_rms_us
    );
    // Downweighting the asymmetric sender link collapses pairwise bias further.
    assert!(
        peer_weighted.sync_rms_us < peer_equal.sync_rms_us * 0.35,
        "weighted peer ({:.1} us) should beat equal-weight peer ({:.1} us)",
        peer_weighted.sync_rms_us,
        peer_equal.sync_rms_us
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
    );
    let hosts = vec![
        HostConfig {
            clock: OscillatorModel {
                offset: -10.0,
                frequency: 20e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            from_sender: LinkModel::WIRED_CALM,
            to_sender: LinkModel::WIRED_CALM,
        },
        HostConfig {
            clock: OscillatorModel {
                offset: 100.0,
                frequency: -25e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            from_sender: LinkModel::WIRED_CALM,
            to_sender: LinkModel::WIRED_CALM,
        },
        HostConfig {
            clock: OscillatorModel {
                offset: -500.0,
                frequency: 5e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            from_sender: LinkModel::WIRED_CALM,
            to_sender: LinkModel::WIRED_CALM,
        },
    ];
    let mut receivers = vec![
        ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
        ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
        ReceiverConfig::peer(2, 3, OscillatorModel::ideal(0.0)),
        ReceiverConfig::peer(2, 4, OscillatorModel::ideal(0.0)),
    ];
    wire_full_peer_mesh(&mut receivers, WEIGHT_UNITY_Q16);
    let mut cfg = SceneConfig::new(sender.clone(), hosts, receivers);
    cfg.objective_window = Some((6.0, 18.0));
    cfg.objective_weights = LIPSYNC_WEIGHTS;
    let wired_rep = run_report(cfg, 19.0, 77);
    assert!(
        wired_rep.sync_rms_us < 10.0,
        "3-host/4-speaker wired sync_rms_us={}",
        wired_rep.sync_rms_us
    );
    assert_eq!(wired_rep.missed_per_s, 0.0);
    assert_eq!(wired_rep.discontinuities_per_s, 0.0);

    // 2 wired + 2 wireless hosts with shared AP contention.
    let mixed_hosts = vec![
        HostConfig {
            clock: OscillatorModel {
                offset: -20.0,
                frequency: 15e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            from_sender: LinkModel::WIRED_CALM,
            to_sender: LinkModel::WIRED_CALM,
        },
        HostConfig {
            clock: OscillatorModel {
                offset: 40.0,
                frequency: -15e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            from_sender: LinkModel::WIRED_CALM,
            to_sender: LinkModel::WIRED_CALM,
        },
        HostConfig {
            clock: OscillatorModel {
                offset: -100.0,
                frequency: 30e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            from_sender: LinkModel::WIRELESS,
            to_sender: LinkModel::WIRELESS,
        },
        HostConfig {
            clock: OscillatorModel {
                offset: 200.0,
                frequency: -30e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            from_sender: LinkModel::WIRELESS,
            to_sender: LinkModel::WIRELESS,
        },
    ];
    let mut mixed_rx = vec![
        ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
        ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
        ReceiverConfig::peer(2, 3, OscillatorModel::ideal(0.0)),
        ReceiverConfig::peer(3, 4, OscillatorModel::ideal(0.0)),
    ];
    wire_full_peer_mesh(&mut mixed_rx, WEIGHT_UNITY_Q16);
    let mut mixed_sender = sender;
    mixed_sender.level_ns = 90_000_000;
    let mut mixed_cfg = SceneConfig::new(mixed_sender, mixed_hosts, mixed_rx);
    mixed_cfg.contention = Some(SharedContentionModel::uniform(
        5,
        10e-6,
        10e-6,
        500e-6,
        vec![false, false, false, true, true],
    ));
    mixed_cfg.objective_window = Some((8.0, 20.0));
    mixed_cfg.objective_weights = LIPSYNC_WEIGHTS;
    let mixed_rep = run_report(mixed_cfg, 21.0, 88);
    assert!(
        mixed_rep.sync_rms_us < 250.0,
        "2 wired + 2 wireless shared-AP sync_rms_us={}",
        mixed_rep.sync_rms_us
    );
}

#[test]
fn solo_bursty_wireless_retransmission_and_adaptive_level_reduce_misses() {
    let build = |protect: bool| {
        let mut sender = SenderConfig::standard(
            OscillatorModel {
                offset: 10.0,
                frequency: 15e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            OscillatorModel::ideal(0.0),
            30_000_000,
        );
        if protect {
            sender.kept_packets = 128;
            sender.choice = Some(Choice {
                weights: LevelWeights {
                    latency: 1.0,
                    target: 0,
                    off_target: 0.0,
                    gap: 20.0,
                    missed: 200.0,
                    moving: 0.05,
                },
                history: 512,
                slope: 20_000_000,
            });
        }
        let hosts = vec![HostConfig {
            clock: OscillatorModel {
                offset: -15.0,
                frequency: -20e-6,
                noise: FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            },
            from_sender: LinkModel::WIRELESS_BURSTY,
            to_sender: LinkModel::WIRELESS,
        }];
        let mut rx = ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0));
        rx.modal_regulation = Some(ModalRegulation::low_latency(1_000_000, 240));
        let mut cfg = SceneConfig::new(sender, hosts, vec![rx]);
        cfg.objective_window = Some((5.0, 25.0));
        cfg.objective_weights = LOW_LATENCY_WEIGHTS;
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
        "retransmission + adaptive level ({:.1} missed/s) should beat unprotected ({:.1} missed/s)",
        prot_rep.missed_per_s,
        unprot_rep.missed_per_s
    );
}

#[test]
fn dynamic_fault_recovery_speaker_restart_sender_reboot_and_peer_partition() {
    let cfg = build_two_speaker_scene(
        SyncMode::Peer,
        true,
        LinkModel::WIRED_CALM,
        0.0,
        LinkModel::WIRED_CALM,
        FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        WEIGHT_UNITY_Q16,
        1.0,
        25_000_000,
        None,
        30_000_000,
        (2.0, 50.0),
    );
    let mut scene = Scene::new(cfg, &Generator::new(66));

    // Phase 1: Initial convergence with active peers.
    scene.run(TrueTime::from_seconds(8.0));
    assert!(scene.sync_snapshot(0).is_some_and(|s| s.peer_active));
    assert!(scene.sync_snapshot(1).is_some_and(|s| s.peer_active));

    // Phase 2: Partition the direct peer link -> graceful fallback to Star after 5s timeout.
    scene.set_link_partitioned(1, 2, true);
    scene.set_link_partitioned(2, 1, true);
    scene.run(TrueTime::from_seconds(16.0));
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
    scene.run(TrueTime::from_seconds(22.0));
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
    scene.run(TrueTime::from_seconds(30.0));
    assert!(scene.sync_snapshot(1).is_some_and(|s| s.peer_active));

    // Phase 5: Sender host reboots with a massive clock jump (+500 s) and new clock_id.
    scene.reboot_sender(512.0, -35.0);
    scene.run(TrueTime::from_seconds(40.0));
    assert_eq!(scene.followed(0), Some(1_001));
    assert_eq!(scene.followed(1), Some(1_001));
    assert!(scene.sync_snapshot(0).is_some_and(|s| s.peer_active));
    assert!(scene.sync_snapshot(1).is_some_and(|s| s.peer_active));

    // Phase 6: Step host 1 clock frequency by +25 ppm -> tracks cleanly.
    scene.step_host_frequency(1, 25.0);
    scene.run(TrueTime::from_seconds(50.0));
    assert!(
        scene
            .sync_snapshot(0)
            .is_some_and(|s| s.valid && s.peer_active)
    );
}

#[test]
fn parameter_mismatch_sweeps_degrade_gracefully_without_instability() {
    // Clock-prior sweep: 0.01x .. 10x mismatch against consumer quartz + flicker.
    for &scale in &[0.01, 0.1, 1.0, 10.0] {
        let rep = run_report(
            build_two_speaker_scene(
                SyncMode::Peer,
                true,
                LinkModel::WIRED_CALM,
                0.0,
                LinkModel::WIRED_CALM,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
                WEIGHT_UNITY_Q16,
                scale,
                25_000_000,
                None,
                30_000_000,
                (6.0, 16.0),
            ),
            17.0,
            31,
        );
        assert!(
            rep.sync_rms_us < 25.0 && rep.discontinuities_per_s == 0.0,
            "prior scale {scale}: sync_rms_us={}, disc={}",
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
                WEIGHT_UNITY_Q16,
                1.0,
                floor,
                None,
                30_000_000,
                (6.0, 16.0),
            ),
            17.0,
            32,
        );
        assert!(
            rep.sync_rms_us < 30.0 && rep.discontinuities_per_s == 0.0,
            "variance floor {floor}: sync_rms_us={}",
            rep.sync_rms_us
        );
    }

    // Modal gain presets: lipsync vs low-latency.
    for &(modal, bound_us) in &[
        (ModalRegulation::lipsync(1_000_000, 240), 15.0),
        (ModalRegulation::low_latency(1_000_000, 240), 25.0),
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
                WEIGHT_UNITY_Q16,
                1.0,
                25_000_000,
                Some(modal),
                30_000_000,
                (6.0, 16.0),
            ),
            17.0,
            33,
        );
        assert!(
            rep.sync_rms_us < bound_us && rep.discontinuities_per_s == 0.0,
            "modal {modal:?}: sync_rms_us={}",
            rep.sync_rms_us
        );
    }
}

#[test]
fn oracle_analytical_benchmarks_agree_with_closed_form_identities() {
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

    // [ORACLE / CENTRALIZED BENCHMARK] Filtered star Lyapunov gain stays positive and finite.
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
    let gain = oracle::optimal_filtered_star_gain(model);
    let cost = oracle::filtered_star_lyapunov_cost(model, gain);
    assert!(gain > 0.0 && gain < 1.0 && cost.is_finite() && cost > 0.0);
}
