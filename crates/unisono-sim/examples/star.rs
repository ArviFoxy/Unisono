// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Reproducible multi-seed benchmark suite for `docs/star-and-peer-analysis.tex`.
//!
//! Runs the production [`unisono_runtime`] network and playback engines
//! (`SenderNetEngine`, `ReceiverNetEngine`, `ReceiverPlayback`,
//! `ReportSchedule`) over real serialized UDP wire bytes via
//! [`unisono_sim::scene::Scene`], scoring all six canonical objectives of
//! `Unisono.Spec.Objectives` alongside `[ORACLE / CENTRALIZED BENCHMARK]`
//! analytical lower bounds from [`unisono_sim::oracle`].
//!
//! Usage:
//! - Full multi-seed benchmark (tables for the report):
//!   `cargo run --release -p unisono-sim --example star`
//! - Fast smoke check (run by `just test`):
//!   `cargo run --quiet -p unisono-sim --example star -- --smoke`

use std::env;

use unisono_core::kalman::NoisePrior;
use unisono_core::player::ModalRegulation;
use unisono_core::sync::WEIGHT_UNITY_Q16;
use unisono_runtime::level::{Choice, Weights as LevelWeights};
use unisono_runtime::receive::{Reporting, SyncMode};
use unisono_sim::TrueTime;
use unisono_sim::clock::{FrequencyNoise, OscillatorModel};
use unisono_sim::link::{LinkModel, SharedContentionModel};
use unisono_sim::objectives::{ObjectiveReport, ObjectiveWeights, Quantiles, quantiles};
use unisono_sim::oracle;
use unisono_sim::random::Generator;
use unisono_sim::scene::{HostConfig, PathDelay, ReceiverConfig, Scene, SceneConfig, SenderConfig};

const FULL_SEEDS: [u64; 10] = [101, 202, 303, 404, 505, 606, 707, 808, 909, 1010];
const SMOKE_SEEDS: [u64; 1] = [101];

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

#[derive(Clone, Copy)]
struct RunHorizon {
    seeds: &'static [u64],
    duration_s: f64,
    window: (f64, f64),
}

impl RunHorizon {
    fn for_mode(smoke: bool) -> Self {
        if smoke {
            Self {
                seeds: &SMOKE_SEEDS,
                duration_s: 12.5,
                window: (6.0, 12.0),
            }
        } else {
            Self {
                seeds: &FULL_SEEDS,
                duration_s: 36.0,
                window: (10.0, 35.0),
            }
        }
    }
}

struct Summary {
    sync_rms_us: Quantiles,
    max_spread_us: Quantiles,
    tracking_rms_us: Quantiles,
    mean_latency_ms: Quantiles,
    roughness: Quantiles,
    missed_per_s: Quantiles,
    disc_per_s: Quantiles,
}

fn summarize(reports: &[ObjectiveReport]) -> Summary {
    let collect = |f: fn(&ObjectiveReport) -> f64| -> Quantiles {
        let vals: Vec<f64> = reports.iter().map(f).collect();
        quantiles(&vals)
    };
    Summary {
        sync_rms_us: collect(|r| r.sync_rms_us),
        max_spread_us: collect(|r| r.max_abs_pair_spread_us),
        tracking_rms_us: collect(|r| r.tracking_s2.max(0.0).sqrt() * 1e6),
        mean_latency_ms: collect(|r| r.mean_latency_s * 1e3),
        roughness: collect(|r| r.roughness_per_s2),
        missed_per_s: collect(|r| r.missed_per_s),
        disc_per_s: collect(|r| r.discontinuities_per_s),
    }
}

fn print_summary_row(label: &str, s: &Summary) {
    println!(
        "{label:<44} | {:7.2} ({:5.2}-{:5.2}) | {:7.1} | {:8.1} | {:6.2} | {:9.2e} | {:6.2} | {:5.3}",
        s.sync_rms_us.median,
        s.sync_rms_us.p25,
        s.sync_rms_us.p75,
        s.max_spread_us.median,
        s.tracking_rms_us.median,
        s.mean_latency_ms.median,
        s.roughness.median,
        s.missed_per_s.median,
        s.disc_per_s.median,
    );
}

fn print_table_header(title: &str) {
    println!("\n=== {title} ===");
    println!(
        "{:<44} | {:>21} | {:>7} | {:>8} | {:>6} | {:>9} | {:>6} | {:>5}",
        "Configuration",
        "Sync RMS us (IQR)",
        "Peak us",
        "Trk us",
        "Lat ms",
        "Rough s-2",
        "Miss/s",
        "Clk/s"
    );
    println!("{}", "-".repeat(124));
}

fn wire_full_peer_mesh(receivers: &mut [ReceiverConfig], peer_weight_q16: u32) {
    let count = receivers.len();
    for (idx, rx) in receivers.iter_mut().enumerate() {
        rx.peers = (0..count)
            .filter(|&other| other != idx)
            .map(|other| (other, peer_weight_q16))
            .collect();
    }
}

fn run_multi_seed(horizon: RunHorizon, build: impl Fn() -> SceneConfig) -> Summary {
    let mut reports = Vec::with_capacity(horizon.seeds.len());
    for &seed in horizon.seeds {
        let mut scene = Scene::new(build(), &Generator::new(seed));
        scene.run(TrueTime::from_seconds(horizon.duration_s));
        reports.push(scene.finish_objectives().expect("objectives enabled"));
    }
    summarize(&reports)
}

/// Prints Section 1: `[ORACLE / CENTRALIZED BENCHMARK]` analytical bounds.
#[allow(clippy::too_many_lines)]
fn print_oracle_benchmarks(smoke: bool) {
    println!("=== SECTION 1: [ORACLE / CENTRALIZED BENCHMARK] ANALYTICAL BOUNDS ===");
    let cycle = 256.0 / 48_000.0;
    let c_sync = oracle::cycle_position_weight(1e6, 1e2, cycle);
    let c_track = oracle::cycle_position_weight(1e4, 1e2, cycle);
    let g_track_only = oracle::gain_for_weight(c_track);
    let g_uncorr_3 = oracle::gain_for_weight(oracle::decentralized_star_weight(3, c_sync, c_track));
    println!(
        "[ORACLE / CENTRALIZED BENCHMARK] Cycle dt={:.3} ms: g_track={g_track_only:.4}, g_uncorr(R=3)={g_uncorr_3:.4}",
        cycle * 1e3
    );

    println!(
        "{:<34} | {:>10} | {:>10} | {:>12}",
        "[ORACLE] Filtered Star Scenario", "sigma_meas", "g_opt*", "J_opt (cyc)"
    );
    println!("{}", "-".repeat(76));
    let cases = [
        (
            "Wired calm (R=3, consumer)",
            5e-6,
            FrequencyNoise::CONSUMER_QUARTZ,
        ),
        (
            "Wired busy (R=3, consumer)",
            20e-6,
            FrequencyNoise::CONSUMER_QUARTZ,
        ),
        (
            "Wireless (R=3, wandering src)",
            170e-6,
            FrequencyNoise::WANDERING_QUARTZ,
        ),
    ];
    for (name, sigma_s, src_noise) in cases {
        let cfg = oracle::FilteredStarLyapunov {
            receivers: 3,
            c_sync,
            c_track,
            sender_noise: src_noise,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            meas_var: sigma_s * sigma_s,
            cycle,
            meas_stride: 47,
        };
        let g_opt = oracle::optimal_filtered_star_gain(cfg);
        let cost = oracle::filtered_star_lyapunov_cost(cfg, g_opt);
        println!(
            "{name:<34} | {:>7.1} us | {:>10.5} | {:>12.3e}",
            sigma_s * 1e6,
            g_opt,
            cost
        );
    }

    // Graph-BLUE effective resistance & triangle asymmetry bias.
    let v_wired = (5e-6_f64).powi(2);
    let v_wifi = (170e-6_f64).powi(2);
    let star_wired = [
        oracle::GraphEdge {
            src: 0,
            dst: 1,
            variance: v_wired,
            bias: -500e-6,
        },
        oracle::GraphEdge {
            src: 0,
            dst: 2,
            variance: v_wired,
            bias: 500e-6,
        },
    ];
    let tri_wired = [
        star_wired[0],
        star_wired[1],
        oracle::GraphEdge {
            src: 1,
            dst: 2,
            variance: v_wired,
            bias: 0.0,
        },
    ];
    let tri_wifi_sender = [
        oracle::GraphEdge {
            src: 0,
            dst: 1,
            variance: v_wifi,
            bias: -500e-6,
        },
        oracle::GraphEdge {
            src: 0,
            dst: 2,
            variance: v_wifi,
            bias: 500e-6,
        },
        oracle::GraphEdge {
            src: 1,
            dst: 2,
            variance: v_wired,
            bias: 0.0,
        },
    ];
    println!("\n[ORACLE / CENTRALIZED BENCHMARK] Graph-BLUE (3 hosts, +/-500 us sender asym):");
    println!(
        "  Star wired:            R_eff(1,2)={:6.2} us^2  pair_bias={:6.1} us",
        oracle::effective_resistance(3, &star_wired, 1, 2) * 1e12,
        oracle::blue_pair_bias(3, &star_wired, 1, 2).abs() * 1e6
    );
    println!(
        "  Triangle wired equal:  R_eff(1,2)={:6.2} us^2  pair_bias={:6.1} us",
        oracle::effective_resistance(3, &tri_wired, 1, 2) * 1e12,
        oracle::blue_pair_bias(3, &tri_wired, 1, 2).abs() * 1e6
    );
    println!(
        "  Wi-Fi src + wired peer:R_eff(1,2)={:6.2} us^2  pair_bias={:6.1} us",
        oracle::effective_resistance(3, &tri_wifi_sender, 1, 2) * 1e12,
        oracle::blue_pair_bias(3, &tri_wifi_sender, 1, 2).abs() * 1e6
    );

    // Campbell pause margin calculator.
    let dur = if smoke { 120.0 } else { 3_600.0 };
    if let Some(m_star) = oracle::hold_margin_with_clicks(1.0 / 20.0, 30e-3, 1.0, 200.0, 20.0) {
        let (miss_frac, clk_rate, _) = oracle::pure_pause_block_metrics(
            1.0 / 20.0,
            30e-3,
            cycle,
            24.0 / 48_000.0,
            dur,
            m_star,
            7,
        );
        println!(
            "[ORACLE / CENTRALIZED BENCHMARK] Campbell margin (lambda=0.05/s, d=30 ms): m*={:.1} ms, sim_miss={:.4}%, sim_clicks={:.4}/s",
            m_star * 1e3,
            miss_frac * 100.0,
            clk_rate
        );
    }
}

/// Builds a generic `2-host / 2-speaker` scenario for topology & sweep runs.
#[allow(clippy::too_many_arguments)]
fn two_speaker_config(
    mode: SyncMode,
    with_peers: bool,
    sender_link: LinkModel,
    asym_s: f64,
    peer_link: LinkModel,
    sender_noise: FrequencyNoise,
    rx_noise: FrequencyNoise,
    sender_weight_q16: u32,
    prior_scale: f64,
    variance_floor_ns2: u64,
    modal_reg: Option<ModalRegulation>,
    level_ns: i64,
    window: (f64, f64),
    weights: ObjectiveWeights,
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
    let mut fwd0 = sender_link;
    let mut rev0 = sender_link;
    fwd0.minimum += asym_s.max(0.0);
    rev0.minimum += (-asym_s).max(0.0);

    let mut fwd1 = sender_link;
    let mut rev1 = sender_link;
    fwd1.minimum += (-asym_s).max(0.0);
    rev1.minimum += asym_s.max(0.0);

    let hosts = vec![
        HostConfig {
            clock: OscillatorModel {
                offset: -5.0,
                frequency: -20e-6,
                noise: rx_noise,
            },
            from_sender: fwd0,
            to_sender: rev0,
        },
        HostConfig {
            clock: OscillatorModel {
                offset: 30.0,
                frequency: 25e-6,
                noise: rx_noise,
            },
            from_sender: fwd1,
            to_sender: rev1,
        },
    ];
    let sender_prior = if sender_noise == FrequencyNoise::ZERO {
        NoisePrior::TCXO
    } else {
        sender_noise.scale(prior_scale).to_core_prior()
    };
    let local_prior = if rx_noise == FrequencyNoise::ZERO {
        NoisePrior::TCXO
    } else {
        rx_noise.scale(prior_scale).to_core_prior()
    };
    let make_rx = |host: usize, id: u64, ppm: f64| {
        let dev = OscillatorModel {
            offset: 0.0,
            frequency: ppm * 1e-6,
            noise: rx_noise,
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
    cfg.objective_weights = weights;
    cfg
}

/// Prints Section 2: Multi-topology production protocol comparisons.
#[allow(clippy::too_many_lines)]
fn print_topology_comparisons(horizon: RunHorizon) {
    print_table_header("SECTION 2: [PRODUCTION PROTOCOL] MULTI-TOPOLOGY COMPARISONS");
    let lipsync = Some(ModalRegulation::lipsync(1_000_000, 240));
    let low_lat = Some(ModalRegulation::low_latency(1_000_000, 240));
    let cq = FrequencyNoise::CONSUMER_QUARTZ_FLICKER;
    let wq = FrequencyNoise::WANDERING_QUARTZ;

    // 1. Ideal noiseless baseline.
    let ideal_peer = run_multi_seed(horizon, || {
        two_speaker_config(
            SyncMode::Peer,
            true,
            LinkModel::IDEAL,
            0.0,
            LinkModel::IDEAL,
            FrequencyNoise::ZERO,
            FrequencyNoise::ZERO,
            WEIGHT_UNITY_Q16,
            1.0,
            25_000_000,
            lipsync,
            20_000_000,
            horizon.window,
            LIPSYNC_WEIGHTS,
        )
    });
    print_summary_row("Ideal 2-host/2-spk: Peer", &ideal_peer);

    // 2. 2-host / 2-speaker wired LAN.
    for &(label, mode, peers, modal, weights) in &[
        (
            "Wired 2-host/2-spk: Hull",
            SyncMode::Hull,
            false,
            None,
            LIPSYNC_WEIGHTS,
        ),
        (
            "Wired 2-host/2-spk: Star",
            SyncMode::Peer,
            false,
            lipsync,
            LIPSYNC_WEIGHTS,
        ),
        (
            "Wired 2-host/2-spk: Peer (lipsync)",
            SyncMode::Peer,
            true,
            lipsync,
            LIPSYNC_WEIGHTS,
        ),
        (
            "Wired 2-host/2-spk: Peer (low-lat)",
            SyncMode::Peer,
            true,
            low_lat,
            LOW_LATENCY_WEIGHTS,
        ),
    ] {
        let s = run_multi_seed(horizon, || {
            two_speaker_config(
                mode,
                peers,
                LinkModel::WIRED_CALM,
                0.0,
                LinkModel::WIRED_CALM,
                cq,
                cq,
                WEIGHT_UNITY_Q16,
                1.0,
                25_000_000,
                modal,
                30_000_000,
                horizon.window,
                weights,
            )
        });
        print_summary_row(label, &s);
    }

    // 3. 3-host / 4-speaker co-located wired LAN.
    for &(label, mode, peers) in &[
        ("Wired 3-host/4-spk coloc: Star", SyncMode::Peer, false),
        ("Wired 3-host/4-spk coloc: Peer", SyncMode::Peer, true),
    ] {
        let s = run_multi_seed(horizon, || {
            let sender = SenderConfig::standard(
                OscillatorModel {
                    offset: 50.0,
                    frequency: 10e-6,
                    noise: cq,
                },
                OscillatorModel {
                    offset: 0.0,
                    frequency: -15e-6,
                    noise: cq,
                },
                30_000_000,
            );
            let hosts = vec![
                HostConfig {
                    clock: OscillatorModel {
                        offset: -10.0,
                        frequency: 20e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRED_CALM,
                    to_sender: LinkModel::WIRED_CALM,
                },
                HostConfig {
                    clock: OscillatorModel {
                        offset: 100.0,
                        frequency: -25e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRED_CALM,
                    to_sender: LinkModel::WIRED_CALM,
                },
                HostConfig {
                    clock: OscillatorModel {
                        offset: -500.0,
                        frequency: 5e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRED_CALM,
                    to_sender: LinkModel::WIRED_CALM,
                },
            ];
            let mut rxs = vec![
                ReceiverConfig::peer(
                    0,
                    1,
                    OscillatorModel {
                        offset: 0.0,
                        frequency: 15e-6,
                        noise: cq,
                    },
                ),
                ReceiverConfig::peer(
                    1,
                    2,
                    OscillatorModel {
                        offset: 0.0,
                        frequency: -20e-6,
                        noise: cq,
                    },
                ),
                ReceiverConfig::peer(
                    2,
                    3,
                    OscillatorModel {
                        offset: 0.0,
                        frequency: 10e-6,
                        noise: cq,
                    },
                ),
                ReceiverConfig::peer(
                    2,
                    4,
                    OscillatorModel {
                        offset: 0.0,
                        frequency: -12e-6,
                        noise: cq,
                    },
                ),
            ];
            for rx in &mut rxs {
                rx.sync_mode = mode;
            }
            if peers {
                wire_full_peer_mesh(&mut rxs, WEIGHT_UNITY_Q16);
            }
            let mut cfg = SceneConfig::new(sender, hosts, rxs);
            cfg.objective_window = Some(horizon.window);
            cfg.objective_weights = LIPSYNC_WEIGHTS;
            cfg
        });
        print_summary_row(label, &s);
    }

    // 4. Wireless wandering sender -> 3 wired peers.
    for &(label, mode, peers, modal, weights) in &[
        (
            "Wi-Fi src -> 3 wired: Hull",
            SyncMode::Hull,
            false,
            None,
            LIPSYNC_WEIGHTS,
        ),
        (
            "Wi-Fi src -> 3 wired: Star",
            SyncMode::Peer,
            false,
            lipsync,
            LIPSYNC_WEIGHTS,
        ),
        (
            "Wi-Fi src -> 3 wired: Peer (lipsync)",
            SyncMode::Peer,
            true,
            lipsync,
            LIPSYNC_WEIGHTS,
        ),
        (
            "Wi-Fi src -> 3 wired: Peer (low-lat)",
            SyncMode::Peer,
            true,
            low_lat,
            LOW_LATENCY_WEIGHTS,
        ),
    ] {
        let s = run_multi_seed(horizon, || {
            let sender = SenderConfig::standard(
                OscillatorModel {
                    offset: 12.0,
                    frequency: 15e-6,
                    noise: wq,
                },
                OscillatorModel {
                    offset: 0.0,
                    frequency: -10e-6,
                    noise: wq,
                },
                90_000_000,
            );
            let hosts = vec![
                HostConfig {
                    clock: OscillatorModel {
                        offset: -5.0,
                        frequency: -20e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRELESS,
                    to_sender: LinkModel::WIRELESS,
                },
                HostConfig {
                    clock: OscillatorModel {
                        offset: 30.0,
                        frequency: 25e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRELESS,
                    to_sender: LinkModel::WIRELESS,
                },
                HostConfig {
                    clock: OscillatorModel {
                        offset: -80.0,
                        frequency: -10e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRELESS,
                    to_sender: LinkModel::WIRELESS,
                },
            ];
            let mut rxs: Vec<ReceiverConfig> = (0..3)
                .map(|idx| {
                    let dev = OscillatorModel {
                        offset: 0.0,
                        frequency: 0.0,
                        noise: cq,
                    };
                    let mut rx = match mode {
                        SyncMode::Peer => ReceiverConfig::peer(idx, (idx + 1) as u64, dev),
                        SyncMode::Hull => ReceiverConfig::hull(idx, (idx + 1) as u64, dev),
                    };
                    rx.sync_settings.sender_prior = wq.to_core_prior();
                    rx.sync_settings.local_prior = cq.to_core_prior();
                    if mode == SyncMode::Peer {
                        rx.modal_regulation = modal.or(rx.modal_regulation);
                    }
                    rx
                })
                .collect();
            if mode == SyncMode::Peer && peers {
                wire_full_peer_mesh(&mut rxs, WEIGHT_UNITY_Q16);
            }
            let mut cfg = SceneConfig::new(sender, hosts, rxs);
            cfg.peer_link = LinkModel::WIRED_CALM;
            cfg.objective_window = Some(horizon.window);
            cfg.objective_weights = weights;
            cfg
        });
        print_summary_row(label, &s);
    }

    // 5. 2 wired + 2 wireless shared AP contention.
    for &(label, peers) in &[
        ("2 wired + 2 Wi-Fi (shared AP): Star", false),
        ("2 wired + 2 Wi-Fi (shared AP): Peer", true),
    ] {
        let s = run_multi_seed(horizon, || {
            let sender = SenderConfig::standard(
                OscillatorModel {
                    offset: 20.0,
                    frequency: 10e-6,
                    noise: cq,
                },
                OscillatorModel::ideal(0.0),
                90_000_000,
            );
            let hosts = vec![
                HostConfig {
                    clock: OscillatorModel {
                        offset: -20.0,
                        frequency: 15e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRED_CALM,
                    to_sender: LinkModel::WIRED_CALM,
                },
                HostConfig {
                    clock: OscillatorModel {
                        offset: 40.0,
                        frequency: -15e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRED_CALM,
                    to_sender: LinkModel::WIRED_CALM,
                },
                HostConfig {
                    clock: OscillatorModel {
                        offset: -100.0,
                        frequency: 30e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRELESS,
                    to_sender: LinkModel::WIRELESS,
                },
                HostConfig {
                    clock: OscillatorModel {
                        offset: 200.0,
                        frequency: -30e-6,
                        noise: cq,
                    },
                    from_sender: LinkModel::WIRELESS,
                    to_sender: LinkModel::WIRELESS,
                },
            ];
            let mut rxs: Vec<ReceiverConfig> = (0..4)
                .map(|i| ReceiverConfig::peer(i, (i + 1) as u64, OscillatorModel::ideal(0.0)))
                .collect();
            if peers {
                wire_full_peer_mesh(&mut rxs, WEIGHT_UNITY_Q16);
            }
            let mut cfg = SceneConfig::new(sender, hosts, rxs);
            cfg.contention = Some(SharedContentionModel::uniform(
                5,
                10e-6,
                10e-6,
                500e-6,
                vec![false, false, false, true, true],
            ));
            cfg.objective_window = Some(horizon.window);
            cfg.objective_weights = LIPSYNC_WEIGHTS;
            cfg
        });
        print_summary_row(label, &s);
    }

    // 6. 1-to-1 solo bursty wireless: unprotected vs retransmit + adaptive chooser.
    for &(label, protect) in &[
        ("1-to-1 bursty Wi-Fi: fixed/no-retx", false),
        ("1-to-1 bursty Wi-Fi: retx+Chooser", true),
    ] {
        let s = run_multi_seed(horizon, || {
            let mut sender = SenderConfig::standard(
                OscillatorModel {
                    offset: 10.0,
                    frequency: 15e-6,
                    noise: cq,
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
                    noise: cq,
                },
                from_sender: LinkModel::WIRELESS_BURSTY,
                to_sender: LinkModel::WIRELESS,
            }];
            let mut rx = ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0));
            rx.modal_regulation = low_lat;
            let mut cfg = SceneConfig::new(sender, hosts, vec![rx]);
            cfg.objective_window = Some(horizon.window);
            cfg.objective_weights = LOW_LATENCY_WEIGHTS;
            cfg
        });
        print_summary_row(label, &s);
    }
}

/// Prints Section 3: All 4 parameter-mismatch sensitivity sweeps.
#[allow(clippy::too_many_lines)]
fn print_sensitivity_sweeps(horizon: RunHorizon) {
    let cq = FrequencyNoise::CONSUMER_QUARTZ_FLICKER;
    let lipsync = Some(ModalRegulation::lipsync(1_000_000, 240));

    // Sweep A: --clock-prior mismatch (0.01x .. 10x).
    print_table_header("SECTION 3A: [PRODUCTION PROTOCOL] CLOCK-PRIOR MISMATCH SWEEP (WIRED PEER)");
    for &scale in &[0.01, 0.1, 1.0, 10.0] {
        let s = run_multi_seed(horizon, || {
            two_speaker_config(
                SyncMode::Peer,
                true,
                LinkModel::WIRED_CALM,
                0.0,
                LinkModel::WIRED_CALM,
                cq,
                cq,
                WEIGHT_UNITY_Q16,
                scale,
                25_000_000,
                lipsync,
                30_000_000,
                horizon.window,
                LIPSYNC_WEIGHTS,
            )
        });
        print_summary_row(&format!("Clock prior scale = {scale:>5.2}x"), &s);
    }

    // Sweep B: SlidingMinRtt variance floor across link types.
    print_table_header("SECTION 3B: [PRODUCTION PROTOCOL] VARIANCE-FLOOR SWEEP");
    for &(label, link, floor_us) in &[
        ("Wired peer, floor =   1 us", LinkModel::WIRED_CALM, 1u64),
        (
            "Wired peer, floor =   5 us (default)",
            LinkModel::WIRED_CALM,
            5,
        ),
        ("Wired peer, floor =  25 us", LinkModel::WIRED_CALM, 25),
        ("Wired peer, floor = 100 us", LinkModel::WIRED_CALM, 100),
        (
            "Wi-Fi src->peer, floor =   5 us (def)",
            LinkModel::WIRELESS,
            5,
        ),
        ("Wi-Fi src->peer, floor =  25 us", LinkModel::WIRELESS, 25),
    ] {
        let level_ns = if link.minimum >= 500e-6 {
            90_000_000
        } else {
            30_000_000
        };
        let floor_ns2 = floor_us * floor_us * 1_000_000;
        let s = run_multi_seed(horizon, || {
            two_speaker_config(
                SyncMode::Peer,
                true,
                link,
                0.0,
                LinkModel::WIRED_CALM,
                cq,
                cq,
                WEIGHT_UNITY_Q16,
                1.0,
                floor_ns2,
                lipsync,
                level_ns,
                horizon.window,
                LIPSYNC_WEIGHTS,
            )
        });
        print_summary_row(label, &s);
    }

    // Sweep C: Modal gains (g_com, g_diff) trade-off.
    print_table_header(
        "SECTION 3C: [PRODUCTION PROTOCOL] MODAL-GAIN SWEEP (WI-FI SRC -> WIRED PEERS)",
    );
    let gain_cases = [
        ("g_com=0.05/s, g_diff=4.0/s (low-lat)", 3_277u32, 4 << 16),
        ("g_com=0.50/s, g_diff=4.0/s (lipsync)", 32_768, 4 << 16),
        ("g_com=2.00/s, g_diff=4.0/s", 2 << 16, 4 << 16),
        ("g_com=0.50/s, g_diff=8.0/s", 32_768, 8 << 16),
    ];
    for &(label, g_com, g_diff) in &gain_cases {
        let modal = Some(ModalRegulation {
            star_gain: 4 << 16,
            common_gain: g_com,
            diff_gain: g_diff,
            limit: 1_000_000,
            jump: 240,
        });
        let s = run_multi_seed(horizon, || {
            two_speaker_config(
                SyncMode::Peer,
                true,
                LinkModel::WIRELESS,
                0.0,
                LinkModel::WIRED_CALM,
                FrequencyNoise::WANDERING_QUARTZ,
                cq,
                WEIGHT_UNITY_Q16,
                1.0,
                25_000_000,
                modal,
                90_000_000,
                horizon.window,
                LIPSYNC_WEIGHTS,
            )
        });
        print_summary_row(label, &s);
    }

    // Sweep D: Unknown static sender-link asymmetry (with & without --link-weight).
    print_table_header("SECTION 3D: [PRODUCTION PROTOCOL] STATIC ASYMMETRY & --link-weight SWEEP");
    for &asym_us in &[0.0_f64, 200.0, 1_000.0, 2_000.0] {
        let asym_s = asym_us * 1e-6;
        for &(tag, peers, sender_w) in &[
            ("Star", false, WEIGHT_UNITY_Q16),
            ("Peer (w_src=1.00)", true, WEIGHT_UNITY_Q16),
            ("Peer (w_src=0.05)", true, 3_277),
        ] {
            let s = run_multi_seed(horizon, || {
                two_speaker_config(
                    SyncMode::Peer,
                    peers,
                    LinkModel::WIRED_CALM,
                    asym_s,
                    LinkModel::WIRED_CALM,
                    cq,
                    cq,
                    sender_w,
                    1.0,
                    25_000_000,
                    lipsync,
                    30_000_000,
                    horizon.window,
                    LIPSYNC_WEIGHTS,
                )
            });
            print_summary_row(&format!("Asym {asym_us:4.0} us: {tag}"), &s);
        }
    }
}

fn main() {
    let smoke = env::args().any(|arg| arg == "--smoke");
    let horizon = RunHorizon::for_mode(smoke);
    println!(
        "Unisono faithful production simulation suite (mode={}, seeds={}, window=[{:.0}s, {:.0}s))",
        if smoke { "smoke" } else { "full" },
        horizon.seeds.len(),
        horizon.window.0,
        horizon.window.1,
    );
    print_oracle_benchmarks(smoke);
    print_topology_comparisons(horizon);
    print_sensitivity_sweeps(horizon);
}
