// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Reproducible multi-seed steady-state benchmark suite for
//! `docs/star-and-peer-analysis.tex`.
//!
//! Runs the shipped [`unisono_runtime`] SPSC-ring pipelines (`CaptureEnd`,
//! `SenderNetBridge`, `ReceiverNetBridge`, `ShippedAudio` /
//! `ReceiverAudio<256, 64, 8, 64>`) over real serialized UDP wire bytes via
//! [`unisono_sim::scene::Scene`], scoring all six canonical objectives of
//! `Unisono.Spec.Objectives` strictly from black-box rendered PCM output via
//! `ProbeDecoder`, alongside offline `[ORACLE / MODEL BENCHMARK]` and
//! `[ORACLE / CENTRALIZED BENCHMARK]` references from [`unisono_sim::oracle`].
//!
//! Usage:
//! - Full 300 s 10-seed steady-state benchmark (`[200 s, 299 s)` window):
//!   `cargo run --release -p unisono-sim --example star`
//! - Fast smoke check (run by `just test`):
//!   `cargo run --quiet -p unisono-sim --example star -- --smoke`

use std::env;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

use unisono_core::kalman::NoisePrior;
use unisono_core::player::ModalRegulation;
use unisono_core::sync::WEIGHT_UNITY_Q16;
use unisono_runtime::receive::{Reporting, SyncMode};
use unisono_sim::TrueTime;
use unisono_sim::clock::{FrequencyNoise, OscillatorModel};
use unisono_sim::link::{LinkModel, SharedContentionModel};
use unisono_sim::objectives::{ObjectiveReport, ObjectiveWeights, Quantiles, quantiles};
use unisono_sim::oracle;
use unisono_sim::random::Generator;
use unisono_sim::scene::{
    CycleLength, HostConfig, PathDelay, ReceiverConfig, Scene, SceneConfig, SenderConfig,
};

const FULL_SEEDS: [u64; 10] = [101, 202, 303, 404, 505, 606, 707, 808, 909, 1010];
const SMOKE_SEEDS: [u64; 1] = [101];
const CAMPBELL_SEEDS: [u64; 20] = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
];

/// Realistic capture-device timestamp noise std (5 us) on non-ideal scenes.
const REALISTIC_CAPTURE_STD_S: f64 = 5e-6;

/// Realistic playback-device timestamp uniform half-range (±5 us) on non-ideal
/// scenes.
const REALISTIC_DEVICE_JITTER_NS: i64 = 5_000;

/// Realistic RX-to-`T3` software processing latency (5 us) on non-ideal hosts.
const REALISTIC_REPLY_PROC_S: f64 = 5e-6;

/// Realistic post-`T3` kernel/NIC send latency on a wired sender (10 us).
const REALISTIC_WIRED_SENDER_SEND_S: f64 = 10e-6;

/// Realistic post-`T3` kernel/NIC send latency on a wireless sender (15 us).
const REALISTIC_WIFI_SENDER_SEND_S: f64 = 15e-6;

/// Heterogeneous per-host post-`T3` send latencies (8, 12, 14, 10 us) so
/// responder send-latency bias does not artificially cancel across peers.
const REALISTIC_HOST_SEND_S: [f64; 4] = [8e-6, 12e-6, 14e-6, 10e-6];

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
            // 300 s runs scored over the true steady-state window [200 s, 299 s)
            // with 2.5 s tail so every in-window frame plays out even under
            // adaptive high-latency Wi-Fi buffering.
            Self {
                seeds: &FULL_SEEDS,
                duration_s: 301.5,
                window: (200.0, 299.0),
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
        "{label:<44} | {:7.2} [{:5.2}-{:5.2}] (max {:6.1}) | {:7.1} [{:5.1}-{:5.1}] | {:8.1} [{:6.1}-{:6.1}] | {:6.2} [{:5.2}-{:5.2}] | {:8.2e} [{:8.2e}-{:8.2e}] | {:6.2} [{:5.2}-{:5.2}] | {:5.3} [{:5.3}-{:5.3}]",
        s.sync_rms_us.median,
        s.sync_rms_us.p25,
        s.sync_rms_us.p75,
        s.sync_rms_us.max,
        s.max_spread_us.median,
        s.max_spread_us.p25,
        s.max_spread_us.p75,
        s.tracking_rms_us.median,
        s.tracking_rms_us.p25,
        s.tracking_rms_us.p75,
        s.mean_latency_ms.median,
        s.mean_latency_ms.p25,
        s.mean_latency_ms.p75,
        s.roughness.median,
        s.roughness.p25,
        s.roughness.p75,
        s.missed_per_s.median,
        s.missed_per_s.p25,
        s.missed_per_s.p75,
        s.disc_per_s.median,
        s.disc_per_s.p25,
        s.disc_per_s.p75,
    );
}

fn print_table_header(title: &str) {
    println!("\n=== {title} ===");
    println!(
        "{:<44} | {:^34} | {:^21} | {:^24} | {:^20} | {:^28} | {:^20} | {:^19}",
        "Configuration",
        "Sync RMS us [IQR] (max)",
        "Peak us [IQR]",
        "Trk us [IQR]",
        "Lat ms [IQR]",
        "Rough s-2 [IQR]",
        "Miss/s [IQR]",
        "Clk/s [IQR]"
    );
    println!("{}", "-".repeat(230));
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

struct TableRow {
    label: String,
    build: Box<dyn Fn() -> SceneConfig + Sync>,
}

impl TableRow {
    fn new(label: impl Into<String>, build: impl Fn() -> SceneConfig + Sync + 'static) -> Self {
        Self {
            label: label.into(),
            build: Box::new(build),
        }
    }
}

/// Runs all `(row, seed)` jobs for one benchmark table in parallel across
/// available cores while printing rows in exact deterministic order.
fn run_table(title: &str, horizon: RunHorizon, rows: &[TableRow]) {
    print_table_header(title);
    let seed_count = horizon.seeds.len();
    let total = rows.len() * seed_count;
    if total == 0 {
        return;
    }
    let workers = thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .clamp(1, 36)
        .min(total);
    let next = AtomicUsize::new(0);
    let results: Vec<Mutex<Option<ObjectiveReport>>> =
        (0..total).map(|_| Mutex::new(None)).collect();
    thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let job = next.fetch_add(1, Ordering::Relaxed);
                    if job >= total {
                        break;
                    }
                    let row_idx = job / seed_count;
                    let seed = horizon.seeds[job % seed_count];
                    let mut scene = Scene::new((rows[row_idx].build)(), &Generator::new(seed));
                    scene.run(TrueTime::from_seconds(horizon.duration_s));
                    let report = scene.finish_objectives().expect("objectives enabled");
                    *results[job].lock().expect("result lock") = Some(report);
                }
            });
        }
    });
    for (row_idx, row) in rows.iter().enumerate() {
        let reports: Vec<ObjectiveReport> = (0..seed_count)
            .map(|s| {
                results[row_idx * seed_count + s]
                    .lock()
                    .expect("result lock")
                    .take()
                    .expect("job completed")
            })
            .collect();
        print_summary_row(&row.label, &summarize(&reports));
    }
}

/// Applies realistic hardware timestamp jitter and post-`T3` responder send
/// latency to a non-ideal scene.
fn apply_realistic_hardware(cfg: &mut SceneConfig, wireless_sender: bool) {
    cfg.sender.capture_timestamp_std_s = REALISTIC_CAPTURE_STD_S;
    cfg.sender.reply_processing_s = REALISTIC_REPLY_PROC_S;
    cfg.sender.reply_send_latency_s = if wireless_sender {
        REALISTIC_WIFI_SENDER_SEND_S
    } else {
        REALISTIC_WIRED_SENDER_SEND_S
    };
    for (idx, host) in cfg.hosts.iter_mut().enumerate() {
        host.reply_processing_s = REALISTIC_REPLY_PROC_S;
        host.reply_send_latency_s = REALISTIC_HOST_SEND_S[idx % REALISTIC_HOST_SEND_S.len()];
    }
    for rx in &mut cfg.receivers {
        rx.cycle_length = CycleLength::Fitted(REALISTIC_DEVICE_JITTER_NS);
    }
}

/// Prints explicit simulation parameter inventory matching the paper table.
fn print_parameter_summary(horizon: RunHorizon) {
    println!("--- Simulation Parameters ---");
    println!(
        "  Shipped pipeline: CaptureEnd + SenderNetBridge + ReceiverNetBridge + ShippedAudio<256,64,8,64>"
    );
    println!(
        "  Shipped defaults: rate=48kHz, ch=2, fmt=Signed24, pkt=240f, cyc=256f, lead=4ms, span=2000ms, win=2400f, kept=256, pri=consumer, report=50ms(5s)/200ms"
    );
    println!(
        "  Scoring: pure black-box PCM decoding (ProbeDecoder) against fixed World.target over [{:.0}s, {:.0}s) of {:.1}s runs ({} seeds)",
        horizon.window.0,
        horizon.window.1,
        horizon.duration_s,
        horizon.seeds.len(),
    );
    println!(
        "  Non-ideal hardware model: capture_ts_std={:.0}us, dac_ts_jitter=+/-{:.0}us, reply_proc={:.0}us, sender_T3_send={:.0}/{:.0}us (wired/wifi), host_T3_send=[8,12,14,10]us, hidden_dac_latency=0us (calibrated; sensitivity shown explicitly)",
        REALISTIC_CAPTURE_STD_S * 1e6,
        f64::from(i32::try_from(REALISTIC_DEVICE_JITTER_NS).unwrap_or(0)) * 1e-3,
        REALISTIC_REPLY_PROC_S * 1e6,
        REALISTIC_WIRED_SENDER_SEND_S * 1e6,
        REALISTIC_WIFI_SENDER_SEND_S * 1e6,
    );
}

/// Prints Section 1: Offline `[ORACLE / MODEL BENCHMARK]` and
/// `[ORACLE / CENTRALIZED BENCHMARK]` analytical references.
#[allow(clippy::too_many_lines)]
fn print_oracle_benchmarks(smoke: bool) {
    println!("\n=== SECTION 1: OFFLINE ORACLE & MODEL BENCHMARKS ===");
    let cycle = 256.0 / 48_000.0;
    let c_sync = oracle::cycle_position_weight(1e6, 1e2, cycle);
    let c_track = oracle::cycle_position_weight(1e4, 1e2, cycle);
    let g_track_only = oracle::gain_for_weight(c_track);
    let g_uncorr_3 = oracle::gain_for_weight(oracle::decentralized_star_weight(3, c_sync, c_track));
    println!(
        "[ORACLE / MODEL BENCHMARK] multiCycleCost dt={:.3} ms: g_track={g_track_only:.4}, g_uncorr(R=3)={g_uncorr_3:.4}",
        cycle * 1e3
    );

    println!(
        "[ORACLE / MODEL BENCHMARK] Filtered Star Lyapunov (numerical golden-section search for one decentralized 2-state Kalman + Regulation.law design using known true noise; NOT a lower bound over all policies):"
    );
    println!(
        "{:<34} | {:>10} | {:>10} | {:>12}",
        "Filtered Star Scenario", "sigma_meas", "g_search*", "J_model(cyc)"
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
        "  Star wired:             R_eff(1,2)={:6.2} us^2  pair_bias={:6.1} us",
        oracle::effective_resistance(3, &star_wired, 1, 2) * 1e12,
        oracle::blue_pair_bias(3, &star_wired, 1, 2).abs() * 1e6
    );
    println!(
        "  Triangle wired equal:   R_eff(1,2)={:6.2} us^2  pair_bias={:6.1} us",
        oracle::effective_resistance(3, &tri_wired, 1, 2) * 1e12,
        oracle::blue_pair_bias(3, &tri_wired, 1, 2).abs() * 1e6
    );
    println!(
        "  Wi-Fi src + wired peer: R_eff(1,2)={:6.2} us^2  pair_bias={:6.1} us",
        oracle::effective_resistance(3, &tri_wifi_sender, 1, 2) * 1e12,
        oracle::blue_pair_bias(3, &tri_wifi_sender, 1, 2).abs() * 1e6
    );

    // Campbell pause margin calculator (20-seed median & IQR in full mode).
    let dur = if smoke { 120.0 } else { 3_600.0 };
    let seeds: &[u64] = if smoke { &SMOKE_SEEDS } else { &CAMPBELL_SEEDS };
    if let Some(m_star) = oracle::hold_margin_with_clicks(1.0 / 20.0, 30e-3, 1.0, 200.0, 20.0) {
        let th_miss = oracle::campbell_fraction(1.0 / 20.0, 30e-3, m_star);
        let th_clk = oracle::click_rate(1.0 / 20.0, 30e-3, m_star);
        let mut misses = Vec::with_capacity(seeds.len());
        let mut clicks = Vec::with_capacity(seeds.len());
        for &seed in seeds {
            let (miss_frac, clk_rate, _) = oracle::pure_pause_block_metrics(
                1.0 / 20.0,
                30e-3,
                cycle,
                24.0 / 48_000.0,
                dur,
                m_star,
                seed,
            );
            misses.push(miss_frac * 100.0);
            clicks.push(clk_rate);
        }
        let q_miss = quantiles(&misses);
        let q_clk = quantiles(&clicks);
        println!(
            "[ORACLE / MODEL BENCHMARK] Campbell J_buf margin (lambda=0.05/s, d=30 ms, {} seeds x {:.0}s): m*={:.1} ms | theory miss={:.4}%, clicks={:.4}/s | sim_miss={:.4}% [{:.4}-{:.4}%], sim_clicks={:.4}/s [{:.4}-{:.4}/s]",
            seeds.len(),
            dur,
            m_star * 1e3,
            th_miss * 100.0,
            th_clk,
            q_miss.median,
            q_miss.p25,
            q_miss.p75,
            q_clk.median,
            q_clk.p25,
            q_clk.p75,
        );
    }
}

/// Builds a generic 2-host / 2-speaker scenario using ONLY CLI-expressible
/// `NoisePrior` presets.
#[allow(clippy::too_many_arguments)]
fn two_speaker_config(
    mode: SyncMode,
    with_peers: bool,
    sender_link: LinkModel,
    sender_asym_s: f64,
    peer_asym_s: f64,
    peer_link: LinkModel,
    sender_noise: FrequencyNoise,
    rx_noise: FrequencyNoise,
    sender_prior: NoisePrior,
    local_prior: NoisePrior,
    sender_weight_q16: u32,
    variance_floor_ns2: u64,
    modal_reg: Option<ModalRegulation>,
    level_ns: i64,
    window: (f64, f64),
    weights: ObjectiveWeights,
    realistic_hw: bool,
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
    let mut fwd0 = sender_link;
    let mut rev0 = sender_link;
    fwd0.minimum += sender_asym_s.max(0.0);
    rev0.minimum += (-sender_asym_s).max(0.0);

    let mut fwd1 = sender_link;
    let mut rev1 = sender_link;
    fwd1.minimum += (-sender_asym_s).max(0.0);
    rev1.minimum += sender_asym_s.max(0.0);

    let hosts = vec![
        HostConfig::new(
            OscillatorModel {
                offset: -5.0,
                frequency: -20e-6,
                noise: rx_noise,
            },
            fwd0,
            rev0,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: 30.0,
                frequency: 25e-6,
                noise: rx_noise,
            },
            fwd1,
            rev1,
        ),
    ];
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
    if peer_asym_s > 0.0 {
        let mut slow_peer = peer_link;
        slow_peer.minimum += peer_asym_s;
        cfg.link_overrides.push((1, 2, slow_peer));
    }
    cfg.objective_window = Some(window);
    cfg.objective_weights = weights;
    cfg.record_trace = false;
    if realistic_hw {
        apply_realistic_hardware(&mut cfg, sender_link.minimum >= 500e-6);
    }
    cfg
}

/// Builds the 3-wired-receiver scene fed by a wireless wandering sender using
/// explicit CLI `NoisePrior` presets.
fn wifi_src_three_wired_config(
    mode: SyncMode,
    with_peers: bool,
    modal: Option<ModalRegulation>,
    sender_prior: NoisePrior,
    local_prior: NoisePrior,
    window: (f64, f64),
    weights: ObjectiveWeights,
) -> SceneConfig {
    let cq = FrequencyNoise::CONSUMER_QUARTZ_FLICKER;
    let wq = FrequencyNoise::WANDERING_QUARTZ;
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
    )
    .with_fixed_level();
    let hosts = vec![
        HostConfig::new(
            OscillatorModel {
                offset: -5.0,
                frequency: -20e-6,
                noise: cq,
            },
            LinkModel::WIRELESS,
            LinkModel::WIRELESS,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: 30.0,
                frequency: 25e-6,
                noise: cq,
            },
            LinkModel::WIRELESS,
            LinkModel::WIRELESS,
        ),
        HostConfig::new(
            OscillatorModel {
                offset: -80.0,
                frequency: -10e-6,
                noise: cq,
            },
            LinkModel::WIRELESS,
            LinkModel::WIRELESS,
        ),
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
            rx.sync_settings.sender_prior = sender_prior;
            rx.sync_settings.local_prior = local_prior;
            if mode == SyncMode::Peer {
                rx.modal_regulation = modal.or(rx.modal_regulation);
            }
            rx
        })
        .collect();
    if mode == SyncMode::Peer && with_peers {
        wire_full_peer_mesh(&mut rxs, WEIGHT_UNITY_Q16);
    }
    let mut cfg = SceneConfig::new(sender, hosts, rxs);
    cfg.peer_link = LinkModel::WIRED_CALM;
    cfg.objective_window = Some(window);
    cfg.objective_weights = weights;
    cfg.record_trace = false;
    apply_realistic_hardware(&mut cfg, true);
    cfg
}

/// Prints Section 2: Multi-topology production protocol comparisons (all using
/// shipped CLI default `NoisePrior::CONSUMER_QUARTZ` and realistic hardware
/// timestamp jitter + responder send latency on non-ideal scenes).
#[allow(clippy::too_many_lines)]
fn print_topology_comparisons(horizon: RunHorizon) {
    let lipsync = Some(ModalRegulation::lipsync(1_000_000, 240));
    let low_lat = Some(ModalRegulation::low_latency(1_000_000, 240));
    let cq = FrequencyNoise::CONSUMER_QUARTZ_FLICKER;
    let def_prior = NoisePrior::CONSUMER_QUARTZ;
    let window = horizon.window;
    let mut rows = Vec::new();

    // 1. Ideal noiseless baseline (exact timestamps, zero responder send delay).
    rows.push(TableRow::new("Ideal 2-host/2-spk: Peer", move || {
        let sender = SenderConfig::standard(
            OscillatorModel::ideal(12.0),
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
                OscillatorModel::ideal(30.0),
                LinkModel::IDEAL,
                LinkModel::IDEAL,
            ),
        ];
        let mut rxs = vec![
            ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0)),
            ReceiverConfig::peer(1, 2, OscillatorModel::ideal(0.0)),
        ];
        wire_full_peer_mesh(&mut rxs, WEIGHT_UNITY_Q16);
        let mut cfg = SceneConfig::new(sender, hosts, rxs);
        cfg.peer_link = LinkModel::IDEAL;
        cfg.objective_window = Some(window);
        cfg.objective_weights = LIPSYNC_WEIGHTS;
        cfg.record_trace = false;
        cfg
    }));

    // 2. 2-host / 2-speaker wired LAN (realistic device jitter & responder T3).
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
        rows.push(TableRow::new(label, move || {
            two_speaker_config(
                mode,
                peers,
                LinkModel::WIRED_CALM,
                0.0,
                0.0,
                LinkModel::WIRED_CALM,
                cq,
                cq,
                def_prior,
                def_prior,
                WEIGHT_UNITY_Q16,
                25_000_000,
                modal,
                30_000_000,
                window,
                weights,
                true,
            )
        }));
    }

    // 2b. Uncalibrated DAC hardware latency sensitivity (+100 us on 1 speaker).
    rows.push(TableRow::new(
        "Wired 2-host/2-spk: Peer (+100us uncal DAC)",
        move || {
            let mut cfg = two_speaker_config(
                SyncMode::Peer,
                true,
                LinkModel::WIRED_CALM,
                0.0,
                0.0,
                LinkModel::WIRED_CALM,
                cq,
                cq,
                def_prior,
                def_prior,
                WEIGHT_UNITY_Q16,
                25_000_000,
                lipsync,
                30_000_000,
                window,
                LIPSYNC_WEIGHTS,
                true,
            );
            cfg.receivers[1].hidden_latency_s = 100e-6;
            cfg
        },
    ));

    // 3. 3-host / 4-speaker co-located wired LAN.
    for &(label, mode, peers) in &[
        ("Wired 3-host/4-spk coloc: Star", SyncMode::Peer, false),
        ("Wired 3-host/4-spk coloc: Peer", SyncMode::Peer, true),
    ] {
        rows.push(TableRow::new(label, move || {
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
            )
            .with_fixed_level();
            let hosts = vec![
                HostConfig::new(
                    OscillatorModel {
                        offset: -10.0,
                        frequency: 20e-6,
                        noise: cq,
                    },
                    LinkModel::WIRED_CALM,
                    LinkModel::WIRED_CALM,
                ),
                HostConfig::new(
                    OscillatorModel {
                        offset: 100.0,
                        frequency: -25e-6,
                        noise: cq,
                    },
                    LinkModel::WIRED_CALM,
                    LinkModel::WIRED_CALM,
                ),
                HostConfig::new(
                    OscillatorModel {
                        offset: -500.0,
                        frequency: 5e-6,
                        noise: cq,
                    },
                    LinkModel::WIRED_CALM,
                    LinkModel::WIRED_CALM,
                ),
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
            cfg.objective_window = Some(window);
            cfg.objective_weights = LIPSYNC_WEIGHTS;
            cfg.record_trace = false;
            apply_realistic_hardware(&mut cfg, false);
            cfg
        }));
    }

    // 4. Wireless wandering sender -> 3 wired peers (using shipped default
    //    `consumer` priors on both sender and local oscillators!).
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
        rows.push(TableRow::new(label, move || {
            wifi_src_three_wired_config(mode, peers, modal, def_prior, def_prior, window, weights)
        }));
    }

    // 5. 2 wired + 2 wireless shared AP contention.
    for &(label, peers) in &[
        ("2 wired + 2 Wi-Fi (shared AP): Star", false),
        ("2 wired + 2 Wi-Fi (shared AP): Peer", true),
    ] {
        rows.push(TableRow::new(label, move || {
            let sender = SenderConfig::standard(
                OscillatorModel {
                    offset: 20.0,
                    frequency: 10e-6,
                    noise: cq,
                },
                OscillatorModel::ideal(0.0),
                90_000_000,
            )
            .with_fixed_level();
            let hosts = vec![
                HostConfig::new(
                    OscillatorModel {
                        offset: -20.0,
                        frequency: 15e-6,
                        noise: cq,
                    },
                    LinkModel::WIRED_CALM,
                    LinkModel::WIRED_CALM,
                ),
                HostConfig::new(
                    OscillatorModel {
                        offset: 40.0,
                        frequency: -15e-6,
                        noise: cq,
                    },
                    LinkModel::WIRED_CALM,
                    LinkModel::WIRED_CALM,
                ),
                HostConfig::new(
                    OscillatorModel {
                        offset: -100.0,
                        frequency: 30e-6,
                        noise: cq,
                    },
                    LinkModel::WIRELESS,
                    LinkModel::WIRELESS,
                ),
                HostConfig::new(
                    OscillatorModel {
                        offset: 200.0,
                        frequency: -30e-6,
                        noise: cq,
                    },
                    LinkModel::WIRELESS,
                    LinkModel::WIRELESS,
                ),
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
            cfg.objective_window = Some(window);
            cfg.objective_weights = LIPSYNC_WEIGHTS;
            cfg.record_trace = false;
            apply_realistic_hardware(&mut cfg, false);
            cfg
        }));
    }

    // 6. 1-to-1 solo bursty wireless: fixed unprotected vs exact shipped
    //    `--protection on --level-choice on` (`kept = 256`, `slope = 500 us/s`).
    for &(label, protect) in &[
        ("1-to-1 bursty Wi-Fi: fixed/no-retx", false),
        ("1-to-1 bursty Wi-Fi: shipped retx+Chooser", true),
    ] {
        rows.push(TableRow::new(label, move || {
            let mut sender = SenderConfig::standard(
                OscillatorModel {
                    offset: 10.0,
                    frequency: 15e-6,
                    noise: cq,
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
                    noise: cq,
                },
                LinkModel::WIRELESS_BURSTY,
                LinkModel::WIRELESS,
            )];
            let mut rx = ReceiverConfig::peer(0, 1, OscillatorModel::ideal(0.0));
            rx.modal_regulation = low_lat;
            let mut cfg = SceneConfig::new(sender, hosts, vec![rx]);
            cfg.objective_window = Some(window);
            cfg.objective_weights = LOW_LATENCY_WEIGHTS;
            cfg.record_trace = false;
            apply_realistic_hardware(&mut cfg, true);
            cfg
        }));
    }

    run_table(
        "SECTION 2: [PRODUCTION PROTOCOL] MULTI-TOPOLOGY COMPARISONS",
        horizon,
        &rows,
    );
}

/// Prints Section 3: All 4 parameter-mismatch sensitivity sweeps over the
/// steady-state horizon using only CLI-expressible settings.
#[allow(clippy::too_many_lines)]
fn print_sensitivity_sweeps(horizon: RunHorizon) {
    let cq = FrequencyNoise::CONSUMER_QUARTZ_FLICKER;
    let def_prior = NoisePrior::CONSUMER_QUARTZ;
    let lipsync = Some(ModalRegulation::lipsync(1_000_000, 240));
    let window = horizon.window;

    // Sweep A: Real CLI `--sender-clock-prior` / `--clock-prior` combinations
    // across BOTH wired and wireless-sender scenes (including independent
    // sender vs local mismatches).
    let prior_combos = [
        ("tcxo / tcxo", NoisePrior::TCXO, NoisePrior::TCXO),
        (
            "consumer / consumer (default)",
            NoisePrior::CONSUMER_QUARTZ,
            NoisePrior::CONSUMER_QUARTZ,
        ),
        (
            "wandering / wandering",
            NoisePrior::WANDERING_QUARTZ,
            NoisePrior::WANDERING_QUARTZ,
        ),
        (
            "wandering / consumer",
            NoisePrior::WANDERING_QUARTZ,
            NoisePrior::CONSUMER_QUARTZ,
        ),
        (
            "tcxo / consumer",
            NoisePrior::TCXO,
            NoisePrior::CONSUMER_QUARTZ,
        ),
        (
            "consumer / wandering",
            NoisePrior::CONSUMER_QUARTZ,
            NoisePrior::WANDERING_QUARTZ,
        ),
    ];
    let mut rows_a = Vec::new();
    for &(name, s_pri, l_pri) in &prior_combos {
        rows_a.push(TableRow::new(format!("Wired Peer: {name}"), move || {
            two_speaker_config(
                SyncMode::Peer,
                true,
                LinkModel::WIRED_CALM,
                0.0,
                0.0,
                LinkModel::WIRED_CALM,
                cq,
                cq,
                s_pri,
                l_pri,
                WEIGHT_UNITY_Q16,
                25_000_000,
                lipsync,
                30_000_000,
                window,
                LIPSYNC_WEIGHTS,
                true,
            )
        }));
    }
    for &(name, s_pri, l_pri) in &prior_combos {
        rows_a.push(TableRow::new(format!("Wi-Fi->3w: {name}"), move || {
            wifi_src_three_wired_config(
                SyncMode::Peer,
                true,
                lipsync,
                s_pri,
                l_pri,
                window,
                LIPSYNC_WEIGHTS,
            )
        }));
    }
    run_table(
        "SECTION 3A: [PRODUCTION PROTOCOL] CLI CLOCK-PRIOR MISMATCH SWEEP",
        horizon,
        &rows_a,
    );

    // Sweep B: SlidingMinRtt variance floor across link types.
    let mut rows_b = Vec::new();
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
        rows_b.push(TableRow::new(label, move || {
            two_speaker_config(
                SyncMode::Peer,
                true,
                link,
                0.0,
                0.0,
                LinkModel::WIRED_CALM,
                cq,
                cq,
                def_prior,
                def_prior,
                WEIGHT_UNITY_Q16,
                floor_ns2,
                lipsync,
                level_ns,
                window,
                LIPSYNC_WEIGHTS,
                true,
            )
        }));
    }
    run_table(
        "SECTION 3B: [PRODUCTION PROTOCOL] VARIANCE-FLOOR SWEEP",
        horizon,
        &rows_b,
    );

    // Sweep C: Modal gains (g_com, g_diff) trade-off including `g_com = 0`.
    let gain_cases = [
        ("g_com=0.00/s, g_diff=4.0/s (unanchored)", 0u32, 4 << 16),
        ("g_com=0.05/s, g_diff=4.0/s (low-lat)", 3_277u32, 4 << 16),
        ("g_com=0.50/s, g_diff=4.0/s (lipsync)", 32_768, 4 << 16),
        ("g_com=2.00/s, g_diff=4.0/s", 2 << 16, 4 << 16),
        ("g_com=0.50/s, g_diff=8.0/s", 32_768, 8 << 16),
    ];
    let mut rows_c = Vec::new();
    for &(label, g_com, g_diff) in &gain_cases {
        let modal = Some(ModalRegulation {
            star_gain: 4 << 16,
            common_gain: g_com,
            diff_gain: g_diff,
            limit: 1_000_000,
            jump: 240,
        });
        rows_c.push(TableRow::new(label, move || {
            two_speaker_config(
                SyncMode::Peer,
                true,
                LinkModel::WIRELESS,
                0.0,
                0.0,
                LinkModel::WIRED_CALM,
                FrequencyNoise::WANDERING_QUARTZ,
                cq,
                def_prior,
                def_prior,
                WEIGHT_UNITY_Q16,
                25_000_000,
                modal,
                90_000_000,
                window,
                LIPSYNC_WEIGHTS,
                true,
            )
        }));
    }
    run_table(
        "SECTION 3C: [PRODUCTION PROTOCOL] MODAL-GAIN SWEEP (WI-FI SRC -> 2 WIRED PEERS)",
        horizon,
        &rows_c,
    );

    // Sweep D: Unknown static asymmetry on BOTH sender links AND peer links
    // (showing where `--link-weight` helps and where it severely degrades).
    let mut rows_d = Vec::new();
    for &asym_us in &[0.0_f64, 200.0, 1_000.0, 2_000.0] {
        let asym_s = asym_us * 1e-6;
        for &(tag, peers, sender_w) in &[
            ("Star", false, WEIGHT_UNITY_Q16),
            ("Peer (w_src=1.00)", true, WEIGHT_UNITY_Q16),
            ("Peer (w_src=0.05)", true, 3_277),
        ] {
            rows_d.push(TableRow::new(
                format!("Src asym {asym_us:4.0} us: {tag}"),
                move || {
                    two_speaker_config(
                        SyncMode::Peer,
                        peers,
                        LinkModel::WIRED_CALM,
                        asym_s,
                        0.0,
                        LinkModel::WIRED_CALM,
                        cq,
                        cq,
                        def_prior,
                        def_prior,
                        sender_w,
                        25_000_000,
                        lipsync,
                        30_000_000,
                        window,
                        LIPSYNC_WEIGHTS,
                        true,
                    )
                },
            ));
        }
    }
    for &asym_us in &[200.0_f64, 1_000.0] {
        let asym_s = asym_us * 1e-6;
        for &(tag, peers, sender_w) in &[
            ("Star", false, WEIGHT_UNITY_Q16),
            ("Peer (w_src=1.00)", true, WEIGHT_UNITY_Q16),
            ("Peer (w_src=0.05)", true, 3_277),
        ] {
            rows_d.push(TableRow::new(
                format!("Peer asym {asym_us:4.0} us: {tag}"),
                move || {
                    two_speaker_config(
                        SyncMode::Peer,
                        peers,
                        LinkModel::WIRED_CALM,
                        0.0,
                        asym_s,
                        LinkModel::WIRED_CALM,
                        cq,
                        cq,
                        def_prior,
                        def_prior,
                        sender_w,
                        25_000_000,
                        lipsync,
                        30_000_000,
                        window,
                        LIPSYNC_WEIGHTS,
                        true,
                    )
                },
            ));
        }
    }
    run_table(
        "SECTION 3D: [PRODUCTION PROTOCOL] STATIC ASYMMETRY & --link-weight (SENDER vs PEER LINK)",
        horizon,
        &rows_d,
    );
}

fn main() {
    let smoke = env::args().any(|arg| arg == "--smoke");
    let horizon = RunHorizon::for_mode(smoke);
    println!(
        "Unisono faithful production simulation suite (mode={}, seeds={}, window=[{:.0}s, {:.0}s) of {:.1}s)",
        if smoke { "smoke" } else { "full" },
        horizon.seeds.len(),
        horizon.window.0,
        horizon.window.1,
        horizon.duration_s,
    );
    print_parameter_summary(horizon);
    print_oracle_benchmarks(smoke);
    print_topology_comparisons(horizon);
    print_sensitivity_sweeps(horizon);
}
