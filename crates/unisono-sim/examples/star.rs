// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Prints the simulation tables for `docs/star-optimum.tex`:
//!
//! 1. Shared-gain star Lyapunov analysis: perfect-information benchmark (exact
//!    offsets known every 10 ms, corrected negative cross-covariance in
//!    `cycle_clock_innovation_cov`) and coupled Kalman-filter-in-the-loop
//!    Lyapunov solver showing noisy measurements push the optimal shared star
//!    gain *below* `gain_for_weight(c_track)`.
//! 2. Star topology (20-seed medians and IQR): baselines (1000 ppm, 100 ppm,
//!    and min-RTT + 100 ppm) vs. star controllers (fixed nominal offline
//!    variance and online adaptive variance with fixed conservative floor),
//!    using only causally observed `min_rtt / 2` for playback deadlines, plus
//!    a tight-margin (`2 ms`) Wi-Fi comparison and a prior-mismatch sweep
//!    (`0.01x` to `10x`).
//! 3. Causal sender-disciplined timestamped schedule (20-seed medians and IQR)
//!    with strictly local step-0 initialization (no cross-receiver average),
//!    delayed/lossy uplinks, and delayed downlink broadcasts.
//! 4. Star vs. Peer Graph-Laplacian BLUE + modal control (20-seed medians and
//!    IQR) showing Star (including tuned Star `g = 0.03` on wandering `K_5`),
//!    **centralized** peer benchmarks, and **decentralized** receiver-local
//!    peer controllers (1-step delay, 2% relay loss).
//! 5. Playout margin under exponential pauses with discontinuity pricing
//!    (pooled across all 20 seeds).
//!
//! Run with `cargo run --release -p unisono-sim --example star`.

use unisono_sim::link::LinkModel;
use unisono_sim::star::{
    FilteredStarLyapunov, FrequencyNoise, GraphEdge, HeterogeneousKinds, Outcome, PauseSimConfig,
    PeerComparisonConfig, ReceiverSetting, ScheduleMetrics, StarComparison, campbell_fraction,
    click_rate, compare_star, cycle_clock_innovation_cov, decentralized_star_weight,
    disciplined_schedule_comparison, filtered_star_lyapunov_cost, gain_for_weight,
    hold_margin_with_clicks, optimal_filtered_star_gain, optimal_shared_star_gain,
    peer_topology_comparison, pure_pause_block_metrics, quantiles, star_lyapunov_cost,
    stream_block_pause_metrics,
};

const SEEDS: [u64; 20] = [
    101, 202, 303, 404, 505, 606, 707, 808, 909, 1010, 1111, 1212, 1313, 1414, 1515, 1616, 1717,
    1818, 1919, 2020,
];

/// Switched wired Ethernet link.
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

/// Consumer Wi-Fi link with 50% contention and 30 ms stalls every 20 s.
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

/// Fixed nominal offline measurement variance for wired links `(10 us)^2`
/// (never peeks at the simulator's true `timestamp_std`).
const NOMINAL_WIRED_VAR: f64 = 1e-10;

/// Fixed nominal offline measurement variance for Wi-Fi links `(170 us)^2`.
const NOMINAL_WIRELESS_VAR: f64 = 2.89e-8;

fn with_min(base: LinkModel, minimum: f64) -> LinkModel {
    LinkModel { minimum, ..base }
}

fn wired_rx(
    clock: FrequencyNoise,
    timestamp_std: f64,
    asym: f64,
    filter_override: Option<FrequencyNoise>,
) -> ReceiverSetting {
    ReceiverSetting {
        forward: with_min(WIRED, (WIRED.minimum + asym).max(10e-6)),
        backward: with_min(WIRED, (WIRED.minimum - asym).max(10e-6)),
        drop_rate: 0.0,
        timestamp_std,
        clock,
        filter_noise_override: filter_override,
        calibrated_variance: NOMINAL_WIRED_VAR,
    }
}

fn wireless_rx(
    clock: FrequencyNoise,
    asym: f64,
    filter_override: Option<FrequencyNoise>,
) -> ReceiverSetting {
    ReceiverSetting {
        forward: with_min(WIRELESS, (WIRELESS.minimum + asym).max(100e-6)),
        backward: with_min(WIRELESS, (WIRELESS.minimum - asym).max(100e-6)),
        drop_rate: 0.02,
        timestamp_std: 10e-6,
        clock,
        filter_noise_override: filter_override,
        calibrated_variance: NOMINAL_WIRELESS_VAR,
    }
}

fn star_scenario(
    sender: FrequencyNoise,
    receivers: Vec<ReceiverSetting>,
    playout_margin: f64,
    smoke: bool,
) -> StarComparison {
    // Shared star gain from uncorrelated formula at `(c_sync = 2e-6, c_track = 4e-7)`:
    // yields `g = 0.04748` for `R = 2` and `g = 0.05180` for `R = 5`.
    let r = receivers.len().max(1);
    let gain = gain_for_weight(decentralized_star_weight(r, 2.0e-6, 4.0e-7));
    StarComparison {
        cycle: 0.01,
        lookahead: 16.0 / 48_000.0,
        period: 0.25,
        window: 8,
        stride: 4,
        duration: if smoke { 40.0 } else { 600.0 },
        warmup: if smoke { 10.0 } else { 60.0 },
        playout_margin,
        online_variance_floor: (5e-6_f64).powi(2),
        gain,
        sender,
        receivers,
    }
}

fn fmt_q(vals: &[f64], scale: f64) -> String {
    let (med, p25, p75) = quantiles(vals);
    format!(
        "{:>6.2} [{:>5.2},{:>5.2}]",
        med * scale,
        p25 * scale,
        p75 * scale
    )
}

fn print_lyapunov_star_gain_table() {
    println!(
        "=== 1A. Perfect-Info Shared Star Gain Benchmark (R = 4, dt = 10 ms, exact offsets) ==="
    );
    let receivers = 4;
    let c_sync = 1.0e-5;
    let c_track = 1.0e-7;
    let dt = 0.01;
    let g_indep = gain_for_weight(decentralized_star_weight(receivers, c_sync, c_track));
    let g_track = gain_for_weight(c_track);
    let g_diff = gain_for_weight(c_sync + c_track);
    println!(
        "Benchmarks: g(c_track) = {g_track:.5}, g(((R-1)/R)c_S + c_track) = {g_indep:.5}, g(c_S + c_track) = {g_diff:.5}"
    );
    println!(
        "{:<22} | {:>10} | {:>12} | {:>12} | {:>9}",
        "sender wander scale", "g_star*", "J(g_star*)", "J(g_indep)", "reduction"
    );
    let sigma_rx = cycle_clock_innovation_cov(FrequencyNoise::CONSUMER_QUARTZ, dt);
    for (label, scale) in [
        ("0x (ideal sender)", 0.0_f64),
        ("1x consumer quartz", 1.0),
        ("10x h_{-2}", 10.0),
        ("100x h_{-2}", 100.0),
        ("1000x h_{-2}", 1000.0),
    ] {
        let sender_noise = FrequencyNoise {
            h0_white: FrequencyNoise::CONSUMER_QUARTZ.h0_white * scale.min(1.0),
            h1_flicker: 0.0,
            h2_walk: FrequencyNoise::CONSUMER_QUARTZ.h2_walk * scale,
        };
        let sigma_s = cycle_clock_innovation_cov(sender_noise, dt);
        let g_opt = optimal_shared_star_gain(receivers, c_sync, c_track, sigma_s, sigma_rx);
        let j_opt = star_lyapunov_cost(receivers, c_sync, c_track, sigma_s, sigma_rx, g_opt);
        let j_ind = star_lyapunov_cost(receivers, c_sync, c_track, sigma_s, sigma_rx, g_indep);
        let pct = if j_ind > 0.0 {
            100.0 * (1.0 - j_opt / j_ind)
        } else {
            0.0
        };
        println!("{label:<22} | {g_opt:>10.5} | {j_opt:>12.4e} | {j_ind:>12.4e} | {pct:>8.2}%");
    }
    println!();

    println!(
        "=== 1B. Filter-in-the-Loop Shared Star Gain (R = 4, 100x sender h_{{-2}}, dt = 10 ms) ==="
    );
    println!(
        "{:<28} | {:>10} | {:>11} | {:>16}",
        "measurement cadence & noise", "g_filt*", "vs g_indep", "extra at g(c_tr)"
    );
    let sender_100 = FrequencyNoise {
        h0_white: FrequencyNoise::CONSUMER_QUARTZ.h0_white,
        h1_flicker: 0.0,
        h2_walk: FrequencyNoise::CONSUMER_QUARTZ.h2_walk * 100.0,
    };
    for (label, stride, meas_std) in [
        ("every 10 ms, 1 us noise", 1_usize, 1e-6_f64),
        ("every 1 s, 2.8 us (wired)", 100, 2.8e-6),
        ("every 1 s, 170 us (Wi-Fi)", 100, 170e-6),
    ] {
        let cfg = FilteredStarLyapunov {
            receivers,
            c_sync,
            c_track,
            sender_noise: sender_100,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            meas_var: meas_std * meas_std,
            cycle: dt,
            meas_stride: stride,
        };
        let g_opt = optimal_filtered_star_gain(cfg);
        let j_opt = filtered_star_lyapunov_cost(cfg, g_opt);
        let j_ind = filtered_star_lyapunov_cost(cfg, g_indep);
        let j_tr = filtered_star_lyapunov_cost(cfg, g_track);
        let saving = 100.0 * (1.0 - j_opt / j_ind);
        let extra_in_old_range = 100.0 * (j_tr / j_opt - 1.0);
        println!("{label:<28} | {g_opt:>10.5} | {saving:>10.2}% | +{extra_in_old_range:>14.2}%");
    }
    println!();
}

fn summarize_outcomes(label: &str, items: &[Outcome]) {
    let spreads: Vec<f64> = items.iter().map(|o| o.spread).collect();
    let errors: Vec<f64> = items.iter().map(|o| o.error).collect();
    let rms_sc: Vec<f64> = items.iter().map(|o| o.speed_change).collect();
    let max_sc: Vec<f64> = items.iter().map(|o| o.largest_speed_change).collect();
    let missed: Vec<f64> = items.iter().map(|o| o.missed_fraction).collect();
    let clicks: Vec<f64> = items.iter().map(|o| o.discontinuity_rate).collect();
    let (m_med, _, _) = quantiles(&missed);
    let (c_med, _, _) = quantiles(&clicks);
    println!(
        "{label:<50} | {} | {} | {} | {:>7.2} | {:>7.2e} / {:>5.2}",
        fmt_q(&spreads, 1e6),
        fmt_q(&errors, 1e6),
        fmt_q(&rms_sc, 1e6),
        quantiles(&max_sc).0 * 1e6,
        m_med,
        c_med,
    );
}

fn star_cases() -> Vec<(&'static str, FrequencyNoise, Vec<ReceiverSetting>, f64)> {
    let under_prior = Some(FrequencyNoise::TCXO.combine(FrequencyNoise::TCXO));
    vec![
        (
            "2 wired (TCXO, hw ts 2us)",
            FrequencyNoise::TCXO,
            vec![
                wired_rx(FrequencyNoise::TCXO, 2e-6, 0.0, None),
                wired_rx(FrequencyNoise::TCXO, 2e-6, 0.0, None),
            ],
            0.05,
        ),
        (
            "2 wired (quartz, sw ts 10us)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, None),
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, None),
            ],
            0.05,
        ),
        (
            "2 wired asym +-50us (quartz)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 50e-6, None),
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, -50e-6, None),
            ],
            0.05,
        ),
        (
            "2 wireless (quartz, 2% drop, 50ms)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, None),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, None),
            ],
            0.05,
        ),
        (
            "2 wireless (quartz, 2% drop, 2ms)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, None),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, None),
            ],
            0.002,
        ),
        (
            "2 wireless asym +-200us (2% drop)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 200e-6, None),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, -200e-6, None),
            ],
            0.05,
        ),
        (
            "2 wireless asym +-500us (2% drop)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 500e-6, None),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, -500e-6, None),
            ],
            0.05,
        ),
        (
            "3 wired + 2 wireless (quartz)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, None),
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, None),
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, None),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, None),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, None),
            ],
            0.05,
        ),
        (
            "2 wireless flicker (TCXO prior)",
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            vec![
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ_FLICKER, 0.0, under_prior),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ_FLICKER, 0.0, under_prior),
            ],
            0.05,
        ),
    ]
}

fn print_star_table(seeds: &[u64], smoke: bool) {
    println!(
        "=== 2A. Star Topology ({}-seed medians [p25, p75]): Baselines vs. Star Controllers ===",
        seeds.len()
    );
    println!(
        "Note: star rows use the true oscillator (h_0, h_{{-2}}) prior unless noted; \
         deadlines use causally observed min_rtt / 2; calib uses fixed nominal (10us)^2 / (170us)^2."
    );
    println!(
        "{:<50} | {:>19} | {:>19} | {:>19} | {:>7} | {:>15}",
        "scenario [policy]",
        "spread us [IQR]",
        "error us [IQR]",
        "rms ppm [IQR]",
        "max ppm",
        "missed / clk/s"
    );
    for (name, sender, rxs, margin) in star_cases() {
        let scenario = star_scenario(sender, rxs, margin, smoke);
        let mut b1000 = Vec::with_capacity(seeds.len());
        let mut b100 = Vec::with_capacity(seeds.len());
        let mut bmin = Vec::with_capacity(seeds.len());
        let mut cal = Vec::with_capacity(seeds.len());
        let mut onl = Vec::with_capacity(seeds.len());
        for &seed in seeds {
            let res = compare_star(&scenario, seed);
            b1000.push(res.baseline_1000ppm);
            b100.push(res.baseline_100ppm);
            bmin.push(res.baseline_min_rtt_100ppm);
            cal.push(res.star_calibrated);
            onl.push(res.star_online);
        }
        summarize_outcomes(&format!("{name} [base 1000ppm]"), &b1000);
        summarize_outcomes(&format!("{name} [base  100ppm]"), &b100);
        summarize_outcomes(&format!("{name} [minRTT 100  ]"), &bmin);
        summarize_outcomes(&format!("{name} [star nom var]"), &cal);
        summarize_outcomes(&format!("{name} [star online ]"), &onl);
        println!();
    }
}

fn print_prior_mismatch_table(seeds: &[u64], smoke: bool) {
    println!(
        "=== 2B. Oscillator Prior-Mismatch Sensitivity ({}-seed medians [IQR], star online) ===",
        seeds.len()
    );
    println!(
        "{:<34} | {:>19} | {:>19} | {:>19}",
        "link & prior scale vs true", "spread us [IQR]", "error us [IQR]", "rms ppm [IQR]"
    );
    let q_comb = FrequencyNoise::CONSUMER_QUARTZ.combine(FrequencyNoise::CONSUMER_QUARTZ);
    for (link_name, is_wifi) in [("2 wired (quartz)", false), ("2 wireless (quartz)", true)] {
        let base_rxs = if is_wifi {
            vec![
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, None),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, None),
            ]
        } else {
            vec![
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, None),
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, None),
            ]
        };
        let base_sc = star_scenario(FrequencyNoise::CONSUMER_QUARTZ, base_rxs, 0.05, smoke);
        let mut bmin_sp = Vec::with_capacity(seeds.len());
        let mut bmin_er = Vec::with_capacity(seeds.len());
        let mut bmin_rg = Vec::with_capacity(seeds.len());
        for &seed in seeds {
            let res = compare_star(&base_sc, seed);
            bmin_sp.push(res.baseline_min_rtt_100ppm.spread);
            bmin_er.push(res.baseline_min_rtt_100ppm.error);
            bmin_rg.push(res.baseline_min_rtt_100ppm.speed_change);
        }
        println!(
            "{:<34} | {} | {} | {}",
            format!("{link_name} [minRTT 100]"),
            fmt_q(&bmin_sp, 1e6),
            fmt_q(&bmin_er, 1e6),
            fmt_q(&bmin_rg, 1e6),
        );
        for scale in [0.01_f64, 0.1, 0.3, 1.0, 3.0, 10.0] {
            let scaled = Some(FrequencyNoise {
                h0_white: q_comb.h0_white * scale,
                h1_flicker: 0.0,
                h2_walk: q_comb.h2_walk * scale,
            });
            let rxs = if is_wifi {
                vec![
                    wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, scaled),
                    wireless_rx(FrequencyNoise::CONSUMER_QUARTZ, 0.0, scaled),
                ]
            } else {
                vec![
                    wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, scaled),
                    wired_rx(FrequencyNoise::CONSUMER_QUARTZ, 10e-6, 0.0, scaled),
                ]
            };
            let sc = star_scenario(FrequencyNoise::CONSUMER_QUARTZ, rxs, 0.05, smoke);
            let mut sp = Vec::with_capacity(seeds.len());
            let mut er = Vec::with_capacity(seeds.len());
            let mut rg = Vec::with_capacity(seeds.len());
            for &seed in seeds {
                let res = compare_star(&sc, seed);
                sp.push(res.star_online.spread);
                er.push(res.star_online.error);
                rg.push(res.star_online.speed_change);
            }
            println!(
                "{:<34} | {} | {} | {}",
                format!("{link_name} [{scale:>4.2}x prior]"),
                fmt_q(&sp, 1e6),
                fmt_q(&er, 1e6),
                fmt_q(&rg, 1e6),
            );
        }
        println!();
    }
}

fn summarize_schedule(label: &str, items: &[ScheduleMetrics]) {
    let all: Vec<f64> = items.iter().map(|m| m.spreads.all).collect();
    let wired: Vec<f64> = items.iter().map(|m| m.spreads.first_kind).collect();
    let mixed: Vec<f64> = items.iter().map(|m| m.spreads.mixed).collect();
    let err: Vec<f64> = items.iter().map(|m| m.rms_error).collect();
    let rough: Vec<f64> = items.iter().map(|m| m.rms_roughness).collect();
    println!(
        "{label:<28} | {} | {} | {} | {} | {}",
        fmt_q(&all, 1e6),
        fmt_q(&wired, 1e6),
        fmt_q(&mixed, 1e6),
        fmt_q(&err, 1e6),
        fmt_q(&rough, 1e6),
    );
}

fn print_schedule_table(seeds: &[u64], smoke: bool) {
    println!(
        "=== 3. Causal Sender-Disciplined Schedule ({}-seed medians [IQR], causal step-0, 1-step up/down, 2% drop) ===",
        seeds.len()
    );
    println!(
        "{:<28} | {:>19} | {:>19} | {:>19} | {:>19} | {:>19}",
        "sender [policy]",
        "all spread us",
        "wired spread us",
        "mixed spread us",
        "rms error us",
        "rms rough ppm"
    );
    let kinds = HeterogeneousKinds {
        first: 3,
        second: 2,
        first_error: 4e-6,
        second_error: 150e-6,
        tx_common_error: 20e-6,
        uplink_delay_steps: 1,
        downlink_delay_steps: 1,
        report_drop_rate: 0.02,
        gain: 0.15,
    };
    let steps = if smoke { 500 } else { 20_000 };
    for (name, sender, rx) in [
        (
            "consumer quartz",
            FrequencyNoise::CONSUMER_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ,
        ),
        (
            "flicker quartz",
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
            FrequencyNoise::CONSUMER_QUARTZ_FLICKER,
        ),
        (
            "100x wandering h_{-2}",
            FrequencyNoise::WANDERING_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ,
        ),
    ] {
        let mut own_v = Vec::with_capacity(seeds.len());
        let mut sched_v = Vec::with_capacity(seeds.len());
        for &seed in seeds {
            let (own, sched) = disciplined_schedule_comparison(kinds, sender, rx, 1.0, steps, seed);
            own_v.push(own);
            sched_v.push(sched);
        }
        summarize_schedule(&format!("{name} [own]"), &own_v);
        summarize_schedule(&format!("{name} [sched]"), &sched_v);
    }
    println!();
}

fn complete_mesh_edges(nodes: usize, std_dev: f64) -> Vec<GraphEdge> {
    let var = std_dev.powi(2);
    let mut edges = Vec::new();
    for src in 0..nodes {
        for dst in (src + 1)..nodes {
            edges.push(GraphEdge {
                src,
                dst,
                variance: var,
                bias: 0.0,
            });
        }
    }
    edges
}

fn summarize_peer_row(label: &str, items: &[Outcome]) {
    let sp: Vec<f64> = items.iter().map(|o| o.spread).collect();
    let er: Vec<f64> = items.iter().map(|o| o.error).collect();
    let rg: Vec<f64> = items.iter().map(|o| o.speed_change).collect();
    let max_sp = sp.iter().copied().fold(0.0_f64, f64::max);
    println!(
        "{label:<48} | {} | {} | {} | {:>8.2}",
        fmt_q(&sp, 1e6),
        fmt_q(&er, 1e6),
        fmt_q(&rg, 1e6),
        max_sp * 1e6,
    );
}

fn peer_cases(smoke: bool) -> Vec<(&'static str, PeerComparisonConfig, Option<f64>)> {
    let steps = if smoke { 400 } else { 10_000 };
    let wifi_tri = |b1: f64, b2: f64| {
        vec![
            GraphEdge {
                src: 0,
                dst: 1,
                variance: (150e-6_f64).powi(2),
                bias: b1,
            },
            GraphEdge {
                src: 0,
                dst: 2,
                variance: (150e-6_f64).powi(2),
                bias: b2,
            },
            GraphEdge {
                src: 1,
                dst: 2,
                variance: (5e-6_f64).powi(2),
                bias: 0.0,
            },
        ]
    };
    vec![
        (
            "K5 symmetric (R=4, 150us)",
            PeerComparisonConfig {
                receivers: 4,
                peer_edges: complete_mesh_edges(5, 150e-6),
                sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
                receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
                interval: 0.5,
                steps,
                star_gain: 0.15,
                g_com: 0.05,
                g_com_low: 0.005,
                g_diff: 0.15,
                relay_delay_steps: 1,
                relay_drop_rate: 0.02,
            },
            None,
        ),
        (
            "Wi-Fi + wired opp (+-750us, R=2)",
            PeerComparisonConfig {
                receivers: 2,
                peer_edges: wifi_tri(750e-6, -750e-6),
                sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
                receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
                interval: 0.5,
                steps,
                star_gain: 0.15,
                g_com: 0.05,
                g_com_low: 0.005,
                g_diff: 0.15,
                relay_delay_steps: 1,
                relay_drop_rate: 0.02,
            },
            None,
        ),
        (
            "Wi-Fi + wired same (+750/+750us)",
            PeerComparisonConfig {
                receivers: 2,
                peer_edges: wifi_tri(750e-6, 750e-6),
                sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
                receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
                interval: 0.5,
                steps,
                star_gain: 0.15,
                g_com: 0.05,
                g_com_low: 0.005,
                g_diff: 0.15,
                relay_delay_steps: 1,
                relay_drop_rate: 0.02,
            },
            None,
        ),
        (
            "K5 wandering sender (R=4, 50us)",
            PeerComparisonConfig {
                receivers: 4,
                peer_edges: complete_mesh_edges(5, 50e-6),
                sender_noise: FrequencyNoise::WANDERING_QUARTZ,
                receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
                interval: 0.5,
                steps,
                star_gain: 0.15,
                g_com: 0.10,
                g_com_low: 0.005,
                g_diff: 0.15,
                relay_delay_steps: 1,
                relay_drop_rate: 0.02,
            },
            Some(0.03),
        ),
    ]
}

fn print_peer_table(seeds: &[u64], smoke: bool) {
    println!(
        "=== 4. Star vs. Peer Graph-Laplacian BLUE ({}-seed medians [IQR], dec = 1-step / 2% loss relay) ===",
        seeds.len()
    );
    println!(
        "{:<48} | {:>19} | {:>19} | {:>19} | {:>8}",
        "topology [policy]",
        "spread us [IQR]",
        "rms error us [IQR]",
        "rms rough ppm [IQR]",
        "worst sp"
    );

    for (name, cfg, tuned_star_gain) in peer_cases(smoke) {
        let mut star_v = Vec::with_capacity(seeds.len());
        let mut star_tuned_v = Vec::with_capacity(seeds.len());
        let mut cent_lip = Vec::with_capacity(seeds.len());
        let mut cent_low = Vec::with_capacity(seeds.len());
        let mut cent_unb = Vec::with_capacity(seeds.len());
        let mut dec_lip = Vec::with_capacity(seeds.len());
        let mut dec_low = Vec::with_capacity(seeds.len());
        let mut dec_unb = Vec::with_capacity(seeds.len());
        let mut star_th = 0.0;
        let mut peer_th = 0.0;
        let mut bias_th = 0.0;
        for &seed in seeds {
            let res = peer_topology_comparison(&cfg, seed);
            star_th = res.star_pair_std_theory;
            peer_th = res.peer_pair_std_theory;
            bias_th = res.peer_pair_bias_theory;
            star_v.push(res.star);
            cent_lip.push(res.centralized_lipsync);
            cent_low.push(res.centralized_lowlatency);
            cent_unb.push(res.centralized_unbounded_consensus);
            dec_lip.push(res.decentralized_lipsync);
            dec_low.push(res.decentralized_lowlatency);
            dec_unb.push(res.decentralized_unbounded_consensus);
            if let Some(g_tuned) = tuned_star_gain {
                let mut tuned_cfg = cfg.clone();
                tuned_cfg.star_gain = g_tuned;
                star_tuned_v.push(peer_topology_comparison(&tuned_cfg, seed).star);
            }
        }
        println!(
            "  [{name}: theory pair std {:.1} -> {:.1} us, BLUE pair bias {:.2} us]",
            star_th * 1e6,
            peer_th * 1e6,
            bias_th * 1e6,
        );
        summarize_peer_row(&format!("{name} [star g=0.15]"), &star_v);
        if let Some(g_tuned) = tuned_star_gain {
            summarize_peer_row(&format!("{name} [star g={g_tuned:.2}]"), &star_tuned_v);
        }
        summarize_peer_row(&format!("{name} [cent lip  ]"), &cent_lip);
        summarize_peer_row(&format!("{name} [dec  lip  ]"), &dec_lip);
        summarize_peer_row(&format!("{name} [cent low  ]"), &cent_low);
        summarize_peer_row(&format!("{name} [dec  low  ]"), &dec_low);
        summarize_peer_row(&format!("{name} [cent g0   ]"), &cent_unb);
        summarize_peer_row(&format!("{name} [dec  g0   ]"), &dec_unb);
        println!();
    }
}

fn print_margin_table(seeds: &[u64], smoke: bool) {
    println!(
        "=== 5. Playout Margin under Exponential Pauses (pooled {}-seed, true (lambda, d_bar), 10 ms blocks) ===",
        seeds.len()
    );
    println!(
        "{:>10} | {:>10} | {:>11} | {:>21} | {:>21} | {:>6} | {:>8} | {:>19}",
        "w_lat/w_M",
        "w_D/w_M(s)",
        "margin (ms)",
        "missed: theory / sim",
        "clicks/s: thry / sim",
        "c_rat",
        "events",
        "full-link (pooled)"
    );
    let lookahead = 16.0 / 48_000.0;
    #[allow(clippy::cast_precision_loss)]
    let seed_count = seeds.len() as f64;
    let pure_per_seed = if smoke { 50_000.0 } else { 25_000_000.0 };
    let link_per_seed = if smoke { 2_000.0 } else { 10_000.0 };
    for (w_lat, w_click) in [
        (1e-2, 0.0),
        (1e-3, 0.0),
        (1e-3, 0.05),
        (1e-3, 0.25),
        (1e-4, 0.0),
        (1e-4, 0.25),
    ] {
        let margin = hold_margin_with_clicks(
            WIRELESS.pause_rate,
            WIRELESS.pause_length,
            w_lat,
            1.0,
            w_click,
        )
        .unwrap_or(0.0);
        let th_missed = campbell_fraction(WIRELESS.pause_rate, WIRELESS.pause_length, margin);
        let th_clicks = click_rate(WIRELESS.pause_rate, WIRELESS.pause_length, margin);
        let mut pure_missed_sum = 0.0;
        let mut pure_clicks_sum = 0.0;
        let mut total_events = 0_usize;
        let mut link_missed_sum = 0.0;
        let mut link_clicks_sum = 0.0;
        for &seed in seeds {
            let (sm, sc, ev) = pure_pause_block_metrics(
                WIRELESS.pause_rate,
                WIRELESS.pause_length,
                0.01,
                lookahead,
                pure_per_seed,
                margin,
                seed,
            );
            pure_missed_sum += sm;
            pure_clicks_sum += sc;
            total_events += ev;
            let (lm, lc, _) = stream_block_pause_metrics(
                WIRELESS,
                0.0,
                margin,
                PauseSimConfig {
                    cycle: 0.01,
                    lookahead,
                    duration: link_per_seed,
                    warmup: 100.0,
                },
                seed,
            );
            link_missed_sum += lm;
            link_clicks_sum += lc;
        }
        let sim_missed = pure_missed_sum / seed_count;
        let sim_clicks = pure_clicks_sum / seed_count;
        let link_missed = link_missed_sum / seed_count;
        let link_clicks = link_clicks_sum / seed_count;
        let click_ratio = if th_clicks > 0.0 {
            sim_clicks / th_clicks
        } else {
            0.0
        };
        println!(
            "{w_lat:>10.0e} | {w_click:>10.2} | {:>11.1} | {:>9.2e} / {:>9.2e} | {:>9.2e} / {:>9.2e} | {:>6.3} | {:>8} | {:>8.2e}/{:>8.2e}",
            margin * 1e3,
            th_missed,
            sim_missed,
            th_clicks,
            sim_clicks,
            click_ratio,
            total_events,
            link_missed,
            link_clicks,
        );
    }
}

fn main() {
    let smoke = std::env::args().any(|a| a == "--smoke");
    let seeds: &[u64] = if smoke { &SEEDS[..1] } else { &SEEDS };
    print_lyapunov_star_gain_table();
    print_star_table(seeds, smoke);
    print_prior_mismatch_table(seeds, smoke);
    print_schedule_table(seeds, smoke);
    print_peer_table(seeds, smoke);
    print_margin_table(seeds, smoke);
}
