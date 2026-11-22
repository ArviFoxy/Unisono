// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Verification tests for the star and peer synchronization simulations in
//! `unisono_sim::star` against the analytical results of
//! `Unisono.Solutions.Optimal`.

use unisono_sim::link::LinkModel;
use unisono_sim::star::{
    FrequencyNoise, GraphEdge, HeterogeneousKinds, OffsetFilter, PeerComparisonConfig,
    ReceiverSetting, StarComparison, campbell_fraction, click_rate, compare_star,
    decentralized_star_weight, disciplined_schedule_comparison, effective_resistance,
    gain_for_weight, hold_margin_with_clicks, peer_topology_comparison, solve_graph_blue,
    stream_pause_metrics,
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

/// Both oracle and online-adaptive star-optimal controllers beat the
/// fixed-delay baseline (at both 1000 ppm and fair 100 ppm slew) on spread,
/// error, and roughness, even with consumer quartz oscillators and UDP packet
/// loss.
#[test]
fn star_optimal_beats_baselines_under_quartz_and_drops() {
    let wired = ReceiverSetting {
        forward: WIRED,
        backward: WIRED,
        drop_rate: 0.0,
        timestamp_std: 2e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        oracle_variance: (4e-6_f64).powi(2),
    };
    let wireless = ReceiverSetting {
        forward: WIRELESS,
        backward: WIRELESS,
        drop_rate: 0.02,
        timestamp_std: 5e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        oracle_variance: (150e-6_f64).powi(2),
    };
    let setting = StarComparison {
        cycle: 0.01,
        period: 0.25,
        window: 8,
        stride: 4,
        duration: 600.0,
        warmup: 120.0,
        playout_margin: 0.05,
        gain: 0.05,
        sender: FrequencyNoise::CONSUMER_QUARTZ,
        receivers: vec![wired, wired, wireless],
    };
    let res = compare_star(&setting, 7);
    assert!(
        res.star_oracle.spread * 3.0 < res.baseline_1000ppm.spread,
        "oracle {:?} vs base1000 {:?}",
        res.star_oracle,
        res.baseline_1000ppm
    );
    assert!(
        res.star_online.spread * 3.0 < res.baseline_1000ppm.spread,
        "online {:?} vs base1000 {:?}",
        res.star_online,
        res.baseline_1000ppm
    );
    assert!(
        res.star_online.spread * 2.0 < res.baseline_100ppm.spread,
        "online {:?} vs base100 {:?}",
        res.star_online,
        res.baseline_100ppm
    );
    assert!(
        res.star_oracle.largest_speed_change * 10.0 < res.baseline_100ppm.largest_speed_change,
        "oracle {:?} vs base100 {:?}",
        res.star_oracle,
        res.baseline_100ppm
    );
}

/// With a sender-disciplined timestamped schedule (even with non-zero initial
/// offsets, delivery delay, and shared sender-NIC jitter), a 100x wandering
/// sender oscillator leaves fleet synchronization tight, whereas independent
/// heterogeneous star filters leak sender clock wander into inter-speaker spread.
#[test]
fn disciplined_schedule_suppresses_wandering_sender_leakage() {
    let kinds = HeterogeneousKinds {
        first: 3,
        second: 2,
        first_error: 4e-6,
        second_error: 150e-6,
        tx_common_error: 20e-6,
        schedule_delay_steps: 1,
    };
    let (own_q, sched_q) = disciplined_schedule_comparison(
        kinds,
        FrequencyNoise::CONSUMER_QUARTZ,
        FrequencyNoise::CONSUMER_QUARTZ,
        1.0,
        20_000,
        11,
    );
    let (own_w, sched_w) = disciplined_schedule_comparison(
        kinds,
        FrequencyNoise::WANDERING_QUARTZ,
        FrequencyNoise::CONSUMER_QUARTZ,
        1.0,
        20_000,
        11,
    );
    assert!(
        own_w.all > 1.3 * own_q.all,
        "expected wandering sender to widen independent spread: own_w={own_w:?}, own_q={own_q:?}"
    );
    assert!(
        sched_w.all < own_w.all * 0.65,
        "expected disciplined schedule to beat independent filters on wandering sender: sched_w={sched_w:?}, own_w={own_w:?}"
    );
    assert!(
        (sched_w.all - sched_q.all).abs() < 0.05 * sched_q.all,
        "expected disciplined schedule spread to stay invariant to sender wander: sched_w={sched_w:?}, sched_q={sched_q:?}"
    );
}

/// Graph-Laplacian BLUE effective resistance matches exact Thomson's principle
/// formulas from `Unisono.Solutions.Optimal.Estimation`:
/// - Star: `v1 + v2`
/// - Complete graph $K_{R+1}$: `2 v / (R + 1)`
/// - Wi-Fi sender + wired peer triangle: `2 vW vP / (2 vW + vP)`
#[test]
fn graph_laplacian_matches_thomson_formulas() {
    let v = 1e-8;
    // Star on 5 nodes: R_eff(1, 2) = 2 v.
    let star_edges: Vec<GraphEdge> = (1..5)
        .map(|u| GraphEdge {
            src: 0,
            dst: u,
            variance: v,
            bias: 0.0,
        })
        .collect();
    let r_star = effective_resistance(5, &star_edges, 1, 2);
    assert!((r_star - 2.0 * v).abs() < 1e-18 * v.max(1.0));

    // Complete graph K_5: R_eff(1, 2) = 2 v / 5.
    let mut k5_edges = Vec::new();
    for u in 0..5 {
        for w in (u + 1)..5 {
            k5_edges.push(GraphEdge {
                src: u,
                dst: w,
                variance: v,
                bias: 0.0,
            });
        }
    }
    let r_k5 = effective_resistance(5, &k5_edges, 1, 2);
    assert!((r_k5 - 2.0 * v / 5.0).abs() < 1e-18);

    // Wi-Fi sender + wired peer triangle: R_eff(1, 2) = 2 vW vP / (2 vW + vP).
    let vw = (150e-6_f64).powi(2);
    let vp = (5e-6_f64).powi(2);
    let tri = vec![
        GraphEdge {
            src: 0,
            dst: 1,
            variance: vw,
            bias: 0.0,
        },
        GraphEdge {
            src: 0,
            dst: 2,
            variance: vw,
            bias: 0.0,
        },
        GraphEdge {
            src: 1,
            dst: 2,
            variance: vp,
            bias: 0.0,
        },
    ];
    let r_tri = effective_resistance(3, &tri, 1, 2);
    let expected_tri = (2.0 * vw * vp) / (2.0 * vw + vp);
    assert!((r_tri - expected_tri).abs() < 1e-20);

    // Noiseless exact recovery check for `solve_graph_blue`.
    let truth = [0.0, 0.123, -0.456];
    let obs: Vec<f64> = tri.iter().map(|e| truth[e.dst] - truth[e.src]).collect();
    let est = solve_graph_blue(3, &tri, &obs);
    for (e, t) in est.iter().zip(truth) {
        assert!((e - t).abs() < 1e-12);
    }
}

/// On an asymmetric Wi-Fi sender + symmetric wired peer topology, Star is
/// trapped at the 750 us asymmetry spread floor while Peer Graph-Laplacian BLUE
/// eliminates the asymmetry bias and drops spread by more than 50x.
#[test]
fn peer_beats_star_on_asymmetric_wifi_sender_and_pure_consensus_cuts_roughness() {
    let wifi_wired = peer_topology_comparison(
        &PeerComparisonConfig {
            receivers: 2,
            peer_edges: vec![
                GraphEdge {
                    src: 0,
                    dst: 1,
                    variance: (150e-6_f64).powi(2),
                    bias: 750e-6,
                },
                GraphEdge {
                    src: 0,
                    dst: 2,
                    variance: (150e-6_f64).powi(2),
                    bias: -750e-6,
                },
                GraphEdge {
                    src: 1,
                    dst: 2,
                    variance: (5e-6_f64).powi(2),
                    bias: 0.0,
                },
            ],
            sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            interval: 0.5,
            steps: 10_000,
            g_com: 0.05,
            g_diff: 0.15,
        },
        23,
    );
    // Star cannot escape the 750 us half-difference asymmetry floor.
    assert!(
        wifi_wired.star.spread > 700e-6,
        "star spread unexpectedly small: {:?}",
        wifi_wired.star
    );
    // Peer BLUE collapses inter-speaker spread below 15 us.
    assert!(
        wifi_wired.peer_lipsync.spread < 15e-6,
        "peer spread too large: {:?}",
        wifi_wired.peer_lipsync
    );
    assert!(
        wifi_wired.peer_lowlatency.spread < 15e-6,
        "peer low-latency spread too large: {:?}",
        wifi_wired.peer_lowlatency
    );

    // Pure consensus (`g_com = 0`) ignores wandering sender clock in common mode,
    // strictly lowering roughness vs lip-sync mode while keeping identical sync.
    let mut k5 = Vec::new();
    for u in 0..5 {
        for v in (u + 1)..5 {
            k5.push(GraphEdge {
                src: u,
                dst: v,
                variance: (50e-6_f64).powi(2),
                bias: 0.0,
            });
        }
    }
    let wander = peer_topology_comparison(
        &PeerComparisonConfig {
            receivers: 4,
            peer_edges: k5,
            sender_noise: FrequencyNoise::WANDERING_QUARTZ,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            interval: 0.5,
            steps: 10_000,
            g_com: 0.10,
            g_diff: 0.15,
        },
        29,
    );
    assert!(
        wander.peer_lowlatency.speed_change < wander.peer_lipsync.speed_change * 0.6,
        "pure consensus should cut roughness under wandering sender: low={:?} lip={:?}",
        wander.peer_lowlatency,
        wander.peer_lipsync
    );
    assert!(
        (wander.peer_lowlatency.spread - wander.peer_lipsync.spread).abs() < 1e-9,
        "differential sync must be identical across lip-sync and pure-consensus modes"
    );
}

/// Both missed fraction (Campbell's formula) and discontinuity/click rate match
/// simulation on exponential pauses, and pricing clicks strictly raises the
/// optimal playout margin.
#[test]
fn exponential_pauses_match_campbell_and_click_rate() {
    let m0 = hold_margin_with_clicks(WIRELESS.pause_rate, WIRELESS.pause_length, 1e-3, 1.0, 0.0);
    let m1 = hold_margin_with_clicks(WIRELESS.pause_rate, WIRELESS.pause_length, 1e-3, 1.0, 0.15);
    assert!(m1 > m0, "click penalty must increase optimal margin");

    let th_missed = campbell_fraction(WIRELESS.pause_rate, WIRELESS.pause_length, m0);
    let th_clicks = click_rate(WIRELESS.pause_rate, WIRELESS.pause_length, m0);
    let (sim_missed, sim_clicks) =
        stream_pause_metrics(WIRELESS, 0.0, 0.01, 60_000.0, 100.0, m0, 3);
    assert!(
        (sim_missed - th_missed).abs() < 0.25 * th_missed,
        "missed sim={sim_missed}, theory={th_missed}"
    );
    assert!(
        (sim_clicks - th_clicks).abs() < 0.25 * th_clicks,
        "clicks sim={sim_clicks}, theory={th_clicks}"
    );
}

/// Scalar random-walk steady-state variance matches `Spectral.posterior_variance`,
/// and `decentralized_star_weight` / `gain_for_weight` invert `Regulation.weight`.
#[test]
fn kalman_closed_form_and_decentralized_gain() {
    let step_variance = 4e-12;
    let measurement_variance = 9e-12;
    let noise = FrequencyNoise {
        white: 2.0 * step_variance,
        walk: 0.0,
    };
    let mut filter = OffsetFilter::new(0.0, 1.0, 0.0, noise);
    for _ in 0..1000 {
        filter.predict(1.0);
        filter.update_zero_lag(0.0, measurement_variance);
    }
    let s = step_variance / measurement_variance;
    let a = 1.0 + s / 2.0 - (s + (s / 2.0) * (s / 2.0)).sqrt();
    let closed = measurement_variance * (1.0 - a);
    assert!(
        (filter.offset_variance() - closed).abs() < 1e-9 * closed,
        "{} vs {closed}",
        filter.offset_variance()
    );

    let c_eff = decentralized_star_weight(4, 1.0, 0.25);
    assert!((c_eff - 1.0).abs() < 1e-12);
    let g = gain_for_weight(c_eff);
    let w = g.powi(4) / ((2.0 - g).powi(2) * (1.0 - g));
    assert!((w - c_eff).abs() < 1e-10);
}
