// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Prints the simulation tables for `docs/star-optimum.tex`:
//!
//! 1. Star topology: fixed-delay baseline (1000 ppm and fair 100 ppm slew) vs.
//!    star-optimal (sliding-window min-RTT + zero-lag Joseph Kalman +
//!    `Regulation.law`), both with calibrated and online adaptive variance,
//!    under realistic consumer quartz and OCXO clocks, UDP loss, and pauses.
//! 2. Sender-disciplined timestamped schedule across heterogeneous wired +
//!    wireless receivers with delayed delivery and shared sender-NIC jitter.
//! 3. Star vs. Peer (receiver-receiver) Graph-Laplacian BLUE + two-mode modal
//!    control (lip-sync and pure-consensus low-latency), including complete
//!    mesh `K_5` and asymmetric Wi-Fi sender + wired peer topologies.
//! 4. Playout latency margin under exponential pauses with discontinuity
//!    (click) pricing.
//!
//! Run with `cargo run --release -p unisono-sim --example star`.

use unisono_sim::link::LinkModel;
use unisono_sim::star::{
    FrequencyNoise, GraphEdge, HeterogeneousKinds, PeerComparisonConfig, ReceiverSetting,
    StarComparison, campbell_fraction, click_rate, compare_star, disciplined_schedule_comparison,
    hold_margin_with_clicks, peer_topology_comparison, stream_pause_metrics,
};

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

fn wired_rx(clock: FrequencyNoise) -> ReceiverSetting {
    ReceiverSetting {
        forward: WIRED,
        backward: WIRED,
        drop_rate: 0.0,
        timestamp_std: 2e-6,
        clock,
        oracle_variance: (4e-6_f64).powi(2),
    }
}

fn wireless_rx(clock: FrequencyNoise) -> ReceiverSetting {
    ReceiverSetting {
        forward: WIRELESS,
        backward: WIRELESS,
        drop_rate: 0.02,
        timestamp_std: 5e-6,
        clock,
        oracle_variance: (150e-6_f64).powi(2),
    }
}

fn star_scenario(sender: FrequencyNoise, receivers: Vec<ReceiverSetting>) -> StarComparison {
    StarComparison {
        cycle: 0.01,
        period: 0.25,
        window: 8,
        stride: 4,
        duration: 600.0,
        warmup: 60.0,
        playout_margin: 0.05,
        gain: 0.05,
        sender,
        receivers,
    }
}

fn print_star_table() {
    println!("=== 1. Star Topology: Baseline (1000/100 ppm) vs Star-Optimal (Oracle/Online) ===");
    println!(
        "{:<44} | {:>11} | {:>10} | {:>15} | {:>17}",
        "scenario [policy]", "spread (us)", "error (us)", "rms / max (ppm)", "missed / clicks/s"
    );
    let star_cases = [
        (
            "2 wired (OCXO)",
            FrequencyNoise::OCXO,
            vec![
                wired_rx(FrequencyNoise::OCXO),
                wired_rx(FrequencyNoise::OCXO),
            ],
        ),
        (
            "2 wired (consumer quartz)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ),
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ),
            ],
        ),
        (
            "2 wireless (quartz, 2% drop)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ),
            ],
        ),
        (
            "3 wired + 2 wireless (quartz)",
            FrequencyNoise::CONSUMER_QUARTZ,
            vec![
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ),
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ),
                wired_rx(FrequencyNoise::CONSUMER_QUARTZ),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ),
                wireless_rx(FrequencyNoise::CONSUMER_QUARTZ),
            ],
        ),
    ];
    for (name, sender, rxs) in star_cases {
        let res = compare_star(&star_scenario(sender, rxs), 7);
        for (label, out) in [
            ("base 1000ppm", res.baseline_1000ppm),
            ("base  100ppm", res.baseline_100ppm),
            ("star oracle ", res.star_oracle),
            ("star online ", res.star_online),
        ] {
            println!(
                "{:<44} | {:>11.2} | {:>10.2} | {:>6.2} / {:>6.2} | {:>7.2e} / {:>7.2e}",
                format!("{name} [{label}]"),
                out.spread * 1e6,
                out.error * 1e6,
                out.speed_change * 1e6,
                out.largest_speed_change * 1e6,
                out.missed_fraction,
                out.discontinuity_rate,
            );
        }
        println!();
    }
}

fn print_schedule_table() {
    println!(
        "=== 2. Sender-Disciplined Timestamped Schedule (3 wired + 2 wireless, 1-step delay) ==="
    );
    println!(
        "{:<22} | {:>18} | {:>18} | {:>18}",
        "sender oscillator", "all: own / sched", "wired: own / sched", "mixed: own / sched"
    );
    let kinds = HeterogeneousKinds {
        first: 3,
        second: 2,
        first_error: 4e-6,
        second_error: 150e-6,
        tx_common_error: 20e-6,
        schedule_delay_steps: 1,
    };
    for (name, sender) in [
        ("consumer quartz", FrequencyNoise::CONSUMER_QUARTZ),
        ("wandering quartz", FrequencyNoise::WANDERING_QUARTZ),
    ] {
        let (own, sched) = disciplined_schedule_comparison(
            kinds,
            sender,
            FrequencyNoise::CONSUMER_QUARTZ,
            1.0,
            50_000,
            11,
        );
        println!(
            "{:<22} | {:>8.2} / {:>7.2} | {:>8.2} / {:>7.2} | {:>8.2} / {:>7.2}",
            name,
            own.all * 1e6,
            sched.all * 1e6,
            own.first_kind * 1e6,
            sched.first_kind * 1e6,
            own.mixed * 1e6,
            sched.mixed * 1e6,
        );
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

fn print_peer_table() {
    println!("=== 3. Star vs Peer (Receiver-Receiver) Graph-Laplacian BLUE + Modal Control ===");
    println!(
        "{:<28} | {:>14} | {:>28} | {:>28}",
        "topology", "pair std (us)", "spread (us) star/lip/low", "rough (ppm) star/lip/low"
    );

    let cases = [
        (
            "K5 symmetric (R=4, 150us)",
            PeerComparisonConfig {
                receivers: 4,
                peer_edges: complete_mesh_edges(5, 150e-6),
                sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
                receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
                interval: 0.5,
                steps: 20_000,
                g_com: 0.05,
                g_diff: 0.15,
            },
            19_u64,
        ),
        (
            "Wi-Fi sender + wired (R=2)",
            PeerComparisonConfig {
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
                steps: 20_000,
                g_com: 0.05,
                g_diff: 0.15,
            },
            23_u64,
        ),
        (
            "K5 wandering sender (R=4)",
            PeerComparisonConfig {
                receivers: 4,
                peer_edges: complete_mesh_edges(5, 50e-6),
                sender_noise: FrequencyNoise::WANDERING_QUARTZ,
                receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
                interval: 0.5,
                steps: 20_000,
                g_com: 0.10,
                g_diff: 0.15,
            },
            29_u64,
        ),
    ];

    for (name, cfg, seed) in cases {
        let res = peer_topology_comparison(&cfg, seed);
        println!(
            "{:<28} | {:>5.1} -> {:>5.1} | {:>8.2} / {:>7.2} / {:>7.2} | {:>8.3} / {:>7.3} / {:>7.3}",
            name,
            res.star_pair_std_theory * 1e6,
            res.peer_pair_std_theory * 1e6,
            res.star.spread * 1e6,
            res.peer_lipsync.spread * 1e6,
            res.peer_lowlatency.spread * 1e6,
            res.star.speed_change * 1e6,
            res.peer_lipsync.speed_change * 1e6,
            res.peer_lowlatency.speed_change * 1e6,
        );
    }
    println!();
}

fn print_margin_table() {
    println!(
        "=== 4. Playout Margin under Exponential Pauses (30 ms / 20 s) with Click Pricing ==="
    );
    println!(
        "{:>10} | {:>10} | {:>11} | {:>21} | {:>21}",
        "w_lat/w_M", "w_D/w_M(s)", "margin (ms)", "missed: theory / sim", "clicks/s: thry / sim"
    );
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
        );
        let th_missed = campbell_fraction(WIRELESS.pause_rate, WIRELESS.pause_length, margin);
        let th_clicks = click_rate(WIRELESS.pause_rate, WIRELESS.pause_length, margin);
        let (sim_missed, sim_clicks) =
            stream_pause_metrics(WIRELESS, 0.0, 0.01, 200_000.0, 100.0, margin, 3);
        println!(
            "{w_lat:>10.0e} | {w_click:>10.2} | {:>11.1} | {:>9.2e} / {:>9.2e} | {:>9.2e} / {:>9.2e}",
            margin * 1e3,
            th_missed,
            sim_missed,
            th_clicks,
            sim_clicks,
        );
    }
}

fn main() {
    print_star_table();
    print_schedule_table();
    print_peer_table();
    print_margin_table();
}
