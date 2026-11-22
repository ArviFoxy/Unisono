// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Verification and mutation-catching tests for the star and peer
//! synchronization simulations in `unisono_sim::star` against the analytical
//! results of `Unisono.Solutions.Optimal`.

use std::f64::consts::{LN_2, PI};

use unisono_sim::link::LinkModel;
use unisono_sim::random::Generator;
use unisono_sim::star::{
    ClockState, Exchange, FrequencyNoise, GraphEdge, HeterogeneousKinds, OffsetFilter,
    PeerComparisonConfig, ReceiverSetting, SlidingMinRtt, StarComparison, VarianceMode,
    advance_clock, blue_common_variance, blue_diff_variances, blue_pair_bias, campbell_fraction,
    click_rate, compare_star, cycle_clock_innovation_cov, decentralized_star_weight,
    disciplined_schedule_comparison, effective_resistance, gain_for_weight,
    hold_margin_with_clicks, mode_lyapunov_cost, optimal_shared_star_gain,
    peer_topology_comparison, pure_pause_block_metrics, quantiles, solve_graph_blue,
    star_lyapunov_cost,
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

/// Catches removing the `2 * pi^2` IEEE 1139 conversion factor and catches
/// replacing exact continuous-time Cholesky sampling with Euler-Maruyama
/// (which has zero phase-frequency increment cross-covariance and drops the
/// `q2 * dt^3 / 3` phase variance term).
#[test]
fn advance_clock_matches_exact_cholesky_covariance_and_2pi2_factor() {
    let noise = FrequencyNoise {
        h0_white: 2e-14,
        h1_flicker: 0.0,
        h2_walk: 5e-14,
    };
    let expected_q0 = noise.h0_white / 2.0;
    let expected_q2 = 2.0 * PI * PI * noise.h2_walk;
    assert!(
        (noise.white_variance_rate() - expected_q0).abs() < 1e-30,
        "white_variance_rate mismatch"
    );
    assert!(
        (noise.walk_variance_rate() - expected_q2).abs() < 1e-26,
        "walk_variance_rate must include 2 * pi^2 factor"
    );

    let dt = 2.0;
    let samples = 20_000_i32;
    let mut rng = Generator::new(42);
    let mut phase_sq_sum = 0.0;
    let mut cross_sum = 0.0;
    let mut freq_sq_sum = 0.0;
    for _ in 0..samples {
        let mut st = (0.0, 0.0);
        advance_clock(&mut st, noise, dt, &mut rng);
        phase_sq_sum += st.0 * st.0;
        cross_sum += st.0 * st.1;
        freq_sq_sum += st.1 * st.1;
    }
    let n = f64::from(samples);
    let var_p = phase_sq_sum / n;
    let cov_pf = cross_sum / n;
    let var_f = freq_sq_sum / n;

    let theory_phase = expected_q0 * dt + expected_q2 * dt.powi(3) / 3.0;
    let theory_cross = expected_q2 * dt * dt / 2.0;
    let theory_freq = expected_q2 * dt;
    assert!(
        (var_p - theory_phase).abs() < 0.05 * theory_phase,
        "phase increment variance {var_p} vs exact {theory_phase} (Euler-Maruyama would give {})",
        expected_q0 * dt
    );
    assert!(
        (cov_pf - theory_cross).abs() < 0.05 * theory_cross,
        "phase-frequency cross-covariance {cov_pf} vs exact {theory_cross} (Euler-Maruyama gives 0)"
    );
    assert!(
        (var_f - theory_freq).abs() < 0.05 * theory_freq,
        "frequency increment variance {var_f} vs exact {theory_freq}"
    );
}

/// Verifies the multi-stage Ornstein-Uhlenbeck flicker frequency synthesis
/// bank produces a nearly flat Allan deviation matching the IEEE 1139 flicker
/// floor `sqrt(2 * ln(2) * h_{-1})` across `tau = 1 s` and `tau = 10 s`.
#[test]
fn flicker_bank_matches_ieee_1139_allan_deviation_floor() {
    let h1 = 1e-14;
    let noise = FrequencyNoise {
        h0_white: 0.0,
        h1_flicker: h1,
        h2_walk: 0.0,
    };
    let floor = (2.0 * LN_2 * h1).sqrt();
    let mut rng = Generator::new(99);
    let mut clk = ClockState::new(0.0, 0.0, noise, &mut rng);
    let steps = 4000;
    let dt = 1.0;
    let mut phases = Vec::with_capacity(steps + 1);
    phases.push(clk.phase);
    for _ in 0..steps {
        clk.advance(dt, &mut rng);
        phases.push(clk.phase);
    }
    let allan_dev = |tau_steps: usize| -> f64 {
        let mut acc = 0.0;
        let mut cnt = 0_usize;
        for k in 0..(phases.len() - 2 * tau_steps) {
            let d2 = phases[k + 2 * tau_steps] - 2.0 * phases[k + tau_steps] + phases[k];
            acc += d2 * d2;
            cnt += 1;
        }
        #[allow(clippy::cast_precision_loss)]
        let tau = tau_steps as f64 * dt;
        #[allow(clippy::cast_precision_loss)]
        let var = acc / (2.0 * tau * tau * cnt as f64);
        var.sqrt()
    };
    let adev_1 = allan_dev(1);
    let adev_10 = allan_dev(10);
    assert!(
        (0.70 * floor..1.35 * floor).contains(&adev_1),
        "flicker ADEV(1 s) = {adev_1:.3e} vs IEEE 1139 floor {floor:.3e}"
    );
    assert!(
        (0.70 * floor..1.35 * floor).contains(&adev_10),
        "flicker ADEV(10 s) = {adev_10:.3e} vs IEEE 1139 floor {floor:.3e}"
    );
}

/// Deterministic analytical test catching missing cross-covariance terms in
/// `OffsetFilter::predict`, wrong `2 * pi^2` scaling in `Q(dt)`, and Riccati
/// steady-state mismatch against `Spectral.posterior_variance`.
#[test]
fn kalman_predict_exact_covariance_and_riccati_fixed_point() {
    let noise = FrequencyNoise {
        h0_white: 2e-14,
        h1_flicker: 0.0,
        h2_walk: 5e-14,
    };
    let mut f = OffsetFilter::new(0.0, 1e-8, 1e-10, noise);
    f.predict(0.5);
    f.update_zero_lag(1e-4, 4e-10);
    // Now `p01` is strictly nonzero. Check one exact `predict(dt)` step
    // analytically against `F P F^T + Q(dt)`.
    let [[p00, p01], [_, p11]] = f.covariance();
    assert!(p01 > 0.0, "posterior cross-covariance must be positive");
    let dt = 1.5;
    let q0 = noise.h0_white / 2.0;
    let q2 = 2.0 * PI * PI * noise.h2_walk;
    let exp_p00 = p00 + 2.0 * p01 * dt + p11 * dt * dt + q0 * dt + q2 * dt.powi(3) / 3.0;
    let exp_p01 = p01 + p11 * dt + q2 * dt * dt / 2.0;
    let exp_p11 = p11 + q2 * dt;
    f.predict(dt);
    let got = f.covariance();
    assert!(
        (got[0][0] - exp_p00).abs() < 1e-18,
        "p00 mismatch: {} vs {exp_p00}",
        got[0][0]
    );
    assert!(
        (got[0][1] - exp_p01).abs() < 1e-18,
        "p01 mismatch: {} vs {exp_p01}",
        got[0][1]
    );
    assert!(
        (got[1][1] - exp_p11).abs() < 1e-18,
        "p11 mismatch: {} vs {exp_p11}",
        got[1][1]
    );

    // Scalar random-walk steady-state check matching `Spectral.posterior_variance`.
    let step_variance = 4e-12;
    let measurement_variance = 9e-12;
    let rw = FrequencyNoise {
        h0_white: 2.0 * step_variance,
        h1_flicker: 0.0,
        h2_walk: 0.0,
    };
    let mut filter = OffsetFilter::new(0.0, 1.0, 0.0, rw);
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
}

/// Verifies `SlidingMinRtt` never feeds the same `Exchange` twice into the
/// Kalman filter, even when an unusually low-RTT exchange remains in the
/// sliding window across consecutive strides.
#[test]
fn sliding_min_rtt_never_reuses_an_exchange() {
    let mut sel = SlidingMinRtt::new(8, 4);
    let mode = VarianceMode::Online {
        initial: 1e-8,
        floor: 25e-12,
    };
    let mut last_id = 0_u64;
    let mut emitted = 0_usize;
    for idx in 1..=200_u64 {
        // Every 8th exchange is unusually fast (`100 us`), while others are
        // slower (`500 us`), so without deduplication the fast exchange would
        // be emitted on two consecutive strides.
        #[allow(clippy::cast_precision_loss)]
        let t = idx as f64 * 0.25;
        let rtt = if idx % 8 == 6 { 100e-6 } else { 500e-6 };
        let ex = Exchange {
            id: idx,
            offset: 0.0,
            round_trip: rtt,
            middle: t,
            arrival: t + rtt / 2.0,
        };
        if let Some((best, _)) = sel.push(ex, mode) {
            assert!(
                best.id > last_id,
                "exchange id {} reused after {}",
                best.id,
                last_id
            );
            last_id = best.id;
            emitted += 1;
        }
    }
    assert!(
        emitted >= 25,
        "expected regular fresh emissions, got {emitted}"
    );
}

/// Catches the `+ V_bc` vs `- V_bc` residual-variance sign error in
/// `Estimation.residual_variance_sub` directly by comparing empirical residual
/// variance `Var(m_r - m_bar)` against `sigma_r^2 - V_bc`.
#[test]
fn inverse_variance_residual_variance_is_sigma_sq_minus_v_bc() {
    let sigmas = [4e-6_f64, 4e-6, 4e-6, 150e-6, 150e-6];
    let weights: Vec<f64> = sigmas.iter().map(|s| 1.0 / (s * s)).collect();
    let total_w: f64 = weights.iter().sum();
    let v_bc = 1.0 / total_w;
    let expected_wired = sigmas[0].powi(2) - v_bc;
    let wrong_plus = sigmas[0].powi(2) + v_bc;
    assert!(expected_wired < 0.7 * sigmas[0].powi(2));
    assert!(wrong_plus > 1.3 * sigmas[0].powi(2));

    let trials = 40_000_i32;
    let mut rng = Generator::new(77);
    let mut sum_sq_wired = 0.0;
    for _ in 0..trials {
        let errs: Vec<f64> = sigmas.iter().map(|&s| s * rng.normal()).collect();
        let mean_w: f64 = errs.iter().zip(&weights).map(|(e, w)| e * w).sum::<f64>() / total_w;
        let res0 = errs[0] - mean_w;
        sum_sq_wired += res0 * res0;
    }
    let emp_var = sum_sq_wired / f64::from(trials);
    assert!(
        (emp_var - expected_wired).abs() < 0.04 * expected_wired,
        "empirical residual variance {emp_var:.3e} vs sigma^2 - V_bc = {expected_wired:.3e} (sigma^2 + V_bc = {wrong_plus:.3e})"
    );
}

/// Deterministic analytical verification of the discrete Lyapunov star-gain
/// solver:
/// 1. For a single mode, `mode_lyapunov_cost(g, weight(g*), sigma)` is
///    uniquely minimized at `g = g*`.
/// 2. With zero sender wander, `optimal_shared_star_gain` equals
///    `gain_for_weight(((R-1)/R) c_S + c_track)`.
/// 3. As sender wander increases, `optimal_shared_star_gain` strictly shifts
///    down toward `gain_for_weight(c_track)` and beats the independent gain.
#[test]
fn lyapunov_star_gain_matches_independent_limit_and_shifts_under_sender_wander() {
    let c_sync = 1.0e-5;
    let c_track = 1.0e-7;
    let receivers = 4;
    let dt = 0.01;

    // 1. Single-mode optimality check for `gain_for_weight`.
    let c_eff = decentralized_star_weight(receivers, c_sync, c_track);
    let g_indep = gain_for_weight(c_eff);
    let w_check = g_indep.powi(4) / ((2.0 - g_indep).powi(2) * (1.0 - g_indep));
    assert!((w_check - c_eff).abs() < 1e-12);

    let sigma_rx = cycle_clock_innovation_cov(FrequencyNoise::CONSUMER_QUARTZ, dt);
    let j_at_opt = mode_lyapunov_cost(g_indep, c_eff, sigma_rx);
    assert!(mode_lyapunov_cost(g_indep * 0.8, c_eff, sigma_rx) > j_at_opt);
    assert!(mode_lyapunov_cost(g_indep * 1.2, c_eff, sigma_rx) > j_at_opt);

    // 2. Zero sender wander -> exact match with `gain_for_weight(((R-1)/R) c_S + c_track)`.
    let zero_cov = [[0.0, 0.0], [0.0, 0.0]];
    let g0 = optimal_shared_star_gain(receivers, c_sync, c_track, zero_cov, sigma_rx);
    assert!(
        (g0 - g_indep).abs() < 1e-4 * g_indep,
        "zero-sender-wander optimal star gain {g0} vs independent gain {g_indep}"
    );

    // 3. Large sender wander -> shifts down toward `gain_for_weight(c_track)`.
    let g_track = gain_for_weight(c_track);
    let sigma_s_100 = cycle_clock_innovation_cov(FrequencyNoise::WANDERING_QUARTZ, dt);
    let g100 = optimal_shared_star_gain(receivers, c_sync, c_track, sigma_s_100, sigma_rx);
    assert!(
        g100 > g_track && g100 < g_indep * 0.9,
        "expected wandering sender to pull shared star gain toward g_track={g_track}: g100={g100}, g_indep={g_indep}"
    );
    let j_opt = star_lyapunov_cost(receivers, c_sync, c_track, sigma_s_100, sigma_rx, g100);
    let j_ind = star_lyapunov_cost(receivers, c_sync, c_track, sigma_s_100, sigma_rx, g_indep);
    assert!(
        j_opt < j_ind,
        "Lyapunov optimal shared gain must strictly beat independent gain: {j_opt} vs {j_ind}"
    );
}

/// Verifies exact Thomson effective resistance, exact correlated BLUE
/// common-mode variance `(1/R^2) 1^T L_red^{-1} 1` (catching the old buggy
/// trace formula `tr(L_red^{-1}) / R^2`), differential variances, and the
/// exact BLUE bias formula `sum_e f_e^* alpha_e` across all three triangle
/// regimes.
#[test]
fn graph_blue_resistance_correlated_common_variance_and_exact_bias() {
    let v = 1e-8;
    // Complete graph K_5 (`R = 4` receivers, sender 0):
    // `L_red = (1/v) * (5 I - 1 1^T)`, so `L_red^{-1} 1 = v * 1` and
    // `(1/R^2) 1^T L_red^{-1} 1 = v / 4`, whereas the old buggy trace formula
    // `tr(L_red^{-1}) / R^2 = (4 * 2v/5) / 16 = v / 10` (2.5x too small!).
    let mut k5 = Vec::new();
    for u in 0..5 {
        for w in (u + 1)..5 {
            k5.push(GraphEdge {
                src: u,
                dst: w,
                variance: v,
                bias: 0.0,
            });
        }
    }
    assert!((effective_resistance(5, &k5, 1, 2) - 2.0 * v / 5.0).abs() < 1e-20);
    let com_var_k5 = blue_common_variance(5, &k5);
    assert!(
        (com_var_k5 - v / 4.0).abs() < 1e-20,
        "K5 BLUE common-mode variance {com_var_k5} must equal v/4 = {} (trace formula gave {})",
        v / 4.0,
        v / 10.0
    );
    let diff_vars_k5 = blue_diff_variances(5, &k5);
    // On K_5, `(e_r - 1/4 1)^T L_red^{-1} (e_r - 1/4 1) = (3/4) * (v/5) = 3v/20`.
    for &dv in &diff_vars_k5 {
        assert!((dv - 3.0 * v / 20.0).abs() < 1e-20, "K5 diff var {dv}");
    }

    // Triangle BLUE exact bias `(vP / (2 vW + vP)) * (b2 - b1)` matching
    // `Unisono.Solutions.Optimal.triangle_blue_bias`:
    let tri_bias = |std_w: f64, std_p: f64| -> f64 {
        let vw = std_w * std_w;
        let vp = std_p * std_p;
        let edges = vec![
            GraphEdge {
                src: 0,
                dst: 1,
                variance: vw,
                bias: 750e-6,
            },
            GraphEdge {
                src: 0,
                dst: 2,
                variance: vw,
                bias: -750e-6,
            },
            GraphEdge {
                src: 1,
                dst: 2,
                variance: vp,
                bias: 0.0,
            },
        ];
        blue_pair_bias(3, &edges, 1, 2).abs()
    };
    // 1. Equal link variances -> 1/3 of 1500 us = 500 us.
    assert!((tri_bias(50e-6, 50e-6) - 500e-6).abs() < 1e-12);
    // 2. Wired sender (5 us), Wi-Fi peer (150 us) -> ~1496.67 us.
    let b_wired_sender = tri_bias(5e-6, 150e-6);
    let expected_wired_sender = 1500e-6 * (150.0_f64.powi(2) / (2.0 * 25.0 + 150.0_f64.powi(2)));
    assert!((b_wired_sender - expected_wired_sender).abs() < 1e-12);
    // 3. Wi-Fi sender (150 us), wired peer (5 us) -> ~0.833 us (nonzero!).
    let b_wifi_sender = tri_bias(150e-6, 5e-6);
    let expected_wifi_sender = 1500e-6 * (25.0 / (2.0 * 150.0_f64.powi(2) + 25.0));
    assert!((b_wifi_sender - expected_wifi_sender).abs() < 1e-12);
    assert!(
        b_wifi_sender > 0.5e-6,
        "BLUE bias is small but strictly nonzero"
    );

    // Noiseless exact recovery check for `solve_graph_blue`.
    let truth = [0.0, 0.123, -0.456];
    let tri = vec![
        GraphEdge {
            src: 0,
            dst: 1,
            variance: 1e-8,
            bias: 0.0,
        },
        GraphEdge {
            src: 0,
            dst: 2,
            variance: 1e-8,
            bias: 0.0,
        },
        GraphEdge {
            src: 1,
            dst: 2,
            variance: 1e-10,
            bias: 0.0,
        },
    ];
    let obs: Vec<f64> = tri.iter().map(|e| truth[e.dst] - truth[e.src]).collect();
    let est = solve_graph_blue(3, &tri, &obs);
    for (e, t) in est.iter().zip(truth) {
        assert!((e - t).abs() < 1e-12);
    }
}

/// Checks `hold_margin_with_clicks` returns `None` for `w_lat <= 0`, increases
/// strictly with click pricing, and matches exact block-grid pause simulation
/// (including the constant exponential discretization factor) across multiple
/// seeds.
#[test]
fn playout_margin_handles_zero_latency_weight_and_matches_block_sim() {
    assert!(hold_margin_with_clicks(0.05, 0.03, 0.0, 1.0, 0.0).is_none());
    assert!(hold_margin_with_clicks(0.05, 0.03, -1e-3, 1.0, 0.0).is_none());

    let m0 = hold_margin_with_clicks(WIRELESS.pause_rate, WIRELESS.pause_length, 1e-3, 1.0, 0.0)
        .expect("positive w_lat yields finite margin");
    let m1 = hold_margin_with_clicks(WIRELESS.pause_rate, WIRELESS.pause_length, 1e-3, 1.0, 0.15)
        .expect("positive w_lat yields finite margin");
    assert!(
        m1 > m0,
        "click penalty must strictly increase optimal margin"
    );

    // Under pure exponential pauses of mean `h_bar = 30 ms` sampled on a
    // `cycle = 10 ms` block grid, a pause exceeding `m` misses at least one
    // block with probability `(1 - exp(-cycle / h_bar)) / (cycle / h_bar)`
    // (roughly `0.850` for `cycle / h_bar = 1/3`, constant across margins by
    // memorylessness of the exponential distribution).
    let th_missed = campbell_fraction(WIRELESS.pause_rate, WIRELESS.pause_length, m0);
    let th_clicks = click_rate(WIRELESS.pause_rate, WIRELESS.pause_length, m0);
    let ratio = 0.01 / WIRELESS.pause_length;
    let discrete_factor = (1.0 - (-ratio).exp()) / ratio;
    for seed in [11_u64, 22, 33] {
        let (sim_m, sim_c, events) = pure_pause_block_metrics(
            WIRELESS.pause_rate,
            WIRELESS.pause_length,
            0.01,
            0.0,
            2_000_000.0,
            m0,
            seed,
        );
        assert!(events > 1000, "expected ample events, got {events}");
        assert!(
            (sim_m - th_missed).abs() < 0.08 * th_missed,
            "seed {seed}: missed sim={sim_m:.3e} vs theory={th_missed:.3e}"
        );
        let expected_c = th_clicks * discrete_factor;
        assert!(
            (sim_c - expected_c).abs() < 0.08 * expected_c,
            "seed {seed}: clicks sim={sim_c:.3e} vs discrete theory={expected_c:.3e}"
        );
    }
}

/// Multi-seed verification that the strictly causal sender-disciplined
/// schedule (with delayed/lossy uplinks, delayed downlinks, and noisy
/// initialization) reduces mixed-pair spread under a 100x wandering sender.
#[test]
fn causal_disciplined_schedule_reduces_wandering_sender_mixed_spread() {
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
    let seeds = [101_u64, 202, 303, 404, 505];
    let mut own_mixed = Vec::new();
    let mut sched_mixed = Vec::new();
    for &seed in &seeds {
        let (own, sched) = disciplined_schedule_comparison(
            kinds,
            FrequencyNoise::WANDERING_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ,
            1.0,
            8_000,
            seed,
        );
        own_mixed.push(own.spreads.mixed);
        sched_mixed.push(sched.spreads.mixed);
    }
    let own_med = quantiles(&own_mixed).0;
    let sched_med = quantiles(&sched_mixed).0;
    assert!(
        sched_med < own_med * 0.85,
        "expected causal schedule median mixed spread {sched_med:.3e} < 0.85 * own {own_med:.3e}"
    );
}

/// Seed-independent multi-seed verification of star baselines (including
/// min-RTT 100 ppm) vs star calibrated/online controllers.
#[test]
fn multi_seed_star_comparisons_are_consistent() {
    let wired = ReceiverSetting {
        forward: WIRED,
        backward: WIRED,
        drop_rate: 0.0,
        timestamp_std: 10e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        filter_noise_override: None,
        calibrated_variance: (10.4e-6_f64).powi(2),
    };
    let wireless = ReceiverSetting {
        forward: WIRELESS,
        backward: WIRELESS,
        drop_rate: 0.02,
        timestamp_std: 10e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        filter_noise_override: None,
        calibrated_variance: (170e-6_f64).powi(2),
    };
    let setting = StarComparison {
        cycle: 0.01,
        lookahead: 16.0 / 48_000.0,
        period: 0.25,
        window: 8,
        stride: 4,
        duration: 400.0,
        warmup: 80.0,
        playout_margin: 0.05,
        online_variance_floor: (5e-6_f64).powi(2),
        gain: gain_for_weight(decentralized_star_weight(3, 2.0e-6, 4.0e-7)),
        sender: FrequencyNoise::CONSUMER_QUARTZ,
        receivers: vec![wired, wired, wireless],
    };
    let seeds = [101_u64, 202, 303, 404, 505, 606, 707];
    let mut b1000_sp = Vec::new();
    let mut bmin_rg = Vec::new();
    let mut onl_sp = Vec::new();
    let mut onl_rg = Vec::new();
    for &seed in &seeds {
        let res = compare_star(&setting, seed);
        b1000_sp.push(res.baseline_1000ppm.spread);
        bmin_rg.push(res.baseline_min_rtt_100ppm.speed_change);
        onl_sp.push(res.star_online.spread);
        onl_rg.push(res.star_online.speed_change);
    }
    assert!(
        quantiles(&onl_sp).0 * 3.0 < quantiles(&b1000_sp).0,
        "star online median spread should beat 1000 ppm baseline by >3x"
    );
    assert!(
        quantiles(&onl_rg).0 * 5.0 < quantiles(&bmin_rg).0,
        "star online median roughness should beat min-RTT 100 ppm baseline by >5x"
    );
}

/// Verifies peer BLUE under both opposite-sign and same-sign sender asymmetry.
#[test]
fn peer_asymmetry_opposite_and_same_sign() {
    let opp = peer_topology_comparison(
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
            steps: 6_000,
            g_com: 0.05,
            g_com_low: 0.005,
            g_diff: 0.15,
        },
        23,
    );
    assert!(opp.star.spread > 700e-6);
    assert!(opp.peer_lipsync.spread < 15e-6);
    assert!(opp.peer_lowlatency.spread < 15e-6);

    let same = peer_topology_comparison(
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
                    bias: 750e-6,
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
            steps: 6_000,
            g_com: 0.05,
            g_com_low: 0.005,
            g_diff: 0.15,
        },
        23,
    );
    assert!(
        same.star.spread < 80e-6,
        "same-sign asymmetry cancels in spread"
    );
    assert!(
        same.star.error > 700e-6,
        "same-sign asymmetry appears in tracking error"
    );
    assert!(
        same.peer_lipsync.spread * 3.0 < same.star.spread,
        "wired peer link still cuts spread by >3x under same-sign asymmetry"
    );
}

/// Verifies bounded low-latency peer control keeps latency error far below
/// unbounded `g_com = 0` while cutting roughness vs lip-sync, and checks
/// bidirectional star edges do not double-predict star filters.
#[test]
fn peer_bounded_lowlatency_and_bidirectional_edges() {
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
            steps: 6_000,
            g_com: 0.10,
            g_com_low: 0.005,
            g_diff: 0.15,
        },
        29,
    );
    assert!(
        wander.peer_lowlatency.speed_change < wander.peer_lipsync.speed_change * 0.65,
        "bounded low-latency should cut roughness: low={:?} lip={:?}",
        wander.peer_lowlatency,
        wander.peer_lipsync
    );
    assert!(
        wander.peer_lowlatency.error * 10.0 < wander.peer_unbounded_consensus.error,
        "bounded low-latency must keep latency error far below unbounded g_com=0: low={:?} unb={:?}",
        wander.peer_lowlatency,
        wander.peer_unbounded_consensus
    );

    let bidir = peer_topology_comparison(
        &PeerComparisonConfig {
            receivers: 2,
            peer_edges: vec![
                GraphEdge {
                    src: 0,
                    dst: 1,
                    variance: 2e-8,
                    bias: 0.0,
                },
                GraphEdge {
                    src: 1,
                    dst: 0,
                    variance: 2e-8,
                    bias: 0.0,
                },
                GraphEdge {
                    src: 0,
                    dst: 2,
                    variance: 1e-8,
                    bias: 0.0,
                },
            ],
            sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            interval: 0.5,
            steps: 2_000,
            g_com: 0.05,
            g_com_low: 0.005,
            g_diff: 0.15,
        },
        55,
    );
    assert!(
        bidir.star.error < 100e-6,
        "bidirectional star edges must remain accurate without double prediction: {:?}",
        bidir.star
    );
}
