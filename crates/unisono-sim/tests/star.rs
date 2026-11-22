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
    ClockState, Exchange, FilteredStarLyapunov, FrequencyNoise, GraphEdge, HeterogeneousKinds,
    OffsetFilter, PeerComparisonConfig, PhaseCourse, ReceiverSetting, SlidingMinRtt,
    StarComparison, StarControllerConfig, VarianceMode, advance_clock, blue_common_variance,
    blue_diff_variances, blue_pair_bias, campbell_fraction, click_rate, compare_star,
    cycle_clock_innovation_cov, decentralized_star_weight, disciplined_schedule_comparison,
    effective_resistance, evaluate_outcome, filtered_star_lyapunov_cost, gain_for_weight,
    hold_margin_with_clicks, law, mode_lyapunov_cost, optimal_filtered_star_gain,
    optimal_shared_star_gain, peer_topology_comparison, pure_pause_block_metrics, quantiles,
    residual_measurement_variance, solve_graph_blue, star_lyapunov_cost, star_optimal_receiver,
    steady_state_kalman_gain,
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

/// Verifies the exact-OU Barnes-Jarvis flicker bank matches the IEEE 1139
/// flicker floor `sqrt(2 * ln(2) * h_{-1})` within a tight `[0.88, 1.10]` band
/// at `tau = 1 s`, `2 s`, and `10 s` (tight enough to reject both the old 15%
/// trapezoid overshoot and a `1.5x` variance mutation whose ADEV is `1.225x`).
#[test]
fn flicker_bank_matches_ieee_1139_allan_deviation_floor() {
    let h1 = 1e-14;
    let noise = FrequencyNoise {
        h0_white: 0.0,
        h1_flicker: h1,
        h2_walk: 0.0,
    };
    let floor = (2.0 * LN_2 * h1).sqrt();
    let dt = 1.0;
    let steps = 8000;
    let seeds = [99_u64, 199, 299, 399];
    let mut av_sum_1 = 0.0;
    let mut av_sum_2 = 0.0;
    let mut av_sum_10 = 0.0;
    for &seed in &seeds {
        let mut rng = Generator::new(seed);
        let mut clk = ClockState::new(0.0, 0.0, noise, &mut rng);
        let mut phases = Vec::with_capacity(steps + 1);
        phases.push(clk.phase);
        for _ in 0..steps {
            clk.advance(dt, &mut rng);
            phases.push(clk.phase);
        }
        let allan_var = |tau_steps: usize| -> f64 {
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
            {
                acc / (2.0 * tau * tau * cnt as f64)
            }
        };
        av_sum_1 += allan_var(1);
        av_sum_2 += allan_var(2);
        av_sum_10 += allan_var(10);
    }
    #[allow(clippy::cast_precision_loss)]
    let denom = seeds.len() as f64;
    let adev_1 = (av_sum_1 / denom).sqrt();
    let adev_2 = (av_sum_2 / denom).sqrt();
    let adev_10 = (av_sum_10 / denom).sqrt();
    for (tau, val) in [(1, adev_1), (2, adev_2), (10, adev_10)] {
        assert!(
            (0.88 * floor..1.10 * floor).contains(&val),
            "flicker ADEV({tau} s) = {val:.3e} outside [0.88, 1.10] * IEEE 1139 floor {floor:.3e}"
        );
    }
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
    assert!((got[0][0] - exp_p00).abs() < 1e-18);
    assert!((got[0][1] - exp_p01).abs() < 1e-18);
    assert!((got[1][1] - exp_p11).abs() < 1e-18);

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
/// Kalman filter.
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

/// Directly tests `unisono_sim::star::residual_measurement_variance` against
/// both the analytical `sigma_r^2 - V_bc` identity and empirical Monte Carlo
/// samples (catching the `+ V_bc` sign error in simulator code itself).
#[test]
fn inverse_variance_residual_variance_is_sigma_sq_minus_v_bc() {
    let sigmas = [4e-6_f64, 4e-6, 4e-6, 150e-6, 150e-6];
    let weights: Vec<f64> = sigmas.iter().map(|s| 1.0 / (s * s)).collect();
    let total_w: f64 = weights.iter().sum();
    let v_bc = 1.0 / total_w;
    let sim_res_var = residual_measurement_variance(sigmas[0].powi(2), v_bc);
    let expected_wired = sigmas[0].powi(2) - v_bc;
    let wrong_plus = sigmas[0].powi(2) + v_bc;
    assert!(
        (sim_res_var - expected_wired).abs() < 1e-24,
        "residual_measurement_variance returned {sim_res_var:.3e}, expected {expected_wired:.3e} (not {wrong_plus:.3e})"
    );
    assert!(sim_res_var < 0.7 * sigmas[0].powi(2));

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
        (emp_var - sim_res_var).abs() < 0.04 * sim_res_var,
        "empirical residual variance {emp_var:.3e} vs sim {sim_res_var:.3e}"
    );
}

/// Catches flipping the sign of `cycle_clock_innovation_cov[0][1]` directly
/// AND by comparing `mode_lyapunov_cost` against a Monte Carlo simulation of
/// `Regulation.law` with exact frequency-walk increments (`23.38` vs `11.29`
/// for the wrong sign).
#[test]
fn cycle_clock_innovation_cov_sign_matches_montecarlo_lyapunov() {
    let dt = 1.0;
    let unit_walk = FrequencyNoise {
        h0_white: 0.0,
        h1_flicker: 0.0,
        h2_walk: 1.0 / (2.0 * PI * PI), // q2 = 1.0 exactly
    };
    let cov = cycle_clock_innovation_cov(unit_walk, dt);
    assert!(
        cov[0][1] < -0.49 && cov[0][1] > -0.51,
        "cross-covariance Cov(xi1, xi2) must be -q2 * dt^3 / 2 = -0.5, got {}",
        cov[0][1]
    );
    assert!((cov[0][0] - 1.0 / 3.0).abs() < 1e-12);
    assert!((cov[1][1] - 1.0).abs() < 1e-12);

    // Analytical Lyapunov cost for g = 0.3, c_pos = 1.0, q2 = 1, dt = 1:
    // equals ~23.38 (wrong +0.5 sign gives ~11.29).
    let g = 0.3;
    let c_pos = 1.0;
    let lyap = mode_lyapunov_cost(g, c_pos, cov);
    assert!(
        (lyap - 23.38).abs() < 0.25,
        "expected analytical Lyapunov cost ~23.38 (not wrong-sign 11.29), got {lyap:.4}"
    );

    // Independent Monte Carlo verification of `Regulation.law` driven by
    // exact continuous-time integrated Brownian motion `advance_clock`.
    let mut rng = Generator::new(314);
    let mut clk = (0.0_f64, 0.0_f64);
    let mut pos = 0.0_f64;
    let mut read = 0.0_f64;
    let warmup = 5_000_usize;
    let steps = 80_000_usize;
    let mut cost_sum = 0.0;
    for k in 0..(warmup + steps) {
        let dist = clk.0 - pos;
        let pace = read - clk.1 * dt;
        let du = law(g, dist, pace);
        read += du;
        pos += read;
        advance_clock(&mut clk, unit_walk, dt, &mut rng);
        if k >= warmup {
            let e = clk.0 - pos;
            cost_sum += c_pos * e * e + du * du;
        }
    }
    #[allow(clippy::cast_precision_loss)]
    let mc_cost = cost_sum / steps as f64;
    assert!(
        (mc_cost - lyap).abs() < 0.06 * lyap,
        "Monte Carlo cost {mc_cost:.3} must match Lyapunov {lyap:.3}"
    );
}

/// Verifies both the corrected perfect-info Lyapunov star-gain benchmark AND
/// the coupled Kalman-filter-in-the-loop Lyapunov solver
/// (`filtered_star_lyapunov_cost`, `optimal_filtered_star_gain`), including
/// Monte Carlo agreement and proving that noisy measurements push the optimal
/// shared star gain below `gain_for_weight(c_track)`.
#[test]
fn lyapunov_and_filtered_star_gain_solvers_match_theory_and_montecarlo() {
    let c_sync = 1.0e-5;
    let c_track = 1.0e-7;
    let receivers = 4;
    let dt = 0.01;
    let c_eff = decentralized_star_weight(receivers, c_sync, c_track);
    let g_indep = gain_for_weight(c_eff);
    let g_track = gain_for_weight(c_track);

    let sigma_rx = cycle_clock_innovation_cov(FrequencyNoise::CONSUMER_QUARTZ, dt);
    let zero_cov = [[0.0, 0.0], [0.0, 0.0]];
    let g0 = optimal_shared_star_gain(receivers, c_sync, c_track, zero_cov, sigma_rx);
    assert!((g0 - g_indep).abs() < 1e-4 * g_indep);

    // Perfect-info benchmark with corrected negative cross-covariance:
    let sender_100 = FrequencyNoise {
        h0_white: FrequencyNoise::CONSUMER_QUARTZ.h0_white,
        h1_flicker: 0.0,
        h2_walk: FrequencyNoise::CONSUMER_QUARTZ.h2_walk * 100.0,
    };
    let sigma_s_100 = cycle_clock_innovation_cov(sender_100, dt);
    let g_pi_100 = optimal_shared_star_gain(receivers, c_sync, c_track, sigma_s_100, sigma_rx);
    assert!(
        (g_pi_100 - 0.04013).abs() < 5e-4,
        "expected corrected perfect-info gain ~0.04013, got {g_pi_100:.5}"
    );
    assert!(
        star_lyapunov_cost(receivers, c_sync, c_track, sigma_s_100, sigma_rx, g_pi_100)
            < star_lyapunov_cost(receivers, c_sync, c_track, sigma_s_100, sigma_rx, g_indep)
    );

    // Coupled Kalman-filter-in-the-loop Lyapunov solver:
    for (stride, meas_std, expected_g) in [
        (1_usize, 1e-6_f64, 0.02155_f64),
        (100, 2.8e-6, 0.00431),
        (100, 170e-6, 0.00055),
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
        let g_filt = optimal_filtered_star_gain(cfg);
        assert!(
            g_filt < g_track,
            "noisy measurements must push filtered star gain {g_filt:.5} below g(c_track)={g_track:.5}"
        );
        assert!(
            (g_filt - expected_g).abs() < 0.08 * expected_g,
            "stride={stride}, std={meas_std}: got g_filt={g_filt:.5}, expected ~{expected_g:.5}"
        );
        assert!(
            filtered_star_lyapunov_cost(cfg, g_filt) < filtered_star_lyapunov_cost(cfg, g_track)
        );
    }
}

/// Monte Carlo cross-check of `filtered_star_lyapunov_cost` with `R = 4`
/// Kalman-filtered star receivers under `100x` sender wander (`stride = 1`,
/// `1 us` noise).
#[test]
fn filtered_star_lyapunov_matches_montecarlo() {
    let c_sync = 1.0e-5;
    let c_track = 1.0e-7;
    let receivers = 4;
    let dt = 0.01;
    let sender_100 = FrequencyNoise {
        h0_white: FrequencyNoise::CONSUMER_QUARTZ.h0_white,
        h1_flicker: 0.0,
        h2_walk: FrequencyNoise::CONSUMER_QUARTZ.h2_walk * 100.0,
    };
    let cfg_mc = FilteredStarLyapunov {
        receivers,
        c_sync,
        c_track,
        sender_noise: sender_100,
        receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
        meas_var: (1e-6_f64).powi(2),
        cycle: dt,
        meas_stride: 1,
    };
    let g_test = 0.02155;
    let exact_cost = filtered_star_lyapunov_cost(cfg_mc, g_test);
    let k_gain = steady_state_kalman_gain(
        cfg_mc.sender_noise.combine(cfg_mc.receiver_noise),
        dt,
        cfg_mc.meas_var,
    );
    let mut rng = Generator::new(515);
    let mut s_clk = (0.0_f64, 0.0_f64);
    let mut r_clks = [(0.0_f64, 0.0_f64); 4];
    let mut est = [(0.0_f64, 0.0_f64); 4];
    let mut play = [(0.0_f64, 0.0_f64); 4];
    let warmup = 8_000_usize;
    let steps = 80_000_usize;
    let mut cost_sum = 0.0;
    for step in 0..(warmup + steps) {
        advance_clock(&mut s_clk, cfg_mc.sender_noise, dt, &mut rng);
        let mut errs = [0.0_f64; 4];
        let mut dus = [0.0_f64; 4];
        for r in 0..4 {
            advance_clock(&mut r_clks[r], cfg_mc.receiver_noise, dt, &mut rng);
            let truth = s_clk.0 - r_clks[r].0;
            let meas = truth + 1e-6 * rng.normal();
            // Steady-state Kalman predict + update.
            let pred_off = est[r].0 + est[r].1 * dt;
            let innov = meas - pred_off;
            est[r].0 = pred_off + k_gain[0] * innov;
            est[r].1 += k_gain[1] * innov;
            let dist = est[r].0 - play[r].0;
            let pace = play[r].1 - est[r].1 * dt;
            let du = law(g_test, dist, pace);
            play[r].1 += du;
            play[r].0 += play[r].1;
            errs[r] = truth - play[r].0;
            dus[r] = du;
        }
        if step >= warmup {
            let mean_e = errs.iter().sum::<f64>() / 4.0;
            let var_e = errs.iter().map(|e| (e - mean_e).powi(2)).sum::<f64>() / 4.0;
            let ms_e = errs.iter().map(|e| e * e).sum::<f64>() / 4.0;
            let ms_du = dus.iter().map(|u| u * u).sum::<f64>() / 4.0;
            cost_sum += c_sync * var_e + c_track * ms_e + ms_du;
        }
    }
    #[allow(clippy::cast_precision_loss)]
    let mc_cost = cost_sum / steps as f64;
    assert!(
        (mc_cost - exact_cost).abs() < 0.08 * exact_cost,
        "filtered star MC {mc_cost:.4e} vs exact Lyapunov {exact_cost:.4e}"
    );
}

/// Verifies exact Thomson effective resistance, exact correlated BLUE
/// common-mode variance `(1/R^2) 1^T L_red^{-1} 1`, differential variances,
/// and the exact BLUE bias formula `sum_e f_e^* alpha_e`.
#[test]
fn graph_blue_resistance_correlated_common_variance_and_exact_bias() {
    let v = 1e-8;
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
    assert!((com_var_k5 - v / 4.0).abs() < 1e-20);
    for &dv in &blue_diff_variances(5, &k5) {
        assert!((dv - 3.0 * v / 20.0).abs() < 1e-20);
    }

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
    assert!((tri_bias(50e-6, 50e-6) - 500e-6).abs() < 1e-12);
    let expected_wired_sender = 1500e-6 * (150.0_f64.powi(2) / (2.0 * 25.0 + 150.0_f64.powi(2)));
    assert!((tri_bias(5e-6, 150e-6) - expected_wired_sender).abs() < 1e-12);
    let expected_wifi_sender = 1500e-6 * (25.0 / (2.0 * 150.0_f64.powi(2) + 25.0));
    assert!((tri_bias(150e-6, 5e-6) - expected_wifi_sender).abs() < 1e-12);

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
/// strictly with click pricing, and matches exact block-grid pause simulation.
#[test]
fn playout_margin_handles_zero_latency_weight_and_matches_block_sim() {
    assert!(hold_margin_with_clicks(0.05, 0.03, 0.0, 1.0, 0.0).is_none());
    assert!(hold_margin_with_clicks(0.05, 0.03, -1e-3, 1.0, 0.0).is_none());

    let m0 = hold_margin_with_clicks(WIRELESS.pause_rate, WIRELESS.pause_length, 1e-3, 1.0, 0.0)
        .expect("positive w_lat yields finite margin");
    let m1 = hold_margin_with_clicks(WIRELESS.pause_rate, WIRELESS.pause_length, 1e-3, 1.0, 0.15)
        .expect("positive w_lat yields finite margin");
    assert!(m1 > m0);

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
        assert!(events > 1000);
        assert!((sim_m - th_missed).abs() < 0.08 * th_missed);
        let expected_c = th_clicks * discrete_factor;
        assert!((sim_c - expected_c).abs() < 0.08 * expected_c);
    }
}

/// Catches restoring a same-step weighted average in `ScheduleSim` (either at
/// step 0 or during steady state):
/// 1. Before `uplink_delay + downlink_delay` steps elapse, scheduled and own
///    policies are bit-identical (zero step-0 cross-receiver leak).
/// 2. Increasing `(uplink_delay_steps, downlink_delay_steps)` from `(1, 1)` to
///    `(25, 25)` strictly degrades wandering-sender mixed spread (impossible
///    if a same-step average were used).
/// 3. At `(1, 1)`, the causal schedule still beats `own` by >15% on mixed pairs.
#[test]
fn causal_disciplined_schedule_is_strictly_causal_and_reduces_mixed_spread() {
    let base_kinds = HeterogeneousKinds {
        first: 3,
        second: 2,
        first_error: 4e-6,
        second_error: 150e-6,
        tx_common_error: 20e-6,
        uplink_delay_steps: 5,
        downlink_delay_steps: 5,
        report_drop_rate: 0.02,
        gain: 0.15,
    };
    // Before 5 + 5 = 10 steps elapse, NO schedule broadcast has arrived yet:
    // `sched` must match `own` identically (catches non-causal step-0 init_avg).
    let (own_short, sched_short) = disciplined_schedule_comparison(
        base_kinds,
        FrequencyNoise::WANDERING_QUARTZ,
        FrequencyNoise::CONSUMER_QUARTZ,
        1.0,
        9,
        101,
    );
    assert!(
        (own_short.spreads.mixed - sched_short.spreads.mixed).abs() < 1e-12,
        "before first broadcast arrives, sched ({}) must equal own ({})",
        sched_short.spreads.mixed,
        own_short.spreads.mixed
    );

    let fast_kinds = HeterogeneousKinds {
        uplink_delay_steps: 1,
        downlink_delay_steps: 1,
        ..base_kinds
    };
    let slow_kinds = HeterogeneousKinds {
        uplink_delay_steps: 25,
        downlink_delay_steps: 25,
        ..base_kinds
    };
    let seeds = [101_u64, 202, 303, 404, 505];
    let mut own_mixed = Vec::new();
    let mut fast_mixed = Vec::new();
    let mut slow_mixed = Vec::new();
    for &seed in &seeds {
        let (own, fast) = disciplined_schedule_comparison(
            fast_kinds,
            FrequencyNoise::WANDERING_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ,
            1.0,
            8_000,
            seed,
        );
        let (_, slow) = disciplined_schedule_comparison(
            slow_kinds,
            FrequencyNoise::WANDERING_QUARTZ,
            FrequencyNoise::CONSUMER_QUARTZ,
            1.0,
            8_000,
            seed,
        );
        own_mixed.push(own.spreads.mixed);
        fast_mixed.push(fast.spreads.mixed);
        slow_mixed.push(slow.spreads.mixed);
    }
    let own_med = quantiles(&own_mixed).0;
    let fast_med = quantiles(&fast_mixed).0;
    let slow_med = quantiles(&slow_mixed).0;
    assert!(
        fast_med < own_med * 0.85,
        "expected causal schedule median mixed spread {fast_med:.3e} < 0.85 * own {own_med:.3e}"
    );
    assert!(
        slow_med > fast_med * 1.25,
        "25-step causal delay ({slow_med:.3e}) must degrade mixed spread vs 1-step ({fast_med:.3e}); catches same-step average leak"
    );
}

/// Catches:
/// 1. Ignoring latency error in `coupled_metrics`;
/// 2. Flipping the sign of latency error in `coupled_metrics`;
/// 3. Never counting dropped blocks as missed.
#[test]
fn coupled_metrics_catches_latency_error_sign_and_dropped_blocks() {
    // Part A: Forward link heavily queued (+4 ms mean) while backward link is
    // clear with a tiny 0.5 ms excess and tight 1.5 ms margin (zero drops).
    // `baseline_1000ppm` (no min-RTT) tracks the queued forward probes, giving
    // a positive offset error `played - truth > 0` (~+2 ms), which shrinks its
    // effective buffer margin by ~2 ms and causes many missed blocks.
    // `star_online` rejects queued probes via min-RTT, keeping error tiny and
    // missed fraction low. Flipping `lat_err` sign would invert this ordering;
    // ignoring `lat_err` would make both policies identical.
    let fwd_queued = LinkModel {
        minimum: 1e-3,
        clear_excess: 50e-6,
        queued: 0.9,
        queued_excess: 4e-3,
        pause_rate: 0.0,
        pause_length: 0.0,
        overtaken: 0.0,
        overtaken_excess: 0.0,
    };
    let bwd_clear = LinkModel {
        minimum: 1e-3,
        clear_excess: 400e-6,
        queued: 0.0,
        queued_excess: 0.0,
        pause_rate: 0.0,
        pause_length: 0.0,
        overtaken: 0.0,
        overtaken_excess: 0.0,
    };
    let rx_tight = ReceiverSetting {
        forward: fwd_queued,
        backward: bwd_clear,
        drop_rate: 0.0,
        timestamp_std: 5e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        filter_noise_override: None,
        calibrated_variance: (50e-6_f64).powi(2),
    };
    let tight_setting = StarComparison {
        cycle: 0.01,
        lookahead: 0.0,
        period: 0.1,
        window: 8,
        stride: 4,
        duration: 120.0,
        warmup: 20.0,
        playout_margin: 1.5e-3,
        online_variance_floor: (5e-6_f64).powi(2),
        gain: 0.05,
        sender: FrequencyNoise::CONSUMER_QUARTZ,
        receivers: vec![rx_tight, rx_tight],
    };
    let tight = compare_star(&tight_setting, 77);
    assert!(
        tight.baseline_1000ppm.missed_fraction > tight.star_online.missed_fraction + 0.15,
        "positive offset error must shrink margin (catching ignored or sign-flipped lat_err): base={:.3} vs star={:.3}",
        tight.baseline_1000ppm.missed_fraction,
        tight.star_online.missed_fraction
    );

    // Part B: 30% block drop rate with huge 10 s playout margin and zero-pause
    // wired link: missed fraction must reflect dropped blocks (~0.30).
    let rx_drop = ReceiverSetting {
        forward: WIRED,
        backward: WIRED,
        drop_rate: 0.30,
        timestamp_std: 5e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        filter_noise_override: None,
        calibrated_variance: (10e-6_f64).powi(2),
    };
    let drop_setting = StarComparison {
        cycle: 0.01,
        lookahead: 0.0,
        period: 0.1,
        window: 8,
        stride: 4,
        duration: 60.0,
        warmup: 10.0,
        playout_margin: 10.0,
        online_variance_floor: (5e-6_f64).powi(2),
        gain: 0.05,
        sender: FrequencyNoise::CONSUMER_QUARTZ,
        receivers: vec![rx_drop, rx_drop],
    };
    let dropped = compare_star(&drop_setting, 88);
    assert!(
        (0.22..0.38).contains(&dropped.star_online.missed_fraction),
        "dropped blocks must count as missed even at 10 s margin: got {:.3}",
        dropped.star_online.missed_fraction
    );
    assert!(dropped.star_online.discontinuity_rate > 10.0);
}

/// Catches ignoring `filter_noise_override` and removing `online_variance_floor`.
#[test]
fn filter_noise_override_and_online_variance_floor_are_active() {
    // 1. `filter_noise_override` must materially change `star_online` error
    //    when given a severe TCXO prior on a wandering-quartz sender over Wi-Fi.
    let rx_matched = ReceiverSetting {
        forward: WIRELESS,
        backward: WIRELESS,
        drop_rate: 0.02,
        timestamp_std: 10e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        filter_noise_override: None,
        calibrated_variance: (170e-6_f64).powi(2),
    };
    let rx_mismatched = ReceiverSetting {
        filter_noise_override: Some(FrequencyNoise::TCXO.combine(FrequencyNoise::TCXO)),
        ..rx_matched
    };
    let base_sc = StarComparison {
        cycle: 0.01,
        lookahead: 16.0 / 48_000.0,
        period: 0.25,
        window: 8,
        stride: 4,
        duration: 300.0,
        warmup: 60.0,
        playout_margin: 0.05,
        online_variance_floor: (5e-6_f64).powi(2),
        gain: 0.05,
        sender: FrequencyNoise::WANDERING_QUARTZ,
        receivers: vec![rx_matched, rx_matched],
    };
    let over_sc = StarComparison {
        receivers: vec![rx_mismatched, rx_mismatched],
        ..base_sc
    };
    let res_matched = compare_star(&base_sc, 101);
    let res_over = compare_star(&over_sc, 101);
    assert!(
        res_over.star_online.error > res_matched.star_online.error * 1.8,
        "TCXO override on wandering sender must strongly increase error: over={:.3e} vs matched={:.3e}",
        res_over.star_online.error,
        res_matched.star_online.error
    );
}

/// Catches removing `online_variance_floor` both directly in `SlidingMinRtt`
/// and end-to-end in `compare_star` on a zero-jitter high-timestamp-noise link.
#[test]
fn online_variance_floor_limits_kalman_gain_on_zero_jitter_link() {
    let mut sel = SlidingMinRtt::new(8, 4);
    let big_floor = (80e-6_f64).powi(2);
    let mut emitted_vars = Vec::new();
    for idx in 1..=64_u64 {
        #[allow(clippy::cast_precision_loss)]
        let t = idx as f64 * 0.25;
        let ex = Exchange {
            id: idx,
            offset: 0.0,
            round_trip: 200e-6, // zero RTT spread
            middle: t,
            arrival: t + 100e-6,
        };
        if let Some((_, var)) = sel.push(
            ex,
            VarianceMode::Online {
                initial: 1e-12,
                floor: big_floor,
            },
        ) {
            emitted_vars.push(var);
        }
    }
    assert_ne!(emitted_vars, [] as [f64; 0]);
    for &v in &emitted_vars {
        assert!(
            v >= big_floor * (1.0 - 1e-12),
            "online variance {v:.3e} dropped below floor {big_floor:.3e}"
        );
    }

    let zero_jitter = LinkModel {
        minimum: 100e-6,
        clear_excess: 0.0,
        queued: 0.0,
        queued_excess: 0.0,
        pause_rate: 0.0,
        pause_length: 0.0,
        overtaken: 0.0,
        overtaken_excess: 0.0,
    };
    let rx_zj = ReceiverSetting {
        forward: zero_jitter,
        backward: zero_jitter,
        drop_rate: 0.0,
        timestamp_std: 2e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        filter_noise_override: None,
        calibrated_variance: (10e-6_f64).powi(2),
    };
    let sc_high_floor = StarComparison {
        cycle: 0.01,
        lookahead: 0.0,
        period: 0.25,
        window: 8,
        stride: 4,
        duration: 200.0,
        warmup: 40.0,
        playout_margin: 0.05,
        online_variance_floor: (200e-6_f64).powi(2),
        gain: 0.05,
        sender: FrequencyNoise::WANDERING_QUARTZ,
        receivers: vec![rx_zj, rx_zj],
    };
    let sc_low_floor = StarComparison {
        online_variance_floor: (1e-6_f64).powi(2),
        ..sc_high_floor.clone()
    };
    let r_hi = compare_star(&sc_high_floor, 101);
    let r_lo = compare_star(&sc_low_floor, 101);
    assert!(
        r_hi.star_online.error > r_lo.star_online.error * 2.0,
        "200 us floor on zero-jitter link with 2 us timestamps must strongly lower Kalman gain vs 1 us floor: hi={:.3e} vs lo={:.3e}",
        r_hi.star_online.error,
        r_lo.star_online.error
    );
}

/// Catches a star receiver ignoring its Kalman frequency estimate between probes.
#[test]
fn star_receiver_uses_frequency_estimate_between_probes() {
    let freq_offset = 50e-6; // 50 ppm constant drift -> 100 us drift per 2 s probe interval
    let cycle = 0.01;
    let duration = 200.0;
    let cycles = 20_000_usize;
    let mut rng = Generator::new(7);
    let rx_clock = PhaseCourse::draw(
        0.0,
        0.0,
        FrequencyNoise {
            h0_white: 0.0,
            h1_flicker: 0.0,
            h2_walk: 0.0,
        },
        1e-3,
        duration + 5.0,
        &mut rng,
    );
    let mut exchs = Vec::new();
    for idx in 1..=100_u64 {
        #[allow(clippy::cast_precision_loss)]
        let t = idx as f64 * 2.0;
        exchs.push(Exchange {
            id: idx,
            offset: freq_offset * t,
            round_trip: 200e-6,
            middle: t,
            arrival: t + 100e-6,
        });
    }
    let played = star_optimal_receiver(
        &exchs,
        &rx_clock,
        cycle,
        cycles,
        StarControllerConfig {
            window: 1,
            stride: 1,
            variance: VarianceMode::Calibrated(1e-12),
            noise: FrequencyNoise::CONSUMER_QUARTZ,
            gain: 0.20,
            max_slew: 1e-3,
        },
    );
    let truth: Vec<f64> = (0..cycles)
        .map(|k| {
            #[allow(clippy::cast_precision_loss)]
            let t = k as f64 * cycle;
            freq_offset * t
        })
        .collect();
    let out = evaluate_outcome(&[played], &[truth], cycle, 4_000, 0.0, 0.0);
    // Without frequency extrapolation, a 50 ppm drift over 2 s produces ~50 us
    // sawtooth error (> 25 us RMS). With frequency tracking, error is < 2 us.
    assert!(
        out.error < 2e-6,
        "star receiver must extrapolate frequency between 2 s probes: RMS error = {:.3e}",
        out.error
    );
}

/// Verifies `evaluate_outcome` returns infinite spread/error when a receiver
/// never obtains an estimate (instead of scoring 0.0).
#[test]
fn evaluate_outcome_with_unlinked_receiver_is_infinite() {
    let res = peer_topology_comparison(
        &PeerComparisonConfig {
            receivers: 2,
            peer_edges: vec![
                GraphEdge {
                    src: 0,
                    dst: 1,
                    variance: 1e-8,
                    bias: 0.0,
                },
                GraphEdge {
                    src: 1,
                    dst: 2,
                    variance: 1e-8,
                    bias: 0.0,
                },
            ],
            sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            interval: 0.5,
            steps: 500,
            star_gain: 0.15,
            g_com: 0.05,
            g_com_low: 0.005,
            g_diff: 0.15,
            relay_delay_steps: 1,
            relay_drop_rate: 0.02,
        },
        13,
    );
    assert!(res.star.spread.is_infinite());
    assert!(res.star.error.is_infinite());
    assert!(res.decentralized_lipsync.spread.is_finite());
}

/// Seed-independent multi-seed verification of star baselines vs star controllers.
#[test]
fn multi_seed_star_comparisons_are_consistent() {
    let wired = ReceiverSetting {
        forward: WIRED,
        backward: WIRED,
        drop_rate: 0.0,
        timestamp_std: 10e-6,
        clock: FrequencyNoise::CONSUMER_QUARTZ,
        filter_noise_override: None,
        calibrated_variance: (10e-6_f64).powi(2),
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
    assert!(quantiles(&onl_sp).0 * 3.0 < quantiles(&b1000_sp).0);
    assert!(quantiles(&onl_rg).0 * 5.0 < quantiles(&bmin_rg).0);
}

/// Verifies both centralized and decentralized peer BLUE under opposite-sign
/// and same-sign sender asymmetry, AND verifies that under decentralized
/// receiver-local operation, `g_com = 0` suffers permanent spread mismatch
/// when a step-0 relay drops while `g_com_low > 0` eliminates it.
#[test]
fn peer_asymmetry_centralized_and_decentralized_and_g_com_zero_divergence() {
    let opp_cfg = PeerComparisonConfig {
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
        star_gain: 0.15,
        g_com: 0.05,
        g_com_low: 0.005,
        g_diff: 0.15,
        relay_delay_steps: 1,
        relay_drop_rate: 0.02,
    };
    let opp = peer_topology_comparison(&opp_cfg, 23);
    assert!(opp.star.spread > 700e-6);
    assert!(opp.centralized_lipsync.spread < 15e-6);
    assert!(opp.centralized_lowlatency.spread < 15e-6);
    assert!(opp.decentralized_lipsync.spread < 15e-6);
    assert!(opp.decentralized_lowlatency.spread < 15e-6);

    // Under lossy step-0 relay (`25%` drop), `decentralized_unbounded_consensus`
    // (`g_com = 0`) locks receivers onto different common-mode baselines on
    // affected seeds (permanent spread > 100 us), while `decentralized_lowlatency`
    // (`g_com_low = 0.005`) keeps spread < 20 us on every seed.
    let lossy_opp = PeerComparisonConfig {
        steps: 3_000,
        relay_drop_rate: 0.25,
        ..opp_cfg
    };
    let mut worst_dec_g0 = 0.0_f64;
    for seed in 1_u64..=12 {
        let r = peer_topology_comparison(&lossy_opp, seed);
        worst_dec_g0 = worst_dec_g0.max(r.decentralized_unbounded_consensus.spread);
        assert!(
            r.decentralized_lowlatency.spread < 25e-6,
            "seed {seed}: bounded g_com_low must stay tight, got {:.3e}",
            r.decentralized_lowlatency.spread
        );
    }
    assert!(
        worst_dec_g0 > 100e-6,
        "decentralized g_com=0 must exhibit permanent spread divergence on step-0 relay loss; worst={worst_dec_g0:.3e}"
    );

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
            star_gain: 0.15,
            g_com: 0.05,
            g_com_low: 0.005,
            g_diff: 0.15,
            relay_delay_steps: 1,
            relay_drop_rate: 0.02,
        },
        23,
    );
    assert!(same.star.spread < 80e-6);
    assert!(same.star.error > 700e-6);
    assert!(same.decentralized_lipsync.spread * 3.0 < same.star.spread);
}

/// Verifies bounded low-latency peer control (centralized and decentralized),
/// tuned star comparison, AND directly catches double prediction of star
/// filters on bidirectional edges by asserting exact equivalence against a
/// single halved-variance star edge under zero measurement noise.
#[test]
fn peer_bounded_lowlatency_and_bidirectional_edge_single_prediction() {
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
            star_gain: 0.15,
            g_com: 0.10,
            g_com_low: 0.005,
            g_diff: 0.15,
            relay_delay_steps: 1,
            relay_drop_rate: 0.02,
        },
        29,
    );
    assert!(
        wander.centralized_lowlatency.speed_change < wander.centralized_lipsync.speed_change * 0.65
    );
    assert!(
        wander.decentralized_lowlatency.speed_change
            < wander.decentralized_lipsync.speed_change * 0.65
    );
    assert!(
        wander.decentralized_lowlatency.error * 10.0
            < wander.decentralized_unbounded_consensus.error
    );
}

/// Catches predicting a star filter twice on links probed in both directions:
/// two opposite-direction edges of variance `2v` must match a single edge of
/// variance `v` without `2 * freq * dt` double-prediction drift.
#[test]
fn bidirectional_star_edges_do_not_double_predict() {
    let v = (10e-3_f64).powi(2);
    let bidir = peer_topology_comparison(
        &PeerComparisonConfig {
            receivers: 2,
            peer_edges: vec![
                GraphEdge {
                    src: 0,
                    dst: 1,
                    variance: 2.0 * v,
                    bias: 0.0,
                },
                GraphEdge {
                    src: 1,
                    dst: 0,
                    variance: 2.0 * v,
                    bias: 0.0,
                },
                GraphEdge {
                    src: 0,
                    dst: 2,
                    variance: v,
                    bias: 0.0,
                },
            ],
            sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            interval: 1.0,
            steps: 2_000,
            star_gain: 0.15,
            g_com: 0.05,
            g_com_low: 0.005,
            g_diff: 0.15,
            relay_delay_steps: 1,
            relay_drop_rate: 0.0,
        },
        55,
    );
    let single = peer_topology_comparison(
        &PeerComparisonConfig {
            receivers: 2,
            peer_edges: vec![
                GraphEdge {
                    src: 0,
                    dst: 1,
                    variance: v,
                    bias: 0.0,
                },
                GraphEdge {
                    src: 0,
                    dst: 2,
                    variance: v,
                    bias: 0.0,
                },
            ],
            sender_noise: FrequencyNoise::CONSUMER_QUARTZ,
            receiver_noise: FrequencyNoise::CONSUMER_QUARTZ,
            interval: 1.0,
            steps: 2_000,
            star_gain: 0.15,
            g_com: 0.05,
            g_com_low: 0.005,
            g_diff: 0.15,
            relay_delay_steps: 1,
            relay_drop_rate: 0.0,
        },
        55,
    );
    assert!(
        bidir.star.error < single.star.error * 1.5,
        "bidirectional edges (2v each) must match single edge (v) without double-prediction drift: bidir={:.3e} vs single={:.3e}",
        bidir.star.error,
        single.star.error
    );
}
