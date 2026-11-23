# The theorems

Every theorem indexed below is in `lean/Unisono` and checked in
`lean/Unisono/Audit.lean`, which pins the axioms each proof depends on via
`#guard_msgs` and `#print axioms`. Every theorem depends solely on Lean's three
standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`). The
build fails if any proof contains `sorry` or introduces an unexpected axiom.

The proofs fall into three groups:

1. **Formal specification, models, topologies, and fundamental limits**
   (`Unisono.Spec.*`, plus the abstract reference solution
   `Unisono.Solutions.FixedDelay`): definitions of the problem, the five
   approved world models, communication topologies, and impossibility and
   separation theorems in the official framework (`docs/specification.tex`).
2. **Supplementary analytical results** (`Unisono.Model.*`,
   `Unisono.Analysis.*`): component-level and centralized/oracle analyses in
   simplified settings (real numbers, fixed filtrations, per-cycle quadratic
   approximations, continuous-time pause formulas). Per `PRINCIPLES.md`, these
   serve as analytical references and lower-bound benchmarks, never as
   replacements for end-to-end proofs in `Unisono.Spec`.
3. **Production core code** (`Unisono.*` and `Unisono.Solutions.Core`): proofs
   directly about the Aeneas-generated Lean translation of
   `crates/unisono-core`. The generated translation files
   (`lean/UnisonoCore/{Types,Funs}.lean`) are regenerated on demand by
   `tools/extract.sh` (`just translate` / `just prove`), are not checked into
   git, and are cross-checked against Rust execution on concrete inputs by
   `just translation-check` (`crates/translation-check` and
   `lean/TranslationCheck.lean`).

"Returns for every input" below means totality: the function terminates without
integer overflow, out-of-bounds indexing, or panic for every state and every
argument, whether or not reachable in a run.

## 1. Formal specification, models, topologies, and fundamental limits

### 1.1 Specification checks, run mechanics, and fixed-latency bounds (`Spec.Checks`, `Spec.Run`, `Spec.AtLatency`)

| Theorem | What it says |
|---|---|
| `Spec.speed_eq` | On any continuous step, playback speed equals one minus the rate of change of latency. |
| `Spec.missedAt_none`, `missedAt_after`, `missedAt_continues`, `missedAt_skip`, `missedAt_repeat`, `missedAt_after_gap`, `missedAt_resume` | Missed-sample counting agrees with the specification in every case: non-source output counts 1, continuous playback counts 0, skipping or repeating `J` frames counts `J`, and resuming or continuing after `g` non-source outputs adds no extra count beyond `g`. |
| `Spec.discontinuities_gap`, `discontinuityAt_jump` | A playback gap counts one discontinuity regardless of length, and a position jump counts one. |
| `Spec.roughnessCost_across` | Across a break, roughness equals the minimum cost of a linear speed change over the break duration, so breaks cannot hide speed changes. |
| `Spec.sum_pairs_eq`, `syncCost_one_off`, `latencyCost_unplayed` | When all `R` speakers play a frame, pairwise synchronization cost equals the variance of play times; one speaker off by `Δ` adds `(R - 1) Δ² / R²`; muting speaker `r` (with latency `ℓ_r`) lowers latency cost by `ℓ_r / R`. |
| `Spec.Solution.eventTime_le_succ`, `Solution.decided`, `Solution.eventTime_mono` | The run processes events in chronological order, and any non-Zeno run decides what every output sample of every speaker plays. |
| `Spec.Solution.held_mono`, `frames_arrive`, `State.sendAll_delivered`, `State.handle_delivered`, `Solution.sent_inFlight`, `copy_inFlight`, `mem_inFlight_succ` | Held frame sets are monotonic; delivered sends enter transit and arrive at their destination before any strictly later step. |
| `Spec.Solution.views_succ`, `views_append`, `handled_before`, `handled_of_mem_views`, `handled_time`, `handled_of_views_eq`, `exists_handed_step`, `askedNext_mono`, `askedNext_succ`, `exists_asked_step`, `plays_of_asked_step`, `handled_of_asked`, `handled_asked`, `no_request_between`, `Solution.progress` | Structural run invariants connecting host views, handled events, playback-block requests, playback decisions, and sufficient conditions for non-Zeno progress. |
| `Spec.longRun_le`, `missed_eq_zero`, `discontinuities_eq_zero`, `meanLatency_le`, `sync_le`, `tracking_le` | Linear accrual bounds long-run averages; any playback within `E` of fixed latency `L` from some sample onward has zero long-run missed samples and discontinuities, mean latency at most `L + E + δ`, synchronization cost at most `(E + δ)²`, and tracking cost at most `(D + E + δ)²`, where `δ` bounds output sample spacing and `D` bounds `|L* - L|` for target latency `L*`. |

### 1.2 Approved world models (`Spec.Models.{Ideal,Bounded,Delays,SecondOrder,StochasticWorld}`)

| Theorem | Model | What it says |
|---|---|---|
| `Spec.IdealConstantWorld.withinBounds`, `IdealConstantWorld.example_holds` | `IdealConstantWorld` | Every ideal constant world satisfies `World.WithinBounds` for its tight bounds; both symmetric and asymmetric subclasses are non-empty. |
| `Spec.Bounds.example_within`, `offset_error`, `offset_drift`, `offset_drift_abs`, `Clock.read_sub_near` | `BoundedWorld` (`Bounds`) | `BoundedWorld` is non-empty; a round-trip offset estimate errs by at most half the worst delay asymmetry plus clock rate-error bound `ε_C` times mean maximum delay; two clocks drift apart by at most `2 ε_C` per second. |
| `Spec.CaptureDevice.capture_sub_mem`, `PlaybackDevice.out_sub_mem`, `World.captured_sub_mem`, `World.exists_captured_eq`, `World.sub_le_of_captured`, `World.captured_lipschitz`, `CaptureDevice.handed_unbounded`, `PlaybackDevice.asked_unbounded` | `BoundedWorld` (`Bounds`) | For nominal sample rate `ρ` and device rate-error bound `ε_D`, device frame and sample spacing stays within `(1 ± ε_D) / ρ`; `World.captured` is bi-Lipschitz and surjective; capture handoffs and playback requests advance past every true time. |
| `Spec.Link.deliver_after`, `StationaryNetworkDisturbances.example_holds` | `StationaryNetworkDisturbances` | Positive baseline and nonnegative per-packet jitter ensure every delivered message arrives strictly after send time; the model class is non-empty. |
| `Spec.ClockNoise.density_nonneg`, `secondDifferenceCovariance_integrableOn`, `secondDifferenceCovariance_diag_le`, `SecondOrderMoments.example_holds` | `SecondOrderMoments` | The band-limited IEEE Std 1139-2008 power-law one-sided frequency-noise spectral density `S(f)` is nonnegative and yields convergent phase second-difference covariances bounded by `4 τ² ∫ S(f) df` at every lag `τ`; a three-host witness with nonzero uncorrelated per-packet link jitter proves satisfiability. |
| `Spec.StochasticWorld.Holds.network_random`, `StochasticWorld.example_holds` | `StochasticWorld` | Every composite stochastic world satisfies `StationaryNetworkDisturbances.Random`; the composite model class is non-empty. |

### 1.3 Communication topologies, modal split, and shift invariance (`Spec.Topologies`)

| Theorem | What it says |
|---|---|
| `Spec.modal_sq_split`, `World.syncCost_eq_var`, `World.trackingCost_eq_sync_add_mean`, `World.weighted_frame_modal_split` | Exact orthogonal decomposition of quadratic frame objectives: synchronization cost `S` equals latency variance (differential mode), tracking cost `Θ` equals `S` plus squared common-mode tracking error, and a weighted sum `w_S S + w_Θ Θ` (with weights `w_S`, `w_Θ`) weights differential mode by `w_S + w_Θ` and common mode by `w_Θ`. |
| `Spec.World.roughness_linear_ramp`, `World.roughness_boundary_step`, `cyclePositionWeight_eq` | Over `M` uniform samples at nominal rate `ρ` (duration `Δt = M / ρ`), ramping speed linearly by `Δv` costs `ρ Δv² / M` roughness (whereas a boundary step costs `M` times more), converting specification position and roughness weights `(c_pos, c_rough)` to per-cycle position weight `(c_pos / c_rough) Δt⁴`. |
| `Spec.World.shiftHosts_rtt_eq`, `Solution.plays_shiftHosts`, `Solution.sync_shiftHosts_lower_bound`, `Solution.tracking_shiftHosts_lower_bound` | Shifting host timelines by a shift vector `Δ` (`Δ sender = 0`) preserves all round-trip times and, for any non-Zeno solution without cross-origin arrival collisions, leaves every host's view and playback decisions unchanged, forcing long-run lower bounds on `World.sync` and `World.tracking` across opposite shifts `±Δ`. |

### 1.4 Fundamental topology limits and Star-vs-Peer separation (`Spec.Limits`)

| Theorem | What it says |
|---|---|
| `Spec.withinSpeed_of_step_bound` | Converts a per-sample frame-advance bound `|y - x - 1| ≤ u` (`0 ≤ u < 1`) into `Solution.WithinSpeed` with bound `(2 ε_D + (1 + ε_D) u) / (1 - ε_D)` in any `BoundedWorld` with device rate-error bound `ε_D`. |
| `Spec.fixedDelay_isStar`, `FixedDelay.noCrossOriginCollision_sepBaseWorld` | The abstract `FixedDelay.solution` is a star solution (`IsStar`) and has no cross-origin arrival collisions on `sepBaseWorld`. |
| `Spec.star_states_eq_of_star_links_eq` | Any star solution (`Solution.IsStar`) has identical run states and playback decisions when receiver-to-receiver links are modified. |
| `Spec.star_sync_lower_bound_with_symmetric_peers` | On the world pair `(w⁺, w⁻) = (shiftStarKeepPeers w Δ, shiftStarKeepPeers w (-Δ))`, where star links carry opposite asymmetries `±Δ` and direct peer links remain unmodified (including arbitrarily fast, symmetric peer links), every qualifying non-Zeno star solution suffers `max (w⁺.sync) (w⁻.sync) ≥ Var_r (Δ (host r))`, the variance across speakers `r` of their host shifts. |
| `Spec.peer_probe_recovers_exact_offset` | On a symmetric constant-delay peer link in a shifted ideal world with host clock offsets `c₁`, `c₂` and shifts `Δ h₁`, `Δ h₂`, a four-timestamp peer exchange recovers the exact relative shifted clock offset `(c₂ - Δ h₂) - (c₁ - Δ h₁)`. |
| `Spec.ForwardStar.isStar`, `ForwardStar.noCrossOriginCollision`, `ForwardStar.progress`, `ForwardStar.sync_eq` | Tightness witness on `(sepWorldPlus A, sepWorldMinus A)` for any asymmetry parameter `A ∈ (0, 1/4)` (both in `IdealConstantWorld.Asymmetric`): `ForwardStar.solution` is a qualifying star solution attaining `sync = A²` in both worlds. |
| `Spec.PeerSync.usesGraph`, `PeerSync.progress`, `PeerSync.sync_eq_zero`, `peer_beats_star_asymmetry_bound` | Two-sided separation directly on `Unisono.Spec`: for any asymmetry parameter `A ∈ (0, 1/4)`, every qualifying star solution suffers `max sync ≥ A²`, whereas `PeerSync.solution` uses only star links plus the symmetric peer link `1 ↔ 2`, is non-Zeno, plays every frame `n ≥ 2`, and achieves `sync = 0` in both `sepWorldPlus A` and `sepWorldMinus A`. |

### 1.5 Abstract fixed-delay reference solution (`Solutions.FixedDelay`)

An abstract, real-valued reference `Unisono.Spec.Solution` (not the Rust
production core) verified end to end under `BoundedWorld`:

| Theorem | What it says |
|---|---|
| `Solutions.FixedDelay.solution_append`, `block_received`, `block_latest`, `offset_received`, `offset_latest`, `asked_request`, `last_after_request`, `last_none`, `answered_query`, `answered_latest`, `positions_fold`, `lookup_chosen`, `positions_block`, `lastChosen_block`, `chosen_succ`, `chosen_isSome` | Host memory and block-position recursion invariants of the abstract fixed-delay baseline. |
| `Solutions.FixedDelay.block_arrives`, `origin_inFlight`, `replicate_copies`, `query_inFlight`, `answer_inFlight`, `query_answered`, `answer_reaches`, `offset_sample`, `block_handled`, `block_memory`, `offset_recent`, `exists_block_of_frame`, `frame_held`, `playable_of_captured` | Message delivery, query-answer timing, and frame playability under `BoundedWorld` when message repetition exceeds the consecutive-loss bound `lossRun`. |
| `Solutions.FixedDelay.progress`, `asked_gap`, `handed_gap`, `request_step`, `last_at_next_request`, `advance_tracks`, `advance_converges`, `target_time_error`, `captured_nominal`, `captured_target`, `target_band`, `exists_last_below`, `exists_block_of_sample`, `trajectory_step`, `plays_eq_chosen`, `targetError_mono`, `late_targets` | Non-Zeno progress, bounded inter-event gaps, clock-estimate freshness, and slew convergence into the target latency band. |
| `Solutions.FixedDelay.speaker_at_latency`, `plays_at_latency`, `guarantees`, `plays_at_latency_example` | From some output sample onward, every speaker plays continuously within `latencyError` of `L`, yielding zero long-run missed samples and discontinuities and explicit bounds on mean latency, synchronization, and tracking; `plays_at_latency_example` exhibits a two-host world meeting all hypotheses. |

## 2. Supplementary analytical results

The theorems in this section operate in simplified component or
centralized/oracle models (explicitly named in each subsection) rather than
directly on `Unisono.Spec.Solution` and `Unisono.Spec.Objectives`.

### 2.1 Component clock, stream, single-mode regulation, and level models (`Model.*`)

| Theorem | Module | What it says |
|---|---|---|
| `Model.Exchange.error_bound` | `Model.Exchange` | A bidirectional packet exchange determines clock offset up to half the minimum-delay asymmetry plus half the excess delays. |
| `Model.SupportLine.highest`, `estimate_isGreatest`, `excess_le`, `excess_near`, `error_at_centre`, `error_ahead` | `Model.SupportLine` | The lower-hull support line through two samples straddling the mean time is the highest line under all samples, minimizes total excess (maximum likelihood for independent exponential delays, up to rounding), and has explicit error bounds independent of delayed outliers. |
| `Model.LineFit.cost_le`, `error_bound`, `schedule_invariant` | `Model.LineFit` | Weighted least-squares line optimality, error bound from point errors, and invariance of synchronization to sender-clock offset and rate. |
| `Model.Stream.group_misses_iff`, `sum_sq_errors`, `dueTime_position`, `groupNeed_errors`, `group_misses_errors` | `Model.Stream` | Fleet miss condition against group need, squared timing-error decomposition, packet-header due-position formula, and perturbation bound on group need under bounded timing errors. |
| `Model.Regulation.cost_add_value`, `total_cost_ge`, `total_cost_law`, `value_step`, `distance_from_rest`, `weight_gainFor`, `gain_unique`, `at_limit`, `next_shift` | `Model.Regulation` | Deterministic dynamic-programming optimality, geometric contraction, closed-form unique weight-to-gain relation, and limit behavior for the single-mode quadratic pace regulator. |
| `Model.RegulationRandom.mean_cost_sum`, `mean_cost_law_le`, `mean_value_law_le`, `mean_cost_rate`, `mean_square_split`, `unforeseen_revision`, `distance_step`, `unforeseen_pace` | `Model.RegulationRandom` | Stochastic separation and long-run optimality of the linear regulation law under arbitrary martingale (unforeseen) schedule revisions. |
| `Model.Gains.gains_close`, `gains_of_integers`, `law_close`, `planned`, `cost_of_distance` | `Model.Gains` | Exact closeness bounds between integer floor-rounded gains/planned cycle reads and the real-valued regulation law, plus quadratic cost of deviation from the law. |
| `Model.Level.measure_largest`, `measure_largest_le`, `integral_predictive`, `volume_missed`, `missed_le`, `missed_ge`, `volume_lasts`, `move_pays_iff` | `Model.Level` | After `N` observed stretches, exchangeable next-stretch exceedance probability is at most `1 / (N + 1)`; predictive cost integral, pause-duration missed-time bounds, and break-even criterion for changing playout level. |

### 2.2 Multi-speaker modal control (`Analysis.ModalControl`)

*Boundary:* discrete-time per-cycle linear-quadratic approximation with uniform
aligned cycles `Δt`, unconstrained real-valued per-cycle reads (omitting
continuity, speed bounds, and data availability), assumed martingale expected
increments (not derived from `SecondOrderMoments`), and a centralized shared
filtration `ℱ`. Centralized optimality theorems serve as lower-bound benchmarks
that decentralized nodes cannot beat.

| Theorem | What it says |
|---|---|
| `Analysis.weight_gainForWeight`, `gainForWeight_unique` | Exact inversion of `Regulation.weight` on `(0, 1)`: `gainForWeight c = gainFor (c^{1/4})` is the unique gain with position weight `c`. |
| `Analysis.single_cost_split`, `single_law_optimal`, `single_law_unique_ae` | Under a fixed filtration `ℱ` and martingale expected increments, applying `Regulation.law g` to the conditional-mean state uniquely (almost everywhere, a.e.) minimizes finite-horizon expected cost plus terminal value. |
| `Analysis.multiCycleCost_modal_split`, `multi_lipsync_optimal`, `multi_lipsync_unique_ae`, `multi_lipsync_cost_rate`, `multi_lipsync_law_cost_le` | Centralized full-information lip-sync benchmark: orthogonal modal decomposition into common mode (tracking weight `cΘ`) and differential mode (weight `cS + cΘ`, where `cS` is the synchronization weight), with two-gain `modalRead` as the a.e. unique finite-horizon and long-run minimizer. |
| `Analysis.multi_lowlatency_optimal`, `multi_lowlatency_unique_ae` | Centralized benchmark when tracking weight `cΘ = 0` and mean-latency/missed-sample costs are omitted: `consensusRead` holds mean pace constant and applies `law gDiff` (with differential-mode gain `gDiff`) to differential mode (requires an additional small common-mode loop in practice to prevent drift). |
| `Analysis.decentralized_star_cost_eq`, `symmetric_star_cost_split`, `decentralized_star_uncorrelated_optimal`, `consensus_one_hot_var` | Cost decomposition for symmetric pure-star policies across `R` speakers into shared common vs. private uncorrelated components (weighting private errors by `((R - 1) / R) cS + cΘ`), optimality when cross-receiver errors are uncorrelated, and zero-mean projection norm `((R - 1) / R) Δ²` of a single-speaker step `Δ`. |

### 2.3 Spectral factorization and steady-state Riccati algebra (`Analysis.Spectral`)

*Boundary:* standalone frequency-domain and scalar random-walk algebraic
identities. `clockProcessCov_nonneg` proves positive semidefiniteness of the
2×2 state-space covariance formula rather than constructing a process under
`SecondOrderMoments`.

| Theorem | What it says |
|---|---|
| `Analysis.weight_factor`, `step_step`, `butterworth` | Discrete unit-circle spectral factorization (in unit-circle variable `z`) of `weight g + |1 - z|⁴` matching the closed-loop characteristic polynomial of `Regulation.step g`, and continuous-time second-order Butterworth factorization with damping ratio `ζ = 1 / √2`. |
| `Analysis.filterRoot_eq`, `filterRoot_unique`, `estimate_factor`, `riccati_fixed`, `posterior_variance`, `revision_variance` | Unique root `a ∈ (0, 1)` of `a² - (2 + q / r) a + 1 = 0` (for process variance `q` and measurement variance `r`) giving the steady-state scalar random-walk Riccati fixed point, Kalman gain `1 - a`, posterior variance `r (1 - a)`, and squared innovation-revision variance `q`. |
| `Analysis.clockProcessCov_nonneg` | The 2×2 two-state oscillator process-noise covariance matrix `Q(dt)` parameterized by `ClockNoise` white and random-walk frequency-noise variance rates `(q₀, q₂)` is positive semidefinite for every time interval `dt ≥ 0`. |

### 2.4 Star and peer graph clock estimation (`Analysis.Estimation`)

*Boundary:* static linear algebraic and square-integrable (`L²`) random-variable
identities on fixed measurement graphs. `thomson_blue_optimal` assumes
zero-mean, mutually uncorrelated edge errors (shared wireless media can
correlate links, and static asymmetries induce bias `graph_estimator_bias`).

| Theorem | What it says |
|---|---|
| `Analysis.star_pair_error_same`, `star_pair_error_heterogeneous`, `disciplined_schedule_error`, `residual_variance_sub`, `residual_variance_L2` | Sender-clock wander cancels across receivers sharing one linear filter, leaks under heterogeneous filters, is reduced by an index-aligned common schedule correction, and inverse-variance residuals have strictly smaller second moment `σ_r² - V_bc` (raw error variance `σ_r²` minus broadcast variance `V_bc`) under pairwise-uncorrelated `L²` errors. |
| `Analysis.linear_unbiased_iff_unitFlow`, `graph_estimator_bias`, `thomson_blue_optimal` | On any directed measurement graph, linear unbiasedness for phase difference `φ(t) - φ(s)` between nodes `s` and `t` holds if and only if weights `f_e` form a unit `s → t` flow; static edge biases `α_e` yield exact bias `∑ f_e α_e`; the electrical (Laplacian) flow is the unique best linear unbiased estimator (BLUE), minimizing `∑ var_e f_e²` (for edge error variances `var_e`) and attaining the effective resistance. |
| `Analysis.star_effective_resistance`, `complete_graph_effective_resistance`, `complete_graph_equal_budget`, `wifi_sender_wired_peers_resistance`, `triangle_blue_bias` | Closed-form effective resistance on star graphs (`v₁ + v₂` for star edge variances `v₁, v₂`), complete `N`-node peer graphs `K_N` (`2 v / N` at common edge variance `v`, or `v` at equal total probe budget), and two-speaker wireless-sender/wired-peer triangles (`2 v_W v_P / (2 v_W + v_P)` for wireless variance `v_W` and peer variance `v_P`), plus exact triangle BLUE bias under link asymmetries. |

### 2.5 Continuous-time Campbell pause margin (`Analysis.Level`)

*Boundary:* standalone continuous-time Campbell-formula model of link pauses
only (not outages), measuring missed audio in seconds per second rather than
discrete missed samples, and omitting block boundaries, resampler lookahead,
background jitter tails, and overlapping pauses.

| Theorem | What it says |
|---|---|
| `Analysis.margin_best_missed`, `margin_best_tracking` | Global optimality quantile conditions for playout margin `m` under mean-latency plus missed-fraction cost (and with quadratic target-margin tracking). |
| `Analysis.fleet_average_missed_cost` | Linearity of Campbell missed-audio cost over the fleet-averaged pause intensity measure. |
| `Analysis.margin_best_exponential_with_clicks`, `discontinuity_nonconvex_example` | Closed-form global optimum `m* = max 0 (h̄ log (λ (w_M + w_D / h̄) / w_Λ))` for a shared exponential pause distribution (mean pause duration `h̄`, pause arrival rate `λ`, and weights `w_M` for missed audio, `w_D` for discontinuities, and `w_Λ` for mean latency), and an atomic-pause counterexample showing discontinuity penalties can break convexity in general. |

## 3. Production core code (`crates/unisono-core`)

Every theorem below targets the Aeneas-translated Rust functions in
`lean/UnisonoCore`.

### 3.1 Fixed-point arithmetic (`Fixed`)

| Theorem | What it says |
|---|---|
| `Fixed.saturate_spec`, `mul_shift_spec`, `div_floor_spec`, `div_floor_wide_spec`, `rem_euclid_wide_spec`, `root_spec` | Exact integer specifications for 64-bit saturation, rounded fixed-point product, floor division on 64-bit (`i64`) and 128-bit (`i128`) signed integers, Euclidean remainder (`none` modulo zero), and integer square root. |
| `Fixed.saturating_mul_i128_spec`, `saturating_mul_i64_spec`, `scale_div_pow2_spec` | Exact clamped specifications for saturating 128-bit and 64-bit multiplication and exact overflow-safe `(num * 2^min(shift, 64)) / den` floor division (returning `0` when `den ≤ 0`). |

### 3.2 Version 2 wire packets (`Packet`)

| Theorem | What it says |
|---|---|
| `Packet.read_spec`, `write_spec`, `kind_spec` | Little-endian multi-byte reads and writes (up to 8 bytes) and 6-byte magic/version-2/kind header inspection. |
| `Packet.payload_spec`, `validate_audio_spec`, `parse_audio_valid`, `write_audio_spec`, `audio_roundtrip`, `write_report_spec`, `report_roundtrip`, `write_echo_spec`, `echo_roundtrip`, `write_request_spec`, `request_roundtrip` | Exact serialized layouts, zero-padded reports, version 2 40-byte `Echo` (carrying both `arrival` and `departure`), semantic header validation, and exact write-then-parse round-trips for `Audio`, `Report`, `Echo`, and `Request`. |
| `Packet.write_peer_probe_spec`, `peer_probe_roundtrip`, `write_peer_echo_spec`, `peer_echo_roundtrip` | Exact serialized layouts and write-then-parse round-trips for 32-byte `PeerProbe` and 48-byte `PeerEcho`. |
| `Packet.parse_audio_kind`, `parse_report_kind`, `parse_echo_kind`, `parse_request_kind`, `parse_peer_probe_kind`, `parse_peer_echo_kind`, `parse_peer_relay_kind` | Every packet kind tag dispatches exclusively to its matching parser (no packet is accepted as two kinds). |
| `Packet.parse_audio_total`, `write_audio_total`, `parse_report_total`, `write_report_total`, `parse_echo_total`, `write_echo_total`, `parse_request_total`, `write_request_total`, `parse_needs_total`, `write_needs_total`, `parse_peer_probe_total`, `write_peer_probe_total`, `parse_peer_echo_total`, `write_peer_echo_total`, `parse_peer_relay_total`, `write_peer_relay_total` | All version 2 packet parsers and serializers (including `PeerProbe`, `PeerEcho`, `PeerRelay`, and report `Recent` needs) return for every input: no network bytes can crash or trap a parser. |

### 3.3 Legacy lower-hull clock estimator (`Relation`, `Estimate`)

Theorems in both `Unisono.Relation` and `Unisono.Estimate` live in the
`Unisono.Relation` namespace:

| Theorem | What it says |
|---|---|
| `Relation.fit_spec`, `mean_time_spec`, `anchor_near_mean`, `through_best`, `through_excess` | `fit` changes only the line, stores a slope-limited support line under all kept samples through two samples straddling the rounded mean time, and matches the optimal support line of Section 2.1 in real numbers. |
| `Relation.side_spec`, `is_under_spec`, `bridge_spec`, `slope_within_spec`, `limited_spec`, `eval_spec` | Exact specifications for point-line side test, lower-envelope test, support bridge, slope clamping, and clamped line evaluation. |
| `Relation.put_spec`, `drop_oldest_spec`, `forget_before_spec`, `new_spec`, `remember_spec`, `reset_window_spec`, `consider_spec`, `overtaken_spec`, `append_spec`, `keep_spec`, `end_window_spec`, `observe_spec`, `observe_later`, `observe_in_order`, `observe_total`, `end_window_total` | Window management, kept-count bound `len ≤ M` (window capacity `M`), rejection of overtaken packets, acceptance of all non-overtaken packets, and totality for all inputs. |

### 3.4 Audio device clock regressor (`Device`)

| Theorem | What it says |
|---|---|
| `Device.fit_spec`, `when_spec`, `when_cycle_spec`, `beyondZ_eq_floor_lineFit`, `beyondSlopeQ16Z_eq_floor_lineFit` | Exact non-wrapping regression sums, frame-time and cycle-duration evaluation, and exact agreement with the floor-rounded least-squares line of Section 2.1. |
| `Device.observe_spec`, `observe_after_aside`, `step_spec`, `push_spec`, `start_spec`, `shift_spec`, `observe_total`, `when_total` | Outlier setting-aside (at most one report aside in a row), window insertion/reset/shift invariants, and totality. |

### 3.5 Frame presence bitmap (`Presence`)

| Theorem | What it says |
|---|---|
| `Presence.mark_spec`, `mark_frame_spec`, `countOf_total`, `Arrived.comm`, `Arrived.again` | Exact frame-membership update, outcome counting, order-commutativity of arrivals, and idempotence of duplicate packets. |
| `Presence.advance_spec`, `run_spec`, `gap_spec`, `held_spec`, `new_spec`, `restart_spec`, `width_spec`, `covers_spec` | Playhead advancement, contiguous held/missing run lengths, capacity width, and timeline restart. |

### 3.6 Four-timestamp NTP exchanges and sliding minimum-RTT selection (`MinRtt`)

| Theorem | What it says |
|---|---|
| `MinRtt.ntp_exchange_spec` | Exact integer specification of a four-timestamp Network Time Protocol (NTP) exchange (`ntp_exchange`, given client transmit `T1`, responder receive `T2`, responder transmit `T3`, and client receive `T4`): rejects negative responder processing time `T3 - T2 < 0` or negative round-trip time (RTT) `(T4 - T1) - (T3 - T2) < 0`, and otherwise returns clamped nonnegative `rtt_ns`, exact `offset_ns = floor(((T2 - T1) + (T3 - T4)) / 2)`, and `midpoint_ns`. |
| `MinRtt.new_spec`, `reset_spec`, `observe_spec`, `path_ns_spec`, `variance_ns2_spec` | Totality, ring-length invariant `len ≤ W` (sliding window capacity `W`), nonnegative `path_ns`, variance-floor enforcement on every emitted measurement, and strict monotonic deduplication of emitted exchange identifiers. |

### 3.7 Two-state fixed-point Kalman filter (`Kalman`)

| Theorem | What it says |
|---|---|
| `Kalman.enforce_psd_spec`, `new_spec`, `anchor_spec`, `predict_psd`, `update_psd`, `to_line_spec` | Totality, 2×2 covariance positive semidefiniteness (diagonal entries `p00 ≥ 0`, `p11 ≥ 0`, off-diagonal `p01² ≤ p00 * p11`) preserved across initialization, anchoring, prediction, and Joseph-form update, and valid `Line` export (`run = LINE_RUN > 0`). |
| `Kalman.predict_zero_fixed_point`, `update_zero_innovation_fixed_point`, `to_line_zero_fixed_point` | Zero-residual, zero-frequency anchored filter state `(base_offset_ns, 0, 0)` is an exact fixed point of `predict` and zero-innovation `update`, exporting the exact constant offset line. |

### 3.8 Fixed-point graph-Laplacian BLUE solver (`Blue`)

| Theorem | What it says |
|---|---|
| `Blue.solve_ldlt_total`, `solve_ldlt_zero_rhs` | The square-root-free lower-diagonal-transpose (`LDL^T`) triangular solver returns for every input and maps an all-zero right-hand side to an exact all-zero solution. |
| `Blue.solve_blue_spec` | `solve_blue` returns for every input, caps `active_count ≤ MAX_PEERS`, clamps positive output variances into `[1, MAX_OUT_VAR_NS2]`, and sets `self_diff_var_ns2 = 0` when `active_count = 1`. |
| `Blue.solve_blue_single_edge_star` | On a single-edge two-host graph `(0 → 1)` with measured offset `d` and variance `v`, `solve_blue` recovers the exact offset `-d`, `self_diff_offset_ns = 0`, and `common_var_ns2 = min(v, MAX_OUT_VAR_NS2)`. |

### 3.9 Playback regulator and timing (`Player`, `Gains`, `Due`)

`Unisono.Gains` defines `Player.gain_spec`, `Player.gains_spec`, and
`Player.regulate_spec` inside the `Unisono.Player` namespace:

| Theorem | What it says |
|---|---|
| `Player.cycle_spec`, `cycle_step_small`, `step_clamped_spec`, `gain_spec`, `gains_spec`, `regulate_spec` | Single-mode `Player` cycle totality, resampler pace-limit safety (`|offset| < 2^56`), exact cycle-gain calculation, and closeness of computed gains and planned cycle reads to Section 2.1's regulation law. |
| `Player.modal_cycle_spec`, `modal_cycle_step_small`, `modal_star_matches_player` | `ModalPlayer.cycle` totality, preservation of regulation settings, pace-limit safety (`|offset| ≤ reachOf limit < 2^56`), and exact Star equivalence: when `peer_active = false` and `was_peer = false`, `ModalPlayer.cycle` produces the identical `Plan` and playback state as single-mode `Player.cycle` at `star_gain`. |
| `Due.due_spec`, `Due.dueUnits_eq_floor`, `Player.sender_time_total`, `due_total`, `position_units_total`, `position_from_units_total`, `step_units_total`, `step_new_total`, `position_advance_total`, `step_from_parts_per_billion_total` | Exact formula and validity domain of `timing::due` (rounded down to `2⁻³²` frame), and totality of all time, position, and step conversions. |

### 3.10 Unified Peer/Star synchronization engine (`Sync`)

| Theorem | What it says |
|---|---|
| `Sync.new_total`, `add_peer_total`, `on_sender_echo_total`, `next_peer_probe_total`, `on_peer_echo_total`, `build_relay_total`, `on_peer_relay_total`, `step_total` | Every public method of `Sync` returns for every state and input. |
| `Sync.on_peer_probe_allowlist` | `Sync.on_peer_probe` replies with `some PeerEcho` only when stream and target match and `probe.prober` is a configured peer in the static peer table; unknown senders always get `none`. |
| `Sync.publish_star_spec`, `zero_peers_no_peer_traffic`, `step_zero_peers_star` | With `peer_count = 0`, `Sync` emits zero peer probes or relays, rejects incoming peer probes and relays, and `Sync.step` always publishes a Star snapshot (`peer_active = false`, `active_peers = 0`, `diff_var_ns2 = 0`, `fleet_line = ZERO_LINE`, `common_line = sender_filter.to_line`). |

### 3.11 Receiver state machine (`Receiver`)

| Theorem | What it says |
|---|---|
| `Receiver.packet_spec`, `follows_after_silence`, `late_run_is_short`, `restart_stores`, `adopt_spec`, `keep_newest_spec`, `new_spec` | Timeline adoption, silence-timeout recovery, late-packet restart, and clock-identifier reset handling (preserving path state on the same clock, clearing it on a new clock). |
| `Receiver.wrong_stream_packet_noop`, `wrong_stream_echo_noop`, `single_stray_timeline_noop` | Packets of another stream and a single stray packet of another timeline leave playback, schedule, clock estimate, path delay, answers, and departures unchanged. |
| `Receiver.take_spec`, `take_idle`, `skip_spec`, `cycle_spec`, `due_at_total`, `echo_spec`, `report_spec`, `reported_spec` | Monotonic playhead, contiguous held/missing frame runs, cycle-planning totality, and isolation of path-delay updates from timeline and frame storage. |

### 3.12 Sender state machine (`Sender`)

| Theorem | What it says |
|---|---|
| `Sender.packet_spec`, `current_level_spec`, `levelAt_eq_floor`, `packet_ramp_consistent`, `level_spec`, `restart_spec`, `departed_spec`, `answer_spec` | Contiguous packet numbering, exact non-accumulating ramp levels rounded down, timeline monotonicity on restart, and `Echo` generation (carrying arrival and departure) without mutating stream state. |

### 3.13 Needs, answers, and arrivals tables (`Needs`, `Answers`, `Arrivals`)

| Theorem | What it says |
|---|---|
| `Needs.new_total`, `clear_total`, `observe_total`, `newest_total`, `get_total`, `recent_total` | Stretch-need tracking returns for every input. |
| `Answers.new_total`, `observe_total`, `shortest_total`, `clear_spec` | Sliding shortest-RTT window table returns for every input, and `clear` empties every slot. |
| `Arrivals.find_spec`, `record_spec` | Departure/arrival lookup table preserves and retrieves the recorded timestamp of each sequence number. |

### 3.14 Loop round bounds (`Rounds`)

| Theorem | What it says |
|---|---|
| `Rounds.endsWithin_of_measure` | Any translated loop whose measure strictly decreases at each step terminates within that bound. |
| `Rounds.mark_rounds`, `run_rounds`, `gap_rounds`, `advance_rounds`, `clear_rounds`, `find_rounds`, `sums_rounds`, `shift_rounds` | Explicit upper bounds on loop iterations for the audio-thread presence, arrival, and device-regression loops. |

### 3.15 End-to-end production-core solution wrapper (`Unisono.Solutions.Core`)

Wraps the Aeneas-translated production core (`Sender`, `Sync`, `Receiver`,
`ModalPlayer`, and version 2 `packet` headers) directly as a
`Unisono.Spec.Solution` with strictly local observations:

| Theorem | Model / Scope | What it says |
|---|---|---|
| `Solutions.Core.usesGraph_of_peers`, `isStar_of_no_peers` | Any `World` | Every message sent by `Core.solution` respects the declared sender + peer allowlist graph; when every host's peer list is empty, `Core.solution` satisfies `Solution.IsStar`. |
| `Solutions.Core.progress`, `request_step` | `BoundedWorld` | In every world satisfying `World.WithinBounds`, the run of `Core.solution` is non-Zeno (advances past every true time) and reaches every speaker block request `(r, b)`. |
| `Solutions.Core.sync_zero_peers_inv`, `star_no_peer_messages`, `star_sync_snapshot_eq_sender_kalman`, `star_modal_player_eq_single_mode` | Any `World` | When `peers h = []`, `Sync.peer_count` stays `0`, zero `peerProbe`/`peerEcho`/`peerRelay` messages are sent, every `Sync.step` exports a Star snapshot (`peer_active = false`, `active_peers = 0`, `diff_var_ns2 = 0`), and `ModalPlayer.cycle` matches single-mode `Player.cycle` at `star_gain`. |
| `Solutions.Core.modal_cycle_full_spec`, `receiver_cycle_plan_spec`, `rcv_modal_inv`, `withinBlock_speed_bound`, `boundary_step_safe` | `BoundedWorld` | `Core.solution` preserves `use_sync = true` and regulation settings across all events; every consecutive pair inside a playback block unconditionally obeys the `World.speed` bound in every `BoundedWorld`; across adjacent non-empty blocks (without intervening `stop()` or 64-bit unsigned integer `u64::MAX` overflow, and with `jump ≥ 3`), every continuous boundary step obeys `|y - x - 1| ≤ paceBound limit`. |
| `Solutions.Core.ideal_ntp_exchange_exact`, `ideal_kalman_and_sender_time_exact`, `ideal_modal_cycle_unity`, `ideal_zero_cost_objectives` | `IdealConstantWorld` (Symmetric) | Within the 64-bit nanosecond range, `ntp_exchange` recovers exact offset and RTT, `KalmanFilter` preserves the exact zero-innovation fixed point and `SyncSnapshot.sender_time` maps local time to exact sender time, `ModalPlayer.cycle` plans exact `Step.UNITY`, and any unity-step playback trajectory at `m.targetLatency` achieves `sync = 0`, `tracking = 0`, `roughness = 0`, `missed = 0`, `discontinuities = 0`, and `meanLatency ≤ targetLatency`. |

## 4. What is not proved (Open)

1. **Noisy-network end-to-end objectives for the production core:**
   `Unisono.Solutions.Core` proves causality, communication-graph membership,
   exact Star degeneration, non-Zeno progress and request liveness under
   `BoundedWorld`, speed safety (within blocks unconditionally and across block
   boundaries under the stated non-restart/non-overflow/`jump ≥ 3` conditions),
   and exact ideal-world component and trajectory behavior. It does **not**
   prove end-to-end `Unisono.Spec.Objectives` bounds or stochastic optimality
   under noisy `BoundedWorld`, `StationaryNetworkDisturbances`,
   `SecondOrderMoments`, or `StochasticWorld`.
2. **Unused stochastic world hypotheses:** no theorem in the repository
   currently takes `SecondOrderMoments` or `StochasticWorld` as a hypothesis;
   constructing a random strictly increasing `Clock` with nonzero `ClockNoise`
   also remains open.
3. **`WithinSpeed` and `ideal_zero_cost_objectives` boundaries:**
   - Unconditional `Solution.WithinSpeed` for `Core.solution` across all block
     boundaries (including silence restarts and arbitrary `jump` settings) is
     not yet proved; `boundary_step_safe` proves the non-restart, non-overflow,
     `jump ≥ 3` boundary condition separately from `withinBlock_speed_bound`.
   - `ideal_zero_cost_objectives` takes the steady-state unity-step trajectory
     as its hypothesis; wiring the full event-driven run of `Core.solution`
     from startup lock into that steady-state trajectory on
     `IdealConstantWorld.Symmetric` remains open.
4. **Finite-precision graph BLUE error bounds:** `Blue.lean` proves totality,
   variance/count invariants, zero right-hand-side fixed point, and exact
   single-edge Star recovery (`solve_blue_single_edge_star`), but not
   finite-precision error bounds comparing integer `LDL^T` against real-valued
   `Analysis.Estimation.thomson_blue_optimal` on noisy multi-peer graphs or
   noiseless multi-edge trees.
5. **Other core gaps:** `PeerRelay` byte-level round-trip (totality and kind
   separation are proved; round-trip is covered by Rust unit tests and
   `translation-check`), lower-hull fit existence in `Relation`, cycle-step
   rounding error, and explicit loop-round counts in `Rounds.lean` for
   network-thread loops (`MinRtt`, `Kalman`, `Blue`, `Sync`, which are proved
   total in their own modules).
6. **Code outside `crates/unisono-core` (tested, not proved):** the
   floating-point adaptive latency chooser (`crates/unisono-runtime/src/level.rs`,
   whose unlinked real-valued companion is `Model.Level`), retransmission
   tracking and operating-system socket, clock, and ring-buffer runtime
   (`crates/unisono-runtime`), digital signal processing (resampling, sample
   conversion, fades, and gap concealment in `crates/unisono-dsp`), audio
   backends (`unisono-pipewire`, `unisono-alsa`), metrics, the C library, and
   the command-line program are verified by unit tests, multi-seed true-time
   simulation (`crates/unisono-sim`), Loom concurrency interleavings,
   machine-code inspection (`crates/reachable`, `crates/cycle-cost`), and
   container tests against PipeWire and Advanced Linux Sound Architecture
   (ALSA).
