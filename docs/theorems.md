# The theorems

All 751 theorems indexed below live in `lean/Unisono` and are checked in
`lean/Unisono/Audit.lean`, which pins the axioms each proof depends on via
`#guard_msgs` and `#print axioms`. Every theorem depends solely on Lean's three
standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`). The
build fails if any proof contains `sorry` or introduces an unexpected axiom.

The proofs fall into three groups:

1. **Formal specification, models, topologies, and fundamental limits**
   (`Unisono.Spec.*`, plus the abstract reference solution
   `Unisono.Solutions.FixedDelay`): definitions of the problem, the six
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

### 1.1 Specification checks, run mechanics, and fixed-latency bounds (`Spec.Checks`, `Spec.Run`, `Spec.Held`, `Spec.AtLatency`, `Spec.ExactLatency`, `Spec.MissingSamples`)

| Theorem | What it says |
|---|---|
| `Spec.speed_eq` | On any continuous step, playback speed equals one minus the rate of change of latency. |
| `Spec.missedAt_none`, `missedAt_after`, `missedAt_continues`, `missedAt_skip`, `missedAt_repeat`, `missedAt_after_gap`, `missedAt_resume` | Missed-sample counting agrees with the specification in every case: non-source output counts 1, continuous playback counts 0, skipping or repeating `J` frames counts `J`, and resuming or continuing after `g` non-source outputs adds no extra count beyond `g`. |
| `Spec.discontinuities_gap`, `discontinuityAt_jump` | A playback gap counts one discontinuity regardless of length, and a position jump counts one. |
| `Spec.roughnessCost_across` | Across a break, roughness equals the minimum cost of a linear speed change over the break duration, so breaks cannot hide speed changes. |
| `Spec.sum_pairs_eq`, `syncCost_one_off`, `latencyCost_unplayed` | When all `R` speakers play a frame, pairwise synchronization cost equals the variance of play times; one speaker off by `Δ` adds `(R - 1) Δ² / R²`; muting speaker `r` (with latency `ℓ_r`) lowers latency cost by `ℓ_r / R`. |
| `Spec.Solution.eventTime_le_succ`, `Solution.decided`, `Solution.eventTime_mono` | The run processes events in chronological order, and any non-Zeno run decides what every output sample of every speaker plays. |
| `Spec.Solution.held_mono`, `frames_arrive`, `State.sendAll_delivered`, `State.handle_delivered`, `Solution.sent_inFlight`, `copy_inFlight`, `mem_inFlight_succ` | Held frame sets are monotonic; delivered sends enter transit and arrive at their destination before any strictly later step. |
| `Spec.Solution.held_succ`, `mem_held_iff`, `received_lt_asked`, `handedNext_mono`, `earliest_of_handled_handed`, `handed_step_unique` | A host holds exactly the frames that the events in its view brought: the blocks that the capture device handed over to it and the messages that arrived. A device request is handled before a message that arrives at the same true time, so a message that some step handles arrived strictly before every request that is pending at that step or at a later step. The handover of a block is handled at one step of the run only. |
| `Spec.Solution.views_succ`, `views_append`, `handled_before`, `handled_of_mem_views`, `handled_time`, `handled_of_views_eq`, `exists_handed_step`, `askedNext_mono`, `askedNext_succ`, `exists_asked_step`, `plays_of_asked_step`, `handled_of_asked`, `handled_asked`, `no_request_between`, `Solution.progress` | Structural run invariants connecting host views, handled events, playback-block requests, playback decisions, and sufficient conditions for non-Zeno progress. |
| `Spec.longRun_le`, `missed_eq_zero`, `discontinuities_eq_zero`, `meanLatency_le`, `sync_le`, `tracking_le` | Linear accrual bounds long-run averages; any playback within `E` of fixed latency `L` from some sample onward has zero long-run missed samples and discontinuities, mean latency at most `L + E + δ`, synchronization cost at most `(E + δ)²`, and tracking cost at most `(D + E + δ)²`, where `δ` bounds output sample spacing and `D` bounds `|L* - L|` for target latency `L*`. |
| `Spec.World.PlaysAtLatencies.playsOnly`, `World.latency_eq_of_playsOnly`, `World.meanLatency_le_of_playsOnly`, `World.tracking_le_of_playsOnly`, `World.sync_le_of_playsOnly`, `nextContinuous_gt`, `World.speed_eq_one_of_playsOnly`, `World.roughnessCost_eq_zero_of_playsOnly`, `World.roughness_eq_zero_of_playsOnly` | Consider a playback in which, from some output sample on, every output sample that plays the source plays the sound captured exactly `L r` before it leaves, and an output sample may also play nothing of the source (`World.PlaysOnlyAtLatencies`), in a world whose capture times are linear in the position. Every frame that a speaker plays has latency `L r`. The long-run latency is at most the mean of the `L r`, the long-run tracking is at most the mean of `(L r - target)²`, and the long-run synchronization is at most the sum over the pairs of speakers of `(L r - L r')²`, divided by the square of the number of speakers. Every step of continuous playback has speed one, so the long-run roughness is zero. |
| `Spec.longRun_le_mul_add`, `PlaybackDevice.tsum_out_lt`, `World.accruedOutputs_eq_sum`, `World.longRun_outputs_le`, `missingAt_le_one`, `trailing_le`, `trailing_succ_none`, `trailing_succ_some`, `isSome_before_trailing`, `gapBefore_le_trailing`, `sum_gapBefore_le`, `toNat_cast_le`, `missedAt_le_of_line`, `exists_missedAt_le`, `sum_missedAt_le`, `discontinuityAt_le_of_line`, `sum_discontinuityAt_le`, `World.missed_le_of_line`, `World.discontinuities_le_of_line` | Consider a playback in which, from some output sample on, every played position of speaker `r` lies on the line `a r + c r * k` in the output sample `k`, with `0 < c r < 2`, in a world whose output samples leave without end. Playback breaks only where the next output sample plays nothing, so the long-run number of discontinuities is at most the long-run number of output samples that play nothing (`missingAt`). An output sample that plays after a gap counts at most `2 (c r - 1)` missed samples for each output sample of the gap when `c r > 1`, and none otherwise. So when `c r - 1 ≤ d` for every speaker, the long-run number of missed samples is at most `1 + 2 d` times the long-run number of output samples that play nothing. |

### 1.2 Approved world models (`Spec.Models.{Ideal,Bounded,Delays,SecondOrder,StochasticWorld,GenerativeWorld,GenerativeNoiseless,GenerativeDelivery,GenerativeRates,GenerativeCanonical,GenerativeTransfer,GenerativeReflection,GenerativeStar,GenerativeTies}`)

| Theorem | Model | What it says |
|---|---|---|
| `Spec.IdealConstantWorld.withinBounds`, `IdealConstantWorld.example_holds` | `IdealConstantWorld` | Every ideal constant world satisfies `World.WithinBounds` for its tight bounds; both symmetric and asymmetric subclasses are non-empty. |
| `Spec.Bounds.example_within`, `offset_error`, `offset_drift`, `offset_drift_abs`, `Clock.read_sub_near` | `Bounds` (`World.WithinBounds`) | `World.WithinBounds` is non-empty; a round-trip offset estimate errs by at most half the worst delay asymmetry plus clock rate-error bound `ε_C` times mean maximum delay; two clocks drift apart by at most `2 ε_C` per second. |
| `Spec.CaptureDevice.capture_sub_mem`, `PlaybackDevice.out_sub_mem`, `World.captured_sub_mem`, `World.exists_captured_eq`, `World.sub_le_of_captured`, `World.captured_lipschitz`, `CaptureDevice.handed_unbounded`, `PlaybackDevice.asked_unbounded` | `Bounds` (`World.WithinBounds`) | For nominal sample rate `ρ` and device rate-error bound `ε_D`, device frame and sample spacing stays within `(1 ± ε_D) / ρ`; `World.captured` is bi-Lipschitz and surjective; capture handoffs and playback requests advance past every true time. |
| `Spec.Link.deliver_after`, `StationaryNetworkDisturbances.example_holds` | `StationaryNetworkDisturbances` | Positive baseline and nonnegative per-packet jitter ensure every delivered message arrives strictly after send time; the model class is non-empty. |
| `Spec.ClockNoise.density_nonneg`, `secondDifferenceCovariance_integrableOn`, `secondDifferenceCovariance_diag_le`, `SecondOrderMoments.example_holds` | `SecondOrderMoments` | The band-limited IEEE Std 1139-2008 power-law one-sided frequency-noise spectral density `S(f)` is nonnegative and yields convergent phase second-difference covariances bounded by `4 τ² ∫ S(f) df` at every lag `τ`; a three-host witness with nonzero uncorrelated per-packet link jitter proves satisfiability. |
| `Spec.StochasticWorld.Holds.network_random`, `StochasticWorld.example_holds` | `StochasticWorld` | Every composite stochastic world satisfies `StationaryNetworkDisturbances.Random`; the composite model class is non-empty. |
| `Spec.GenerativeWorld.Prior.leastDelay_pos`, `Prior.leastDelay_add`, `pauseLaw_univ`, `pauseLaw_zero`, `betaPDF_one_sub`, `betaMeasure_map_one_sub`, `betaMeasure_compl_Ioo`, `GenerativeWorld.example_holds` | `GenerativeWorld` | In every outcome both least delays of a pair of hosts are positive and add up to the pair's least round-trip time; the law of the paused time that begins in a period is a probability law, and when no pauses begin it is zero; the Beta law of a split gives no mass outside `(0, 1)` and is the same for a split and for one minus it, so it prefers no direction; a random world with three hosts, random splits, clock offsets and mean clock rates, no pauses and no wander satisfies the model. |
| `Spec.World.finite_hosts`, `GenerativeWorld.Prior.logRate_ae_eq_zero`, `Prior.wander_ae_eq_zero`, `Prior.linkPaused_ae_const`, `Prior.hostPaused_ae_const`, `isBacklog_zero_of_const`, `Draw.reading_of_noiseless`, `Prior.deviceLogRate_ae_eq_zero`, `Prior.deviceWander_ae_eq_zero`, `Prior.reportError_ae_eq_zero`, `Draw.deviceReading_noiseless`, `Prior.ae_idealConstantWorld`, `Prior.ae_withinBounds` | `GenerativeWorld` (noiseless members) | A world has finitely many hosts. In a member whose links and hosts never pause, whose clocks of hosts and of audio devices do not wander and have no spread of their mean rates, and whose audio devices report exact timestamps (`Member.Noiseless`), almost every outcome has clocks that read true time plus their drawn offset, audio devices that run at the nominal rate of true time, links and hosts with no paused time and no backlog, and is therefore an ideal constant world (`IdealConstantWorld.Holds`) whose constant delays are the least delays of the outcome; it satisfies the tight bounds of that world (`World.WithinBounds`), so the theorems about bounded worlds apply to it. |
| `Spec.GenerativeWorld.IsBacklog.backlog_eq`, `IsBacklog.nonneg`, `IsBacklog.add_le_add`, `Builds.deliver`, `Builds.arrival_eq`, `Builds.le_arrival`, `Builds.arrival_mono` | `GenerativeWorld` (every draw) | In a world built from a draw, a message from `i` to `j` sent at true time `s` arrives at the true time `Draw.arrival`, whichever message of the link it is: after the backlog of the sending host, then the least delay of the direction plus the backlog of the link, then the backlog of the receiving host. A backlog is not negative, so a message takes at least the least delay of its direction. When the paused time that has begun never decreases, a backlog falls by at most one second per second, so a message sent later on the same link arrives no earlier; messages sent during one pause arrive together. |
| `Spec.GenerativeWorld.ConstantRates.clock`, `ConstantRates.deviceReading`, `ConstantRates.capture`, `ConstantRates.capture_reported`, `ConstantRates.out`, `ConstantRates.speaker_reported`, `ConstantRates.asked`, `ConstantRates.captured`, `ConstantRates.handed`, `ConstantRates.handed_unbounded`, `ConstantRates.asked_unbounded`, `ConstantRates.arrival_mono` | `GenerativeWorld` (worlds whose clocks run at constant rates) | In a world built from a draw in which no clock wanders and the audio devices report exact timestamps (`ConstantRates`), with or without pauses of links and of hosts: the clock of a host reads its offset plus its rate times true time, and the clock of an audio device advances by its rate times true time; frames and output samples occur at the rate of their device's clock from the device's start, and blocks are handed over and requested without end; the timestamp of a block is a line in the number of its first frame or output sample; a message sent later on a link arrives no earlier. The rates of the hosts' clocks and of the devices' clocks may all differ. |
| `Spec.GenerativeWorld.ConstantDelays.toConstantRates`, `ConstantDelays.deliver`, `ConstantDelays.arrival`, `abs_inv_sub_one_le`, `ConstantDelays.withinBounds` | `GenerativeWorld` (worlds with constant rates and constant delays) | When moreover nothing pauses (`ConstantDelays`), every message takes the least delay of its direction, and when all rates are within `ε < 1/2` of one, the world satisfies `World.WithinBounds` for explicit bounds. A world in which something pauses satisfies no such bounds, because its delays have no upper bound. |
| `Spec.iIndepFun_of_const`, `isGaussianProcess_zero`, `GenerativeWorld.splitOf_mem`, `measurable_splitOf`, `splitOf_ae_eq`, `splitOf_one_sub`, `pairOf_swap`, `refOrientation_pairOf`, `canonicalDraw_split_mem`, `canonicalDraw_split_swap`, `measurable_canonicalMap`, `canonicalDraw_component`, `canonicalDraw_split_law`, `canonicalDraw_prior`, `idealWorld_builds`, `canonicalWorld_builds`, `exists_holds_of_noiseless` | `GenerativeWorld` (noiseless members) | Every noiseless member has a random world, for any hosts and speakers. The outcomes are one real number for each component of a draw, drawn independently with the law of the component; the draw of an outcome takes its splits and offsets from these numbers and has the law of the member, and the world of an outcome is the ideal constant world with those offsets and the least delays that the splits give, which is the world built from the draw. |
| `Spec.Clock.ext_read`, `CaptureDevice.ext_fields`, `PlaybackDevice.ext_fields`, `Network.ext_deliver`, `World.ext_fields`, `GenerativeWorld.Draw.ext_fields`, `Builds.unique`, `Component.measurable_scalar`, `Draw.coordinates_eq_scalar`, `canonicalDraw_coordinates`, `measurable_canonicalDraw_split`, `measurable_canonicalDraw`, `Prior.coordinates_law`, `Prior.ae_eq_canonicalDraw`, `Prior.ae_eq_canonicalWorld`, `Prior.ae_of_ae_canonicalDraw`, `Prior.ae_of_ae_canonical`, `Prior.lintegral_eq_canonical` | `GenerativeWorld` (noiseless members) | A draw determines the world built from it. In almost every outcome of every random world of a noiseless member, the draw is the draw of its own coordinates and the world is the concrete world of those coordinates, and the coordinates have the law of the concrete probability space. A property that holds in almost every outcome of the concrete random world therefore holds in almost every outcome of every random world of the member, and the mean of a function of the world that is measurable on the concrete probability space is the same in every random world of the member. |
| `Spec.updatePair_right`, `updatePair_left`, `updatePair_of_ne`, `measurable_updatePair`, `measurePreserving_updatePair`, `measurePreserving_restrict_of_eqOn`, `GenerativeWorld.reflectPair_shift`, `measurable_reflectPair`, `measurePreserving_reflectPair`, `idealWorld_shiftStarKeepPeers`, `senderSplit_injective`, `senderSplit_ne_offset`, `reflectList_of_ne`, `reflectList_apply`, `measurePreserving_reflectHost`, `measurePreserving_reflectList`, `measurePreserving_reflect`, `reflect_apply`, `reflect_of_ne`, `reflectShift_sender`, `reflect_split_sender`, `reflect_split_peer`, `reflect_delay_star`, `reflectShift_star`, `canonicalWorld_reflect` | `GenerativeWorld` (noiseless members) | Changing two of several independent numbers by a map that keeps the joint law of the two keeps the joint law of all. A map that agrees with a measure-preserving map on a set that this map sends to itself, and changes nothing elsewhere, keeps the measure restricted to any measurable set that contains the first. The reflection exchanges the two least delays between the sender and each receiving host and moves the offset of the host's clock by twice the host's asymmetry, when the moved offset stays within the range of the offsets. It keeps the law of the outcomes of the concrete random world, and the world of the reflected outcome is the world of the outcome with the hosts' timelines shifted along the links to and from the sender. |
| `GenerativeWorld.almostSurely_iff`, `aemeasurable_cost`, `expectedCost_eq_canonical`, `capture_unbounded_canonical`, `StarSolutions.le_canonical`, `StarSolutions.le_expectedCost` | `GenerativeWorld` (noiseless members) | The expected cost of a solution whose cost is a measurable function of what is drawn is the same in every random world of a noiseless member. Every star solution compared at the member (`GenerativeWorld.StarSolutions`) has an expected cost of at least `starLowerBound`: the mean, over the outcomes of the concrete random world, of the shift cost of half the shifts of the reflection, for any number of hosts and speakers. |
| `Spec.cond_volume_singleton`, `measure_pi_graph_eq_zero`, `GenerativeWorld.canonicalDraw_split_update`, `measurable_requestArrival`, `ae_requestArrival_ne_of_ne`, `ae_requestArrival_ne`, `canonicalWorld_deliver_request` | `GenerativeWorld` (noiseless members) | Among independent numbers, one whose law gives no single number a positive probability equals a function of the others with probability zero. In almost every outcome of the concrete random world, no two requests of playback devices on different hosts, each delayed by the least delay from its host to the sender, reach the sender at the same time. |

### 1.3 Communication topologies, modal split, and shift invariance (`Spec.Topologies`)

| Theorem | What it says |
|---|---|
| `Spec.modal_sq_split`, `World.syncCost_eq_var`, `World.trackingCost_eq_sync_add_mean`, `World.weighted_frame_modal_split` | Exact orthogonal decomposition of quadratic frame objectives: synchronization cost `S` equals latency variance (differential mode), tracking cost `Θ` equals `S` plus squared common-mode tracking error, and a weighted sum `w_S S + w_Θ Θ` (with weights `w_S`, `w_Θ`) weights differential mode by `w_S + w_Θ` and common mode by `w_Θ`. |
| `Spec.World.roughness_linear_ramp`, `World.roughness_boundary_step`, `cyclePositionWeight_eq` | Over `M` uniform samples at nominal rate `ρ` (duration `Δt = M / ρ`), ramping speed linearly by `Δv` costs `ρ Δv² / M` roughness (whereas a boundary step costs `M` times more), converting specification position and roughness weights `(c_pos, c_rough)` to per-cycle position weight `(c_pos / c_rough) Δt⁴`. |
| `Spec.World.shiftHosts_rtt_eq`, `Solution.plays_shiftHosts`, `Solution.sync_shiftHosts_lower_bound`, `Solution.tracking_shiftHosts_lower_bound` | Shifting host timelines by a shift vector `Δ` (`Δ sender = 0`) preserves all round-trip times and, for any non-Zeno solution without cross-origin arrival collisions, leaves every host's view and playback decisions unchanged, forcing long-run lower bounds on `World.sync` and `World.tracking` across opposite shifts `±Δ`. |

### 1.4 Fundamental topology limits and Star-vs-Peer separation (`Spec.Limits`)

| Theorem | What it says |
|---|---|
| `Spec.withinSpeed_of_step_bound` | Converts a per-sample frame-advance bound `|y - x - 1| ≤ u` (`0 ≤ u < 1`) into `Solution.WithinSpeed` with bound `(2 ε_D + (1 + ε_D) u) / (1 - ε_D)` in any world satisfying `World.WithinBounds` with device rate-error bound `ε_D`. |
| `Spec.fixedDelay_isStar`, `FixedDelay.noCrossOriginCollision_sepBaseWorld` | The abstract `FixedDelay.solution` is a star solution (`IsStar`) and has no cross-origin arrival collisions on `sepBaseWorld`. |
| `Spec.star_states_eq_of_star_links_eq` | Any star solution (`Solution.IsStar`) has identical run states and playback decisions when receiver-to-receiver links are modified. |
| `Spec.star_sync_lower_bound_with_symmetric_peers` | On the world pair `(w⁺, w⁻) = (shiftStarKeepPeers w Δ, shiftStarKeepPeers w (-Δ))`, where star links carry opposite asymmetries `±Δ` and direct peer links remain unmodified (including arbitrarily fast, symmetric peer links), every qualifying non-Zeno star solution suffers `max (w⁺.sync) (w⁻.sync) ≥ Var_r (Δ (host r))`, the variance across speakers `r` of their host shifts. |
| `Spec.peer_probe_recovers_exact_offset` | On a symmetric constant-delay peer link in a shifted ideal world with host clock offsets `c₁`, `c₂` and shifts `Δ h₁`, `Δ h₂`, a four-timestamp peer exchange recovers the exact relative shifted clock offset `(c₂ - Δ h₂) - (c₁ - Δ h₁)`. |
| `Spec.ForwardStar.isStar`, `ForwardStar.noCrossOriginCollision`, `ForwardStar.progress`, `ForwardStar.sync_eq` | Tightness witness on `(sepWorldPlus A, sepWorldMinus A)` for any asymmetry parameter `A ∈ (0, 1/4)` (both in `IdealConstantWorld.Asymmetric`): `ForwardStar.solution` is a qualifying star solution attaining `sync = A²` in both worlds. |
| `Spec.PeerSync.usesGraph`, `PeerSync.progress`, `PeerSync.sync_eq_zero`, `peer_beats_star_asymmetry_bound` | Two-sided separation directly on `Unisono.Spec`: for any asymmetry parameter `A ∈ (0, 1/4)`, every qualifying star solution suffers `max sync ≥ A²`, whereas `PeerSync.solution` uses only star links plus the symmetric peer link `1 ↔ 2`, is non-Zeno, plays every frame `n ≥ 2`, and achieves `sync = 0` in both `sepWorldPlus A` and `sepWorldMinus A`. |

### 1.5 Abstract fixed-delay reference solution (`Solutions.FixedDelay`)

An abstract, real-valued reference `Unisono.Spec.Solution` (not the Rust
production core) proved end to end under `World.WithinBounds`:

| Theorem | What it says |
|---|---|
| `Solutions.FixedDelay.solution_append`, `block_received`, `block_latest`, `offset_received`, `offset_latest`, `asked_request`, `last_after_request`, `last_none`, `answered_query`, `answered_latest`, `positions_fold`, `lookup_chosen`, `positions_block`, `lastChosen_block`, `chosen_succ`, `chosen_isSome` | Host memory and block-position recursion invariants of the abstract fixed-delay baseline. |
| `Solutions.FixedDelay.block_arrives`, `origin_inFlight`, `replicate_copies`, `query_inFlight`, `answer_inFlight`, `query_answered`, `answer_reaches`, `offset_sample`, `block_handled`, `block_memory`, `offset_recent`, `exists_block_of_frame`, `frame_held`, `playable_of_captured` | Message delivery, query-answer timing, and frame playability under `World.WithinBounds` when message repetition exceeds the consecutive-loss bound `lossRun`. |
| `Solutions.FixedDelay.progress`, `asked_gap`, `handed_gap`, `request_step`, `last_at_next_request`, `advance_tracks`, `advance_converges`, `target_time_error`, `captured_nominal`, `captured_target`, `target_band`, `exists_last_below`, `exists_block_of_sample`, `trajectory_step`, `plays_eq_chosen`, `targetError_mono`, `late_targets` | Non-Zeno progress, bounded inter-event gaps, clock-estimate freshness, and slew convergence into the target latency band. |
| `Solutions.FixedDelay.progress_of_unbounded`, `request_step_of_unbounded` | The baseline's run advances past every true time and handles every request of every speaker in every world whose capture device hands over blocks without end and whose playback devices request blocks without end, whatever the delays of the network. |
| `Spec.CaptureDevice.block_unique`, `Solutions.FixedDelay.block_inFlight`, `block_arrives_of_noLoss`, `block_handled_of_noLoss`, `inFlight_frames`, `held_of_noLoss`, `mem_held_iff_arrived` | In a world whose network loses nothing and delivers a message at a true time that does not depend on which message of its link it is, with delays that need not be bounded: the message of every block is in transit to every receiving host after the block's handover; only block messages carry frames; and when a playback device requests a block, its host holds a frame if and only if the message of the frame's block arrived strictly before the request. |
| `Solutions.FixedDelay.speaker_at_latency`, `plays_at_latency`, `guarantees`, `plays_at_latency_example` | From some output sample onward, every speaker plays continuously within `latencyError` of `L`, yielding zero long-run missed samples and discontinuities and explicit bounds on mean latency, synchronization, and tracking; `plays_at_latency_example` exhibits a two-host world meeting all hypotheses. |
| `Spec.limsup_weighted`, `World.cost_le`, `World.weighted_tracking_le_cost`, `World.PlaysAtLatencies.playsAtLatency`, `World.missed_eq_zero_of_exact`, `World.discontinuities_eq_zero_of_exact`, `World.latency_eq_of_exact`, `World.capture_step_of_linear`, `World.tracking_le_of_exact`, `World.sync_le_of_exact`, `IdealConstantWorld.Holds.captured_eq` | The cost of a playback is at most the weighted sum of the long-run values of the six objectives and at least the weighted long-run tracking. When every output sample of each speaker `r` plays the sound captured exactly `L r` seconds before it leaves, in a world whose capture times are linear in the position, every frame that speaker `r` plays has latency exactly `L r`; the long-run tracking is at most the mean over the speakers of the squares of `L r` minus the target latency, the long-run synchronization is at most the sum over the pairs of speakers of the squared differences of their latencies divided by the square of the number of speakers, and no samples are missed and playback has no discontinuities in the long run. |
| `Spec.Solution.plays_shiftStarKeepPeers`, `IdealConstantWorld.Holds.starNet`, `IdealConstantWorld.Holds.shiftStarKeepPeers` | A star solution that makes progress, in whose run no two messages from different hosts arrive at one host at the same time, plays the same when the timelines of the hosts are shifted along the links to and from the sender while the other links stay as they are; an ideal constant world shifted in this way is an ideal constant world with the shifted delays. |
| `Spec.State.fields_of_withoutPlays_eq`, `State.sendAll_withoutPlays`, `State.handle_withoutPlays_eq`, `State.handle_withoutPlays`, `State.step_withoutPlays`, `Solution.states_withoutPlays`, `Solution.views_eq_of_sends_eq`, `Solution.held_eq_of_sends_eq`, `Solution.askedNext_eq_of_sends_eq`, `Solution.earliest_eq_of_sends_eq`, `Solution.handled_eq_of_sends_eq`, `Solution.eventTime_eq_of_sends_eq` | Two solutions that send the same messages and set the same timers at every view have the same run in every world, except for what the speakers play: the hosts observe the same events at the same true times, hold the same frames, and handle the same requests. |
| `Spec.Observation.frames_mapMsg`, `State.forget_send`, `State.forget_sendAll`, `State.forget_observe`, `State.forget_addTimers`, `State.forget_withoutPlays`, `State.forget_handle`, `State.forget_key`, `State.forget_due`, `State.forget_step`, `Solution.states_forget`, `Solution.views_forget`, `Solution.held_forget`, `Solution.askedNext_forget`, `Solution.earliest_forget`, `Solution.handled_forget`, `Solution.eventTime_forget` | Let one solution send the messages of another with further fields in each payload, and set the same timers (`Solution.SendsMore`). Once the further fields are forgotten, the two have the same run in every world, except for what the speakers play: the hosts observe the same events at the same true times, hold the same frames, and handle the same requests. |
| `Spec.shiftCost_nonneg`, `frameCost_nonneg`, `meanFin_add`, `meanFin_sub`, `varFin_add_add_varFin_sub`, `two_mul_shiftCost_le`, `World.accruedFrames_mono`, `World.accruedFrames_weighted`, `World.longRun_frames_le_cost`, `playTime_shiftStarKeepPeers`, `Solution.cost_shiftStarKeepPeers_add_ge` | A star solution that makes progress and eventually plays every frame, in whose run no two messages from different hosts arrive at one host at the same time, has costs in a world and in the same world with the star links shifted that add up to at least twice the cost of half the shift, for any number of hosts and speakers. The cost of a shift at one frame is the weight of synchronization times the variance of the speakers' shifts plus the weight of tracking times the mean of their squares. |
| `Solutions.FixedDelay.latencyError_ideal`, `cost_le_of_ideal` | In an ideal constant world with any number of receiving hosts and no speaker on the sender's host, the baseline at the target latency, under the delivery margin and with no two messages from different hosts arriving at one host at the same time, has a cost of at most the weight of synchronization times the sum over the pairs of speakers of the squared differences of their hosts' asymmetries divided by the square of the number of speakers, plus the weight of tracking times the mean over the speakers of the squared asymmetry of the host, when the weights of latency and roughness are zero. The asymmetry of a host is half the difference between the delay from the sender to it and the delay back. |
| `Spec.meanFin_const_add`, `varFin_const_add`, `frameCost_const_add`, `shiftCost_neg`, `shiftCost_le`, `ofReal_shiftCost`, `World.PlaysAtLatencies.exists_covers`, `World.PlaysAtLatencies.exists_playTime`, `World.frameCost_le_cost_of_exact` | Under playback at exact latencies, in a world whose capture times are linear in the position and whose output samples leave after every true time, every speaker plays every frame from some frame on, exactly its latency after the frame's capture, and the cost is at least the frame cost of the latencies when the target latency is constant. With latencies `t + a r` and target `t` the frame cost is the shift cost of `a`, which does not change when `a` changes sign and is at most the sum of the weights of synchronization and tracking times the square of a bound on the sizes of the entries of `a`. |
| `Spec.Solution.handled_asked_time`, `Solutions.FixedDelay.act_sends`, `inFlight_provenance`, `noCrossOriginCollision` | In any world, every message of the baseline in transit to a host other than the sender comes from the sender, and every message in transit to the sender is a clock query that another host sent when one of its playback devices requested a block. Two of the baseline's messages from different hosts therefore arrive at one host at the same time only when two such requests, each delayed by the network, reach the sender at the same time. |
| `Spec.IdealConstantWorld.Holds.out_unbounded`, `IdealConstantWorld.Holds.capture_unbounded`, `Solutions.FixedDelay.playsAtLatencies_of_ideal`, `playTime_of_ideal`, `cost_eq_of_ideal` | Under the conditions of `cost_le_of_ideal`, from some output sample on every output sample of each speaker plays the sound captured exactly the target latency plus the asymmetry of the speaker's host before it leaves; from some frame on every speaker plays every frame at that latency; and the baseline's cost equals the shift cost of the asymmetries of the speakers' hosts. |

### 1.6 The controller: playback at a level that the sender announces (`Solutions.Controller`)

`Solutions.Controller.solution` sends the baseline's messages with further
fields and plays differently. The sender announces with every block the
level of the block's first frame, which is the latency that every speaker is
to hold for it, and the slope of the level; how it chooses the level is a
parameter (`LevelRule`). The sender estimates the capture time of each frame
on its clock as a line through the capture device's timestamps, each
receiving host estimates the sender's clock as a line in its own clock from
its clock exchanges, and each host estimates when each output sample leaves
as a line through its playback device's timestamps. The estimators are
parameters. A speaker plays, at each output sample, the position whose
capture time plus level is the sender's clock reading at which the sample
leaves. Each frame has the level announced with its own block: a host keeps
the header of every block that arrived and uses, for an output sample, the
header of a block whose own frames contain the position that the header says
is due (`Header.Covers`, `dueOf`), so that every host changes the level at
the same frame. When the clocks of the hosts and of the audio devices run at constant rates,
each its own, and the level is held at `L`, the position that is due at an
output sample is the one captured `L` divided by the rate of the sender's
clock, plus the asymmetry of the speaker's host, before the sample leaves.
When links and hosts pause, from some output sample on each output sample
plays that position if the message of the capture block it needs took less
than the sample's margin, and plays nothing of the source otherwise
(`speaker_plays`, `plays_eq_of_margin`, `plays_under_pauses`). The margin of
an output sample is the time from the handover of the capture block it needs
to the request of its own block. It lies between two numbers that do not
depend on the sample, and both rise by one second for each second of latency
(`margin_mem`). Without pauses every block is in time, and the speaker plays
every frame at that latency (`playsAtLatencies`).

An output sample is late when the message of the capture block it needs
takes at least the sample's margin, and the late rate of a level is the
long-run number of late output samples per second, averaged over the
speakers. The cost of a held level is at most the cost of the speakers'
latencies in synchronization, latency and tracking, plus a multiple of the
late rate (`cost_le_of_heldLevel`). The first part rises with the level and
the late rate falls with it.

These theorems hold in one outcome. Not proved: how large the late rate is
under the generative model, and so anything about expected cost; that no
other solution has a lower cost; and that two clock exchanges of a host
escape every pause with probability one, which `plays_under_pauses` assumes
of the outcome. The solution does not yet change its pace smoothly, measure
what frames need, or choose the level from such measurements.

| Theorem | What it says |
|---|---|
| `Solutions.Controller.twoExchanges_exact`, `twoReports_exact` | The estimator of the sender's clock that uses two clock exchanges, and the estimator of a device's line that uses two timestamps, are exact on undisturbed data: when all exchanges, or all timestamps, lie on one line, they return it. |
| `Solutions.Controller.plain_enrich`, `sendsMore`, `plays_asked` | The controller sends what the baseline sends, with more in each message (`Solution.SendsMore`), so with the further fields forgotten its run is the baseline's, apart from what the speakers play. At a device request it plays the position that is due by its schedule, its clock line and its device line. |
| `Spec.CaptureDevice.head?_block`, `PlaybackDevice.head?_block`, `Solutions.FixedDelay.act_sends_block`, `Solutions.Controller.exchangesOf_eq`, `mem_plainExchangesOf`, `plainExchangesOf_mem`, `mem_headersOf`, `headersOf_mem`, `headersOf_append_asked`, `mem_playbackReports`, `mem_captureReports`, `sends_block`, `block_header` | In any world: the timestamps that a host has collected from a device are those of the device's blocks, each with the block's first frame or output sample; the clock exchanges of a view are those of the view with the further fields forgotten; the schedule of a receiving host holds exactly the headers of the blocks that arrived, each with the number of frames that its message carried; and every block in transit carries the header that the sender computed from its view when the capture device handed the block over. |
| `Solutions.Controller.leastRoundTrip_exactFromLeast` | The estimator of the sender's clock that keeps the clock exchanges of least round trip and applies the two-exchange estimator to them is exact from the exchanges of least round trip (`ClockEstimator.ExactFromLeast`): when no exchange has a round trip shorter than `τ`, and the exchanges with round trip `τ` lie on one line, it returns that line. |
| `Solutions.Controller.captured_duePosition`, `duePosition_succ`, `exchange_lines`, `exchange_of_built`, `handedNext_of_handled`, `captureLine_exact`, `playbackLine_exact`, `speaker_plays`, `margin_mem`, `plays_eq_of_margin`, `plays_of_delay` | Consider a world whose clocks run at constant rates, with exact timestamps and with pauses of links and of hosts (`ConstantRates`), a device estimator that is exact on undisturbed reports, the level held at `L`, a speaker whose host is not the sender's, and an estimate of the sender's clock at that host that is the line of its undelayed clock exchanges from some true time on (`ClockLineFrom`). From some output sample on, output sample `k` plays the position that is due (`duePosition`), captured `latencyOf` before the sample leaves, if the message of the capture block that holds the last frame the resampler needs arrived strictly before the playback device requested the sample's block; otherwise it plays nothing of the source. Equivalently, it plays if and only if that message took less than the sample's margin. The margin is more than `marginLeast` and at most `marginMost`: the latency minus the request lead, and minus between the span of `lookahead - 1` frames and the spans of one playback block, one capture block and `lookahead` frames. So a block that takes at most `marginLeast` is in time, and one that takes at least `marginMost` is late. The lines through the timestamps of the capture device and of each playback device are exact from the second block on. |
| `Solutions.Controller.exchange_roundTrip`, `clockLineFrom_of_undelayed`, `plays_under_pauses` | In such a world, the round trip of every clock exchange on the querying host's clock is at least the rate of that clock times the least round-trip time of the pair, and an exchange with exactly that round trip was delayed in neither direction. Once a host's view holds two such exchanges whose queries were sent at different readings (`TwoUndelayed`), every clock estimator that is exact from the exchanges of least round trip returns the line of the undelayed exchanges from then on, whatever pauses come later. With the least-round-trip estimator and the two-report estimator the controller therefore plays as the previous row says. That two exchanges escape every pause is assumed of the outcome. |
| `Solutions.Controller.exists_duePosition_nonneg`, `lateRate_le`, `cost_le_of_heldLevel`, `cost_le_under_pauses` | **The cost of a held level under pauses.** Consider a world whose clocks run at constant rates, with exact timestamps and with pauses, with no speaker on the sender's host, the level held at `L`, an estimate of the sender's clock at every speaker's host that is the line of its undelayed exchanges from some true time on, and a capture device whose clock runs less than twice as fast as the clock of every playback device and faster by a fraction of at most `δ`. For any weights, the cost is at most: the weight of synchronization times the sum over the pairs of speakers of the squares of the differences of their latencies, divided by the square of the number of speakers; plus the weight of latency times the mean latency; plus the weight of tracking times the mean square of the latency minus the target latency; plus the weight of missed samples times `1 + 2 δ`, plus the weight of discontinuities, times the late rate (`lateRate`). The late rate is the long-run number of output samples per second, averaged over the speakers, whose capture block takes at least the sample's margin; it is at most the long-run number of output samples whose block takes more than the least margin. Roughness costs nothing. With the least-round-trip estimator the condition on the estimate holds once two clock exchanges of every speaker's host were not delayed. The bound holds in one outcome: it is not a statement of expected cost, and no lower bound for other solutions is proved. |
| `Solutions.Controller.exchange_of_view`, `exists_two_exchanges`, `clockLineFrom_of_exact`, `speaker_exact`, `playsAtLatencies`, `playsAtLatencies_example` | In a world with constant rates within `ε < 1/2` of one and constant delays (`ConstantDelays`), with estimators that are exact on undisturbed data, the level held at `L`, no speaker on the sender's host, the capture device's clock less than twice as fast as the clock of every playback device, and `L` above the delivery margin: from some output sample on, every speaker plays continuously, and every output sample plays the sound captured exactly `L` divided by the rate of the sender's clock, plus half the difference between the delay from the sender to the speaker's host and the delay back, before the sample leaves. This is the case without pauses of the two previous rows: every block takes the least delay of its direction, which is within the least margin. The conditions can be met (`playsAtLatencies_example`, in a world whose clocks all run at the rate of true time). |

### 1.7 Optimality in expected cost (`Spec.Optimality`)

`OptimalWithin` defines what it means for a solution to be optimal within a
margin: its expected cost exceeds that of no compared solution by more than
the margin, in every random world of every member of a family of laws. The
solutions compared at a member depend on that member alone. A margin of `⊤`
at a member says nothing about that member. A statement about
`GenerativeWorld` is always about every member
(`GenerativeWorld.OptimalWithin`), so a statement that covers only some
members shows the margin `⊤` for the others.
One statement of optimality is proved: in the noiseless members of
`GenerativeWorld`, the baseline is optimal among the compared star solutions
within a known margin (`Solutions.FixedDelay.optimalWithin`). A star
solution is one whose hosts exchange messages only with the sender. The
statement does not compare solutions that use links between receiving
hosts, and it does not cover members with pauses or clock wander.

| Theorem | What it says |
|---|---|
| `Spec.OptimalWithin.expectedCost_eq` | Two solutions that are both optimal with no margin have the same expected cost in every random world of every member. |
| `Spec.measurable_shiftCost`, `cond_volume_Icc_compl_le`, `GenerativeWorld.Draw.measurable_split`, `Draw.measurable_asymmetry`, `abs_asymmetry_le`, `reflectScale_mul`, `reflectShift_of_mem`, `measure_reflect_out_le`, `lintegral_asymmetry_le` | The asymmetry of a host in a draw is how far the least delay from the sender to it exceeds half the least round-trip time between the two; its size is at most half that round-trip time. The reflection moves the offset of a receiving host's clock out of the range of the offsets with a probability of at most the least round-trip time between the sender and the host divided by the bound of the offsets. The mean, over the outcomes of the concrete random world, of the shift cost of the asymmetries of the speakers' hosts exceeds `starLowerBound` by at most `starMargin`. |
| `Solutions.FixedDelay.asymmetry_idealWorld`, `margin_idealWorld`, `noCollision_canonicalWorld`, `ae_idealWorld`, `ae_cost_eq`, `starSolutions`, `optimalWithin`, `optimalWithin_conditions` | Consider a generative model in which no speaker is on the sender's host, weights with no weight on latency or roughness, and the baseline configured for the model (`Params.Fits`). Take the noiseless members in which the target latency exceeds the delivery margin of every speaker (`NoiselessWithMargin`). In almost every outcome the baseline's cost is the shift cost of the asymmetries of the speakers' hosts. The baseline is a compared star solution (`GenerativeWorld.StarSolutions`). The theorem is stated for every member of the model: for these members, with any number of hosts and speakers, the baseline's expected cost exceeds that of no star solution compared at the member by more than `starMargin`, and for every other member its margin is `⊤`. `starMargin` is the sum of the weights of synchronization and tracking times `ρ ^ 3 / (4 * Θ)`, where `ρ` is the sum over the speakers of the least round-trip time between the sender and the speaker's host and `Θ` is the bound of the clock offsets. The conditions can be met: a model with three hosts and two speakers, a configuration of the baseline and a noiseless member with a random world satisfy them. |

## 2. Supplementary analytical results

The theorems in this section operate in simplified component or
centralized/oracle models (explicitly named in each subsection) rather than
directly on `Unisono.Spec.Solution` and `Unisono.Spec.Objectives`.

### 2.1 Component clock, stream, single-mode regulation, and level models (`Model.*`)

| Theorem | Module | What it says |
|---|---|---|
| `Model.Exchange.error_bound` | `Model.Exchange` | A bidirectional packet exchange determines clock offset up to half the minimum-delay asymmetry plus half the excess delays. |
| `Model.SupportLine.highest`, `estimate_isGreatest`, `excess_le`, `excess_near`, `error_at_centre`, `error_ahead` | `Model.SupportLine` | The lower-hull support line through two samples straddling the mean time is the highest line under all samples, minimizes total excess (maximum likelihood for independent exponential delays, up to rounding), and has explicit error bounds independent of delayed outliers. |
| `Model.LineFit.cost_le`, `error_bound`, `schedule_invariant` | `Model.LineFit` | Weighted least-squares line minimization, error bound from point errors, and invariance of synchronization to sender-clock offset and rate. |
| `Model.Stream.group_misses_iff`, `sum_sq_errors`, `dueTime_position`, `groupNeed_errors`, `group_misses_errors` | `Model.Stream` | Fleet miss condition against group need, squared timing-error decomposition, packet-header due-position formula, and perturbation bound on group need under bounded timing errors. |
| `Model.Regulation.cost_add_value`, `total_cost_ge`, `total_cost_law`, `value_step`, `distance_from_rest`, `weight_gainFor`, `gain_unique`, `at_limit`, `next_shift` | `Model.Regulation` | Deterministic dynamic-programming minimization, geometric contraction, closed-form unique weight-to-gain relation, and limit behavior for the single-mode quadratic pace regulator. |
| `Model.RegulationRandom.mean_cost_sum`, `mean_cost_law_le`, `mean_value_law_le`, `mean_cost_rate`, `mean_square_split`, `unforeseen_revision`, `distance_step`, `unforeseen_pace` | `Model.RegulationRandom` | Stochastic separation and long-run cost minimization of the linear regulation law in the single-mode quadratic model under arbitrary martingale (unforeseen) schedule revisions. |
| `Model.Gains.gains_close`, `gains_of_integers`, `law_close`, `planned`, `cost_of_distance` | `Model.Gains` | Exact closeness bounds between integer floor-rounded gains/planned cycle reads and the real-valued regulation law, plus quadratic cost of deviation from the law. |
| `Model.Level.measure_largest`, `measure_largest_le`, `integral_predictive`, `volume_missed`, `missed_le`, `missed_ge`, `volume_lasts`, `move_pays_iff` | `Model.Level` | After `N` observed stretches, exchangeable next-stretch exceedance probability is at most `1 / (N + 1)`; predictive cost integral, pause-duration missed-time bounds, and break-even criterion for changing playout level. |

### 2.2 Multi-speaker modal control (`Analysis.ModalControl`)

*Boundary:* discrete-time per-cycle linear-quadratic approximation with uniform
aligned cycles `Δt`, unconstrained real-valued per-cycle reads (omitting
continuity, speed bounds, and data availability), assumed martingale expected
increments (not derived from `SecondOrderMoments`), and a centralized shared
filtration `ℱ`. Centralized minimization theorems serve as lower-bound
benchmarks on the auxiliary per-cycle cost `multiCycleCost` (not on
`Unisono.Spec.Objectives`) that decentralized nodes cannot beat within that
per-cycle model.

| Theorem | What it says |
|---|---|
| `Analysis.weight_gainForWeight`, `gainForWeight_unique` | Exact inversion of `Regulation.weight` on `(0, 1)`: `gainForWeight c = gainFor (c^{1/4})` is the unique gain with position weight `c`. |
| `Analysis.single_cost_split`, `single_law_optimal`, `single_law_unique_ae` | Under a fixed filtration `ℱ` and martingale expected increments, applying `Regulation.law g` to the conditional-mean state uniquely (almost everywhere, a.e.) minimizes finite-horizon expected per-cycle quadratic cost plus terminal value. |
| `Analysis.multiCycleCost_modal_split`, `multi_lipsync_optimal`, `multi_lipsync_unique_ae`, `multi_lipsync_cost_rate`, `multi_lipsync_law_cost_le` | Centralized full-information lip-sync benchmark on `multiCycleCost`: orthogonal modal decomposition into common mode (tracking weight `cΘ`) and differential mode (weight `cS + cΘ`, where `cS` is the synchronization weight), with two-gain `modalRead` as the a.e. unique finite-horizon and long-run minimizer. |
| `Analysis.multi_lowlatency_optimal`, `multi_lowlatency_unique_ae` | Centralized `multiCycleCost` benchmark when tracking weight `cΘ = 0` and mean-latency/missed-sample costs are omitted: `consensusRead` holds mean pace constant and applies `law gDiff` (with differential-mode gain `gDiff`) to differential mode (requires an additional small common-mode loop in practice to prevent drift). |
| `Analysis.decentralized_star_cost_eq`, `symmetric_star_cost_split`, `decentralized_star_uncorrelated_optimal`, `consensus_one_hot_var` | `multiCycleCost` decomposition for symmetric pure-star policies across `R` speakers into shared common vs. private uncorrelated components (weighting private errors by `((R - 1) / R) cS + cΘ`), minimization of `multiCycleCost` when cross-receiver errors are uncorrelated, and zero-mean projection norm `((R - 1) / R) Δ²` of a single-speaker step `Δ`. |

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
| `Analysis.margin_best_missed`, `margin_best_tracking` | Global minimization quantile conditions for playout margin `m` under Campbell mean-latency plus missed-fraction cost `J_buf(m)` (and with quadratic target-margin tracking). |
| `Analysis.fleet_average_missed_cost` | Linearity of Campbell missed-audio cost over the fleet-averaged pause intensity measure. |
| `Analysis.margin_best_exponential_with_clicks`, `discontinuity_nonconvex_example` | Closed-form global minimizer `m* = max 0 (h̄ log (λ (w_M + w_D / h̄) / w_Λ))` of `J_buf(m)` for a shared exponential pause distribution (mean pause duration `h̄`, pause arrival rate `λ`, and weights `w_M` for missed audio, `w_D` for discontinuities, and `w_Λ` for mean latency), and an atomic-pause counterexample showing discontinuity penalties can break convexity in general. |

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
| `Relation.fit_spec`, `mean_time_spec`, `anchor_near_mean`, `through_best`, `through_excess` | `fit` changes only the line, stores a slope-limited support line under all kept samples through two samples straddling the rounded mean time, and matches the excess-minimizing support line of Section 2.1 in real numbers. |
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
| `MinRtt.new_spec`, `reset_spec`, `observe_spec`, `path_ns_spec`, `variance_ns2_spec`, `uncalibrated_variance_spec` | Totality, ring-length invariant `len ≤ W` (sliding window capacity `W`), nonnegative `path_ns`, variance-floor enforcement on every emitted measurement, inflated variance `(rtt / 2)²` for uncalibrated single-sample windows (`len < 2`), and strict monotonic deduplication of emitted exchange identifiers. |

### 3.7 Two-state fixed-point Kalman filter (`Kalman`)

| Theorem | What it says |
|---|---|
| `Kalman.enforce_psd_spec`, `new_spec`, `anchor_spec`, `anchor_with_freq_spec`, `predict_psd`, `update_psd`, `to_line_spec` | Totality, 2×2 covariance positive semidefiniteness (diagonal entries `p00 ≥ 0`, `p11 ≥ 0`, off-diagonal `p01² ≤ p00 * p11`) preserved across initialization, zero- and preserved-frequency anchoring, prediction, and Joseph-form update (enforced by explicit clamping in `enforce_psd`), and valid `Line` export (`run = LINE_RUN > 0`). |
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
| `Sync.new_total`, `add_peer_total`, `set_sender_clock_id_total`, `reset_sender_clock_total`, `on_sender_echo_total`, `next_peer_probe_total`, `on_peer_echo_total`, `build_relay_total`, `on_peer_relay_total`, `update_modal_filters_total`, `step_total` | Every public method of `Sync` (and its internal modal-filter transition helper) returns for every state and input. |
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

### 3.15 Production-core `Solution` composition (`Unisono.Solutions.Core`)

Composes the Aeneas-translated production core (`Sender`, `Sync`, `Receiver`,
`ModalPlayer`, and version 2 `packet` headers) into a `Unisono.Spec.Solution`
with strictly local observations. Because `unisono-runtime` is not translated to
Lean, `Core.solution` is a Lean composition of the core functions (without
`Device` line fitting, independent timer events, or separate `T3` send reads)
rather than a proof about the runtime threads.

| Theorem | Model / Scope | What it says |
|---|---|---|
| `Solutions.Core.usesGraph_of_peers`, `isStar_of_no_peers` | Any `World` | Every message sent by `Core.solution` respects the declared sender + peer allowlist graph; when every host's peer list is empty, `Core.solution` satisfies `Solution.IsStar`. |
| `Solutions.Core.progress`, `request_step` | `World.WithinBounds` | In every world satisfying `World.WithinBounds`, the run of `Core.solution` is non-Zeno (advances past every true time) and reaches every speaker block request `(r, b)`. |
| `Solutions.Core.sync_zero_peers_inv`, `star_no_peer_messages`, `star_sync_snapshot_eq_sender_kalman`, `star_modal_player_eq_single_mode` | Any `World` | When `peers h = []`, `Sync.peer_count` stays `0`, zero `peerProbe`/`peerEcho`/`peerRelay` messages are sent, every `Sync.step` exports a Star snapshot (`peer_active = false`, `active_peers = 0`, `diff_var_ns2 = 0`), and `ModalPlayer.cycle` matches single-mode `Player.cycle` at `star_gain`. |
| `Solutions.Core.modal_cycle_full_spec`, `receiver_cycle_plan_spec`, `rcv_modal_inv`, `withinBlock_speed_bound`, `boundary_step_safe` | `World.WithinBounds` | `Core.solution` preserves `use_sync = true` and regulation settings across all events; every consecutive pair inside a playback block unconditionally obeys the `World.speed` bound under `World.WithinBounds`; across adjacent non-empty blocks (without intervening `stop()` or 64-bit unsigned integer `u64::MAX` overflow, and with `jump ≥ 3`), every continuous boundary step obeys `|y - x - 1| ≤ paceBound limit`. |
| `Solutions.Core.ideal_ntp_exchange_exact`, `ideal_kalman_and_sender_time_exact`, `ideal_modal_cycle_unity`, `ideal_zero_cost_objectives` | `IdealConstantWorld` | Within the 64-bit nanosecond range, `ntp_exchange` recovers exact offset and RTT, `KalmanFilter` preserves the exact zero-innovation fixed point and `SyncSnapshot.sender_time` maps local time to exact sender time, `ModalPlayer.cycle` plans exact `Step.UNITY`, and any playback trajectory already on the ideal unity-step schedule at `m.targetLatency` achieves `sync = 0`, `tracking = 0`, `roughness = 0`, `missed = 0`, `discontinuities = 0`, and `meanLatency ≤ targetLatency` (note: `ideal_zero_cost_objectives` takes that trajectory as a hypothesis and does not mention `Core.solution`). |

## 4. What is not proved (Open)

1. **No objective bounds for `Core.solution` in any model:**
   `Unisono.Solutions.Core` proves causality, communication-graph membership,
   exact Star degeneration, non-Zeno progress and request liveness under
   `World.WithinBounds`, within-block speed bounds unconditionally under
   `World.WithinBounds` (plus the conditional adjacent-block bound
   `boundary_step_safe`), and component-level exactness on ideal constant
   inputs. No theorem currently connects a run of `Core.solution` to any of the
   six `Unisono.Spec.Objectives` in any model (`IdealConstantWorld`,
   `World.WithinBounds`, `StationaryNetworkDisturbances`,
   `SecondOrderMoments`, `StochasticWorld`, or `GenerativeWorld`).
2. **Unused stochastic world hypotheses:** no theorem in the repository
   currently takes `SecondOrderMoments`, `StochasticWorld` or `GenerativeWorld`
   as a hypothesis;
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
4. **Integer-to-real estimator equivalence (`MinRtt`, `Kalman`, `Blue`):**
   - `MinRtt.lean` proves totality, exact single-exchange NTP arithmetic, ring
     size, variance floors, and deduplication, but not that `SlidingMinRtt`
     emits the exact minimum RTT across its window.
   - `Kalman.lean` proves totality, zero-innovation fixed-point preservation,
     and PSD preservation via explicit clamping in `enforce_psd`, but not
     equivalence or error bounds against the real-valued Kalman recursion.
   - `Blue.lean` proves totality, variance/count invariants, zero right-hand-side
     fixed point, and exact single-edge Star recovery
     (`solve_blue_single_edge_star`), but not finite-precision error bounds
     comparing integer `LDL^T` against real-valued
     `Analysis.Estimation.thomson_blue_optimal` on multi-peer graphs.
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
   the command-line program are checked by unit tests, multi-seed true-time
   simulation (`crates/unisono-sim`), Loom concurrency interleavings,
   machine-code inspection (`crates/reachable`, `crates/cycle-cost`), and
   container tests against PipeWire and Advanced Linux Sound Architecture
   (ALSA).
7. **Optimality in expected cost under `GenerativeWorld`:** the baseline is
   proved optimal within a margin only among star solutions and only in
   noiseless members (`Solutions.FixedDelay.optimalWithin`). No solution is
   proved optimal among all solutions. No lower bound on expected cost is
   proved for solutions that use links between receiving hosts, and nothing
   is proved about expected cost in members with pauses or clock
   wander. The compared star solutions exclude any solution in whose run two
   messages from different hosts arrive at one host at the same time with
   positive probability. Random worlds are constructed for every
   noiseless member and for one member with random mean clock rates; a
   random world with pauses needs a Poisson process and one with
   wander needs a stationary Gaussian process with continuous paths, and
   neither is constructed in Lean. The expectation that a solution loses nothing in the long run by not
   being told the numbers of its member is not proved. The generative
   model is not shown to belong to the model classes above.
8. **The controller under the generative model:** `Solutions.Controller` is
   described output sample by output sample, and only in worlds whose clocks
   run at constant rates with exact timestamps. The cost of a held level is
   bounded in each outcome by the late rate of that outcome. Not proved: any
   statement of probability or of expected cost about it (how large the late
   rate is, a choice of the level); a lower bound on the cost of other
   solutions under pauses; that two clock exchanges of a host escape every
   pause with probability one; anything when clocks wander or timestamps
   have errors. Its pace does not yet change smoothly,
   and it does not yet measure what frames need or choose the level; the
   regulator and the choice of the level exist only as side models
   (`Model.Regulation`, `Model.Level`) and in the production code. No world
   with a pause is constructed in Lean, so the theorems about worlds with
   pauses have no example yet.
