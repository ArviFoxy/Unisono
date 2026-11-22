/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Model.RegulationRandom
public import Unisono.Spec.Topologies

/-!
# Multi-speaker modal control for a per-cycle linear-quadratic approximation

This module analyzes a discrete-time, per-cycle linear-quadratic approximation
to the playback control problem of `Unisono.Spec.Objectives`.

## Relationship to `Unisono.Spec.Objectives`

The specification's `World.syncCost`, `World.trackingCost`, and
`World.roughnessCost` are measured in seconds and accrue per output sample, and
a `Solution` is additionally subject to continuity, speed-bound, and
data-availability constraints, as well as latency, missed-sample, and
discontinuity costs. Here we isolate the quadratic position-versus-roughness
tradeoff under equal-duration cycles of length `Δt` seconds:

* Speaker `r` starts cycle `k` at position `p_{r,k}`, reads `read r k` frames
  during cycle `k` (`p_{r,k+1} = p_{r,k} + read r k`), and changes its pace by
  `w_{r,k} = read r k - read r (k - 1)` frames per cycle.
* `S r k` is the frame position due at the start of cycle `k`.
* Under linear speed ramps across each cycle of length `Δt` at sample rate `ρ`
  (`Unisono.Spec.Topologies.World.roughness_linear_ramp` and
  `Unisono.Spec.Topologies.cyclePositionWeight_eq`), a specification position
  weight `c_pos` and roughness weight `c_rough` convert to the dimensionless
  per-cycle position weight `c_cyc = (c_pos / c_rough) * Δt ^ 4` relative to
  unit per-cycle roughness weight.
* With per-cycle synchronization weight `cS` and per-cycle tracking weight `cΘ`,
  the per-cycle multi-speaker cost is

      cS * var_r (S r k - p_{r,k})
        + cΘ * mean_r (S r k - p_{r,k})²
        + mean_r w_{r,k}².

By `Unisono.Spec.modal_sq_split`, this per-cycle objective decomposes
orthogonally into two decoupled control problems:

1. **Common mode** (group mean across speakers), with per-cycle position weight
   `cΘ` and unit roughness weight.
2. **Differential mode** (zero-mean deviations across speakers), with per-cycle
   position weight `cS + cΘ` and unit roughness weight.

## Main results

* **Weight-to-gain inversion (`gainForWeight`, `weight_gainForWeight`,
  `gainForWeight_unique`).** Because `Regulation.weight (gainFor a) = a⁴`,
  `gainForWeight c = gainFor (√(√c))` is the unique `g ∈ (0, 1)` satisfying
  `weight g = c`.
* **Single-mode separation and a.e. uniqueness (`single_cost_split`,
  `single_law_optimal`, `single_law_unique_ae`).** For a fixed filtration `ℱ`
  and martingale one-step expected increments
  (`E[S_{k+2} - S_{k+1} | ℱ_k] = E[S_{k+1} - S_k | ℱ_k]`), applying
  `Unisono.Model.Regulation.law g` to the conditional-mean state minimizes the
  expected finite-horizon cost plus terminal value-to-go among all `ℱ`-adapted
  policies, uniquely almost surely.
* **Centralized full-information lip-sync benchmark (`multi_lipsync_optimal`,
  `multi_lipsync_unique_ae`, `multi_lipsync_cost_rate`,
  `multi_lipsync_law_cost_le`).** When a central controller observes one shared
  filtration `ℱ` for all speakers and `cΘ = weight gCom`,
  `cS + cΘ = weight gDiff`, the two-gain modal controller `modalRead` is the
  almost-surely unique finite-horizon minimizer and achieves the optimal
  long-run average cost per cycle (with no terminal-value dependence). Because
  decentralized star or delayed-peer policies have strictly less information
  than a shared instantaneous `ℱ`, these theorems serve as centralized lower
  bounds rather than attainable decentralized optima.
* **Centralized full-information benchmark for `cΘ = 0`
  (`multi_lowlatency_optimal`, `multi_lowlatency_unique_ae`).** When `cΘ = 0`
  and latency/missed-sample costs are omitted (`multiCycleCost cS 0`),
  `consensusRead` holds the common-mode pace constant and applies `law gDiff`
  to the differential mode. Because `multiCycleCost cS 0` does not penalize
  mean latency or missed samples, holding the mean pace constant is trivially
  optimal for that objective, but allows unbounded mean latency drift under
  clock drift in the full specification; a practical low-latency controller
  must add a small common-mode loop (`0 < gCom ≪ gDiff`) to hold the playout
  margin.
* **Decentralized pure-star decomposition (`symmetric_star_cost_split`,
  `decentralized_star_cost_eq`, `decentralized_star_uncorrelated_optimal`).**
  Splitting receiver errors and pace changes into a shared common component
  (e.g., sender-clock wander through a shared filter) and pairwise uncorrelated
  private components shows that the common component carries weight `cΘ` while
  the private components carry weight `((R - 1) / R) * cS + cΘ`. Thus
  `((R - 1) / R) * cS + cΘ` is the optimal per-receiver decentralized weight
  only when cross-receiver errors are uncorrelated (zero common-mode error);
  under a wandering sender, the best shared scalar star gain shifts toward
  `cΘ`.
* **One-hot disturbance split (`consensus_roughness_savings`).** Projecting a
  single-speaker step `Δ` onto the zero-mean subspace reduces its squared norm
  from `Δ²` to `((R - 1) / R) * Δ²`, while leaving the group mean shifted by
  `Δ / R`.

## Scope and modeling assumptions

These theorems assume:
1. A fixed filtration `ℱ` (optimality is relative to what `ℱ` observes, not
   over probing schedules or lossy front ends that shrink `ℱ`).
2. Unconstrained real-valued `read r k` in frames per cycle; continuity
   (`0 < speed < 2` frames per output sample, i.e., `0 < read < 2 M` for a
   cycle of `M` output samples), speed bounds, and data availability are
   omitted here.
3. Uniform cycle length `Δt` aligned across speakers, with linear speed ramps
   within cycles so `(Δn)²` matches per-sample roughness up to `1 / (ρ² Δt³)`.
4. Martingale expected increments, which are assumed rather than derived from
   `Unisono.Spec.SecondOrderModel` and do not hold under flicker frequency
   noise, varying block sizes, or changes of target latency.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Optimal

open MeasureTheory Unisono.Model.Regulation Unisono.Model.RegulationRandom Unisono.Spec

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-! ## Weight-to-gain inversion -/

/-- The unique gain `g ∈ (0, 1)` whose regulation weight `weight g` equals
`c > 0`. Because `Regulation.weight (gainFor a) = a ^ 4`, passing
`a = Real.sqrt (Real.sqrt c)` inverts `weight` directly. -/
def gainForWeight (c : ℝ) : ℝ := gainFor (Real.sqrt (Real.sqrt c))

theorem gainForWeight_pos {c : ℝ} (hc : 0 < c) : 0 < gainForWeight c :=
  gainFor_pos (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hc))

theorem gainForWeight_lt_one {c : ℝ} (hc : 0 < c) : gainForWeight c < 1 :=
  gainFor_lt_one (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hc))

/-- `gainForWeight c` has regulation weight exactly `c` for every `c > 0`. -/
theorem weight_gainForWeight {c : ℝ} (hc : 0 < c) : weight (gainForWeight c) = c := by
  have ha : 0 < Real.sqrt (Real.sqrt c) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hc)
  rw [gainForWeight, weight_gainFor ha]
  have hpow : Real.sqrt (Real.sqrt c) ^ 4 = (Real.sqrt (Real.sqrt c) ^ 2) ^ 2 := by ring
  rw [hpow, Real.sq_sqrt (Real.sqrt_nonneg c), Real.sq_sqrt hc.le]

/-- `gainForWeight c` is the unique gain in `(0, 1)` with weight `c`. -/
theorem gainForWeight_unique {c g : ℝ} (hc : 0 < c) (hg0 : 0 < g) (hg1 : g < 1)
    (hw : weight g = c) : g = gainForWeight c := by
  rcases lt_trichotomy g (gainForWeight c) with hlt | heq | hgt
  · exfalso
    have hlt' := weight_strictMono hg0 hlt (gainForWeight_lt_one hc)
    rw [hw, weight_gainForWeight hc] at hlt'
    exact lt_irrefl c hlt'
  · exact heq
  · exfalso
    have hlt' := weight_strictMono (gainForWeight_pos hc) hgt hg1
    rw [hw, weight_gainForWeight hc] at hlt'
    exact lt_irrefl c hlt'

/-! ## Single-channel separation (conditional mean + feedback law) -/

/-- Playback position at the start of cycle `k`, starting at `start` and
advancing by `read j` frames during cycle `j`. -/
def position (start : Ω → ℝ) (read : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => start
  | k + 1 => fun ω => position start read k ω + read k ω

/-- Frames read during the cycle immediately preceding cycle `k` (or `pace`
before cycle `0`). -/
def previous (pace : Ω → ℝ) (read : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => pace
  | k + 1 => read k

/-- Pace change at cycle `k`: `read k - previous k`. -/
def paceChange (pace : Ω → ℝ) (read : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  read k ω - previous pace read k ω

variable (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ)

/-- Conditional-mean estimate before cycle `k` of the due position's advance
`S (k + 1) - S k` over cycle `k`. -/
def advance (k : ℕ) : Ω → ℝ := μ[S (k + 1) - S k | ℱ k]

/-- Controller state `(E_k, v_k)` before cycle `k`: estimated position lag
`E_k = E[S_k | ℱ_k] - p_k` and excess previous pace `v_k = n_{k-1} - a_k`. -/
def state (start pace : Ω → ℝ) (read : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ × ℝ :=
  ((μ[S k | ℱ k]) ω - position start read k ω, previous pace read k ω - advance μ ℱ S k ω)

/-- Estimate revision `ξ_k` between cycles `k` and `k + 1`: position revision
`E[S_{k+1} | ℱ_{k+1}] - E[S_{k+1} | ℱ_k]` and negated pace revision
`a_k - a_{k+1}`. -/
def revision (k : ℕ) (ω : Ω) : ℝ × ℝ :=
  ((μ[S (k + 1) | ℱ (k + 1)]) ω - (μ[S (k + 1) | ℱ k]) ω,
    advance μ ℱ S k ω - advance μ ℱ S (k + 1) ω)

/-- Single-channel trajectory `(p_k, n_{k-1})` produced by applying `law g` to
the conditional-mean state at every cycle. -/
def lawRun (g : ℝ) (start pace : Ω → ℝ) : ℕ → Ω → ℝ × ℝ
  | 0 => fun ω => (start ω, pace ω)
  | k + 1 => fun ω =>
    let x := lawRun g start pace k ω
    let r := x.2 + law g ((μ[S k | ℱ k]) ω - x.1, x.2 - advance μ ℱ S k ω)
    (x.1 + r, r)

/-- Frames read during cycle `k` under the optimal feedback law `law g`. -/
def lawRead (g : ℝ) (start pace : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (lawRun μ ℱ S g start pace (k + 1) ω).2

/-- Irreducible per-cycle cost floor for a single mode with gain `g`: the
position estimation MMSE weighted by `weight g` plus the expected value-to-go
of the cycle's estimate revision. -/
def modeFloor (g : ℝ) (k : ℕ) : ℝ :=
  weight g * ∫ ω, (S k ω - (μ[S k | ℱ k]) ω) ^ 2 ∂μ
    + ∫ ω, value g (revision μ ℱ S k ω) ∂μ

variable {μ ℱ S}

/-- Negating an unforeseen revision remains unforeseen. -/
theorem unforeseen_neg {k : ℕ} {f : Ω → ℝ} (h : Unforeseen ℱ μ k f) :
    Unforeseen ℱ μ k fun ω => -f ω := by
  refine ⟨⟨h.1.1.neg, h.1.2.neg⟩, ?_⟩
  have hneg : μ[-f | ℱ k] =ᵐ[μ] -μ[f | ℱ k] := condExp_neg f (ℱ k)
  filter_upwards [hneg, h.2] with ω e1 e2
  change (μ[-f | ℱ k]) ω = 0
  rw [e1, Pi.neg_apply, e2]
  simp

theorem known_position {start : Ω → ℝ} {read : ℕ → Ω → ℝ} (hstart : Known ℱ μ 0 start)
    (hread : ∀ k, Known ℱ μ k (read k)) : ∀ k, Known ℱ μ k (position start read k)
  | 0 => hstart
  | k + 1 => (known_position hstart hread k).later.add (hread k).later

theorem known_previous {pace : Ω → ℝ} {read : ℕ → Ω → ℝ} (hpace : Known ℱ μ 0 pace)
    (hread : ∀ k, Known ℱ μ k (read k)) : ∀ k, Known ℱ μ k (previous pace read k)
  | 0 => hpace
  | k + 1 => (hread k).later

theorem known_condExp [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) (k : ℕ) :
    Known ℱ μ k (μ[f | ℱ k]) :=
  ⟨stronglyMeasurable_condExp, hf.condExp one_le_two⟩

theorem state_succ [IsFiniteMeasure μ] (hS : ∀ k, MemLp (S k) 2 μ) (start pace : Ω → ℝ)
    (read : ℕ → Ω → ℝ) (k : ℕ) :
    ∀ᵐ ω ∂μ, state μ ℱ S start pace read (k + 1) ω
      = next (state μ ℱ S start pace read k ω) (paceChange pace read k ω) (revision μ ℱ S k ω) := by
  have hsub : μ[S (k + 1) - S k | ℱ k] =ᵐ[μ] μ[S (k + 1) | ℱ k] - μ[S k | ℱ k] :=
    condExp_sub ((hS (k + 1)).integrable one_le_two) ((hS k).integrable one_le_two) _
  filter_upwards [hsub] with ω h
  simp only [state, next, revision, paceChange, position, previous, advance]
  rw [h, Pi.sub_apply, Prod.mk.injEq]
  constructor <;> ring

theorem path_ae [IsFiniteMeasure μ] (hS : ∀ k, MemLp (S k) 2 μ) (start pace : Ω → ℝ)
    (read : ℕ → Ω → ℝ) :
    ∀ k, path (state μ ℱ S start pace read 0) (paceChange pace read) (revision μ ℱ S) k
      =ᵐ[μ] state μ ℱ S start pace read k
  | 0 => Filter.EventuallyEq.rfl
  | k + 1 => by
    filter_upwards [path_ae hS start pace read k, state_succ (ℱ := ℱ) hS start pace read k]
      with ω h1 h2
    change next (path (state μ ℱ S start pace read 0) (paceChange pace read) (revision μ ℱ S) k ω)
      (paceChange pace read k ω) (revision μ ℱ S k ω) = _
    rw [h1, h2]

theorem admissible [IsProbabilityMeasure μ] (hS : ∀ k, MemLp (S k) 2 μ)
    (hstay : ∀ k, μ[S (k + 2) - S (k + 1) | ℱ k] =ᵐ[μ] μ[S (k + 1) - S k | ℱ k])
    {start pace : Ω → ℝ} {read : ℕ → Ω → ℝ} (hstart : Known ℱ μ 0 start)
    (hpace : Known ℱ μ 0 pace) (hread : ∀ k, Known ℱ μ k (read k)) :
    Admissible ℱ μ (state μ ℱ S start pace read 0) (paceChange pace read) (revision μ ℱ S) := by
  have hadv : ∀ k, Known ℱ μ k (advance μ ℱ S k) :=
    fun k => known_condExp ((hS (k + 1)).sub (hS k)) k
  refine ⟨(known_condExp (hS 0) 0).sub hstart, hpace.sub (hadv 0),
    fun k => (hread k).sub (known_previous hpace hread k), fun k => ?_, fun k => ?_⟩
  · exact unforeseen_revision (hS (k + 1)) k
  · have h := unforeseen_neg (unforeseen_pace hS k (hstay k))
    have hfun : (fun ω => (revision μ ℱ S k ω).2)
        = fun ω => -((μ[S (k + 2) - S (k + 1) | ℱ (k + 1)] - μ[S (k + 1) - S k | ℱ k]) ω) := by
      funext ω
      simp only [revision, advance, Pi.sub_apply, neg_sub]
    rw [hfun]
    exact h

/-- **Single-channel certainty-equivalence cost split.** For any `ℱ`-adapted
policy `read` under martingale one-step expected increments, the expected cost
over `n` cycles plus expected terminal value-to-go splits into three
policy-independent terms (estimation MMSE, initial value-to-go, and revision
costs) plus a nonnegative excess proportional to the squared deviation from
`law g`. -/
theorem single_cost_split {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) [IsProbabilityMeasure μ]
    (hS : ∀ k, MemLp (S k) 2 μ)
    (hstay : ∀ k, μ[S (k + 2) - S (k + 1) | ℱ k] =ᵐ[μ] μ[S (k + 1) - S k | ℱ k])
    {start pace : Ω → ℝ} {read : ℕ → Ω → ℝ} (hstart : Known ℱ μ 0 start)
    (hpace : Known ℱ μ 0 pace) (hread : ∀ k, Known ℱ μ k (read k)) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        ∫ ω, (weight g * (S k ω - position start read k ω) ^ 2 + paceChange pace read k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace read n ω) ∂μ
      = weight g * (∑ k ∈ Finset.range n, ∫ ω, (S k ω - (μ[S k | ℱ k]) ω) ^ 2 ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace read 0 ω) ∂μ
        + (∑ k ∈ Finset.range n, ∫ ω, value g (revision μ ℱ S k ω) ∂μ)
        + ∑ k ∈ Finset.range n, ∫ ω, (paceChange pace read k ω
            - law g (state μ ℱ S start pace read k ω)) ^ 2 / (1 - g) ∂μ := by
  have hadm := admissible hS hstay hstart hpace hread
  have hsum := mean_cost_sum hg0 hg1 hadm n
  have hpath := path_ae (ℱ := ℱ) hS start pace read
  have hcycle : ∀ k, ∫ ω, (weight g * (S k ω - position start read k ω) ^ 2
      + paceChange pace read k ω ^ 2) ∂μ
      = ∫ ω, cost g (path (state μ ℱ S start pace read 0) (paceChange pace read)
          (revision μ ℱ S) k ω) (paceChange pace read k ω) ∂μ
        + weight g * ∫ ω, (S k ω - (μ[S k | ℱ k]) ω) ^ 2 ∂μ := by
    intro k
    have hpos := known_position hstart hread k
    have hsplit := mean_square_split (hS k) hpos
    have hest := known_condExp (ℱ := ℱ) (hS k) k
    have hw : MemLp (paceChange pace read k) 2 μ :=
      (hread k).2.sub (known_previous hpace hread k).2
    have i1 : Integrable (fun ω => (S k ω - position start read k ω) ^ 2) μ :=
      ((hS k).sub hpos.2).integrable_sq
    have i2 : Integrable (fun ω => paceChange pace read k ω ^ 2) μ := hw.integrable_sq
    have i3 : Integrable (fun ω => ((μ[S k | ℱ k]) ω - position start read k ω) ^ 2) μ :=
      (hest.2.sub hpos.2).integrable_sq
    have hcost : ∫ ω, cost g (path (state μ ℱ S start pace read 0) (paceChange pace read)
        (revision μ ℱ S) k ω) (paceChange pace read k ω) ∂μ
        = weight g * ∫ ω, ((μ[S k | ℱ k]) ω - position start read k ω) ^ 2 ∂μ
          + ∫ ω, paceChange pace read k ω ^ 2 ∂μ := by
      have hae : (fun ω => cost g (path (state μ ℱ S start pace read 0) (paceChange pace read)
          (revision μ ℱ S) k ω) (paceChange pace read k ω))
          =ᵐ[μ] fun ω => weight g * ((μ[S k | ℱ k]) ω - position start read k ω) ^ 2
            + paceChange pace read k ω ^ 2 := by
        filter_upwards [hpath k] with ω h
        rw [h]
        rfl
      rw [integral_congr_ae hae, integral_add (i3.const_mul _) i2, integral_const_mul]
    rw [hcost, integral_add (i1.const_mul _) i2, integral_const_mul, hsplit]
    ring
  have hvalue_n : ∫ ω, value g (path (state μ ℱ S start pace read 0) (paceChange pace read)
      (revision μ ℱ S) n ω) ∂μ = ∫ ω, value g (state μ ℱ S start pace read n ω) ∂μ :=
    integral_congr_ae (by filter_upwards [hpath n] with ω h; rw [h])
  have hlaw : ∀ k, ∫ ω, (paceChange pace read k ω - law g (path (state μ ℱ S start pace read 0)
      (paceChange pace read) (revision μ ℱ S) k ω)) ^ 2 / (1 - g) ∂μ
      = ∫ ω, (paceChange pace read k ω
          - law g (state μ ℱ S start pace read k ω)) ^ 2 / (1 - g) ∂μ :=
    fun k => integral_congr_ae (by filter_upwards [hpath k] with ω h; rw [h])
  rw [Finset.sum_congr rfl fun k _ => hcycle k, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hvalue_n, Finset.sum_congr rfl fun k _ => hlaw k] at hsum
  linarith

theorem lawRun_eq (g : ℝ) (start pace : Ω → ℝ) :
    ∀ k, position start (lawRead μ ℱ S g start pace) k
        = (fun ω => (lawRun μ ℱ S g start pace k ω).1)
      ∧ previous pace (lawRead μ ℱ S g start pace) k
        = (fun ω => (lawRun μ ℱ S g start pace k ω).2)
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
    obtain ⟨hp, -⟩ := lawRun_eq g start pace k
    refine ⟨?_, rfl⟩
    funext ω
    change position start (lawRead μ ℱ S g start pace) k ω + lawRead μ ℱ S g start pace k ω = _
    rw [hp]
    rfl

theorem paceChange_lawRead (g : ℝ) (start pace : Ω → ℝ) (k : ℕ) (ω : Ω) :
    paceChange pace (lawRead μ ℱ S g start pace) k ω
      = law g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) k ω) := by
  obtain ⟨hp, hq⟩ := lawRun_eq (μ := μ) (ℱ := ℱ) (S := S) g start pace k
  simp only [paceChange, state, hp, hq]
  change (lawRun μ ℱ S g start pace k ω).2
      + law g ((μ[S k | ℱ k]) ω - (lawRun μ ℱ S g start pace k ω).1,
        (lawRun μ ℱ S g start pace k ω).2 - advance μ ℱ S k ω)
      - (lawRun μ ℱ S g start pace k ω).2 = _
  ring

theorem known_lawRead [IsFiniteMeasure μ] (hS : ∀ k, MemLp (S k) 2 μ) {g : ℝ}
    {start pace : Ω → ℝ} (hstart : Known ℱ μ 0 start) (hpace : Known ℱ μ 0 pace) :
    ∀ k, Known ℱ μ k (lawRead μ ℱ S g start pace k) := by
  have hstep : ∀ k, Known ℱ μ k (fun ω => (lawRun μ ℱ S g start pace k ω).1)
      → Known ℱ μ k (fun ω => (lawRun μ ℱ S g start pace k ω).2)
      → Known ℱ μ k (fun ω => (lawRun μ ℱ S g start pace (k + 1) ω).2) := by
    intro k h1 h2
    have hadv : Known ℱ μ k (advance μ ℱ S k) :=
      known_condExp ((hS (k + 1)).sub (hS k)) k
    have hE : Known ℱ μ k fun ω => (μ[S k | ℱ k]) ω - (lawRun μ ℱ S g start pace k ω).1 :=
      (known_condExp (hS k) k).sub h1
    have hv : Known ℱ μ k fun ω => (lawRun μ ℱ S g start pace k ω).2 - advance μ ℱ S k ω :=
      h2.sub hadv
    simp only [lawRun, law]
    exact h2.add ((hE.const_mul (gainE g)).sub (hv.const_mul g))
  have hrun : ∀ k, Known ℱ μ k (fun ω => (lawRun μ ℱ S g start pace k ω).1)
      ∧ Known ℱ μ k (fun ω => (lawRun μ ℱ S g start pace k ω).2) := by
    intro k
    induction k with
    | zero => exact ⟨hstart, hpace⟩
    | succ k ih =>
      have hr := hstep k ih.1 ih.2
      have hpos : Known ℱ μ k fun ω => (lawRun μ ℱ S g start pace k ω).1
          + (lawRun μ ℱ S g start pace (k + 1) ω).2 := ih.1.add hr
      exact ⟨hpos.later, hr.later⟩
  intro k
  exact hstep k (hrun k).1 (hrun k).2

/-- **Single-channel optimality of `lawRead`.** Among all `ℱ`-adapted policies
starting from `(start, pace)`, `lawRead` minimizes expected `n`-cycle cost plus
expected terminal value-to-go. -/
theorem single_law_optimal {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) [IsProbabilityMeasure μ]
    (hS : ∀ k, MemLp (S k) 2 μ)
    (hstay : ∀ k, μ[S (k + 2) - S (k + 1) | ℱ k] =ᵐ[μ] μ[S (k + 1) - S k | ℱ k])
    {start pace : Ω → ℝ} {read : ℕ → Ω → ℝ} (hstart : Known ℱ μ 0 start)
    (hpace : Known ℱ μ 0 pace) (hread : ∀ k, Known ℱ μ k (read k)) (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, (weight g * (S k ω - position start
        (lawRead μ ℱ S g start pace) k ω) ^ 2
        + paceChange pace (lawRead μ ℱ S g start pace) k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) n ω) ∂μ
      ≤ (∑ k ∈ Finset.range n,
          ∫ ω, (weight g * (S k ω - position start read k ω) ^ 2
            + paceChange pace read k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace read n ω) ∂μ := by
  rw [single_cost_split hg0 hg1 hS hstay hstart hpace (known_lawRead hS hstart hpace) n,
    single_cost_split hg0 hg1 hS hstay hstart hpace hread n]
  have hzero : ∑ k ∈ Finset.range n, ∫ ω, (paceChange pace (lawRead μ ℱ S g start pace) k ω
      - law g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) k ω)) ^ 2 / (1 - g) ∂μ
      = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp [paceChange_lawRead]
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range n, ∫ ω, (paceChange pace read k ω
      - law g (state μ ℱ S start pace read k ω)) ^ 2 / (1 - g) ∂μ := by
    have h1 : 0 < 1 - g := by linarith
    exact Finset.sum_nonneg fun k _ => integral_nonneg fun ω => by positivity
  have hstate0 : ∫ ω, value g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) 0 ω) ∂μ
      = ∫ ω, value g (state μ ℱ S start pace read 0 ω) ∂μ := rfl
  rw [hzero, hstate0]
  linarith

/-- **Single-channel almost-sure uniqueness of `lawRead`.** Any `ℱ`-adapted
policy achieving equality in `single_law_optimal` over horizon `n` coincides
almost surely with `lawRead` at every cycle `k < n`. -/
theorem single_law_unique_ae {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) [IsProbabilityMeasure μ]
    (hS : ∀ k, MemLp (S k) 2 μ)
    (hstay : ∀ k, μ[S (k + 2) - S (k + 1) | ℱ k] =ᵐ[μ] μ[S (k + 1) - S k | ℱ k])
    {start pace : Ω → ℝ} {read : ℕ → Ω → ℝ} (hstart : Known ℱ μ 0 start)
    (hpace : Known ℱ μ 0 pace) (hread : ∀ k, Known ℱ μ k (read k)) (n : ℕ)
    (heq : (∑ k ∈ Finset.range n,
        ∫ ω, (weight g * (S k ω - position start read k ω) ^ 2 + paceChange pace read k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace read n ω) ∂μ
      = (∑ k ∈ Finset.range n, ∫ ω, (weight g * (S k ω - position start
          (lawRead μ ℱ S g start pace) k ω) ^ 2
          + paceChange pace (lawRead μ ℱ S g start pace) k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) n ω) ∂μ) :
    ∀ k < n, read k =ᵐ[μ] lawRead μ ℱ S g start pace k := by
  have h1g : 0 < 1 - g := by linarith
  rw [single_cost_split hg0 hg1 hS hstay hstart hpace hread n,
    single_cost_split hg0 hg1 hS hstay hstart hpace (known_lawRead hS hstart hpace) n] at heq
  have hzero_opt : ∑ k ∈ Finset.range n, ∫ ω, (paceChange pace (lawRead μ ℱ S g start pace) k ω
      - law g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) k ω)) ^ 2 / (1 - g) ∂μ = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp [paceChange_lawRead]
  have hstate0 : ∫ ω, value g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) 0 ω) ∂μ
      = ∫ ω, value g (state μ ℱ S start pace read 0 ω) ∂μ := rfl
  have hexcess : ∑ k ∈ Finset.range n, ∫ ω, (paceChange pace read k ω
      - law g (state μ ℱ S start pace read k ω)) ^ 2 / (1 - g) ∂μ = 0 := by
    rw [hzero_opt, hstate0] at heq
    linarith
  have hstep_ae : ∀ k < n,
      ∀ᵐ ω ∂μ, paceChange pace read k ω = law g (state μ ℱ S start pace read k ω) := by
    intro k hk
    have hint_zero : ∫ ω, (paceChange pace read k ω
        - law g (state μ ℱ S start pace read k ω)) ^ 2 / (1 - g) ∂μ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        integral_nonneg fun ω => by positivity).mp hexcess k (Finset.mem_range.mpr hk)
    have hmem : MemLp (fun ω => paceChange pace read k ω
        - law g (state μ ℱ S start pace read k ω)) 2 μ := by
      have hw : MemLp (paceChange pace read k) 2 μ :=
        (hread k).2.sub (known_previous hpace hread k).2
      have hE : MemLp (fun ω => (state μ ℱ S start pace read k ω).1) 2 μ :=
        (known_condExp (hS k) k).2.sub (known_position hstart hread k).2
      have hv : MemLp (fun ω => (state μ ℱ S start pace read k ω).2) 2 μ :=
        (known_previous hpace hread k).2.sub (known_condExp ((hS (k + 1)).sub (hS k)) k).2
      have hlaw : MemLp (fun ω => law g (state μ ℱ S start pace read k ω)) 2 μ := by
        change MemLp (fun ω => gainE g * (state μ ℱ S start pace read k ω).1
            - g * (state μ ℱ S start pace read k ω).2) 2 μ
        exact (hE.const_mul (gainE g)).sub (hv.const_mul g)
      exact hw.sub hlaw
    have hint : Integrable (fun ω => (paceChange pace read k ω
        - law g (state μ ℱ S start pace read k ω)) ^ 2 / (1 - g)) μ :=
      hmem.integrable_sq.div_const (1 - g)
    have hae0 : (fun ω => (paceChange pace read k ω
        - law g (state μ ℱ S start pace read k ω)) ^ 2 / (1 - g)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hint).mp hint_zero
    filter_upwards [hae0] with ω hω
    have hsq : (paceChange pace read k ω - law g (state μ ℱ S start pace read k ω)) ^ 2 = 0 := by
      have hω' : (paceChange pace read k ω - law g (state μ ℱ S start pace read k ω)) ^ 2
          / (1 - g) = 0 := hω
      exact (div_eq_zero_iff.mp hω').resolve_right h1g.ne'
    linarith [sq_eq_zero_iff.mp hsq]
  have htraj : ∀ k ≤ n,
      (position start read k =ᵐ[μ] position start (lawRead μ ℱ S g start pace) k)
      ∧ (previous pace read k =ᵐ[μ] previous pace (lawRead μ ℱ S g start pace) k) := by
    intro k hk
    induction k with
    | zero => exact ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
    | succ k ih =>
      obtain ⟨hpos, hprev⟩ := ih (Nat.le_of_succ_le hk)
      have hread_k : read k =ᵐ[μ] lawRead μ ℱ S g start pace k := by
        filter_upwards [hpos, hprev, hstep_ae k (Nat.lt_of_succ_le hk)] with ω hp hpr hpc
        have hst : state μ ℱ S start pace read k ω
            = state μ ℱ S start pace (lawRead μ ℱ S g start pace) k ω := by
          simp only [state, hp, hpr]
        have hpc' : read k ω - previous pace read k ω
            = lawRead μ ℱ S g start pace k ω
              - previous pace (lawRead μ ℱ S g start pace) k ω := by
          calc read k ω - previous pace read k ω
              = paceChange pace read k ω := rfl
            _ = law g (state μ ℱ S start pace read k ω) := hpc
            _ = law g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) k ω) := by rw [hst]
            _ = paceChange pace (lawRead μ ℱ S g start pace) k ω :=
                (paceChange_lawRead g start pace k ω).symm
            _ = lawRead μ ℱ S g start pace k ω
                - previous pace (lawRead μ ℱ S g start pace) k ω := rfl
        linarith
      refine ⟨?_, hread_k⟩
      filter_upwards [hpos, hread_k] with ω hp hr
      change position start read k ω + read k ω
        = position start (lawRead μ ℱ S g start pace) k ω + lawRead μ ℱ S g start pace k ω
      rw [hp, hr]
  intro k hk
  exact (htraj (k + 1) hk).2

/-! ## Multi-speaker modal control (centralized full-information benchmarks) -/

section MultiSpeaker

variable {R : ℕ}

/-- Common mode (mean across `R` speakers) of a speaker-indexed random vector. -/
def commonOf (f : Fin R → Ω → ℝ) (ω : Ω) : ℝ :=
  meanFin fun r => f r ω

/-- Differential mode (deviation from the group mean) of speaker `r`. -/
def diffOf (f : Fin R → Ω → ℝ) (r : Fin R) (ω : Ω) : ℝ :=
  f r ω - commonOf f ω

/-- Multi-speaker per-cycle linear-quadratic cost with per-cycle
synchronization weight `cS`, per-cycle tracking weight `cΘ`, and unit
per-cycle roughness weight. -/
def multiCycleCost (cS cΘ : ℝ) (S : Fin R → ℕ → Ω → ℝ) (start pace : Fin R → Ω → ℝ)
    (read : Fin R → ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  cS * varFin (fun r => S r k ω - position (start r) (read r) k ω)
    + cΘ * (∑ r : Fin R, (S r k ω - position (start r) (read r) k ω) ^ 2) / R
    + (∑ r : Fin R, paceChange (pace r) (read r) k ω ^ 2) / R

theorem position_common (start : Fin R → Ω → ℝ) (read : Fin R → ℕ → Ω → ℝ)
    (k : ℕ) (ω : Ω) :
    position (commonOf start) (fun j => commonOf (fun r => read r j)) k ω
      = commonOf (fun r => position (start r) (read r) k) ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [position, ih, commonOf, meanFin]
    rw [← add_div, ← Finset.sum_add_distrib]

theorem position_diff (start : Fin R → Ω → ℝ) (read : Fin R → ℕ → Ω → ℝ)
    (r : Fin R) (k : ℕ) (ω : Ω) :
    position (diffOf start r) (fun j => diffOf (fun i => read i j) r) k ω
      = diffOf (fun i => position (start i) (read i) k) r ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [position, ih, diffOf]
    rw [← position_common start read k ω]
    have hnext := position_common start read (k + 1) ω
    simp only [position] at hnext
    rw [← hnext]
    ring

theorem paceChange_common (pace : Fin R → Ω → ℝ) (read : Fin R → ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    paceChange (commonOf pace) (fun j => commonOf (fun r => read r j)) k ω
      = commonOf (fun r => paceChange (pace r) (read r) k) ω := by
  cases k with
  | zero =>
    simp only [paceChange, previous, commonOf, meanFin]
    rw [← sub_div, ← Finset.sum_sub_distrib]
  | succ k =>
    simp only [paceChange, previous, commonOf, meanFin]
    rw [← sub_div, ← Finset.sum_sub_distrib]

theorem paceChange_diff (pace : Fin R → Ω → ℝ) (read : Fin R → ℕ → Ω → ℝ)
    (r : Fin R) (k : ℕ) (ω : Ω) :
    paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω
      = diffOf (fun i => paceChange (pace i) (read i) k) r ω := by
  cases k with
  | zero =>
    simp only [paceChange, previous, diffOf, commonOf, meanFin]
    rw [Finset.sum_sub_distrib]
    ring
  | succ k =>
    simp only [paceChange, previous, diffOf, commonOf, meanFin]
    rw [Finset.sum_sub_distrib]
    ring

/-- **Pointwise modal split of the multi-speaker per-cycle cost.** The
multi-speaker per-cycle objective decomposes orthogonally into a common-mode
problem with position weight `cΘ` and `R` differential-mode problems each with
position weight `cS + cΘ`. -/
theorem multiCycleCost_modal_split (hR : 0 < R) (cS cΘ : ℝ) (S : Fin R → ℕ → Ω → ℝ)
    (start pace : Fin R → Ω → ℝ) (read : Fin R → ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    multiCycleCost cS cΘ S start pace read k ω
      = (cΘ * (commonOf (fun r => S r k) ω
              - position (commonOf start) (fun j => commonOf (fun r => read r j)) k ω) ^ 2
            + paceChange (commonOf pace) (fun j => commonOf (fun r => read r j)) k ω ^ 2)
        + (∑ r : Fin R,
            ((cS + cΘ) * (diffOf (fun i => S i k) r ω
                - position (diffOf start r) (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
              + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2))
            / R := by
  set e : Fin R → ℝ := fun r => S r k ω - position (start r) (read r) k ω
  set w : Fin R → ℝ := fun r => paceChange (pace r) (read r) k ω
  have he_com : commonOf (fun r => S r k) ω
      - position (commonOf start) (fun j => commonOf (fun r => read r j)) k ω = meanFin e := by
    rw [position_common start read k ω]
    simp only [commonOf, meanFin, e]
    rw [← sub_div, ← Finset.sum_sub_distrib]
  have he_diff : ∀ r, diffOf (fun i => S i k) r ω
      - position (diffOf start r) (fun j => diffOf (fun i => read i j) r) k ω
      = e r - meanFin e := fun r => by
    rw [position_diff start read r k ω]
    simp only [diffOf, e]
    have : commonOf (fun i => S i k) ω - commonOf (fun i => position (start i) (read i) k) ω
        = meanFin e := by
      simp only [commonOf, meanFin, e]
      rw [← sub_div, ← Finset.sum_sub_distrib]
    linarith
  have hw_com : paceChange (commonOf pace) (fun j => commonOf (fun r => read r j)) k ω
      = meanFin w := paceChange_common pace read k ω
  have hw_diff : ∀ r, paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω
      = w r - meanFin w := fun r => paceChange_diff pace read r k ω
  unfold multiCycleCost
  rw [mul_div_assoc, modal_sq_split hR e, modal_sq_split hR w, he_com, hw_com]
  have hsum_diff :
      (∑ r : Fin R,
        ((cS + cΘ) * (diffOf (fun i => S i k) r ω
            - position (diffOf start r) (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2)) / R
        = (cS + cΘ) * varFin e + varFin w := by
    simp only [he_diff, hw_diff, Finset.sum_add_distrib, ← Finset.mul_sum, varFin]
    ring
  rw [hsum_diff]
  ring

theorem memLp_commonOf {f : Fin R → Ω → ℝ}
    (hf : ∀ r, MemLp (f r) 2 μ) : MemLp (commonOf f) 2 μ := by
  have hsum : MemLp (fun ω => ∑ r : Fin R, f r ω) 2 μ :=
    memLp_finsetSum (Finset.univ : Finset (Fin R)) (fun r _ => hf r)
  have hdiv : commonOf f = fun ω => ((R : ℝ)⁻¹) * ∑ r : Fin R, f r ω := by
    funext ω; simp [commonOf, meanFin, div_eq_inv_mul]
  rw [hdiv]
  exact hsum.const_mul _

theorem memLp_diffOf {f : Fin R → Ω → ℝ}
    (hf : ∀ r, MemLp (f r) 2 μ) (r : Fin R) : MemLp (diffOf f r) 2 μ :=
  (hf r).sub (memLp_commonOf hf)

theorem known_commonOf {k : ℕ} {f : Fin R → Ω → ℝ}
    (hf : ∀ r, Known ℱ μ k (f r)) : Known ℱ μ k (commonOf f) := by
  refine ⟨?_, memLp_commonOf (fun r => (hf r).2)⟩
  have hsum : StronglyMeasurable[ℱ k] (fun ω => ∑ r : Fin R, f r ω) := by
    have h := Finset.stronglyMeasurable_sum Finset.univ fun r _ => (hf r).1
    have hfun : (fun ω => ∑ r : Fin R, f r ω) = ∑ r : Fin R, f r := by
      funext ω; simp [Finset.sum_apply]
    rw [hfun]
    exact h
  have hdiv : commonOf f = fun ω => ((R : ℝ)⁻¹) * ∑ r : Fin R, f r ω := by
    funext ω; simp [commonOf, meanFin, div_eq_inv_mul]
  rw [hdiv]
  exact hsum.const_mul _

theorem known_diffOf {k : ℕ} {f : Fin R → Ω → ℝ}
    (hf : ∀ r, Known ℱ μ k (f r)) (r : Fin R) : Known ℱ μ k (diffOf f r) :=
  (hf r).sub (known_commonOf hf)

theorem hstay_commonOf [IsProbabilityMeasure μ] {S : Fin R → ℕ → Ω → ℝ}
    (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ k])
    (k : ℕ) :
    μ[(fun ω => commonOf (fun r => S r (k + 2)) ω) - (fun ω => commonOf (fun r => S r (k + 1)) ω)
        | ℱ k]
      =ᵐ[μ]
    μ[(fun ω => commonOf (fun r => S r (k + 1)) ω) - (fun ω => commonOf (fun r => S r k) ω)
        | ℱ k] := by
  have hint : ∀ r j, Integrable (S r (j + 1) - S r j) μ :=
    fun r j => ((hS r (j + 1)).sub (hS r j)).integrable one_le_two
  have hrew : ∀ j,
      (fun ω => commonOf (fun r => S r (j + 1)) ω) - (fun ω => commonOf (fun r => S r j) ω)
        = ((R : ℝ)⁻¹) • ∑ r : Fin R, (S r (j + 1) - S r j) := by
    intro j; funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, commonOf, meanFin, smul_eq_mul,
      div_eq_inv_mul]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [hrew (k + 1), hrew k]
  have h1 := condExp_smul (μ := μ) (m := ℱ k) ((R : ℝ)⁻¹) (∑ r : Fin R, (S r (k + 2) - S r (k + 1)))
  have h2 := condExp_smul (μ := μ) (m := ℱ k) ((R : ℝ)⁻¹) (∑ r : Fin R, (S r (k + 1) - S r k))
  have hs1 := condExp_finsetSum (μ := μ) (m := ℱ k) (s := Finset.univ)
    (fun r _ => hint r (k + 1))
  have hs2 := condExp_finsetSum (μ := μ) (m := ℱ k) (s := Finset.univ)
    (fun r _ => hint r k)
  have hsum_ae : (∑ r : Fin R, μ[S r (k + 2) - S r (k + 1) | ℱ k])
      =ᵐ[μ] (∑ r : Fin R, μ[S r (k + 1) - S r k | ℱ k]) := by
    have hall : ∀ᵐ ω ∂μ, ∀ r : Fin R,
        (μ[S r (k + 2) - S r (k + 1) | ℱ k]) ω = (μ[S r (k + 1) - S r k | ℱ k]) ω :=
      ae_all_iff.mpr fun r => hstay r k
    filter_upwards [hall] with ω h
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => h r
  filter_upwards [h1, h2, hs1, hs2, hsum_ae] with ω e1 e2 es1 es2 esum
  rw [e1, e2]
  simp only [Pi.smul_apply]
  rw [es1, es2, esum]

theorem hstay_diffOf [IsProbabilityMeasure μ] {S : Fin R → ℕ → Ω → ℝ}
    (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ k])
    (r : Fin R) (k : ℕ) :
    μ[(fun ω => diffOf (fun i => S i (k + 2)) r ω) - (fun ω => diffOf (fun i => S i (k + 1)) r ω)
        | ℱ k]
      =ᵐ[μ]
    μ[(fun ω => diffOf (fun i => S i (k + 1)) r ω) - (fun ω => diffOf (fun i => S i k) r ω)
        | ℱ k] := by
  have hint_r : ∀ j, Integrable (S r (j + 1) - S r j) μ :=
    fun j => ((hS r (j + 1)).sub (hS r j)).integrable one_le_two
  have hint_c : ∀ j, Integrable
      ((fun ω => commonOf (fun i => S i (j + 1)) ω) - (fun ω => commonOf (fun i => S i j) ω)) μ :=
    fun j => ((memLp_commonOf fun i => hS i (j + 1)).sub
      (memLp_commonOf fun i => hS i j)).integrable one_le_two
  have hrew : ∀ j,
      (fun ω => diffOf (fun i => S i (j + 1)) r ω) - (fun ω => diffOf (fun i => S i j) r ω)
        = (S r (j + 1) - S r j)
          - ((fun ω => commonOf (fun i => S i (j + 1)) ω)
              - (fun ω => commonOf (fun i => S i j) ω)) := by
    intro j; funext ω; simp [diffOf]; ring
  rw [hrew (k + 1), hrew k]
  have hs1 := condExp_sub (hint_r (k + 1)) (hint_c (k + 1)) (ℱ k)
  have hs2 := condExp_sub (hint_r k) (hint_c k) (ℱ k)
  have hc := hstay_commonOf hS hstay k
  filter_upwards [hs1, hs2, hstay r k, hc] with ω e1 e2 er ec
  rw [e1, e2]
  simp only [Pi.sub_apply]
  rw [er, ec]

/-- **Two-gain modal controller for lip-sync mode.** Combines `lawRead` with
gain `gCom` on the common mode and `lawRead` with gain `gDiff` on each
speaker's differential mode. Requires one shared filtration `ℱ` across all
speakers. -/
def modalRead (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : Fin R → ℕ → Ω → ℝ)
    (gCom gDiff : ℝ) (start pace : Fin R → Ω → ℝ) (r : Fin R) (k : ℕ) (ω : Ω) : ℝ :=
  lawRead μ ℱ (fun j => commonOf fun i => S i j) gCom (commonOf start) (commonOf pace) k ω
    + lawRead μ ℱ (fun j => diffOf (fun i => S i j) r) gDiff (diffOf start r) (diffOf pace r) k ω

/-- **Constant-mean differential controller for `multiCycleCost cS 0`.** Keeps
the common-mode pace constant (`read_bar k = commonOf pace`, zero common-mode
roughness) and applies `lawRead` with gain `gDiff` to the zero-mean
differential mode. Requires one shared filtration `ℱ` across all speakers. -/
def consensusRead (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : Fin R → ℕ → Ω → ℝ)
    (gDiff : ℝ) (start pace : Fin R → Ω → ℝ) (r : Fin R) (k : ℕ) (ω : Ω) : ℝ :=
  commonOf pace ω
    + lawRead μ ℱ (fun j => diffOf (fun i => S i j) r) gDiff (diffOf start r) (diffOf pace r) k ω

/-- For any zero-sum collection of initial states and targets, the differential
`lawRun` trajectories sum to zero across speakers almost surely at every cycle. -/
theorem sum_lawRun_diff_ae [IsProbabilityMeasure μ] (hR : 0 < R) (S : Fin R → ℕ → Ω → ℝ)
    (hS : ∀ r k, MemLp (S r k) 2 μ) (g : ℝ) (start pace : Fin R → Ω → ℝ) :
    ∀ k, ∀ᵐ ω ∂μ,
      (∑ r : Fin R, (lawRun μ ℱ (fun j => diffOf (fun i => S i j) r) g
          (diffOf start r) (diffOf pace r) k ω).1 = 0)
      ∧ (∑ r : Fin R, (lawRun μ ℱ (fun j => diffOf (fun i => S i j) r) g
          (diffOf start r) (diffOf pace r) k ω).2 = 0) := by
  have hsum_diff : ∀ f : Fin R → ℝ, ∑ r : Fin R, (f r - meanFin f) = 0 := by
    intro f
    have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, meanFin]
    field_simp
    ring
  intro k
  induction k with
  | zero =>
    filter_upwards with ω
    exact ⟨hsum_diff (fun r => start r ω), hsum_diff (fun r => pace r ω)⟩
  | succ k ih =>
    have hS_sum : (∑ r : Fin R, μ[fun ω => diffOf (fun i => S i k) r ω | ℱ k]) =ᵐ[μ] 0 := by
      have h1 := condExp_finsetSum (μ := μ) (m := ℱ k) (s := Finset.univ)
        (fun r _ => (memLp_diffOf (fun i => hS i k) r).integrable one_le_two)
      have h0 : (∑ r : Fin R, fun ω => diffOf (fun i => S i k) r ω) = (0 : Ω → ℝ) := by
        funext ω
        simp only [Finset.sum_apply, Pi.zero_apply, diffOf, commonOf]
        exact hsum_diff (fun r => S r k ω)
      filter_upwards [h1] with ω e
      rw [← e, h0, condExp_zero]
    have hadv_sum : (∑ r : Fin R, advance μ ℱ (fun j => diffOf (fun i => S i j) r) k) =ᵐ[μ] 0 := by
      have h1 := condExp_finsetSum (μ := μ) (m := ℱ k) (s := Finset.univ)
        (fun r _ => ((memLp_diffOf (fun i => hS i (k + 1)) r).sub
          (memLp_diffOf (fun i => hS i k) r)).integrable one_le_two)
      have h0 : (∑ r : Fin R, ((fun ω => diffOf (fun i => S i (k + 1)) r ω)
          - (fun ω => diffOf (fun i => S i k) r ω))) = (0 : Ω → ℝ) := by
        funext ω
        simp only [Finset.sum_apply, Pi.sub_apply, Pi.zero_apply]
        rw [Finset.sum_sub_distrib]
        simp only [diffOf, commonOf]
        rw [hsum_diff (fun r => S r (k + 1) ω), hsum_diff (fun r => S r k ω), sub_self]
      filter_upwards [h1] with ω e
      simp only [advance]
      rw [← e, h0, condExp_zero]
    filter_upwards [ih, hS_sum, hadv_sum] with ω ⟨hp, hv⟩ hS0 ha0
    simp only [Finset.sum_apply, Pi.zero_apply] at hS0 ha0
    have hr_sum : ∑ r : Fin R,
        ((lawRun μ ℱ (fun j => diffOf (fun i => S i j) r) g (diffOf start r) (diffOf pace r) k ω).2
          + law g ((μ[fun ω => diffOf (fun i => S i k) r ω | ℱ k]) ω
              - (lawRun μ ℱ (fun j => diffOf (fun i => S i j) r) g
                  (diffOf start r) (diffOf pace r) k ω).1,
            (lawRun μ ℱ (fun j => diffOf (fun i => S i j) r) g
                  (diffOf start r) (diffOf pace r) k ω).2
              - advance μ ℱ (fun j => diffOf (fun i => S i j) r) k ω)) = 0 := by
      simp only [law, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        mul_sub, hv, hp, hS0, ha0]
      ring
    refine ⟨?_, hr_sum⟩
    simp only [lawRun]
    rw [Finset.sum_add_distrib, hp, hr_sum, add_zero]

/-- **Differential reads sum to zero almost surely.** Consequently, `modalRead`
has common mode equal to the common `lawRead` and differential mode equal to
the differential `lawRead` a.e. -/
theorem modalRead_modes_ae [IsProbabilityMeasure μ] (hR : 0 < R) (S : Fin R → ℕ → Ω → ℝ)
    (hS : ∀ r k, MemLp (S r k) 2 μ) (gCom gDiff : ℝ) (start pace : Fin R → Ω → ℝ) (k : ℕ) :
    (∀ᵐ ω ∂μ, commonOf (fun r => modalRead μ ℱ S gCom gDiff start pace r k) ω
        = lawRead μ ℱ (fun j => commonOf fun i => S i j) gCom (commonOf start) (commonOf pace) k ω)
      ∧ (∀ r, ∀ᵐ ω ∂μ, diffOf (fun i => modalRead μ ℱ S gCom gDiff start pace i k) r ω
        = lawRead μ ℱ (fun j => diffOf (fun i => S i j) r) gDiff (diffOf start r) (diffOf pace r) k ω) := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hsum0 := sum_lawRun_diff_ae (μ := μ) (ℱ := ℱ) hR S hS gDiff start pace (k + 1)
  have hcom : ∀ᵐ ω ∂μ, commonOf (fun r => modalRead μ ℱ S gCom gDiff start pace r k) ω
      = lawRead μ ℱ (fun j => commonOf fun i => S i j) gCom (commonOf start) (commonOf pace) k ω := by
    filter_upwards [hsum0] with ω ⟨_, hr0⟩
    simp only [commonOf, meanFin, modalRead, lawRead, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hr0, add_zero]
    field_simp
  refine ⟨hcom, fun r => ?_⟩
  filter_upwards [hcom] with ω hc
  simp only [diffOf, hc, modalRead]
  ring

/-- `consensusRead` has constant common mode `commonOf pace` (zero common-mode
pace change) and differential mode equal to `lawRead gDiff` a.e. -/
theorem consensusRead_modes_ae [IsProbabilityMeasure μ] (hR : 0 < R) (S : Fin R → ℕ → Ω → ℝ)
    (hS : ∀ r k, MemLp (S r k) 2 μ) (gDiff : ℝ) (start pace : Fin R → Ω → ℝ) (k : ℕ) :
    (∀ᵐ ω ∂μ, commonOf (fun r => consensusRead μ ℱ S gDiff start pace r k) ω = commonOf pace ω)
      ∧ (∀ r, ∀ᵐ ω ∂μ, diffOf (fun i => consensusRead μ ℱ S gDiff start pace i k) r ω
        = lawRead μ ℱ (fun j => diffOf (fun i => S i j) r) gDiff (diffOf start r) (diffOf pace r) k ω) := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hsum0 := sum_lawRun_diff_ae (μ := μ) (ℱ := ℱ) hR S hS gDiff start pace (k + 1)
  have hcom : ∀ᵐ ω ∂μ, commonOf (fun r => consensusRead μ ℱ S gDiff start pace r k) ω
      = commonOf pace ω := by
    filter_upwards [hsum0] with ω ⟨_, hr0⟩
    simp only [commonOf, meanFin, consensusRead, lawRead, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hr0, add_zero]
    field_simp
  refine ⟨hcom, fun r => ?_⟩
  filter_upwards [hcom] with ω hc
  simp only [diffOf, hc, consensusRead]
  ring

private theorem pos_prev_pace_ae {st pc : Ω → ℝ} {r1 r2 : ℕ → Ω → ℝ}
    (heq : ∀ᵐ ω ∂μ, ∀ j, r1 j ω = r2 j ω) (k : ℕ) :
    (∀ᵐ ω ∂μ, position st r1 k ω = position st r2 k ω)
      ∧ (∀ᵐ ω ∂μ, paceChange pc r1 k ω = paceChange pc r2 k ω)
      ∧ (∀ᵐ ω ∂μ, previous pc r1 k ω = previous pc r2 k ω) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [heq] with ω h
    induction k with
    | zero => rfl
    | succ k ih => simp [position, ih, h k]
  · filter_upwards [heq] with ω h
    cases k <;> simp [paceChange, previous, h]
  · filter_upwards [heq] with ω h
    cases k <;> simp [previous, h]

private theorem multiCycleCost_integral_split [IsProbabilityMeasure μ] (hR : 0 < R)
    {gCom gDiff cS cΘ : ℝ} (hcΘ : cΘ = weight gCom) (hcSD : cS + cΘ = weight gDiff)
    {S : Fin R → ℕ → Ω → ℝ} (hS : ∀ r k, MemLp (S r k) 2 μ)
    {start pace : Fin R → Ω → ℝ} {rd : Fin R → ℕ → Ω → ℝ}
    (hstart : ∀ r, Known ℱ μ 0 (start r)) (hpace : ∀ r, Known ℱ μ 0 (pace r))
    (hrd : ∀ r k, Known ℱ μ k (rd r k)) (k : ℕ) :
    let Sc : ℕ → Ω → ℝ := fun j => commonOf fun i => S i j
    let Sd : Fin R → ℕ → Ω → ℝ := fun r j => diffOf (fun i => S i j) r
    ∫ ω, multiCycleCost cS cΘ S start pace rd k ω ∂μ
      = (∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
            (fun j => commonOf fun i => rd i j) k ω) ^ 2
          + paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2) ∂μ)
        + (∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) ∂μ) / R := by
  intro Sc Sd
  have hSc : ∀ j, MemLp (Sc j) 2 μ := fun j => memLp_commonOf fun r => hS r j
  have hSd : ∀ r j, MemLp (Sd r j) 2 μ := fun r j => memLp_diffOf (fun i => hS i j) r
  have hstartC : Known ℱ μ 0 (commonOf start) := known_commonOf hstart
  have hpaceC : Known ℱ μ 0 (commonOf pace) := known_commonOf hpace
  have hstartD : ∀ r, Known ℱ μ 0 (diffOf start r) := fun r => known_diffOf hstart r
  have hpaceD : ∀ r, Known ℱ μ 0 (diffOf pace r) := fun r => known_diffOf hpace r
  have hrdC : ∀ j, Known ℱ μ j (commonOf fun i => rd i j) :=
    fun j => known_commonOf fun i => hrd i j
  have hrdD : ∀ r j, Known ℱ μ j (diffOf (fun i => rd i j) r) :=
    fun r j => known_diffOf (fun i => hrd i j) r
  have hpt : ∀ ω, multiCycleCost cS cΘ S start pace rd k ω
      = (weight gCom * (Sc k ω - position (commonOf start)
            (fun j => commonOf fun i => rd i j) k ω) ^ 2
          + paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2)
        + (∑ r : Fin R, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2)) / R := by
    intro ω
    rw [multiCycleCost_modal_split hR cS cΘ S start pace rd k ω, hcSD, hcΘ]
  have hiC : Integrable (fun ω =>
      weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => rd i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2) μ :=
    (((hSc k).sub (known_position hstartC hrdC k).2).integrable_sq.const_mul _).add
      (((hrdC k).2.sub (known_previous hpaceC hrdC k).2).integrable_sq)
  have hiD : ∀ r : Fin R, Integrable (fun ω =>
      weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) μ := fun r =>
    (((hSd r k).sub (known_position (hstartD r) (hrdD r) k).2).integrable_sq.const_mul _).add
      (((hrdD r k).2.sub (known_previous (hpaceD r) (hrdD r) k).2).integrable_sq)
  simp_rw [hpt]
  rw [integral_add hiC ((integrable_finsetSum Finset.univ fun r _ => hiD r).div_const _),
    integral_div, integral_finsetSum Finset.univ fun r _ => hiD r]

/-- **Centralized full-information lip-sync benchmark.** For any `R > 0`
speakers controlled from one shared filtration `ℱ` with per-cycle weights
`cΘ = weight gCom` and `cS + cΘ = weight gDiff` (`0 < gCom, gDiff < 1`), the
two-gain modal controller `modalRead` is causal (`Known`) and minimizes the
expected `n`-cycle cost plus expected modal terminal value-to-go among all
`ℱ`-adapted multi-speaker policies. Because decentralized star or delayed-peer
policies use strictly less information than a shared instantaneous `ℱ`, this
provides a centralized lower bound. -/
theorem multi_lipsync_optimal [IsProbabilityMeasure μ] (hR : 0 < R)
    {gCom gDiff cS cΘ : ℝ} (hgC0 : 0 < gCom) (hgC1 : gCom < 1)
    (hgD0 : 0 < gDiff) (hgD1 : gDiff < 1)
    (hcΘ : cΘ = weight gCom) (hcSD : cS + cΘ = weight gDiff)
    {S : Fin R → ℕ → Ω → ℝ} (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ k])
    {start pace : Fin R → Ω → ℝ} {read : Fin R → ℕ → Ω → ℝ}
    (hstart : ∀ r, Known ℱ μ 0 (start r)) (hpace : ∀ r, Known ℱ μ 0 (pace r))
    (hread : ∀ r k, Known ℱ μ k (read r k)) (n : ℕ) :
    let opt := modalRead μ ℱ S gCom gDiff start pace
    (∀ r k, Known ℱ μ k (opt r k))
    ∧ ((∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace opt k ω ∂μ)
          + ∫ ω, value gCom (state μ ℱ (fun j => commonOf fun i => S i j)
              (commonOf start) (commonOf pace) (fun j => commonOf fun i => opt i j) n ω) ∂μ
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
              (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ) / R
        ≤ (∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace read k ω ∂μ)
          + ∫ ω, value gCom (state μ ℱ (fun j => commonOf fun i => S i j)
              (commonOf start) (commonOf pace) (fun j => commonOf fun i => read i j) n ω) ∂μ
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
              (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  set opt := modalRead μ ℱ S gCom gDiff start pace
  set Sc : ℕ → Ω → ℝ := fun j => commonOf fun i => S i j
  set Sd : Fin R → ℕ → Ω → ℝ := fun r j => diffOf (fun i => S i j) r
  have hSc : ∀ k, MemLp (Sc k) 2 μ := fun k => memLp_commonOf fun r => hS r k
  have hSd : ∀ r k, MemLp (Sd r k) 2 μ := fun r k => memLp_diffOf (fun i => hS i k) r
  have hstayC : ∀ k, μ[Sc (k + 2) - Sc (k + 1) | ℱ k] =ᵐ[μ] μ[Sc (k + 1) - Sc k | ℱ k] :=
    fun k => hstay_commonOf hS hstay k
  have hstayD : ∀ r k, μ[Sd r (k + 2) - Sd r (k + 1) | ℱ k] =ᵐ[μ] μ[Sd r (k + 1) - Sd r k | ℱ k] :=
    fun r k => hstay_diffOf hS hstay r k
  have hstartC : Known ℱ μ 0 (commonOf start) := known_commonOf hstart
  have hpaceC : Known ℱ μ 0 (commonOf pace) := known_commonOf hpace
  have hstartD : ∀ r, Known ℱ μ 0 (diffOf start r) := fun r => known_diffOf hstart r
  have hpaceD : ∀ r, Known ℱ μ 0 (diffOf pace r) := fun r => known_diffOf hpace r
  have hopt_known : ∀ r k, Known ℱ μ k (opt r k) := fun r k =>
    (known_lawRead hSc hstartC hpaceC k).add (known_lawRead (hSd r) (hstartD r) (hpaceD r) k)
  refine ⟨hopt_known, ?_⟩
  have hsplit_int : ∀ (rd : Fin R → ℕ → Ω → ℝ), (∀ r k, Known ℱ μ k (rd r k)) →
      ∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace rd k ω ∂μ
        = (∑ k ∈ Finset.range n, ∫ ω,
            (weight gCom * (Sc k ω - position (commonOf start)
                (fun j => commonOf fun i => rd i j) k ω) ^ 2
              + paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2) ∂μ)
          + (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
            (weight gDiff * (Sd r k ω - position (diffOf start r)
                (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
              + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) ∂μ) / R := by
    intro rd hrd
    rw [Finset.sum_congr rfl fun k _ =>
      multiCycleCost_integral_split hR hcΘ hcSD hS hstart hpace hrd k,
      Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_comm]
  rw [hsplit_int opt hopt_known, hsplit_int read hread]
  have hmodes := fun j => modalRead_modes_ae (μ := μ) (ℱ := ℱ) hR S hS gCom gDiff start pace j
  have hcom_all : ∀ᵐ ω ∂μ, ∀ j,
      commonOf (fun i => opt i j) ω = lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace) j ω :=
    ae_all_iff.mpr fun j => (hmodes j).1
  have hdiff_all : ∀ r, ∀ᵐ ω ∂μ, ∀ j,
      diffOf (fun i => opt i j) r ω
        = lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r) j ω :=
    fun r => ae_all_iff.mpr fun j => (hmodes j).2 r
  have hC_opt := single_law_optimal hgC0 hgC1 hSc hstayC hstartC hpaceC
    (fun k => known_commonOf fun r => hread r k) n
  have hC_eq :
      (∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => opt i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => opt i j) k ω ^ 2) ∂μ)
        + ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
            (fun j => commonOf fun i => opt i j) n ω) ∂μ
      = (∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) k ω) ^ 2
        + paceChange (commonOf pace)
          (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) k ω ^ 2) ∂μ)
        + ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
            (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) n ω) ∂μ := by
    congr 1
    · refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
      obtain ⟨hp, hw, _⟩ := pos_prev_pace_ae (st := commonOf start) (pc := commonOf pace) hcom_all k
      filter_upwards [hp, hw] with ω ep ew
      rw [ep, ew]
    · refine integral_congr_ae ?_
      obtain ⟨hp, _, hpr⟩ := pos_prev_pace_ae (st := commonOf start) (pc := commonOf pace) hcom_all n
      filter_upwards [hp, hpr] with ω ep epr
      simp only [state, ep, epr]
  have hD_opt : ∀ r : Fin R,
      (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ)
        + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ
      ≤ (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ)
        + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => read i j) r) n ω) ∂μ := by
    intro r
    have hD_eq :
        (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ)
          + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
              (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ
        = (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) k ω) ^ 2
          + paceChange (diffOf pace r)
            (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) k ω ^ 2) ∂μ)
          + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
              (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) n ω) ∂μ := by
      congr 1
      · refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
        obtain ⟨hp, hw, _⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
          (hdiff_all r) k
        filter_upwards [hp, hw] with ω ep ew
        rw [ep, ew]
      · refine integral_congr_ae ?_
        obtain ⟨hp, _, hpr⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
          (hdiff_all r) n
        filter_upwards [hp, hpr] with ω ep epr
        simp only [state, ep, epr]
    rw [hD_eq]
    exact single_law_optimal hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r)
      (fun k => known_diffOf (fun i => hread i k) r) n
  have hD_sum :
      ((∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ)
        + ∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ) / R
      ≤ ((∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ)
        + ∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R := by
    apply div_le_div_of_nonneg_right _ hRpos.le
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r _ => hD_opt r
  have hC_opt' :
      (∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => opt i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => opt i j) k ω ^ 2) ∂μ)
        + ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
            (fun j => commonOf fun i => opt i j) n ω) ∂μ
      ≤ (∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => read i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2) ∂μ)
        + ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
            (fun j => commonOf fun i => read i j) n ω) ∂μ := by
    rw [hC_eq]; exact hC_opt
  rw [add_div, add_div] at hD_sum
  change _ + _ + _ + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r)
      (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ) / R
    ≤ _ + _ + _ + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r)
      (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R
  linarith

/-- **Almost-sure uniqueness of `modalRead` in the centralized lip-sync
benchmark.** Any `ℱ`-adapted multi-speaker policy achieving equality in
`multi_lipsync_optimal` over horizon `n` coincides almost surely with
`modalRead` for every speaker `r` and cycle `k < n`. -/
theorem multi_lipsync_unique_ae [IsProbabilityMeasure μ] (hR : 0 < R)
    {gCom gDiff cS cΘ : ℝ} (hgC0 : 0 < gCom) (hgC1 : gCom < 1)
    (hgD0 : 0 < gDiff) (hgD1 : gDiff < 1)
    (hcΘ : cΘ = weight gCom) (hcSD : cS + cΘ = weight gDiff)
    {S : Fin R → ℕ → Ω → ℝ} (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ k])
    {start pace : Fin R → Ω → ℝ} {read : Fin R → ℕ → Ω → ℝ}
    (hstart : ∀ r, Known ℱ μ 0 (start r)) (hpace : ∀ r, Known ℱ μ 0 (pace r))
    (hread : ∀ r k, Known ℱ μ k (read r k)) (n : ℕ)
    (heq : let opt := modalRead μ ℱ S gCom gDiff start pace
      (∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace read k ω ∂μ)
          + ∫ ω, value gCom (state μ ℱ (fun j => commonOf fun i => S i j)
              (commonOf start) (commonOf pace) (fun j => commonOf fun i => read i j) n ω) ∂μ
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
              (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R
        = (∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace opt k ω ∂μ)
          + ∫ ω, value gCom (state μ ℱ (fun j => commonOf fun i => S i j)
              (commonOf start) (commonOf pace) (fun j => commonOf fun i => opt i j) n ω) ∂μ
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
              (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ) / R) :
    ∀ r, ∀ k < n, read r k =ᵐ[μ] modalRead μ ℱ S gCom gDiff start pace r k := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  set opt := modalRead μ ℱ S gCom gDiff start pace
  set Sc : ℕ → Ω → ℝ := fun j => commonOf fun i => S i j
  set Sd : Fin R → ℕ → Ω → ℝ := fun r j => diffOf (fun i => S i j) r
  have hSc : ∀ k, MemLp (Sc k) 2 μ := fun k => memLp_commonOf fun r => hS r k
  have hSd : ∀ r k, MemLp (Sd r k) 2 μ := fun r k => memLp_diffOf (fun i => hS i k) r
  have hstayC : ∀ k, μ[Sc (k + 2) - Sc (k + 1) | ℱ k] =ᵐ[μ] μ[Sc (k + 1) - Sc k | ℱ k] :=
    fun k => hstay_commonOf hS hstay k
  have hstayD : ∀ r k, μ[Sd r (k + 2) - Sd r (k + 1) | ℱ k] =ᵐ[μ] μ[Sd r (k + 1) - Sd r k | ℱ k] :=
    fun r k => hstay_diffOf hS hstay r k
  have hstartC : Known ℱ μ 0 (commonOf start) := known_commonOf hstart
  have hpaceC : Known ℱ μ 0 (commonOf pace) := known_commonOf hpace
  have hstartD : ∀ r, Known ℱ μ 0 (diffOf start r) := fun r => known_diffOf hstart r
  have hpaceD : ∀ r, Known ℱ μ 0 (diffOf pace r) := fun r => known_diffOf hpace r
  have hopt_known : ∀ r k, Known ℱ μ k (opt r k) := fun r k =>
    (known_lawRead hSc hstartC hpaceC k).add (known_lawRead (hSd r) (hstartD r) (hpaceD r) k)
  have hsplit_int : ∀ (rd : Fin R → ℕ → Ω → ℝ), (∀ r k, Known ℱ μ k (rd r k)) →
      ∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace rd k ω ∂μ
        = (∑ k ∈ Finset.range n, ∫ ω,
            (weight gCom * (Sc k ω - position (commonOf start)
                (fun j => commonOf fun i => rd i j) k ω) ^ 2
              + paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2) ∂μ)
          + (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
            (weight gDiff * (Sd r k ω - position (diffOf start r)
                (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
              + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) ∂μ) / R := by
    intro rd hrd
    rw [Finset.sum_congr rfl fun k _ =>
      multiCycleCost_integral_split hR hcΘ hcSD hS hstart hpace hrd k,
      Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_comm]
  have hmodes := fun j => modalRead_modes_ae (μ := μ) (ℱ := ℱ) hR S hS gCom gDiff start pace j
  have hcom_all : ∀ᵐ ω ∂μ, ∀ j,
      commonOf (fun i => opt i j) ω = lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace) j ω :=
    ae_all_iff.mpr fun j => (hmodes j).1
  have hdiff_all : ∀ r, ∀ᵐ ω ∂μ, ∀ j,
      diffOf (fun i => opt i j) r ω
        = lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r) j ω :=
    fun r => ae_all_iff.mpr fun j => (hmodes j).2 r
  set Jc : (ℕ → Ω → ℝ) → ℝ := fun rd =>
    (∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start) rd k ω) ^ 2
      + paceChange (commonOf pace) rd k ω ^ 2) ∂μ)
    + ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace) rd n ω) ∂μ
  set Jd : Fin R → (ℕ → Ω → ℝ) → ℝ := fun r rd =>
    (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r) rd k ω) ^ 2
      + paceChange (diffOf pace r) rd k ω ^ 2) ∂μ)
    + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r) rd n ω) ∂μ
  have hJc_opt : Jc (fun j => commonOf fun i => opt i j)
      = Jc (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) := by
    dsimp only [Jc]; congr 1
    · refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
      obtain ⟨hp, hw, _⟩ := pos_prev_pace_ae (st := commonOf start) (pc := commonOf pace) hcom_all k
      filter_upwards [hp, hw] with ω ep ew; rw [ep, ew]
    · refine integral_congr_ae ?_
      obtain ⟨hp, _, hpr⟩ := pos_prev_pace_ae (st := commonOf start) (pc := commonOf pace) hcom_all n
      filter_upwards [hp, hpr] with ω ep epr; simp only [state, ep, epr]
  have hJd_opt : ∀ r, Jd r (fun j => diffOf (fun i => opt i j) r)
      = Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) := by
    intro r; dsimp only [Jd]; congr 1
    · refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
      obtain ⟨hp, hw, _⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
        (hdiff_all r) k
      filter_upwards [hp, hw] with ω ep ew; rw [ep, ew]
    · refine integral_congr_ae ?_
      obtain ⟨hp, _, hpr⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
        (hdiff_all r) n
      filter_upwards [hp, hpr] with ω ep epr; simp only [state, ep, epr]
  have hJc_le : Jc (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace))
      ≤ Jc (fun j => commonOf fun i => read i j) :=
    single_law_optimal hgC0 hgC1 hSc hstayC hstartC hpaceC
      (fun k => known_commonOf fun r => hread r k) n
  have hJd_le : ∀ r, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))
      ≤ Jd r (fun j => diffOf (fun i => read i j) r) := fun r =>
    single_law_optimal hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r)
      (fun k => known_diffOf (fun i => hread i k) r) n
  have htot : Jc (fun j => commonOf fun i => read i j)
        + (∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)) / R
      = Jc (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace))
        + (∑ r : Fin R, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))) / R := by
    dsimp only [opt] at heq
    rw [hsplit_int read hread, hsplit_int opt hopt_known] at heq
    have h1 : Jc (fun j => commonOf fun i => read i j)
          + (∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)) / R
        = Jc (fun j => commonOf fun i => opt i j)
          + (∑ r : Fin R, Jd r (fun j => diffOf (fun i => opt i j) r)) / R := by
      dsimp only [Jc, Jd]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_div, add_div]
      linarith
    rw [h1, hJc_opt]
    congr 2
    exact Finset.sum_congr rfl fun r _ => hJd_opt r
  have hsum_le : (∑ r : Fin R, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))) / R
      ≤ (∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)) / R :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun r _ => hJd_le r) hRpos.le
  have hJc_eq : Jc (fun j => commonOf fun i => read i j)
      = Jc (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) := by linarith
  have hJd_sum_eq : ∑ r : Fin R, (Jd r (fun j => diffOf (fun i => read i j) r)
      - Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))) = 0 := by
    have hdiv_eq : (∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)) / R
        = (∑ r : Fin R, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))) / R := by
      linarith
    have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
    have hsum_eq : ∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)
        = ∑ r : Fin R, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) := by
      field_simp at hdiv_eq
      exact hdiv_eq
    rw [Finset.sum_sub_distrib, hsum_eq, sub_self]
  have hJd_eq : ∀ r, Jd r (fun j => diffOf (fun i => read i j) r)
      = Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) := by
    intro r
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.mpr (hJd_le i)).mp
      hJd_sum_eq r (Finset.mem_univ r)
    linarith
  have hC_ae := single_law_unique_ae hgC0 hgC1 hSc hstayC hstartC hpaceC
    (fun k => known_commonOf fun i => hread i k) n hJc_eq
  have hD_ae : ∀ r, ∀ k < n, diffOf (fun i => read i k) r
      =ᵐ[μ] lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r) k := fun r =>
    single_law_unique_ae hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r)
      (fun k => known_diffOf (fun i => hread i k) r) n (hJd_eq r)
  intro r k hk
  filter_upwards [hC_ae k hk, hD_ae r k hk] with ω hc hd
  change read r k ω = modalRead μ ℱ S gCom gDiff start pace r k ω
  have hdecomp : read r k ω = commonOf (fun i => read i k) ω + diffOf (fun i => read i k) r ω := by
    simp only [diffOf]; ring
  rw [hdecomp, hc, hd]
  rfl

/-- **Long-run average cost-rate lower bound (centralized lip-sync benchmark).**
If the combined modal per-cycle irreducible cost floor (estimation MMSE plus
expected revision value-to-go in the common mode and average differential mode)
is at least `s` at every cycle, and the combined squared position-revision
second moment is bounded by `q`, then no `ℱ`-adapted multi-speaker policy can
keep its average expected cost per cycle below `s - ε` for all large horizons
`n` (with no terminal-value term). -/
theorem multi_lipsync_cost_rate [IsProbabilityMeasure μ] (hR : 0 < R)
    {gCom gDiff cS cΘ s q : ℝ} (hgC0 : 0 < gCom) (hgC1 : gCom < 1)
    (hgD0 : 0 < gDiff) (hgD1 : gDiff < 1)
    (hcΘ : cΘ = weight gCom) (hcSD : cS + cΘ = weight gDiff)
    {S : Fin R → ℕ → Ω → ℝ} (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ k])
    {start pace : Fin R → Ω → ℝ} {read : Fin R → ℕ → Ω → ℝ}
    (hstart : ∀ r, Known ℱ μ 0 (start r)) (hpace : ∀ r, Known ℱ μ 0 (pace r))
    (hread : ∀ r k, Known ℱ μ k (read r k))
    (hs : ∀ k, s ≤ modeFloor μ ℱ (fun j => commonOf fun i => S i j) gCom k
        + (∑ r : Fin R, modeFloor μ ℱ (fun j => diffOf (fun i => S i j) r) gDiff k) / R)
    (hq : ∀ k, ∫ ω, (revision μ ℱ (fun j => commonOf fun i => S i j) k ω).1 ^ 2 ∂μ
        + (∑ r : Fin R, ∫ ω, (revision μ ℱ (fun j => diffOf (fun i => S i j) r) k ω).1 ^ 2 ∂μ) / R
        ≤ q)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n, N ≤ n ∧ (s - ε) * n
      < ∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace read k ω ∂μ := by
  by_contra hcon
  push Not at hcon
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  set Sc : ℕ → Ω → ℝ := fun j => commonOf fun i => S i j
  set Sd : Fin R → ℕ → Ω → ℝ := fun r j => diffOf (fun i => S i j) r
  have hSc : ∀ k, MemLp (Sc k) 2 μ := fun k => memLp_commonOf fun r => hS r k
  have hSd : ∀ r k, MemLp (Sd r k) 2 μ := fun r k => memLp_diffOf (fun i => hS i k) r
  have hstayC : ∀ k, μ[Sc (k + 2) - Sc (k + 1) | ℱ k] =ᵐ[μ] μ[Sc (k + 1) - Sc k | ℱ k] :=
    fun k => hstay_commonOf hS hstay k
  have hstayD : ∀ r k, μ[Sd r (k + 2) - Sd r (k + 1) | ℱ k] =ᵐ[μ] μ[Sd r (k + 1) - Sd r k | ℱ k] :=
    fun r k => hstay_diffOf hS hstay r k
  have hstartC : Known ℱ μ 0 (commonOf start) := known_commonOf hstart
  have hpaceC : Known ℱ μ 0 (commonOf pace) := known_commonOf hpace
  have hstartD : ∀ r, Known ℱ μ 0 (diffOf start r) := fun r => known_diffOf hstart r
  have hpaceD : ∀ r, Known ℱ μ 0 (diffOf pace r) := fun r => known_diffOf hpace r
  have hrdC : ∀ k, Known ℱ μ k (commonOf fun i => read i k) :=
    fun k => known_commonOf fun i => hread i k
  have hrdD : ∀ r k, Known ℱ μ k (diffOf (fun i => read i k) r) :=
    fun r k => known_diffOf (fun i => hread i k) r
  set c : ℕ → ℝ := fun k => ∫ ω, multiCycleCost cS cΘ S start pace read k ω ∂μ
  set a : ℕ → ℝ := fun n =>
    ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
        (fun j => commonOf fun i => read i j) n ω) ∂μ
    + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
        (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R
  set Kc : ℝ := 4 + 4 / weight gCom + 1 / gCom
  set Kd : ℝ := 4 + 4 / weight gDiff + 1 / gDiff
  set K : ℝ := max Kc Kd
  have hwC : 0 < weight gCom := weight_pos hgC0 hgC1
  have hwD : 0 < weight gDiff := weight_pos hgD0 hgD1
  have hK : 0 < K := lt_of_lt_of_le (by positivity : 0 < Kc) (le_max_left _ _)
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    have hsp := multiCycleCost_integral_split hR hcΘ hcSD hS hstart hpace hread k
    dsimp only [c]
    rw [hsp]
    have h1 : 0 ≤ ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => read i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2) ∂μ :=
      integral_nonneg fun ω => by positivity
    have h2 : 0 ≤ (∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ) / R :=
      div_nonneg (Finset.sum_nonneg fun r _ => integral_nonneg fun ω => by positivity) hRpos.le
    linarith
  have ha0 : ∀ n, 0 ≤ a n := fun n => by
    dsimp only [a]
    have h1 : 0 ≤ ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
        (fun j => commonOf fun i => read i j) n ω) ∂μ :=
      integral_nonneg fun ω => value_nonneg hgC0 hgC1 _
    have h2 : 0 ≤ (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r)
        (diffOf pace r) (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R :=
      div_nonneg (Finset.sum_nonneg fun r _ =>
        integral_nonneg fun ω => value_nonneg hgD0 hgD1 _) hRpos.le
    linarith
  have hq0 : 0 ≤ q := by
    have h1 : 0 ≤ ∫ ω, (revision μ ℱ Sc 0 ω).1 ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have h2 : 0 ≤ (∑ r : Fin R, ∫ ω, (revision μ ℱ (Sd r) 0 ω).1 ^ 2 ∂μ) / R :=
      div_nonneg (Finset.sum_nonneg fun r _ => integral_nonneg fun ω => sq_nonneg _) hRpos.le
    linarith [hq 0]
  -- (A) Cumulative cost plus terminal value exceeds `n * s`.
  have hA : ∀ n : ℕ, (n : ℝ) * s ≤ (∑ k ∈ Finset.range n, c k) + a n := by
    intro n
    have hC := single_cost_split hgC0 hgC1 hSc hstayC hstartC hpaceC hrdC n
    have hD : ∀ r, (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ)
        + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
          (fun j => diffOf (fun i => read i j) r) n ω) ∂μ
      ≥ ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
          (fun j => diffOf (fun i => read i j) r) 0 ω) ∂μ
        + ∑ k ∈ Finset.range n, modeFloor μ ℱ (Sd r) gDiff k := by
      intro r
      have hsp := single_cost_split hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r) (hrdD r) n
      have hex : 0 ≤ ∑ k ∈ Finset.range n, ∫ ω,
          (paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω
            - law gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
              (fun j => diffOf (fun i => read i j) r) k ω)) ^ 2 / (1 - gDiff) ∂μ := by
        have h1 : 0 < 1 - gDiff := by linarith
        exact Finset.sum_nonneg fun k _ => integral_nonneg fun ω => by positivity
      have hmf : ∑ k ∈ Finset.range n, modeFloor μ ℱ (Sd r) gDiff k
          = weight gDiff * (∑ k ∈ Finset.range n, ∫ ω, (Sd r k ω - (μ[Sd r k | ℱ k]) ω) ^ 2 ∂μ)
            + ∑ k ∈ Finset.range n, ∫ ω, value gDiff (revision μ ℱ (Sd r) k ω) ∂μ := by
        simp only [modeFloor, Finset.sum_add_distrib, Finset.mul_sum]
      linarith
    have hC_ge : ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
          (fun j => commonOf fun i => read i j) 0 ω) ∂μ
        + ∑ k ∈ Finset.range n, modeFloor μ ℱ Sc gCom k
      ≤ (∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => read i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2) ∂μ)
        + ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
          (fun j => commonOf fun i => read i j) n ω) ∂μ := by
      have hex : 0 ≤ ∑ k ∈ Finset.range n, ∫ ω,
          (paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω
            - law gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
              (fun j => commonOf fun i => read i j) k ω)) ^ 2 / (1 - gCom) ∂μ := by
        have h1 : 0 < 1 - gCom := by linarith
        exact Finset.sum_nonneg fun k _ => integral_nonneg fun ω => by positivity
      have hmf : ∑ k ∈ Finset.range n, modeFloor μ ℱ Sc gCom k
          = weight gCom * (∑ k ∈ Finset.range n, ∫ ω, (Sc k ω - (μ[Sc k | ℱ k]) ω) ^ 2 ∂μ)
            + ∑ k ∈ Finset.range n, ∫ ω, value gCom (revision μ ℱ Sc k ω) ∂μ := by
        simp only [modeFloor, Finset.sum_add_distrib, Finset.mul_sum]
      linarith
    have hD_avg : (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => read i j) r) 0 ω) ∂μ) / R
          + ∑ k ∈ Finset.range n, (∑ r : Fin R, modeFloor μ ℱ (Sd r) gDiff k) / R
        ≤ (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
            (weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ) / R
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R := by
      have hsum := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hD r
      have hdiv := div_le_div_of_nonneg_right hsum hRpos.le
      have hcomm : (∑ r : Fin R, ∑ k ∈ Finset.range n, modeFloor μ ℱ (Sd r) gDiff k) / R
          = ∑ k ∈ Finset.range n, (∑ r : Fin R, modeFloor μ ℱ (Sd r) gDiff k) / R := by
        rw [Finset.sum_comm, Finset.sum_div]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_div, add_div, hcomm] at hdiv
      exact hdiv
    have hsplit_c : ∑ k ∈ Finset.range n, c k
        = (∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
            (fun j => commonOf fun i => read i j) k ω) ^ 2
          + paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2) ∂μ)
          + (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
            (weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ) / R := by
      dsimp only [c]
      rw [Finset.sum_congr rfl fun k _ =>
        multiCycleCost_integral_split hR hcΘ hcSD hS hstart hpace hread k,
        Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_comm]
    have hns : (n : ℝ) * s ≤ ∑ k ∈ Finset.range n, (modeFloor μ ℱ Sc gCom k
        + (∑ r : Fin R, modeFloor μ ℱ (Sd r) gDiff k) / R) := by
      have := Finset.sum_le_sum (s := Finset.range n) fun k _ => hs k
      simpa using this
    rw [Finset.sum_add_distrib] at hns
    have ha0' : 0 ≤ a 0 := ha0 0
    dsimp only [a] at ha0' ⊢
    linarith
  -- (B) Terminal value is paid for within two cycles.
  have hB : ∀ k, a k ≤ K * (c k + c (k + 1)) + 4 * q := by
    intro k
    have hmode_bound : ∀ {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) {T : ℕ → Ω → ℝ}
        (hT : ∀ j, MemLp (T j) 2 μ)
        (hstayT : ∀ j, μ[T (j + 2) - T (j + 1) | ℱ j] =ᵐ[μ] μ[T (j + 1) - T j | ℱ j])
        {st pc : Ω → ℝ} {rd : ℕ → Ω → ℝ}
        (hst : Known ℱ μ 0 st) (hpc : Known ℱ μ 0 pc) (hrd : ∀ j, Known ℱ μ j (rd j)),
        ∫ ω, value g (state μ ℱ T st pc rd k ω) ∂μ
          ≤ (4 + 4 / weight g + 1 / g)
              * (∫ ω, (weight g * (T k ω - position st rd k ω) ^ 2 + paceChange pc rd k ω ^ 2) ∂μ
                + ∫ ω, (weight g * (T (k + 1) ω - position st rd (k + 1) ω) ^ 2
                    + paceChange pc rd (k + 1) ω ^ 2) ∂μ)
            + 4 * ∫ ω, (revision μ ℱ T k ω).1 ^ 2 ∂μ := by
      intro g hg0 hg1 T hT hstayT st pc rd hst hpc hrd
      have hadm := admissible hT hstayT hst hpc hrd
      have hmv := mean_value_le_costs hg0 hg1 hadm k
      have hpath := path_ae (ℱ := ℱ) hT st pc rd
      have hval_eq : ∫ ω, value g (path (state μ ℱ T st pc rd 0) (paceChange pc rd)
            (revision μ ℱ T) k ω) ∂μ
          = ∫ ω, value g (state μ ℱ T st pc rd k ω) ∂μ :=
        integral_congr_ae (by filter_upwards [hpath k] with ω h; rw [h])
      have hcost_le : ∀ j,
          ∫ ω, cost g (path (state μ ℱ T st pc rd 0) (paceChange pc rd) (revision μ ℱ T) j ω)
              (paceChange pc rd j ω) ∂μ
            ≤ ∫ ω, (weight g * (T j ω - position st rd j ω) ^ 2 + paceChange pc rd j ω ^ 2) ∂μ := by
        intro j
        have hpos := known_position hst hrd j
        have hsplit := mean_square_split (hT j) hpos
        have hest := known_condExp (ℱ := ℱ) (hT j) j
        have hw : MemLp (paceChange pc rd j) 2 μ := (hrd j).2.sub (known_previous hpc hrd j).2
        have i1 : Integrable (fun ω => (T j ω - position st rd j ω) ^ 2) μ :=
          ((hT j).sub hpos.2).integrable_sq
        have i2 : Integrable (fun ω => paceChange pc rd j ω ^ 2) μ := hw.integrable_sq
        have i3 : Integrable (fun ω => ((μ[T j | ℱ j]) ω - position st rd j ω) ^ 2) μ :=
          (hest.2.sub hpos.2).integrable_sq
        have hcost_eq : ∫ ω, cost g (path (state μ ℱ T st pc rd 0) (paceChange pc rd)
              (revision μ ℱ T) j ω) (paceChange pc rd j ω) ∂μ
            = weight g * ∫ ω, ((μ[T j | ℱ j]) ω - position st rd j ω) ^ 2 ∂μ
              + ∫ ω, paceChange pc rd j ω ^ 2 ∂μ := by
          have hae : (fun ω => cost g (path (state μ ℱ T st pc rd 0) (paceChange pc rd)
                (revision μ ℱ T) j ω) (paceChange pc rd j ω))
              =ᵐ[μ] fun ω => weight g * ((μ[T j | ℱ j]) ω - position st rd j ω) ^ 2
                + paceChange pc rd j ω ^ 2 := by
            filter_upwards [hpath j] with ω h; rw [h]; rfl
          rw [integral_congr_ae hae, integral_add (i3.const_mul _) i2, integral_const_mul]
        rw [hcost_eq, integral_add (i1.const_mul _) i2, integral_const_mul, hsplit]
        have hwg : 0 < weight g := weight_pos hg0 hg1
        have hmmse : 0 ≤ ∫ ω, (T j ω - (μ[T j | ℱ j]) ω) ^ 2 ∂μ :=
          integral_nonneg fun ω => sq_nonneg _
        nlinarith
      have hKg : 0 ≤ 4 + 4 / weight g + 1 / g := by
        have := weight_pos hg0 hg1; positivity
      rw [hval_eq] at hmv
      nlinarith [hcost_le k, hcost_le (k + 1)]
    have hBC := hmode_bound hgC0 hgC1 hSc hstayC hstartC hpaceC hrdC
    have hBD : ∀ r, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
          (fun j => diffOf (fun i => read i j) r) k ω) ∂μ
        ≤ Kd * (∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ
          + ∫ ω, (weight gDiff * (Sd r (k + 1) ω - position (diffOf start r)
              (fun j => diffOf (fun i => read i j) r) (k + 1) ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) (k + 1) ω ^ 2) ∂μ)
          + 4 * ∫ ω, (revision μ ℱ (Sd r) k ω).1 ^ 2 ∂μ := fun r =>
      hmode_bound hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r) (hrdD r)
    have hBD_avg : (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => read i j) r) k ω) ∂μ) / R
        ≤ Kd * ((∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ) / R
          + (∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r (k + 1) ω - position (diffOf start r)
              (fun j => diffOf (fun i => read i j) r) (k + 1) ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) (k + 1) ω ^ 2) ∂μ) / R)
          + 4 * ((∑ r : Fin R, ∫ ω, (revision μ ℱ (Sd r) k ω).1 ^ 2 ∂μ) / R) := by
      have hsum := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hBD r
      have hdiv := div_le_div_of_nonneg_right hsum hRpos.le
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        add_div, mul_div_assoc, add_div, mul_div_assoc] at hdiv
      exact hdiv
    have hc_k := multiCycleCost_integral_split hR hcΘ hcSD hS hstart hpace hread k
    have hc_k1 := multiCycleCost_integral_split hR hcΘ hcSD hS hstart hpace hread (k + 1)
    have hC_nonneg : 0 ≤ ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => read i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2) ∂μ
      + ∫ ω, (weight gCom * (Sc (k + 1) ω - position (commonOf start)
          (fun j => commonOf fun i => read i j) (k + 1) ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => read i j) (k + 1) ω ^ 2) ∂μ :=
      add_nonneg (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity)
    have hD_nonneg : 0 ≤ (∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ) / R
      + (∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r (k + 1) ω - position (diffOf start r)
          (fun j => diffOf (fun i => read i j) r) (k + 1) ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) (k + 1) ω ^ 2) ∂μ) / R :=
      add_nonneg
        (div_nonneg (Finset.sum_nonneg fun r _ => integral_nonneg fun ω => by positivity) hRpos.le)
        (div_nonneg (Finset.sum_nonneg fun r _ => integral_nonneg fun ω => by positivity) hRpos.le)
    have hKcK : Kc ≤ K := le_max_left _ _
    have hKdK : Kd ≤ K := le_max_right _ _
    have h1 := mul_le_mul_of_nonneg_right hKcK hC_nonneg
    have h2 := mul_le_mul_of_nonneg_right hKdK hD_nonneg
    have hqk := hq k
    dsimp only [a, c]
    rw [hc_k, hc_k1]
    nlinarith
  -- Standard pigeonhole contradiction (as in `RegulationRandom.mean_cost_rate`).
  have hlow : ∀ n : ℕ, N ≤ n → ε * n ≤ a n := fun n hn => by nlinarith [hA n, hcon n hn]
  have hnonneg : 0 ≤ s - ε := by
    by_contra hneg
    have hneg' : s - ε < 0 := lt_of_not_ge hneg
    have h1 := hcon (N + 1) (Nat.le_succ N)
    have h2 : 0 ≤ ∑ k ∈ Finset.range (N + 1), c k := Finset.sum_nonneg fun k _ => hc0 k
    have h3 : (s - ε) * ((N + 1 : ℕ) : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hneg' (by positivity)
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((6 * K * (s - ε) + 4 * q) / ε)
  set n₀ : ℕ := max (max N m) 1
  have hN : N ≤ n₀ := le_trans (le_max_left N m) (le_max_left _ _)
  have hm' : (m : ℝ) ≤ n₀ := by exact_mod_cast le_trans (le_max_right N m) (le_max_left _ _)
  have h1 : (1 : ℝ) ≤ n₀ := by exact_mod_cast le_max_right (max N m) 1
  have hbig : 6 * K * (s - ε) + 4 * q < ε * n₀ := by
    rw [div_lt_iff₀ hε] at hm; nlinarith
  have hsumlow : ε * n₀ * n₀ ≤ ∑ n ∈ Finset.Ico n₀ (2 * n₀), a n := by
    have : ∑ _n ∈ Finset.Ico n₀ (2 * n₀), ε * (n₀ : ℝ) ≤ ∑ n ∈ Finset.Ico n₀ (2 * n₀), a n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := (Finset.mem_Ico.mp hn).1
      have : ε * (n₀ : ℝ) ≤ ε * n := by
        have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn'
        nlinarith
      exact le_trans this (hlow n (le_trans hN hn'))
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at this
    have hcard : ((2 * n₀ - n₀ : ℕ) : ℝ) = n₀ := by
      have : 2 * n₀ - n₀ = n₀ := by omega
      rw [this]
    rw [hcard] at this
    linarith
  have hsumhigh : ∑ n ∈ Finset.Ico n₀ (2 * n₀), a n
      ≤ 2 * K * (∑ k ∈ Finset.range (2 * n₀ + 1), c k) + 4 * q * n₀ := by
    have hterm : ∑ n ∈ Finset.Ico n₀ (2 * n₀), a n
        ≤ ∑ n ∈ Finset.Ico n₀ (2 * n₀), (K * (c n + c (n + 1)) + 4 * q) :=
      Finset.sum_le_sum fun n _ => hB n
    have hfirst : ∑ n ∈ Finset.Ico n₀ (2 * n₀), c n ≤ ∑ k ∈ Finset.range (2 * n₀ + 1), c k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn; exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hn).2; omega)
      · intro k _ _; exact hc0 k
    have hsecond : ∑ n ∈ Finset.Ico n₀ (2 * n₀), c (n + 1)
        ≤ ∑ k ∈ Finset.range (2 * n₀ + 1), c k := by
      rw [Finset.sum_Ico_add' c n₀ (2 * n₀) 1]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn; exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hn).2; omega)
      · intro k _ _; exact hc0 k
    have hsplit : ∑ n ∈ Finset.Ico n₀ (2 * n₀), (K * (c n + c (n + 1)) + 4 * q)
        = K * (∑ n ∈ Finset.Ico n₀ (2 * n₀), c n + ∑ n ∈ Finset.Ico n₀ (2 * n₀), c (n + 1))
          + 4 * q * n₀ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have : 2 * n₀ - n₀ = n₀ := by omega
      rw [this]; ring
    rw [hsplit] at hterm
    nlinarith
  have hcosts := hcon (2 * n₀ + 1) (by omega)
  have hcast : ((2 * n₀ + 1 : ℕ) : ℝ) ≤ 3 * n₀ := by push_cast; linarith
  have hfinal : ε * n₀ * n₀ ≤ (6 * K * (s - ε) + 4 * q) * n₀ := by
    have : (s - ε) * ((2 * n₀ + 1 : ℕ) : ℝ) ≤ (s - ε) * (3 * n₀) :=
      mul_le_mul_of_nonneg_left hcast hnonneg
    nlinarith
  have hpos : (0 : ℝ) < n₀ := by linarith
  nlinarith

/-- **Long-run cost upper bound for `modalRead` (no terminal value).** When the
combined modal per-cycle irreducible cost floor is at most `s` at every cycle,
the expected cumulative cost of `modalRead` over `n` cycles is at most
`n * s` plus the initial modal value-to-go, so its average cost per cycle
approaches at most `s` as `n → ∞`, matching `multi_lipsync_cost_rate`. -/
theorem multi_lipsync_law_cost_le [IsProbabilityMeasure μ] (hR : 0 < R)
    {gCom gDiff cS cΘ s : ℝ} (hgC0 : 0 < gCom) (hgC1 : gCom < 1)
    (hgD0 : 0 < gDiff) (hgD1 : gDiff < 1)
    (hcΘ : cΘ = weight gCom) (hcSD : cS + cΘ = weight gDiff)
    {S : Fin R → ℕ → Ω → ℝ} (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ k])
    {start pace : Fin R → Ω → ℝ}
    (hstart : ∀ r, Known ℱ μ 0 (start r)) (hpace : ∀ r, Known ℱ μ 0 (pace r))
    (hs : ∀ k, modeFloor μ ℱ (fun j => commonOf fun i => S i j) gCom k
        + (∑ r : Fin R, modeFloor μ ℱ (fun j => diffOf (fun i => S i j) r) gDiff k) / R ≤ s)
    (n : ℕ) :
    let opt := modalRead μ ℱ S gCom gDiff start pace
    ∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace opt k ω ∂μ
      ≤ (n : ℝ) * s
        + ∫ ω, value gCom (state μ ℱ (fun j => commonOf fun i => S i j)
            (commonOf start) (commonOf pace) (fun j => commonOf fun i => opt i j) 0 ω) ∂μ
        + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
            (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) 0 ω) ∂μ) / R := by
  intro opt
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  set Sc : ℕ → Ω → ℝ := fun j => commonOf fun i => S i j
  set Sd : Fin R → ℕ → Ω → ℝ := fun r j => diffOf (fun i => S i j) r
  have hSc : ∀ k, MemLp (Sc k) 2 μ := fun k => memLp_commonOf fun r => hS r k
  have hSd : ∀ r k, MemLp (Sd r k) 2 μ := fun r k => memLp_diffOf (fun i => hS i k) r
  have hstayC : ∀ k, μ[Sc (k + 2) - Sc (k + 1) | ℱ k] =ᵐ[μ] μ[Sc (k + 1) - Sc k | ℱ k] :=
    fun k => hstay_commonOf hS hstay k
  have hstayD : ∀ r k, μ[Sd r (k + 2) - Sd r (k + 1) | ℱ k] =ᵐ[μ] μ[Sd r (k + 1) - Sd r k | ℱ k] :=
    fun r k => hstay_diffOf hS hstay r k
  have hstartC : Known ℱ μ 0 (commonOf start) := known_commonOf hstart
  have hpaceC : Known ℱ μ 0 (commonOf pace) := known_commonOf hpace
  have hstartD : ∀ r, Known ℱ μ 0 (diffOf start r) := fun r => known_diffOf hstart r
  have hpaceD : ∀ r, Known ℱ μ 0 (diffOf pace r) := fun r => known_diffOf hpace r
  have hopt_known : ∀ r k, Known ℱ μ k (opt r k) := fun r k =>
    (known_lawRead hSc hstartC hpaceC k).add (known_lawRead (hSd r) (hstartD r) (hpaceD r) k)
  have hmodes := fun j => modalRead_modes_ae (μ := μ) (ℱ := ℱ) hR S hS gCom gDiff start pace j
  have hcom_all : ∀ᵐ ω ∂μ, ∀ j,
      commonOf (fun i => opt i j) ω = lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace) j ω :=
    ae_all_iff.mpr fun j => (hmodes j).1
  have hdiff_all : ∀ r, ∀ᵐ ω ∂μ, ∀ j,
      diffOf (fun i => opt i j) r ω
        = lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r) j ω :=
    fun r => ae_all_iff.mpr fun j => (hmodes j).2 r
  have hsplit_c : ∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace opt k ω ∂μ
      = (∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => opt i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => opt i j) k ω ^ 2) ∂μ)
        + (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
          (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ) / R := by
    rw [Finset.sum_congr rfl fun k _ =>
      multiCycleCost_integral_split hR hcΘ hcSD hS hstart hpace hopt_known k,
      Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_comm]
  have hC_eq : ∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
        (fun j => commonOf fun i => opt i j) k ω) ^ 2
      + paceChange (commonOf pace) (fun j => commonOf fun i => opt i j) k ω ^ 2) ∂μ
      + ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
          (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) n ω) ∂μ
      = ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
          (fun j => commonOf fun i => opt i j) 0 ω) ∂μ
        + ∑ k ∈ Finset.range n, modeFloor μ ℱ Sc gCom k := by
    have hsp := single_cost_split hgC0 hgC1 hSc hstayC hstartC hpaceC
      (known_lawRead (g := gCom) hSc hstartC hpaceC) n
    have hzero : ∑ k ∈ Finset.range n, ∫ ω,
        (paceChange (commonOf pace) (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) k ω
          - law gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
            (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) k ω)) ^ 2 / (1 - gCom) ∂μ = 0 := by
      apply Finset.sum_eq_zero; intro k _; simp [paceChange_lawRead]
    have hsum_eq : ∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (fun j => commonOf fun i => opt i j) k ω) ^ 2
        + paceChange (commonOf pace) (fun j => commonOf fun i => opt i j) k ω ^ 2) ∂μ
        = ∑ k ∈ Finset.range n, ∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
          (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) k ω) ^ 2
        + paceChange (commonOf pace)
          (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) k ω ^ 2) ∂μ := by
      refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
      obtain ⟨hp, hw, _⟩ := pos_prev_pace_ae (st := commonOf start) (pc := commonOf pace) hcom_all k
      filter_upwards [hp, hw] with ω ep ew; rw [ep, ew]
    have hmf : ∑ k ∈ Finset.range n, modeFloor μ ℱ Sc gCom k
        = weight gCom * (∑ k ∈ Finset.range n, ∫ ω, (Sc k ω - (μ[Sc k | ℱ k]) ω) ^ 2 ∂μ)
          + ∑ k ∈ Finset.range n, ∫ ω, value gCom (revision μ ℱ Sc k ω) ∂μ := by
      simp only [modeFloor, Finset.sum_add_distrib, Finset.mul_sum]
    have hst0 : ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
          (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) 0 ω) ∂μ
        = ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
          (fun j => commonOf fun i => opt i j) 0 ω) ∂μ := rfl
    rw [hsum_eq, hsp, hzero, hst0, hmf]; ring
  have hD_le : ∀ r, ∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
        (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
      + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ
      ≤ ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
          (fun j => diffOf (fun i => opt i j) r) 0 ω) ∂μ
        + ∑ k ∈ Finset.range n, modeFloor μ ℱ (Sd r) gDiff k := by
    intro r
    have hsp := single_cost_split hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r)
      (known_lawRead (g := gDiff) (hSd r) (hstartD r) (hpaceD r)) n
    have hzero : ∑ k ∈ Finset.range n, ∫ ω,
        (paceChange (diffOf pace r) (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) k ω
          - law gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) k ω)) ^ 2
          / (1 - gDiff) ∂μ = 0 := by
      apply Finset.sum_eq_zero; intro k _; simp [paceChange_lawRead]
    have hsum_eq : ∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ
        = ∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) k ω) ^ 2
        + paceChange (diffOf pace r)
          (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) k ω ^ 2) ∂μ := by
      refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
      obtain ⟨hp, hw, _⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
        (hdiff_all r) k
      filter_upwards [hp, hw] with ω ep ew; rw [ep, ew]
    have hmf : ∑ k ∈ Finset.range n, modeFloor μ ℱ (Sd r) gDiff k
        = weight gDiff * (∑ k ∈ Finset.range n, ∫ ω, (Sd r k ω - (μ[Sd r k | ℱ k]) ω) ^ 2 ∂μ)
          + ∑ k ∈ Finset.range n, ∫ ω, value gDiff (revision μ ℱ (Sd r) k ω) ∂μ := by
      simp only [modeFloor, Finset.sum_add_distrib, Finset.mul_sum]
    have hval_nonneg : 0 ≤ ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
        (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) n ω) ∂μ :=
      integral_nonneg fun ω => value_nonneg hgD0 hgD1 _
    have hst0 : ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
          (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) 0 ω) ∂μ
        = ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
          (fun j => diffOf (fun i => opt i j) r) 0 ω) ∂μ := rfl
    linarith
  have hC_val_nonneg : 0 ≤ ∫ ω, value gCom (state μ ℱ Sc (commonOf start) (commonOf pace)
      (lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace)) n ω) ∂μ :=
    integral_nonneg fun ω => value_nonneg hgC0 hgC1 _
  have hD_avg : (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
        (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ) / R
      ≤ (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
          (fun j => diffOf (fun i => opt i j) r) 0 ω) ∂μ) / R
        + ∑ k ∈ Finset.range n, (∑ r : Fin R, modeFloor μ ℱ (Sd r) gDiff k) / R := by
    have hsum := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hD_le r
    have hdiv := div_le_div_of_nonneg_right hsum hRpos.le
    have hcomm : (∑ r : Fin R, ∑ k ∈ Finset.range n, modeFloor μ ℱ (Sd r) gDiff k) / R
        = ∑ k ∈ Finset.range n, (∑ r : Fin R, modeFloor μ ℱ (Sd r) gDiff k) / R := by
      rw [Finset.sum_comm, Finset.sum_div]
    rw [Finset.sum_add_distrib, add_div, hcomm] at hdiv
    exact hdiv
  have hns : ∑ k ∈ Finset.range n, (modeFloor μ ℱ Sc gCom k
      + (∑ r : Fin R, modeFloor μ ℱ (Sd r) gDiff k) / R) ≤ (n : ℝ) * s := by
    have := Finset.sum_le_sum (s := Finset.range n) fun k _ => hs k
    simpa using this
  rw [Finset.sum_add_distrib] at hns
  rw [hsplit_c]
  linarith

/-- **Centralized full-information benchmark for `multiCycleCost cS 0`.**
When tracking weight is zero (`cΘ = 0`) and latency and missed-sample costs are
omitted, `consensusRead` is causal (`Known`), keeps the common-mode pace
constant, and minimizes expected `multiCycleCost cS 0` plus differential
terminal value-to-go among all `ℱ`-adapted multi-speaker policies. Note:
holding the common-mode pace fixed is trivially optimal only because
`multiCycleCost cS 0` does not penalize mean latency or missed samples; in the
full specification, clock drift causes unbounded mean latency drift unless a
small common-mode loop is added. -/
theorem multi_lowlatency_optimal [IsProbabilityMeasure μ] (hR : 0 < R)
    {gDiff cS : ℝ} (hgD0 : 0 < gDiff) (hgD1 : gDiff < 1) (hcS : cS = weight gDiff)
    {S : Fin R → ℕ → Ω → ℝ} (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ k])
    {start pace : Fin R → Ω → ℝ} {read : Fin R → ℕ → Ω → ℝ}
    (hstart : ∀ r, Known ℱ μ 0 (start r)) (hpace : ∀ r, Known ℱ μ 0 (pace r))
    (hread : ∀ r k, Known ℱ μ k (read r k)) (n : ℕ) :
    let opt := consensusRead μ ℱ S gDiff start pace
    (∀ r k, Known ℱ μ k (opt r k))
    ∧ ((∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS 0 S start pace opt k ω ∂μ)
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
              (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ) / R
        ≤ (∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS 0 S start pace read k ω ∂μ)
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
              (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  set opt := consensusRead μ ℱ S gDiff start pace
  set Sd : Fin R → ℕ → Ω → ℝ := fun r j => diffOf (fun i => S i j) r
  have hSd : ∀ r k, MemLp (Sd r k) 2 μ := fun r k => memLp_diffOf (fun i => hS i k) r
  have hstayD : ∀ r k, μ[Sd r (k + 2) - Sd r (k + 1) | ℱ k] =ᵐ[μ] μ[Sd r (k + 1) - Sd r k | ℱ k] :=
    fun r k => hstay_diffOf hS hstay r k
  have hpaceC : Known ℱ μ 0 (commonOf pace) := known_commonOf hpace
  have hstartD : ∀ r, Known ℱ μ 0 (diffOf start r) := fun r => known_diffOf hstart r
  have hpaceD : ∀ r, Known ℱ μ 0 (diffOf pace r) := fun r => known_diffOf hpace r
  have hpaceC_k : ∀ k, Known ℱ μ k (commonOf pace) := by
    intro k
    induction k with
    | zero => exact hpaceC
    | succ k ih => exact ih.later
  have hopt_known : ∀ r k, Known ℱ μ k (opt r k) := fun r k =>
    (hpaceC_k k).add (known_lawRead (hSd r) (hstartD r) (hpaceD r) k)
  refine ⟨hopt_known, ?_⟩
  have hsplit_int : ∀ (rd : Fin R → ℕ → Ω → ℝ), (∀ r k, Known ℱ μ k (rd r k)) →
      ∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS 0 S start pace rd k ω ∂μ
        = (∑ k ∈ Finset.range n, ∫ ω,
            paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2 ∂μ)
          + (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
            (weight gDiff * (Sd r k ω - position (diffOf start r)
                (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
              + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) ∂μ) / R := by
    intro rd hrd
    have hcycle : ∀ k, ∫ ω, multiCycleCost cS 0 S start pace rd k ω ∂μ
        = (∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2 ∂μ)
          + (∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) ∂μ) / R := by
      intro k
      have hpt : ∀ ω, multiCycleCost cS 0 S start pace rd k ω
          = paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2
            + (∑ r : Fin R, (weight gDiff * (Sd r k ω - position (diffOf start r)
                (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
              + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2)) / R := by
        intro ω
        rw [multiCycleCost_modal_split hR cS 0 S start pace rd k ω, hcS]
        simp only [zero_mul, zero_add, add_zero]
        rfl
      have hrdC : ∀ j, Known ℱ μ j (commonOf fun i => rd i j) :=
        fun j => known_commonOf fun i => hrd i j
      have hrdD : ∀ r j, Known ℱ μ j (diffOf (fun i => rd i j) r) :=
        fun r j => known_diffOf (fun i => hrd i j) r
      have hiC : Integrable (fun ω =>
          paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2) μ :=
        ((hrdC k).2.sub (known_previous hpaceC hrdC k).2).integrable_sq
      have hiD : ∀ r : Fin R, Integrable (fun ω =>
          weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) μ := fun r =>
        (((hSd r k).sub (known_position (hstartD r) (hrdD r) k).2).integrable_sq.const_mul _).add
          (((hrdD r k).2.sub (known_previous (hpaceD r) (hrdD r) k).2).integrable_sq)
      simp_rw [hpt]
      rw [integral_add hiC ((integrable_finsetSum Finset.univ fun r _ => hiD r).div_const _),
        integral_div, integral_finsetSum Finset.univ fun r _ => hiD r]
    rw [Finset.sum_congr rfl fun k _ => hcycle k, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_comm]
  rw [hsplit_int opt hopt_known, hsplit_int read hread]
  have hmodes := fun j => consensusRead_modes_ae (μ := μ) (ℱ := ℱ) hR S hS gDiff start pace j
  have hcom_all : ∀ᵐ ω ∂μ, ∀ j, commonOf (fun i => opt i j) ω = commonOf pace ω :=
    ae_all_iff.mpr fun j => (hmodes j).1
  have hdiff_all : ∀ r, ∀ᵐ ω ∂μ, ∀ j,
      diffOf (fun i => opt i j) r ω
        = lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r) j ω :=
    fun r => ae_all_iff.mpr fun j => (hmodes j).2 r
  have hC_zero : ∑ k ∈ Finset.range n,
      ∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => opt i j) k ω ^ 2 ∂μ = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hae : (fun ω => paceChange (commonOf pace)
        (fun j => commonOf fun i => opt i j) k ω ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) := by
      filter_upwards [hcom_all] with ω h
      cases k <;> simp [paceChange, previous, h]
    rw [integral_congr_ae hae, integral_zero]
  have hC_nonneg : 0 ≤ ∑ k ∈ Finset.range n,
      ∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2 ∂μ :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _
  have hD_opt : ∀ r : Fin R,
      (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ)
        + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ
      ≤ (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
          (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
        + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ)
        + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => read i j) r) n ω) ∂μ := by
    intro r
    have hD_eq :
        (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ)
          + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
              (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ
        = (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) k ω) ^ 2
          + paceChange (diffOf pace r)
            (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) k ω ^ 2) ∂μ)
          + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
              (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) n ω) ∂μ := by
      congr 1
      · refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
        obtain ⟨hp, hw, _⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
          (hdiff_all r) k
        filter_upwards [hp, hw] with ω ep ew
        rw [ep, ew]
      · refine integral_congr_ae ?_
        obtain ⟨hp, _, hpr⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
          (hdiff_all r) n
        filter_upwards [hp, hpr] with ω ep epr
        simp only [state, ep, epr]
    rw [hD_eq]
    exact single_law_optimal hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r)
      (fun k => known_diffOf (fun i => hread i k) r) n
  have hD_sum :
      ((∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => opt i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) k ω ^ 2) ∂μ)
        + ∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ) / R
      ≤ ((∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
            (fun j => diffOf (fun i => read i j) r) k ω) ^ 2
          + paceChange (diffOf pace r) (fun j => diffOf (fun i => read i j) r) k ω ^ 2) ∂μ)
        + ∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r)
            (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R := by
    apply div_le_div_of_nonneg_right _ hRpos.le
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r _ => hD_opt r
  rw [hC_zero]
  rw [add_div, add_div] at hD_sum
  change _ + _ + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r)
      (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ) / R
    ≤ _ + _ + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (Sd r)
      (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R
  linarith

/-- **Almost-sure uniqueness of `consensusRead` for `multiCycleCost cS 0`.** -/
theorem multi_lowlatency_unique_ae [IsProbabilityMeasure μ] (hR : 0 < R)
    {gDiff cS : ℝ} (hgD0 : 0 < gDiff) (hgD1 : gDiff < 1) (hcS : cS = weight gDiff)
    {S : Fin R → ℕ → Ω → ℝ} (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ k])
    {start pace : Fin R → Ω → ℝ} {read : Fin R → ℕ → Ω → ℝ}
    (hstart : ∀ r, Known ℱ μ 0 (start r)) (hpace : ∀ r, Known ℱ μ 0 (pace r))
    (hread : ∀ r k, Known ℱ μ k (read r k)) (n : ℕ)
    (heq : let opt := consensusRead μ ℱ S gDiff start pace
      (∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS 0 S start pace read k ω ∂μ)
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
              (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => read i j) r) n ω) ∂μ) / R
        = (∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS 0 S start pace opt k ω ∂μ)
          + (∑ r : Fin R, ∫ ω, value gDiff (state μ ℱ (fun j => diffOf (fun i => S i j) r)
              (diffOf start r) (diffOf pace r) (fun j => diffOf (fun i => opt i j) r) n ω) ∂μ) / R) :
    ∀ r, ∀ k < n, read r k =ᵐ[μ] consensusRead μ ℱ S gDiff start pace r k := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  set opt := consensusRead μ ℱ S gDiff start pace
  set Sd : Fin R → ℕ → Ω → ℝ := fun r j => diffOf (fun i => S i j) r
  have hSd : ∀ r k, MemLp (Sd r k) 2 μ := fun r k => memLp_diffOf (fun i => hS i k) r
  have hstayD : ∀ r k, μ[Sd r (k + 2) - Sd r (k + 1) | ℱ k] =ᵐ[μ] μ[Sd r (k + 1) - Sd r k | ℱ k] :=
    fun r k => hstay_diffOf hS hstay r k
  have hpaceC : Known ℱ μ 0 (commonOf pace) := known_commonOf hpace
  have hstartD : ∀ r, Known ℱ μ 0 (diffOf start r) := fun r => known_diffOf hstart r
  have hpaceD : ∀ r, Known ℱ μ 0 (diffOf pace r) := fun r => known_diffOf hpace r
  have hpaceC_k : ∀ k, Known ℱ μ k (commonOf pace) := by
    intro k; induction k with | zero => exact hpaceC | succ k ih => exact ih.later
  have hopt_known : ∀ r k, Known ℱ μ k (opt r k) := fun r k =>
    (hpaceC_k k).add (known_lawRead (hSd r) (hstartD r) (hpaceD r) k)
  have hsplit_int : ∀ (rd : Fin R → ℕ → Ω → ℝ), (∀ r k, Known ℱ μ k (rd r k)) →
      ∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS 0 S start pace rd k ω ∂μ
        = (∑ k ∈ Finset.range n, ∫ ω,
            paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2 ∂μ)
          + (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
            (weight gDiff * (Sd r k ω - position (diffOf start r)
                (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
              + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) ∂μ) / R := by
    intro rd hrd
    have hcycle : ∀ k, ∫ ω, multiCycleCost cS 0 S start pace rd k ω ∂μ
        = (∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2 ∂μ)
          + (∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) ∂μ) / R := by
      intro k
      have hpt : ∀ ω, multiCycleCost cS 0 S start pace rd k ω
          = paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2
            + (∑ r : Fin R, (weight gDiff * (Sd r k ω - position (diffOf start r)
                (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
              + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2)) / R := by
        intro ω; rw [multiCycleCost_modal_split hR cS 0 S start pace rd k ω, hcS]
        simp only [zero_mul, zero_add, add_zero]; rfl
      have hrdC : ∀ j, Known ℱ μ j (commonOf fun i => rd i j) :=
        fun j => known_commonOf fun i => hrd i j
      have hrdD : ∀ r j, Known ℱ μ j (diffOf (fun i => rd i j) r) :=
        fun r j => known_diffOf (fun i => hrd i j) r
      have hiC : Integrable (fun ω =>
          paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2) μ :=
        ((hrdC k).2.sub (known_previous hpaceC hrdC k).2).integrable_sq
      have hiD : ∀ r : Fin R, Integrable (fun ω =>
          weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) μ := fun r =>
        (((hSd r k).sub (known_position (hstartD r) (hrdD r) k).2).integrable_sq.const_mul _).add
          (((hrdD r k).2.sub (known_previous (hpaceD r) (hrdD r) k).2).integrable_sq)
      simp_rw [hpt]
      rw [integral_add hiC ((integrable_finsetSum Finset.univ fun r _ => hiD r).div_const _),
        integral_div, integral_finsetSum Finset.univ fun r _ => hiD r]
    rw [Finset.sum_congr rfl fun k _ => hcycle k, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_comm]
  have hmodes := fun j => consensusRead_modes_ae (μ := μ) (ℱ := ℱ) hR S hS gDiff start pace j
  have hcom_all : ∀ᵐ ω ∂μ, ∀ j, commonOf (fun i => opt i j) ω = commonOf pace ω :=
    ae_all_iff.mpr fun j => (hmodes j).1
  have hdiff_all : ∀ r, ∀ᵐ ω ∂μ, ∀ j,
      diffOf (fun i => opt i j) r ω
        = lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r) j ω :=
    fun r => ae_all_iff.mpr fun j => (hmodes j).2 r
  set Jd : Fin R → (ℕ → Ω → ℝ) → ℝ := fun r rd =>
    (∑ k ∈ Finset.range n, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r) rd k ω) ^ 2
      + paceChange (diffOf pace r) rd k ω ^ 2) ∂μ)
    + ∫ ω, value gDiff (state μ ℱ (Sd r) (diffOf start r) (diffOf pace r) rd n ω) ∂μ
  have hC_opt_zero : ∑ k ∈ Finset.range n,
      ∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => opt i j) k ω ^ 2 ∂μ = 0 := by
    apply Finset.sum_eq_zero; intro k _
    have hae : (fun ω => paceChange (commonOf pace)
        (fun j => commonOf fun i => opt i j) k ω ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) := by
      filter_upwards [hcom_all] with ω h; cases k <;> simp [paceChange, previous, h]
    rw [integral_congr_ae hae, integral_zero]
  have hJd_opt : ∀ r, Jd r (fun j => diffOf (fun i => opt i j) r)
      = Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) := by
    intro r; dsimp only [Jd]; congr 1
    · refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
      obtain ⟨hp, hw, _⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
        (hdiff_all r) k
      filter_upwards [hp, hw] with ω ep ew; rw [ep, ew]
    · refine integral_congr_ae ?_
      obtain ⟨hp, _, hpr⟩ := pos_prev_pace_ae (st := diffOf start r) (pc := diffOf pace r)
        (hdiff_all r) n
      filter_upwards [hp, hpr] with ω ep epr; simp only [state, ep, epr]
  have hJd_le : ∀ r, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))
      ≤ Jd r (fun j => diffOf (fun i => read i j) r) := fun r =>
    single_law_optimal hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r)
      (fun k => known_diffOf (fun i => hread i k) r) n
  have hC_nonneg : 0 ≤ ∑ k ∈ Finset.range n,
      ∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2 ∂μ :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _
  have htot : (∑ k ∈ Finset.range n,
          ∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2 ∂μ)
        + (∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)) / R
      = (∑ r : Fin R, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))) / R := by
    dsimp only [opt] at heq
    rw [hsplit_int read hread, hsplit_int opt hopt_known, hC_opt_zero, zero_add] at heq
    have h1 : (∑ k ∈ Finset.range n,
            ∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2 ∂μ)
          + (∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)) / R
        = (∑ r : Fin R, Jd r (fun j => diffOf (fun i => opt i j) r)) / R := by
      dsimp only [Jd]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_div, add_div]
      linarith
    rw [h1]
    congr 1
    exact Finset.sum_congr rfl fun r _ => hJd_opt r
  have hsum_le : (∑ r : Fin R, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))) / R
      ≤ (∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)) / R :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun r _ => hJd_le r) hRpos.le
  have hC_zero : ∑ k ∈ Finset.range n,
      ∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2 ∂μ = 0 := by
    linarith
  have hJd_sum_eq : ∑ r : Fin R, (Jd r (fun j => diffOf (fun i => read i j) r)
      - Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))) = 0 := by
    have hdiv_eq : (∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)) / R
        = (∑ r : Fin R, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r))) / R := by
      linarith
    have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
    have hsum_eq : ∑ r : Fin R, Jd r (fun j => diffOf (fun i => read i j) r)
        = ∑ r : Fin R, Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) := by
      field_simp at hdiv_eq; exact hdiv_eq
    rw [Finset.sum_sub_distrib, hsum_eq, sub_self]
  have hJd_eq : ∀ r, Jd r (fun j => diffOf (fun i => read i j) r)
      = Jd r (lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r)) := by
    intro r
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.mpr (hJd_le i)).mp
      hJd_sum_eq r (Finset.mem_univ r)
    linarith
  have hC_step : ∀ k < n,
      ∀ᵐ ω ∂μ, paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω = 0 := by
    intro k hk
    have hint_zero : ∫ ω, paceChange (commonOf pace) (fun j => commonOf fun i => read i j) k ω ^ 2 ∂μ
        = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        integral_nonneg fun ω => sq_nonneg _).mp hC_zero k (Finset.mem_range.mpr hk)
    have hrdC : ∀ j, Known ℱ μ j (commonOf fun i => read i j) :=
      fun j => known_commonOf fun i => hread i j
    have hint : Integrable (fun ω => paceChange (commonOf pace)
        (fun j => commonOf fun i => read i j) k ω ^ 2) μ :=
      ((hrdC k).2.sub (known_previous hpaceC hrdC k).2).integrable_sq
    have hae0 : (fun ω => paceChange (commonOf pace)
        (fun j => commonOf fun i => read i j) k ω ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).mp hint_zero
    filter_upwards [hae0] with ω hω
    exact sq_eq_zero_iff.mp hω
  have hC_ae : ∀ k < n, commonOf (fun i => read i k) =ᵐ[μ] commonOf pace := by
    intro k hk
    induction k with
    | zero =>
      filter_upwards [hC_step 0 hk] with ω hω
      change commonOf (fun i => read i 0) ω - commonOf pace ω = 0 at hω
      linarith
    | succ k ih =>
      filter_upwards [ih (Nat.lt_of_succ_lt hk), hC_step (k + 1) hk] with ω hprev hω
      change commonOf (fun i => read i (k + 1)) ω - commonOf (fun i => read i k) ω = 0 at hω
      linarith
  have hD_ae : ∀ r, ∀ k < n, diffOf (fun i => read i k) r
      =ᵐ[μ] lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r) k := fun r =>
    single_law_unique_ae hgD0 hgD1 (hSd r) (hstayD r) (hstartD r) (hpaceD r)
      (fun k => known_diffOf (fun i => hread i k) r) n (hJd_eq r)
  intro r k hk
  filter_upwards [hC_ae k hk, hD_ae r k hk] with ω hc hd
  change read r k ω = consensusRead μ ℱ S gDiff start pace r k ω
  have hdecomp : read r k ω = commonOf (fun i => read i k) ω + diffOf (fun i => read i k) r ω := by
    simp only [diffOf]; ring
  rw [hdecomp, hc, hd]
  rfl

/-! ## Decentralized pure-star team decomposition and one-hot disturbance split -/

/-- **Effective position weight under pairwise uncorrelated errors.** When `R`
receivers have `L²` tracking errors `e r` that are pairwise uncorrelated
(`∫ e r * e s = 0` for `r ≠ s`), the expected multi-speaker synchronization
plus tracking cost equals `(((R - 1) / R) * cS + cΘ)` times the average
mean-squared error across speakers. -/
theorem decentralized_star_cost_eq (hR : 0 < R) (cS cΘ : ℝ) {e : Fin R → Ω → ℝ}
    (he : ∀ r, MemLp (e r) 2 μ)
    (hunc : ∀ r s : Fin R, r ≠ s → ∫ ω, e r ω * e s ω ∂μ = 0) :
    ∫ ω, (cS * varFin (fun r => e r ω) + cΘ * (∑ r : Fin R, e r ω ^ 2) / R) ∂μ
      = (((R : ℝ) - 1) / R * cS + cΘ) * ((∑ r : Fin R, ∫ ω, e r ω ^ 2 ∂μ) / R) := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hi_sq : ∀ r, Integrable (fun ω => e r ω ^ 2) μ := fun r => (he r).integrable_sq
  have hi_prod : ∀ r s, Integrable (fun ω => e r ω * e s ω) μ :=
    fun r s => (he r).integrable_mul (he s)
  have hmean_sq : ∫ ω, meanFin (fun r => e r ω) ^ 2 ∂μ
      = (∑ r : Fin R, ∫ ω, e r ω ^ 2 ∂μ) / (R : ℝ) ^ 2 := by
    have hexp : ∀ ω, meanFin (fun r => e r ω) ^ 2
        = (∑ r : Fin R, ∑ s : Fin R, e r ω * e s ω) / (R : ℝ) ^ 2 := by
      intro ω
      unfold meanFin
      rw [div_pow, sq, Finset.sum_mul_sum]
    simp_rw [hexp]
    rw [integral_div, integral_finsetSum Finset.univ fun r _ =>
      integrable_finsetSum Finset.univ fun s _ => hi_prod r s]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_finsetSum Finset.univ fun s _ => hi_prod r s,
      Finset.sum_eq_single r (fun s _ hne => hunc r s hne.symm) (by simp)]
    simp_rw [sq]
  have hvar_int : ∫ ω, varFin (fun r => e r ω) ∂μ
      = ((R : ℝ) - 1) / R * ((∑ r : Fin R, ∫ ω, e r ω ^ 2 ∂μ) / R) := by
    have hpt : ∀ ω, varFin (fun r => e r ω)
        = (∑ r : Fin R, e r ω ^ 2) / R - meanFin (fun r => e r ω) ^ 2 := by
      intro ω
      linarith [modal_sq_split hR (fun r => e r ω)]
    have hi_m : Integrable (fun ω => meanFin (fun r => e r ω) ^ 2) μ :=
      (memLp_commonOf he).integrable_sq
    simp_rw [hpt]
    rw [integral_sub ((integrable_finsetSum Finset.univ fun r _ => hi_sq r).div_const _) hi_m,
      integral_div, integral_finsetSum Finset.univ fun r _ => hi_sq r, hmean_sq]
    field_simp
  have hi_var : Integrable (fun ω => varFin (fun r => e r ω)) μ := by
    have hpt : (fun ω => varFin (fun r => e r ω))
        = fun ω => (∑ r : Fin R, e r ω ^ 2) / R - meanFin (fun r => e r ω) ^ 2 := by
      funext ω; linarith [modal_sq_split hR (fun r => e r ω)]
    rw [hpt]
    exact ((integrable_finsetSum Finset.univ fun r _ => hi_sq r).div_const _).sub
      (memLp_commonOf he).integrable_sq
  have hi_sum : Integrable (fun ω => (∑ r : Fin R, e r ω ^ 2) / R) μ :=
    (integrable_finsetSum Finset.univ fun r _ => hi_sq r).div_const _
  have hrew : (fun ω => cS * varFin (fun r => e r ω) + cΘ * (∑ r : Fin R, e r ω ^ 2) / R)
      = fun ω => cS * varFin (fun r => e r ω) + cΘ * ((∑ r : Fin R, e r ω ^ 2) / R) := by
    funext ω; ring
  rw [hrew, integral_add (hi_var.const_mul _) (hi_sum.const_mul _),
    integral_const_mul, integral_const_mul, hvar_int, integral_div,
    integral_finsetSum Finset.univ fun r _ => hi_sq r]
  ring

/-- **Symmetric star team-cost decomposition with a wandering sender.**
In a star where every receiver runs the same linear filter and controller on
its noisy observation of `φ_s - φ_r`, each receiver's tracking error splits as
`e r = eCom + ePriv r` and its pace change as `w r = wCom + wPriv r`, where
`(eCom, wCom)` comes from the common sender clock `φ_s` and `(ePriv r, wPriv r)`
comes from receiver `r`'s own clock and link noise. When `(eCom, wCom)` is
uncorrelated with `(ePriv r, wPriv r)` and the private components are pairwise
uncorrelated across `r ≠ s`, the expected per-cycle multi-speaker cost splits
cleanly into:
* a **common-mode term** `cΘ · E[eCom²] + E[wCom²]` (independent of `cS`,
  because `eCom` cancels out of `varFin`), and
* a **private-mode term** `(((R - 1) / R) * cS + cΘ) · mean_r E[(ePriv r)²]
  + mean_r E[(wPriv r)²]`.

Consequently, `((R - 1) / R) * cS + cΘ` is optimal for a shared star gain only
when `eCom = 0` (no sender wander); whenever the sender clock wanders, the
optimal shared star gain lies between the gains for `cΘ` and
`((R - 1) / R) * cS + cΘ`. -/
theorem symmetric_star_cost_split (hR : 0 < R) (cS cΘ : ℝ)
    {eCom wCom : Ω → ℝ} {ePriv wPriv : Fin R → Ω → ℝ}
    (heC : MemLp eCom 2 μ) (heP : ∀ r, MemLp (ePriv r) 2 μ)
    (hwC : MemLp wCom 2 μ) (hwP : ∀ r, MemLp (wPriv r) 2 μ)
    (heCP : ∀ r, ∫ ω, eCom ω * ePriv r ω ∂μ = 0)
    (hePP : ∀ r s : Fin R, r ≠ s → ∫ ω, ePriv r ω * ePriv s ω ∂μ = 0)
    (hwCP : ∀ r, ∫ ω, wCom ω * wPriv r ω ∂μ = 0) :
    let e : Fin R → Ω → ℝ := fun r ω => eCom ω + ePriv r ω
    let w : Fin R → Ω → ℝ := fun r ω => wCom ω + wPriv r ω
    ∫ ω, (cS * varFin (fun r => e r ω)
        + cΘ * (∑ r : Fin R, e r ω ^ 2) / R
        + (∑ r : Fin R, w r ω ^ 2) / R) ∂μ
      = (cΘ * ∫ ω, eCom ω ^ 2 ∂μ + ∫ ω, wCom ω ^ 2 ∂μ)
        + ((((R : ℝ) - 1) / R * cS + cΘ) * ((∑ r : Fin R, ∫ ω, ePriv r ω ^ 2 ∂μ) / R)
            + (∑ r : Fin R, ∫ ω, wPriv r ω ^ 2 ∂μ) / R) := by
  intro e w
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  -- Adding a constant `eCom ω` across all `r` leaves `varFin` invariant.
  have hvar_inv : ∀ ω, varFin (fun r => e r ω) = varFin (fun r => ePriv r ω) := by
    intro ω
    have hm : meanFin (fun r => e r ω) = eCom ω + meanFin (fun r => ePriv r ω) := by
      unfold meanFin
      simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    unfold varFin
    refine congrArg (· / (R : ℝ)) (Finset.sum_congr rfl fun r _ => ?_)
    rw [hm]; dsimp only [e]; ring
  have hsum_orth : ∀ (a : Ω → ℝ) (b : Fin R → Ω → ℝ),
      MemLp a 2 μ → (∀ r, MemLp (b r) 2 μ) → (∀ r, ∫ ω, a ω * b r ω ∂μ = 0) →
      ∫ ω, (∑ r : Fin R, (a ω + b r ω) ^ 2) / R ∂μ
        = ∫ ω, a ω ^ 2 ∂μ + (∑ r : Fin R, ∫ ω, b r ω ^ 2 ∂μ) / R := by
    intro a b ha hb hab
    have hi_ab : ∀ r, Integrable (fun ω => (a ω + b r ω) ^ 2) μ :=
      fun r => (ha.add (hb r)).integrable_sq
    rw [integral_div, integral_finsetSum Finset.univ fun r _ => hi_ab r]
    have hterm : ∀ r, ∫ ω, (a ω + b r ω) ^ 2 ∂μ = ∫ ω, a ω ^ 2 ∂μ + ∫ ω, b r ω ^ 2 ∂μ := by
      intro r
      have h1 : Integrable (fun ω => a ω ^ 2) μ := ha.integrable_sq
      have h2 : Integrable (fun ω => 2 * (a ω * b r ω)) μ := (ha.integrable_mul (hb r)).const_mul 2
      have h3 : Integrable (fun ω => b r ω ^ 2) μ := (hb r).integrable_sq
      have h12 : Integrable (fun ω => a ω ^ 2 + 2 * (a ω * b r ω)) μ := h1.add h2
      have hpt : (fun ω => (a ω + b r ω) ^ 2)
          = fun ω => (a ω ^ 2 + 2 * (a ω * b r ω)) + b r ω ^ 2 := by funext ω; ring
      rw [hpt, integral_add h12 h3, integral_add h1 h2, integral_const_mul, hab r]
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      add_div, mul_div_cancel_left₀ _ hR']
  have hi_var : Integrable (fun ω => varFin (fun r => ePriv r ω)) μ := by
    have hpt : (fun ω => varFin (fun r => ePriv r ω))
        = fun ω => (∑ r : Fin R, ePriv r ω ^ 2) / R - meanFin (fun r => ePriv r ω) ^ 2 := by
      funext ω; linarith [modal_sq_split hR (fun r => ePriv r ω)]
    rw [hpt]
    exact ((integrable_finsetSum Finset.univ fun r _ => (heP r).integrable_sq).div_const _).sub
      (memLp_commonOf heP).integrable_sq
  have hi_e : Integrable (fun ω => (∑ r : Fin R, e r ω ^ 2) / R) μ :=
    (integrable_finsetSum Finset.univ fun r _ => (heC.add (heP r)).integrable_sq).div_const _
  have hi_w : Integrable (fun ω => (∑ r : Fin R, w r ω ^ 2) / R) μ :=
    (integrable_finsetSum Finset.univ fun r _ => (hwC.add (hwP r)).integrable_sq).div_const _
  have hrew : (fun ω => cS * varFin (fun r => e r ω)
        + cΘ * (∑ r : Fin R, e r ω ^ 2) / R + (∑ r : Fin R, w r ω ^ 2) / R)
      = fun ω => (cS * varFin (fun r => ePriv r ω)
          + cΘ * ((∑ r : Fin R, e r ω ^ 2) / R))
        + (∑ r : Fin R, w r ω ^ 2) / R := by
    funext ω; rw [hvar_inv ω]; ring
  have hvarP := decentralized_star_cost_eq hR cS 0 heP hePP
  simp only [zero_mul, zero_div, add_zero] at hvarP
  have hi_var_cS : Integrable (fun ω => cS * varFin (fun r => ePriv r ω)) μ := hi_var.const_mul cS
  have hi_e_cΘ : Integrable (fun ω => cΘ * ((∑ r : Fin R, e r ω ^ 2) / R)) μ := hi_e.const_mul cΘ
  have hi_lhs : Integrable (fun ω => cS * varFin (fun r => ePriv r ω)
      + cΘ * ((∑ r : Fin R, e r ω ^ 2) / R)) μ := hi_var_cS.add hi_e_cΘ
  rw [hrew, integral_add hi_lhs hi_w, integral_add hi_var_cS hi_e_cΘ,
    hvarP, integral_const_mul, hsum_orth eCom ePriv heC heP heCP,
    hsum_orth wCom wPriv hwC hwP hwCP]
  ring

/-- **Decentralized star optimality when cross-receiver tracking errors remain
uncorrelated (zero common-mode wander).** Suppose each receiver `r` has its own
local filtration `ℱ r` and `weight gStar = ((R - 1) / R) * cS + cΘ`. Among all
decentralized policies `(read r)` adapted to `(ℱ r)` whose tracking errors are
pairwise uncorrelated across `r ≠ s` at every cycle `k < n` (as holds when the
sender's clock does not wander and receivers have independent observations),
running `lawRead` with gain `gStar` on each receiver's own filtration minimizes
the expected `n`-cycle multi-speaker cost plus averaged terminal value-to-go. -/
theorem decentralized_star_uncorrelated_optimal [IsProbabilityMeasure μ] (hR : 0 < R)
    {gStar cS cΘ : ℝ} (hg0 : 0 < gStar) (hg1 : gStar < 1)
    (hwStar : ((R : ℝ) - 1) / R * cS + cΘ = weight gStar)
    (ℱ : Fin R → Filtration ℕ m0)
    {S : Fin R → ℕ → Ω → ℝ} (hS : ∀ r k, MemLp (S r k) 2 μ)
    (hstay : ∀ r k, μ[S r (k + 2) - S r (k + 1) | ℱ r k] =ᵐ[μ] μ[S r (k + 1) - S r k | ℱ r k])
    {start pace : Fin R → Ω → ℝ} {read : Fin R → ℕ → Ω → ℝ}
    (hstart : ∀ r, Known (ℱ r) μ 0 (start r)) (hpace : ∀ r, Known (ℱ r) μ 0 (pace r))
    (hread : ∀ r k, Known (ℱ r) μ k (read r k)) (n : ℕ)
    (hunc_opt : ∀ k < n, ∀ r s : Fin R, r ≠ s →
      ∫ ω, (S r k ω - position (start r) (lawRead μ (ℱ r) (S r) gStar (start r) (pace r)) k ω)
        * (S s k ω - position (start s) (lawRead μ (ℱ s) (S s) gStar (start s) (pace s)) k ω) ∂μ = 0)
    (hunc_read : ∀ k < n, ∀ r s : Fin R, r ≠ s →
      ∫ ω, (S r k ω - position (start r) (read r) k ω)
        * (S s k ω - position (start s) (read s) k ω) ∂μ = 0) :
    let opt : Fin R → ℕ → Ω → ℝ := fun r => lawRead μ (ℱ r) (S r) gStar (start r) (pace r)
    (∀ r k, Known (ℱ r) μ k (opt r k))
    ∧ ((∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace opt k ω ∂μ)
          + (∑ r : Fin R, ∫ ω, value gStar (state μ (ℱ r) (S r) (start r) (pace r) (opt r) n ω) ∂μ) / R
        ≤ (∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace read k ω ∂μ)
          + (∑ r : Fin R, ∫ ω, value gStar (state μ (ℱ r) (S r) (start r) (pace r) (read r) n ω) ∂μ) / R) := by
  intro opt
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hopt_known : ∀ r k, Known (ℱ r) μ k (opt r k) :=
    fun r k => known_lawRead (hS r) (hstart r) (hpace r) k
  refine ⟨hopt_known, ?_⟩
  have hreduce : ∀ (rd : Fin R → ℕ → Ω → ℝ), (∀ r k, Known (ℱ r) μ k (rd r k)) →
      (∀ k < n, ∀ r s : Fin R, r ≠ s →
        ∫ ω, (S r k ω - position (start r) (rd r) k ω)
          * (S s k ω - position (start s) (rd s) k ω) ∂μ = 0) →
      ∑ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace rd k ω ∂μ
        = (∑ r : Fin R, ∑ k ∈ Finset.range n, ∫ ω,
            (weight gStar * (S r k ω - position (start r) (rd r) k ω) ^ 2
              + paceChange (pace r) (rd r) k ω ^ 2) ∂μ) / R := by
    intro rd hrd hunc
    have hcycle : ∀ k ∈ Finset.range n, ∫ ω, multiCycleCost cS cΘ S start pace rd k ω ∂μ
        = (∑ r : Fin R, ∫ ω, (weight gStar * (S r k ω - position (start r) (rd r) k ω) ^ 2
            + paceChange (pace r) (rd r) k ω ^ 2) ∂μ) / R := by
      intro k hk
      have hk' : k < n := Finset.mem_range.mp hk
      set e : Fin R → Ω → ℝ := fun r ω => S r k ω - position (start r) (rd r) k ω
      have he : ∀ r, MemLp (e r) 2 μ := fun r =>
        (hS r k).sub (known_position (hstart r) (hrd r) k).2
      have hw : ∀ r, MemLp (paceChange (pace r) (rd r) k) 2 μ := fun r =>
        (hrd r k).2.sub (known_previous (hpace r) (hrd r) k).2
      have hpos_int : ∫ ω, (cS * varFin (fun r => e r ω)
            + cΘ * (∑ r : Fin R, e r ω ^ 2) / R) ∂μ
          = weight gStar * ((∑ r : Fin R, ∫ ω, e r ω ^ 2 ∂μ) / R) := by
        rw [decentralized_star_cost_eq hR cS cΘ he (hunc k hk'), hwStar]
      have hi1 : Integrable (fun ω => cS * varFin (fun r => e r ω)
            + cΘ * (∑ r : Fin R, e r ω ^ 2) / R) μ := by
        have hvar_pt : (fun ω => varFin (fun r => e r ω))
            = fun ω => (∑ r : Fin R, e r ω ^ 2) / R - meanFin (fun r => e r ω) ^ 2 := by
          funext ω; linarith [modal_sq_split hR (fun r => e r ω)]
        have hi_var : Integrable (fun ω => varFin (fun r => e r ω)) μ := by
          rw [hvar_pt]
          exact ((integrable_finsetSum Finset.univ fun r _ => (he r).integrable_sq).div_const _).sub
            (memLp_commonOf he).integrable_sq
        have hi_e : Integrable (fun ω => cΘ * (∑ r : Fin R, e r ω ^ 2) / R) μ := by
          have hrew : (fun ω => cΘ * (∑ r : Fin R, e r ω ^ 2) / R)
              = fun ω => cΘ * ((∑ r : Fin R, e r ω ^ 2) / R) := by funext ω; ring
          rw [hrew]
          exact ((integrable_finsetSum Finset.univ fun r _ =>
            (he r).integrable_sq).div_const _).const_mul cΘ
        exact (hi_var.const_mul cS).add hi_e
      have hi2 : Integrable (fun ω => (∑ r : Fin R, paceChange (pace r) (rd r) k ω ^ 2) / R) μ :=
        (integrable_finsetSum Finset.univ fun r _ => (hw r).integrable_sq).div_const _
      unfold multiCycleCost
      rw [integral_add hi1 hi2, hpos_int, integral_div,
        integral_finsetSum Finset.univ fun r _ => (hw r).integrable_sq]
      have hcombine : ∀ r, weight gStar * ∫ ω, e r ω ^ 2 ∂μ
            + ∫ ω, paceChange (pace r) (rd r) k ω ^ 2 ∂μ
          = ∫ ω, (weight gStar * e r ω ^ 2 + paceChange (pace r) (rd r) k ω ^ 2) ∂μ := by
        intro r
        rw [integral_add ((he r).integrable_sq.const_mul _) (hw r).integrable_sq, integral_const_mul]
      rw [← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun r _ => hcombine r
    rw [Finset.sum_congr rfl hcycle, ← Finset.sum_div, Finset.sum_comm]
  rw [hreduce opt hopt_known hunc_opt, hreduce read hread hunc_read, ← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ hRpos.le
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ => ?_
  exact single_law_optimal hg0 hg1 (hS r) (hstay r) (hstart r) (hpace r) (hread r) n

/-- **One-hot disturbance split onto the zero-mean subspace.** When one
speaker `r₀` incurs a step `Δ` (and all other speakers incur `0`), subtracting
the mean `Δ / R` reduces the sum of squares from `Δ²` to `((R - 1) / R) * Δ²`.
Note that this leaves the group mean shifted by `Δ / R`: in lip-sync mode,
removing that mean shift later costs `R * (Δ / R)² = Δ² / R` (restoring the
total `Δ²`), whereas without a common-mode loop the mean latency stays shifted
by `Δ / R`. -/
theorem consensus_roughness_savings (hR : 0 < R) (r₀ : Fin R) (Δ : ℝ) :
    let d : Fin R → ℝ := fun r => if r = r₀ then Δ else 0
    ∑ r : Fin R, (d r - meanFin d) ^ 2 = ((R : ℝ) - 1) / R * Δ ^ 2 := by
  intro d
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hm : meanFin d = Δ / R := by
    unfold meanFin
    have : ∑ r : Fin R, d r = Δ := by
      simp [d]
    rw [this]
  have hsq : ∑ r : Fin R, d r ^ 2 = Δ ^ 2 := by
    have : ∀ r : Fin R, d r ^ 2 = if r = r₀ then Δ ^ 2 else 0 := by
      intro r; simp only [d]; split_ifs <;> ring
    simp [this]
  have hvar := modal_sq_split hR d
  have hsum := sum_sq_sub_mean hR d
  rw [hm, hsq] at hvar
  rw [hsum]
  field_simp at hvar ⊢
  linarith

end MultiSpeaker

end Unisono.Solutions.Optimal
