/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Model.RegulationRandom
public import Unisono.Spec.Topologies

/-!
# Optimal multi-speaker modal control for peer and star topologies

This module derives the optimal discrete-time playback pace controller directly
from the modal decomposition of `Unisono.Spec.Objectives`
(`Unisono.Spec.Topologies.World.weighted_frame_modal_split`,
`Unisono.Spec.Topologies.modal_sq_split`).

For `R > 0` speakers operating over equal-duration cycles:
* Speaker `r` starts cycle `k` at position `p_{r,k}`, reads `read r k` frames
  during cycle `k` (`p_{r,k+1} = p_{r,k} + read r k`), and changes its pace by
  `w_{r,k} = read r k - read r (k - 1)`.
* `S r k` is the frame position due at the start of cycle `k` (captured `L`
  seconds before the cycle's first output sample leaves).
* Given specification weights `(cS, cΘ)` relative to roughness weight `1`, the
  multi-speaker cost of cycle `k` is

      cS * var_r (S r k - p_{r,k})
        + cΘ * mean_r (S r k - p_{r,k})²
        + mean_r w_{r,k}².

By `Unisono.Spec.modal_sq_split`, this multi-speaker objective decomposes
orthogonally into two decoupled control problems:

1. **Common mode** (group mean across speakers), with position weight `cΘ`
   (`0` in low-latency mode, positive in lip-sync mode) and roughness weight `1`.
2. **Differential mode** (zero-mean deviations across speakers), with position
   weight `cS + cΘ` and roughness weight `1`.

## Main results

* **Single-mode separation (`single_cost_split`, `single_law_optimal`).** For
  any fixed filtration `ℱ` and any noise distribution whose one-step expected
  increments are constant (`E[S_{k+2} - S_{k+1} | ℱ_k] = E[S_{k+1} - S_k | ℱ_k]`),
  applying `Unisono.Model.Regulation.law g` to the conditional-mean state
  minimizes the expected finite-horizon cost plus terminal value-to-go among
  all `ℱ`-adapted policies.
* **Peer / hub-coordinated lip-sync optimum (`multi_lipsync_optimal`).** When
  all speakers share observations `ℱ_k` (via peer state exchange or sender-hub
  coordination) and `cΘ = weight gCom`, `cS + cΘ = weight gDiff`, the unique
  optimal multi-speaker controller is the **two-gain modal law**:
  `w_{r,k}* = law gCom (common state) + law gDiff (differential state r)`.
* **Peer / hub-coordinated low-latency optimum (`multi_lowlatency_optimal`).**
  When `cΘ = 0` and `cS = weight gDiff`, the unique optimal multi-speaker
  controller is **pure consensus**: `w_{r,k}* = law gDiff (differential state r)`
  with zero common-mode pace change (`mean_r w_{r,k}* = 0`), completely
  independent of common-mode sender-clock wander.
* **Decentralized pure-star weight (`decentralized_star_cost_eq`) and
  consensus roughness savings (`consensus_roughness_savings`).** When `R`
  receivers act independently with pairwise uncorrelated zero-mean errors in a
  pure star, each receiver's effective quadratic position weight is
  `((R - 1) / R) * cS + cΘ` (neither `cS + cΘ` nor `cΘ`). Splitting a
  single-receiver disturbance across all `R` speakers via consensus reduces
  total squared pace-change energy by the factor `(R - 1) / R` (a 2× reduction
  for `R = 2`).

## Scope and modeling assumptions

These theorems assume: (1) a fixed filtration `ℱ` (optimality is relative to
what `ℱ` observes, not over probing schedules or lossy front ends that shrink
`ℱ`); (2) unconstrained real-valued `read r k` (continuity `0 < read < 2` and
buffer-availability constraints are enforced separately); (3) uniform cycle
length across speakers so cycle-level `(Δn)²` matches linearized roughness; and
(4) martingale expected increments (satisfied by white and random-walk
frequency noise with constant block sizes, not by flicker noise or varying
block sizes).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Optimal

open MeasureTheory Unisono.Model.Regulation Unisono.Model.RegulationRandom Unisono.Spec

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

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

/-! ## Multi-speaker modal control (peer / hub-coordinated optimum) -/

section MultiSpeaker

variable {R : ℕ}

/-- Common mode (mean across `R` speakers) of a speaker-indexed random vector. -/
def commonOf (f : Fin R → Ω → ℝ) (ω : Ω) : ℝ :=
  meanFin fun r => f r ω

/-- Differential mode (deviation from the group mean) of speaker `r`. -/
def diffOf (f : Fin R → Ω → ℝ) (r : Fin R) (ω : Ω) : ℝ :=
  f r ω - commonOf f ω

/-- Multi-speaker cycle cost matching `Unisono.Spec.Topologies.weighted_frame_modal_split`
and `modal_sq_split`: synchronization weight `cS`, tracking weight `cΘ`, and
unit roughness weight. -/
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

/-- **Exact pointwise modal split of the multi-speaker cycle cost.** The
multi-speaker objective decomposes orthogonally into a common-mode problem with
position weight `cΘ` and `R` differential-mode problems each with position
weight `cS + cΘ`. -/
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
speaker's differential mode. -/
def modalRead (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : Fin R → ℕ → Ω → ℝ)
    (gCom gDiff : ℝ) (start pace : Fin R → Ω → ℝ) (r : Fin R) (k : ℕ) (ω : Ω) : ℝ :=
  lawRead μ ℱ (fun j => commonOf fun i => S i j) gCom (commonOf start) (commonOf pace) k ω
    + lawRead μ ℱ (fun j => diffOf (fun i => S i j) r) gDiff (diffOf start r) (diffOf pace r) k ω

/-- **Pure-consensus controller for low-latency mode (`cΘ = 0`).** Keeps the
common-mode pace constant (`read_bar k = commonOf pace`, zero common-mode
roughness) and applies `lawRead` with gain `gDiff` solely to the zero-mean
differential mode. -/
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

/-- **Multi-speaker lip-sync optimality (Peer / Hub-Coordinated optimum).**
For any `R > 0` speakers sharing filtration `ℱ` with lip-sync weights
`cΘ = weight gCom` and `cS + cΘ = weight gDiff` (`0 < gCom, gDiff < 1`), the
two-gain modal controller `modalRead` is causal (`Known`) and minimizes the
expected multi-speaker cost plus expected modal terminal value-to-go among all
`ℱ`-adapted multi-speaker policies. -/
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
  -- Helper: split integral of `multiCycleCost` into common + average differential integrals.
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
    have hcycle : ∀ k, ∫ ω, multiCycleCost cS cΘ S start pace rd k ω ∂μ
        = (∫ ω, (weight gCom * (Sc k ω - position (commonOf start)
              (fun j => commonOf fun i => rd i j) k ω) ^ 2
            + paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2) ∂μ)
          + (∑ r : Fin R, ∫ ω, (weight gDiff * (Sd r k ω - position (diffOf start r)
              (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
            + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2) ∂μ) / R := by
      intro k
      have hpt : ∀ ω, multiCycleCost cS cΘ S start pace rd k ω
          = (weight gCom * (Sc k ω - position (commonOf start)
                (fun j => commonOf fun i => rd i j) k ω) ^ 2
              + paceChange (commonOf pace) (fun j => commonOf fun i => rd i j) k ω ^ 2)
            + (∑ r : Fin R, (weight gDiff * (Sd r k ω - position (diffOf start r)
                (fun j => diffOf (fun i => rd i j) r) k ω) ^ 2
              + paceChange (diffOf pace r) (fun j => diffOf (fun i => rd i j) r) k ω ^ 2)) / R := by
        intro ω
        rw [multiCycleCost_modal_split hR cS cΘ S start pace rd k ω, hcSD, hcΘ]
      have hrdC : ∀ j, Known ℱ μ j (commonOf fun i => rd i j) :=
        fun j => known_commonOf fun i => hrd i j
      have hrdD : ∀ r j, Known ℱ μ j (diffOf (fun i => rd i j) r) :=
        fun r j => known_diffOf (fun i => hrd i j) r
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
    rw [Finset.sum_congr rfl fun k _ => hcycle k, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_comm]
  rw [hsplit_int opt hopt_known, hsplit_int read hread]
  -- Match `opt`'s common and differential modes to `lawRead` a.e.
  have hmodes := fun j => modalRead_modes_ae (μ := μ) (ℱ := ℱ) hR S hS gCom gDiff start pace j
  have hcom_all : ∀ᵐ ω ∂μ, ∀ j,
      commonOf (fun i => opt i j) ω = lawRead μ ℱ Sc gCom (commonOf start) (commonOf pace) j ω :=
    ae_all_iff.mpr fun j => (hmodes j).1
  have hdiff_all : ∀ r, ∀ᵐ ω ∂μ, ∀ j,
      diffOf (fun i => opt i j) r ω
        = lawRead μ ℱ (Sd r) gDiff (diffOf start r) (diffOf pace r) j ω :=
    fun r => ae_all_iff.mpr fun j => (hmodes j).2 r
  have hpos_ae : ∀ (st pc : Ω → ℝ) (r1 r2 : ℕ → Ω → ℝ),
      (∀ᵐ ω ∂μ, ∀ j, r1 j ω = r2 j ω) →
      ∀ k, (∀ᵐ ω ∂μ, position st r1 k ω = position st r2 k ω)
        ∧ (∀ᵐ ω ∂μ, paceChange pc r1 k ω = paceChange pc r2 k ω)
        ∧ (∀ᵐ ω ∂μ, previous pc r1 k ω = previous pc r2 k ω) := by
    intro st pc r1 r2 heq k
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [heq] with ω h
      induction k with
      | zero => rfl
      | succ k ih => simp [position, ih, h k]
    · filter_upwards [heq] with ω h
      cases k <;> simp [paceChange, previous, h]
    · filter_upwards [heq] with ω h
      cases k <;> simp [previous, h]
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
      obtain ⟨hp, hw, _⟩ := hpos_ae (commonOf start) (commonOf pace) _ _ hcom_all k
      filter_upwards [hp, hw] with ω ep ew
      rw [ep, ew]
    · refine integral_congr_ae ?_
      obtain ⟨hp, _, hpr⟩ := hpos_ae (commonOf start) (commonOf pace) _ _ hcom_all n
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
        obtain ⟨hp, hw, _⟩ := hpos_ae (diffOf start r) (diffOf pace r) _ _ (hdiff_all r) k
        filter_upwards [hp, hw] with ω ep ew
        rw [ep, ew]
      · refine integral_congr_ae ?_
        obtain ⟨hp, _, hpr⟩ := hpos_ae (diffOf start r) (diffOf pace r) _ _ (hdiff_all r) n
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

/-- **Multi-speaker low-latency optimality (Pure Consensus optimum).**
When tracking weight is zero (`cΘ = 0`, low-latency mode) and synchronization
weight is `cS = weight gDiff`, `consensusRead` is causal (`Known`), has zero
common-mode pace change, does not depend on common-mode sender clock wander,
and minimizes expected multi-speaker cost plus differential terminal
value-to-go among all `ℱ`-adapted multi-speaker policies. -/
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
  have hpos_ae : ∀ (st pc : Ω → ℝ) (r1 r2 : ℕ → Ω → ℝ),
      (∀ᵐ ω ∂μ, ∀ j, r1 j ω = r2 j ω) →
      ∀ k, (∀ᵐ ω ∂μ, position st r1 k ω = position st r2 k ω)
        ∧ (∀ᵐ ω ∂μ, paceChange pc r1 k ω = paceChange pc r2 k ω)
        ∧ (∀ᵐ ω ∂μ, previous pc r1 k ω = previous pc r2 k ω) := by
    intro st pc r1 r2 heq k
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [heq] with ω h
      induction k with
      | zero => rfl
      | succ k ih => simp [position, ih, h k]
    · filter_upwards [heq] with ω h
      cases k <;> simp [paceChange, previous, h]
    · filter_upwards [heq] with ω h
      cases k <;> simp [previous, h]
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
        obtain ⟨hp, hw, _⟩ := hpos_ae (diffOf start r) (diffOf pace r) _ _ (hdiff_all r) k
        filter_upwards [hp, hw] with ω ep ew
        rw [ep, ew]
      · refine integral_congr_ae ?_
        obtain ⟨hp, _, hpr⟩ := hpos_ae (diffOf start r) (diffOf pace r) _ _ (hdiff_all r) n
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

/-! ## Decentralized pure-star weight and consensus roughness savings -/

/-- **Effective position weight in a decentralized pure star.** When `R`
receivers act independently and their tracking errors `e r` are pairwise
uncorrelated (`∫ e r * e s = 0` for `r ≠ s`), the expected multi-speaker
synchronization + tracking cost equals `(((R - 1) / R) * cS + cΘ)` times the
average mean-squared error across speakers. Hence the optimal per-receiver
decentralized gain weight in a pure star is `((R - 1) / R) * cS + cΘ` (not
`cS + cΘ` and not `cΘ`). -/
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

/-- **Consensus roughness savings on a single-speaker disturbance.** When one
speaker `r₀` incurs a step disturbance `Δ` (and all other speakers incur `0`),
splitting the correction across all `R` speakers in the differential mode
reduces total squared pace-change energy from `Δ²` to `((R - 1) / R) * Δ²`
(half the roughness for `R = 2`). -/
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
