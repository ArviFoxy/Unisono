/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Model.RegulationRandom

/-!
# The best estimate and the law are best together

A receiver reads the stream once in each cycle of its device. `S k` is the
position, in frames, that is truly due at the start of cycle `k`: the
position whose sound was captured the latency `L` before the cycle's first
output sample leaves. The receiver does not know `S k`. Before cycle `k` it
has seen what the σ-algebra `ℱ k` describes, and it chooses `read k`, the
number of frames that cycle `k` reads. Its position at the start of cycle
`k` is `position start read k`, and cycle `k` costs

    weight g * (S k - position start read k) ^ 2 + paceChange pace read k ^ 2,

where the first term measures the latency error and the second is the
squared change of the pace, which is heard as a change of pitch.

The theorem of this file (`mean_cost_split`) holds for every way of playing
that uses only what the receiver has seen, and for every probability
distribution of the noise. The mean cost of the first `n` cycles, plus the
mean value of the state after them, is the sum of four parts:

* the mean squared error of the best estimate of the due position, which is
  the mean of `S k` given `ℱ k`; no way of playing avoids this part;
* the mean value of the state at the start;
* the mean value of each revision of the best estimates; no way of playing
  avoids this part either;
* the mean squared distance of each change of the pace from the law of
  `Unisono.Model.Regulation`, applied to the state, divided by `1 - g`.

The state before a cycle consists of the distance of the position behind
the best estimate of the due position, and of the number of frames by which
the last cycle read more than the best estimate of the advance over the
coming cycle.

Applying the law to the state makes the last part zero (`lawRead`,
`mean_cost_law`), so this way of playing is the best of all that use only
what has been seen (`mean_cost_law_le`). The proof uses the orthogonality
principle twice. First, the distance to the due position splits into the
distance to its best estimate and the error of the estimate, because the
error is orthogonal to everything known before the cycle
(`mean_square_split`). Second, the law is best against revisions that are
orthogonal to everything known before them (`mean_cost_sum`).

The one condition on the due position is that its pace is expected to stay:
given what is known before cycle `k`, its expected advance over cycle
`k + 1` equals its expected advance over cycle `k`. A due position driven by
a clock whose frequency follows a random walk satisfies it.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Star

open MeasureTheory Unisono.Model.Regulation Unisono.Model.RegulationRandom

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The position at the start of cycle `k`, from the position `start` at the
start of cycle `0`, when cycle `j` reads `read j` frames. -/
def position (start : Ω → ℝ) (read : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => start
  | k + 1 => fun ω => position start read k ω + read k ω

/-- The number of frames read by the cycle before cycle `k`; before cycle `0`
it is `pace`. -/
def previous (pace : Ω → ℝ) (read : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => pace
  | k + 1 => read k

/-- The change of the pace at cycle `k`. -/
def paceChange (pace : Ω → ℝ) (read : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  read k ω - previous pace read k ω

variable (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ)

/-- The best estimate, before cycle `k`, of how far the due position advances
over cycle `k`. -/
def advance (k : ℕ) : Ω → ℝ := μ[S (k + 1) - S k | ℱ k]

/-- The state of the law before cycle `k`: the distance of the position
behind the best estimate of the due position, and the number of frames by
which the last cycle read more than the expected advance over cycle `k`. -/
def state (start pace : Ω → ℝ) (read : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ × ℝ :=
  ((μ[S k | ℱ k]) ω - position start read k ω, previous pace read k ω - advance μ ℱ S k ω)

/-- The revisions between cycle `k` and cycle `k + 1`: of the estimate of the
due position at the start of cycle `k + 1`, and of the expected advance, with
the sign of the latter reversed. -/
def revision (k : ℕ) (ω : Ω) : ℝ × ℝ :=
  ((μ[S (k + 1) | ℱ (k + 1)]) ω - (μ[S (k + 1) | ℱ k]) ω,
    advance μ ℱ S k ω - advance μ ℱ S (k + 1) ω)

variable {μ ℱ S}

/-- A revision with its sign reversed cannot be foreseen either. -/
theorem unforeseen_neg {k : ℕ} {f : Ω → ℝ} (h : Unforeseen ℱ μ k f) :
    Unforeseen ℱ μ k fun ω => -f ω := by
  refine ⟨⟨h.1.1.neg, h.1.2.neg⟩, ?_⟩
  have hneg : μ[-f | ℱ k] =ᵐ[μ] -μ[f | ℱ k] := condExp_neg f (ℱ k)
  filter_upwards [hneg, h.2] with ω e1 e2
  change (μ[-f | ℱ k]) ω = 0
  rw [e1, Pi.neg_apply, e2]
  simp

/-- The position at the start of cycle `k` is known before cycle `k`. -/
theorem known_position {start : Ω → ℝ} {read : ℕ → Ω → ℝ} (hstart : Known ℱ μ 0 start)
    (hread : ∀ k, Known ℱ μ k (read k)) : ∀ k, Known ℱ μ k (position start read k)
  | 0 => hstart
  | k + 1 => (known_position hstart hread k).later.add (hread k).later

/-- The number of frames read by the cycle before cycle `k` is known before
cycle `k`. -/
theorem known_previous {pace : Ω → ℝ} {read : ℕ → Ω → ℝ} (hpace : Known ℱ μ 0 pace)
    (hread : ∀ k, Known ℱ μ k (read k)) : ∀ k, Known ℱ μ k (previous pace read k)
  | 0 => hpace
  | k + 1 => (hread k).later

/-- A best estimate before cycle `k` is known before cycle `k`. -/
theorem known_condExp [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) (k : ℕ) :
    Known ℱ μ k (μ[f | ℱ k]) :=
  ⟨stronglyMeasurable_condExp, hf.condExp one_le_two⟩

/-- The state moves from one cycle to the next as the law's problem says: by
the change of the pace and by the revisions. -/
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

/-- The states that the law's problem goes through are the states of the
receiver, at almost every outcome. -/
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

/-- A way of playing that uses only what has been seen is admissible for the
law's problem, when the pace of the due position is expected to stay. -/
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

/-- **The cost splits.** For every way of playing that uses only what has
been seen, the mean cost of the first `n` cycles plus the mean value of the
state after them is the sum of: the mean squared errors of the best
estimates of the due positions, times the weight; the mean value of the
state at the start; the mean values of the revisions; and the mean squared
distances of the changes of the pace from the law, divided by `1 - g`. -/
theorem mean_cost_split {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) [IsProbabilityMeasure μ]
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
  -- Each cycle's cost splits into the law's cost and the error of the estimate.
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
  -- The law's problem is about the receiver's states.
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

/-- **What no way of playing avoids.** For every way of playing that uses only
what has been seen, the mean cost of the first `n` cycles plus the mean value
of the state after them is at least the weighted mean squared errors of the
best estimates, plus the mean value of the state at the start, plus the mean
values of the revisions. -/
theorem mean_cost_ge {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) [IsProbabilityMeasure μ]
    (hS : ∀ k, MemLp (S k) 2 μ)
    (hstay : ∀ k, μ[S (k + 2) - S (k + 1) | ℱ k] =ᵐ[μ] μ[S (k + 1) - S k | ℱ k])
    {start pace : Ω → ℝ} {read : ℕ → Ω → ℝ} (hstart : Known ℱ μ 0 start)
    (hpace : Known ℱ μ 0 pace) (hread : ∀ k, Known ℱ μ k (read k)) (n : ℕ) :
    weight g * (∑ k ∈ Finset.range n, ∫ ω, (S k ω - (μ[S k | ℱ k]) ω) ^ 2 ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace read 0 ω) ∂μ
        + ∑ k ∈ Finset.range n, ∫ ω, value g (revision μ ℱ S k ω) ∂μ
      ≤ (∑ k ∈ Finset.range n,
          ∫ ω, (weight g * (S k ω - position start read k ω) ^ 2 + paceChange pace read k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace read n ω) ∂μ := by
  rw [mean_cost_split hg0 hg1 hS hstay hstart hpace hread n]
  have h1 : 0 < 1 - g := by linarith
  have : 0 ≤ ∑ k ∈ Finset.range n, ∫ ω, (paceChange pace read k ω
      - law g (state μ ℱ S start pace read k ω)) ^ 2 / (1 - g) ∂μ :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun ω => by positivity
  linarith

/-! ## Playing by the law -/

variable (μ ℱ S)

/-- Playing by the law with gain `g` from the position `start` and the pace
`pace`: before cycle `k`, the position and the number of frames read by the
cycle before. Each cycle reads the previous number of frames plus the law's
change, applied to the distance behind the best estimate of the due position
and to the pace beyond the expected advance. -/
def lawRun (g : ℝ) (start pace : Ω → ℝ) : ℕ → Ω → ℝ × ℝ
  | 0 => fun ω => (start ω, pace ω)
  | k + 1 => fun ω =>
    let x := lawRun g start pace k ω
    let r := x.2 + law g ((μ[S k | ℱ k]) ω - x.1, x.2 - advance μ ℱ S k ω)
    (x.1 + r, r)

/-- The number of frames that cycle `k` reads when playing by the law. -/
def lawRead (g : ℝ) (start pace : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (lawRun μ ℱ S g start pace (k + 1) ω).2

variable {μ ℱ S}

/-- Playing by the law, the position and the number of frames read by the
cycle before are those that `lawRun` records. -/
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

/-- Playing by the law, each change of the pace is the law's change. -/
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

/-- Playing by the law uses only what has been seen: the number of frames that
cycle `k` reads is known before cycle `k`. -/
theorem known_lawRead [IsFiniteMeasure μ] (hS : ∀ k, MemLp (S k) 2 μ) {g : ℝ}
    {start pace : Ω → ℝ}
    (hstart : Known ℱ μ 0 start) (hpace : Known ℱ μ 0 pace) :
    ∀ k, Known ℱ μ k (lawRead μ ℱ S g start pace k) := by
  -- The number of frames that a cycle reads is known before it, when the
  -- position and the previous number of frames are.
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

/-- **Playing by the law costs only what no way of playing avoids.** -/
theorem mean_cost_law {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) [IsProbabilityMeasure μ]
    (hS : ∀ k, MemLp (S k) 2 μ)
    (hstay : ∀ k, μ[S (k + 2) - S (k + 1) | ℱ k] =ᵐ[μ] μ[S (k + 1) - S k | ℱ k])
    {start pace : Ω → ℝ} (hstart : Known ℱ μ 0 start) (hpace : Known ℱ μ 0 pace) (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, (weight g * (S k ω - position start
        (lawRead μ ℱ S g start pace) k ω) ^ 2
        + paceChange pace (lawRead μ ℱ S g start pace) k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) n ω) ∂μ
      = weight g * (∑ k ∈ Finset.range n, ∫ ω, (S k ω - (μ[S k | ℱ k]) ω) ^ 2 ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) 0 ω) ∂μ
        + ∑ k ∈ Finset.range n, ∫ ω, value g (revision μ ℱ S k ω) ∂μ := by
  rw [mean_cost_split hg0 hg1 hS hstay hstart hpace (known_lawRead hS hstart hpace) n]
  have hzero : ∑ k ∈ Finset.range n, ∫ ω, (paceChange pace (lawRead μ ℱ S g start pace) k ω
      - law g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) k ω)) ^ 2 / (1 - g) ∂μ
      = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp [paceChange_lawRead]
  rw [hzero]
  ring

/-- **The best estimate and the law are best together.** For every way of
playing that uses only what has been seen and starts from the same position
and pace, and for every number of cycles, its mean cost plus the mean value
of the state after the cycles is at least what playing by the law gives. -/
theorem mean_cost_law_le {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) [IsProbabilityMeasure μ]
    (hS : ∀ k, MemLp (S k) 2 μ)
    (hstay : ∀ k, μ[S (k + 2) - S (k + 1) | ℱ k] =ᵐ[μ] μ[S (k + 1) - S k | ℱ k])
    {start pace : Ω → ℝ} {read : ℕ → Ω → ℝ} (hstart : Known ℱ μ 0 start)
    (hpace : Known ℱ μ 0 pace) (hread : ∀ k, Known ℱ μ k (read k)) (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, (weight g * (S k ω - position start
        (lawRead μ ℱ S g start pace) k ω) ^ 2
        + paceChange pace (lawRead μ ℱ S g start pace) k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) n ω) ∂μ
      ≤ (∑ k ∈ Finset.range n,
          ∫ ω, (weight g * (S k ω - position start read k ω) ^ 2 + paceChange pace read k ω ^ 2) ∂μ)
        + ∫ ω, value g (state μ ℱ S start pace read n ω) ∂μ := by
  rw [mean_cost_law hg0 hg1 hS hstay hstart hpace n]
  have hstate0 : ∫ ω, value g (state μ ℱ S start pace (lawRead μ ℱ S g start pace) 0 ω) ∂μ
      = ∫ ω, value g (state μ ℱ S start pace read 0 ω) ∂μ := rfl
  rw [hstate0]
  exact mean_cost_ge hg0 hg1 hS hstay hstart hpace hread n

end Unisono.Solutions.Star
