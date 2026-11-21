/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Process.Filtration
public import Unisono.Model.Regulation

/-!
# The best law for a receiver's pace, when the schedule is revised

`Unisono.Model.Regulation` states the problem of one receiver, cycle by cycle
of its device, and solves it for a schedule that is not revised. Here the
schedule is revised between the cycles, in a way that the receiver cannot
foresee, and the receiver may use everything it has seen so far.

What the receiver has seen before cycle `k` is the σ-algebra `ℱ k` of a
filtration on a probability space. A quantity is *known* before cycle `k`
when it is measurable for `ℱ k` and has a finite mean square. A revision is
*unforeseen* at cycle `k` when it is known before cycle `k + 1` and its mean,
given what is known before cycle `k`, is zero. This is what a revision of a
best estimate is: an estimate that is the mean of a quantity given what has
been seen changes, when more is seen, by an amount whose mean given what was
seen before is zero.

A way of playing is *admissible* when the state at the start is known before
the first cycle, each change of the pace is known before its cycle, and each
revision is unforeseen at its cycle. Nothing else is asked: the changes of
the pace may depend on everything seen so far in any way, and the revisions
need not be independent, of one law, or Gaussian.

The result (`mean_cost_sum`): for every admissible way of playing and every
number `n` of cycles, the mean cost of the cycles plus the mean value of the
state after them equals

* the mean value of the state at the start,
* plus the mean value of each revision, taken as a state, which no way of
  playing avoids,
* plus the mean squared distance of each change of the pace from the law,
  divided by `1 - g`.

The law makes the last part zero and is admissible (`admissible_lawful`), so
it is best among all admissible ways of playing, for every `n`
(`mean_cost_law_le`), and what any other way loses against it is exactly that
last part.
-/

@[expose] public noncomputable section

namespace Unisono.Model.RegulationRandom

open MeasureTheory Unisono.Model.Regulation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-- A quantity that the receiver knows before cycle `k`, with a finite mean
square. -/
def Known (ℱ : Filtration ℕ m0) (μ : Measure Ω) (k : ℕ) (f : Ω → ℝ) : Prop :=
  StronglyMeasurable[ℱ k] f ∧ MemLp f 2 μ

/-- A revision that the receiver cannot foresee before cycle `k`: it is known
before the next cycle, and its mean given what is known before cycle `k` is
zero. -/
def Unforeseen (ℱ : Filtration ℕ m0) (μ : Measure Ω) (k : ℕ) (f : Ω → ℝ) : Prop :=
  Known ℱ μ (k + 1) f ∧ μ[f | ℱ k] =ᵐ[μ] 0

theorem Known.add {k : ℕ} {f₁ f₂ : Ω → ℝ} (h₁ : Known ℱ μ k f₁) (h₂ : Known ℱ μ k f₂) :
    Known ℱ μ k fun ω => f₁ ω + f₂ ω :=
  ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

theorem Known.sub {k : ℕ} {f₁ f₂ : Ω → ℝ} (h₁ : Known ℱ μ k f₁) (h₂ : Known ℱ μ k f₂) :
    Known ℱ μ k fun ω => f₁ ω - f₂ ω :=
  ⟨h₁.1.sub h₂.1, h₁.2.sub h₂.2⟩

theorem Known.const_mul {k : ℕ} {f : Ω → ℝ} (h : Known ℱ μ k f) (c : ℝ) :
    Known ℱ μ k fun ω => c * f ω :=
  ⟨h.1.const_mul c, h.2.const_mul c⟩

/-- What is known before a cycle is known before the next. -/
theorem Known.later {k : ℕ} {f : Ω → ℝ} (h : Known ℱ μ k f) : Known ℱ μ (k + 1) f :=
  ⟨h.1.mono (ℱ.mono (Nat.le_succ k)), h.2⟩

/-- A quadratic form of two quantities with finite mean squares has a mean. -/
theorem integrable_form {f₁ f₂ : Ω → ℝ} (h₁ : MemLp f₁ 2 μ) (h₂ : MemLp f₂ 2 μ) (a b c : ℝ) :
    Integrable (fun ω => a * f₁ ω ^ 2 + b * (f₁ ω * f₂ ω) + c * f₂ ω ^ 2) μ :=
  ((h₁.integrable_sq.const_mul a).add ((h₁.integrable_mul h₂).const_mul b)).add
    (h₂.integrable_sq.const_mul c)

theorem integrable_value (g : ℝ) {f₁ f₂ : Ω → ℝ} (h₁ : MemLp f₁ 2 μ) (h₂ : MemLp f₂ 2 μ) :
    Integrable (fun ω => value g (f₁ ω, f₂ ω)) μ := by
  have := integrable_form h₁ h₂ (g ^ 3 / ((2 - g) * (1 - g))) (-2 * gainE g) g
  refine this.congr (ae_of_all _ fun ω => ?_)
  simp only [value]
  ring

/-- The mean of a sum of five parts, of which two have the mean zero. -/
theorem integral_parts {A D C₁ C₂ R : Ω → ℝ} (hA : Integrable A μ) (hD : Integrable D μ)
    (hC₁ : Integrable C₁ μ) (hC₂ : Integrable C₂ μ) (hR : Integrable R μ)
    (h₁ : ∫ ω, C₁ ω ∂μ = 0) (h₂ : ∫ ω, C₂ ω ∂μ = 0) :
    ∫ ω, (A ω + D ω + 2 * (C₁ ω + C₂ ω) + R ω) ∂μ
      = ∫ ω, A ω ∂μ + ∫ ω, D ω ∂μ + ∫ ω, R ω ∂μ := by
  have hAD : Integrable (fun ω => A ω + D ω) μ := hA.add hD
  have hC : Integrable (fun ω => C₁ ω + C₂ ω) μ := hC₁.add hC₂
  have hC2 : Integrable (fun ω => 2 * (C₁ ω + C₂ ω)) μ := hC.const_mul 2
  have hADC : Integrable (fun ω => A ω + D ω + 2 * (C₁ ω + C₂ ω)) μ := hAD.add hC2
  rw [integral_add hADC hR, integral_add hAD hC2, integral_add hA hD, integral_const_mul,
    integral_add hC₁ hC₂, h₁, h₂]
  ring

variable [IsProbabilityMeasure μ]

/-- The mean of the product of a quantity known before a cycle and a revision
unforeseen at that cycle is zero. -/
theorem integral_mul_eq_zero {k : ℕ} {y ξ : Ω → ℝ} (hy : Known ℱ μ k y)
    (hξ : Unforeseen ℱ μ k ξ) : ∫ ω, y ω * ξ ω ∂μ = 0 := by
  have hint : Integrable (y * ξ) μ := hy.2.integrable_mul hξ.1.2
  have hξint : Integrable ξ μ := hξ.1.2.integrable one_le_two
  have hpull := condExp_mul_of_stronglyMeasurable_left hy.1 hint hξint
  have hzero : μ[y * ξ | ℱ k] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hξ.2] with ω h1 h2
    simp [h1, h2]
  calc ∫ ω, y ω * ξ ω ∂μ = ∫ ω, (μ[y * ξ | ℱ k]) ω ∂μ := (integral_condExp (ℱ.le k)).symm
    _ = ∫ ω, (0 : Ω → ℝ) ω ∂μ := integral_congr_ae hzero
    _ = 0 := by simp

/-! ## A way of playing -/

/-- The states that the changes `w` of the pace and the revisions `ξ` lead
through from `x₀`. -/
def path (x₀ : Ω → ℝ × ℝ) (w : ℕ → Ω → ℝ) (ξ : ℕ → Ω → ℝ × ℝ) : ℕ → Ω → ℝ × ℝ
  | 0 => x₀
  | k + 1 => fun ω => next (path x₀ w ξ k ω) (w k ω) (ξ k ω)

/-- The state at the start is known before the first cycle, each change of
the pace is known before its cycle, and each revision is unforeseen at its
cycle. -/
structure Admissible (ℱ : Filtration ℕ m0) (μ : Measure Ω) (x₀ : Ω → ℝ × ℝ)
    (w : ℕ → Ω → ℝ) (ξ : ℕ → Ω → ℝ × ℝ) : Prop where
  /-- The distance at the start is known. -/
  start_distance : Known ℱ μ 0 fun ω => (x₀ ω).1
  /-- The pace at the start is known. -/
  start_pace : Known ℱ μ 0 fun ω => (x₀ ω).2
  /-- Each change of the pace uses only what is known before its cycle. -/
  change : ∀ k, Known ℱ μ k (w k)
  /-- The revisions of the schedule's position are unforeseen. -/
  revised_position : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).1
  /-- The revisions of the schedule's pace are unforeseen. -/
  revised_pace : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).2

variable {x₀ : Ω → ℝ × ℝ} {w : ℕ → Ω → ℝ} {ξ : ℕ → Ω → ℝ × ℝ}

omit [IsProbabilityMeasure μ] in
/-- The state before a cycle is known before that cycle. -/
theorem known_path (h : Admissible ℱ μ x₀ w ξ) (k : ℕ) :
    Known ℱ μ k (fun ω => (path x₀ w ξ k ω).1) ∧ Known ℱ μ k (fun ω => (path x₀ w ξ k ω).2) := by
  induction k with
  | zero => exact ⟨h.start_distance, h.start_pace⟩
  | succ k ih =>
    constructor
    · exact ((ih.1.later.sub ih.2.later).sub (h.change k).later).add (h.revised_position k).1
    · exact (ih.2.later.add (h.change k).later).add (h.revised_pace k).1

/-- **One cycle.** The mean cost of a cycle plus the mean value of the state
after it is the mean value of the state before it, plus the mean squared
distance of the change of the pace from the law, divided by `1 - g`, plus the
mean value of the revision. -/
theorem mean_cost_step {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (h : Admissible ℱ μ x₀ w ξ)
    (k : ℕ) :
    ∫ ω, cost g (path x₀ w ξ k ω) (w k ω) ∂μ + ∫ ω, value g (path x₀ w ξ (k + 1) ω) ∂μ
      = ∫ ω, value g (path x₀ w ξ k ω) ∂μ
        + ∫ ω, (w k ω - law g (path x₀ w ξ k ω)) ^ 2 / (1 - g) ∂μ
        + ∫ ω, value g (ξ k ω) ∂μ := by
  obtain ⟨hE, hv⟩ := known_path h k
  obtain ⟨hE', hv'⟩ := known_path h (k + 1)
  have hw := h.change k
  have hξ1 := h.revised_position k
  have hξ2 := h.revised_pace k
  -- the state after the cycle if the schedule were not revised
  have hy1 : Known ℱ μ k fun ω => (path x₀ w ξ k ω).1 - (path x₀ w ξ k ω).2 - w k ω :=
    (hE.sub hv).sub hw
  have hy2 : Known ℱ μ k fun ω => (path x₀ w ξ k ω).2 + w k ω := hv.add hw
  -- the two combinations of it that the revisions are multiplied with
  have hz1 := (hy1.const_mul (g ^ 3 / ((2 - g) * (1 - g)))).sub (hy2.const_mul (gainE g))
  have hz2 := (hy2.const_mul g).sub (hy1.const_mul (gainE g))
  have hcross1 := integral_mul_eq_zero hz1 hξ1
  have hcross2 := integral_mul_eq_zero hz2 hξ2
  have ic1 := hz1.2.integrable_mul hξ1.1.2
  have ic2 := hz2.2.integrable_mul hξ2.1.2
  -- every part has a mean
  have icost : Integrable (fun ω => cost g (path x₀ w ξ k ω) (w k ω)) μ := by
    have := integrable_form hE.2 hw.2 (weight g) 0 1
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [cost]
    ring
  have inext : Integrable (fun ω => value g (path x₀ w ξ (k + 1) ω)) μ :=
    integrable_value g hE'.2 hv'.2
  have ival : Integrable (fun ω => value g (path x₀ w ξ k ω)) μ := integrable_value g hE.2 hv.2
  have idev : Integrable (fun ω => (w k ω - law g (path x₀ w ξ k ω)) ^ 2 / (1 - g)) μ := by
    have hdiff : MemLp (fun ω => w k ω - (gainE g * (path x₀ w ξ k ω).1
        - g * (path x₀ w ξ k ω).2)) 2 μ :=
      hw.2.sub ((hE.2.const_mul (gainE g)).sub (hv.2.const_mul g))
    exact hdiff.integrable_sq.div_const (1 - g)
  have irev : Integrable (fun ω => value g (ξ k ω)) μ := integrable_value g hξ1.1.2 hξ2.1.2
  -- the identity, outcome by outcome
  have hpoint : ∀ ω, cost g (path x₀ w ξ k ω) (w k ω) + value g (path x₀ w ξ (k + 1) ω)
      = value g (path x₀ w ξ k ω) + (w k ω - law g (path x₀ w ξ k ω)) ^ 2 / (1 - g)
        + 2 * ((g ^ 3 / ((2 - g) * (1 - g))
              * ((path x₀ w ξ k ω).1 - (path x₀ w ξ k ω).2 - w k ω)
            - gainE g * ((path x₀ w ξ k ω).2 + w k ω)) * (ξ k ω).1
          + (g * ((path x₀ w ξ k ω).2 + w k ω)
            - gainE g * ((path x₀ w ξ k ω).1 - (path x₀ w ξ k ω).2 - w k ω)) * (ξ k ω).2)
        + value g (ξ k ω) := by
    intro ω
    have h1 := cost_add_value hg0 hg1 (path x₀ w ξ k ω) (w k ω)
    have h2 := value_next g (path x₀ w ξ k ω) (w k ω) (ξ k ω)
    have h3 : path x₀ w ξ (k + 1) ω = next (path x₀ w ξ k ω) (w k ω) (ξ k ω) := rfl
    rw [h3, h2]
    simp only [pairing, next, Prod.fst_zero, Prod.snd_zero] at h1 ⊢
    linarith
  calc ∫ ω, cost g (path x₀ w ξ k ω) (w k ω) ∂μ + ∫ ω, value g (path x₀ w ξ (k + 1) ω) ∂μ
      = ∫ ω, (cost g (path x₀ w ξ k ω) (w k ω) + value g (path x₀ w ξ (k + 1) ω)) ∂μ :=
        (integral_add icost inext).symm
    _ = _ := integral_congr_ae (ae_of_all _ hpoint)
    _ = _ := integral_parts ival idev ic1 ic2 irev hcross1 hcross2

/-- **Every number of cycles.** The mean cost of the first `n` cycles plus the
mean value of the state after them is the mean value of the state at the
start, plus what each change of the pace differs from the law by, plus the
mean values of the revisions. -/
theorem mean_cost_sum {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (h : Admissible ℱ μ x₀ w ξ)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, cost g (path x₀ w ξ k ω) (w k ω) ∂μ)
        + ∫ ω, value g (path x₀ w ξ n ω) ∂μ
      = ∫ ω, value g (x₀ ω) ∂μ
        + (∑ k ∈ Finset.range n, ∫ ω, (w k ω - law g (path x₀ w ξ k ω)) ^ 2 / (1 - g) ∂μ)
        + ∑ k ∈ Finset.range n, ∫ ω, value g (ξ k ω) ∂μ := by
  induction n with
  | zero => simp [path]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hstep := mean_cost_step hg0 hg1 h n
    linarith

/-- What no way of playing avoids: the mean cost of the first `n` cycles plus
the mean value of the state after them is at least the mean value of the
state at the start plus the mean values of the revisions. -/
theorem mean_cost_ge {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (h : Admissible ℱ μ x₀ w ξ) (n : ℕ) :
    ∫ ω, value g (x₀ ω) ∂μ + ∑ k ∈ Finset.range n, ∫ ω, value g (ξ k ω) ∂μ
      ≤ (∑ k ∈ Finset.range n, ∫ ω, cost g (path x₀ w ξ k ω) (w k ω) ∂μ)
        + ∫ ω, value g (path x₀ w ξ n ω) ∂μ := by
  have hsum := mean_cost_sum hg0 hg1 h n
  have h1 : 0 < 1 - g := by linarith
  have : 0 ≤ ∑ k ∈ Finset.range n,
      ∫ ω, (w k ω - law g (path x₀ w ξ k ω)) ^ 2 / (1 - g) ∂μ :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun ω => by positivity
  linarith

/-! ## The law -/

/-- The states under the law. -/
def closed (g : ℝ) (x₀ : Ω → ℝ × ℝ) (ξ : ℕ → Ω → ℝ × ℝ) : ℕ → Ω → ℝ × ℝ
  | 0 => x₀
  | k + 1 => fun ω => next (closed g x₀ ξ k ω) (law g (closed g x₀ ξ k ω)) (ξ k ω)

/-- The changes of the pace that the law makes. -/
def lawful (g : ℝ) (x₀ : Ω → ℝ × ℝ) (ξ : ℕ → Ω → ℝ × ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  law g (closed g x₀ ξ k ω)

theorem path_lawful (g : ℝ) (x₀ : Ω → ℝ × ℝ) (ξ : ℕ → Ω → ℝ × ℝ) (k : ℕ) :
    path x₀ (lawful g x₀ ξ) ξ k = closed g x₀ ξ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext ω
    change next (path x₀ (lawful g x₀ ξ) ξ k ω) (lawful g x₀ ξ k ω) (ξ k ω)
      = next (closed g x₀ ξ k ω) (law g (closed g x₀ ξ k ω)) (ξ k ω)
    rw [ih]
    rfl

omit [IsProbabilityMeasure μ] in
/-- The law is an admissible way of playing: its changes of the pace use only
the state before each cycle, which is known then. -/
theorem admissible_lawful (g : ℝ)
    (hE : Known ℱ μ 0 fun ω => (x₀ ω).1) (hv : Known ℱ μ 0 fun ω => (x₀ ω).2)
    (hξ1 : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).1)
    (hξ2 : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).2) :
    Admissible ℱ μ x₀ (lawful g x₀ ξ) ξ := by
  have known : ∀ k, Known ℱ μ k (fun ω => (closed g x₀ ξ k ω).1)
      ∧ Known ℱ μ k (fun ω => (closed g x₀ ξ k ω).2) := by
    intro k
    induction k with
    | zero => exact ⟨hE, hv⟩
    | succ k ih =>
      have hlaw : Known ℱ μ k fun ω => gainE g * (closed g x₀ ξ k ω).1
          - g * (closed g x₀ ξ k ω).2 := (ih.1.const_mul (gainE g)).sub (ih.2.const_mul g)
      constructor
      · exact ((ih.1.later.sub ih.2.later).sub hlaw.later).add (hξ1 k).1
      · exact (ih.2.later.add hlaw.later).add (hξ2 k).1
  exact ⟨hE, hv, fun k => ((known k).1.const_mul (gainE g)).sub ((known k).2.const_mul g),
    hξ1, hξ2⟩

/-- Under the law the mean cost of the first `n` cycles plus the mean value
of the state after them is exactly what no way of playing avoids. -/
theorem mean_cost_law {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (hE : Known ℱ μ 0 fun ω => (x₀ ω).1) (hv : Known ℱ μ 0 fun ω => (x₀ ω).2)
    (hξ1 : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).1)
    (hξ2 : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).2) (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, cost g (closed g x₀ ξ k ω) (lawful g x₀ ξ k ω) ∂μ)
        + ∫ ω, value g (closed g x₀ ξ n ω) ∂μ
      = ∫ ω, value g (x₀ ω) ∂μ + ∑ k ∈ Finset.range n, ∫ ω, value g (ξ k ω) ∂μ := by
  have hsum := mean_cost_sum hg0 hg1 (admissible_lawful g hE hv hξ1 hξ2) n
  simp only [path_lawful] at hsum
  have hzero : ∑ k ∈ Finset.range n,
      ∫ ω, (lawful g x₀ ξ k ω - law g (closed g x₀ ξ k ω)) ^ 2 / (1 - g) ∂μ = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp [lawful]
  rw [hzero] at hsum
  linarith

/-- **The law is best.** For every admissible way of playing and every number
of cycles, the mean cost of the cycles plus the mean value of the state after
them is at least what it is under the law, from the same start and with the
same revisions. -/
theorem mean_cost_law_le {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (h : Admissible ℱ μ x₀ w ξ)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, cost g (closed g x₀ ξ k ω) (lawful g x₀ ξ k ω) ∂μ)
        + ∫ ω, value g (closed g x₀ ξ n ω) ∂μ
      ≤ (∑ k ∈ Finset.range n, ∫ ω, cost g (path x₀ w ξ k ω) (w k ω) ∂μ)
        + ∫ ω, value g (path x₀ w ξ n ω) ∂μ := by
  rw [mean_cost_law hg0 hg1 h.start_distance h.start_pace h.revised_position h.revised_pace]
  exact mean_cost_ge hg0 hg1 h n

/-- Under the law the mean value of the state after a cycle is `1 - g` times
the mean value before it, plus the mean value of the revision. So when the
revisions have mean values of at most `s`, the mean value of the state stays
at most the larger of its mean at the start and `s / g`. -/
theorem mean_value_law {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (hE : Known ℱ μ 0 fun ω => (x₀ ω).1) (hv : Known ℱ μ 0 fun ω => (x₀ ω).2)
    (hξ1 : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).1)
    (hξ2 : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).2) (k : ℕ) :
    ∫ ω, value g (closed g x₀ ξ (k + 1) ω) ∂μ
      = (1 - g) * ∫ ω, value g (closed g x₀ ξ k ω) ∂μ + ∫ ω, value g (ξ k ω) ∂μ := by
  have hadm := admissible_lawful g hE hv hξ1 hξ2
  have hstep := mean_cost_step hg0 hg1 hadm k
  simp only [path_lawful] at hstep
  have hzero : ∫ ω, (lawful g x₀ ξ k ω - law g (closed g x₀ ξ k ω)) ^ 2 / (1 - g) ∂μ = 0 := by
    simp [lawful]
  have hcost : ∫ ω, cost g (closed g x₀ ξ k ω) (lawful g x₀ ξ k ω) ∂μ
      = g * ∫ ω, value g (closed g x₀ ξ k ω) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact cost_law hg0 hg1 _
  rw [hzero, hcost] at hstep
  linarith

/-- Under the law the mean value of the state stays at most the larger of its
mean at the start and `s / g`, when the mean value of every revision is at
most `s`. With `mean_cost_law`, the mean cost of `n` cycles under the law is
therefore within that bound of the mean values of the `n` revisions, which no
way of playing avoids: over many cycles the mean cost of a cycle is the mean
value of a revision. -/
theorem mean_value_law_le {g s : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (hE : Known ℱ μ 0 fun ω => (x₀ ω).1) (hv : Known ℱ μ 0 fun ω => (x₀ ω).2)
    (hξ1 : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).1)
    (hξ2 : ∀ k, Unforeseen ℱ μ k fun ω => (ξ k ω).2)
    (hs : ∀ k, ∫ ω, value g (ξ k ω) ∂μ ≤ s) (k : ℕ) :
    ∫ ω, value g (closed g x₀ ξ k ω) ∂μ ≤ max (∫ ω, value g (x₀ ω) ∂μ) (s / g) := by
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    rw [mean_value_law hg0 hg1 hE hv hξ1 hξ2 k]
    have hbound : s ≤ g * max (∫ ω, value g (x₀ ω) ∂μ) (s / g) := by
      have := le_max_right (∫ ω, value g (x₀ ω) ∂μ) (s / g)
      rw [div_le_iff₀ hg0] at this
      linarith
    have hkeep := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 - g)
    linarith [hs k]

/-! ## The schedule that the receiver follows

The receiver does not know the schedule. It follows its estimate of it, and
the statements above are about the distance to that estimate. Two facts
connect them to the true schedule, when the estimate is the best one: the
mean of the true quantity given what the receiver has seen.

* The mean squared distance of the receiver's position from the true
  schedule is the mean squared distance from the estimate plus the mean
  squared error of the estimate (`mean_square_split`). The second part is the
  same for every way of playing, so the way of playing that is best against
  the estimate is best against the truth.
* When the receiver sees more, the estimate of a quantity changes by an
  amount that it could not foresee (`unforeseen_revision`): this is where the
  revisions come from, and why their mean, given what was seen before, is
  zero.
-/

/-- The mean of the product of a quantity known before cycle `k` and one
whose mean, given what is known before cycle `k`, is zero. -/
theorem integral_mul_eq_zero_of_condExp {k : ℕ} {y ξ : Ω → ℝ} (hy : Known ℱ μ k y)
    (hξ : MemLp ξ 2 μ) (hzero : μ[ξ | ℱ k] =ᵐ[μ] 0) : ∫ ω, y ω * ξ ω ∂μ = 0 := by
  have hint : Integrable (y * ξ) μ := hy.2.integrable_mul hξ
  have hξint : Integrable ξ μ := hξ.integrable one_le_two
  have hpull := condExp_mul_of_stronglyMeasurable_left hy.1 hint hξint
  have hprod : μ[y * ξ | ℱ k] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hzero] with ω h1 h2
    simp [h1, h2]
  calc ∫ ω, y ω * ξ ω ∂μ = ∫ ω, (μ[y * ξ | ℱ k]) ω ∂μ := (integral_condExp (ℱ.le k)).symm
    _ = ∫ ω, (0 : Ω → ℝ) ω ∂μ := integral_congr_ae hprod
    _ = 0 := by simp

/-- **A revision of a best estimate cannot be foreseen.** The estimate of a
quantity `S` before cycle `k + 1`, less the estimate of it before cycle `k`,
is known before cycle `k + 1`, and its mean given what is known before cycle
`k` is zero. -/
theorem unforeseen_revision {S : Ω → ℝ} (hS : MemLp S 2 μ) (k : ℕ) :
    Unforeseen ℱ μ k (μ[S | ℱ (k + 1)] - μ[S | ℱ k]) := by
  have hle : ℱ k ≤ ℱ (k + 1) := ℱ.mono (Nat.le_succ k)
  refine ⟨⟨stronglyMeasurable_condExp.sub (stronglyMeasurable_condExp.mono hle),
    (hS.condExp one_le_two).sub (hS.condExp one_le_two)⟩, ?_⟩
  have h1 : μ[μ[S | ℱ (k + 1)] - μ[S | ℱ k] | ℱ k]
      =ᵐ[μ] μ[μ[S | ℱ (k + 1)] | ℱ k] - μ[μ[S | ℱ k] | ℱ k] :=
    condExp_sub integrable_condExp integrable_condExp _
  have h2 : μ[μ[S | ℱ (k + 1)] | ℱ k] =ᵐ[μ] μ[S | ℱ k] :=
    condExp_condExp_of_le hle (ℱ.le (k + 1))
  have h3 : μ[μ[S | ℱ k] | ℱ k] = μ[S | ℱ k] :=
    condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp integrable_condExp
  filter_upwards [h1, h2] with ω e1 e2
  rw [e1, Pi.sub_apply, e2, h3]
  simp

/-- **The distance to the true schedule.** For a quantity `S` and a position
`p` that is known before cycle `k`, the mean squared distance between them is
the mean squared distance of `p` from the best estimate of `S` before cycle
`k`, plus the mean squared error of that estimate. -/
theorem mean_square_split {S p : Ω → ℝ} {k : ℕ} (hS : MemLp S 2 μ) (hp : Known ℱ μ k p) :
    ∫ ω, (S ω - p ω) ^ 2 ∂μ
      = ∫ ω, ((μ[S | ℱ k]) ω - p ω) ^ 2 ∂μ + ∫ ω, (S ω - (μ[S | ℱ k]) ω) ^ 2 ∂μ := by
  have hest : Known ℱ μ k (μ[S | ℱ k]) := ⟨stronglyMeasurable_condExp, hS.condExp one_le_two⟩
  have hdiff : Known ℱ μ k fun ω => (μ[S | ℱ k]) ω - p ω := hest.sub hp
  have herr : MemLp (S - μ[S | ℱ k]) 2 μ := hS.sub hest.2
  have hzero : μ[S - μ[S | ℱ k] | ℱ k] =ᵐ[μ] 0 := by
    have h1 : μ[S - μ[S | ℱ k] | ℱ k] =ᵐ[μ] μ[S | ℱ k] - μ[μ[S | ℱ k] | ℱ k] :=
      condExp_sub (hS.integrable one_le_two) integrable_condExp _
    have h3 : μ[μ[S | ℱ k] | ℱ k] = μ[S | ℱ k] :=
      condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp integrable_condExp
    filter_upwards [h1] with ω e1
    rw [e1, h3]
    simp
  have hcross : ∫ ω, ((μ[S | ℱ k]) ω - p ω) * (S ω - (μ[S | ℱ k]) ω) ∂μ = 0 :=
    integral_mul_eq_zero_of_condExp hdiff herr hzero
  have i1 : Integrable (fun ω => ((μ[S | ℱ k]) ω - p ω) ^ 2) μ := hdiff.2.integrable_sq
  have i2 : Integrable (fun ω => ((μ[S | ℱ k]) ω - p ω) * (S ω - (μ[S | ℱ k]) ω)) μ :=
    hdiff.2.integrable_mul herr
  have i2' : Integrable (fun ω => 2 * (((μ[S | ℱ k]) ω - p ω) * (S ω - (μ[S | ℱ k]) ω))) μ :=
    i2.const_mul 2
  have i12 : Integrable (fun ω => ((μ[S | ℱ k]) ω - p ω) ^ 2
      + 2 * (((μ[S | ℱ k]) ω - p ω) * (S ω - (μ[S | ℱ k]) ω))) μ := i1.add i2'
  have i3 : Integrable (fun ω => (S ω - (μ[S | ℱ k]) ω) ^ 2) μ := herr.integrable_sq
  calc ∫ ω, (S ω - p ω) ^ 2 ∂μ
      = ∫ ω, (((μ[S | ℱ k]) ω - p ω) ^ 2
          + 2 * (((μ[S | ℱ k]) ω - p ω) * (S ω - (μ[S | ℱ k]) ω))
          + (S ω - (μ[S | ℱ k]) ω) ^ 2) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        ring
    _ = _ := by
        rw [integral_add i12 i3, integral_add i1 i2', integral_const_mul, hcross]
        ring

end Unisono.Model.RegulationRandom
