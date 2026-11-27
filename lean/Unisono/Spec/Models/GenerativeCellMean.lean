/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeResamplePauses
public import Unisono.Spec.Models.GenerativeCellStall

/-!
# Tools for the mean cost of a cell

Three tools for taking the mean of what a pause that begins in a cell costs.
None of them is about a particular member.

* `lintegral_prodMk_of_indepFun`: the mean of a function of two independent
  random variables is the mean, over the first, of its mean over the law of
  the second.
* `pauseLaw_ge_dirac`, `pauseLaw_ge_smul`, `lintegral_pauseLaw_ge`: the law
  of the paused time that begins in a period gives at least the probability
  `exp (-count)` to no paused time, and at least `exp (-count) * count`
  times the law of the length of one pause to the rest. These are the terms
  of the law for no pause and for one pause.
* `describedPlays`, `eq_describedPlays`, `measurable_getD_lastPlayed`: when
  what a speaker plays at each output sample is given by a measurable set
  and a measurable function of the draw, the position that it played last
  before an output sample is a measurable function of the draw.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## A function of two independent random variables -/

/-- **The mean of a function of two independent random variables** is the
mean, over the first, of its mean over the law of the second. -/
theorem lintegral_prodMk_of_indepFun {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {P : Measure Ω} [IsProbabilityMeasure P] {A : Ω → α} {B : Ω → β}
    (hA : AEMeasurable A P) (hB : AEMeasurable B P) (h : IndepFun A B P)
    {Φ : α × β → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (A ω, B ω) ∂P = ∫⁻ ω, ∫⁻ y, Φ (A ω, y) ∂(P.map B) ∂P := by
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hA hB).mp h
  have : IsProbabilityMeasure (P.map B) := (Measure.isProbabilityMeasure_map_iff hB).mpr
    inferInstance
  calc ∫⁻ ω, Φ (A ω, B ω) ∂P
      = ∫⁻ z, Φ z ∂(P.map fun ω => (A ω, B ω)) :=
        (lintegral_map' hΦ.aemeasurable (hA.prodMk hB)).symm
    _ = ∫⁻ z, Φ z ∂((P.map A).prod (P.map B)) := by rw [h1]
    _ = ∫⁻ x, ∫⁻ y, Φ (x, y) ∂(P.map B) ∂(P.map A) := lintegral_prod _ hΦ.aemeasurable
    _ = ∫⁻ ω, ∫⁻ y, Φ (A ω, y) ∂(P.map B) ∂P :=
        lintegral_map' hΦ.lintegral_prod_right'.aemeasurable hA

/-! ## The law of the paused time: no pause, and one pause -/

/-- The law of the paused time that begins in a period gives at least the
probability `exp (-count)` to no paused time. -/
theorem pauseLaw_ge_dirac (count : ℝ≥0) (F : Measure ℝ) :
    ENNReal.ofReal (Real.exp (-(count : ℝ))) • Measure.dirac (0 : ℝ) ≤ pauseLaw count F := by
  have h := Measure.le_sum (fun n : ℕ => poissonMeasure count {n} • sumLaw F n) 0
  have e : poissonMeasure count {0} • sumLaw F 0
      = ENNReal.ofReal (Real.exp (-(count : ℝ))) • Measure.dirac (0 : ℝ) := by
    rw [poissonMeasure_singleton]
    simp [sumLaw]
  rw [← e]
  exact h

/-- The law of the paused time that begins in a period is at least
`exp (-count) * count` times the law of the length of one pause. -/
theorem pauseLaw_ge_smul (count : ℝ≥0) (F : Measure ℝ) [SFinite F] :
    ENNReal.ofReal (Real.exp (-(count : ℝ)) * count) • F ≤ pauseLaw count F := by
  have h := Measure.le_sum (fun n : ℕ => poissonMeasure count {n} • sumLaw F n) 1
  have e : poissonMeasure count {1} • sumLaw F 1
      = ENNReal.ofReal (Real.exp (-(count : ℝ)) * count) • F := by
    rw [poissonMeasure_singleton]
    simp [sumLaw, Measure.dirac_zero_conv]
  rw [← e]
  exact h

/-- **The mean of a function of the paused time that begins in a period** is
at least `exp (-count)` times: its value at no paused time, plus `count`
times its mean over the length of one pause, counted only where the length
is not zero. -/
theorem lintegral_pauseLaw_ge (count : ℝ≥0) (F : Measure ℝ) [SFinite F] (g : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (Real.exp (-(count : ℝ)))
        * (g 0 + ENNReal.ofReal count * ∫⁻ x in {x : ℝ | x ≠ 0}, g x ∂F)
      ≤ ∫⁻ x, g x ∂(pauseLaw count F) := by
  classical
  have hsplit : ∫⁻ x, g x ∂(pauseLaw count F)
      = ∫⁻ x in ({0} : Set ℝ), g x ∂(pauseLaw count F)
        + ∫⁻ x in {x : ℝ | x ≠ 0}, g x ∂(pauseLaw count F) := by
    have hcompl : ({0} : Set ℝ)ᶜ = {x : ℝ | x ≠ 0} := rfl
    rw [← hcompl]
    exact (lintegral_add_compl g (measurableSet_singleton (0 : ℝ))).symm
  have h0 : ENNReal.ofReal (Real.exp (-(count : ℝ))) * g 0
      ≤ ∫⁻ x in ({0} : Set ℝ), g x ∂(pauseLaw count F) := by
    have hle := Measure.restrict_mono (subset_refl ({0} : Set ℝ)) (pauseLaw_ge_dirac count F)
    calc ENNReal.ofReal (Real.exp (-(count : ℝ))) * g 0
        = ∫⁻ x in ({0} : Set ℝ), g x
            ∂(ENNReal.ofReal (Real.exp (-(count : ℝ))) • Measure.dirac (0 : ℝ)) := by
          rw [Measure.restrict_smul, lintegral_smul_measure,
            setLIntegral_dirac g ({0} : Set ℝ)]
          simp
      _ ≤ ∫⁻ x in ({0} : Set ℝ), g x ∂(pauseLaw count F) := lintegral_mono' hle le_rfl
  have h1 : ENNReal.ofReal (Real.exp (-(count : ℝ)))
        * (ENNReal.ofReal count * ∫⁻ x in {x : ℝ | x ≠ 0}, g x ∂F)
      ≤ ∫⁻ x in {x : ℝ | x ≠ 0}, g x ∂(pauseLaw count F) := by
    have hle := Measure.restrict_mono (subset_refl {x : ℝ | x ≠ 0}) (pauseLaw_ge_smul count F)
    calc ENNReal.ofReal (Real.exp (-(count : ℝ)))
          * (ENNReal.ofReal count * ∫⁻ x in {x : ℝ | x ≠ 0}, g x ∂F)
        = ∫⁻ x in {x : ℝ | x ≠ 0}, g x
            ∂(ENNReal.ofReal (Real.exp (-(count : ℝ)) * count) • F) := by
          rw [Measure.restrict_smul, lintegral_smul_measure,
            ENNReal.ofReal_mul (Real.exp_pos _).le, smul_eq_mul, mul_assoc]
      _ ≤ ∫⁻ x in {x : ℝ | x ≠ 0}, g x ∂(pauseLaw count F) := lintegral_mono' hle le_rfl
  rw [hsplit, mul_add]
  exact add_le_add h0 h1

/-! ## The playback, from a measurable description -/

variable {H : Type} {R : ℕ}

/-- What a speaker plays at each output sample when, at output sample `k`,
it plays the source exactly for the draws of `S k`, and then the position
`G k` of the draw. -/
def describedPlays (S : ℕ → Set (Draw H R)) (G : ℕ → Draw H R → ℝ) (e : Draw H R) (k : ℕ) :
    Option ℝ := by
  classical
  exact if e ∈ S k then some (G k e) else none

/-- What is played at an output sample is what its description gives. -/
theorem eq_describedPlays {S : ℕ → Set (Draw H R)} {G : ℕ → Draw H R → ℝ} {e : Draw H R}
    {k : ℕ} {p : Option ℝ} (h : ∀ x : ℝ, p = some x ↔ e ∈ S k ∧ G k e = x) :
    p = describedPlays S G e k := by
  classical
  unfold describedPlays
  by_cases he : e ∈ S k
  · rw [ite_eq_left he]
    exact (h (G k e)).mpr ⟨he, rfl⟩
  · rw [ite_eq_right he]
    cases hp : p with
    | none => rfl
    | some x => exact absurd ((h x).mp hp).1 he

/-- **The position played last is a measurable function of the draw** when
what is played at each output sample is described by measurable sets and
measurable functions of the draw. -/
theorem measurable_getD_lastPlayed {S : ℕ → Set (Draw H R)} {G : ℕ → Draw H R → ℝ}
    (hS : ∀ k, MeasurableSet (S k)) (hG : ∀ k, Measurable (G k)) :
    ∀ K : ℕ, Measurable fun e : Draw H R => (lastPlayed (describedPlays S G e) K).getD 0
  | 0 => by
    have e0 : (fun e : Draw H R => (lastPlayed (describedPlays S G e) 0).getD 0)
        = fun _ => 0 := funext fun e => by simp [lastPlayed]
    rw [e0]
    exact measurable_const
  | K + 1 => by
    classical
    have ih := measurable_getD_lastPlayed hS hG K
    have e1 : (fun e : Draw H R => (lastPlayed (describedPlays S G e) (K + 1)).getD 0)
        = fun e => if e ∈ S K then G K e
          else (lastPlayed (describedPlays S G e) K).getD 0 := funext fun e => by
      by_cases he : e ∈ S K
      · have hp : describedPlays S G e K = some (G K e) := by
          unfold describedPlays
          rw [ite_eq_left he]
        rw [lastPlayed_succ_some hp, ite_eq_left he]
        rfl
      · have hp : describedPlays S G e K = none := by
          unfold describedPlays
          rw [ite_eq_right he]
        rw [lastPlayed_succ_none hp, ite_eq_right he]
    rw [e1]
    exact Measurable.ite (hS K) (hG K) ih

end Unisono.Spec.GenerativeWorld
