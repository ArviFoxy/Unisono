/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.IncrementParts
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.HasLaw

/-!
# A value of an independent sequence at a random place

Let `ℓ` be a sequence of independent values with one law `F`, numbered by
the whole numbers, and let `N` be a random whole number and `Y` any other
random variable, such that `ℓ` is independent of the pair of `N` and `Y`.
Then the value `ℓ (N + 1)`, one place after the random number, has the law
`F`, and it is independent of everything else: the sequence with that value
set to zero, the number `N`, and `Y` (`indepFun_randomIndex`).

The generative model with jitter uses this for the value that the jitter of
a link takes at its first redraw after a true time: the number of redraws
until that time is random, the value drawn at the next redraw has the law of
the link, and it is independent of everything that came before.

* `indepFun_apply_update`: under independent copies of one law, a value of
  the sequence is independent of the sequence with that value set to zero.
* `afterIndex`, `withoutAfterIndex`: the value one place after the number,
  and everything else, as functions of the sequence, the number and the
  other variable.
* `hasLaw_afterIndex`, `indepFun_afterIndex`: the statement for the product
  of the law of the sequence with any law of the number and the other
  variable.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Under independent copies of one law, a value of the sequence is
independent of the sequence with that value set to zero.** -/
theorem indepFun_apply_update (F : Measure ℝ) [IsProbabilityMeasure F] (k : ℤ) :
    IndepFun (fun x : ℤ → ℝ => x k) (fun x : ℤ → ℝ => Function.update x k 0)
      (Measure.infinitePi fun _ : ℤ => F) := by
  classical
  have hI : iIndepFun (fun (i : ℤ) (x : ℤ → ℝ) => x i) (Measure.infinitePi fun _ : ℤ => F) :=
    iIndepFun_infinitePi (P := fun _ : ℤ => F) (X := fun _ => id) fun _ => measurable_id
  have hdisj : Disjoint ({k} : Set ℤ) {i | i ≠ k} :=
    Set.disjoint_left.mpr fun i (h1 : i = k) (h2 : i ≠ k) => h2 h1
  have h := iIndepFun.indepFun_set₀ hdisj hI fun i => (measurable_pi_apply i).aemeasurable
  have hψ : Measurable fun (v : ({i : ℤ | i ≠ k} → ℝ)) (i : ℤ) =>
      if hi : i = k then (0 : ℝ) else v ⟨i, hi⟩ := by
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases hi : i = k
    · simp only [hi, dite_true]
      exact measurable_const
    · simp only [hi, dite_false]
      exact measurable_pi_apply _
  have hφ : Measurable fun v : (({k} : Set ℤ) → ℝ) => v ⟨k, rfl⟩ :=
    measurable_pi_apply (⟨k, rfl⟩ : ({k} : Set ℤ))
  have h2 := h.comp hφ hψ
  have e : ((fun (v : ({i : ℤ | i ≠ k} → ℝ)) (i : ℤ) =>
        if hi : i = k then (0 : ℝ) else v ⟨i, hi⟩)
        ∘ fun (x : ℤ → ℝ) (j : {i : ℤ | i ≠ k}) => x j)
      = fun x : ℤ → ℝ => Function.update x k 0 := by
    funext x i
    by_cases hi : i = k
    · simp [hi]
    · simp [hi]
  rw [e] at h2
  exact h2

variable {𝒴 : Type*} [MeasurableSpace 𝒴]

/-- The value of the sequence one place after the number. -/
def afterIndex (p : (ℤ → ℝ) × ℤ × 𝒴) : ℝ := p.1 (p.2.1 + 1)

/-- Everything else: the sequence with the value one place after the number
set to zero, the number, and the other variable. -/
def withoutAfterIndex (p : (ℤ → ℝ) × ℤ × 𝒴) : (ℤ → ℝ) × ℤ × 𝒴 :=
  (Function.update p.1 (p.2.1 + 1) 0, p.2)

theorem measurable_afterIndex : Measurable (afterIndex (𝒴 := 𝒴)) := by
  have h : Measurable fun q : ((ℤ → ℝ) × 𝒴) × ℤ => q.1.1 (q.2 + 1) :=
    measurable_from_prod_countable_left fun n =>
      (measurable_pi_apply (n + 1)).comp measurable_fst
  exact h.comp ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_snd))

theorem measurable_withoutAfterIndex : Measurable (withoutAfterIndex (𝒴 := 𝒴)) := by
  classical
  have h : Measurable fun q : ((ℤ → ℝ) × 𝒴) × ℤ => Function.update q.1.1 (q.2 + 1) 0 := by
    refine measurable_from_prod_countable_left fun n => measurable_pi_iff.mpr fun i => ?_
    by_cases hi : i = n + 1
    · simp only [hi, Function.update_self]
      exact measurable_const
    · simp only [Function.update_of_ne hi]
      exact (measurable_pi_apply i).comp measurable_fst
  exact (h.comp ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_snd))).prodMk measurable_snd

section Product

variable (F : Measure ℝ) [IsProbabilityMeasure F] (ν : Measure (ℤ × 𝒴)) [IsProbabilityMeasure ν]

/-- The probability that the value one place after the number lies in `s`
and everything else lies in `t` is the mass that the law gives to `s` times
the probability that everything else lies in `t`. -/
theorem prod_afterIndex_inter {s : Set ℝ} (hs : MeasurableSet s)
    {t : Set ((ℤ → ℝ) × ℤ × 𝒴)} (ht : MeasurableSet t) :
    ((Measure.infinitePi fun _ : ℤ => F).prod ν) (afterIndex ⁻¹' s ∩ withoutAfterIndex ⁻¹' t)
      = F s * ((Measure.infinitePi fun _ : ℤ => F).prod ν) (withoutAfterIndex ⁻¹' t) := by
  have hm1 : MeasurableSet (afterIndex (𝒴 := 𝒴) ⁻¹' s) := measurable_afterIndex hs
  have hm2 : MeasurableSet (withoutAfterIndex (𝒴 := 𝒴) ⁻¹' t) := measurable_withoutAfterIndex ht
  rw [Measure.prod_apply_symm (hm1.inter hm2), Measure.prod_apply_symm hm2,
    ← lintegral_const_mul' _ _ (measure_ne_top F s)]
  refine lintegral_congr fun z => ?_
  -- For a fixed number and a fixed other variable, the two events are independent.
  have hsec : MeasurableSet {x : ℤ → ℝ | (x, z) ∈ t} := measurable_prodMk_right ht
  have hind := (indepFun_iff_measure_inter_preimage_eq_mul.mp
    (indepFun_apply_update F (z.1 + 1))) s {x : ℤ → ℝ | (x, z) ∈ t} hs hsec
  have hmarg : (Measure.infinitePi fun _ : ℤ => F) ((fun x : ℤ → ℝ => x (z.1 + 1)) ⁻¹' s)
      = F s := by
    have := (measurePreserving_eval_infinitePi (fun _ : ℤ => F) (z.1 + 1)).measure_preimage
      hs.nullMeasurableSet
    exact this
  rw [hmarg] at hind
  exact hind

/-- **The value one place after the number has the law of the sequence's
values.** -/
theorem hasLaw_afterIndex :
    HasLaw (afterIndex (𝒴 := 𝒴)) F ((Measure.infinitePi fun _ : ℤ => F).prod ν) := by
  refine ⟨measurable_afterIndex.aemeasurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply measurable_afterIndex hs]
  have h := prod_afterIndex_inter F ν hs (t := Set.univ) MeasurableSet.univ
  simpa using h

/-- **The value one place after the number is independent of everything
else.** -/
theorem indepFun_afterIndex :
    IndepFun (afterIndex (𝒴 := 𝒴)) withoutAfterIndex
      ((Measure.infinitePi fun _ : ℤ => F).prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  rw [prod_afterIndex_inter F ν hs ht]
  have h := (hasLaw_afterIndex F ν).map_eq
  rw [← Measure.map_apply measurable_afterIndex hs, h]

end Product

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **A value of an independent sequence at a random place.** Let the
sequence `ℓ` have the law of independent copies of `F`, and be independent
of the pair of a random whole number `N` and another random variable `Y`.
Then the value `ℓ (N + 1)` has the law `F`, and it is independent of the
sequence with that value set to zero together with `N` and `Y`. -/
theorem indepFun_randomIndex [IsProbabilityMeasure P] {F : Measure ℝ} [IsProbabilityMeasure F]
    {ℓ : Ω → ℤ → ℝ} {N : Ω → ℤ} {Y : Ω → 𝒴}
    (hℓ : HasLaw ℓ (Measure.infinitePi fun _ : ℤ => F) P) (hN : AEMeasurable N P)
    (hY : AEMeasurable Y P) (hind : IndepFun ℓ (fun ω => (N ω, Y ω)) P) :
    HasLaw (fun ω => ℓ ω (N ω + 1)) F P
      ∧ IndepFun (fun ω => ℓ ω (N ω + 1))
        (fun ω => (Function.update (ℓ ω) (N ω + 1) 0, N ω, Y ω)) P := by
  have hNY : AEMeasurable (fun ω => (N ω, Y ω)) P := hN.prodMk hY
  have hZ : AEMeasurable (fun ω => (ℓ ω, N ω, Y ω)) P := hℓ.aemeasurable.prodMk hNY
  have : IsProbabilityMeasure (P.map fun ω => (N ω, Y ω)) :=
    (Measure.isProbabilityMeasure_map_iff hNY).mpr inferInstance
  have hlaw : P.map (fun ω => (ℓ ω, N ω, Y ω))
      = (Measure.infinitePi fun _ : ℤ => F).prod (P.map fun ω => (N ω, Y ω)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hℓ.aemeasurable hNY).mp hind, hℓ.map_eq]
  have hZlaw : HasLaw (fun ω => (ℓ ω, N ω, Y ω))
      ((Measure.infinitePi fun _ : ℤ => F).prod (P.map fun ω => (N ω, Y ω))) P := ⟨hZ, hlaw⟩
  refine ⟨(hasLaw_afterIndex F _).comp hZlaw, ?_⟩
  have h := indepFun_afterIndex F (P.map fun ω => (N ω, Y ω))
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have key : ∀ A : Set ((ℤ → ℝ) × ℤ × 𝒴), MeasurableSet A →
      P ((fun ω => (ℓ ω, N ω, Y ω)) ⁻¹' A)
        = ((Measure.infinitePi fun _ : ℤ => F).prod (P.map fun ω => (N ω, Y ω))) A :=
    fun A hA => by rw [← hlaw, Measure.map_apply_of_aemeasurable hZ hA]
  have e1 : (fun ω => ℓ ω (N ω + 1)) ⁻¹' s
      = (fun ω => (ℓ ω, N ω, Y ω)) ⁻¹' (afterIndex ⁻¹' s) := rfl
  have e2 : (fun ω => (Function.update (ℓ ω) (N ω + 1) 0, N ω, Y ω)) ⁻¹' t
      = (fun ω => (ℓ ω, N ω, Y ω)) ⁻¹' (withoutAfterIndex ⁻¹' t) := rfl
  rw [e1, e2, ← Set.preimage_inter,
    key _ ((measurable_afterIndex hs).inter (measurable_withoutAfterIndex ht)),
    key _ (measurable_afterIndex hs), key _ (measurable_withoutAfterIndex ht)]
  exact h s t hs ht

end Unisono.Spec
