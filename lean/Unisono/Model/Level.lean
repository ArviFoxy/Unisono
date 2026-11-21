/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Tactic.Linarith

/-!
# What is expected of the next stretch

The sender chooses the level from the needs of the stretches it has seen. For
each stretch it keeps a record: the need of the stretch before it and its
own. A level costs, in a stretch, what the record of the stretch says
(`stretchCost`), and the level is chosen to make the mean of that cost over
the next stretch small. This file states what that mean is taken over, and
proves the two facts it rests on.

* **A need larger than all that were seen.** When nothing sets the next
  stretch apart from the `m` seen, that is, when the law of the `m + 1` needs
  is the same in every order, and no two needs are equal, the next need is the
  largest of them with the probability `1 / (m + 1)` (`measure_largest`). No
  further assumption about the law is used.

* **The mean.** The next stretch is taken to be one of the stretches seen,
  each as likely as the others, or, as likely as each of them, a stretch whose
  record is drawn from a law `ν` of stretches that need more than all seen.
  The mean of any cost over that is the mean of the cost under `ν` plus its
  sum over the stretches seen, divided by `m + 1` (`integral_predictive`).
-/

@[expose] public noncomputable section

namespace Unisono.Model.Level

open MeasureTheory
open scoped ENNReal

/-! ## A need larger than all that were seen -/

/-- The needs `x` of which the need at place `i` is the largest, strictly. -/
def largestAt {n : ℕ} (i : Fin n) : Set (Fin n → ℝ) := {x | ∀ j, j ≠ i → x j < x i}

theorem measurableSet_largestAt {n : ℕ} (i : Fin n) : MeasurableSet (largestAt i) := by
  have : largestAt i = ⋂ j, ⋂ (_ : j ≠ i), {x : Fin n → ℝ | x j < x i} := by
    ext x
    simp [largestAt]
  rw [this]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

/-- **The next need is the largest with the probability one in the number of
needs.** For `n` needs whose law is the same in every order, and of which no
two are equal, each of them is the largest with the probability `1 / n`. -/
theorem measure_largest {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (horder : ∀ σ : Equiv.Perm (Fin n), μ.map (fun x => x ∘ σ) = μ)
    (hties : μ {x | ∃ i j, i ≠ j ∧ x i = x j} = 0) (i : Fin n) :
    μ (largestAt i) = (n : ℝ≥0∞)⁻¹ := by
  -- every place is the largest with the same probability
  have hsame : ∀ k, μ (largestAt k) = μ (largestAt i) := by
    intro k
    have hmap : Measurable fun x : Fin n → ℝ => x ∘ (Equiv.swap i k) :=
      measurable_pi_iff.mpr fun j => measurable_pi_apply _
    have hpre : (fun x : Fin n → ℝ => x ∘ (Equiv.swap i k)) ⁻¹' (largestAt i) = largestAt k := by
      ext x
      simp only [Set.mem_preimage, largestAt, Set.mem_ofPred_eq, Function.comp_apply,
        Equiv.swap_apply_left]
      constructor
      · intro h j hj
        have := h (Equiv.swap i k j) (by
          intro hcon
          apply hj
          have := congrArg (Equiv.swap i k) hcon
          simpa using this)
        simpa using this
      · intro h j hj
        exact h (Equiv.swap i k j) (by
          intro hcon
          apply hj
          have := congrArg (Equiv.swap i k) hcon
          simpa using this)
    rw [← hpre, ← Measure.map_apply hmap (measurableSet_largestAt i), horder]
  -- no two places are the largest at once
  have hdisjoint : Pairwise (Function.onFun Disjoint (largestAt (n := n))) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro x ha hb
    have h1 := ha b (Ne.symm hab)
    have h2 := hb a hab
    exact lt_asymm h1 h2
  -- and unless two needs are equal, one place is
  have hcover : μ (⋃ k, largestAt k) = 1 := by
    have hsub : (⋃ k, largestAt k)ᶜ ⊆ {x : Fin n → ℝ | ∃ i j, i ≠ j ∧ x i = x j} := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hx
      obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ x ⟨i, Finset.mem_univ i⟩
      have hnot := hx k
      simp only [largestAt, Set.mem_ofPred_eq, not_forall] at hnot
      obtain ⟨j, hj, hjk⟩ := hnot
      exact ⟨j, k, hj, le_antisymm (hk j (Finset.mem_univ j)) (not_lt.mp hjk)⟩
    have hzero : μ (⋃ k, largestAt k)ᶜ = 0 := measure_mono_null hsub hties
    have hmeas : MeasurableSet (⋃ k, largestAt (n := n) k) :=
      MeasurableSet.iUnion fun k => measurableSet_largestAt k
    rwa [prob_compl_eq_zero_iff hmeas] at hzero
  rw [measure_iUnion hdisjoint measurableSet_largestAt, tsum_fintype] at hcover
  simp only [hsame, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcover
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hcover)

/-! ## The mean over the next stretch -/

/-- What a stretch costs at the level `l`, when the stretch before it needed
`r.1` and it needs `r.2`: `gap` if a gap starts in it, and `missed` for each
second of its frames that are missed, of which there are `min (r.2 - l) D`
when it needs more than the level and its length is `D`. -/
def stretchCost (gap missed D l : ℝ) (r : ℝ × ℝ) : ℝ :=
  gap * (if r.1 ≤ l ∧ l < r.2 then 1 else 0) + missed * min (max (r.2 - l) 0) D

/-- A stretch costs nothing at a level that it does not need more than. -/
theorem stretchCost_eq_zero {gap missed D l : ℝ} {r : ℝ × ℝ} (hD : 0 ≤ D) (h : r.2 ≤ l) :
    stretchCost gap missed D l r = 0 := by
  have h1 : ¬(r.1 ≤ l ∧ l < r.2) := fun hc => absurd hc.2 (not_lt.mpr h)
  have h2 : max (r.2 - l) 0 = 0 := max_eq_right (by linarith)
  simp [stretchCost, h1, h2, hD]

/-- The law that the next stretch is taken to have, given the records `rs` of
the stretches seen and the law `ν` of the record of a stretch that needs more
than all of them: each stretch seen, and such a stretch, with the same
weight. -/
def predictive (rs : List (ℝ × ℝ)) (ν : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  ((rs.length : ℝ≥0∞) + 1)⁻¹ • (ν + (rs.map Measure.dirac).sum)

/-- The mean of a cost over the stretches seen, each counted once. -/
theorem integral_sum_dirac (rs : List (ℝ × ℝ)) (c : ℝ × ℝ → ℝ) :
    Integrable c (rs.map Measure.dirac).sum
      ∧ ∫ r, c r ∂(rs.map Measure.dirac).sum = (rs.map c).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hdirac : Integrable c (Measure.dirac r) := integrable_dirac eNorm_lt_top
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hdirac.add_measure ih.1, ?_⟩
    rw [integral_add_measure hdirac ih.1, ih.2, integral_dirac]

/-- **The mean of a cost over the next stretch.** It is the mean of the cost
over a stretch that needs more than all seen, plus the sum of the cost over
the stretches seen, divided by their number and one. -/
theorem integral_predictive (rs : List (ℝ × ℝ)) (ν : Measure (ℝ × ℝ)) (c : ℝ × ℝ → ℝ)
    (hν : Integrable c ν) :
    ∫ r, c r ∂(predictive rs ν) = (∫ r, c r ∂ν + (rs.map c).sum) / (rs.length + 1) := by
  obtain ⟨hint, hsum⟩ := integral_sum_dirac rs c
  simp only [predictive]
  rw [integral_smul_measure, integral_add_measure hν hint, hsum]
  have hne : ((rs.length : ℝ≥0∞) + 1) ≠ 0 := by positivity
  have htop : ((rs.length : ℝ≥0∞) + 1) ≠ ⊤ := by simp
  rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_one, smul_eq_mul]
  rw [inv_mul_eq_div]

end Unisono.Model.Level
