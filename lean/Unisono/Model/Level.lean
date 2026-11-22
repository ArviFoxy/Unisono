/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

Two further things that the choice rests on are stated here.

* **The frames that a stretch misses.** A pause holds back every frame
  captured while it lasts, and a frame captured later in it waited that much
  less. Of a stretch in which a pause begins, the level therefore misses the
  frames captured in the first `y - l` seconds from the start of the pause,
  where `y` is the largest need of the stretch and `l` the level. The count
  `min (y - l) D` used in `stretchCost` is that time when the pause begins
  with the stretch, and never less than it (`volume_missed`, `missed_le`,
  `missed_ge`).

* **When moving the level pays.** A move costs `c` once and saves `s` per
  second for as long as the needs keep the law they have. If the moment of
  the choice is as likely to lie in any part of that time as in any other,
  and the needs have kept their law for `T` so far, they keep it for more
  than `t` longer with the probability `T / (T + t)` (`volume_lasts`). The
  move then more likely than not pays for itself exactly when `s T > c`
  (`move_pays_iff`).
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

private theorem largestAt_measure_eq {n : ℕ} (μ : Measure (Fin n → ℝ))
    (horder : ∀ σ : Equiv.Perm (Fin n), μ.map (fun x => x ∘ σ) = μ) (i k : Fin n) :
    μ (largestAt k) = μ (largestAt i) := by
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

private theorem largestAt_pairwise_disjoint {n : ℕ} :
    Pairwise (Function.onFun Disjoint (largestAt (n := n))) := by
  intro a b hab
  rw [Function.onFun, Set.disjoint_left]
  intro x ha hb
  have h1 := ha b (Ne.symm hab)
  have h2 := hb a hab
  exact lt_asymm h1 h2

/-- **Even when ties are allowed, a place is strictly largest with probability
at most `1 / n`.** For `n` exchangeable needs, without any no-ties assumption,
each place is strictly larger than all others with probability at most `1 / n`. -/
theorem measure_largest_le {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (horder : ∀ σ : Equiv.Perm (Fin n), μ.map (fun x => x ∘ σ) = μ) (i : Fin n) :
    μ (largestAt i) ≤ (n : ℝ≥0∞)⁻¹ := by
  have hle : μ (⋃ k, largestAt k) ≤ 1 := by
    calc μ (⋃ k, largestAt k) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  rw [measure_iUnion largestAt_pairwise_disjoint measurableSet_largestAt, tsum_fintype] at hle
  simp only [largestAt_measure_eq μ horder i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hle
  have hne0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_ne_zero (Fin.pos i).ne').ne'
  have hnetop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  rw [← one_div, ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnetop), mul_comm]
  exact hle

/-- **The next need is the largest with the probability one in the number of
needs.** For `n` needs whose law is the same in every order, and of which no
two are equal, each of them is the largest with the probability `1 / n`. -/
theorem measure_largest {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (horder : ∀ σ : Equiv.Perm (Fin n), μ.map (fun x => x ∘ σ) = μ)
    (hties : μ {x | ∃ i j, i ≠ j ∧ x i = x j} = 0) (i : Fin n) :
    μ (largestAt i) = (n : ℝ≥0∞)⁻¹ := by
  -- unless two needs are equal, one place is strictly largest
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
  rw [measure_iUnion largestAt_pairwise_disjoint measurableSet_largestAt, tsum_fintype] at hcover
  simp only [largestAt_measure_eq μ horder i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hcover
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

/-! ## The frames that a stretch misses -/

/-- The need of the frame captured at the time `t`, when a pause that began at
the time `t₀` holds back every frame captured from then on, and the frame
captured at `t₀` needs `y`: a frame captured later waited that much less. -/
def pausedNeed (y t₀ t : ℝ) : ℝ := y - (t - t₀)

/-- The level misses the frames captured before `y - l` has passed since the
pause began. -/
theorem lt_pausedNeed_iff {l y t₀ t : ℝ} : l < pausedNeed y t₀ t ↔ t < t₀ + (y - l) := by
  simp only [pausedNeed]
  constructor <;> intro h <;> linarith

/-- **The time for which a stretch is missed.** Of a stretch that begins at
`a` and lasts `D`, in which a pause begins at `t₀`, the frames captured from
`t₀` on that the level `l` misses were captured over `min (y - l) (a + D - t₀)`
seconds, where `y` is the need of the frame captured at `t₀`: the largest
need of the stretch. -/
theorem volume_missed {D l y a t₀ : ℝ} :
    volume {t : ℝ | t₀ ≤ t ∧ t < a + D ∧ l < pausedNeed y t₀ t}
      = ENNReal.ofReal (min (y - l) (a + D - t₀)) := by
  have hset : {t : ℝ | t₀ ≤ t ∧ t < a + D ∧ l < pausedNeed y t₀ t}
      = Set.Ico t₀ (min (t₀ + (y - l)) (a + D)) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Ico, lt_pausedNeed_iff, lt_min_iff]
    tauto
  rw [hset, Real.volume_Ico]
  congr 1
  rcases le_total (y - l) (a + D - t₀) with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, min_eq_right (by linarith)]

/-- The count of missed time in `stretchCost` is never less than the time for
which the stretch is missed. -/
theorem missed_le {D l y a t₀ : ℝ} (ha : a ≤ t₀) :
    min (y - l) (a + D - t₀) ≤ min (max (y - l) 0) D :=
  le_min (le_trans (min_le_left _ _) (le_max_left _ _))
    (le_trans (min_le_right _ _) (by linarith))

/-- It is more than that time by at most the time from the start of the
stretch to the start of the pause, and so equal to it for a pause that begins
with the stretch and a need above the level. -/
theorem missed_ge {D l y a t₀ : ℝ} (ha : a ≤ t₀) (hy : l ≤ y) :
    min (max (y - l) 0) D - (t₀ - a) ≤ min (y - l) (a + D - t₀) := by
  rw [max_eq_left (by linarith)]
  refine le_min ?_ ?_
  · linarith [min_le_left (y - l) D]
  · linarith [min_le_right (y - l) D]

/-! ## When moving the level pays -/

/-- The probability that needs which have kept their law for `T` keep it for
more than `t` longer. -/
def lasts (T t : ℝ) : ℝ := T / (T + t)

/-- **Where the probability comes from.** Let the needs keep their law over a
time of which the part `u` has passed at the moment of the choice, so that
the whole time is `T / u` when `T` has passed. If `u` is as likely to be in
any part of the range from 0 to 1 as in any other, the time that remains,
`T / u - T`, is more than `t` with the probability `T / (T + t)`. -/
theorem volume_lasts {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) :
    volume {u : ℝ | 0 < u ∧ u < 1 ∧ t < T / u - T} = ENNReal.ofReal (lasts T t) := by
  have hsum : 0 < T + t := by linarith
  have hset : {u : ℝ | 0 < u ∧ u < 1 ∧ t < T / u - T} = Set.Ioo 0 (T / (T + t)) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨hu0, -, hmore⟩
      refine ⟨hu0, ?_⟩
      have h1 : T + t < T / u := by linarith
      rw [lt_div_iff₀ hu0] at h1
      rw [lt_div_iff₀ hsum]
      linarith
    · rintro ⟨hu0, hu⟩
      have h1 : u * (T + t) < T := (lt_div_iff₀ hsum).mp hu
      have hle : T / (T + t) ≤ 1 := (div_le_one hsum).mpr (by linarith)
      refine ⟨hu0, lt_of_lt_of_le hu hle, ?_⟩
      have h2 : T + t < T / u := by
        rw [lt_div_iff₀ hu0]
        linarith
      linarith
  rw [hset, Real.volume_Ioo, sub_zero, lasts]

/-- **A move more likely than not pays for itself exactly when what it saves
over the time of the evidence exceeds its cost.** The move costs `c` and
saves `s` per second, so it pays for itself when the needs keep their law for
more than `c / s` longer. -/
theorem move_pays_iff {T s c : ℝ} (hT : 0 < T) (hs : 0 < s) (hc : 0 ≤ c) :
    1 / 2 < lasts T (c / s) ↔ c < s * T := by
  have hquot : 0 ≤ c / s := div_nonneg hc hs.le
  have hden : 0 < T + c / s := by linarith
  rw [lasts, lt_div_iff₀ hden]
  constructor
  · intro h
    have h1 : c / s < T := by linarith
    rw [div_lt_iff₀ hs] at h1
    linarith
  · intro h
    have h1 : c / s < T := by
      rw [div_lt_iff₀ hs]
      linarith
    linarith

end Unisono.Model.Level
