/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The limit of a function along the dyadic numbers

A function on the real numbers whose values at neighbouring dyadic numbers
differ by summable amounts has a continuous limit along the dyadic numbers.
This is the part of the construction of a process with continuous paths that
involves no probability (`Unisono.Spec.continuousModification`).

* `dyadicFloor n t` is the largest multiple of `1 / 2 ^ n` that is at most
  `t`.
* `StepsWithin y M d` says that, between `-M` and `M`, the values of `y` at
  two neighbouring multiples of `1 / 2 ^ n` differ by at most `d n`, for
  every `n`.
* `dyadicLimit y t` is the limit of `y (dyadicFloor n t)` as `n` grows.
* `StepsWithin.abs_dyadicLimit_sub_le`: when the bounds `d` are summable, the
  limits at two numbers that are at most `1 / 2 ^ n` apart differ by at most
  twice the sum of the bounds from `n` on.
* `StepsWithin.continuousOn_dyadicLimit`: so the limit is continuous between
  `-M` and `M`.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open Filter Topology

/-- The dyadic number with denominator `2 ^ n` at or below `t`. -/
def dyadicFloor (n : ℕ) (t : ℝ) : ℝ := (⌊t * 2 ^ n⌋ : ℝ) / 2 ^ n

theorem dyadicFloor_le (n : ℕ) (t : ℝ) : dyadicFloor n t ≤ t := by
  unfold dyadicFloor
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem lt_dyadicFloor_add (n : ℕ) (t : ℝ) : t < dyadicFloor n t + 1 / 2 ^ n := by
  unfold dyadicFloor
  rw [← add_div, lt_div_iff₀ (by positivity)]
  exact Int.lt_floor_add_one _

theorem abs_dyadicFloor_sub_le (n : ℕ) (t : ℝ) : |dyadicFloor n t - t| ≤ 1 / 2 ^ n := by
  have h1 := dyadicFloor_le n t
  have h2 := lt_dyadicFloor_add n t
  rw [abs_le]
  constructor <;> linarith

/-- The floor at the next level is twice the floor, or one more. -/
theorem floor_succ_eq (n : ℕ) (t : ℝ) :
    ⌊t * 2 ^ (n + 1)⌋ = 2 * ⌊t * 2 ^ n⌋ ∨ ⌊t * 2 ^ (n + 1)⌋ = 2 * ⌊t * 2 ^ n⌋ + 1 := by
  have h1 : (⌊t * 2 ^ n⌋ : ℝ) ≤ t * 2 ^ n := Int.floor_le _
  have h2 : t * 2 ^ n < ⌊t * 2 ^ n⌋ + 1 := Int.lt_floor_add_one _
  have e : t * 2 ^ (n + 1) = 2 * (t * 2 ^ n) := by ring
  have h3 : 2 * ⌊t * 2 ^ n⌋ ≤ ⌊t * 2 ^ (n + 1)⌋ := by
    rw [Int.le_floor, e]
    push_cast
    linarith
  have h4 : ⌊t * 2 ^ (n + 1)⌋ < 2 * ⌊t * 2 ^ n⌋ + 2 := by
    rw [Int.floor_lt, e]
    push_cast
    linarith
  omega

/-- The floor of a number from `-M` to below `M` is in the range of the
steps. -/
theorem floor_mem_range {M : ℕ} {t : ℝ} (h1 : -(M : ℝ) ≤ t) (h2 : t < M) (n : ℕ) :
    -(M : ℤ) * 2 ^ n ≤ ⌊t * 2 ^ n⌋ ∧ ⌊t * 2 ^ n⌋ < (M : ℤ) * 2 ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  constructor
  · rw [Int.le_floor]
    push_cast
    nlinarith
  · rw [Int.floor_lt]
    push_cast
    nlinarith

/-- **The steps of a function on the dyadic numbers from `-M` to `M` are at
most `d`**: at each level `n`, its values at neighbouring dyadic numbers with
denominator `2 ^ n` differ by at most `d n`. -/
structure StepsWithin (y : ℝ → ℝ) (M : ℕ) (d : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ d n
  step : ∀ (n : ℕ) (k : ℤ), -(M : ℤ) * 2 ^ n ≤ k → k < (M : ℤ) * 2 ^ n →
    |y (((k + 1 : ℤ) : ℝ) / 2 ^ n) - y ((k : ℝ) / 2 ^ n)| ≤ d n

variable {y : ℝ → ℝ} {M : ℕ} {d : ℕ → ℝ}

/-- From one level to the next, the value at the dyadic floor of `t` changes
by at most the step of the next level. -/
theorem StepsWithin.abs_succ_sub_le (h : StepsWithin y M d) {t : ℝ} (h1 : -(M : ℝ) ≤ t)
    (h2 : t < M) (n : ℕ) :
    |y (dyadicFloor (n + 1) t) - y (dyadicFloor n t)| ≤ d (n + 1) := by
  obtain ⟨hr1, hr2⟩ := floor_mem_range h1 h2 n
  have hfl : dyadicFloor n t = ((2 * ⌊t * 2 ^ n⌋ : ℤ) : ℝ) / 2 ^ (n + 1) := by
    unfold dyadicFloor
    push_cast
    rw [pow_succ]
    field_simp
  rcases floor_succ_eq n t with h0 | h0
  · have : dyadicFloor (n + 1) t = dyadicFloor n t := by
      rw [hfl]
      unfold dyadicFloor
      rw [h0]
    rw [this, sub_self, abs_zero]
    exact h.nonneg _
  · have hs := h.step (n + 1) (2 * ⌊t * 2 ^ n⌋) (by rw [pow_succ]; linarith)
      (by rw [pow_succ]; linarith)
    have : dyadicFloor (n + 1) t = ((2 * ⌊t * 2 ^ n⌋ + 1 : ℤ) : ℝ) / 2 ^ (n + 1) := by
      unfold dyadicFloor
      rw [h0]
    rw [this, hfl]
    exact hs

/-- The values at the dyadic floors of two numbers that are at most one step
of level `n` apart differ by at most the step of that level. -/
theorem StepsWithin.abs_sub_le_of_near (h : StepsWithin y M d) {s t : ℝ}
    (hs1 : -(M : ℝ) ≤ s) (hs2 : s < M) (ht1 : -(M : ℝ) ≤ t) (ht2 : t < M) {n : ℕ}
    (hst : |s - t| ≤ 1 / 2 ^ n) :
    |y (dyadicFloor n s) - y (dyadicFloor n t)| ≤ d n := by
  wlog hle : s ≤ t generalizing s t
  · rw [abs_sub_comm]
    exact this ht1 ht2 hs1 hs2 (by rwa [abs_sub_comm]) (le_of_not_ge hle)
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hmono : ⌊s * 2 ^ n⌋ ≤ ⌊t * 2 ^ n⌋ := Int.floor_mono (by nlinarith)
  have hnear : ⌊t * 2 ^ n⌋ < ⌊s * 2 ^ n⌋ + 2 := by
    rw [Int.floor_lt]
    push_cast
    have h1 : (⌊s * 2 ^ n⌋ : ℝ) + 1 > s * 2 ^ n := Int.lt_floor_add_one _
    have h2 : t - s ≤ 1 / 2 ^ n := by
      have := (abs_le.mp hst).1
      linarith
    have h3 : (t - s) * 2 ^ n ≤ 1 := by
      calc (t - s) * 2 ^ n ≤ 1 / 2 ^ n * 2 ^ n := by gcongr
        _ = 1 := by field_simp
    nlinarith
  rcases (by omega : ⌊t * 2 ^ n⌋ = ⌊s * 2 ^ n⌋ ∨ ⌊t * 2 ^ n⌋ = ⌊s * 2 ^ n⌋ + 1) with h0 | h0
  · unfold dyadicFloor
    rw [h0, sub_self, abs_zero]
    exact h.nonneg _
  · obtain ⟨hr1, hr2⟩ := floor_mem_range hs1 hs2 n
    have := h.step n ⌊s * 2 ^ n⌋ hr1 hr2
    unfold dyadicFloor
    rw [h0, abs_sub_comm]
    exact this

/-- **The limit of the values at the dyadic floors of `t`.** -/
def dyadicLimit (y : ℝ → ℝ) (t : ℝ) : ℝ := limUnder atTop fun n => y (dyadicFloor n t)

/-- With summable steps, the values at the dyadic floors of `t` converge. -/
theorem StepsWithin.tendsto_dyadicLimit (h : StepsWithin y M d) (hd : Summable d) {t : ℝ}
    (h1 : -(M : ℝ) ≤ t) (h2 : t < M) :
    Tendsto (fun n => y (dyadicFloor n t)) atTop (𝓝 (dyadicLimit y t)) := by
  have hsum : Summable fun n => dist (y (dyadicFloor n t)) (y (dyadicFloor n.succ t)) := by
    refine Summable.of_nonneg_of_le (fun _ => dist_nonneg) (fun n => ?_)
      ((summable_nat_add_iff 1).mpr hd)
    rw [dist_comm, Real.dist_eq]
    exact h.abs_succ_sub_le h1 h2 n
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
  have hlim : dyadicLimit y t = a := ha.limUnder_eq
  rw [hlim]
  exact ha

/-- The value at the dyadic floor of level `n` is within the sum of the later
steps of the limit. -/
theorem StepsWithin.abs_sub_dyadicLimit_le (h : StepsWithin y M d) (hd : Summable d) {t : ℝ}
    (h1 : -(M : ℝ) ≤ t) (h2 : t < M) (n : ℕ) :
    |y (dyadicFloor n t) - dyadicLimit y t| ≤ ∑' m, d (n + m + 1) := by
  have hd' : Summable fun n => d (n + 1) := (summable_nat_add_iff 1).mpr hd
  have := dist_le_tsum_of_dist_le_of_tendsto (fun n => d (n + 1))
    (fun n => by
      rw [dist_comm, Real.dist_eq]
      exact h.abs_succ_sub_le h1 h2 n) hd' (h.tendsto_dyadicLimit hd h1 h2) n
  rwa [Real.dist_eq] at this

/-- **The limits at two numbers that are at most one step of level `n` apart
differ by at most twice the sum of the steps from level `n` on.** -/
theorem StepsWithin.abs_dyadicLimit_sub_le (h : StepsWithin y M d) (hd : Summable d)
    {s t : ℝ} (hs1 : -(M : ℝ) ≤ s) (hs2 : s < M) (ht1 : -(M : ℝ) ≤ t) (ht2 : t < M) {n : ℕ}
    (hst : |s - t| ≤ 1 / 2 ^ n) :
    |dyadicLimit y s - dyadicLimit y t| ≤ 2 * ∑' m, d (n + m) := by
  have ha := h.abs_sub_dyadicLimit_le hd hs1 hs2 n
  have hb := h.abs_sub_dyadicLimit_le hd ht1 ht2 n
  have hc := h.abs_sub_le_of_near hs1 hs2 ht1 ht2 hst
  have hd' : Summable fun m => d (n + m) := by
    simpa [add_comm] using (summable_nat_add_iff n).mpr hd
  have hsplit : ∑' m, d (n + m) = d n + ∑' m, d (n + m + 1) := by
    rw [hd'.tsum_eq_zero_add]
    simp [add_assoc]
  have htail : 0 ≤ ∑' m, d (n + m + 1) := tsum_nonneg fun _ => h.nonneg _
  have habs : |dyadicLimit y s - dyadicLimit y t|
      ≤ |y (dyadicFloor n s) - dyadicLimit y s| + |y (dyadicFloor n s) - y (dyadicFloor n t)|
        + |y (dyadicFloor n t) - dyadicLimit y t| := by
    have e : dyadicLimit y s - dyadicLimit y t
        = -(y (dyadicFloor n s) - dyadicLimit y s) + (y (dyadicFloor n s) - y (dyadicFloor n t))
          + (y (dyadicFloor n t) - dyadicLimit y t) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans ?_) le_rfl
    rw [abs_neg]
  have := h.nonneg n
  linarith

/-- **With summable steps, the limit is continuous between `-M` and `M`.** -/
theorem StepsWithin.continuousOn_dyadicLimit (h : StepsWithin y M d) (hd : Summable d) :
    ContinuousOn (dyadicLimit y) (Set.Ioo (-(M : ℝ)) M) := by
  have htail : Tendsto (fun n => 2 * ∑' m, d (n + m)) atTop (𝓝 0) := by
    have := tendsto_sum_nat_add d
    have h2 : Tendsto (fun n => 2 * ∑' m, d (m + n)) atTop (𝓝 (2 * 0)) := this.const_mul 2
    simpa [add_comm] using h2
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨n, hn⟩ := ((htail.eventually (gt_mem_nhds hε)).exists)
  refine ⟨1 / 2 ^ n, by positivity, fun s hs hst => ?_⟩
  rw [Real.dist_eq] at hst ⊢
  exact lt_of_le_of_lt
    (h.abs_dyadicLimit_sub_le hd hs.1.le hs.2 ht.1.le ht.2 hst.le) hn


end Unisono.Spec
