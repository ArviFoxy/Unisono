/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A line fitted to weighted samples

Sample `j` of a finite set `s` has a time `t j`, a value `z j` and a weight
`w j`. The fitted line is the one with the smallest weighted sum of squared
residuals. It is described by its value at a reference time `t₀` and its
slope, both computed from five weighted sums.

This is the estimator of a clock relation: the times are stamps of the
sender's clock, the values are differences of the receiver's and the sender's
stamps, and the weights fall with the age of a sample.
-/

@[expose] public noncomputable section

open Finset

namespace Unisono.Model.LineFit

variable {ι : Type*} (s : Finset ι) (w t z : ι → ℝ) (t₀ : ℝ)

/-- The weighted moment of order `m` of the sample times about `t₀`. -/
def moment (m : ℕ) : ℝ := ∑ j ∈ s, w j * (t j - t₀) ^ m

/-- The weighted sum of the values. -/
def sumZ : ℝ := ∑ j ∈ s, w j * z j

/-- The weighted sum of the values, each times its distance in time from `t₀`. -/
def sumTZ : ℝ := ∑ j ∈ s, w j * ((t j - t₀) * z j)

/-- The determinant of the two equations that the fitted line solves. It is
positive when samples of positive weight lie at two or more distinct times. -/
def det : ℝ := moment s w t t₀ 0 * moment s w t t₀ 2 - moment s w t t₀ 1 ^ 2

/-- The value of the fitted line at `t₀`. -/
def value : ℝ :=
  (moment s w t t₀ 2 * sumZ s w z - moment s w t t₀ 1 * sumTZ s w t z t₀) / det s w t t₀

/-- The slope of the fitted line. -/
def slope : ℝ :=
  (moment s w t t₀ 0 * sumTZ s w t z t₀ - moment s w t t₀ 1 * sumZ s w z) / det s w t t₀

/-- The weighted sum of squared residuals of the line through `(t₀, θ)` with slope `ρ`. -/
def cost (θ ρ : ℝ) : ℝ := ∑ j ∈ s, w j * (z j - θ - ρ * (t j - t₀)) ^ 2

/-! ## The fitted line has the smallest cost -/

theorem normal_value (h : det s w t t₀ ≠ 0) :
    moment s w t t₀ 0 * value s w t z t₀ + moment s w t t₀ 1 * slope s w t z t₀
      = sumZ s w z := by
  unfold value slope
  field_simp
  unfold det
  ring

theorem normal_slope (h : det s w t t₀ ≠ 0) :
    moment s w t t₀ 1 * value s w t z t₀ + moment s w t t₀ 2 * slope s w t z t₀
      = sumTZ s w t z t₀ := by
  unfold value slope
  field_simp
  unfold det
  ring

theorem cost_expand (θ ρ : ℝ) :
    cost s w t z t₀ θ ρ
      = (∑ j ∈ s, w j * z j ^ 2) - 2 * θ * sumZ s w z - 2 * ρ * sumTZ s w t z t₀
        + θ ^ 2 * moment s w t t₀ 0 + 2 * θ * ρ * moment s w t t₀ 1
        + ρ ^ 2 * moment s w t t₀ 2 := by
  simp only [cost, sumZ, sumTZ, moment, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quadratic_expand (x y : ℝ) :
    (∑ j ∈ s, w j * (x + y * (t j - t₀)) ^ 2)
      = x ^ 2 * moment s w t t₀ 0 + 2 * x * y * moment s w t t₀ 1
        + y ^ 2 * moment s w t t₀ 2 := by
  simp only [moment, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The cost of any line is the cost of the fitted line plus a sum of squares. -/
theorem cost_eq (h : det s w t t₀ ≠ 0) (θ ρ : ℝ) :
    cost s w t z t₀ θ ρ
      = cost s w t z t₀ (value s w t z t₀) (slope s w t z t₀)
        + ∑ j ∈ s, w j * ((θ - value s w t z t₀)
            + (ρ - slope s w t z t₀) * (t j - t₀)) ^ 2 := by
  have h1 := normal_value s w t z t₀ h
  have h2 := normal_slope s w t z t₀ h
  rw [cost_expand, cost_expand, quadratic_expand]
  linear_combination (2 * (θ - value s w t z t₀)) * h1 + (2 * (ρ - slope s w t z t₀)) * h2

/-- The fitted line has the smallest weighted sum of squared residuals. -/
theorem cost_le (hw : ∀ j ∈ s, 0 ≤ w j) (h : det s w t t₀ ≠ 0) (θ ρ : ℝ) :
    cost s w t z t₀ (value s w t z t₀) (slope s w t z t₀) ≤ cost s w t z t₀ θ ρ := by
  rw [cost_eq s w t z t₀ h θ ρ]
  have : 0 ≤ ∑ j ∈ s, w j * ((θ - value s w t z t₀)
      + (ρ - slope s w t z t₀) * (t j - t₀)) ^ 2 :=
    Finset.sum_nonneg fun j hj => mul_nonneg (hw j hj) (sq_nonneg _)
  linarith

/-! ## The sums can be kept as samples come and go -/

/-- Moving the reference time from `t₀` to `t₁`. -/
theorem moment_shift (t₁ : ℝ) :
    moment s w t t₁ 0 = moment s w t t₀ 0
    ∧ moment s w t t₁ 1 = moment s w t t₀ 1 - (t₁ - t₀) * moment s w t t₀ 0
    ∧ moment s w t t₁ 2
        = moment s w t t₀ 2 - 2 * (t₁ - t₀) * moment s w t t₀ 1
          + (t₁ - t₀) ^ 2 * moment s w t t₀ 0
    ∧ sumTZ s w t z t₁ = sumTZ s w t z t₀ - (t₁ - t₀) * sumZ s w z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [moment, sumTZ, sumZ, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Scaling every weight by `c` scales every sum by `c`. -/
theorem moment_scale (c : ℝ) (m : ℕ) :
    moment s (fun j => c * w j) t t₀ m = c * moment s w t t₀ m
    ∧ sumZ s (fun j => c * w j) z = c * sumZ s w z
    ∧ sumTZ s (fun j => c * w j) t z t₀ = c * sumTZ s w t z t₀ := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [moment, sumTZ, sumZ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Adding a sample adds its term to every sum. -/
theorem moment_insert [DecidableEq ι] (i : ι) (hi : i ∉ s) (m : ℕ) :
    moment (insert i s) w t t₀ m = w i * (t i - t₀) ^ m + moment s w t t₀ m
    ∧ sumZ (insert i s) w z = w i * z i + sumZ s w z
    ∧ sumTZ (insert i s) w t z t₀ = w i * ((t i - t₀) * z i) + sumTZ s w t z t₀ := by
  simp only [moment, sumZ, sumTZ, Finset.sum_insert hi, and_self]

/-- Scaling every weight by a nonzero factor does not change the fitted line. -/
theorem value_slope_scale (c : ℝ) (hc : c ≠ 0) (h : det s w t t₀ ≠ 0) :
    value s (fun j => c * w j) t z t₀ = value s w t z t₀
    ∧ slope s (fun j => c * w j) t z t₀ = slope s w t z t₀ := by
  have hm := fun m => (moment_scale s w t z t₀ c m).1
  have hz := (moment_scale s w t z t₀ c 0).2.1
  have htz := (moment_scale s w t z t₀ c 0).2.2
  constructor
  · unfold value det
    rw [hm 0, hm 1, hm 2, hz, htz]
    unfold det at h
    field_simp
  · unfold slope det
    rw [hm 0, hm 1, hm 2, hz, htz]
    unfold det at h
    field_simp

/-! ## Symmetries -/

theorem sumZ_add_affine (α β : ℝ) :
    sumZ s w (fun j => z j + α + β * t j)
      = sumZ s w z + (α + β * t₀) * moment s w t t₀ 0 + β * moment s w t t₀ 1 := by
  simp only [sumZ, moment, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sumTZ_add_affine (α β : ℝ) :
    sumTZ s w t (fun j => z j + α + β * t j) t₀
      = sumTZ s w t z t₀ + (α + β * t₀) * moment s w t t₀ 1 + β * moment s w t t₀ 2 := by
  simp only [sumTZ, moment, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Adding an affine function of the times to the values adds it to the fitted line. -/
theorem add_affine (h : det s w t t₀ ≠ 0) (α β : ℝ) :
    value s w t (fun j => z j + α + β * t j) t₀ = value s w t z t₀ + (α + β * t₀)
    ∧ slope s w t (fun j => z j + α + β * t j) t₀ = slope s w t z t₀ + β := by
  constructor
  · unfold value
    rw [sumZ_add_affine s w t z t₀, sumTZ_add_affine s w t z t₀]
    field_simp
    unfold det
    ring
  · unfold slope
    rw [sumZ_add_affine s w t z t₀, sumTZ_add_affine s w t z t₀]
    field_simp
    unfold det
    ring

theorem moment_reparam (c k : ℝ) (m : ℕ) :
    moment s w (fun j => c + k * t j) (c + k * t₀) m = k ^ m * moment s w t t₀ m := by
  simp only [moment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : c + k * t j - (c + k * t₀) = k * (t j - t₀) := by ring
  rw [this, mul_pow]
  ring

theorem sumTZ_reparam (c k : ℝ) :
    sumTZ s w (fun j => c + k * t j) z (c + k * t₀) = k * sumTZ s w t z t₀ := by
  simp only [sumTZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_reparam (c k : ℝ) :
    det s w (fun j => c + k * t j) (c + k * t₀) = k ^ 2 * det s w t t₀ := by
  unfold det
  rw [moment_reparam, moment_reparam, moment_reparam]
  ring

/-- Replacing every time `x` by `c + k * x` keeps the value of the fitted line
and divides its slope by `k`. -/
theorem reparametrize (h : det s w t t₀ ≠ 0) (c k : ℝ) (hk : k ≠ 0) :
    value s w (fun j => c + k * t j) z (c + k * t₀) = value s w t z t₀
    ∧ slope s w (fun j => c + k * t j) z (c + k * t₀) = slope s w t z t₀ / k := by
  constructor
  · unfold value
    rw [det_reparam, moment_reparam, moment_reparam, sumTZ_reparam]
    field_simp
  · unfold slope
    rw [det_reparam, moment_reparam, moment_reparam, sumTZ_reparam]
    field_simp

/-- The reading that the fitted line predicts for an event with stamp `x`. -/
def predict (x : ℝ) : ℝ := x + (value s w t z t₀ + slope s w t z t₀ * (x - t₀))

/-- Synchronization does not depend on the offset or the rate of the sender's
clock. Suppose the sender's clock read `c + k * x` wherever it reads `x`.
Each stamp of departure `t j` becomes `c + k * t j`, and each value, which is
a stamp of arrival minus a stamp of departure, becomes `z j + t j - (c + k * t j)`.
The reading of the receiver's clock that the fitted line predicts for an
event is the same as before. -/
theorem schedule_invariant (h : det s w t t₀ ≠ 0) (c k : ℝ) (hk : k ≠ 0) (x : ℝ) :
    predict s (w := w) (fun j => c + k * t j) (fun j => z j + (-c) + (1 - k) * t j)
        (c + k * t₀) (c + k * x)
      = predict s w t z t₀ x := by
  obtain ⟨hv1, hs1⟩ := add_affine s w t z t₀ h (-c) (1 - k)
  obtain ⟨hv2, hs2⟩ :=
    reparametrize s w t (fun j => z j + (-c) + (1 - k) * t j) t₀ h c k hk
  unfold predict
  rw [hv2, hs2, hv1, hs1]
  field_simp
  ring

/-! ## The error of the fitted value -/

/-- The weight with which the value of sample `j` enters the fitted value,
before division by the determinant. -/
def kernel (j : ι) : ℝ := w j * (moment s w t t₀ 2 - moment s w t t₀ 1 * (t j - t₀))

theorem value_eq_sum :
    value s w t z t₀ = (∑ j ∈ s, kernel s w t t₀ j * z j) / det s w t t₀ := by
  unfold value sumZ sumTZ kernel
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_weight : ∑ j ∈ s, w j = moment s w t t₀ 0 := by simp [moment]

theorem sum_weight_time : ∑ j ∈ s, w j * (t j - t₀) = moment s w t t₀ 1 := by simp [moment]

theorem kernel_sum : ∑ j ∈ s, kernel s w t t₀ j = det s w t t₀ := by
  have : ∑ j ∈ s, kernel s w t t₀ j
      = moment s w t t₀ 2 * ∑ j ∈ s, w j
        - moment s w t t₀ 1 * ∑ j ∈ s, w j * (t j - t₀) := by
    unfold kernel
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, sum_weight s w t t₀, sum_weight_time s w t t₀]
  unfold det
  ring

theorem kernel_time_sum : ∑ j ∈ s, kernel s w t t₀ j * (t j - t₀) = 0 := by
  have : ∑ j ∈ s, kernel s w t t₀ j * (t j - t₀)
      = moment s w t t₀ 2 * ∑ j ∈ s, w j * (t j - t₀)
        - moment s w t t₀ 1 * ∑ j ∈ s, w j * (t j - t₀) ^ 2 := by
    unfold kernel
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, sum_weight_time s w t t₀]
  have h2 : ∑ j ∈ s, w j * (t j - t₀) ^ 2 = moment s w t t₀ 2 := rfl
  rw [h2]
  ring

/-- The sum that the Cauchy-Schwarz inequality needs: the squared kernels,
each divided by its weight, add up to the second moment times the determinant. -/
theorem kernel_sq_sum :
    ∑ j ∈ s, w j * (moment s w t t₀ 2 - moment s w t t₀ 1 * (t j - t₀)) ^ 2
      = moment s w t t₀ 2 * det s w t t₀ := by
  have e : ∀ j, moment s w t t₀ 2 - moment s w t t₀ 1 * (t j - t₀)
      = moment s w t t₀ 2 + -(moment s w t t₀ 1) * (t j - t₀) := fun j => by ring
  simp only [e]
  rw [quadratic_expand]
  unfold det
  ring

/-- The fitted value of samples that lie on a line, up to the errors `u j`,
differs from the line by the weighted sum of the errors. -/
theorem value_sub (h : det s w t t₀ ≠ 0) (θ₀ ρ₀ : ℝ) (u : ι → ℝ)
    (hz : ∀ j ∈ s, z j = θ₀ + ρ₀ * (t j - t₀) + u j) :
    value s w t z t₀ - θ₀ = (∑ j ∈ s, kernel s w t t₀ j * u j) / det s w t t₀ := by
  rw [value_eq_sum]
  have : ∑ j ∈ s, kernel s w t t₀ j * z j
      = θ₀ * ∑ j ∈ s, kernel s w t t₀ j
        + ρ₀ * ∑ j ∈ s, kernel s w t t₀ j * (t j - t₀)
        + ∑ j ∈ s, kernel s w t t₀ j * u j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hz j hj]
    ring
  rw [this, kernel_sum, kernel_time_sum]
  field_simp
  ring

/-- The error of the fitted value, from quantities the fit itself holds.

Let the values lie on a line through `(t₀, θ₀)` up to two errors: a noise
`n j` of magnitude at most `ε`, and a departure `c j` of the true relation
from the line of at most `a / 2 * (t j - t₀) ^ 2`, which is what a rate that
changes by at most `a` per unit of time gives. Then the fitted value at `t₀`
is within the stated distance of `θ₀`.

The bound is for errors that may all have one sign, so averaging does not
shrink its first term: that term is at least `ε` whatever the weights. The
second term grows as older samples keep more weight. -/
theorem error_bound (hw : ∀ j ∈ s, 0 ≤ w j) (hdet : 0 < det s w t t₀)
    (θ₀ ρ₀ ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 ≤ a) (n c : ι → ℝ)
    (hz : ∀ j ∈ s, z j = θ₀ + ρ₀ * (t j - t₀) + (n j + c j))
    (hn : ∀ j ∈ s, |n j| ≤ ε) (hc : ∀ j ∈ s, |c j| ≤ a / 2 * (t j - t₀) ^ 2) :
    |value s w t z t₀ - θ₀|
      ≤ ε * √(moment s w t t₀ 0 * moment s w t t₀ 2 / det s w t t₀)
        + a / 2 * √(moment s w t t₀ 2 * moment s w t t₀ 4 / det s w t t₀) := by
  set g : ι → ℝ := fun j => moment s w t t₀ 2 - moment s w t t₀ 1 * (t j - t₀) with hg
  set D := det s w t t₀ with hD
  -- the two sums of absolute kernels
  set A := ∑ j ∈ s, w j * |g j| with hA
  set B := ∑ j ∈ s, w j * |g j| * (t j - t₀) ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j hj => mul_nonneg (hw j hj) (abs_nonneg _)
  have hB0 : 0 ≤ B :=
    Finset.sum_nonneg fun j hj => mul_nonneg (mul_nonneg (hw j hj) (abs_nonneg _)) (sq_nonneg _)
  -- Cauchy-Schwarz, twice
  have hA2 : A ^ 2 ≤ moment s w t t₀ 0 * (moment s w t t₀ 2 * D) := by
    rw [← sum_weight s w t t₀, ← kernel_sq_sum s w t t₀]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun j hj => hw j hj)
      (fun j hj => mul_nonneg (hw j hj) (sq_nonneg _)) (fun j _ => le_of_eq ?_)
    rw [mul_pow, sq_abs]
    ring
  have hB2 : B ^ 2 ≤ (moment s w t t₀ 2 * D) * moment s w t t₀ 4 := by
    rw [← kernel_sq_sum s w t t₀]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun j hj => mul_nonneg (hw j hj) (sq_nonneg _))
      (fun j hj => mul_nonneg (hw j hj) (by positivity)) (fun j _ => le_of_eq ?_)
    rw [mul_pow, mul_pow, sq_abs]
    ring
  -- the error as a weighted sum
  have hval := value_sub s w t z t₀ hdet.ne' θ₀ ρ₀ (fun j => n j + c j) hz
  have hnum : |∑ j ∈ s, kernel s w t t₀ j * (n j + c j)| ≤ ε * A + a / 2 * B := by
    calc |∑ j ∈ s, kernel s w t t₀ j * (n j + c j)|
        ≤ ∑ j ∈ s, |kernel s w t t₀ j * (n j + c j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, (ε * (w j * |g j|) + a / 2 * (w j * |g j| * (t j - t₀) ^ 2)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hk : |kernel s w t t₀ j| = w j * |g j| := by
            unfold kernel
            rw [abs_mul, abs_of_nonneg (hw j hj)]
          rw [abs_mul, hk]
          have hu : |n j + c j| ≤ ε + a / 2 * (t j - t₀) ^ 2 :=
            (abs_add_le _ _).trans (add_le_add (hn j hj) (hc j hj))
          have hk0 : 0 ≤ w j * |g j| := mul_nonneg (hw j hj) (abs_nonneg _)
          calc w j * |g j| * |n j + c j|
              ≤ w j * |g j| * (ε + a / 2 * (t j - t₀) ^ 2) :=
                mul_le_mul_of_nonneg_left hu hk0
            _ = ε * (w j * |g j|) + a / 2 * (w j * |g j| * (t j - t₀) ^ 2) := by ring
      _ = ε * A + a / 2 * B := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- from the squares to the square roots
  have hAD : A / D ≤ √(moment s w t t₀ 0 * moment s w t t₀ 2 / D) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [div_pow, div_le_div_iff₀ (by positivity) hdet]
    nlinarith [hA2, hdet]
  have hBD : B / D ≤ √(moment s w t t₀ 2 * moment s w t t₀ 4 / D) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [div_pow, div_le_div_iff₀ (by positivity) hdet]
    nlinarith [hB2, hdet]
  rw [hval, abs_div, abs_of_pos hdet]
  calc |∑ j ∈ s, kernel s w t t₀ j * (n j + c j)| / D
      ≤ (ε * A + a / 2 * B) / D := div_le_div_of_nonneg_right hnum hdet.le
    _ = ε * (A / D) + a / 2 * (B / D) := by ring
    _ ≤ ε * √(moment s w t t₀ 0 * moment s w t t₀ 2 / D)
        + a / 2 * √(moment s w t t₀ 2 * moment s w t t₀ 4 / D) :=
        add_le_add (mul_le_mul_of_nonneg_left hAD hε)
          (mul_le_mul_of_nonneg_left hBD (by positivity))

end Unisono.Model.LineFit
