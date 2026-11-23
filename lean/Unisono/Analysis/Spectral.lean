/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Unisono.Model.Regulation
public import Unisono.Spec.Models.SecondOrder

/-!
# Spectral factorization and steady-state filter identities

> **Status (supplementary component / oracle analysis):** This module proves
> algebraic and stochastic properties in a simplified component or oracle
> setting as a supplement to `Unisono.Spec`. Per `PRINCIPLES.md`, results
> here do **not** replace end-to-end proofs on `Unisono.Spec.Solution` and
> `Unisono.Spec.Objectives` under a named model class in `Unisono.Spec.Models`.


In the time domain, `Unisono.Analysis.ModalControl` analyzes applying
`Unisono.Model.Regulation.law` to the conditional-mean state in each decoupled
mode (common and differential). This module records the companion
frequency-domain and steady-state algebraic identities:

* **Controller spectral factorization (`weight_factor`, `step_step`).** On the
  unit circle `z = e^{iω}`, the per-cycle control weight `weight g + |1 - z|⁴`
  factors as `|P(z)|² / (1 - g)` with `P(z) = z² - lawTrace g · z + (1 - g)`,
  matching the closed-loop characteristic polynomial of `Regulation.step g`.
* **Continuous-time Butterworth prototype (`butterworth`).** The continuous-time
  quadratic cost `c₀² + c₂² ω⁴` (squared position error plus squared rate of
  change of playback pace) factors as `|c₂ (iω)² + c₁ (iω) + c₀|²` with
  `c₁² = 2 c₀ c₂`, a second-order Butterworth filter with damping ratio
  `ζ = 1 / √2` (distinct from critical damping `ζ = 1`) and natural frequency
  `(c₀ / c₂)^{1/2}`.
* **Scalar random-walk Riccati/spectral algebra (`filterRoot_*`,
  `filterRoot_unique`, `estimate_factor`, `riccati_fixed`,
  `posterior_variance`, `revision_variance`).** For `s = q / r > 0`,
  `filterRoot s` is the unique root `a ∈ (0, 1)` of `a² - (2 + s) a + 1 = 0`,
  yielding the algebraic Riccati fixed point `p = r (1 - a) / a`, gain
  `K = 1 - a`, simplified posterior variance `(1 - K) p = r (1 - a)`, and
  squared innovation-revision variance `K² (p + r) = q`.
* **Positive semidefiniteness of the two-state oscillator covariance matrix
  formula (`clockProcessCov_nonneg`).** For `ClockNoise` parameters `c` with
  `q₀ = c.whiteVarianceRate` and `q₂ = c.walkVarianceRate`, the 2×2 matrix
  formula `Q(dt)` for `dt ≥ 0` is positive semidefinite. (This proves matrix
  semidefiniteness rather than constructing a stochastic process or proving
  `Q(dt)` is the increment covariance of a `SecondOrderMoments`.)
-/

@[expose] public noncomputable section

namespace Unisono.Analysis

open Unisono.Model.Regulation
open Unisono.Spec

/-- Trace coefficient `β = 4 (1 - g) / (2 - g)` of the closed-loop
characteristic polynomial of `Regulation.step g`. -/
def lawTrace (g : ℝ) : ℝ := 4 * (1 - g) / (2 - g)

/-- **Spectral factorization of the discrete control cost.** For every nonzero
`z : ℂ` and `g ∈ (0, 1)`,
`weight g + (2 - z - z⁻¹)² = P(z) P(z⁻¹) / (1 - g)` where
`P(z) = z² - lawTrace g · z + (1 - g)`. On the unit circle,
`2 - z - z⁻¹ = |1 - z|²` and `P(z⁻¹) = conj (P z)`. -/
theorem weight_factor {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) {z : ℂ} (hz : z ≠ 0) :
    (weight g : ℂ) + (2 - z - z⁻¹) ^ 2
      = (z ^ 2 - (lawTrace g : ℂ) * z + ((1 - g : ℝ) : ℂ))
        * (z⁻¹ ^ 2 - (lawTrace g : ℂ) * z⁻¹ + ((1 - g : ℝ) : ℂ)) / ((1 - g : ℝ) : ℂ) := by
  have h1 : ((1 - g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h2 : ((2 - g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  push_cast at h1 h2 ⊢
  simp only [weight, lawTrace]
  push_cast
  field_simp
  ring

/-- **Closed-loop recurrence of `Regulation.step g`.** In the absence of new
disturbances, two consecutive cycles satisfy
`step g (step g x) = lawTrace g • step g x - (1 - g) • x`, so its
characteristic polynomial is `P(z) = z² - lawTrace g · z + (1 - g)`. -/
theorem step_step {g : ℝ} (hg1 : g < 1) (x : ℝ × ℝ) :
    step g (step g x) = lawTrace g • step g x - (1 - g) • x := by
  have h2 : (2 - g) ≠ 0 := by linarith
  obtain ⟨E, v⟩ := x
  simp only [step, next, law, gainE, lawTrace, Prod.smul_mk, smul_eq_mul, Prod.mk_sub_mk,
    Prod.fst_zero, Prod.snd_zero, add_zero, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- **Continuous-time Butterworth spectral factorization.** When
`c₁² = 2 c₀ c₂`, the second-order Butterworth polynomial
`W(s) = c₂ s² + c₁ s + c₀` (damping ratio `ζ = 1 / √2`) satisfies
`|W(iω)|² = c₀² + c₂² ω⁴` for every real angular frequency `ω`. -/
theorem butterworth {c₀ c₁ c₂ : ℝ} (hc : c₁ ^ 2 = 2 * c₀ * c₂) (ω : ℝ) :
    Complex.normSq (c₂ * (Complex.I * ω) ^ 2 + c₁ * (Complex.I * ω) + c₀)
      = c₀ ^ 2 + c₂ ^ 2 * ω ^ 4 := by
  have hre : ((c₂ : ℂ) * (Complex.I * ω) ^ 2 + c₁ * (Complex.I * ω) + c₀).re
      = c₀ - c₂ * ω ^ 2 := by
    simp [pow_two]
    ring
  have him : ((c₂ : ℂ) * (Complex.I * ω) ^ 2 + c₁ * (Complex.I * ω) + c₀).im = c₁ * ω := by
    simp [pow_two]
  rw [Complex.normSq_apply, hre, him]
  nlinarith [hc]

/-- Unique root in `(0, 1)` of `a² - (2 + s) a + 1 = 0`, where `s = q / r > 0`
is the process-to-measurement variance ratio of a scalar random walk. -/
def filterRoot (s : ℝ) : ℝ := 1 + s / 2 - Real.sqrt (s + (s / 2) ^ 2)

theorem filterRoot_eq {s : ℝ} (hs : 0 ≤ s) :
    filterRoot s ^ 2 - (2 + s) * filterRoot s + 1 = 0 := by
  have hq : 0 ≤ s + (s / 2) ^ 2 := by positivity
  have hsq := Real.sq_sqrt hq
  simp only [filterRoot]
  nlinarith [hsq]

theorem filterRoot_pos {s : ℝ} (hs : 0 ≤ s) : 0 < filterRoot s := by
  have hq : 0 ≤ s + (s / 2) ^ 2 := by positivity
  have hsq := Real.sq_sqrt hq
  have hlt : Real.sqrt (s + (s / 2) ^ 2) < 1 + s / 2 := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  simp only [filterRoot]
  linarith

theorem filterRoot_lt_one {s : ℝ} (hs : 0 < s) : filterRoot s < 1 := by
  have hgt : s / 2 < Real.sqrt (s + (s / 2) ^ 2) := by
    rw [Real.lt_sqrt (by positivity)]
    nlinarith
  simp only [filterRoot]
  linarith

/-- **Uniqueness of `filterRoot s` in `(0, 1)`.** For any `s > 0`, `filterRoot s`
is the unique root of `a² - (2 + s) a + 1 = 0` strictly inside `(0, 1)`. -/
theorem filterRoot_unique {s a : ℝ} (hs : 0 < s) (ha1 : a < 1)
    (hroot : a ^ 2 - (2 + s) * a + 1 = 0) : a = filterRoot s := by
  have hb := filterRoot_eq hs.le
  have hb1 : filterRoot s < 1 := filterRoot_lt_one hs
  have hdiff : (a - filterRoot s) * (a + filterRoot s - (2 + s)) = 0 := by nlinarith
  have hneg : a + filterRoot s - (2 + s) < 0 := by linarith
  rcases mul_eq_zero.mp hdiff with h | h
  · linarith
  · linarith

/-- **Spectral factorization of noisy random-walk observations.** When
`a² - (2 + q / r) a + 1 = 0`, every nonzero `z : ℂ` satisfies
`q + r (2 - z - z⁻¹) = (r / a) (1 - a z) (1 - a z⁻¹)`. Dividing by
`(1 - z)(1 - z⁻¹)` exhibits the causal innovations factor
`(1 - a z⁻¹) / (1 - z⁻¹)`. -/
theorem estimate_factor {q r a : ℝ} (hr : r ≠ 0) (ha : a ≠ 0)
    (hroot : a ^ 2 - (2 + q / r) * a + 1 = 0) {z : ℂ} (hz : z ≠ 0) :
    (q : ℂ) + r * (2 - z - z⁻¹) = (r / a : ℝ) * (1 - a * z) * (1 - a * z⁻¹) := by
  have hq : q = r * (a ^ 2 - 2 * a + 1) / a := by
    field_simp
    have : a ^ 2 - (2 + q / r) * a + 1 = 0 := hroot
    field_simp at this
    linarith
  rw [hq]
  push_cast
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  field_simp
  ring

/-- **Steady-state scalar Riccati fixed point.** For `r > 0`, `a ∈ (0, 1)`, and
`a² - (2 + q / r) a + 1 = 0`, the prior variance `p = r (1 - a) / a` satisfies
the algebraic Riccati equation `p r / (p + r) + q = p` and produces steady-state
Kalman gain `K = p / (p + r) = 1 - a`. -/
theorem riccati_fixed {q r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha1 : a < 1)
    (hroot : a ^ 2 - (2 + q / r) * a + 1 = 0) :
    r * (1 - a) / a * r / (r * (1 - a) / a + r) + q = r * (1 - a) / a
      ∧ (r * (1 - a) / a) / (r * (1 - a) / a + r) = 1 - a := by
  have hr' : r ≠ 0 := hr.ne'
  have ha' : a ≠ 0 := ha0.ne'
  have hq : q = r * (a ^ 2 - 2 * a + 1) / a := by
    field_simp
    have : a ^ 2 - (2 + q / r) * a + 1 = 0 := hroot
    field_simp at this
    linarith
  have hsum : r * (1 - a) / a + r = r / a := by
    field_simp
    ring
  constructor
  · rw [hsum, hq]
    field_simp
    ring
  · rw [hsum]
    field_simp

/-- **Algebraic simplification of the Riccati posterior variance.** Substituting
the steady-state gain `K = 1 - a` and prior variance `p = r (1 - a) / a` from
`riccati_fixed` into `(1 - K) p` yields `r (1 - a)`. -/
theorem posterior_variance {r a : ℝ} (ha0 : 0 < a) :
    (1 - (1 - a)) * (r * (1 - a) / a) = r * (1 - a) := by
  field_simp
  ring

/-- **Steady-state estimate-revision variance.** At the Riccati fixed point,
`K² (p + r) = (1 - a)² (r (1 - a) / a + r)` simplifies to the process step
variance `q`. -/
theorem revision_variance {q r a : ℝ} (hr : 0 < r) (ha0 : 0 < a)
    (hroot : a ^ 2 - (2 + q / r) * a + 1 = 0) :
    (1 - a) ^ 2 * (r * (1 - a) / a + r) = q := by
  have hr' : r ≠ 0 := hr.ne'
  have ha' : a ≠ 0 := ha0.ne'
  have hq : q = r * (a ^ 2 - 2 * a + 1) / a := by
    field_simp
    have : a ^ 2 - (2 + q / r) * a + 1 = 0 := hroot
    field_simp at this
    linarith
  rw [hq]
  field_simp
  ring

/-- **Positive semidefiniteness of the two-state oscillator covariance matrix
formula.** Given `ClockNoise` parameters `c` and `dt ≥ 0`, the symmetric 2×2
matrix with entries `Q₀₀ = q₀ dt + q₂ dt³ / 3`, `Q₀₁ = Q₁₀ = q₂ dt² / 2`,
`Q₁₁ = q₂ dt` (where `q₀ = c.whiteVarianceRate` and `q₂ = c.walkVarianceRate`)
has nonnegative quadratic form for every `(u, v) : ℝ × ℝ`. -/
theorem clockProcessCov_nonneg (c : ClockNoise) (dt : ℝ) (hdt : 0 ≤ dt) (u v : ℝ) :
    0 ≤ (c.whiteVarianceRate * dt + c.walkVarianceRate * dt ^ 3 / 3) * u ^ 2
        + 2 * (c.walkVarianceRate * dt ^ 2 / 2) * u * v
        + (c.walkVarianceRate * dt) * v ^ 2 := by
  have hq0 : 0 ≤ c.whiteVarianceRate := by
    unfold ClockNoise.whiteVarianceRate
    linarith [c.white_nonneg]
  have hq2 : 0 ≤ c.walkVarianceRate := by
    unfold ClockNoise.walkVarianceRate
    have hpi : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    have hw : 0 ≤ c.walk := c.walk_nonneg
    positivity
  have hdecomp :
      (c.whiteVarianceRate * dt + c.walkVarianceRate * dt ^ 3 / 3) * u ^ 2
        + 2 * (c.walkVarianceRate * dt ^ 2 / 2) * u * v
        + (c.walkVarianceRate * dt) * v ^ 2
      = c.whiteVarianceRate * dt * u ^ 2
        + c.walkVarianceRate * dt * (v + dt * u / 2) ^ 2
        + c.walkVarianceRate * dt ^ 3 * u ^ 2 / 12 := by ring
  rw [hdecomp]
  positivity

end Unisono.Analysis
