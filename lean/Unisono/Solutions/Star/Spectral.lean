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

/-!
# The spectral factors of the controller

The best way of playing applies the law of `Unisono.Model.Regulation` to the
best estimates (`Unisono.Solutions.Star.Separation`). In the frequency
domain both parts come from a spectral factorization: the law from the
factorization of the cost's weight, and the estimate, in the stationary
Gaussian case, from the factorization of the measurements' spectrum (the
Wiener filter). This file checks the identities that connect the two views.
They are algebraic identities; the optimality itself is proved in the time
domain.

* **The law.** On the unit circle `z = e^{iω}`, the weight of a cycle's cost
  in the frequency domain is `weight g + |1 - z|⁴`, because the change of the
  pace is the second difference of the position. It factors as
  `|P(z)|² / (1 - g)` with `P(z) = z² - β z + (1 - g)` and
  `β = 4 (1 - g) / (2 - g)` (`weight_factor`), and the law's closed loop
  satisfies the recursion whose characteristic polynomial is `P`
  (`step_step`). The law is therefore the causal factor of the weight, as
  the Wiener-Hopf solution prescribes.
* **The papers' law.** In continuous time the weight `q + r ω⁴` of the
  squared error and of the squared rate of change of the warp factors as
  `|W(iω)|²` with `W(s) = c₂ s² + c₁ s + c₀`, `c₀² = q`, `c₂² = r` and
  `c₁² = 2 c₀ c₂` (`butterworth`): the second-order Butterworth polynomial
  with natural frequency `(q / r)^{1/4}` and damping `1 / √2` that the
  earlier papers derived.
* **The estimate.** For a due position that follows a random walk whose
  steps have variance `q`, measured each cycle with white noise of variance
  `r`, let `a` be the root in `(0, 1)` of `a² - (2 + q / r) a + 1 = 0`
  (`filterRoot`). The measurements' spectrum factors with `a`
  (`estimate_factor`); the steady state of the Kalman filter has gain
  `1 - a` (`riccati_fixed`); the estimate errs with variance `r (1 - a)`
  (`posterior_variance`); and its revisions have variance `q`
  (`revision_variance`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Star

open Unisono.Model.Regulation

/-- The middle coefficient of the law's characteristic polynomial. -/
def lawTrace (g : ℝ) : ℝ := 4 * (1 - g) / (2 - g)

/-- **The weight of the law's cost factors.** For every nonzero complex `z`,
`weight g + (2 - z - z⁻¹)² = P(z) P(z⁻¹) / (1 - g)` with
`P(z) = z² - lawTrace g * z + (1 - g)`. On the unit circle
`2 - z - z⁻¹ = |1 - z|²` and `P(z⁻¹)` is the conjugate of `P(z)`. -/
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

/-- **The law's closed loop.** One cycle under the law, without revisions, is
the linear map with trace `lawTrace g` and determinant `1 - g`, so two cycles
satisfy `x₂ = lawTrace g * x₁ - (1 - g) * x₀`: the recursion with
characteristic polynomial `z² - lawTrace g * z + (1 - g)`. -/
theorem step_step {g : ℝ} (hg1 : g < 1) (x : ℝ × ℝ) :
    step g (step g x) = lawTrace g • step g x - (1 - g) • x := by
  have h2 : (2 - g) ≠ 0 := by linarith
  obtain ⟨E, v⟩ := x
  simp only [step, next, law, gainE, lawTrace, Prod.smul_mk, smul_eq_mul, Prod.mk_sub_mk,
    Prod.fst_zero, Prod.snd_zero, add_zero, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- **The papers' law is the causal factor of its weight.** With
`c₁² = 2 c₀ c₂`, the polynomial `W(s) = c₂ s² + c₁ s + c₀` satisfies
`|W(iω)|² = c₀² + c₂² ω⁴` for every real `ω`. -/
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

/-- The root in `(0, 1)` of `a² - (2 + s) a + 1 = 0`, for a ratio `s > 0` of
the variance of a step of the due position to the variance of the
measurement noise. -/
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
  have hq : 0 ≤ s + (s / 2) ^ 2 := by positivity
  have hgt : s / 2 < Real.sqrt (s + (s / 2) ^ 2) := by
    rw [Real.lt_sqrt (by positivity)]
    nlinarith
  simp only [filterRoot]
  linarith

/-- **The measurements' spectrum factors.** When `a² - (2 + q / r) a + 1 = 0`,
for every nonzero complex `z`,
`q + r (2 - z - z⁻¹) = (r / a) (1 - a z) (1 - a z⁻¹)`. Divided by
`(1 - z)(1 - z⁻¹)`, the left side is the spectrum of a random walk with steps
of variance `q`, measured with white noise of variance `r`, and the right side
puts its causal factor `(1 - a z⁻¹) / (1 - z⁻¹)` in evidence. -/
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

/-- **The steady state of the Kalman filter.** When
`a² - (2 + q / r) a + 1 = 0` with `0 < a < 1` and `r > 0`, the variance
`p = r (1 - a) / a` of the prediction is a fixed point of the Riccati
recursion: the variance after a measurement, `p r / (p + r)`, plus the
variance `q` of a step is `p`. The filter's gain `p / (p + r)` is `1 - a`. -/
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

/-- **The error of the estimate.** In the steady state the estimate after a
measurement errs with variance `(1 - K) p = r (1 - a)`, where `K = 1 - a` is
the gain and `p = r (1 - a) / a` the variance of the prediction. -/
theorem posterior_variance {r a : ℝ} (ha0 : 0 < a) :
    (1 - (1 - a)) * (r * (1 - a) / a) = r * (1 - a) := by
  field_simp
  ring

/-- **The revisions of the estimate.** The revision of the estimate at a
measurement is the gain times the innovation, whose variance is `p + r`. In
the steady state its variance `K² (p + r)` equals the variance `q` of a step
of the due position. -/
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

end Unisono.Solutions.Star
