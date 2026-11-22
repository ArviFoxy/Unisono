/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Playout latency margin under a continuous-time Campbell pause model

This module analyzes a standalone continuous-time approximation to the playout
buffer-level problem. It does not import `Unisono.Spec.Objectives`; its
objective `J(m)` is a continuous-time Campbell-formula model with the following
simplifications relative to the discrete specification:

* **Pauses versus outages.** A **pause** of duration `h` holds packets on a
  link for `h` seconds before delivering them, so a safety margin of `m`
  seconds above baseline path and processing delays absorbs up to `m` seconds
  and leaves `(h - m)⁺ = max (h - m) 0` seconds of missed audio and one
  discontinuity (click) whenever `h > m`. By contrast, during an **outage**
  where packets are dropped rather than delayed, the entire outage duration is
  missed regardless of `m`; the model here describes pauses only.
* **Unit conversion.** `J(m)` measures missed audio in **seconds per second**
  (`∫ (h - m)⁺ dν`), whereas `Unisono.Spec.Objectives.World.missed` counts
  missed **output samples per second**. Converting a specification missed-sample
  weight `c_M` to `wM` multiplies by the audio sample rate `ρ`: `wM = ρ * c_M`.
* **Discrete effects omitted.** This continuous-time model omits discrete
  device block-request boundaries, resampler lookahead, background jitter
  tails, and overlapping pauses.

Under Campbell's formula for a stationary marked point process with pause
intensity measure `ν = λ μ` (arrival rate `λ` per second times duration
distribution `μ`), a playout margin `m` incurs steady-state per-second cost:

    J(m) = wΛ · m + wΘ · (m - m₀)² + wM · ∫ (h - m)⁺ dν + wD · ν {h > m}

where `wΛ` prices mean latency, `wΘ` prices quadratic deviation from a target
lip-sync margin `m₀` (determined by the target latency minus baseline path and
processing delay), `wM` prices missed seconds per second, and `wD` prices
discontinuities per second.

## Main results

* **Missed-fraction quantile rule (`margin_best_missed`).** When `wΘ = 0` and
  `wD = 0`, any margin `m` satisfying `wM · ν {h > m} ≤ wΛ ≤ wM · ν {h ≥ m}`
  globally minimizes `wΛ · m + wM · ∫ (h - m)⁺ dν`.
* **Tracking + missed-fraction optimum (`margin_best_tracking`).** With
  quadratic tracking penalty `wΘ ≥ 0` around target margin `m₀` and `wD = 0`,
  any margin `m` satisfying
  `wM · ν {h > m} ≤ wΛ + 2 wΘ (m - m₀) ≤ wM · ν {h ≥ m}` globally minimizes
  `wΛ · m + wΘ · (m - m₀)² + wM · ∫ (h - m)⁺ dν`.
* **Linearity over fleet-averaged pause measures
  (`fleet_average_missed_cost`).** Averaging the Campbell missed-audio cost
  across `R` speakers with pause measures `ν r` at a shared margin `m` equals
  the single-measure cost under `ν̄ = (1 / R) ∑ r, ν r`. (This is an integral
  linearity identity for the Campbell model, not a theorem about
  `World.missed`.)
* **Closed-form exponential optimum with discontinuities in low-latency mode
  (`margin_best_exponential_with_clicks`).** When `wΘ = 0`, `wΛ > 0`, and
  pauses arrive at rate `λ > 0` with a single shared exponential duration
  distribution of mean `hBar > 0`, pricing discontinuities (`wD ≥ 0`) preserves
  convexity on `m ≥ 0` and yields the global minimizer
  `m* = max 0 (hBar * log (λ * (wM + wD / hBar) / wΛ))`. (Note: a mixture of
  exponential pause distributions with different means across speakers is not
  exponential.)
* **Non-convexity under atomic pauses with discontinuities
  (`discontinuity_nonconvex_example`).** For a fixed pause duration `h₀ > 0`,
  the step discontinuity of the indicator `1_{m < h₀}` breaks convexity when
  `wD * λ > wΛ * h₀`, showing why general pause distributions with click
  penalties require a 1D search rather than a local quantile rule.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Optimal

open MeasureTheory Finset

/-- **Missed-fraction quantile optimality.** For a finite pause measure `ν`
with finite first moment, `wM ≥ 0`, and any `m` satisfying the quantile bracket
`wM · ν {h > m} ≤ wΛ ≤ wM · ν {h ≥ m}`, `m` globally minimizes
`x ↦ wΛ · x + wM · ∫ max (h - x) 0 dν` over `x : ℝ`. -/
theorem margin_best_missed (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : Integrable (fun h => h) ν)
    {wΛ wM m : ℝ} (hwM : 0 ≤ wM)
    (hlow : wM * ν.real {h | m < h} ≤ wΛ)
    (hhigh : wΛ ≤ wM * ν.real {h | m ≤ h}) (x : ℝ) :
    wΛ * m + wM * ∫ h, max (h - m) 0 ∂ν ≤ wΛ * x + wM * ∫ h, max (h - x) 0 ∂ν := by
  have hpos : ∀ y : ℝ, Integrable (fun h => max (h - y) 0) ν :=
    fun y => (hint.sub (integrable_const y)).pos_part
  rcases le_total m x with hmx | hxm
  · have hs : MeasurableSet {h : ℝ | m < h} := measurableSet_Ioi
    have hind : Integrable ({h : ℝ | m < h}.indicator 1) ν :=
      (integrable_const (1 : ℝ)).indicator hs
    have hpt : ∀ h, max (h - m) 0 - (x - m) * {h : ℝ | m < h}.indicator 1 h
        ≤ max (h - x) 0 := by
      intro h
      by_cases hh : m < h
      · rw [Set.indicator_of_mem (show h ∈ {h : ℝ | m < h} from hh), Pi.one_apply,
          max_eq_left (by linarith)]
        linarith [le_max_left (h - x) 0]
      · rw [Set.indicator_of_notMem (show h ∉ {h : ℝ | m < h} from hh),
          max_eq_right (by linarith)]
        linarith [le_max_right (h - x) 0]
    have hmono : ∫ h, (max (h - m) 0 - (x - m) * {h : ℝ | m < h}.indicator 1 h) ∂ν
        ≤ ∫ h, max (h - x) 0 ∂ν :=
      integral_mono ((hpos m).sub (hind.const_mul (x - m))) (hpos x) hpt
    rw [integral_sub (hpos m) (hind.const_mul (x - m)), integral_const_mul,
      integral_indicator_one hs] at hmono
    nlinarith [mul_le_mul_of_nonneg_left hmono hwM,
      mul_nonneg (sub_nonneg.2 hmx) (sub_nonneg.2 hlow)]
  · have hs : MeasurableSet {h : ℝ | m ≤ h} := measurableSet_Ici
    have hind : Integrable ({h : ℝ | m ≤ h}.indicator 1) ν :=
      (integrable_const (1 : ℝ)).indicator hs
    have hpt : ∀ h, max (h - m) 0 + (m - x) * {h : ℝ | m ≤ h}.indicator 1 h
        ≤ max (h - x) 0 := by
      intro h
      by_cases hh : m ≤ h
      · rw [Set.indicator_of_mem (show h ∈ {h : ℝ | m ≤ h} from hh), Pi.one_apply,
          max_eq_left (by linarith)]
        linarith [le_max_left (h - x) 0]
      · rw [Set.indicator_of_notMem (show h ∉ {h : ℝ | m ≤ h} from hh),
          max_eq_right (by linarith)]
        linarith [le_max_right (h - x) 0]
    have hmono : ∫ h, (max (h - m) 0 + (m - x) * {h : ℝ | m ≤ h}.indicator 1 h) ∂ν
        ≤ ∫ h, max (h - x) 0 ∂ν :=
      integral_mono ((hpos m).add (hind.const_mul (m - x))) (hpos x) hpt
    rw [integral_add (hpos m) (hind.const_mul (m - x)), integral_const_mul,
      integral_indicator_one hs] at hmono
    nlinarith [mul_le_mul_of_nonneg_left hmono hwM,
      mul_nonneg (sub_nonneg.2 hxm) (sub_nonneg.2 hhigh)]

/-- **Tracking + missed-fraction optimality.** With latency weight `wΛ`,
quadratic tracking penalty `wΘ ≥ 0` around target margin `m₀`, missed-audio
weight `wM ≥ 0`, and `wD = 0`, any margin `m` satisfying the subgradient bracket
`wM · ν {h > m} ≤ wΛ + 2 wΘ (m - m₀) ≤ wM · ν {h ≥ m}` globally minimizes
`x ↦ wΛ · x + wΘ · (x - m₀)² + wM · ∫ max (h - x) 0 dν`. -/
theorem margin_best_tracking (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : Integrable (fun h => h) ν)
    {wΛ wΘ wM m₀ m : ℝ} (hwΘ : 0 ≤ wΘ) (hwM : 0 ≤ wM)
    (hlow : wM * ν.real {h | m < h} ≤ wΛ + 2 * wΘ * (m - m₀))
    (hhigh : wΛ + 2 * wΘ * (m - m₀) ≤ wM * ν.real {h | m ≤ h}) (x : ℝ) :
    wΛ * m + wΘ * (m - m₀) ^ 2 + wM * ∫ h, max (h - m) 0 ∂ν
      ≤ wΛ * x + wΘ * (x - m₀) ^ 2 + wM * ∫ h, max (h - x) 0 ∂ν := by
  have hlin := margin_best_missed ν hint hwM hlow hhigh x
  have hquad : wΘ * (x - m₀) ^ 2 - wΘ * (m - m₀) ^ 2
      = 2 * wΘ * (m - m₀) * (x - m) + wΘ * (x - m) ^ 2 := by ring
  have hsq : 0 ≤ wΘ * (x - m) ^ 2 := mul_nonneg hwΘ (sq_nonneg _)
  linarith

/-- **Linearity of the Campbell missed-audio cost over fleet-averaged pause
measures.** For `R > 0` speakers with finite pause measures `ν r`, averaging
the Campbell missed-audio cost across `r` at a shared margin `m` equals the
single-measure cost under `ν̄ = (R : ℝ≥0∞)⁻¹ • ∑ r, ν r`. -/
theorem fleet_average_missed_cost {R : ℕ} (hR : 0 < R) (ν : Fin R → Measure ℝ)
    [∀ r, IsFiniteMeasure (ν r)]
    (hint : ∀ r, Integrable (fun h => h) (ν r)) (wΛ wM m : ℝ) :
    let νBar : Measure ℝ := ((R : ENNReal)⁻¹) • ∑ r : Fin R, ν r
    (∑ r : Fin R, (wΛ * m + wM * ∫ h, max (h - m) 0 ∂(ν r))) / R
      = wΛ * m + wM * ∫ h, max (h - m) 0 ∂νBar := by
  intro νBar
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hpos : ∀ r : Fin R, Integrable (fun h => max (h - m) 0) (ν r) :=
    fun r => ((hint r).sub (integrable_const m)).pos_part
  have hsum_int : ∫ h, max (h - m) 0 ∂(∑ r : Fin R, ν r)
      = ∑ r : Fin R, ∫ h, max (h - m) 0 ∂(ν r) :=
    integral_finsetSum_measure fun r _ => hpos r
  have hbar_int : ∫ h, max (h - m) 0 ∂νBar
      = (∑ r : Fin R, ∫ h, max (h - m) 0 ∂(ν r)) / R := by
    simp only [νBar, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul, hsum_int, div_eq_inv_mul]
  rw [hbar_int, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  field_simp

/-- **Closed-form exponential pause optimum with discontinuities (low-latency
mode, `wΘ = 0`).** Suppose pauses arrive at rate `lam > 0` with a single shared
exponential duration distribution of mean `hBar > 0`, so at margin `x ≥ 0`:
* expected missed time per second is `lam * hBar * exp (-x / hBar)`,
* expected discontinuity (click) rate is `lam * exp (-x / hBar)`.

With latency weight `wΛ > 0`, missed-audio weight `wM`, discontinuity weight
`wD`, and `wM * hBar + wD > 0` (and `wΘ = 0`), the combined objective
`J(x) = wΛ * x + wM * (lam * hBar * exp (-x / hBar)) + wD * (lam * exp (-x / hBar))`
is globally minimized over all `x ≥ 0` by
`m* = max 0 (hBar * log (lam * (wM + wD / hBar) / wΛ))`. -/
theorem margin_best_exponential_with_clicks {wΛ wM wD lam hBar : ℝ}
    (hwΛ : 0 < wΛ) (hlam : 0 < lam) (hhBar : 0 < hBar) (hpos : 0 < wM * hBar + wD)
    {x : ℝ} (hx : 0 ≤ x) :
    let mStar : ℝ := max 0 (hBar * Real.log (lam * (wM + wD / hBar) / wΛ))
    wΛ * mStar + wM * (lam * hBar * Real.exp (-(mStar / hBar)))
        + wD * (lam * Real.exp (-(mStar / hBar)))
      ≤ wΛ * x + wM * (lam * hBar * Real.exp (-(x / hBar)))
        + wD * (lam * Real.exp (-(x / hBar))) := by
  intro mStar
  set C : ℝ := lam * (wM * hBar + wD)
  have hC : 0 < C := mul_pos hlam hpos
  have hC_ratio : lam * (wM + wD / hBar) / wΛ = C / (wΛ * hBar) := by
    have hh : hBar ≠ 0 := hhBar.ne'
    have hl : wΛ ≠ 0 := hwΛ.ne'
    simp only [C]
    field_simp
  have hrew : ∀ y : ℝ,
      wΛ * y + wM * (lam * hBar * Real.exp (-(y / hBar))) + wD * (lam * Real.exp (-(y / hBar)))
        = wΛ * y + C * Real.exp (-(y / hBar)) := fun y => by
    simp only [C]; ring
  rw [hrew mStar, hrew x]
  have hexp_bound : ∀ y : ℝ,
      Real.exp (-(mStar / hBar)) * (1 - (y - mStar) / hBar) ≤ Real.exp (-(y / hBar)) := by
    intro y
    have h1 := Real.add_one_le_exp (-((y - mStar) / hBar))
    have h2 : Real.exp (-(y / hBar))
        = Real.exp (-(mStar / hBar)) * Real.exp (-((y - mStar) / hBar)) := by
      rw [← Real.exp_add]
      congr 1
      have hh : hBar ≠ 0 := hhBar.ne'
      field_simp
      ring
    rw [h2]
    have hmul := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(mStar / hBar))).le
    linarith
  have hstep : C * Real.exp (-(mStar / hBar)) * (1 - (x - mStar) / hBar)
      ≤ C * Real.exp (-(x / hBar)) := by
    have := mul_le_mul_of_nonneg_left (hexp_bound x) hC.le
    linarith
  by_cases hge : wΛ * hBar ≤ C
  · have hlog_nonneg : 0 ≤ Real.log (C / (wΛ * hBar)) := by
      apply Real.log_nonneg
      rw [one_le_div (mul_pos hwΛ hhBar)]
      exact hge
    have hm_eq : mStar = hBar * Real.log (C / (wΛ * hBar)) := by
      simp only [mStar, hC_ratio]
      exact max_eq_right (mul_nonneg hhBar.le hlog_nonneg)
    have hCe : C * Real.exp (-(mStar / hBar)) = wΛ * hBar := by
      rw [hm_eq]
      have hh : hBar ≠ 0 := hhBar.ne'
      have hdiv : hBar * Real.log (C / (wΛ * hBar)) / hBar = Real.log (C / (wΛ * hBar)) := by
        field_simp
      rw [hdiv, Real.exp_neg, Real.exp_log (div_pos hC (mul_pos hwΛ hhBar))]
      have hCne : C ≠ 0 := hC.ne'
      field_simp
    have hcalc : C * Real.exp (-(mStar / hBar)) * (1 - (x - mStar) / hBar)
        = wΛ * hBar - wΛ * (x - mStar) := by
      rw [hCe]
      have hh : hBar ≠ 0 := hhBar.ne'
      field_simp
    linarith
  · push Not at hge
    have hlog_neg : Real.log (C / (wΛ * hBar)) < 0 := by
      apply Real.log_neg (div_pos hC (mul_pos hwΛ hhBar))
      rw [div_lt_one (mul_pos hwΛ hhBar)]
      exact hge
    have hm_eq : mStar = 0 := by
      simp only [mStar, hC_ratio]
      exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hhBar.le hlog_neg.le)
    rw [hm_eq] at hstep ⊢
    simp only [zero_div, neg_zero, Real.exp_zero, mul_one, mul_zero, zero_add, sub_zero] at hstep ⊢
    have hslope : 0 ≤ (wΛ - C / hBar) * x := by
      apply mul_nonneg _ hx
      rw [sub_nonneg, div_le_iff₀ hhBar]
      linarith
    have halg : C * (1 - x / hBar) = C - (C / hBar) * x := by ring
    linarith

/-- **Non-convexity under discontinuities for atomic pauses.** Consider
identical pauses of fixed duration `h₀ > 0` arriving at rate `lam > 0`, so at
margin `m` the combined cost is
`J(m) = wΛ * m + wM * lam * max (h₀ - m) 0 + wD * lam * (if m < h₀ then 1 else 0)`.
Whenever `wΛ ≥ 0` and `wD * lam > wΛ * h₀` (even with `wM = 0`), the
step discontinuity of the indicator at `m = h₀` breaks convexity
(`J(h₀ / 2) > (J(0) + J(h₀)) / 2`) and makes `m = h₀` beat `m = 0`
(`J(h₀) < J(0)`). -/
theorem discontinuity_nonconvex_example {wΛ wM wD lam h₀ : ℝ}
    (hwΛ : 0 ≤ wΛ) (hwM : 0 ≤ wM) (hlam : 0 < lam) (hh₀ : 0 < h₀)
    (hclick : wΛ * h₀ < wD * lam) :
    let J : ℝ → ℝ := fun m =>
      wΛ * m + wM * lam * max (h₀ - m) 0 + wD * lam * (if m < h₀ then 1 else 0)
    J h₀ < J 0 ∧ (J 0 + J h₀) / 2 < J (h₀ / 2) := by
  intro J
  have hJ0 : J 0 = wM * lam * h₀ + wD * lam := by
    simp only [J, mul_zero, zero_add, sub_zero, max_eq_left hh₀.le, hh₀, ↓reduceIte, mul_one]
  have hJh : J h₀ = wΛ * h₀ := by
    simp only [J, sub_self, max_self, mul_zero, add_zero, lt_irrefl, ↓reduceIte]
  have hhalf_lt : h₀ / 2 < h₀ := by linarith
  have hhalf_pos : 0 ≤ h₀ - h₀ / 2 := by linarith
  have hJhalf : J (h₀ / 2) = wΛ * (h₀ / 2) + wM * lam * (h₀ / 2) + wD * lam := by
    simp only [J, hhalf_lt, ↓reduceIte, mul_one, max_eq_left hhalf_pos]
    ring
  rw [hJ0, hJh, hJhalf]
  have h1 : 0 ≤ wM * lam * h₀ := by positivity
  have h2 : 0 ≤ wΛ * h₀ := by positivity
  constructor <;> linarith

end Unisono.Solutions.Optimal
