/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Optimal playout latency level under link pauses and discontinuities

A **pause** (the link-outage model of `Unisono.Spec.DelayModel`) is an interval
during which packets are delayed or dropped on a link. If the nominal playout
level leaves a safety margin of `m` seconds above baseline path and processing
delays, a non-overlapping pause of duration `h` causes `(h - m)⁺ = max (h - m) 0`
seconds of missed audio and triggers a playback discontinuity (click/glitch)
whenever `h > m`.

By Campbell's formula for stationary marked point processes with pause intensity
measure `ν = λ μ` (arrival rate `λ` per second times duration law `μ`), a
margin `m` incurs steady-state per-second cost:

    J(m) = wΛ · m + wΘ · (m - m₀)² + wM · ∫ (h - m)⁺ dν + wD · ν {h > m}

where `wΛ` prices mean latency, `wΘ` prices quadratic lip-sync deviation from
a target margin `m₀`, `wM` prices missed audio fraction, and `wD` prices
discontinuity rate.

## Main results

* **Missed-fraction quantile rule (`margin_best_missed`).** When `wΘ = 0` and
  `wD = 0`, any margin `m` satisfying `wM · ν {h > m} ≤ wΛ ≤ wM · ν {h ≥ m}`
  globally minimizes `wΛ · m + wM · ∫ (h - m)⁺ dν`.
* **Lip-sync tracking optimum (`margin_best_tracking`).** With quadratic
  tracking penalty `wΘ ≥ 0`, any margin `m` satisfying
  `wM · ν {h > m} ≤ wΛ + 2 wΘ (m - m₀) ≤ wM · ν {h ≥ m}` globally minimizes
  `wΛ · m + wΘ · (m - m₀)² + wM · ∫ (h - m)⁺ dν`.
* **Fleet-averaged pause measure (`fleet_average_missed_cost`).** Because
  `Unisono.Spec.World.missed` averages missed audio across all `R` speakers
  (`1 / R` factor), the fleet-wide expected missed cost at a shared margin `m`
  is governed by the *average* pause measure `ν̄ = (1 / R) ∑ r, ν r` (not the
  sum and not the worst single speaker).
* **Closed-form exponential optimum with discontinuities
  (`margin_best_exponential_with_clicks`).** When pauses arrive at rate `λ > 0`
  with exponentially distributed durations of mean `hBar > 0`, pricing
  discontinuities (`wD ≥ 0`) preserves convexity on `m ≥ 0` and yields the exact
  global minimizer
  `m* = max 0 (hBar * log (λ * (wM + wD / hBar) / wΛ))`.
* **Non-convexity under general discontinuities
  (`discontinuity_nonconvex_example`).** For a deterministic/atomic pause
  duration `h₀ > 0`, pricing discontinuities (`wD > 0`) introduces a downward jump
  at `m = h₀`, breaking convexity and invalidating local missed-only quantile
  rules—justifying a 1D search over candidate margins in practice.
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

/-- **Lip-sync tracking + missed-fraction optimality.** With latency weight `wΛ`,
quadratic tracking penalty `wΘ ≥ 0` around target margin `m₀`, and missed-audio
weight `wM ≥ 0`, any margin `m` satisfying the subgradient bracket
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

/-- **Fleet-averaged pause cost across `R` speakers.** Because
`Unisono.Spec.World.missed` averages the missed fraction across all `R > 0`
speakers, if each speaker `r` sees pause measure `ν r` (shifted by its baseline
delay), the fleet-averaged objective at a shared margin `m` equals the
single-measure objective under the fleet-averaged measure
`ν̄ = (R : ℝ≥0∞)⁻¹ • ∑ r, ν r`. -/
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

/-- **Closed-form exponential pause optimum including discontinuities.**
Suppose pauses arrive at rate `lam > 0` with exponentially distributed
durations of mean `hBar > 0`, so at margin `x ≥ 0`:
* expected missed time per second is `lam * hBar * exp (-x / hBar)`,
* expected discontinuity (click) rate is `lam * exp (-x / hBar)`.

With latency weight `wΛ > 0`, missed-audio weight `wM ≥ 0`, and discontinuity
weight `wD ≥ 0`, the combined objective
`J(x) = wΛ * x + wM * (lam * hBar * exp (-x / hBar)) + wD * (lam * exp (-x / hBar))`
is globally minimized over all `x ≥ 0` by
`m* = max 0 (hBar * log (lam * (wM + wD / hBar) / wΛ))` (when `wM + wD / hBar > 0`). -/
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
discontinuity jump at `m = h₀` breaks convexity
(`J(h₀ / 2) > (J(0) + J(h₀)) / 2`) and makes `m = h₀` strictly beat `m = 0`
(`J(h₀) < J(0)`), showing why general pause distributions with click penalties
require a 1D search rather than a local quantile rule. -/
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
