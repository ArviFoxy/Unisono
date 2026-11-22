/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.Delays
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A second-order noise model of the world

The second-order model specifies the means and covariances of continuous timing
noise in a random world: host clocks, network link jitter, audio device clocks,
and device timestamp errors. Every modeled random variable is required to be
square-integrable (`MemLp · 2 P`) under a probability measure `P`, so all
expectations and cross-moments are well-defined finite integrals.

In `Unisono.Spec.Objectives`, synchronization (`syncCost`) and target tracking
(`trackingCost`) are quadratic in timing errors, and mean latency
(`latencyCost`) is linear. First and second moments therefore determine the
steady-state performance of linear estimators and linear playback control laws
for those objectives (and for per-cycle quadratic roughness approximations),
while missed samples (`missedAt`) and discontinuities (`discontinuityAt`)
depend on how long link pauses and outages last and how often packets are
dropped (`Unisono.Spec.Models.Delays`).

* **Clocks (`ClockNoise`, `FollowsNoise`).** Host `i`'s clock reads
  `t + φ_i(t)` at true time `t`. Its fractional frequency `y_i = φ_i'` has the
  IEEE 1139 one-sided power spectral density
  `S_y(f) = white + flicker / f + walk / f²` for `f > 0` (white, flicker, and
  random-walk frequency noise). Because random-walk frequency noise has
  non-stationary first differences, the model specifies the zero means and
  covariances of second differences
  `Δ²_τ φ(t) = φ(t + 2τ) - 2 φ(t + τ) + φ(t)`. The spectral integral defining
  this covariance converges for every `ClockNoise`
  (`secondDifferenceCovariance_integrableOn`). For the white and random-walk
  components, the corresponding continuous-time phase and frequency diffusion
  variance rates are `white / 2` and `2 π² * walk`.
* **Link jitter (`JitterNoise`, `HasMoments`).** Each directed link `(i, j)`
  splits its jitter into three stationary components: sender-side shared jitter
  `tx i` (common to links leaving host `i`), receiver-side shared jitter `rx j`
  (common to links arriving at host `j`), and link-specific jitter `own i j`.
  Link-specific components are mutually uncorrelated across links and with
  `tx`/`rx`, while `tx i` and `rx i` on the same host (uplink–downlink
  correlation on a wireless interface) and `rx j`, `rx j'` across hosts
  (shared wireless access-point contention) are allowed to correlate.
* **Audio devices (`devicePhase`, `FollowsNoiseOnGrid`, `WhiteErrors`).** The
  capture device and each playback device are modeled as running on their own
  oscillators (for example, USB or dedicated audio clocks): their phases
  `times k - k / rate` relative to true time follow power-law frequency noise
  on the nominal sample grid `k / rate` and are uncorrelated with host clocks
  and with one another. Device timestamp errors are zero-mean and white across
  blocks, with per-device variances. All four source families (host clocks,
  audio device oscillators, link jitter, and timestamp errors) are mutually
  uncorrelated.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory

/-- Power-law frequency noise of a clock or audio device: the IEEE 1139
one-sided power spectral density of its fractional frequency at `f > 0` Hz is
`white + flicker / f + walk / f²`. -/
structure ClockNoise where
  /-- White frequency noise coefficient `h₀`, in `Hz⁻¹`. The corresponding
  phase diffusion variance rate is `white / 2` (`s² / s`). -/
  white : ℝ
  white_nonneg : 0 ≤ white
  /-- Flicker frequency noise coefficient `h₋₁`, dimensionless. -/
  flicker : ℝ
  flicker_nonneg : 0 ≤ flicker
  /-- Random-walk frequency noise coefficient `h₋₂`, in `Hz`. The
  corresponding fractional-frequency Brownian-motion variance rate is
  `2 π² * walk` (`s⁻¹`). -/
  walk : ℝ
  walk_nonneg : 0 ≤ walk

/-- The one-sided fractional-frequency power spectral density at `f > 0` Hz. -/
def ClockNoise.density (n : ClockNoise) (f : ℝ) : ℝ :=
  n.white + n.flicker / f + n.walk / f ^ 2

/-- Phase diffusion variance rate (in `s`) corresponding to white frequency
noise `h₀`: `Var(φ(t + τ) - φ(t)) = (h₀ / 2) * τ`. -/
def ClockNoise.whiteVarianceRate (n : ClockNoise) : ℝ :=
  n.white / 2

/-- Fractional-frequency random-walk variance rate (in `s⁻¹`) corresponding to
IEEE 1139 coefficient `h₋₂`: `Var(y(t + τ) - y(t)) = 2 π² h₋₂ τ`, matching
Allan variance `σ_y²(τ) = (2 π² / 3) h₋₂ τ`. -/
def ClockNoise.walkVarianceRate (n : ClockNoise) : ℝ :=
  2 * Real.pi ^ 2 * n.walk

/-- Zero frequency noise. -/
def ClockNoise.zero : ClockNoise :=
  ⟨0, le_rfl, 0, le_rfl, 0, le_rfl⟩

theorem ClockNoise.density_nonneg (n : ClockNoise) {f : ℝ} (hf : 0 < f) :
    0 ≤ n.density f := by
  unfold density
  have h1 : 0 ≤ n.flicker / f := div_nonneg n.flicker_nonneg hf.le
  have h2 : 0 ≤ n.walk / f ^ 2 := div_nonneg n.walk_nonneg (sq_nonneg f)
  linarith [n.white_nonneg]

theorem ClockNoise.whiteVarianceRate_nonneg (n : ClockNoise) : 0 ≤ n.whiteVarianceRate := by
  unfold whiteVarianceRate
  linarith [n.white_nonneg]

theorem ClockNoise.walkVarianceRate_nonneg (n : ClockNoise) : 0 ≤ n.walkVarianceRate := by
  unfold walkVarianceRate
  positivity [n.walk_nonneg]

/-- Second difference `Δ²_τ φ(t) = φ(t + 2τ) - 2 φ(t + τ) + φ(t)`. -/
def secondDifference (φ : ℝ → ℝ) (t τ : ℝ) : ℝ :=
  φ (t + 2 * τ) - 2 * φ (t + τ) + φ t

/-- The spectral integrand for `secondDifferenceCovariance`. -/
def secondDifferenceIntegrand (S : ℝ → ℝ) (t₁ τ₁ t₂ τ₂ f : ℝ) : ℝ :=
  S f / (2 * Real.pi * f) ^ 2 *
    (Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
      * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
      * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re

/-- Covariance between two phase second differences `Δ²_{τ₁} φ(t₁)` and
`Δ²_{τ₂} φ(t₂)` for a clock with one-sided fractional-frequency spectral
density `S`. The phase spectral density is `S(f) / (2πf)²`, and each second
difference contributes the frequency response `(e^{2πifτ} - 1)²`. -/
def secondDifferenceCovariance (S : ℝ → ℝ) (t₁ τ₁ t₂ τ₂ : ℝ) : ℝ :=
  ∫ f in Set.Ioi 0, secondDifferenceIntegrand S t₁ τ₁ t₂ τ₂ f

theorem secondDifferenceCovariance_zero (t₁ τ₁ t₂ τ₂ : ℝ) :
    secondDifferenceCovariance ClockNoise.zero.density t₁ τ₁ t₂ τ₂ = 0 := by
  simp [secondDifferenceCovariance, secondDifferenceIntegrand, ClockNoise.density, ClockNoise.zero]

private theorem norm_cexp_mul_I_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have hsq : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * Real.sin (x / 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have hcos : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      have h := Real.cos_two_mul (x / 2)
      have h2 : 2 * (x / 2) = x := by ring
      rw [h2] at h
      have hsc := Real.sin_sq_add_cos_sq (x / 2)
      linarith
    have hsc := Real.sin_sq_add_cos_sq x
    nlinarith
  have h1 : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ = |2 * Real.sin (x / 2)| := by
    have hsq' : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ^ 2 = |2 * Real.sin (x / 2)| ^ 2 := by
      rw [hsq, sq_abs]
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hsq'
  rw [h1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsin : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsin
  linarith

private theorem norm_cexp_mul_I_sub_one_le_two (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ 2 := by
  calc ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖
      ≤ ‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num

/-- **Spectral convergence.** For every `ClockNoise` (white, flicker, and
random-walk frequency noise), the improper integral defining
`secondDifferenceCovariance` converges absolutely on `(0, ∞)`. -/
theorem secondDifferenceCovariance_integrableOn (n : ClockNoise) (t₁ τ₁ t₂ τ₂ : ℝ) :
    IntegrableOn (secondDifferenceIntegrand n.density t₁ τ₁ t₂ τ₂) (Set.Ioi 0) volume := by
  have htot : 0 ≤ n.white + n.flicker + n.walk := by
    linarith [n.white_nonneg, n.flicker_nonneg, n.walk_nonneg]
  have hcont : ContinuousOn (secondDifferenceIntegrand n.density t₁ τ₁ t₂ τ₂) (Set.Ioi 0) := by
    unfold secondDifferenceIntegrand ClockNoise.density
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.div ?_ ?_ (fun f hf => ?_)
      · refine ((continuousOn_const.add (continuousOn_const.div continuousOn_id
          (fun f hf => ne_of_gt hf))).add (continuousOn_const.div
          (continuousOn_id.pow 2) (fun f hf => pow_ne_zero 2 (ne_of_gt hf))))
      · exact (continuousOn_const.mul continuousOn_id).pow 2
      · exact pow_ne_zero 2 (mul_ne_zero (by positivity) (ne_of_gt hf))
    · refine Complex.continuous_re.comp_continuousOn ?_
      have hc : Continuous (fun f : ℝ =>
          Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
            * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
            * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)) := by
        fun_prop
      exact hc.continuousOn
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · -- Near `f = 0⁺`, `|e^{2πifτ} - 1|² ≤ (2π|τ|f)²`, so the integrand is bounded by a constant.
    set C : ℝ := (n.white + n.flicker + n.walk) * (2 * Real.pi) ^ 2 * τ₁ ^ 2 * τ₂ ^ 2
    have hC_int : IntegrableOn (fun _ : ℝ => C) (Set.Ioc (0 : ℝ) 1) volume :=
      integrableOn_const (by simp)
    refine hC_int.mono'
      ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with f ⟨hf0, hf1⟩
    rw [Real.norm_eq_abs]
    unfold secondDifferenceIntegrand
    have hden_nn : 0 ≤ n.density f / (2 * Real.pi * f) ^ 2 :=
      div_nonneg (n.density_nonneg hf0) (sq_nonneg _)
    have hden_le : n.density f ≤ (n.white + n.flicker + n.walk) / f ^ 2 := by
      unfold ClockNoise.density
      have hfsq : f ^ 2 ≤ 1 := by nlinarith
      have hfsq' : f ^ 2 ≤ f := by nlinarith
      have h1 : n.white ≤ n.white / f ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hf0)]
        nlinarith [n.white_nonneg]
      have h2 : n.flicker / f ≤ n.flicker / f ^ 2 := by
        rw [div_le_div_iff₀ hf0 (sq_pos_of_pos hf0)]
        nlinarith [n.flicker_nonneg]
      linarith [show (n.white + n.flicker + n.walk) / f ^ 2
        = n.white / f ^ 2 + n.flicker / f ^ 2 + n.walk / f ^ 2 by ring]
    have hre : |(Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
        * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
        * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re|
        ≤ (2 * Real.pi * f) ^ 4 * τ₁ ^ 2 * τ₂ ^ 2 := by
      calc |(Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
            * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
            * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re|
          ≤ ‖Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
            * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
            * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖Complex.exp (((2 * Real.pi * f * (t₁ - t₂) : ℝ) : ℂ) * Complex.I)‖
            * ‖Complex.exp (((2 * Real.pi * f * τ₁ : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2
            * ‖Complex.exp (((2 * Real.pi * f * τ₂ : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 := by
            simp only [norm_mul, norm_pow, Complex.norm_conj, Complex.ofReal_mul,
              Complex.ofReal_sub, Complex.ofReal_ofNat]
        _ ≤ 1 * |2 * Real.pi * f * τ₁| ^ 2 * |2 * Real.pi * f * τ₂| ^ 2 := by
            rw [Complex.norm_exp_ofReal_mul_I]
            gcongr
            · exact norm_cexp_mul_I_sub_one_le _
            · exact norm_cexp_mul_I_sub_one_le _
        _ = (2 * Real.pi * f) ^ 4 * τ₁ ^ 2 * τ₂ ^ 2 := by
            rw [sq_abs, sq_abs]; ring
    rw [abs_mul, abs_of_nonneg hden_nn]
    have hbound_nn : 0 ≤ (n.white + n.flicker + n.walk) / f ^ 2 / (2 * Real.pi * f) ^ 2 := by
      positivity
    calc n.density f / (2 * Real.pi * f) ^ 2
          * |(Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
            * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
            * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re|
        ≤ ((n.white + n.flicker + n.walk) / f ^ 2 / (2 * Real.pi * f) ^ 2)
          * ((2 * Real.pi * f) ^ 4 * τ₁ ^ 2 * τ₂ ^ 2) := by
          gcongr
      _ = C := by
          have hf_ne : f ≠ 0 := ne_of_gt hf0
          have hpi_ne : (2 * Real.pi) ≠ 0 := by positivity
          dsimp only [C]
          field_simp
  · -- For `f > 1`, `n.density f` is bounded and the response is `≤ 16`, so `|integrand| ≤ C₂ * f⁻²`.
    set C₂ : ℝ := 16 * (n.white + n.flicker + n.walk) / (2 * Real.pi) ^ 2
    have hpow : IntegrableOn (fun f : ℝ => f ^ (-2 : ℝ)) (Set.Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    have hdom : IntegrableOn (fun f : ℝ => C₂ * f ^ (-2 : ℝ)) (Set.Ioi 1) volume :=
      hpow.const_mul C₂
    refine hdom.mono'
      ((hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with f hf1
    have hf1' : (1 : ℝ) < f := hf1
    have hf0 : (0 : ℝ) < f := lt_trans zero_lt_one hf1'
    rw [Real.norm_eq_abs]
    unfold secondDifferenceIntegrand
    have hden_nn : 0 ≤ n.density f / (2 * Real.pi * f) ^ 2 :=
      div_nonneg (n.density_nonneg hf0) (sq_nonneg _)
    have hden_le : n.density f ≤ n.white + n.flicker + n.walk := by
      unfold ClockNoise.density
      have h1 : n.flicker / f ≤ n.flicker :=
        div_le_self n.flicker_nonneg hf1'.le
      have h2 : n.walk / f ^ 2 ≤ n.walk :=
        div_le_self n.walk_nonneg (by nlinarith)
      linarith
    have hre : |(Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
        * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
        * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re| ≤ 16 := by
      calc |(Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
            * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
            * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re|
          ≤ ‖Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
            * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
            * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖Complex.exp (((2 * Real.pi * f * (t₁ - t₂) : ℝ) : ℂ) * Complex.I)‖
            * ‖Complex.exp (((2 * Real.pi * f * τ₁ : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2
            * ‖Complex.exp (((2 * Real.pi * f * τ₂ : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 := by
            simp only [norm_mul, norm_pow, Complex.norm_conj, Complex.ofReal_mul,
              Complex.ofReal_sub, Complex.ofReal_ofNat]
        _ ≤ 1 * 2 ^ 2 * 2 ^ 2 := by
            rw [Complex.norm_exp_ofReal_mul_I]
            gcongr
            · exact norm_cexp_mul_I_sub_one_le_two _
            · exact norm_cexp_mul_I_sub_one_le_two _
        _ = 16 := by norm_num
    rw [abs_mul, abs_of_nonneg hden_nn]
    have hrpow : f ^ (-2 : ℝ) = (f ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hf0.le, Real.rpow_natCast]
    have hbound_nn : 0 ≤ (n.white + n.flicker + n.walk) / (2 * Real.pi * f) ^ 2 := by
      positivity
    calc n.density f / (2 * Real.pi * f) ^ 2
          * |(Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
            * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
            * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re|
        ≤ ((n.white + n.flicker + n.walk) / (2 * Real.pi * f) ^ 2) * 16 := by gcongr
      _ = C₂ * f ^ (-2 : ℝ) := by
          rw [hrpow]
          have hf_ne : f ≠ 0 := ne_of_gt hf0
          have hpi_ne : (2 * Real.pi) ≠ 0 := by positivity
          dsimp only [C₂]
          field_simp

variable {Ω : Type} [MeasurableSpace Ω]

/-- A random clock phase `φ` follows `ClockNoise` `n`: every second difference
is square-integrable, has mean zero, and has covariance
`secondDifferenceCovariance n.density`. -/
def FollowsNoise (P : Measure Ω) (φ : Ω → ℝ → ℝ) (n : ClockNoise) : Prop :=
  (∀ t τ, MemLp (fun ω => secondDifference (φ ω) t τ) 2 P) ∧
  (∀ t τ, ∫ ω, secondDifference (φ ω) t τ ∂P = 0) ∧
    ∀ t₁ τ₁ t₂ τ₂, ∫ ω, secondDifference (φ ω) t₁ τ₁ * secondDifference (φ ω) t₂ τ₂ ∂P
      = secondDifferenceCovariance n.density t₁ τ₁ t₂ τ₂

/-- Two random phase processes have uncorrelated second differences. -/
def Uncorrelated (P : Measure Ω) (φ ψ : Ω → ℝ → ℝ) : Prop :=
  ∀ t₁ τ₁ t₂ τ₂, ∫ ω, secondDifference (φ ω) t₁ τ₁ * secondDifference (ψ ω) t₂ τ₂ ∂P = 0

/-- Device phase at frame or output sample `k` relative to true time:
`times k - k / rate`. Measuring against true time models audio devices driven
by their own oscillators (for example, USB audio interfaces) independently of
the host CPU clock. -/
def devicePhase (times : ℕ → Time) (rate : ℝ) (k : ℕ) : ℝ :=
  times k - k / rate

/-- Second difference `ψ(k + 2j) - 2 ψ(k + j) + ψ(k)` on a discrete grid. -/
def gridDifference (ψ : ℕ → ℝ) (k j : ℕ) : ℝ :=
  ψ (k + 2 * j) - 2 * ψ (k + j) + ψ k

/-- A discrete device phase process `ψ` follows `ClockNoise` `n` on the nominal
grid `k / rate`, with square-integrable second differences. -/
def FollowsNoiseOnGrid (P : Measure Ω) (ψ : Ω → ℕ → ℝ) (rate : ℝ) (n : ClockNoise) : Prop :=
  (∀ k j, MemLp (fun ω => gridDifference (ψ ω) k j) 2 P) ∧
  (∀ k j, ∫ ω, gridDifference (ψ ω) k j ∂P = 0) ∧
    ∀ k₁ j₁ k₂ j₂, ∫ ω, gridDifference (ψ ω) k₁ j₁ * gridDifference (ψ ω) k₂ j₂ ∂P
      = secondDifferenceCovariance n.density (k₁ / rate) (j₁ / rate) (k₂ / rate) (j₂ / rate)

/-- A continuous phase process and a discrete device phase process have
uncorrelated second differences. -/
def UncorrelatedGrid (P : Measure Ω) (φ : Ω → ℝ → ℝ) (ψ : Ω → ℕ → ℝ) : Prop :=
  ∀ t τ k j, ∫ ω, secondDifference (φ ω) t τ * gridDifference (ψ ω) k j ∂P = 0

/-- Two discrete device phase processes have uncorrelated second differences. -/
def UncorrelatedGrids (P : Measure Ω) (ψ₁ ψ₂ : Ω → ℕ → ℝ) : Prop :=
  ∀ k₁ j₁ k₂ j₂, ∫ ω, gridDifference (ψ₁ ω) k₁ j₁ * gridDifference (ψ₂ ω) k₂ j₂ ∂P = 0

/-- First and second moments of a stationary jitter process. -/
structure JitterNoise where
  /-- Mean jitter, in seconds. -/
  mean : ℝ
  /-- Covariance of jitter between two messages released `u` seconds apart,
  in `s²`. -/
  covariance : ℝ → ℝ

/-- A random jitter process `x` is square-integrable with mean `n.mean` and lag
covariance `n.covariance`. -/
def HasMoments (P : Measure Ω) (x : Ω → Time → ℝ) (n : JitterNoise) : Prop :=
  (∀ s, MemLp (fun ω => x ω s) 2 P) ∧
  (∀ s, ∫ ω, x ω s ∂P = n.mean) ∧
    ∀ s u, ∫ ω, (x ω s - n.mean) * (x ω u - n.mean) ∂P = n.covariance (u - s)

/-- Two random jitter processes have zero cross-covariance at every pair of
release times. -/
def UncorrelatedJitter (P : Measure Ω) (x y : Ω → Time → ℝ) : Prop :=
  ∀ s u, ∫ ω, (x ω s - ∫ ω', x ω' s ∂P) * (y ω u - ∫ ω', y ω' u ∂P) ∂P = 0

/-- A clock phase process and a jitter process are uncorrelated. -/
def UncorrelatedPhaseJitter (P : Measure Ω) (φ : Ω → ℝ → ℝ) (x : Ω → Time → ℝ) : Prop :=
  ∀ t τ s, ∫ ω, secondDifference (φ ω) t τ * (x ω s - ∫ ω', x ω' s ∂P) ∂P = 0

/-- A discrete device phase process and a jitter process are uncorrelated. -/
def UncorrelatedGridJitter (P : Measure Ω) (ψ : Ω → ℕ → ℝ) (x : Ω → Time → ℝ) : Prop :=
  ∀ k j s, ∫ ω, gridDifference (ψ ω) k j * (x ω s - ∫ ω', x ω' s ∂P) ∂P = 0

/-- Capture device timestamp error on block `b`: reported timestamp minus the
sender's clock reading when the block's first frame was captured. -/
def captureError {H : Type} {R : ℕ} (w : World H R) (b : ℕ) : ℝ :=
  w.source.reported b - (w.clock w.sender).read (w.source.capture (w.source.first b))

/-- Playback device timestamp error on speaker `r`, block `b`: reported
timestamp minus the host's clock reading when the block's first output sample
leaves. -/
def playbackError {H : Type} {R : ℕ} (w : World H R) (r : Fin R) (b : ℕ) : ℝ :=
  (w.speaker r).reported b - (w.clock (w.host r)).read ((w.speaker r).out ((w.speaker r).first b))

/-- Timestamp error sequence `e` is square-integrable, zero-mean, and white
across blocks with variance `v`. -/
def WhiteErrors (P : Measure Ω) (e : Ω → ℕ → ℝ) (v : ℝ) : Prop :=
  (∀ b, MemLp (fun ω => e ω b) 2 P) ∧
  (∀ b, ∫ ω, e ω b ∂P = 0) ∧
    ∀ b b', ∫ ω, e ω b * e ω b' ∂P = if b = b' then v else 0

/-- Two zero-mean timestamp error sequences are uncorrelated across all pairs
of blocks. -/
def UncorrelatedErrors (P : Measure Ω) (e₁ e₂ : Ω → ℕ → ℝ) : Prop :=
  ∀ b₁ b₂, ∫ ω, e₁ ω b₁ * e₂ ω b₂ ∂P = 0

/-- A clock phase process and a zero-mean timestamp error sequence are
uncorrelated. -/
def UncorrelatedPhaseError (P : Measure Ω) (φ : Ω → ℝ → ℝ) (e : Ω → ℕ → ℝ) : Prop :=
  ∀ t τ b, ∫ ω, secondDifference (φ ω) t τ * e ω b ∂P = 0

/-- A discrete device phase process and a zero-mean timestamp error sequence
are uncorrelated. -/
def UncorrelatedGridError (P : Measure Ω) (ψ : Ω → ℕ → ℝ) (e : Ω → ℕ → ℝ) : Prop :=
  ∀ k j b, ∫ ω, gridDifference (ψ ω) k j * e ω b ∂P = 0

/-- A jitter process and a zero-mean timestamp error sequence are uncorrelated. -/
def UncorrelatedJitterError (P : Measure Ω) (x : Ω → Time → ℝ) (e : Ω → ℕ → ℝ) : Prop :=
  ∀ s b, ∫ ω, (x ω s - ∫ ω', x ω' s ∂P) * e ω b ∂P = 0

/-- Parameters of the second-order noise model for hosts `H` and `R` speakers. -/
structure SecondOrderModel (H : Type) (R : ℕ) where
  /-- Common nominal sample rate of all realizations, in frames per second. -/
  rate : ℝ
  rate_pos : 0 < rate
  /-- Frequency noise of each host's clock relative to true time. -/
  clock : H → ClockNoise
  /-- Shared outgoing jitter for all links leaving host `i`. -/
  txJitter : H → JitterNoise
  /-- Shared incoming jitter for all links arriving at host `j`. -/
  rxJitter : H → JitterNoise
  /-- Link-specific jitter for each directed link `(i, j)`. -/
  ownJitter : H → H → JitterNoise
  /-- Frequency noise of the capture device oscillator relative to true time. -/
  capture : ClockNoise
  /-- Frequency noise of each speaker's playback oscillator relative to true
  time. -/
  playback : Fin R → ClockNoise
  /-- Variance of the capture device's white timestamp errors, in `s²`. -/
  captureTimestampVariance : ℝ
  captureTimestampVariance_nonneg : 0 ≤ captureTimestampVariance
  /-- Variance of each speaker's white timestamp errors, in `s²`. -/
  playbackTimestampVariance : Fin R → ℝ
  playbackTimestampVariance_nonneg : ∀ r, 0 ≤ playbackTimestampVariance r

/-- A random world `world` under probability measure `P`, with links `d`,
satisfies the second-order noise model `m`:

* `P` is a probability measure and every modeled second difference, jitter
  sample, and timestamp error is square-integrable (`MemLp · 2 P`).
* Every host clock follows `m.clock i`, and distinct host clocks have
  uncorrelated second differences.
* Every link's jitter decomposes into `tx i + rx j + own i j` with the
  specified stationary means and covariances. Link-specific components `own`
  are uncorrelated across links and with `tx`/`rx`, and `tx i` is uncorrelated
  with `tx i'` (`i ≠ i'`) and `rx j` (`j ≠ i`). Same-host `tx i` and `rx i`
  (uplink–downlink correlation) and distinct-host `rx j`, `rx j'` (shared
  wireless access point contention) are left unconstrained.
* The capture and playback devices share a deterministic nominal rate `rate`,
  follow their grid noise spectra relative to true time (modeling independent
  device oscillators), and are uncorrelated with host clocks and with one
  another.
* Capture and playback timestamp errors are white with their per-device
  variances and uncorrelated across devices.
* All four source families (host clocks, device oscillators, link jitter, and
  timestamp errors) are mutually uncorrelated.

Network pauses, outages, and packet drops are not constrained here; combine
this structure with `DelayModel.Holds` when modeling losses and pauses. -/
structure SecondOrderModel.Holds {H : Type} {R : ℕ} (m : SecondOrderModel H R)
    (P : Measure Ω) (world : Ω → World H R) (d : Ω → H → H → Link) : Prop where
  /-- `P` is a probability measure. -/
  prob : IsProbabilityMeasure P
  /-- Each realization's network is given by the links `d ω`. -/
  network : ∀ ω, (world ω).HasDelays (d ω)
  /-- All realizations share the model's nominal sample rate `m.rate`. -/
  rate_eq : ∀ ω, (world ω).rate = m.rate
  /-- Every host clock follows its power-law noise spectrum. -/
  clocks : ∀ i, FollowsNoise P (fun ω t => ((world ω).clock i).read t - t) (m.clock i)
  /-- Distinct hosts have uncorrelated clock phases. -/
  clocks_uncorrelated : ∀ i j, i ≠ j →
    Uncorrelated P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω t => ((world ω).clock j).read t - t)
  /-- Link jitter splits into sender-common, receiver-common, and link-specific
  stationary components, uncorrelated with clocks, device oscillators, and
  timestamp errors. -/
  jitter : ∃ tx : Ω → H → Time → ℝ, ∃ rx : Ω → H → Time → ℝ,
      ∃ own : Ω → H → H → Time → ℝ,
    (∀ ω i j u, (d ω i j).jitter u = tx ω i u + rx ω j u + own ω i j u)
      ∧ (∀ i, HasMoments P (fun ω => tx ω i) (m.txJitter i))
      ∧ (∀ j, HasMoments P (fun ω => rx ω j) (m.rxJitter j))
      ∧ (∀ i j, HasMoments P (fun ω => own ω i j) (m.ownJitter i j))
      ∧ (∀ i i', i ≠ i' → UncorrelatedJitter P (fun ω => tx ω i) (fun ω => tx ω i'))
      ∧ (∀ i j, i ≠ j → UncorrelatedJitter P (fun ω => tx ω i) (fun ω => rx ω j))
      ∧ (∀ i j i', UncorrelatedJitter P (fun ω => own ω i j) (fun ω => tx ω i'))
      ∧ (∀ i j j', UncorrelatedJitter P (fun ω => own ω i j) (fun ω => rx ω j'))
      ∧ (∀ i j i' j', (i, j) ≠ (i', j') →
          UncorrelatedJitter P (fun ω => own ω i j) (fun ω => own ω i' j'))
      ∧ (∀ h i, UncorrelatedPhaseJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => tx ω i))
      ∧ (∀ h j, UncorrelatedPhaseJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => rx ω j))
      ∧ (∀ h i j, UncorrelatedPhaseJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => own ω i j))
      ∧ (∀ i, UncorrelatedGridJitter P (fun ω => devicePhase (world ω).source.capture m.rate)
          (fun ω => tx ω i))
      ∧ (∀ j, UncorrelatedGridJitter P (fun ω => devicePhase (world ω).source.capture m.rate)
          (fun ω => rx ω j))
      ∧ (∀ i j, UncorrelatedGridJitter P (fun ω => devicePhase (world ω).source.capture m.rate)
          (fun ω => own ω i j))
      ∧ (∀ r i, UncorrelatedGridJitter P (fun ω => devicePhase ((world ω).speaker r).out m.rate)
          (fun ω => tx ω i))
      ∧ (∀ r j, UncorrelatedGridJitter P (fun ω => devicePhase ((world ω).speaker r).out m.rate)
          (fun ω => rx ω j))
      ∧ (∀ r i j, UncorrelatedGridJitter P (fun ω => devicePhase ((world ω).speaker r).out m.rate)
          (fun ω => own ω i j))
      ∧ (∀ i, UncorrelatedJitterError P (fun ω => tx ω i) (fun ω => captureError (world ω)))
      ∧ (∀ j, UncorrelatedJitterError P (fun ω => rx ω j) (fun ω => captureError (world ω)))
      ∧ (∀ i j, UncorrelatedJitterError P (fun ω => own ω i j) (fun ω => captureError (world ω)))
      ∧ (∀ r i, UncorrelatedJitterError P (fun ω => tx ω i) (fun ω => playbackError (world ω) r))
      ∧ (∀ r j, UncorrelatedJitterError P (fun ω => rx ω j) (fun ω => playbackError (world ω) r))
      ∧ (∀ r i j, UncorrelatedJitterError P (fun ω => own ω i j)
          (fun ω => playbackError (world ω) r))
  /-- The capture device oscillator follows its power-law noise against true time. -/
  capture : FollowsNoiseOnGrid P
    (fun ω => devicePhase (world ω).source.capture m.rate)
    m.rate m.capture
  /-- Each playback device oscillator follows its power-law noise against true time. -/
  playback : ∀ r, FollowsNoiseOnGrid P
    (fun ω => devicePhase ((world ω).speaker r).out m.rate)
    m.rate (m.playback r)
  /-- Device oscillators are uncorrelated with host clocks and with one another. -/
  capture_clock_uncorrelated : ∀ i,
    UncorrelatedGrid P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω => devicePhase (world ω).source.capture m.rate)
  playback_clock_uncorrelated : ∀ i r,
    UncorrelatedGrid P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω => devicePhase ((world ω).speaker r).out m.rate)
  capture_playback_uncorrelated : ∀ r,
    UncorrelatedGrids P
      (fun ω => devicePhase (world ω).source.capture m.rate)
      (fun ω => devicePhase ((world ω).speaker r).out m.rate)
  playback_uncorrelated : ∀ r r', r ≠ r' →
    UncorrelatedGrids P
      (fun ω => devicePhase ((world ω).speaker r).out m.rate)
      (fun ω => devicePhase ((world ω).speaker r').out m.rate)
  /-- Capture timestamp errors are white with `m.captureTimestampVariance`. -/
  capture_timestamps : WhiteErrors P (fun ω => captureError (world ω)) m.captureTimestampVariance
  /-- Playback timestamp errors are white with `m.playbackTimestampVariance r`. -/
  playback_timestamps : ∀ r,
    WhiteErrors P (fun ω => playbackError (world ω) r) (m.playbackTimestampVariance r)
  /-- Timestamp errors are uncorrelated across devices and with clocks and
  device oscillators. -/
  capture_playback_timestamps_uncorrelated : ∀ r,
    UncorrelatedErrors P (fun ω => captureError (world ω)) (fun ω => playbackError (world ω) r)
  playback_timestamps_uncorrelated : ∀ r r', r ≠ r' →
    UncorrelatedErrors P (fun ω => playbackError (world ω) r) (fun ω => playbackError (world ω) r')
  clock_capture_timestamps_uncorrelated : ∀ i,
    UncorrelatedPhaseError P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω => captureError (world ω))
  clock_playback_timestamps_uncorrelated : ∀ i r,
    UncorrelatedPhaseError P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω => playbackError (world ω) r)
  capture_device_capture_timestamps_uncorrelated :
    UncorrelatedGridError P (fun ω => devicePhase (world ω).source.capture m.rate)
      (fun ω => captureError (world ω))
  capture_device_playback_timestamps_uncorrelated : ∀ r,
    UncorrelatedGridError P (fun ω => devicePhase (world ω).source.capture m.rate)
      (fun ω => playbackError (world ω) r)
  playback_device_capture_timestamps_uncorrelated : ∀ r,
    UncorrelatedGridError P (fun ω => devicePhase ((world ω).speaker r).out m.rate)
      (fun ω => captureError (world ω))
  playback_device_playback_timestamps_uncorrelated : ∀ r r',
    UncorrelatedGridError P (fun ω => devicePhase ((world ω).speaker r').out m.rate)
      (fun ω => playbackError (world ω) r)

end Unisono.Spec
