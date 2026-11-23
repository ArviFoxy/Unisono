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
(`latencyCost`) is linear. For linear time-invariant estimators and linear
control loops with measurements at fixed times, first and second moments
determine steady-state performance on those objectives (and on per-cycle
quadratic roughness approximations); packet loss, minimum-RTT selection, speed
clamps, and random device request times introduce higher-moment dependence,
while missed samples (`missedAt`) and discontinuities (`discontinuityAt`)
depend on how long link pauses and outages last and how often packets are
dropped (`Unisono.Spec.Models.Delays`).

* **Band-limited power-law clocks (`ClockNoise`, `FollowsNoise`).** Host `i`'s
  clock reads `t + φ_i(t)` at true time `t`. Its fractional frequency `y_i = φ_i'`
  has the IEEE Std 1139-2008 one-sided power spectral density
  `S_y(f) = white + flicker / f + walk / f²` over a finite frequency band
  `[lowFreq, highFreq]` with `0 < lowFreq ≤ highFreq` (and `0` outside that
  band). Band-limiting avoids both the small-lag white-noise divergence and the
  large-lag random-walk/flicker divergence that would otherwise conflict with
  any uniform bound on clock rate error (`Clock.RateWithin ε`):
  `secondDifferenceCovariance_diag_le` shows
  `E[(Δ²_τ φ)²] ≤ 4 τ² ∫ S_y(f) df` for every lag `τ`. For the in-band white
  and random-walk components, the state-space phase and frequency diffusion
  variance rates are `white / 2` and `2 π² * walk`.
* **Link jitter (`JitterNoise`, `PacketJitterNoise`, `HasMoments`, `HasPacketMoments`).**
  Each directed link `(i, j)`—covering both hosts' network stacks as well as
  the physical/wireless path between them—splits its per-packet jitter at
  release time `u` and message index `q` into three stationary components:
  sender-side shared jitter `tx i u` (common to links leaving host `i`),
  receiver-side shared jitter `rx j u` (common to links arriving at host `j`),
  and link-specific per-packet jitter `own i j u q`. Link-specific components
  `own` are mutually uncorrelated across distinct links and with `tx`/`rx`,
  while correlations among `tx` and `rx` (same-host network-stack coupling and
  cross-station shared wireless access-point contention) are left unconstrained.
* **Audio devices (`devicePhase`, `FollowsNoiseOnGrid`, `WhiteErrors`).** The
  capture device and each playback device have phase `times k - k / rate`
  relative to true time following band-limited power-law frequency noise on the
  nominal sample grid `k / rate`. Each device is required to be uncorrelated
  with clocks and devices on *other* hosts, while remaining free to correlate
  with its own host's clock and with co-located devices on the same host (thus
  admitting both host-clocked hardware / multichannel interfaces and
  independent USB audio crystals). Device timestamp errors are zero-mean and
  white across blocks, with per-device variances, and are uncorrelated across
  devices and with clocks, devices, and jitter.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory

/-- Band-limited power-law frequency noise of a clock or audio device: the
IEEE Std 1139-2008 one-sided power spectral density of its fractional frequency
is `white + flicker / f + walk / f²` for `f ∈ [lowFreq, highFreq]` (`0 < lowFreq
≤ highFreq`) and `0` outside that band. -/
structure ClockNoise where
  /-- White frequency noise coefficient `h₀`, in `Hz⁻¹`. The corresponding
  in-band phase diffusion variance rate is `white / 2` (`s² / s`). -/
  white : ℝ
  white_nonneg : 0 ≤ white
  /-- Flicker frequency noise coefficient `h₋₁`, dimensionless. -/
  flicker : ℝ
  flicker_nonneg : 0 ≤ flicker
  /-- Random-walk frequency noise coefficient `h₋₂`, in `Hz`. The
  corresponding in-band fractional-frequency Brownian-motion variance rate is
  `2 π² * walk` (`s⁻¹`). -/
  walk : ℝ
  walk_nonneg : 0 ≤ walk
  /-- Lower cutoff frequency `f_lo > 0` in Hz (cuts off infrared drift). -/
  lowFreq : ℝ
  /-- Upper cutoff frequency `f_hi ≥ f_lo` in Hz (cuts off ultraviolet noise). -/
  highFreq : ℝ
  lowFreq_pos : 0 < lowFreq
  lowFreq_le_highFreq : lowFreq ≤ highFreq

/-- The band-limited one-sided fractional-frequency power spectral density at
`f` Hz: `white + flicker / f + walk / f²` on `[lowFreq, highFreq]` and `0`
elsewhere. -/
def ClockNoise.density (n : ClockNoise) (f : ℝ) : ℝ :=
  if n.lowFreq ≤ f ∧ f ≤ n.highFreq then
    n.white + n.flicker / f + n.walk / f ^ 2
  else 0

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
  ⟨0, le_rfl, 0, le_rfl, 0, le_rfl, 1, 1, one_pos, le_rfl⟩

theorem ClockNoise.density_nonneg (n : ClockNoise) {f : ℝ} (hf : 0 < f) :
    0 ≤ n.density f := by
  unfold density
  split_ifs with hband
  · have h1 : 0 ≤ n.flicker / f := div_nonneg n.flicker_nonneg hf.le
    have h2 : 0 ≤ n.walk / f ^ 2 := div_nonneg n.walk_nonneg (sq_nonneg f)
    linarith [n.white_nonneg]
  · exact le_rfl

theorem ClockNoise.density_integrableOn (n : ClockNoise) :
    IntegrableOn n.density (Set.Icc n.lowFreq n.highFreq) volume := by
  have hcont : ContinuousOn (fun f => n.white + n.flicker / f + n.walk / f ^ 2)
      (Set.Icc n.lowFreq n.highFreq) := by
    have hne : ∀ f ∈ Set.Icc n.lowFreq n.highFreq, f ≠ 0 := fun f hf =>
      ne_of_gt (lt_of_lt_of_le n.lowFreq_pos hf.1)
    refine (continuousOn_const.add (continuousOn_const.div continuousOn_id hne)).add
      (continuousOn_const.div (continuousOn_id.pow 2) (fun f hf => pow_ne_zero 2 (hne f hf)))
  refine (hcont.integrableOn_Icc).congr_fun (fun f hf => ?_) measurableSet_Icc
  simp [ClockNoise.density, hf.1, hf.2]

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

/-- **Spectral convergence.** For every band-limited `ClockNoise`, the integral
defining `secondDifferenceCovariance` converges absolutely on `(0, ∞)` (it is
supported on the compact band `[n.lowFreq, n.highFreq]`). -/
theorem secondDifferenceCovariance_integrableOn (n : ClockNoise) (t₁ τ₁ t₂ τ₂ : ℝ) :
    IntegrableOn (secondDifferenceIntegrand n.density t₁ τ₁ t₂ τ₂) (Set.Ioi 0) volume := by
  let g : ℝ → ℝ := fun f =>
    (n.white + n.flicker / f + n.walk / f ^ 2) / (2 * Real.pi * f) ^ 2 *
      (Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
        * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
        * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re
  have hcont : ContinuousOn g (Set.Icc n.lowFreq n.highFreq) := by
    have hne : ∀ f ∈ Set.Icc n.lowFreq n.highFreq, f ≠ 0 := fun f hf =>
      ne_of_gt (lt_of_lt_of_le n.lowFreq_pos hf.1)
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.div ?_ ((continuousOn_const.mul continuousOn_id).pow 2)
        (fun f hf => pow_ne_zero 2 (mul_ne_zero (by positivity) (hne f hf)))
      exact (continuousOn_const.add (continuousOn_const.div continuousOn_id hne)).add
        (continuousOn_const.div (continuousOn_id.pow 2) (fun f hf => pow_ne_zero 2 (hne f hf)))
    · refine Complex.continuous_re.comp_continuousOn ?_
      have hc : Continuous (fun f : ℝ =>
          Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
            * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
            * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)) := by
        fun_prop
      exact hc.continuousOn
  have hint_band : IntegrableOn (secondDifferenceIntegrand n.density t₁ τ₁ t₂ τ₂)
      (Set.Icc n.lowFreq n.highFreq) volume := by
    refine (hcont.integrableOn_Icc).congr_fun (fun f hf => ?_) measurableSet_Icc
    simp only [secondDifferenceIntegrand, ClockNoise.density, hf.1, hf.2, and_self, ↓reduceIte, g]
  have hsub : Set.Icc n.lowFreq n.highFreq ⊆ Set.Ioi 0 :=
    fun f hf => lt_of_lt_of_le n.lowFreq_pos hf.1
  rw [← Set.union_sdiff_cancel hsub]
  refine hint_band.union ?_
  refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ))
      (Set.Ioi 0 \ Set.Icc n.lowFreq n.highFreq) volume).congr_fun (fun f hf => ?_)
      (measurableSet_Ioi.diff measurableSet_Icc)
  have hnot : ¬ (n.lowFreq ≤ f ∧ f ≤ n.highFreq) := hf.2
  simp [secondDifferenceIntegrand, ClockNoise.density, hnot]

/-- **Compatibility with uniform rate bounds.** Because `n` is band-limited to
`[n.lowFreq, n.highFreq]` with `0 < n.lowFreq`, its second-difference variance
satisfies `secondDifferenceCovariance n.density t τ t τ ≤ 4 τ² ∫ S(f) df` for
every `t` and every lag `τ`. Whenever the integrated fractional-frequency
variance `∫ S(f) df ≤ ε²`, this stays within the `(2 ε τ)²` ceiling implied by
`Clock.RateWithin ε` at all lags (both `τ → 0` and `τ → ∞`). -/
theorem secondDifferenceCovariance_diag_le (n : ClockNoise) (t τ : ℝ) :
    secondDifferenceCovariance n.density t τ t τ
      ≤ 4 * τ ^ 2 * ∫ f in Set.Icc n.lowFreq n.highFreq, n.density f := by
  have hsub : Set.Icc n.lowFreq n.highFreq ⊆ Set.Ioi 0 :=
    fun f hf => lt_of_lt_of_le n.lowFreq_pos hf.1
  have hint_all := secondDifferenceCovariance_integrableOn n t τ t τ
  have heq_band : secondDifferenceCovariance n.density t τ t τ
      = ∫ f in Set.Icc n.lowFreq n.highFreq, secondDifferenceIntegrand n.density t τ t τ f := by
    unfold secondDifferenceCovariance
    rw [← Set.union_sdiff_cancel hsub,
      setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioi.diff measurableSet_Icc)
        (hint_all.mono_set hsub) (hint_all.mono_set Set.sdiff_subset)]
    have hzero : ∫ f in Set.Ioi 0 \ Set.Icc n.lowFreq n.highFreq,
        secondDifferenceIntegrand n.density t τ t τ f = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun f hf => ?_
      have hnot : ¬ (n.lowFreq ≤ f ∧ f ≤ n.highFreq) := hf.2
      simp [secondDifferenceIntegrand, ClockNoise.density, hnot]
    rw [hzero, add_zero]
  rw [heq_band, ← integral_const_mul]
  refine setIntegral_mono_on (hint_all.mono_set hsub) (n.density_integrableOn.const_mul _)
    measurableSet_Icc fun f hf => ?_
  have hf0 : 0 < f := lt_of_lt_of_le n.lowFreq_pos hf.1
  have hden_nn : 0 ≤ n.density f := n.density_nonneg hf0
  have h2pf_pos : 0 < 2 * Real.pi * f := by positivity
  unfold secondDifferenceIntegrand
  have hexp0 : Complex.exp (2 * Real.pi * f * (t - t) * Complex.I) = 1 := by simp
  rw [hexp0, one_mul]
  set z : ℂ := Complex.exp (((2 * Real.pi * f * τ : ℝ) : ℂ) * Complex.I) - 1
  have hre : (z ^ 2 * (starRingEnd ℂ) (z ^ 2)).re = ‖z‖ ^ 4 := by
    have hmul : z ^ 2 * (starRingEnd ℂ) (z ^ 2) = ((Complex.normSq (z ^ 2) : ℝ) : ℂ) :=
      Complex.mul_conj (z ^ 2)
    rw [hmul, Complex.ofReal_re, Complex.normSq_eq_norm_sq, norm_pow]
    ring
  have hre' : ((Complex.exp (2 * Real.pi * f * τ * Complex.I) - 1) ^ 2
      * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ * Complex.I) - 1) ^ 2)).re
      = ‖z‖ ^ 4 := by
    have hz_eq : Complex.exp (2 * Real.pi * f * τ * Complex.I) - 1 = z := by
      simp [z, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hz_eq]
    exact hre
  rw [hre']
  have hz1 : ‖z‖ ≤ |2 * Real.pi * f * τ| := norm_cexp_mul_I_sub_one_le _
  have hz2 : ‖z‖ ≤ 2 := norm_cexp_mul_I_sub_one_le_two _
  have hz4 : ‖z‖ ^ 4 ≤ 4 * (2 * Real.pi * f) ^ 2 * τ ^ 2 := by
    have hsq1 : ‖z‖ ^ 2 ≤ (2 * Real.pi * f * τ) ^ 2 := by
      calc ‖z‖ ^ 2 ≤ |2 * Real.pi * f * τ| ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz1 2
        _ = (2 * Real.pi * f * τ) ^ 2 := sq_abs _
    have hsq2 : ‖z‖ ^ 2 ≤ 4 := by
      calc ‖z‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz2 2
        _ = 4 := by norm_num
    calc ‖z‖ ^ 4 = ‖z‖ ^ 2 * ‖z‖ ^ 2 := by ring
      _ ≤ 4 * (2 * Real.pi * f * τ) ^ 2 :=
          mul_le_mul hsq2 hsq1 (sq_nonneg _) (by norm_num)
      _ = 4 * (2 * Real.pi * f) ^ 2 * τ ^ 2 := by ring
  have hdiv : n.density f / (2 * Real.pi * f) ^ 2 * ‖z‖ ^ 4
      ≤ n.density f / (2 * Real.pi * f) ^ 2 * (4 * (2 * Real.pi * f) ^ 2 * τ ^ 2) :=
    mul_le_mul_of_nonneg_left hz4 (div_nonneg hden_nn (sq_nonneg _))
  have hsimp : n.density f / (2 * Real.pi * f) ^ 2 * (4 * (2 * Real.pi * f) ^ 2 * τ ^ 2)
      = 4 * τ ^ 2 * n.density f := by
    have hne : (2 * Real.pi * f) ^ 2 ≠ 0 := pow_ne_zero 2 h2pf_pos.ne'
    field_simp
  linarith

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

/-- First and second moments of a stationary per-packet jitter process indexed
by `(release_time, message_number)`. -/
structure PacketJitterNoise where
  /-- Mean jitter, in seconds. -/
  mean : ℝ
  /-- Covariance of jitter between two messages released `Δt` seconds apart
  and `Δq` message indices apart, in `s²`. -/
  covariance : ℝ → ℤ → ℝ

/-- A random per-packet jitter process `x : Ω → Time → ℕ → ℝ` is
square-integrable with mean `n.mean` and lag covariance `n.covariance`. -/
def HasPacketMoments (P : Measure Ω) (x : Ω → Time → ℕ → ℝ) (n : PacketJitterNoise) : Prop :=
  (∀ s q, MemLp (fun ω => x ω s q) 2 P) ∧
  (∀ s q, ∫ ω, x ω s q ∂P = n.mean) ∧
    ∀ s q u q',
      ∫ ω, (x ω s q - n.mean) * (x ω u q' - n.mean) ∂P
        = n.covariance (u - s) ((q' : ℤ) - (q : ℤ))

/-- Two per-packet jitter processes have zero cross-covariance at every pair of
release times and message indices. -/
def UncorrelatedPacketJitter (P : Measure Ω) (x y : Ω → Time → ℕ → ℝ) : Prop :=
  ∀ s q u q',
    ∫ ω, (x ω s q - ∫ ω', x ω' s q ∂P) * (y ω u q' - ∫ ω', y ω' u q' ∂P) ∂P = 0

/-- A per-packet jitter process and a time-indexed jitter process have zero
cross-covariance. -/
def UncorrelatedPacketTimeJitter (P : Measure Ω) (x : Ω → Time → ℕ → ℝ) (y : Ω → Time → ℝ) :
    Prop :=
  ∀ s q u,
    ∫ ω, (x ω s q - ∫ ω', x ω' s q ∂P) * (y ω u - ∫ ω', y ω' u ∂P) ∂P = 0

/-- A clock phase process and a per-packet jitter process are uncorrelated. -/
def UncorrelatedPhasePacketJitter (P : Measure Ω) (φ : Ω → ℝ → ℝ) (x : Ω → Time → ℕ → ℝ) :
    Prop :=
  ∀ t τ s q,
    ∫ ω, secondDifference (φ ω) t τ * (x ω s q - ∫ ω', x ω' s q ∂P) ∂P = 0

/-- A discrete device phase process and a per-packet jitter process are
uncorrelated. -/
def UncorrelatedGridPacketJitter (P : Measure Ω) (ψ : Ω → ℕ → ℝ) (x : Ω → Time → ℕ → ℝ) :
    Prop :=
  ∀ k j s q,
    ∫ ω, gridDifference (ψ ω) k j * (x ω s q - ∫ ω', x ω' s q ∂P) ∂P = 0

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

/-- A per-packet jitter process and a zero-mean timestamp error sequence are
uncorrelated. -/
def UncorrelatedPacketJitterError (P : Measure Ω) (x : Ω → Time → ℕ → ℝ) (e : Ω → ℕ → ℝ) :
    Prop :=
  ∀ s q b, ∫ ω, (x ω s q - ∫ ω', x ω' s q ∂P) * e ω b ∂P = 0

/-- Parameters of the second-order moment model class for hosts `H` and `R`
speakers. -/
structure SecondOrderMoments (H : Type) (R : ℕ) where
  /-- Common nominal sample rate of all realizations, in frames per second. -/
  rate : ℝ
  rate_pos : 0 < rate
  /-- Fixed sender host across all realizations. -/
  sender : H
  /-- Fixed host carrying each speaker across all realizations. -/
  host : Fin R → H
  /-- Frequency noise of each host's clock relative to true time. -/
  clock : H → ClockNoise
  /-- Shared outgoing jitter for all links leaving host `i` (e.g. host TX
  network stack and shared medium contention). -/
  txJitter : H → JitterNoise
  /-- Shared incoming jitter for all links arriving at host `j` (e.g. host RX
  network stack and shared medium contention). -/
  rxJitter : H → JitterNoise
  /-- Link-specific per-packet jitter for each directed link `(i, j)`. -/
  ownJitter : H → H → PacketJitterNoise
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
belongs to the second-order moment model class `m`:

* `P` is a probability measure and every modeled second difference, jitter
  sample, and timestamp error is square-integrable (`MemLp · 2 P`).
* Every host clock follows `m.clock i` (band-limited to `[lowFreq, highFreq]`),
  and distinct host clocks have uncorrelated second differences.
* Every link's per-packet jitter decomposes into `tx i u + rx j u + own i j u q`
  with the specified stationary means and covariances. Link-specific per-packet
  components `own` are uncorrelated across distinct links and with `tx`/`rx`,
  while correlations among `tx` and `rx` (same-host network-stack coupling and
  cross-station shared wireless access-point contention) are left unconstrained.
* The capture and playback devices share a deterministic nominal rate `rate`
  and follow their grid noise spectra relative to true time. Each device is
  uncorrelated with clocks and devices on *other* hosts, while remaining free
  to correlate with its own host's clock and with co-located devices on the
  same host (covering both host-clocked hardware and independent crystals).
* Capture and playback timestamp errors are white with their per-device
  variances and uncorrelated across devices, clocks, devices, and jitter.

Network pauses, outages, packet drops, block sizes, handoff delay, and request
lead are not constrained here; combine this structure with
`StationaryNetworkDisturbances.Holds` and device/blocking bounds in
`StochasticWorld` for a full-world probabilistic model class. -/
structure SecondOrderMoments.Holds {H : Type} {R : ℕ} (m : SecondOrderMoments H R)
    (P : Measure Ω) (world : Ω → World H R) (d : Ω → H → H → Link) : Prop where
  /-- `P` is a probability measure. -/
  prob : IsProbabilityMeasure P
  /-- Each realization's network is given by the links `d ω`. -/
  network : ∀ ω, (world ω).HasDelays (d ω)
  /-- All realizations share the model's nominal sample rate `m.rate`. -/
  rate_eq : ∀ ω, (world ω).rate = m.rate
  /-- All realizations share the model's sender host `m.sender`. -/
  sender_eq : ∀ ω, (world ω).sender = m.sender
  /-- All realizations share each speaker's host `m.host r`. -/
  host_eq : ∀ ω r, (world ω).host r = m.host r
  /-- Every host clock follows its band-limited power-law noise spectrum. -/
  clocks : ∀ i, FollowsNoise P (fun ω t => ((world ω).clock i).read t - t) (m.clock i)
  /-- Distinct hosts have uncorrelated clock phases. -/
  clocks_uncorrelated : ∀ i j, i ≠ j →
    Uncorrelated P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω t => ((world ω).clock j).read t - t)
  /-- Link jitter splits into sender-common `tx`, receiver-common `rx`, and
  link-specific per-packet `own` stationary components. Link-specific jitter
  `own` is uncorrelated across distinct links and with `tx`/`rx`, while
  correlations among `tx` and `rx` are left unconstrained for shared host
  stacks and wireless media. All jitter components are uncorrelated with
  clocks, device oscillators, and timestamp errors. -/
  jitter : ∃ tx : Ω → H → Time → ℝ, ∃ rx : Ω → H → Time → ℝ,
      ∃ own : Ω → H → H → Time → ℕ → ℝ,
    (∀ ω i j u q, (d ω i j).jitter u q = tx ω i u + rx ω j u + own ω i j u q)
      ∧ (∀ i, HasMoments P (fun ω => tx ω i) (m.txJitter i))
      ∧ (∀ j, HasMoments P (fun ω => rx ω j) (m.rxJitter j))
      ∧ (∀ i j, HasPacketMoments P (fun ω => own ω i j) (m.ownJitter i j))
      ∧ (∀ i j i', UncorrelatedPacketTimeJitter P (fun ω => own ω i j) (fun ω => tx ω i'))
      ∧ (∀ i j j', UncorrelatedPacketTimeJitter P (fun ω => own ω i j) (fun ω => rx ω j'))
      ∧ (∀ i j i' j', (i, j) ≠ (i', j') →
          UncorrelatedPacketJitter P (fun ω => own ω i j) (fun ω => own ω i' j'))
      ∧ (∀ h i, UncorrelatedPhaseJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => tx ω i))
      ∧ (∀ h j, UncorrelatedPhaseJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => rx ω j))
      ∧ (∀ h i j, UncorrelatedPhasePacketJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => own ω i j))
      ∧ (∀ i, UncorrelatedGridJitter P (fun ω => devicePhase (world ω).source.capture m.rate)
          (fun ω => tx ω i))
      ∧ (∀ j, UncorrelatedGridJitter P (fun ω => devicePhase (world ω).source.capture m.rate)
          (fun ω => rx ω j))
      ∧ (∀ i j, UncorrelatedGridPacketJitter P (fun ω => devicePhase (world ω).source.capture m.rate)
          (fun ω => own ω i j))
      ∧ (∀ r i, UncorrelatedGridJitter P (fun ω => devicePhase ((world ω).speaker r).out m.rate)
          (fun ω => tx ω i))
      ∧ (∀ r j, UncorrelatedGridJitter P (fun ω => devicePhase ((world ω).speaker r).out m.rate)
          (fun ω => rx ω j))
      ∧ (∀ r i j, UncorrelatedGridPacketJitter P (fun ω => devicePhase ((world ω).speaker r).out m.rate)
          (fun ω => own ω i j))
      ∧ (∀ i, UncorrelatedJitterError P (fun ω => tx ω i) (fun ω => captureError (world ω)))
      ∧ (∀ j, UncorrelatedJitterError P (fun ω => rx ω j) (fun ω => captureError (world ω)))
      ∧ (∀ i j, UncorrelatedPacketJitterError P (fun ω => own ω i j) (fun ω => captureError (world ω)))
      ∧ (∀ r i, UncorrelatedJitterError P (fun ω => tx ω i) (fun ω => playbackError (world ω) r))
      ∧ (∀ r j, UncorrelatedJitterError P (fun ω => rx ω j) (fun ω => playbackError (world ω) r))
      ∧ (∀ r i j, UncorrelatedPacketJitterError P (fun ω => own ω i j)
          (fun ω => playbackError (world ω) r))
  /-- The capture device oscillator follows its power-law noise against true time. -/
  capture : FollowsNoiseOnGrid P
    (fun ω => devicePhase (world ω).source.capture m.rate)
    m.rate m.capture
  /-- Each playback device oscillator follows its power-law noise against true time. -/
  playback : ∀ r, FollowsNoiseOnGrid P
    (fun ω => devicePhase ((world ω).speaker r).out m.rate)
    m.rate (m.playback r)
  /-- Each device oscillator is uncorrelated with clocks and devices on *other*
  hosts, while remaining free to correlate with its own host's clock and with
  co-located devices on the same host. -/
  capture_clock_uncorrelated : ∀ i, i ≠ m.sender →
    UncorrelatedGrid P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω => devicePhase (world ω).source.capture m.rate)
  playback_clock_uncorrelated : ∀ i r, i ≠ m.host r →
    UncorrelatedGrid P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω => devicePhase ((world ω).speaker r).out m.rate)
  capture_playback_uncorrelated : ∀ r, m.sender ≠ m.host r →
    UncorrelatedGrids P
      (fun ω => devicePhase (world ω).source.capture m.rate)
      (fun ω => devicePhase ((world ω).speaker r).out m.rate)
  playback_uncorrelated : ∀ r r', m.host r ≠ m.host r' →
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
