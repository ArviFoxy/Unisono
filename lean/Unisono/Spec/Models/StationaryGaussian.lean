/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ContinuousModification
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# A stationary Gaussian process with exponential covariance and continuous paths

`exists_stationary_gaussian`: for a size `σ` and a time `τ > 0` there are a
probability measure and a real process on it, indexed by the real numbers,
such that the process is Gaussian with mean zero, the covariance of its
values at the times `s` and `t` is `σ ^ 2 * exp (-|s - t| / τ)`, it is
measurable at every time, and every one of its paths is continuous. This is
the Ornstein–Uhlenbeck process in its stationary law. The generative model
takes it for each part of the wander of a clock and for the error of the
reports of an audio device.

`stationaryLaw σ τ` and `stationaryPath σ τ` name one such law and the path
of each outcome. A random outcome with that law, on any probability space,
gives a process with the same properties (the theorems ending in `_comp`).

The construction:

* A process with the finite-dimensional laws of Brownian motion exists
  (`exists_isPreBrownianReal`), by the extension theorem of Kolmogorov.
* Read at the time `exp (2 * t / τ)` and multiplied by `σ * exp (-t / τ)`
  it is Gaussian with mean zero and the covariance above
  (`scaledBrownian`, `covariance_scaledBrownian`).
* The variance of its increment over a stretch of length `ℓ` is at most
  `2 * σ ^ 2 / τ * ℓ`, and the fourth moment of a Gaussian quantity with
  mean zero is at most 96 times the square of its variance
  (`lintegral_pow_four_le_of_hasGaussianLaw`), so it has a modification with
  continuous paths (`exists_continuous_of_isGaussianProcess`,
  `Unisono.Spec.continuousModification`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A fourth power is at most a multiple of two exponentials. -/
theorem pow_four_le_exp (x : ℝ) {s : ℝ} (hs : 0 < s) :
    x ^ 4 ≤ 24 * s ^ 4 * (Real.exp (x / s) + Real.exp (-(x / s))) := by
  have hu0 : 0 ≤ |x / s| := abs_nonneg _
  have h1 : |x / s| ^ 4 / 24 ≤ Real.exp |x / s| := by
    have h := Real.sum_le_exp_of_nonneg hu0 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    have h2 : 0 ≤ |x / s| ^ 3 := by positivity
    have h3 : 0 ≤ (x / s) ^ 2 := by positivity
    norm_num at h
    linarith
  have h2 : Real.exp |x / s| ≤ Real.exp (x / s) + Real.exp (-(x / s)) := by
    rcases abs_cases (x / s) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      linarith [Real.exp_pos (-(x / s))]
    · rw [h]
      linarith [Real.exp_pos (x / s)]
  have h3 : x ^ 4 = s ^ 4 * |x / s| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity), div_pow]
    field_simp
  rw [h3]
  have hs4 : 0 < s ^ 4 := by positivity
  nlinarith

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  nlinarith [Real.exp_pos (1 / 2)]

/-- **The fourth moment of a Gaussian law with mean zero** is at most 96 times
the square of its variance. -/
theorem lintegral_pow_four_gaussianReal_le (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 v) ≤ ENNReal.ofReal (96 * (v : ℝ) ^ 2) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  · have hv0 : (0 : ℝ) < v := by positivity
    have hs0 : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
    have hs2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0.le
    have hint1 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) (1 / Real.sqrt v)
    have hint2 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-(1 / Real.sqrt v))
    have hle : ∀ x : ℝ, x ^ 4 ≤ 24 * Real.sqrt v ^ 4
        * (Real.exp (1 / Real.sqrt v * x) + Real.exp (-(1 / Real.sqrt v) * x)) := by
      intro x
      have := pow_four_le_exp x hs0
      have e1 : 1 / Real.sqrt v * x = x / Real.sqrt v := by ring
      have e2 : -(1 / Real.sqrt v) * x = -(x / Real.sqrt v) := by ring
      rw [e1, e2]
      exact this
    have hm : ∀ a : ℝ, a ^ 2 = 1 / v →
        ∫ x, Real.exp (a * x) ∂(gaussianReal 0 v) = Real.exp (1 / 2) := by
      intro a ha
      have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) a
      simp only [mgf, id] at h
      rw [h, ha]
      congr 1
      field_simp
      ring
    have h4 : Real.sqrt v ^ 4 = (v : ℝ) ^ 2 := by
      calc Real.sqrt v ^ 4 = (Real.sqrt v ^ 2) ^ 2 := by ring
        _ = (v : ℝ) ^ 2 := by rw [hs2]
    calc ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(gaussianReal 0 v)
        ≤ ∫⁻ x, ENNReal.ofReal (24 * Real.sqrt v ^ 4
            * (Real.exp (1 / Real.sqrt v * x) + Real.exp (-(1 / Real.sqrt v) * x)))
            ∂(gaussianReal 0 v) := lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
      _ = ENNReal.ofReal (∫ x, 24 * Real.sqrt v ^ 4
            * (Real.exp (1 / Real.sqrt v * x) + Real.exp (-(1 / Real.sqrt v) * x))
            ∂(gaussianReal 0 v)) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (hint1.add hint2).const_mul _
          · exact Eventually.of_forall fun x => by positivity
      _ = ENNReal.ofReal (24 * (v : ℝ) ^ 2 * (2 * Real.exp (1 / 2))) := by
          congr 1
          rw [integral_const_mul, integral_add hint1 hint2,
            hm (1 / Real.sqrt v) (by rw [div_pow, hs2]; norm_num),
            hm (-(1 / Real.sqrt v)) (by rw [neg_sq, div_pow, hs2]; norm_num), h4]
          ring
      _ ≤ ENNReal.ofReal (96 * (v : ℝ) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := exp_half_le_two
          have hv2 : (0 : ℝ) ≤ (v : ℝ) ^ 2 := by positivity
          nlinarith

/-- **The fourth moment of a Gaussian quantity with mean zero** is at most 96
times the square of its variance. -/
theorem lintegral_pow_four_le_of_hasGaussianLaw {X : Ω → ℝ} (hX : HasGaussianLaw X P)
    (hmean : ∫ ω, X ω ∂P = 0) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ 4) ∂P ≤ ENNReal.ofReal (96 * Var[X; P] ^ 2) := by
  have hmap := hX.map_eq_gaussianReal
  rw [hmean] at hmap
  have h1 : ∫⁻ ω, ENNReal.ofReal (X ω ^ 4) ∂P = ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(P.map X) := by
    rw [lintegral_map' (by fun_prop) hX.aemeasurable]
  rw [h1, hmap]
  refine (lintegral_pow_four_gaussianReal_le _).trans (le_of_eq ?_)
  rw [Real.coe_toNNReal _ (variance_nonneg _ _)]

/-- Two pairs of quantities that are almost surely equal have the same
covariance. -/
theorem covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    cov[X, Y; P] = cov[X', Y'; P] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

/-- **A Gaussian process with mean zero whose increments have a variance of
at most a multiple of the time between them has a modification with
continuous paths.** -/
theorem exists_continuous_of_isGaussianProcess [IsProbabilityMeasure P] {Y : ℝ → Ω → ℝ}
    (hY : IsGaussianProcess Y P) (hm : ∀ t, Measurable (Y t))
    (hmean : ∀ t, ∫ ω, Y t ω ∂P = 0) {c : ℝ}
    (hvar : ∀ s t, Var[fun ω => Y t ω - Y s ω; P] ≤ c * |t - s|) :
    ∃ X : ℝ → Ω → ℝ, (∀ t, Measurable (X t)) ∧ (∀ t, X t =ᵐ[P] Y t)
      ∧ ∀ ω, Continuous fun t => X t ω := by
  have hmom : ∀ s t, ∫⁻ ω, ENNReal.ofReal ((Y t ω - Y s ω) ^ 4) ∂P
      ≤ ENNReal.ofReal (96 * c ^ 2 * (t - s) ^ 2) := by
    intro s t
    have hg : HasGaussianLaw (fun ω => Y t ω - Y s ω) P := hY.hasGaussianLaw_fun_sub
    have hint : ∀ u, Integrable (Y u) P := fun u => (hY.hasGaussianLaw_eval u).integrable
    have hmean' : ∫ ω, (Y t ω - Y s ω) ∂P = 0 := by
      rw [integral_sub (hint t) (hint s), hmean, hmean, sub_zero]
    refine (lintegral_pow_four_le_of_hasGaussianLaw hg hmean').trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ Var[fun ω => Y t ω - Y s ω; P] := variance_nonneg _ _
    have h1 := hvar s t
    have h2 : Var[fun ω => Y t ω - Y s ω; P] ^ 2 ≤ (c * |t - s|) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have h3 : (c * |t - s|) ^ 2 = c ^ 2 * (t - s) ^ 2 := by
      rw [mul_pow, sq_abs]
    linarith
  refine ⟨continuousModification Y, measurable_continuousModification hm,
    continuousModification_ae_eq hm (by positivity) hmom, continuous_continuousModification Y⟩

/-- A process with the finite-dimensional laws of Brownian motion exists. -/
theorem exists_isPreBrownianReal :
    ∃ P : Measure (ℝ≥0 → ℝ), IsProbabilityMeasure P ∧ IsPreBrownianReal (fun t ω => ω t) P := by
  refine ⟨projectiveLimit BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily, inferInstance, ⟨fun I => ?_⟩⟩
  exact ⟨by fun_prop, isProjectiveLimit_projectiveLimit _ I⟩

/-- The time of the Brownian motion that the true time `t` reads. -/
def expTime (τ t : ℝ) : ℝ≥0 := Real.toNNReal (Real.exp (2 * t / τ))

/-- A Brownian motion read at exponentially growing times and scaled
down. -/
def scaledBrownian (σ τ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  σ * Real.exp (-t / τ) * B (expTime τ t) ω

theorem exp_mul_exp_mul_min (τ : ℝ) (hτ : 0 < τ) (s t : ℝ) :
    Real.exp (-s / τ) * Real.exp (-t / τ)
        * min (Real.exp (2 * s / τ)) (Real.exp (2 * t / τ))
      = Real.exp (-|s - t| / τ) := by
  rcases le_total s t with h | h
  · have hmin : min (Real.exp (2 * s / τ)) (Real.exp (2 * t / τ)) = Real.exp (2 * s / τ) :=
      min_eq_left (Real.exp_le_exp.mpr (by gcongr))
    rw [hmin, ← Real.exp_add, ← Real.exp_add, abs_of_nonpos (by linarith)]
    congr 1
    field_simp
    ring
  · have hmin : min (Real.exp (2 * s / τ)) (Real.exp (2 * t / τ)) = Real.exp (2 * t / τ) :=
      min_eq_right (Real.exp_le_exp.mpr (by gcongr))
    rw [hmin, ← Real.exp_add, ← Real.exp_add, abs_of_nonneg (by linarith)]
    congr 1
    field_simp
    ring

section Scaled

variable {B : ℝ≥0 → Ω → ℝ} {σ τ : ℝ}

theorem scaledBrownian_isGaussianProcess (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (scaledBrownian σ τ B) P :=
  (hB.isGaussianProcess.comp_right (expTime τ)).smul fun t => σ * Real.exp (-t / τ)

theorem integral_scaledBrownian (hB : IsPreBrownianReal B P) (t : ℝ) :
    ∫ ω, scaledBrownian σ τ B t ω ∂P = 0 := by
  unfold scaledBrownian
  rw [integral_const_mul]
  have := hB.integral_eval (expTime τ t)
  rw [this, mul_zero]

theorem covariance_scaledBrownian (hB : IsPreBrownianReal B P) (hτ : 0 < τ) (s t : ℝ) :
    cov[scaledBrownian σ τ B s, scaledBrownian σ τ B t; P]
      = σ ^ 2 * Real.exp (-|s - t| / τ) := by
  have h : cov[scaledBrownian σ τ B s, scaledBrownian σ τ B t; P]
      = σ * Real.exp (-s / τ) * (σ * Real.exp (-t / τ)
        * ((min (expTime τ s) (expTime τ t) : ℝ≥0) : ℝ)) := by
    have e1 : scaledBrownian σ τ B s
        = fun ω => σ * Real.exp (-s / τ) * B (expTime τ s) ω := rfl
    have e2 : scaledBrownian σ τ B t
        = fun ω => σ * Real.exp (-t / τ) * B (expTime τ t) ω := rfl
    rw [e1, e2, covariance_const_mul_left, covariance_const_mul_right,
      hB.covariance_fun_eval]
  rw [h, NNReal.coe_min]
  unfold expTime
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le, Real.coe_toNNReal _ (Real.exp_pos _).le,
    ← exp_mul_exp_mul_min τ hτ s t]
  ring

end Scaled

/-- **A stationary Gaussian process with mean zero, the covariance
`σ ^ 2 * exp (-|s - t| / τ)` and continuous paths exists.** -/
theorem exists_stationary_gaussian (σ τ : ℝ) (hτ : 0 < τ) :
    ∃ (P : Measure (ℝ≥0 → ℝ)) (X : ℝ → (ℝ≥0 → ℝ) → ℝ),
      IsProbabilityMeasure P ∧ (∀ t, Measurable (X t)) ∧ IsGaussianProcess X P
      ∧ (∀ t, ∫ ω, X t ω ∂P = 0)
      ∧ (∀ s t, cov[X s, X t; P] = σ ^ 2 * Real.exp (-|s - t| / τ))
      ∧ ∀ ω, Continuous fun t => X t ω := by
  obtain ⟨P, hP, hB⟩ := exists_isPreBrownianReal
  have hG : IsGaussianProcess (scaledBrownian σ τ fun t ω => ω t) P :=
    scaledBrownian_isGaussianProcess hB
  have hm : ∀ t, Measurable (scaledBrownian σ τ (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) => ω t) t) := by
    intro t
    unfold scaledBrownian
    fun_prop
  have hmean := fun t => integral_scaledBrownian (σ := σ) (τ := τ) hB t
  have hcov := fun s t => covariance_scaledBrownian (σ := σ) hB hτ s t
  have hL2 : ∀ t, MemLp (scaledBrownian σ τ (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) => ω t) t) 2 P :=
    fun t => (hG.hasGaussianLaw_eval t).memLp_two
  have hvar : ∀ s t, Var[fun ω => scaledBrownian σ τ (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) => ω t) t ω
      - scaledBrownian σ τ (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) => ω t) s ω; P]
      ≤ 2 * σ ^ 2 / τ * |t - s| := by
    intro s t
    have h := variance_sub (hL2 t) (hL2 s)
    rw [← covariance_self (hL2 t).aemeasurable, ← covariance_self (hL2 s).aemeasurable,
      hcov, hcov, hcov] at h
    have e : Var[fun ω => scaledBrownian σ τ (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) => ω t) t ω
        - scaledBrownian σ τ (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) => ω t) s ω; P]
        = 2 * σ ^ 2 * (1 - Real.exp (-|t - s| / τ)) := by
      have h' : Var[fun ω => scaledBrownian σ τ (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) => ω t) t ω
          - scaledBrownian σ τ (fun (t : ℝ≥0) (ω : ℝ≥0 → ℝ) => ω t) s ω; P]
          = σ ^ 2 * Real.exp (-|t - t| / τ) - 2 * (σ ^ 2 * Real.exp (-|t - s| / τ))
            + σ ^ 2 * Real.exp (-|s - s| / τ) := h
      rw [h']
      simp only [sub_self, abs_zero, neg_zero, zero_div, Real.exp_zero]
      ring
    rw [e]
    have hx : 1 - |t - s| / τ ≤ Real.exp (-(|t - s| / τ)) := Real.one_sub_le_exp_neg _
    have hneg : -|t - s| / τ = -(|t - s| / τ) := by ring
    rw [hneg]
    have hs2 : 0 ≤ σ ^ 2 := by positivity
    have : 2 * σ ^ 2 / τ * |t - s| = 2 * σ ^ 2 * (|t - s| / τ) := by ring
    rw [this]
    nlinarith
  obtain ⟨X, hXm, hXY, hXc⟩ := exists_continuous_of_isGaussianProcess hG hm hmean hvar
  refine ⟨P, X, hP, hXm, hG.congr fun t => (hXY t).symm, fun t => ?_, fun s t => ?_, hXc⟩
  · rw [integral_congr_ae (hXY t)]
    exact hmean t
  · rw [covariance_congr_ae (hXY s) (hXY t)]
    exact hcov s t


/-! ## A named law and path -/

/-- **The law of the outcomes from which `stationaryPath` reads its paths.**
For a time `τ` that is not positive it is a unit mass. -/
def stationaryLaw (σ τ : ℝ) : Measure (ℝ≥0 → ℝ) := by
  classical
  exact if h : 0 < τ then (exists_stationary_gaussian σ τ h).choose else Measure.dirac 0

/-- **The path of an outcome**: under `stationaryLaw σ τ` with `0 < τ`, a
stationary Gaussian process with mean zero and the covariance
`σ ^ 2 * exp (-|s - t| / τ)`. Every path is continuous. For a time `τ` that
is not positive the path is zero. -/
def stationaryPath (σ τ : ℝ) (y : ℝ≥0 → ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : 0 < τ then (exists_stationary_gaussian σ τ h).choose_spec.choose t y else 0

theorem stationaryLaw_of_pos (σ : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    stationaryLaw σ τ = (exists_stationary_gaussian σ τ hτ).choose := by
  simp [stationaryLaw, hτ]

theorem stationaryPath_of_pos (σ : ℝ) {τ : ℝ} (hτ : 0 < τ) (y : ℝ≥0 → ℝ) (t : ℝ) :
    stationaryPath σ τ y t = (exists_stationary_gaussian σ τ hτ).choose_spec.choose t y := by
  simp [stationaryPath, hτ]

instance (σ τ : ℝ) : IsProbabilityMeasure (stationaryLaw σ τ) := by
  by_cases hτ : 0 < τ
  · rw [stationaryLaw_of_pos σ hτ]
    exact (exists_stationary_gaussian σ τ hτ).choose_spec.choose_spec.1
  · simp only [stationaryLaw, hτ, dite_false]
    infer_instance

theorem measurable_stationaryPath_apply (σ τ t : ℝ) :
    Measurable fun y => stationaryPath σ τ y t := by
  by_cases hτ : 0 < τ
  · have h := (exists_stationary_gaussian σ τ hτ).choose_spec.choose_spec.2.1 t
    have e : (fun y => stationaryPath σ τ y t)
        = (exists_stationary_gaussian σ τ hτ).choose_spec.choose t := by
      funext y
      exact stationaryPath_of_pos σ hτ y t
    rw [e]
    exact h
  · have e : (fun y : ℝ≥0 → ℝ => stationaryPath σ τ y t) = fun _ => 0 := by
      funext y
      simp [stationaryPath, hτ]
    rw [e]
    exact measurable_const

/-- The path is a measurable function of the outcome. -/
theorem measurable_stationaryPath (σ τ : ℝ) : Measurable (stationaryPath σ τ) :=
  measurable_pi_iff.mpr fun t => measurable_stationaryPath_apply σ τ t

/-- **Every path is continuous.** -/
theorem continuous_stationaryPath (σ τ : ℝ) (y : ℝ≥0 → ℝ) :
    Continuous (stationaryPath σ τ y) := by
  by_cases hτ : 0 < τ
  · have h := (exists_stationary_gaussian σ τ hτ).choose_spec.choose_spec.2.2.2.2.2 y
    have e : stationaryPath σ τ y
        = fun t => (exists_stationary_gaussian σ τ hτ).choose_spec.choose t y := by
      funext t
      exact stationaryPath_of_pos σ hτ y t
    rw [e]
    exact h
  · have e : stationaryPath σ τ y = fun _ => 0 := by
      funext t
      simp [stationaryPath, hτ]
    rw [e]
    exact continuous_const

section Positive

variable (σ : ℝ) {τ : ℝ} (hτ : 0 < τ)
include hτ

theorem stationaryPath_eq :
    (fun t y => stationaryPath σ τ y t)
      = (exists_stationary_gaussian σ τ hτ).choose_spec.choose := by
  funext t y
  exact stationaryPath_of_pos σ hτ y t

theorem isGaussianProcess_stationaryPath :
    IsGaussianProcess (fun t y => stationaryPath σ τ y t) (stationaryLaw σ τ) := by
  rw [stationaryPath_eq σ hτ, stationaryLaw_of_pos σ hτ]
  exact (exists_stationary_gaussian σ τ hτ).choose_spec.choose_spec.2.2.1

theorem integral_stationaryPath (t : ℝ) :
    ∫ y, stationaryPath σ τ y t ∂(stationaryLaw σ τ) = 0 := by
  have h := (exists_stationary_gaussian σ τ hτ).choose_spec.choose_spec.2.2.2.1 t
  rw [stationaryLaw_of_pos σ hτ]
  simp_rw [stationaryPath_of_pos σ hτ]
  exact h

theorem covariance_stationaryPath (s t : ℝ) :
    cov[fun y => stationaryPath σ τ y s, fun y => stationaryPath σ τ y t; stationaryLaw σ τ]
      = σ ^ 2 * Real.exp (-|s - t| / τ) := by
  have h := (exists_stationary_gaussian σ τ hτ).choose_spec.choose_spec.2.2.2.2.1 s t
  rw [stationaryLaw_of_pos σ hτ]
  have e : ∀ u, (fun y => stationaryPath σ τ y u)
      = (exists_stationary_gaussian σ τ hτ).choose_spec.choose u := by
    intro u
    funext y
    exact stationaryPath_of_pos σ hτ y u
  rw [e s, e t]
  exact h

/-- **The mean size of the path at each time is bounded.** -/
theorem lintegral_abs_stationaryPath_le (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal |stationaryPath σ τ y t| ∂(stationaryLaw σ τ)
      ≤ ENNReal.ofReal ((1 + σ ^ 2) / 2) := by
  have hG := (isGaussianProcess_stationaryPath σ hτ).hasGaussianLaw_eval t
  have hL2 : MemLp (fun y => stationaryPath σ τ y t) 2 (stationaryLaw σ τ) := hG.memLp_two
  have hsq : Integrable (fun y => stationaryPath σ τ y t ^ 2) (stationaryLaw σ τ) :=
    hL2.integrable_sq
  have hvar : ∫ y, stationaryPath σ τ y t ^ 2 ∂(stationaryLaw σ τ) = σ ^ 2 := by
    have h1 := variance_of_integral_eq_zero hL2.aemeasurable (integral_stationaryPath σ hτ t)
    have h2 := covariance_stationaryPath σ hτ t t
    rw [covariance_self hL2.aemeasurable] at h2
    rw [← h1, h2]
    simp
  calc ∫⁻ y, ENNReal.ofReal |stationaryPath σ τ y t| ∂(stationaryLaw σ τ)
      ≤ ∫⁻ y, ENNReal.ofReal ((1 + stationaryPath σ τ y t ^ 2) / 2)
          ∂(stationaryLaw σ τ) := by
        refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
        nlinarith [sq_nonneg (|stationaryPath σ τ y t| - 1), sq_abs (stationaryPath σ τ y t)]
    _ = ENNReal.ofReal (∫ y, (1 + stationaryPath σ τ y t ^ 2) / 2 ∂(stationaryLaw σ τ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact ((integrable_const 1).add hsq).div_const 2
        · exact Eventually.of_forall fun y => by positivity
    _ = ENNReal.ofReal ((1 + σ ^ 2) / 2) := by
        congr 1
        rw [integral_div, integral_add (integrable_const 1) hsq, hvar]
        simp

end Positive


/-! ## The path of a random outcome -/

/-- A Gaussian process read through a random variable whose law is the
measure of the process is a Gaussian process. -/
theorem isGaussianProcess_comp_hasLaw {Ω' T : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {X : T → Ω' → ℝ} (hX : IsGaussianProcess X μ)
    (hXm : ∀ t, Measurable (X t)) {Z : Ω → Ω'} (hZ : HasLaw Z μ P) :
    IsGaussianProcess (fun t ω => X t (Z ω)) P where
  hasGaussianLaw I := by
    have h := (hX.hasGaussianLaw I).isGaussian_map
    have hm : Measurable fun ω' => I.restrict (X · ω') :=
      measurable_pi_iff.mpr fun i => hXm i
    refine ⟨hm.comp_aemeasurable hZ.aemeasurable, ?_⟩
    have e : P.map (fun ω => I.restrict (fun t => X t (Z ω)))
        = μ.map (fun ω' => I.restrict (X · ω')) := by
      rw [← hZ.map_eq, AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hZ.aemeasurable]
      rfl
    rw [e]
    exact h

section Comp

variable {Z : Ω → ℝ≥0 → ℝ} (σ : ℝ) {τ : ℝ} (hτ : 0 < τ) (hZ : HasLaw Z (stationaryLaw σ τ) P)
include hτ hZ

/-- **The path of a random outcome with the law `stationaryLaw` is a
Gaussian process.** -/
theorem isGaussianProcess_stationaryPath_comp :
    IsGaussianProcess (fun t ω => stationaryPath σ τ (Z ω) t) P :=
  isGaussianProcess_comp_hasLaw (isGaussianProcess_stationaryPath σ hτ)
    (fun t => measurable_stationaryPath_apply σ τ t) hZ

/-- Its mean is zero at every time. -/
theorem integral_stationaryPath_comp (t : ℝ) : ∫ ω, stationaryPath σ τ (Z ω) t ∂P = 0 := by
  have h := hZ.integral_comp (f := fun y => stationaryPath σ τ y t)
    (measurable_stationaryPath_apply σ τ t).aestronglyMeasurable
  rw [integral_stationaryPath σ hτ t] at h
  exact h

/-- Its covariance is `σ ^ 2 * exp (-|s - t| / τ)`. -/
theorem covariance_stationaryPath_comp (s t : ℝ) :
    cov[fun ω => stationaryPath σ τ (Z ω) s, fun ω => stationaryPath σ τ (Z ω) t; P]
      = σ ^ 2 * Real.exp (-|s - t| / τ) := by
  rw [hZ.covariance_fun_comp (f := fun y => stationaryPath σ τ y s)
    (g := fun y => stationaryPath σ τ y t)
    (measurable_stationaryPath_apply σ τ s).aemeasurable
    (measurable_stationaryPath_apply σ τ t).aemeasurable]
  exact covariance_stationaryPath σ hτ s t

/-- Its mean size at each time is bounded. -/
theorem lintegral_abs_stationaryPath_comp_le (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal |stationaryPath σ τ (Z ω) t| ∂P ≤ ENNReal.ofReal ((1 + σ ^ 2) / 2) := by
  rw [hZ.lintegral_comp (f := fun y => ENNReal.ofReal |stationaryPath σ τ y t|)
    (measurable_stationaryPath_apply σ τ t).abs.ennreal_ofReal.aemeasurable]
  exact lintegral_abs_stationaryPath_le σ hτ t

end Comp


end Unisono.Spec
