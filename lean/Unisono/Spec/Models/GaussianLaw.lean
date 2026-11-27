/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Pi

/-!
# The law of a real Gaussian process

**A real Gaussian process has one law for given means and covariances**
(`map_eq_of_isGaussianProcess`): two real Gaussian processes on one
probability space whose values have the same means and the same covariances
have the same law of the path, when both paths are random variables.

The values at finitely many times are a Gaussian vector, and a Gaussian
vector is determined by the mean and the variance of every linear
combination of its coordinates (`integral_variance_linear_of_isGaussianProcess`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory

variable {Ω T : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

open Classical in
/-- **The mean and the variance of a linear combination of finitely many
values of a real Gaussian process**: for a continuous linear form `L` on the
values at the times of a finite set `I`, the mean of `L` is the combination
of the means, and its variance is the combination of the covariances, with
the coefficients that `L` gives to the coordinates. -/
theorem integral_variance_linear_of_isGaussianProcess {Z : T → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (I : Finset T) (L : StrongDual ℝ (I → ℝ)) :
    (∫ x, L x ∂(P.map fun ω => I.restrict (Z · ω)))
        = ∑ i : I, L (Pi.single i 1) * ∫ ω, Z i ω ∂P
      ∧ Var[L; P.map fun ω => I.restrict (Z · ω)]
        = ∑ i : I, ∑ j : I, L (Pi.single i 1) * L (Pi.single j 1) * cov[Z i, Z j; P] := by
  have hprob := hZ.isProbabilityMeasure
  have hZI : AEMeasurable (fun ω => I.restrict (Z · ω)) P := (hZ.hasGaussianLaw I).aemeasurable
  have hL : ∀ x : I → ℝ, L x = ∑ i : I, L (Pi.single i 1) * x i := by
    intro x
    have h1 := LinearMap.pi_apply_eq_sum_univ (L : (I → ℝ) →ₗ[ℝ] ℝ) x
    have h2 : ∀ i : I, (fun j : I => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
      intro i
      funext j
      rw [Pi.single_apply]
      simp only [eq_comm]
    simp only [h2, smul_eq_mul] at h1
    rw [show L x = (L : (I → ℝ) →ₗ[ℝ] ℝ) x from rfl, h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hcomp : (fun ω => L (I.restrict (Z · ω)))
      = fun ω => ∑ i : I, L (Pi.single i 1) * Z i ω := by
    funext ω
    rw [hL]
    rfl
  have hmem : ∀ i : I, MemLp (fun ω => L (Pi.single i 1) * Z i ω) 2 P :=
    fun i => (hZ.hasGaussianLaw_eval i).memLp_two.const_mul _
  constructor
  · have hint : ∀ i ∈ (Finset.univ : Finset I),
        Integrable (fun ω => L (Pi.single i 1) * Z i ω) P :=
      fun i _ => (hZ.hasGaussianLaw_eval (i : T)).integrable.const_mul _
    rw [integral_map hZI L.continuous.aestronglyMeasurable, hcomp,
      integral_finsetSum Finset.univ hint]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · rw [variance_map L.continuous.aemeasurable hZI]
    have hfun : (L ∘ fun ω => I.restrict (Z · ω)) = fun ω => L (I.restrict (Z · ω)) := rfl
    rw [hfun, hcomp, ← covariance_self (by
      exact Finset.aemeasurable_fun_sum _ fun i _ => (hmem i).aemeasurable),
      covariance_fun_sum_fun_sum hmem hmem]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [covariance_const_mul_left, covariance_const_mul_right]
    ring

/-- **A real Gaussian process has one law for given means and covariances.**
Let `X` and `Y` be real Gaussian processes on one probability space whose
paths are random variables. If their values at every time have the same
mean, and their values at every two times have the same covariance, then
they have the same law of the path. -/
theorem map_eq_of_isGaussianProcess {X Y : T → Ω → ℝ} (hX : IsGaussianProcess X P)
    (hY : IsGaussianProcess Y P) (hXm : AEMeasurable (fun ω t => X t ω) P)
    (hYm : AEMeasurable (fun ω t => Y t ω) P)
    (hmean : ∀ t, ∫ ω, X t ω ∂P = ∫ ω, Y t ω ∂P)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; P]) :
    P.map (fun ω t => X t ω) = P.map (fun ω t => Y t ω) := by
  have hprob := hX.isProbabilityMeasure
  rw [map_eq_iff_forall_finset_map_restrict_eq hXm hYm]
  intro I
  have hGX : IsGaussian (P.map fun ω => I.restrict (X · ω)) :=
    (hX.hasGaussianLaw I).isGaussian_map
  have hGY : IsGaussian (P.map fun ω => I.restrict (Y · ω)) :=
    (hY.hasGaussianLaw I).isGaussian_map
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [IsGaussian.charFunDual_eq L, IsGaussian.charFunDual_eq L]
  obtain ⟨m1, v1⟩ := integral_variance_linear_of_isGaussianProcess hX I L
  obtain ⟨m2, v2⟩ := integral_variance_linear_of_isGaussianProcess hY I L
  rw [integral_complex_ofReal, integral_complex_ofReal, m1, m2, v1, v2]
  simp only [hmean, hcov]

end Unisono.Spec
