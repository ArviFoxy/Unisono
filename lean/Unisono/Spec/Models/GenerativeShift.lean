/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GaussianLaw
public import Unisono.Spec.Models.GenerativeDrawLaw
public import Unisono.Spec.Models.ErgodicMean
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The law of what is drawn does not change when time is shifted

In the generative model the wander of every clock and the error of every
device's timestamps are stationary, and the pauses of every link and host
begin at the instants of a Poisson process. So what is drawn looks the same
from every true time, apart from the readings of the clocks, which grow.

`Component.shift ℓ p` reads the value of the component `p` of a draw from
the true time `ℓ` on: a number stays as it is; the wander of a clock and the
error of timestamps are read `ℓ` later; the paused time of a link or a host
is counted from `ℓ`.

* `Prior.map_component_shift`: **every component has the same law after the
  shift.** For the wander and the errors this holds because a Gaussian
  process has one law for given means and covariances
  (`map_eq_of_isGaussianProcess`), and the covariance of the model depends
  only on the time between two instants. For the paused times it holds
  because a process with independent increments has one law for given laws
  of its increments (`HasIncrementLaws.map_path_eq`), and the law of the
  paused time that begins in a period depends only on the length of the
  period.
* `Prior.map_components_shift`: **all components together have the same law
  after the shift**, because they are independent. This is stated for the
  family of the components of the draw, for hosts that can be counted.
* `Prior.lintegral_limsup_shift`: **the mean of a long-run average.** For a
  measurable quantity `Γ` of the components, with values from zero to
  infinity: take the value of `Γ` on the components as read from the true
  times `0`, `ℓ`, `2 ℓ` and so on, and the limit superior of the averages
  of the first `n` of these values. Its mean is at most the mean of `Γ`
  (`lintegral_limsup_average_le`, the maximal ergodic theorem). No
  ergodicity is needed, and `Γ` need not be bounded.

The offsets of the clocks are components too and stay as they are under
`Component.shift`. So the shifted family is not the family of the world seen
`ℓ` later, whose clocks read more. A quantity that does not depend on the
offsets has the same value on both, and it is to such quantities that the
statement is applied.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {H : Type} {R : ℕ}

/-- The value of the component `p` of a draw, read from the true time `ℓ`
on: a number stays as it is; the wander of a clock and the error of
timestamps are read `ℓ` later; the paused time of a link or a host is
counted from `ℓ`. -/
def Component.shift (ℓ : ℝ) : (p : Component H R) → p.Val → p.Val
  | .split _ => fun x => x
  | .offset _ => fun x => x
  | .logRate _ => fun x => x
  | .wander _ => fun (x : Time → ℝ) (t : Time) => x (t + ℓ)
  | .linkPaused _ _ => fun (x : Time → ℝ) (t : Time) => x (t + ℓ) - x ℓ
  | .hostPaused _ => fun (x : Time → ℝ) (t : Time) => x (t + ℓ) - x ℓ
  | .deviceLogRate _ => fun x => x
  | .deviceWander _ => fun (x : Time → ℝ) (t : Time) => x (t + ℓ)
  | .reportError _ => fun (x : Time → ℝ) (t : Time) => x (t + ℓ)

/-- Reading a path later is measurable. -/
theorem measurable_path_shift (ℓ : ℝ) :
    Measurable fun (x : Time → ℝ) (t : Time) => x (t + ℓ) :=
  measurable_pi_iff.mpr fun t => measurable_pi_apply (t + ℓ)

/-- Counting a path from a later time is measurable. -/
theorem measurable_path_shift_sub (ℓ : ℝ) :
    Measurable fun (x : Time → ℝ) (t : Time) => x (t + ℓ) - x ℓ :=
  measurable_pi_iff.mpr fun t => (measurable_pi_apply (t + ℓ)).sub (measurable_pi_apply ℓ)

/-- The shift of every component is measurable. -/
theorem measurable_component_shift (ℓ : ℝ) (p : Component H R) :
    Measurable (Component.shift ℓ p) := by
  cases p with
  | split z => exact measurable_id
  | offset h => exact measurable_id
  | logRate h => exact measurable_id
  | wander h => exact measurable_path_shift ℓ
  | linkPaused i j => exact measurable_path_shift_sub ℓ
  | hostPaused h => exact measurable_path_shift_sub ℓ
  | deviceLogRate x => exact measurable_id
  | deviceWander x => exact measurable_path_shift ℓ
  | reportError x => exact measurable_path_shift ℓ

variable {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R} {f : Member H R}
  {P : Measure Ω} {D : Ω → Draw H R}

/-- **A stationary Gaussian path has the same law when it is read later.**
Let `W` be a real Gaussian process with continuous paths whose values have
one mean and whose covariance at two times depends only on the time between
them. Then the path read `ℓ` later has the law of the path. -/
theorem map_shift_of_isGaussianProcess {W : Time → Ω → ℝ} (hW : IsGaussianProcess W P)
    (hcont : ∀ ω, Continuous fun t => W t ω) {μ₀ : ℝ} (hmean : ∀ t, ∫ ω, W t ω ∂P = μ₀)
    {c : ℝ → ℝ} (hcov : ∀ s t, cov[W s, W t; P] = c (s - t)) (ℓ : ℝ) :
    P.map (fun ω (t : Time) => W (t + ℓ) ω) = P.map (fun ω (t : Time) => W t ω) := by
  have hWs : IsGaussianProcess (fun (t : Time) ω => W (t + ℓ) ω) P :=
    hW.comp_right fun t => t + ℓ
  refine map_eq_of_isGaussianProcess hWs hW ?_ ?_ (fun t => ?_) fun s t => ?_
  · exact aemeasurable_path (fun t => hW.aemeasurable (t + ℓ)) fun ω t =>
      ((hcont ω).comp (continuous_id.add continuous_const)).continuousWithinAt
  · exact aemeasurable_path (fun t => hW.aemeasurable t) fun ω t =>
      (hcont ω).continuousWithinAt
  · rw [hmean, hmean]
  · rw [hcov, hcov]
    congr 1
    ring

/-- **A path with independent increments whose laws depend only on the
length of the period has the same law when it is counted from a later
time.** -/
theorem map_shift_of_hasIncrementLaws {L : ℝ → ℝ → Measure ℝ} {X : ℝ → Ω → ℝ}
    [IsProbabilityMeasure P] (hX : HasIncrementLaws L X P)
    (hright : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) (ℓ : ℝ)
    (hL : ∀ s t, L (s + ℓ) (t + ℓ) = L s t) :
    P.map (fun ω (t : ℝ) => X (t + ℓ) ω - X ℓ ω) = P.map (fun ω (t : ℝ) => X t ω) := by
  have hY : HasIncrementLaws L (fun t ω => X (t + ℓ) ω - X ℓ ω) P := by
    refine ⟨fun ω => ?_, ?_, fun s t hst => ?_⟩
    · show X (0 + ℓ) ω - X ℓ ω = 0
      rw [zero_add, sub_self]
    · intro n t ht
      have h1 := hX.indep n (fun i => t i + ℓ) fun i j hij => by
        have := ht hij
        linarith
      have h2 : (fun (i : Fin n) ω => (X (t i.succ + ℓ) ω - X ℓ ω)
            - (X (t i.castSucc + ℓ) ω - X ℓ ω))
          = fun (i : Fin n) ω => X (t i.succ + ℓ) ω - X (t i.castSucc + ℓ) ω := by
        funext i ω
        ring
      rw [h2]
      exact h1
    · have h1 := hX.law (s + ℓ) (t + ℓ) (by linarith)
      rw [hL s t] at h1
      have h2 : (fun ω => (X (t + ℓ) ω - X ℓ ω) - (X (s + ℓ) ω - X ℓ ω))
          = fun ω => X (t + ℓ) ω - X (s + ℓ) ω := by
        funext ω
        ring
      rw [h2]
      exact h1
  refine hY.map_path_eq hX ?_ ?_
  · refine aemeasurable_path (fun t => hY.aemeasurable t) fun ω t => ?_
    have h1 : ContinuousWithinAt (fun s => X (s + ℓ) ω) (Set.Ici t) t := by
      have h2 := hright ω (t + ℓ)
      refine ContinuousWithinAt.comp (g := fun s => X s ω) (f := fun s => s + ℓ)
        (t := Set.Ici (t + ℓ)) h2 ?_ ?_
      · exact (continuous_id.add continuous_const).continuousWithinAt
      · intro s hs
        exact add_le_add_left (Set.mem_Ici.mp hs) ℓ
    exact h1.sub continuousWithinAt_const
  · exact aemeasurable_path (fun t => hX.aemeasurable t) hright

/-- **Every component of the draw of a random world has the same law after
the shift.** -/
theorem Prior.map_component_shift (hD : m.Prior f P D) (o : Orientation H) (ℓ : ℝ)
    (p : Component H R) :
    P.map (fun ω => Component.shift ℓ p ((D ω).component o p))
      = P.map (fun ω => (D ω).component o p) := by
  have hprob := hD.prob
  cases p with
  | split z => rfl
  | offset h => rfl
  | logRate h => rfl
  | deviceLogRate x => rfl
  | wander h =>
    exact map_shift_of_isGaussianProcess (hD.wander_gaussian h)
      (fun ω => hD.wander_continuous ω h) (hD.wander_mean h)
      (c := fun x => f.wanderSize h ^ 2 * Real.exp (-|x| / f.wanderTime h))
      (hD.wander_covariance h) ℓ
  | deviceWander x =>
    exact map_shift_of_isGaussianProcess (hD.deviceWander_gaussian x)
      (fun ω => hD.deviceWander_continuous ω x) (hD.deviceWander_mean x)
      (c := fun y => f.deviceWanderSize x ^ 2 * Real.exp (-|y| / f.deviceWanderTime x))
      (hD.deviceWander_covariance x) ℓ
  | reportError x =>
    exact map_shift_of_isGaussianProcess (hD.reportError_gaussian x)
      (fun ω => hD.reportError_continuous ω x) (hD.reportError_mean x)
      (c := fun y => f.reportSize x ^ 2 * Real.exp (-|y| / f.reportTime x))
      (hD.reportError_covariance x) ℓ
  | linkPaused i j =>
    have h1 := hD.hasIncrementLaws_paused (.inl (i, j))
    refine map_shift_of_hasIncrementLaws h1
      (fun ω t => hD.linkPaused_rightContinuous ω i j t) ℓ fun s t => ?_
    unfold Member.pauseIncrementLaw
    congr 3
    ring
  | hostPaused h =>
    have h1 := hD.hasIncrementLaws_paused (.inr h)
    refine map_shift_of_hasIncrementLaws h1
      (fun ω t => hD.hostPaused_rightContinuous ω h t) ℓ fun s t => ?_
    unfold Member.pauseIncrementLaw
    congr 3
    ring

/-- **All components of the draw of a random world together have the same
law after the shift.** -/
theorem Prior.map_components_shift [Countable H] (hD : m.Prior f P D) (o : Orientation H)
    (ℓ : ℝ) :
    P.map (fun ω (p : Component H R) => Component.shift ℓ p ((D ω).component o p))
      = P.map (fun ω (p : Component H R) => (D ω).component o p) := by
  have hprob := hD.prob
  have hmeas : AEMeasurable (fun ω (p : Component H R) => (D ω).component o p) P :=
    (measurable_pi_iff.mpr fun p => measurable_component o p).comp_aemeasurable hD.aemeasurable
  have hshift : Measurable fun (x : (p : Component H R) → p.Val) (p : Component H R) =>
      Component.shift ℓ p (x p) :=
    measurable_pi_iff.mpr fun p => (measurable_component_shift ℓ p).comp (measurable_pi_apply p)
  have hlaw := (hD.independent o).map_fun_eq_infinitePi_map₀ hmeas
  have hprobs : ∀ p : Component H R,
      IsProbabilityMeasure (P.map fun ω => (D ω).component o p) :=
    fun p => (Measure.isProbabilityMeasure_map_iff (hmeas.eval p)).mpr hprob
  have hcomp : (fun ω (p : Component H R) => Component.shift ℓ p ((D ω).component o p))
      = (fun (x : (p : Component H R) → p.Val) (p : Component H R) =>
          Component.shift ℓ p (x p)) ∘ fun ω (p : Component H R) => (D ω).component o p := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hshift.aemeasurable hmeas, hlaw,
    Measure.infinitePi_map_pi _ (fun p => measurable_component_shift ℓ p)]
  congr 1
  funext p
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_component_shift ℓ p).aemeasurable
    (hmeas.eval p)]
  exact hD.map_component_shift o ℓ p

/-- All components of a draw, read from the true time `ℓ` on
(`Component.shift`). -/
def shiftComponents (ℓ : ℝ) (x : (p : Component H R) → p.Val) : (p : Component H R) → p.Val :=
  fun p => Component.shift ℓ p (x p)

/-- Reading all components from a later time is measurable. -/
theorem measurable_shiftComponents (ℓ : ℝ) :
    Measurable (shiftComponents (H := H) (R := R) ℓ) :=
  measurable_pi_iff.mpr fun p => (measurable_component_shift ℓ p).comp (measurable_pi_apply p)

/-- **The mean of a long-run average of a quantity of what is drawn, seen
from successive times.** In a random world of the model, for hosts that can
be counted, let `Γ` be a measurable quantity of the components of the draw,
with values from zero to infinity. Take the value of `Γ` on the components
read from the true times `0`, `ℓ`, `2 ℓ`, and so on. The mean of the limit
superior of the averages of the first `n` of these values is at most the
mean of `Γ` on the components of the draw. -/
theorem Prior.lintegral_limsup_shift [Countable H] (hD : m.Prior f P D) (o : Orientation H)
    (ℓ : ℝ) {Γ : ((p : Component H R) → p.Val) → ℝ≥0∞} (hΓ : Measurable Γ) :
    ∫⁻ ω, limsup (fun n : ℕ =>
        (∑ i ∈ Finset.range n, Γ ((shiftComponents ℓ)^[i] ((D ω).component o))) / n) atTop ∂P
      ≤ ∫⁻ ω, Γ ((D ω).component o) ∂P := by
  have hprob := hD.prob
  have hmeas : AEMeasurable (fun ω => (D ω).component o) P :=
    (measurable_pi_iff.mpr fun p => measurable_component o p).comp_aemeasurable hD.aemeasurable
  have hμ : IsProbabilityMeasure (P.map fun ω => (D ω).component o) :=
    (Measure.isProbabilityMeasure_map_iff hmeas).mpr hprob
  have hT : MeasurePreserving (shiftComponents (H := H) (R := R) ℓ)
      (P.map fun ω => (D ω).component o) (P.map fun ω => (D ω).component o) := by
    refine ⟨measurable_shiftComponents ℓ, ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable (measurable_shiftComponents ℓ).aemeasurable hmeas]
    exact hD.map_components_shift o ℓ
  have hmain := lintegral_limsup_average_le hT hΓ
  have hF : Measurable fun x : (p : Component H R) → p.Val =>
      limsup (fun n : ℕ => (∑ i ∈ Finset.range n, Γ ((shiftComponents ℓ)^[i] x)) / n) atTop :=
    Measurable.limsup fun n => (Finset.measurable_sum _ fun i _ =>
      hΓ.comp ((measurable_shiftComponents ℓ).iterate i)).div_const _
  rw [lintegral_map' hF.aemeasurable hmeas, lintegral_map' hΓ.aemeasurable hmeas] at hmain
  exact hmain

end Unisono.Spec.GenerativeWorld
