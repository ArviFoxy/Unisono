/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeLongRun
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# From bounds at horizons to the mean of the long-run cost

The cost of a playback is the limit superior, over the horizon, of the cost
accrued per second. A lower bound on the mean cost therefore needs a limit
under the mean. This file takes that limit without asking that the cost, or
anything accrued, is a measurable function of the outcome.

* `limsup_lintegral_le_of_bounded`: for functions that are bounded by one
  number, the limit superior of the means is at most the mean of any
  function that is at least their limit superior in almost every outcome.
  The means are lower integrals, and each function is replaced by a
  measurable function below it with the same mean.
* `limsup_le_longRun`: the long-run average is at least the limit superior
  along any sequence of horizons that grows without bound.
* `limsup_le_lintegral_cost`: if a quantity `A n` of the outcome is bounded
  by a multiple of the horizon `T n`, has a mean of at least `V n`, and is at
  most the weighted latency, missed samples and discontinuities accrued
  until `T n` plus a number `loss n`, then the limit superior of
  `(V n - loss n) / T n` is at most the mean cost.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory Filter
open scoped ENNReal

/-- **The limit superior of the means of bounded functions.** Let the
functions `h n` be at most a finite number `M` everywhere, on a space of
finite measure, and let `cost` be at least their limit superior in almost
every point. Then the limit superior of the means of the `h n` is at most
the mean of `cost`. Nothing is assumed measurable. -/
theorem limsup_lintegral_le_of_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {h : ℕ → α → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbound : ∀ n a, h n a ≤ M) {cost : α → ℝ≥0∞}
    (hcost : ∀ᵐ a ∂μ, limsup (fun n => h n a) atTop ≤ cost a) :
    limsup (fun n => ∫⁻ a, h n a ∂μ) atTop ≤ ∫⁻ a, cost a ∂μ := by
  choose φ hφm hφle hφeq using fun n => exists_measurable_le_lintegral_eq (μ := μ) (h n)
  have h1 : (fun n => ∫⁻ a, h n a ∂μ) = fun n => ∫⁻ a, φ n a ∂μ := funext hφeq
  rw [h1]
  refine (limsup_lintegral_le (fun _ => M) hφm
    (fun n => Eventually.of_forall fun a => (hφle n a).trans (hbound n a)) ?_).trans ?_
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top hM (measure_ne_top μ _)
  · refine lintegral_mono_ae ?_
    filter_upwards [hcost] with a ha
    exact (limsup_le_limsup (Eventually.of_forall fun n => hφle n a)).trans ha

/-- **The long-run average is at least the limit superior along any sequence
of horizons** that grows without bound. -/
theorem limsup_le_longRun (G : Time → ℝ≥0∞) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    limsup (fun n => G (T n) / ENNReal.ofReal (T n)) atTop ≤ longRun G := by
  unfold longRun
  exact limsup_le_limsup_of_le (u := fun t : Time => G t / ENNReal.ofReal t) hT

variable {H : Type} {R : ℕ}

/-- **From bounds at horizons to the mean cost.** Take a random world
`w ω` with what is played in it, on a probability space, and horizons `T n`
that are positive and grow without bound. Let `A n` be a quantity of the
outcome that is at most a finite number `M` times `T n`, whose mean is at
least `V n`, and that in almost every outcome is at most the weighted
latency, missed samples and discontinuities accrued until `T n`, plus a
number `loss n`. Then the limit superior of `(V n - loss n) / T n` is at
most the mean cost. Nothing is assumed measurable. -/
theorem limsup_le_lintegral_cost {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (w : Ω → World H R) (plays : Ω → Fin R → ℕ → Option ℝ)
    (c : Weights) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) (hTpos : ∀ n, 0 < T n)
    {A : ℕ → Ω → ℝ≥0∞} {loss V : ℕ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbound : ∀ n ω, A n ω ≤ M * ENNReal.ofReal (T n))
    (hmean : ∀ n, V n ≤ ∫⁻ ω, A n ω ∂P)
    (hpath : ∀ᵐ ω ∂P, ∀ n, A n ω
      ≤ (c.latency : ℝ≥0∞) * (w ω).accruedFrames ((w ω).latencyCost (plays ω)) (T n)
        + (c.missed : ℝ≥0∞)
          * (w ω).accruedOutputs (fun r k => (missedAt (plays ω r) k : ℝ≥0∞)) (T n)
        + (c.discontinuities : ℝ≥0∞)
          * (w ω).accruedOutputs (fun r k => (discontinuityAt (plays ω r) k : ℝ≥0∞)) (T n)
        + loss n) :
    limsup (fun n => (V n - loss n) / ENNReal.ofReal (T n)) atTop
      ≤ ∫⁻ ω, (w ω).cost (plays ω) c ∂P := by
  have hTne : ∀ n, ENNReal.ofReal (T n) ≠ 0 := fun n => (ENNReal.ofReal_pos.mpr (hTpos n)).ne'
  have hTtop : ∀ n, ENNReal.ofReal (T n) ≠ ⊤ := fun n => ENNReal.ofReal_ne_top
  have hb : ∀ n ω, (A n ω - loss n) / ENNReal.ofReal (T n) ≤ M := fun n ω =>
    (ENNReal.div_le_iff (hTne n) (hTtop n)).mpr (tsub_le_self.trans (hbound n ω))
  have hcost : ∀ᵐ ω ∂P, limsup (fun n => (A n ω - loss n) / ENNReal.ofReal (T n)) atTop
      ≤ (w ω).cost (plays ω) c := by
    filter_upwards [hpath] with ω hω
    have h1 : ∀ n, (A n ω - loss n) / ENNReal.ofReal (T n)
        ≤ ((c.latency : ℝ≥0∞) * (w ω).accruedFrames ((w ω).latencyCost (plays ω)) (T n)
          + (c.missed : ℝ≥0∞)
            * (w ω).accruedOutputs (fun r k => (missedAt (plays ω r) k : ℝ≥0∞)) (T n)
          + (c.discontinuities : ℝ≥0∞)
            * (w ω).accruedOutputs (fun r k => (discontinuityAt (plays ω r) k : ℝ≥0∞)) (T n))
          / ENNReal.ofReal (T n) := fun n =>
      ENNReal.div_le_div_right (tsub_le_iff_right.mpr (hω n)) _
    refine (limsup_le_limsup (Eventually.of_forall h1)).trans ?_
    refine (limsup_le_longRun (fun t =>
      (c.latency : ℝ≥0∞) * (w ω).accruedFrames ((w ω).latencyCost (plays ω)) t
        + (c.missed : ℝ≥0∞)
          * (w ω).accruedOutputs (fun r k => (missedAt (plays ω r) k : ℝ≥0∞)) t
        + (c.discontinuities : ℝ≥0∞)
          * (w ω).accruedOutputs (fun r k => (discontinuityAt (plays ω r) k : ℝ≥0∞)) t)
      hT).trans ?_
    exact (w ω).longRun_le_cost_of_latency_missed (plays ω) c (T₀ := 0) fun t _ => le_rfl
  refine le_trans (limsup_le_limsup (Eventually.of_forall fun n => ?_))
    (limsup_lintegral_le_of_bounded (μ := P) hM hb hcost)
  have hsub : ∫⁻ ω, A n ω ∂P - loss n ≤ ∫⁻ ω, (A n ω - loss n) ∂P := by
    have h2 := lintegral_sub_le (μ := P) (fun _ => loss n) (A n) measurable_const
    rw [lintegral_const, measure_univ, mul_one] at h2
    exact h2
  calc (V n - loss n) / ENNReal.ofReal (T n)
      ≤ (∫⁻ ω, A n ω ∂P - loss n) / ENNReal.ofReal (T n) :=
        ENNReal.div_le_div_right (tsub_le_tsub_right (hmean n) _) _
    _ ≤ (∫⁻ ω, (A n ω - loss n) ∂P) / ENNReal.ofReal (T n) :=
        ENNReal.div_le_div_right hsub _
    _ ≤ ∫⁻ ω, (A n ω - loss n) / ENNReal.ofReal (T n) ∂P := by
        simp only [div_eq_mul_inv]
        exact lintegral_mul_const_le _ _

end Unisono.Spec
