/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A clock whose rate wanders

`clockAdvance ρ t` is by how much a clock advances from true time zero to
true time `t` when the logarithm of its rate at each true time is `ρ`: the
integral of `exp (ρ x)`.

* For a continuous `ρ` the clock advances strictly and continuously
  (`clockAdvance_strictMono`, `continuous_clockAdvance`). If it advances
  without bound in both directions of time, it reads every value at exactly
  one true time, `clockAdvanceTime ρ c` (`clockAdvance_surjective`,
  `clockAdvance_clockAdvanceTime`, `clockAdvanceTime_clockAdvance`).
* `ae_tendsto_clockAdvance`: let the logarithm of the rate be a random
  constant plus a process with continuous paths, measurable at every time,
  whose mean size is bounded over all times. Then almost surely the clock
  advances without bound in both directions of time.

The proof of the second statement needs no ergodic theorem. The integral of
`exp (c + y)` over a stretch of length `T` is at least the integral of the
tangent line of the exponential at `-A` (`le_integral_exp`). If it is at
most `M`, the integral of `|y|` over the stretch is at least
`T * (1 + A) - M * exp (A - c)`, and by the inequality of Markov that has a
probability of at most `K * T` divided by that amount, where `K` bounds the
mean size (`measure_integral_exp_le`). For a long stretch this is about
`K / (1 + A)`, for every `A`. The integral increases with the stretch, so
the probability that it stays bounded is zero.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

/-- **By how much a clock advances** from true time zero to true time `t`,
when the logarithm of its rate at each true time is `ρ`. -/
def clockAdvance (ρ : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..t, Real.exp (ρ x)

variable {ρ : ℝ → ℝ}

theorem clockAdvance_zero (ρ : ℝ → ℝ) : clockAdvance ρ 0 = 0 := by
  simp [clockAdvance]

theorem clockAdvance_sub (hρ : Continuous ρ) (a b : ℝ) :
    clockAdvance ρ b - clockAdvance ρ a = ∫ x in a..b, Real.exp (ρ x) := by
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun x => Real.exp (ρ x)) volume u v :=
    fun u v => (Real.continuous_exp.comp hρ).intervalIntegrable u v
  unfold clockAdvance
  rw [intervalIntegral.integral_interval_sub_left (hint 0 b) (hint 0 a)]

/-- A clock with a continuous rate advances strictly. -/
theorem clockAdvance_strictMono (hρ : Continuous ρ) : StrictMono (clockAdvance ρ) := by
  intro a b hab
  have h := clockAdvance_sub hρ a b
  have hpos : 0 < ∫ x in a..b, Real.exp (ρ x) :=
    intervalIntegral.intervalIntegral_pos_of_pos
      ((Real.continuous_exp.comp hρ).intervalIntegrable a b) (fun x => Real.exp_pos _) hab
  linarith

/-- A clock with a continuous rate advances continuously. -/
theorem continuous_clockAdvance (hρ : Continuous ρ) : Continuous (clockAdvance ρ) :=
  intervalIntegral.continuous_primitive
    (fun a b => (Real.continuous_exp.comp hρ).intervalIntegrable a b) 0

/-- **A clock that advances without bound in both directions reads every
value at some true time.** -/
theorem clockAdvance_surjective (hρ : Continuous ρ) (htop : Tendsto (clockAdvance ρ) atTop atTop)
    (hbot : Tendsto (clockAdvance ρ) atBot atBot) : Function.Surjective (clockAdvance ρ) :=
  (continuous_clockAdvance hρ).surjective htop hbot

/-- **The true time at which a clock has advanced by `c`**, for a clock that
reads every value. -/
def clockAdvanceTime (ρ : ℝ → ℝ) (c : ℝ) : ℝ := by
  classical
  exact if h : ∃ t, clockAdvance ρ t = c then h.choose else 0

theorem clockAdvance_clockAdvanceTime (hsurj : Function.Surjective (clockAdvance ρ)) (c : ℝ) :
    clockAdvance ρ (clockAdvanceTime ρ c) = c := by
  classical
  have h := hsurj c
  simp only [clockAdvanceTime, h, dite_true]
  exact h.choose_spec

theorem clockAdvanceTime_clockAdvance (hρ : Continuous ρ) (t : ℝ) :
    clockAdvanceTime ρ (clockAdvance ρ t) = t := by
  classical
  have h : ∃ s, clockAdvance ρ s = clockAdvance ρ t := ⟨t, rfl⟩
  simp only [clockAdvanceTime, h, dite_true]
  exact (clockAdvance_strictMono hρ).injective h.choose_spec

theorem clockAdvanceTime_strictMono (hρ : Continuous ρ)
    (hsurj : Function.Surjective (clockAdvance ρ)) :
    StrictMono (clockAdvanceTime ρ) := by
  intro a b hab
  by_contra hcon
  have hle : clockAdvanceTime ρ b ≤ clockAdvanceTime ρ a := not_lt.mp hcon
  have := (clockAdvance_strictMono hρ).monotone hle
  rw [clockAdvance_clockAdvanceTime hsurj, clockAdvance_clockAdvanceTime hsurj] at this
  linarith


/-! ## Clocks that never stop advancing -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The integral of an exponential is at least the integral of one of its
tangent lines**: the tangent at `-A`. -/
theorem le_integral_exp {y : ℝ → ℝ} (hy : Continuous y) (c A : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (c - A) * (T * (1 + A) + ∫ x in (0 : ℝ)..T, y x)
      ≤ ∫ x in (0 : ℝ)..T, Real.exp (c + y x) := by
  have h1 : ∫ x in (0 : ℝ)..T, Real.exp (c - A) * (y x + (1 + A))
      = Real.exp (c - A) * (T * (1 + A) + ∫ x in (0 : ℝ)..T, y x) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (hy.intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [← h1]
  refine intervalIntegral.integral_mono_on hT ?_ ?_ fun x _ => ?_
  · exact (continuous_const.mul (hy.add continuous_const)).intervalIntegrable _ _
  · exact (Real.continuous_exp.comp (continuous_const.add hy)).intervalIntegrable _ _
  · have h := Real.add_one_le_exp (y x + A)
    have e : Real.exp (c + y x) = Real.exp (c - A) * Real.exp (y x + A) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

section Process

variable [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ}

/-- **The probability that the integral of the exponential stays small.** -/
theorem measure_integral_exp_le (hm : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t, ∫⁻ ω, ENNReal.ofReal |X t ω| ∂P ≤ ENNReal.ofReal K) (c M A : ℝ) {T : ℝ}
    (hT : 0 ≤ T) {a : ℝ} (ha : 0 < a) (haT : a ≤ T * (1 + A) - M * Real.exp (A - c)) :
    P {ω | ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω) ≤ M}
      ≤ ENNReal.ofReal (K * T) / ENNReal.ofReal a := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hmeas : Measurable fun p : Ω × ℝ => ENNReal.ofReal |X p.2 p.1| :=
    (hjoint.comp measurable_swap).abs.ennreal_ofReal
  have hJm : Measurable fun ω => ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal |X t ω| :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) T)) hmeas
  have hJint : ∫⁻ ω, (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal |X t ω|) ∂P
      ≤ ENNReal.ofReal (K * T) := by
    rw [lintegral_lintegral_swap
      (f := fun ω t => ENNReal.ofReal |X t ω|) hmeas.aemeasurable]
    calc ∫⁻ t in Ioc (0 : ℝ) T, (∫⁻ ω, ENNReal.ofReal |X t ω| ∂P)
        ≤ ∫⁻ _t in Ioc (0 : ℝ) T, ENNReal.ofReal K := lintegral_mono fun t => hK t
      _ = ENNReal.ofReal (K * T) := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
            Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hK0]
  have hsub : {ω | ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω) ≤ M}
      ⊆ {ω | ENNReal.ofReal a ≤ ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal |X t ω|} := by
    intro ω hω
    have hω' : ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω) ≤ M := hω
    have h1 := le_integral_exp (hc ω) c A hT
    have hpos := Real.exp_pos (c - A)
    have hinv : Real.exp (c - A) * Real.exp (A - c) = 1 := by
      rw [← Real.exp_add]
      simp
    have h2 : T * (1 + A) + ∫ x in (0 : ℝ)..T, X x ω ≤ M * Real.exp (A - c) := by
      have h3 : Real.exp (c - A) * (T * (1 + A) + ∫ x in (0 : ℝ)..T, X x ω) ≤ M :=
        h1.trans hω'
      have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (A - c)).le
      have e : Real.exp (c - A) * (T * (1 + A) + ∫ x in (0 : ℝ)..T, X x ω) * Real.exp (A - c)
          = T * (1 + A) + ∫ x in (0 : ℝ)..T, X x ω := by
        calc Real.exp (c - A) * (T * (1 + A) + ∫ x in (0 : ℝ)..T, X x ω) * Real.exp (A - c)
            = (Real.exp (c - A) * Real.exp (A - c))
              * (T * (1 + A) + ∫ x in (0 : ℝ)..T, X x ω) := by ring
          _ = T * (1 + A) + ∫ x in (0 : ℝ)..T, X x ω := by rw [hinv, one_mul]
      rw [e] at h4
      exact h4
    have h5 : a ≤ ∫ x in (0 : ℝ)..T, |X x ω| := by
      have h6 := intervalIntegral.abs_integral_le_integral_abs (f := fun x => X x ω)
        (μ := volume) hT
      have h7 := neg_abs_le (∫ x in (0 : ℝ)..T, X x ω)
      linarith
    have hint : IntegrableOn (fun x => |X x ω|) (Ioc (0 : ℝ) T) volume :=
      ((hc ω).abs.intervalIntegrable 0 T).1
    have h8 : ENNReal.ofReal (∫ x in (0 : ℝ)..T, |X x ω|)
        = ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal |X t ω| := by
      rw [intervalIntegral.integral_of_le hT, ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun x => abs_nonneg _)]
    show ENNReal.ofReal a ≤ ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal |X t ω|
    rw [← h8]
    exact ENNReal.ofReal_le_ofReal h5
  have hmarkov := mul_meas_ge_le_lintegral (μ := P) hJm (ENNReal.ofReal a)
  have ha0 : ENNReal.ofReal a ≠ 0 := by
    simpa using ha
  rw [ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  refine le_trans ?_ (hmarkov.trans hJint)
  gcongr

/-- **Almost surely the integral of the exponential of the process grows
without bound**, when the mean size of the process is bounded and its paths
are continuous. -/
theorem ae_tendsto_integral_exp_atTop (hm : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t, ∫⁻ ω, ENNReal.ofReal |X t ω| ∂P ≤ ENNReal.ofReal K) (c : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω)) atTop atTop := by
  have hbad : ∀ M : ℕ, P {ω | ∀ T : ℕ, ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω) ≤ M} = 0 := by
    intro M
    have hle : ∀ A : ℕ, P {ω | ∀ T : ℕ, ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω) ≤ M}
        ≤ ENNReal.ofReal (2 * K / (1 + A)) := by
      intro A
      obtain ⟨T, hT⟩ : ∃ T : ℕ, 2 * (M : ℝ) * Real.exp (A - c) + 1 ≤ T :=
        exists_nat_ge _
      have hMe : 0 ≤ (M : ℝ) * Real.exp (A - c) := by positivity
      have hT1 : (1 : ℝ) ≤ T := by linarith
      have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
      have ha : (0 : ℝ) < T * (1 + A) / 2 := by positivity
      have haT : (T : ℝ) * (1 + A) / 2 ≤ T * (1 + A) - M * Real.exp (A - c) := by
        nlinarith
      have hsub : {ω | ∀ T : ℕ, ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω) ≤ M}
          ⊆ {ω | ∫ x in (0 : ℝ)..(T : ℝ), Real.exp (c + X x ω) ≤ (M : ℝ)} :=
        fun ω hω => hω T
      refine (measure_mono hsub).trans
        ((measure_integral_exp_le hm hc hK0 hK c M A (by positivity) ha haT).trans
          (le_of_eq ?_))
      rw [← ENNReal.ofReal_div_of_pos ha]
      congr 1
      field_simp
    have htend : Tendsto (fun A : ℕ => ENNReal.ofReal (2 * K / (1 + A))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun A : ℕ => 2 * K / (1 + (A : ℝ))) atTop (𝓝 0) := by
        refine Tendsto.div_atTop tendsto_const_nhds ?_
        exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
      simpa using ENNReal.tendsto_ofReal h1
    exact le_antisymm (ge_of_tendsto' htend hle) zero_le
  have hall : ∀ᵐ ω ∂P, ∀ M : ℕ, ∃ T : ℕ,
      (M : ℝ) < ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω) := by
    rw [ae_all_iff]
    intro M
    have := measure_eq_zero_iff_ae_notMem.mp (hbad M)
    filter_upwards [this] with ω hω
    by_contra hcon
    exact hω fun T => not_lt.mp fun hlt => hcon ⟨T, hlt⟩
  filter_upwards [hall] with ω hω
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨M, hM⟩ := exists_nat_gt b
  obtain ⟨T, hT⟩ := hω M
  refine ⟨T, fun T' hT' => ?_⟩
  have hcont : Continuous fun x => Real.exp (c + X x ω) :=
    Real.continuous_exp.comp (continuous_const.add (hc ω))
  have hmono := intervalIntegral.integral_mono_interval (μ := volume)
    (f := fun x => Real.exp (c + X x ω)) (a := 0) (b := T) (c := 0) (d := T') le_rfl
    (Nat.cast_nonneg T) hT' (Eventually.of_forall fun x => (Real.exp_pos _).le)
    (hcont.intervalIntegrable _ _)
  linarith

/-- **Almost surely the integral of the exponential of the process falls
without bound toward earlier times.** -/
theorem ae_tendsto_integral_exp_atBot (hm : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t, ∫⁻ ω, ENNReal.ofReal |X t ω| ∂P ≤ ENNReal.ofReal K) (c : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω)) atBot atBot := by
  have h := ae_tendsto_integral_exp_atTop (X := fun t ω => X (-t) ω) (fun t => hm (-t))
    (fun ω => (hc ω).comp continuous_neg) hK0 (fun t => hK (-t)) c
  filter_upwards [h] with ω hω
  have e : (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.exp (c + X x ω))
      = fun T : ℝ => -∫ x in (0 : ℝ)..(-T), Real.exp (c + X (-x) ω) := by
    funext T
    rw [intervalIntegral.integral_comp_neg (fun x => Real.exp (c + X x ω)), neg_neg, neg_zero,
      intervalIntegral.integral_symm]
  rw [e]
  exact tendsto_neg_atTop_atBot.comp (hω.comp tendsto_neg_atBot_atTop)

end Process


/-- By how much a clock advances when its rate has a constant factor. -/
theorem clockAdvance_const_add (c : ℝ) (y : ℝ → ℝ) (T : ℝ) :
    clockAdvance (fun x => c + y x) T = Real.exp c * ∫ x in (0 : ℝ)..T, Real.exp (0 + y x) := by
  unfold clockAdvance
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show Real.exp (c + y x) = Real.exp c * Real.exp (0 + y x)
  rw [zero_add, Real.exp_add]

/-- **Almost surely a clock whose rate wanders advances without bound in
both directions of time**, when the wander has continuous paths and a
bounded mean size. The logarithm of the mean rate may be random. -/
theorem ae_tendsto_clockAdvance [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ} (c : Ω → ℝ)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous fun t => X t ω) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t, ∫⁻ ω, ENNReal.ofReal |X t ω| ∂P ≤ ENNReal.ofReal K) :
    ∀ᵐ ω ∂P, Tendsto (clockAdvance fun x => c ω + X x ω) atTop atTop
      ∧ Tendsto (clockAdvance fun x => c ω + X x ω) atBot atBot := by
  filter_upwards [ae_tendsto_integral_exp_atTop hm hc hK0 hK 0,
    ae_tendsto_integral_exp_atBot hm hc hK0 hK 0] with ω h1 h2
  have e : clockAdvance (fun x => c ω + X x ω)
      = fun T => Real.exp (c ω) * ∫ x in (0 : ℝ)..T, Real.exp (0 + X x ω) := by
    funext T
    exact clockAdvance_const_add (c ω) (fun x => X x ω) T
  rw [e]
  exact ⟨h1.const_mul_atTop (Real.exp_pos _), h2.const_mul_atBot (Real.exp_pos _)⟩

/-- The mean size of a sum of finitely many processes is at most the sum of
the bounds of their mean sizes. -/
theorem lintegral_abs_sum_le {ι : Type*} (s : Finset ι) {X : ι → Ω → ℝ} {K : ι → ℝ}
    (hm : ∀ i ∈ s, Measurable (X i)) (hK0 : ∀ i ∈ s, 0 ≤ K i)
    (hK : ∀ i ∈ s, ∫⁻ ω, ENNReal.ofReal |X i ω| ∂P ≤ ENNReal.ofReal (K i)) :
    ∫⁻ ω, ENNReal.ofReal |∑ i ∈ s, X i ω| ∂P ≤ ENNReal.ofReal (∑ i ∈ s, K i) := by
  calc ∫⁻ ω, ENNReal.ofReal |∑ i ∈ s, X i ω| ∂P
      ≤ ∫⁻ ω, ∑ i ∈ s, ENNReal.ofReal |X i ω| ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
        exact ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal |X i ω| ∂P :=
        lintegral_finsetSum _ fun i hi => (hm i hi).abs.ennreal_ofReal
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (K i) := Finset.sum_le_sum hK
    _ = ENNReal.ofReal (∑ i ∈ s, K i) := (ENNReal.ofReal_sum_of_nonneg hK0).symm


end Unisono.Spec
