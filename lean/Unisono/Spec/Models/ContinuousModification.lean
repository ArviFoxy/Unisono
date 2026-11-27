/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.DyadicLimit
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A process with continuous paths from a bound on fourth moments

Let `Y` be a real process indexed by the real numbers that is measurable at
every time, on a probability space, such that the fourth moment of
`Y t - Y s` is at most `C * (t - s) ^ 2` for all times `s` and `t`. Then
`continuousModification Y` is a process with these properties.

* Every path is continuous (`continuous_continuousModification`).
* At every time it is measurable (`measurable_continuousModification`) and
  almost surely equal to `Y` (`continuousModification_ae_eq`).

This is the theorem of Kolmogorov and Chentsov in the one case that the
generative model needs. The proof bounds every step of a path between
neighbouring multiples of `1 / 2 ^ n`, from `-M` to `M`, by `stepBound`:
`(7 / 8) ^ n` plus the fourth powers of all those steps, summed and divided
by the cube of `(7 / 8) ^ n`. The mean of `stepBound` is at most
`(7 / 8) ^ n + 2 * M * C * (256 / 343) ^ n`, which is summable, so almost
every path has summable step bounds (`ae_mem_summableSteps`), and such a
path has a continuous limit along the dyadic numbers
(`StepsWithin.continuousOn_dyadicLimit`). The limit equals `Y` almost surely
at each time because `Y` at the dyadic floors of the time converges to `Y`
at the time in fourth mean.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ℝ → Ω → ℝ}

/-- A number is at most `a` plus its fourth power divided by the cube of
`a`. -/
theorem abs_le_add_pow_four_div (x : ℝ) {a : ℝ} (ha : 0 < a) : |x| ≤ a + x ^ 4 / a ^ 3 := by
  by_cases h : |x| ≤ a
  · have : 0 ≤ x ^ 4 / a ^ 3 := by positivity
    linarith
  · have h := not_le.mp h
    have e : x ^ 4 = |x| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    have h3 : a ^ 3 ≤ |x| ^ 3 := pow_le_pow_left₀ ha.le h.le 3
    have : |x| ≤ x ^ 4 / a ^ 3 := by
      rw [le_div_iff₀ (by positivity), e]
      calc |x| * a ^ 3 ≤ |x| * |x| ^ 3 := by gcongr
        _ = |x| ^ 4 := by ring
    linarith

/-- The fourth powers of the steps of level `n` between `-M` and `M`,
summed. -/
def stepPowers (Y : ℝ → Ω → ℝ) (M n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Ico (-(M : ℤ) * 2 ^ n) ((M : ℤ) * 2 ^ n),
    (Y (((k + 1 : ℤ) : ℝ) / 2 ^ n) ω - Y ((k : ℝ) / 2 ^ n) ω) ^ 4

/-- A bound of every step of level `n` between `-M` and `M`. -/
def stepBound (Y : ℝ → Ω → ℝ) (M n : ℕ) (ω : Ω) : ℝ :=
  (7 / 8) ^ n + (8 / 7) ^ (3 * n) * stepPowers Y M n ω

theorem stepPowers_nonneg (Y : ℝ → Ω → ℝ) (M n : ℕ) (ω : Ω) : 0 ≤ stepPowers Y M n ω :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem stepBound_nonneg (Y : ℝ → Ω → ℝ) (M n : ℕ) (ω : Ω) : 0 ≤ stepBound Y M n ω := by
  have := stepPowers_nonneg Y M n ω
  unfold stepBound
  positivity

/-- The steps of a path are within its bounds. -/
theorem stepsWithin_stepBound (Y : ℝ → Ω → ℝ) (M : ℕ) (ω : Ω) :
    StepsWithin (fun t => Y t ω) M fun n => stepBound Y M n ω where
  nonneg n := stepBound_nonneg Y M n ω
  step n k hk1 hk2 := by
    have ha : (0 : ℝ) < (7 / 8) ^ n := by positivity
    refine (abs_le_add_pow_four_div _ ha).trans ?_
    unfold stepBound
    have hterm : (Y (((k + 1 : ℤ) : ℝ) / 2 ^ n) ω - Y ((k : ℝ) / 2 ^ n) ω) ^ 4
        ≤ stepPowers Y M n ω :=
      Finset.single_le_sum (f := fun k : ℤ =>
        (Y (((k + 1 : ℤ) : ℝ) / 2 ^ n) ω - Y ((k : ℝ) / 2 ^ n) ω) ^ 4)
        (fun _ _ => by positivity) (Finset.mem_Ico.mpr ⟨hk1, hk2⟩)
    have e : ((7 / 8 : ℝ) ^ n) ^ 3 = ((8 / 7 : ℝ) ^ (3 * n))⁻¹ := by
      rw [← pow_mul, mul_comm n 3, ← inv_pow]
      norm_num
    rw [e, div_inv_eq_mul, mul_comm _ ((8 / 7 : ℝ) ^ (3 * n))]
    gcongr

theorem measurable_stepPowers (hY : ∀ t, Measurable (Y t)) (M n : ℕ) :
    Measurable (stepPowers Y M n) :=
  Finset.measurable_sum _ fun _ _ => ((hY _).sub (hY _)).pow_const 4

theorem measurable_stepBound (hY : ∀ t, Measurable (Y t)) (M n : ℕ) :
    Measurable (stepBound Y M n) :=
  measurable_const.add (measurable_const.mul (measurable_stepPowers hY M n))

/-- **The outcomes whose path has summable step bounds** on every stretch
from `-M` to `M`. -/
def summableSteps (Y : ℝ → Ω → ℝ) : Set Ω := {ω | ∀ M : ℕ, Summable fun n => stepBound Y M n ω}

theorem summable_iff_tsum_ofReal_ne_top {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) :
    Summable b ↔ ∑' n, ENNReal.ofReal (b n) ≠ ⊤ := by
  have h1 : (∑' n, ENNReal.ofReal (b n)) = ∑' n, ((b n).toNNReal : ℝ≥0∞) := rfl
  rw [h1, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  refine summable_congr fun n => ?_
  rw [Real.coe_toNNReal _ (hb n)]

theorem measurableSet_summableSteps (hY : ∀ t, Measurable (Y t)) :
    MeasurableSet (summableSteps Y) := by
  have : summableSteps Y = ⋂ M : ℕ, {ω | ∑' n, ENNReal.ofReal (stepBound Y M n ω) ≠ ⊤} := by
    ext ω
    simp only [summableSteps, Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_congr' fun M =>
      summable_iff_tsum_ofReal_ne_top fun n => stepBound_nonneg Y M n ω
  rw [this]
  refine MeasurableSet.iInter fun M => ?_
  have hm : Measurable fun ω => ∑' n, ENNReal.ofReal (stepBound Y M n ω) :=
    Measurable.tsum fun n => (measurable_stepBound hY M n).ennreal_ofReal
  exact (measurableSet_singleton ⊤).compl.preimage hm

/-- **The continuous modification** of a process: on the outcomes whose path
has summable step bounds, the limit of the path along the dyadic numbers
below each time; zero on the other outcomes. -/
def continuousModification (Y : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ := by
  classical
  exact if ω ∈ summableSteps Y then dyadicLimit (fun s => Y s ω) t else 0

/-- Every number lies strictly between `-M` and `M` for some whole `M`. -/
theorem exists_nat_abs_lt (t : ℝ) : ∃ M : ℕ, -(M : ℝ) < t ∧ t < M := by
  obtain ⟨M, hM⟩ := exists_nat_gt |t|
  exact ⟨M, by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

/-- **Every path of the continuous modification is continuous.** -/
theorem continuous_continuousModification (Y : ℝ → Ω → ℝ) (ω : Ω) :
    Continuous fun t => continuousModification Y t ω := by
  classical
  by_cases hω : ω ∈ summableSteps Y
  · have e : (fun t => continuousModification Y t ω) = dyadicLimit fun s => Y s ω := by
      funext t
      simp [continuousModification, hω]
    rw [e, continuous_iff_continuousAt]
    intro t
    obtain ⟨M, h1, h2⟩ := exists_nat_abs_lt t
    exact ((stepsWithin_stepBound Y M ω).continuousOn_dyadicLimit (hω M)).continuousAt
      (Ioo_mem_nhds h1 h2)
  · have e : (fun t => continuousModification Y t ω) = fun _ => 0 := by
      funext t
      simp [continuousModification, hω]
    rw [e]
    exact continuous_const

/-- On an outcome whose path has summable step bounds, the path along the
dyadic numbers below `t` converges to the continuous modification at `t`. -/
theorem tendsto_continuousModification {ω : Ω} (hω : ω ∈ summableSteps Y) (t : ℝ) :
    Tendsto (fun n => Y (dyadicFloor n t) ω) atTop (𝓝 (continuousModification Y t ω)) := by
  classical
  obtain ⟨M, h1, h2⟩ := exists_nat_abs_lt t
  have := (stepsWithin_stepBound Y M ω).tendsto_dyadicLimit (hω M) h1.le h2
  simpa [continuousModification, hω] using this

/-- **The continuous modification is measurable at each time.** -/
theorem measurable_continuousModification (hY : ∀ t, Measurable (Y t)) (t : ℝ) :
    Measurable (continuousModification Y t) := by
  classical
  have hg := measurableSet_summableSteps hY
  refine measurable_of_tendsto_metrizable
    (f := fun n ω => if ω ∈ summableSteps Y then Y (dyadicFloor n t) ω else 0)
    (fun n => Measurable.ite hg (hY _) measurable_const) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ summableSteps Y
  · simpa [hω] using tendsto_continuousModification hω t
  · simp [continuousModification, hω]

/-- **Almost every path has summable step bounds**, when the fourth moment
of the increment over any stretch is at most `C` times the square of the
length of the stretch. -/
theorem ae_mem_summableSteps [IsProbabilityMeasure P] (hY : ∀ t, Measurable (Y t)) {C : ℝ}
    (hC : 0 ≤ C)
    (hmom : ∀ s t, ∫⁻ ω, ENNReal.ofReal ((Y t ω - Y s ω) ^ 4) ∂P
      ≤ ENNReal.ofReal (C * (t - s) ^ 2)) :
    ∀ᵐ ω ∂P, ω ∈ summableSteps Y := by
  unfold summableSteps
  simp only [Set.mem_ofPred_eq]
  rw [ae_all_iff]
  intro M
  -- The mean of the bound of level `n`.
  have hpow : ∀ n, ∫⁻ ω, ENNReal.ofReal (stepPowers Y M n ω) ∂P
      ≤ ENNReal.ofReal (2 * M * C * (1 / 2) ^ n) := by
    intro n
    have hsum : ∀ ω, ENNReal.ofReal (stepPowers Y M n ω)
        = ∑ k ∈ Finset.Ico (-(M : ℤ) * 2 ^ n) ((M : ℤ) * 2 ^ n),
          ENNReal.ofReal ((Y (((k + 1 : ℤ) : ℝ) / 2 ^ n) ω - Y ((k : ℝ) / 2 ^ n) ω) ^ 4) :=
      fun ω => ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
    simp_rw [hsum]
    rw [lintegral_finsetSum (f := fun (k : ℤ) ω => ENNReal.ofReal
      ((Y (((k + 1 : ℤ) : ℝ) / 2 ^ n) ω - Y ((k : ℝ) / 2 ^ n) ω) ^ 4)) _ fun _ _ =>
      (((hY _).sub (hY _)).pow_const 4).ennreal_ofReal]
    have hone : ∀ k ∈ Finset.Ico (-(M : ℤ) * 2 ^ n) ((M : ℤ) * 2 ^ n),
        ∫⁻ ω, ENNReal.ofReal
          ((Y (((k + 1 : ℤ) : ℝ) / 2 ^ n) ω - Y ((k : ℝ) / 2 ^ n) ω) ^ 4) ∂P
          ≤ ENNReal.ofReal (C * (1 / 2 ^ n) ^ 2) := by
      intro k _
      refine (hmom _ _).trans (le_of_eq ?_)
      congr 2
      push_cast
      field_simp
      ring
    refine (Finset.sum_le_sum hone).trans ?_
    rw [Finset.sum_const, Int.card_Ico, nsmul_eq_mul]
    have hcard : (((M : ℤ) * 2 ^ n - -(M : ℤ) * 2 ^ n).toNat : ℝ≥0∞)
        = ENNReal.ofReal (2 * M * 2 ^ n) := by
      have : ((M : ℤ) * 2 ^ n - -(M : ℤ) * 2 ^ n).toNat = 2 * M * 2 ^ n := by
        have h0 : (M : ℤ) * 2 ^ n - -(M : ℤ) * 2 ^ n = ((2 * M * 2 ^ n : ℕ) : ℤ) := by
          push_cast
          ring
        rw [h0, Int.toNat_natCast]
      rw [this, ← ENNReal.ofReal_natCast]
      push_cast
      rfl
    rw [hcard, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have e : (2 : ℝ) ^ n * (1 / 2 ^ n) ^ 2 = (1 / 2) ^ n := by
      simp only [one_div_pow]
      field_simp
    calc 2 * (M : ℝ) * 2 ^ n * (C * (1 / 2 ^ n) ^ 2)
        = 2 * M * C * (2 ^ n * (1 / 2 ^ n) ^ 2) := by ring
      _ = 2 * M * C * (1 / 2) ^ n := by rw [e]
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal (stepBound Y M n ω) ∂P
      ≤ ENNReal.ofReal ((7 / 8) ^ n + 2 * M * C * (256 / 343) ^ n) := by
    intro n
    have hsplit : ∀ ω, ENNReal.ofReal (stepBound Y M n ω)
        = ENNReal.ofReal ((7 / 8) ^ n)
          + ENNReal.ofReal ((8 / 7) ^ (3 * n)) * ENNReal.ofReal (stepPowers Y M n ω) := by
      intro ω
      unfold stepBound
      rw [ENNReal.ofReal_add (by positivity)
        (mul_nonneg (by positivity) (stepPowers_nonneg Y M n ω)),
        ENNReal.ofReal_mul (by positivity)]
    have hmeas : Measurable fun ω => ENNReal.ofReal (stepPowers Y M n ω) :=
      (measurable_stepPowers hY M n).ennreal_ofReal
    simp_rw [hsplit]
    rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hmeas,
      measure_univ, mul_one]
    calc ENNReal.ofReal ((7 / 8) ^ n)
          + ENNReal.ofReal ((8 / 7) ^ (3 * n)) * ∫⁻ ω, ENNReal.ofReal (stepPowers Y M n ω) ∂P
        ≤ ENNReal.ofReal ((7 / 8) ^ n)
          + ENNReal.ofReal ((8 / 7) ^ (3 * n)) * ENNReal.ofReal (2 * M * C * (1 / 2) ^ n) := by
          gcongr
          exact hpow n
      _ = ENNReal.ofReal ((7 / 8) ^ n + 2 * M * C * (256 / 343) ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 2
          have : ((8 / 7 : ℝ) ^ (3 * n)) * ((1 / 2) ^ n) = (256 / 343) ^ n := by
            rw [pow_mul, ← mul_pow]
            norm_num
          calc (8 / 7 : ℝ) ^ (3 * n) * (2 * M * C * (1 / 2) ^ n)
              = 2 * M * C * ((8 / 7 : ℝ) ^ (3 * n) * (1 / 2) ^ n) := by ring
            _ = 2 * M * C * (256 / 343) ^ n := by rw [this]
  have hg : Summable fun n : ℕ => (7 / 8 : ℝ) ^ n + 2 * M * C * (256 / 343) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).add
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
  have hfin : ∫⁻ ω, ∑' n, ENNReal.ofReal (stepBound Y M n ω) ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => (measurable_stepBound hY M n).ennreal_ofReal.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hg]
    exact ENNReal.ofReal_ne_top
  have hm : Measurable fun ω => ∑' n, ENNReal.ofReal (stepBound Y M n ω) :=
    Measurable.tsum fun n => (measurable_stepBound hY M n).ennreal_ofReal
  filter_upwards [ae_lt_top hm hfin] with ω hω
  exact (summable_iff_tsum_ofReal_ne_top fun n => stepBound_nonneg Y M n ω).mpr hω.ne

/-- **The continuous modification equals the process at each time, almost
surely.** -/
theorem continuousModification_ae_eq [IsProbabilityMeasure P] (hY : ∀ t, Measurable (Y t))
    {C : ℝ} (hC : 0 ≤ C)
    (hmom : ∀ s t, ∫⁻ ω, ENNReal.ofReal ((Y t ω - Y s ω) ^ 4) ∂P
      ≤ ENNReal.ofReal (C * (t - s) ^ 2)) (t : ℝ) :
    continuousModification Y t =ᵐ[P] Y t := by
  have hgood := ae_mem_summableSteps hY hC hmom
  -- The fourth moment of the difference is at most the limit of those along the floors.
  have hlim : ∀ᵐ ω ∂P, liminf (fun n => ENNReal.ofReal ((Y (dyadicFloor n t) ω - Y t ω) ^ 4))
      atTop = ENNReal.ofReal ((continuousModification Y t ω - Y t ω) ^ 4) := by
    filter_upwards [hgood] with ω hω
    have h1 := tendsto_continuousModification hω t
    have h2 : Tendsto (fun n => ENNReal.ofReal ((Y (dyadicFloor n t) ω - Y t ω) ^ 4)) atTop
        (𝓝 (ENNReal.ofReal ((continuousModification Y t ω - Y t ω) ^ 4))) :=
      ENNReal.tendsto_ofReal ((h1.sub_const (Y t ω)).pow 4)
    exact h2.liminf_eq
  have hfatou := lintegral_liminf_le (μ := P) (u := atTop)
    (f := fun n ω => ENNReal.ofReal ((Y (dyadicFloor n t) ω - Y t ω) ^ 4))
    fun n => (((hY _).sub (hY _)).pow_const 4).ennreal_ofReal
  have hzero : liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((Y (dyadicFloor n t) ω - Y t ω) ^ 4) ∂P)
      atTop ≤ 0 := by
    have hle : ∀ n, ∫⁻ ω, ENNReal.ofReal ((Y (dyadicFloor n t) ω - Y t ω) ^ 4) ∂P
        ≤ ENNReal.ofReal (C * (1 / 2 ^ n) ^ 2) := by
      intro n
      refine (hmom t (dyadicFloor n t)).trans (ENNReal.ofReal_le_ofReal ?_)
      have := abs_dyadicFloor_sub_le n t
      have h2 : (dyadicFloor n t - t) ^ 2 ≤ (1 / 2 ^ n) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      gcongr
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (1 / 2 ^ n) ^ 2)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => C * (1 / 2 ^ n : ℝ) ^ 2) atTop (𝓝 (C * 0 ^ 2)) := by
        refine Tendsto.const_mul _ (Tendsto.pow ?_ 2)
        simpa [one_div] using tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
          (by norm_num) (by norm_num)
      simpa using ENNReal.tendsto_ofReal this
    calc liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((Y (dyadicFloor n t) ω - Y t ω) ^ 4) ∂P) atTop
        ≤ liminf (fun n : ℕ => ENNReal.ofReal (C * (1 / 2 ^ n) ^ 2)) atTop :=
          liminf_le_liminf (Eventually.of_forall hle)
      _ = 0 := htend.liminf_eq
  have hint : ∫⁻ ω, ENNReal.ofReal ((continuousModification Y t ω - Y t ω) ^ 4) ∂P = 0 := by
    rw [← lintegral_congr_ae hlim]
    exact le_antisymm (hfatou.trans hzero) zero_le
  have hmeas : Measurable fun ω =>
      ENNReal.ofReal ((continuousModification Y t ω - Y t ω) ^ 4) :=
    (((measurable_continuousModification hY t).sub (hY t)).pow_const 4).ennreal_ofReal
  rw [lintegral_eq_zero_iff hmeas] at hint
  filter_upwards [hint] with ω hω
  have h0 : (continuousModification Y t ω - Y t ω) ^ 4 ≤ 0 := by
    simpa using hω
  have h1 : (continuousModification Y t ω - Y t ω) ^ 4 = 0 :=
    le_antisymm h0 (by positivity)
  have h2 : continuousModification Y t ω - Y t ω = 0 := by
    simpa using h1
  linarith


end Unisono.Spec
