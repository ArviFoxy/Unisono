/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeWorld
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Function.Floor

/-!
# A random process of pauses

The generative model asks for the paused time of a link or of a host as a
random function of true time: it starts at zero at true time zero, never
decreases, counts a pause from the instant at which it begins, and the paused
time that begins in periods that do not overlap is independent, with the law
`pauseLaw` (`GenerativeWorld.Prior`). This file constructs such a process,
for any rate of pauses and any law of their lengths.

The construction cuts true time into cells of one second. In each cell the
number of pauses has the Poisson law with the rate as its mean; each pause
begins at a point drawn uniformly in the cell, and has a length drawn from
the law of the lengths; all of these are independent. The paused time that
begins between two true times is the sum of the lengths of the pauses that
begin in between.

* `pausedPath`: the paused time that has begun since true time zero. In
  every outcome it is zero at true time zero (`pausedPath_zero`), never
  decreases (`pausedPath_monotone`) and is continuous from the right
  (`pausedPath_rightContinuous`).
* `hasLaw_pausedPath_sub`: the paused time that begins between two true
  times has the law `pauseLaw`, for the mean number of pauses that begin in
  between.
* `hasIndepIncrements_pausedPath`: the paused time that begins in periods
  that do not overlap is independent.

The laws are found from characteristic functions.

* `charFun_pauseLaw`: the characteristic function of `pauseLaw` is
  `exp (count * (φ - 1))`, where `φ` is that of the law of the lengths.
* `integral_cexp_cellSum`: for one cell, the mean of `exp (i * S)`, where `S`
  is the sum of a function over the pauses of the cell.
* `integral_cexp_pausedBetween`: the joint characteristic function of the
  paused times of periods that do not overlap is the product of those of
  `pauseLaw`. Independence follows, because a joint characteristic function
  that is a product belongs to independent numbers.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal RealInnerProductSpace

/-! ## The characteristic function of the law of the paused time -/

/-- The mean of `z ^ n`, for a number `n` with the Poisson law of mean `r`. -/
theorem integral_pow_poissonMeasure (r : ℝ≥0) (z : ℂ) :
    ∫ n, z ^ n ∂poissonMeasure r = cexp ((r : ℝ) * (z - 1)) := by
  rw [integral_poissonMeasure r]
  calc ∑' n : ℕ, (Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ)) • z ^ n
      = ∑' n : ℕ, (Real.exp (-r) : ℂ) * ((((r : ℝ) : ℂ) * z) ^ n / (n.factorial : ℂ)) := by
        congr with n
        rw [Complex.real_smul]
        push_cast
        rw [mul_pow]
        ring
    _ = (Real.exp (-r) : ℂ) * ∑' n : ℕ, (((r : ℝ) : ℂ) * z) ^ n / (n.factorial : ℂ) :=
        tsum_mul_left
    _ = (Real.exp (-r) : ℂ) * cexp (((r : ℝ) : ℂ) * z) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp (((r : ℝ) : ℂ) * z)).tsum_eq,
          Complex.exp_eq_exp_ℂ]
    _ = cexp ((r : ℝ) * (z - 1)) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        push_cast
        ring_nf

/-- The characteristic function of the sum of `n` independent lengths. -/
theorem charFun_sumLaw (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) (t : ℝ) :
    charFun (sumLaw F n) t = charFun F t ^ n := by
  induction n with
  | zero => simp [sumLaw]
  | succ n ih => rw [sumLaw, charFun_conv, ih, pow_succ]

instance pauseLaw_prob (count : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (pauseLaw count F) :=
  ⟨pauseLaw_univ count F⟩

/-- **The characteristic function of the law of the paused time of a
period**: `exp (count * (φ t - 1))`, where `φ` is the characteristic function
of the law of the length of a pause and `count` is the mean number of pauses
that begin in the period. -/
theorem charFun_pauseLaw (count : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F] (t : ℝ) :
    charFun (pauseLaw count F) t = cexp ((count : ℝ) * (charFun F t - 1)) := by
  have hint : Integrable (fun x : ℝ => cexp (⟪x, t⟫ * I)) (pauseLaw count F) :=
    (integrable_const (1 : ℝ)).mono (by fun_prop)
      (Filter.Eventually.of_forall fun x => by
        rw [Complex.norm_exp_ofReal_mul_I, norm_one])
  rw [charFun_apply]
  unfold pauseLaw at hint ⊢
  rw [integral_sum_measure hint, ← integral_pow_poissonMeasure, integral_poissonMeasure count]
  congr with n
  rw [integral_smul_measure, poissonMeasure_singleton, ENNReal.toReal_ofReal (by positivity),
    ← charFun_apply, charFun_sumLaw]

/-! ## One cell -/

/-- What is drawn for one cell of true time: the number of pauses that begin
in it, and for each pause a number that fixes where in the cell it begins,
with its length. Only the first pauses, as many as the number says, are
used. -/
abbrev Cell : Type := ℕ × (ℕ → ℝ × ℝ)

/-- The uniform law on the numbers from zero to one. -/
def unitLaw : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

instance : IsProbabilityMeasure unitLaw :=
  ⟨by simp [unitLaw]⟩

/-- The law of what is drawn for one pause: where in its cell it begins,
uniform on the cell, and its length, with the law `F`; the two are
independent. -/
def markLaw (F : Measure ℝ) : Measure (ℝ × ℝ) := unitLaw.prod F

instance (F : Measure ℝ) [IsProbabilityMeasure F] : IsProbabilityMeasure (markLaw F) :=
  inferInstanceAs (IsProbabilityMeasure (unitLaw.prod F))

/-- The law of what is drawn for one cell: the number of pauses has the
Poisson law with mean `rate`, and the pauses are independent of it and of one
another. -/
def cellLaw (rate : ℝ≥0) (F : Measure ℝ) : Measure Cell :=
  (poissonMeasure rate).prod (Measure.infinitePi fun _ : ℕ => markLaw F)

instance (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (cellLaw rate F) :=
  inferInstanceAs (IsProbabilityMeasure
    ((poissonMeasure rate).prod (Measure.infinitePi fun _ : ℕ => markLaw F)))

/-- The sum of a function `h` over the pauses of a cell. -/
def cellSum (h : ℝ × ℝ → ℝ) (cell : Cell) : ℝ :=
  ∑ k ∈ Finset.range cell.1, h (cell.2 k)

theorem measurable_cellSum {h : ℝ × ℝ → ℝ} (hh : Measurable h) : Measurable (cellSum h) := by
  refine measurable_from_prod_countable_right fun n => ?_
  show Measurable fun y : ℕ → ℝ × ℝ => ∑ k ∈ Finset.range n, h (y k)
  exact Finset.measurable_sum (f := fun k (y : ℕ → ℝ × ℝ) => h (y k)) _
    fun k _ => hh.comp (measurable_pi_apply k)

/-- The mean of a product of one function of each of the first `n` pauses is
the `n`-th power of the mean of the function. -/
theorem integral_prod_marks (F : Measure ℝ) [IsProbabilityMeasure F] {g : ℝ × ℝ → ℂ}
    (hg : Measurable g) (n : ℕ) :
    ∫ ξ : ℕ → ℝ × ℝ, ∏ k ∈ Finset.range n, g (ξ k) ∂Measure.infinitePi (fun _ : ℕ => markLaw F)
      = (∫ z, g z ∂markLaw F) ^ n := by
  have hind : iIndepFun (fun (k : Fin n) (ξ : ℕ → ℝ × ℝ) => ξ k)
      (Measure.infinitePi fun _ : ℕ => markLaw F) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => markLaw F) (X := fun _ x => x)
      (fun _ => measurable_id)).precomp Fin.val_injective
  have hprod := hind.integral_fun_prod_comp (f := fun _ => g)
    (fun k => (measurable_pi_apply (k : ℕ)).aemeasurable)
    (fun k => hg.aestronglyMeasurable)
  have hone : ∀ k : Fin n, ∫ ξ : ℕ → ℝ × ℝ, g (ξ k) ∂Measure.infinitePi (fun _ : ℕ => markLaw F)
      = ∫ z, g z ∂markLaw F := by
    intro k
    have hmap := Measure.infinitePi_map_eval (fun _ : ℕ => markLaw F) (k : ℕ)
    calc ∫ ξ : ℕ → ℝ × ℝ, g (ξ k) ∂Measure.infinitePi (fun _ : ℕ => markLaw F)
        = ∫ z, g z ∂(Measure.infinitePi fun _ : ℕ => markLaw F).map (fun ξ => ξ (k : ℕ)) :=
          (integral_map (measurable_pi_apply (k : ℕ)).aemeasurable
            hg.aestronglyMeasurable).symm
      _ = ∫ z, g z ∂markLaw F := by rw [hmap]
  have e : ∀ ξ : ℕ → ℝ × ℝ, ∏ k ∈ Finset.range n, g (ξ k) = ∏ k : Fin n, g (ξ k) :=
    fun ξ => Finset.prod_range fun k => g (ξ k)
  simp_rw [e]
  rw [hprod, Finset.prod_congr rfl fun k _ => hone k, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **The pauses of one cell.** For a measurable function `h` of a pause,
the mean of `exp (i * S)`, where `S` is the sum of `h` over the pauses of the
cell, is `exp (rate * (m - 1))`, where `m` is the mean of `exp (i * h)` for
one pause. -/
theorem integral_cexp_cellSum (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    {h : ℝ × ℝ → ℝ} (hh : Measurable h) :
    ∫ cell, cexp (cellSum h cell * I) ∂cellLaw rate F
      = cexp ((rate : ℝ) * (∫ z, cexp (h z * I) ∂markLaw F - 1)) := by
  have hmeas : Measurable fun cell : Cell => cexp (cellSum h cell * I) := by
    have := measurable_cellSum hh
    fun_prop
  have hint : Integrable (fun cell : Cell => cexp (cellSum h cell * I)) (cellLaw rate F) :=
    (integrable_const (1 : ℝ)).mono hmeas.aestronglyMeasurable (by simp)
  unfold cellLaw at hint ⊢
  rw [integral_prod _ hint, ← integral_pow_poissonMeasure]
  congr with n
  rw [← integral_prod_marks F (g := fun z => cexp (h z * I)) (by fun_prop) n]
  congr with ξ
  simp only [cellSum]
  rw [← Complex.exp_sum, ← Finset.sum_mul]
  push_cast
  rfl

/-! ## The paused time as a function of true time -/

/-- What is drawn for all cells. Cell `c` is the second of true time that
begins at `c`. -/
abbrev Cells : Type := ℤ → Cell

/-- The law of what is drawn for all cells: the cells are independent, each
with the law `cellLaw`. -/
def cellsLaw (rate : ℝ≥0) (F : Measure ℝ) : Measure Cells :=
  Measure.infinitePi fun _ : ℤ => cellLaw rate F

instance (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (cellsLaw rate F) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℤ => cellLaw rate F))

/-- The true time at which a pause of cell `c` begins, from the number `u`
drawn for it: `u`, reduced to its fractional part, after the start of the
cell. -/
def pauseStart (c : ℤ) (u : ℝ) : ℝ := c + Int.fract u

/-- The length of a pause of cell `c`, if the pause begins after `s` and not
after `t`, and zero otherwise. A length that is not positive counts as
zero. -/
def markIn (c : ℤ) (s t : ℝ) (z : ℝ × ℝ) : ℝ :=
  if s < pauseStart c z.1 ∧ pauseStart c z.1 ≤ t then max z.2 0 else 0

/-- The paused time that begins after `s` and not after `t`: the sum of the
lengths of the pauses that begin then. -/
def pausedBetween (s t : ℝ) (ω : Cells) : ℝ :=
  ∑ c ∈ Finset.Icc ⌊s⌋ ⌊t⌋, cellSum (markIn c s t) (ω c)

/-- **The paused time that has begun since true time zero**, as a function
of true time; before true time zero, the opposite of the paused time that
begins from then until true time zero. -/
def pausedPath (ω : Cells) (t : ℝ) : ℝ :=
  if 0 ≤ t then pausedBetween 0 t ω else -pausedBetween t 0 ω

theorem markIn_nonneg (c : ℤ) (s t : ℝ) (z : ℝ × ℝ) : 0 ≤ markIn c s t z := by
  unfold markIn
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

/-- A pause of cell `c` begins in the second that starts at `c`. -/
theorem markIn_eq_zero {c : ℤ} {s t : ℝ} (hc : c ∉ Finset.Icc ⌊s⌋ ⌊t⌋) (z : ℝ × ℝ) :
    markIn c s t z = 0 := by
  unfold markIn
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  apply hc
  have hf0 := Int.fract_nonneg z.1
  have hf1 := Int.fract_lt_one z.1
  unfold pauseStart at h1 h2
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_le_iff.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩

theorem cellSum_nonneg {h : ℝ × ℝ → ℝ} (hh : ∀ z, 0 ≤ h z) (cell : Cell) :
    0 ≤ cellSum h cell :=
  Finset.sum_nonneg fun _ _ => hh _

theorem cellSum_eq_zero {h : ℝ × ℝ → ℝ} (hh : ∀ z, h z = 0) (cell : Cell) :
    cellSum h cell = 0 :=
  Finset.sum_eq_zero fun _ _ => hh _

/-- The paused time that begins between two true times, as a sum over any
finite set of cells that holds every cell between the two. -/
theorem pausedBetween_eq_sum {s t : ℝ} {C : Finset ℤ} (hC : Finset.Icc ⌊s⌋ ⌊t⌋ ⊆ C)
    (ω : Cells) : pausedBetween s t ω = ∑ c ∈ C, cellSum (markIn c s t) (ω c) :=
  Finset.sum_subset hC fun _ _ hc => cellSum_eq_zero (markIn_eq_zero hc) _

theorem markIn_add {s t r : ℝ} (hst : s ≤ t) (htr : t ≤ r) (c : ℤ) (z : ℝ × ℝ) :
    markIn c s t z + markIn c t r z = markIn c s r z := by
  unfold markIn
  by_cases hsp : s < pauseStart c z.1
  · by_cases hpt : pauseStart c z.1 ≤ t
    · rw [ite_eq_left ⟨hsp, hpt⟩, ite_eq_right (fun h => absurd hpt (not_le.mpr h.1)),
        ite_eq_left ⟨hsp, hpt.trans htr⟩, add_zero]
    · by_cases hpr : pauseStart c z.1 ≤ r
      · rw [ite_eq_right (fun h => hpt h.2), ite_eq_left ⟨not_le.mp hpt, hpr⟩,
          ite_eq_left ⟨hsp, hpr⟩, zero_add]
      · rw [ite_eq_right (fun h => hpt h.2), ite_eq_right (fun h => hpr h.2),
          ite_eq_right (fun h => hpr h.2), add_zero]
  · have hps : ¬ t < pauseStart c z.1 := fun h => hsp (lt_of_le_of_lt hst h)
    rw [ite_eq_right (fun h => hsp h.1), ite_eq_right (fun h => hps h.1),
      ite_eq_right (fun h => hsp h.1), add_zero]

/-- **The paused time of two periods that follow each other adds up.** -/
theorem pausedBetween_add {s t r : ℝ} (hst : s ≤ t) (htr : t ≤ r) (ω : Cells) :
    pausedBetween s t ω + pausedBetween t r ω = pausedBetween s r ω := by
  have h1 : Finset.Icc ⌊s⌋ ⌊t⌋ ⊆ Finset.Icc ⌊s⌋ ⌊r⌋ :=
    Finset.Icc_subset_Icc le_rfl (Int.floor_le_floor htr)
  have h2 : Finset.Icc ⌊t⌋ ⌊r⌋ ⊆ Finset.Icc ⌊s⌋ ⌊r⌋ :=
    Finset.Icc_subset_Icc (Int.floor_le_floor hst) le_rfl
  rw [pausedBetween_eq_sum h1, pausedBetween_eq_sum h2, pausedBetween, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold cellSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => markIn_add hst htr c _

theorem pausedBetween_nonneg (s t : ℝ) (ω : Cells) : 0 ≤ pausedBetween s t ω :=
  Finset.sum_nonneg fun c _ => cellSum_nonneg (markIn_nonneg c s t) _

theorem pausedBetween_self (t : ℝ) (ω : Cells) : pausedBetween t t ω = 0 := by
  refine Finset.sum_eq_zero fun c _ => cellSum_eq_zero (fun z => ?_) _
  unfold markIn
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  exact absurd h2 (not_le.mpr h1)

/-- **The paused time that begins between two true times** is the
difference of the paused time that has begun at the two. -/
theorem pausedPath_sub {s t : ℝ} (hst : s ≤ t) (ω : Cells) :
    pausedPath ω t - pausedPath ω s = pausedBetween s t ω := by
  unfold pausedPath
  by_cases hs : 0 ≤ s
  · have ht : 0 ≤ t := hs.trans hst
    rw [ite_eq_left hs, ite_eq_left ht, ← pausedBetween_add hs hst ω]
    ring
  · by_cases ht : 0 ≤ t
    · rw [ite_eq_right hs, ite_eq_left ht, ← pausedBetween_add (not_le.mp hs).le ht ω]
      ring
    · rw [ite_eq_right hs, ite_eq_right ht, ← pausedBetween_add hst (not_le.mp ht).le ω]
      ring

theorem pausedPath_zero (ω : Cells) : pausedPath ω 0 = 0 := by
  unfold pausedPath
  rw [ite_eq_left le_rfl, pausedBetween_self]

/-- The paused time that has begun never decreases. -/
theorem pausedPath_monotone (ω : Cells) : Monotone (pausedPath ω) := by
  intro s t hst
  have h := pausedPath_sub hst ω
  have h0 := pausedBetween_nonneg s t ω
  linarith

/-- Just after a true time `s`, no further pause of a given cell with a
given draw has begun. -/
theorem markIn_continuousWithinAt (c : ℤ) (s : ℝ) (z : ℝ × ℝ) :
    ContinuousWithinAt (fun t => markIn c s t z) (Set.Ici s) s := by
  by_cases hp : s < pauseStart c z.1
  · have hev : (fun t => markIn c s t z) =ᶠ[nhdsWithin s (Set.Ici s)] fun _ => 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hp)] with t ht
      unfold markIn
      rw [ite_eq_right]
      rintro ⟨-, h2⟩
      exact absurd h2 (not_le.mpr ht)
    refine continuousWithinAt_const.congr_of_eventuallyEq hev ?_
    unfold markIn
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact absurd h2 (not_le.mpr h1)
  · have hconst : (fun t => markIn c s t z) = fun _ => 0 := by
      funext t
      unfold markIn
      rw [ite_eq_right]
      exact fun h => hp h.1
    rw [hconst]
    exact continuousWithinAt_const

/-- **A pause counts from the instant at which it begins**: the paused time
that has begun is continuous from the right. -/
theorem pausedPath_rightContinuous (ω : Cells) (s : ℝ) :
    ContinuousWithinAt (pausedPath ω) (Set.Ici s) s := by
  -- Within a second after `s`, only two cells matter.
  have hev : pausedPath ω =ᶠ[nhdsWithin s (Set.Ici s)] fun t =>
      pausedPath ω s + ∑ c ∈ Finset.Icc ⌊s⌋ (⌊s⌋ + 1),
        ∑ k ∈ Finset.range (ω c).1, markIn c s t ((ω c).2 k) := by
    filter_upwards [Ico_mem_nhdsGE (show s < s + 1 by linarith)] with t ht
    have hsub : Finset.Icc ⌊s⌋ ⌊t⌋ ⊆ Finset.Icc ⌊s⌋ (⌊s⌋ + 1) := by
      refine Finset.Icc_subset_Icc le_rfl (Int.floor_le_iff.mpr ?_)
      have := Int.lt_floor_add_one s
      push_cast
      linarith [ht.2]
    have h := pausedPath_sub ht.1 ω
    rw [pausedBetween_eq_sum hsub] at h
    show pausedPath ω t = pausedPath ω s + ∑ c ∈ Finset.Icc ⌊s⌋ (⌊s⌋ + 1),
      cellSum (markIn c s t) (ω c)
    linarith
  have hcont : ContinuousWithinAt (fun t =>
      pausedPath ω s + ∑ c ∈ Finset.Icc ⌊s⌋ (⌊s⌋ + 1),
        ∑ k ∈ Finset.range (ω c).1, markIn c s t ((ω c).2 k)) (Set.Ici s) s :=
    continuousWithinAt_const.add (tendsto_finsetSum _ fun c _ =>
      tendsto_finsetSum _ fun k _ => markIn_continuousWithinAt c s _)
  refine hcont.congr_of_eventuallyEq hev ?_
  have h0 : ∀ c : ℤ, ∑ k ∈ Finset.range (ω c).1, markIn c s s ((ω c).2 k) = 0 := fun c =>
    Finset.sum_eq_zero fun k _ => by
      unfold markIn
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact absurd h2 (not_le.mpr h1)
  simp only [h0, Finset.sum_const_zero, add_zero]

theorem measurable_markIn (c : ℤ) (s t : ℝ) : Measurable (markIn c s t) := by
  have hp : Measurable fun z : ℝ × ℝ => pauseStart c z.1 :=
    measurable_const.add (measurable_fract.comp measurable_fst)
  exact Measurable.ite ((measurableSet_lt measurable_const hp).inter
    (measurableSet_le hp measurable_const)) (measurable_snd.max measurable_const)
    measurable_const

theorem measurable_pausedBetween (s t : ℝ) : Measurable (pausedBetween s t) :=
  Finset.measurable_sum (f := fun c (ω : Cells) => cellSum (markIn c s t) (ω c)) _
    fun c _ => (measurable_cellSum (measurable_markIn c s t)).comp (measurable_pi_apply c)

theorem measurable_pausedPath (t : ℝ) : Measurable fun ω : Cells => pausedPath ω t := by
  unfold pausedPath
  split_ifs
  · exact measurable_pausedBetween 0 t
  · exact (measurable_pausedBetween t 0).neg

/-! ## The law of the paused time -/

/-- The mean of a product of one function of each of finitely many cells is
the product of the means. -/
theorem integral_prod_cells (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (C : Finset ℤ) {G : ℤ → Cell → ℂ} (hG : ∀ c, Measurable (G c)) :
    ∫ ω : Cells, ∏ c ∈ C, G c (ω c) ∂cellsLaw rate F
      = ∏ c ∈ C, ∫ cell, G c cell ∂cellLaw rate F := by
  have hind : iIndepFun (fun (c : ↥C) (ω : Cells) => ω c) (cellsLaw rate F) :=
    (iIndepFun_infinitePi (P := fun _ : ℤ => cellLaw rate F) (X := fun _ x => x)
      (fun _ => measurable_id)).precomp Subtype.val_injective
  have hprod := hind.integral_fun_prod_comp (f := fun c : ↥C => G c)
    (fun c => (measurable_pi_apply (c : ℤ)).aemeasurable)
    (fun c => (hG c).aestronglyMeasurable)
  have hone : ∀ c : ↥C, ∫ ω : Cells, G c (ω c) ∂cellsLaw rate F
      = ∫ cell, G c cell ∂cellLaw rate F := by
    intro c
    have hmap := Measure.infinitePi_map_eval (fun _ : ℤ => cellLaw rate F) (c : ℤ)
    calc ∫ ω : Cells, G c (ω c) ∂cellsLaw rate F
        = ∫ cell, G c cell ∂(cellsLaw rate F).map (fun ω => ω (c : ℤ)) :=
          (integral_map (measurable_pi_apply (c : ℤ)).aemeasurable
            (hG c).aestronglyMeasurable).symm
      _ = ∫ cell, G c cell ∂cellLaw rate F := by rw [cellsLaw, hmap]
  have e : ∀ ω : Cells, ∏ c ∈ C, G c (ω c) = ∏ c : ↥C, G c (ω c) :=
    fun ω => (Finset.prod_coe_sort C fun c => G c (ω c)).symm
  simp_rw [e]
  rw [hprod, Finset.prod_congr rfl fun c _ => hone c]
  exact Finset.prod_coe_sort C fun c => ∫ cell, G c cell ∂cellLaw rate F

/-- **The parts of a period in the cells add up to the period**: the lengths
of the parts of the period from `a` to `b` that lie in each cell add up to
`b - a`. -/
theorem sum_volume_cells {a b : ℝ} (hab : a ≤ b) {C : Finset ℤ}
    (hC : Finset.Icc ⌊a⌋ ⌊b⌋ ⊆ C) :
    ∑ c ∈ C, (volume (Set.Ioc a b ∩ Set.Ico (c : ℝ) (c + 1))).toReal = b - a := by
  have hdisj : (↑C : Set ℤ).PairwiseDisjoint
      fun c : ℤ => Set.Ioc a b ∩ Set.Ico (c : ℝ) (c + 1) := by
    intro c _ c' _ hcc
    refine Set.disjoint_left.mpr fun x hx hx' => hcc ?_
    have h1 : ⌊x⌋ = c := Int.floor_eq_iff.mpr ⟨hx.2.1, hx.2.2⟩
    have h2 : ⌊x⌋ = c' := Int.floor_eq_iff.mpr ⟨hx'.2.1, hx'.2.2⟩
    exact h1.symm.trans h2
  have hunion : (⋃ c ∈ C, Set.Ioc a b ∩ Set.Ico (c : ℝ) (c + 1)) = Set.Ioc a b := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, -, hxc⟩ := Set.mem_iUnion₂.mp hx
      exact hxc.1
    · intro hx
      refine Set.mem_iUnion₂.mpr ⟨⌊x⌋, hC (Finset.mem_Icc.mpr
        ⟨Int.floor_le_floor hx.1.le, Int.floor_le_floor hx.2⟩), hx, Int.floor_le x,
        Int.lt_floor_add_one x⟩
  have hsum := measure_biUnion_finset (μ := (volume : Measure ℝ)) hdisj
    (fun c _ => measurableSet_Ioc.inter measurableSet_Ico)
  rw [hunion, Real.volume_Ioc] at hsum
  have hfin : ∀ c ∈ C, volume (Set.Ioc a b ∩ Set.Ico (c : ℝ) (c + 1)) ≠ ⊤ := fun c _ =>
    ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_left)
  rw [← ENNReal.toReal_sum hfin, ← hsum, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- The probability that a pause of cell `c` begins after `a` and not after
`b` is the length of the part of that period in the cell. -/
theorem unitLaw_pauseStart (c : ℤ) (a b : ℝ) :
    unitLaw {u | a < pauseStart c u ∧ pauseStart c u ≤ b}
      = volume (Set.Ioc a b ∩ Set.Ico (c : ℝ) (c + 1)) := by
  have hmeas : MeasurableSet {u : ℝ | a < pauseStart c u ∧ pauseStart c u ≤ b} := by
    have hp : Measurable (pauseStart c) := measurable_const.add measurable_fract
    exact (measurableSet_lt measurable_const hp).inter (measurableSet_le hp measurable_const)
  unfold unitLaw
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | a < pauseStart c u ∧ pauseStart c u ≤ b} ∩ Set.Ico 0 1
      = (fun u : ℝ => (c : ℝ) + u) ⁻¹' (Set.Ioc a b ∩ Set.Ico (c : ℝ) (c + 1)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_preimage, Set.mem_Ioc,
      pauseStart]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      rw [Int.fract_eq_self.mpr ⟨h3, h4⟩] at h1 h2
      exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have h0 : 0 ≤ u := by linarith
      have h1' : u < 1 := by linarith
      rw [Int.fract_eq_self.mpr ⟨h0, h1'⟩]
      exact ⟨⟨h1, h2⟩, h0, h1'⟩
  rw [hset, measure_preimage_add]

section Step

variable {ι : Type} [Fintype ι]

/-- For periods `(a i, b i]` and numbers `θ i`: `θ i` times the length of a
pause of cell `c` that begins in period `i`, summed over the periods. -/
def stepMark (c : ℤ) (a b θ : ι → ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑ i, θ i * markIn c (a i) (b i) z

theorem measurable_stepMark (c : ℤ) (a b θ : ι → ℝ) : Measurable (stepMark c a b θ) :=
  Finset.measurable_sum (f := fun i (z : ℝ × ℝ) => θ i * markIn c (a i) (b i) z) _
    fun i _ => (measurable_markIn c (a i) (b i)).const_mul (θ i)

/-- A pause begins in at most one of periods that do not overlap. -/
theorem cexp_stepMark_sub_one (c : ℤ) {a b : ι → ℝ} (θ : ι → ℝ)
    (hdisj : ∀ i j, i ≠ j → ∀ p : ℝ, ¬ ((a i < p ∧ p ≤ b i) ∧ (a j < p ∧ p ≤ b j)))
    (z : ℝ × ℝ) :
    cexp (stepMark c a b θ z * I) - 1
      = ∑ i, {u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i}.indicator
            (fun _ => (1 : ℂ)) z.1
          * (cexp ((θ i * max z.2 0 : ℝ) * I) - 1) := by
  classical
  by_cases hex : ∃ i, a i < pauseStart c z.1 ∧ pauseStart c z.1 ≤ b i
  · obtain ⟨i₀, hi₀⟩ := hex
    have hother : ∀ i, i ≠ i₀ → ¬ (a i < pauseStart c z.1 ∧ pauseStart c z.1 ≤ b i) :=
      fun i hi h => hdisj i i₀ hi _ ⟨h, hi₀⟩
    have hstep : stepMark c a b θ z = θ i₀ * max z.2 0 := by
      unfold stepMark
      rw [Finset.sum_eq_single i₀]
      · unfold markIn
        rw [ite_eq_left hi₀]
      · intro i _ hi
        unfold markIn
        rw [ite_eq_right (hother i hi), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hstep, Finset.sum_eq_single i₀]
    · rw [Set.indicator_of_mem (show z.1 ∈ {u : ℝ | a i₀ < pauseStart c u
        ∧ pauseStart c u ≤ b i₀} from hi₀), one_mul]
    · intro i _ hi
      rw [Set.indicator_of_notMem (show z.1 ∉ {u : ℝ | a i < pauseStart c u
        ∧ pauseStart c u ≤ b i} from hother i hi), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hnone : ∀ i, ¬ (a i < pauseStart c z.1 ∧ pauseStart c z.1 ≤ b i) :=
      fun i h => hex ⟨i, h⟩
    have hstep : stepMark c a b θ z = 0 := by
      unfold stepMark
      refine Finset.sum_eq_zero fun i _ => ?_
      unfold markIn
      rw [ite_eq_right (hnone i), mul_zero]
    rw [hstep]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [Set.indicator_of_notMem (show z.1 ∉ {u : ℝ | a i < pauseStart c u
      ∧ pauseStart c u ≤ b i} from hnone i), zero_mul]

/-- **One pause.** For periods that do not overlap, the mean of
`exp (i * s) - 1`, where `s` is `stepMark` of one pause of cell `c`, is the
sum over the periods of the length of the part of the period in the cell,
times `φ (θ i) - 1`, where `φ` is the characteristic function of the law of
the lengths. -/
theorem integral_cexp_stepMark (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) (c : ℤ) {a b : ι → ℝ} (θ : ι → ℝ)
    (hdisj : ∀ i j, i ≠ j → ∀ p : ℝ, ¬ ((a i < p ∧ p ≤ b i) ∧ (a j < p ∧ p ≤ b j))) :
    ∫ z, cexp (stepMark c a b θ z * I) ∂markLaw F - 1
      = ∑ i, ((volume (Set.Ioc (a i) (b i) ∩ Set.Ico (c : ℝ) (c + 1))).toReal : ℂ)
          * (charFun F (θ i) - 1) := by
  have hmeasS : ∀ i, MeasurableSet {u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i} := by
    intro i
    have hp : Measurable (pauseStart c) := measurable_const.add measurable_fract
    exact (measurableSet_lt measurable_const hp).inter (measurableSet_le hp measurable_const)
  have hnorm : ∀ x : ℝ, ‖cexp ((x : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I
  -- The mean of `exp (i * s)`, less one, is the mean of `exp (i * s) - 1`.
  have hint1 : Integrable (fun z => cexp (stepMark c a b θ z * I)) (markLaw F) := by
    have hm := measurable_stepMark c a b θ
    exact (integrable_const (1 : ℝ)).mono (by fun_prop)
      (Filter.Eventually.of_forall fun z => by rw [hnorm, norm_one])
  have hsub : ∫ z, cexp (stepMark c a b θ z * I) ∂markLaw F - 1
      = ∫ z, (cexp (stepMark c a b θ z * I) - 1) ∂markLaw F := by
    rw [integral_sub hint1 (integrable_const 1), integral_const]
    simp
  rw [hsub, integral_congr_ae (Filter.Eventually.of_forall
    fun z => cexp_stepMark_sub_one c θ hdisj z)]
  -- Each period on its own.
  have hterm : ∀ i, ∫ z : ℝ × ℝ, {u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i}.indicator
          (fun _ => (1 : ℂ)) z.1 * (cexp ((θ i * max z.2 0 : ℝ) * I) - 1) ∂markLaw F
      = ((volume (Set.Ioc (a i) (b i) ∩ Set.Ico (c : ℝ) (c + 1))).toReal : ℂ)
          * (charFun F (θ i) - 1) := by
    intro i
    unfold markLaw
    rw [integral_prod_mul
      (f := {u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i}.indicator fun _ => (1 : ℂ))
      (g := fun l : ℝ => cexp ((θ i * max l 0 : ℝ) * I) - 1)]
    congr 1
    · rw [integral_indicator_const _ (hmeasS i), measureReal_def, unitLaw_pauseStart]
      simp
    · have hint2 : Integrable (fun l : ℝ => cexp ((θ i * max l 0 : ℝ) * I)) F :=
        (integrable_const (1 : ℝ)).mono (by fun_prop)
          (Filter.Eventually.of_forall fun l => by rw [hnorm, norm_one])
      rw [integral_sub hint2 (integrable_const 1), integral_const, charFun_apply_real]
      have hpos : ∀ᵐ l ∂F, 0 < l := by
        rw [ae_iff]
        simpa [Set.Iic] using hF
      have hae : (fun l : ℝ => cexp ((θ i * max l 0 : ℝ) * I))
          =ᵐ[F] fun l => cexp (θ i * l * I) := by
        filter_upwards [hpos] with l hl
        rw [max_eq_left hl.le]
        push_cast
        rfl
      rw [integral_congr_ae hae]
      simp
  have hint3 : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun z : ℝ × ℝ =>
      {u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i}.indicator (fun _ => (1 : ℂ)) z.1
        * (cexp ((θ i * max z.2 0 : ℝ) * I) - 1)) (markLaw F) := by
    intro i _
    have hmi : Measurable fun z : ℝ × ℝ =>
        {u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i}.indicator
          (fun _ => (1 : ℂ)) z.1 :=
      (measurable_const.indicator (hmeasS i)).comp measurable_fst
    refine (integrable_const (2 : ℝ)).mono (by fun_prop)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 : ‖{u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i}.indicator
        (fun _ => (1 : ℂ)) z.1‖ ≤ 1 := by
      by_cases hz : z.1 ∈ {u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i}
      · rw [Set.indicator_of_mem hz, norm_one]
      · rw [Set.indicator_of_notMem hz, norm_zero]
        exact zero_le_one
    have h2 : ‖cexp ((θ i * max z.2 0 : ℝ) * I) - 1‖ ≤ 2 := by
      calc ‖cexp ((θ i * max z.2 0 : ℝ) * I) - 1‖
          ≤ ‖cexp ((θ i * max z.2 0 : ℝ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hnorm, norm_one]; norm_num
    calc ‖{u : ℝ | a i < pauseStart c u ∧ pauseStart c u ≤ b i}.indicator
          (fun _ => (1 : ℂ)) z.1‖ * ‖cexp ((θ i * max z.2 0 : ℝ) * I) - 1‖
        ≤ 1 * 2 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 2 := one_mul 2
  rw [integral_finsetSum _ hint3]
  exact Finset.sum_congr rfl fun i _ => hterm i

/-- **The paused time of periods that do not overlap.** The mean of
`exp (i * S)`, where `S` is the sum over the periods of `θ i` times the
paused time that begins in period `i`, is the product over the periods of
`exp (rate * (b i - a i) * (φ (θ i) - 1))`. -/
theorem integral_cexp_pausedBetween (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i) (θ : ι → ℝ)
    (hdisj : ∀ i j, i ≠ j → ∀ p : ℝ, ¬ ((a i < p ∧ p ≤ b i) ∧ (a j < p ∧ p ≤ b j))) :
    ∫ ω, cexp ((∑ i, θ i * pausedBetween (a i) (b i) ω : ℝ) * I) ∂cellsLaw rate F
      = ∏ i, cexp ((rate : ℝ) * (b i - a i) * (charFun F (θ i) - 1)) := by
  classical
  -- A finite set of cells that holds every cell of every period.
  let C : Finset ℤ := Finset.univ.biUnion fun i : ι => Finset.Icc ⌊a i⌋ ⌊b i⌋
  have hC : ∀ i, Finset.Icc ⌊a i⌋ ⌊b i⌋ ⊆ C := fun i =>
    Finset.subset_biUnion_of_mem (fun i : ι => Finset.Icc ⌊a i⌋ ⌊b i⌋) (Finset.mem_univ i)
  have hsum : ∀ ω : Cells, ∑ i, θ i * pausedBetween (a i) (b i) ω
      = ∑ c ∈ C, cellSum (stepMark c a b θ) (ω c) := by
    intro ω
    have h1 : ∀ i, θ i * pausedBetween (a i) (b i) ω
        = ∑ c ∈ C, θ i * cellSum (markIn c (a i) (b i)) (ω c) := fun i => by
      rw [pausedBetween_eq_sum (hC i), Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold cellSum stepMark
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  have hexp : ∀ ω : Cells, cexp ((∑ i, θ i * pausedBetween (a i) (b i) ω : ℝ) * I)
      = ∏ c ∈ C, cexp (cellSum (stepMark c a b θ) (ω c) * I) := by
    intro ω
    rw [hsum ω, ← Complex.exp_sum, Complex.ofReal_sum, Finset.sum_mul]
  have hmeasG : ∀ c : ℤ, Measurable fun cell : Cell =>
      cexp (cellSum (stepMark c a b θ) cell * I) := by
    intro c
    have := measurable_cellSum (measurable_stepMark c a b θ)
    fun_prop
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_prod_cells rate F C hmeasG]
  have hcell : ∀ c : ℤ, ∫ cell, cexp (cellSum (stepMark c a b θ) cell * I) ∂cellLaw rate F
      = cexp ((rate : ℝ) * ∑ i, ((volume (Set.Ioc (a i) (b i)
          ∩ Set.Ico (c : ℝ) (c + 1))).toReal : ℂ) * (charFun F (θ i) - 1)) := by
    intro c
    rw [integral_cexp_cellSum rate F (measurable_stepMark c a b θ),
      integral_cexp_stepMark F hF c θ hdisj]
  rw [Finset.prod_congr rfl fun c _ => hcell c, ← Complex.exp_sum, ← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_volume_cells (hab i) (hC i)]
  push_cast
  ring

end Step

/-! ## The two properties that the model asks for -/

/-- **The paused time that begins in a period has the law `pauseLaw`**, for
the mean number of pauses that begin in the period and the law of their
lengths. -/
theorem hasLaw_pausedBetween (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) {s t : ℝ} (hst : s ≤ t) :
    HasLaw (pausedBetween s t) (pauseLaw (Real.toNNReal (rate * (t - s))) F)
      (cellsLaw rate F) where
  aemeasurable := (measurable_pausedBetween s t).aemeasurable
  map_eq := by
    refine Measure.ext_of_charFun ?_
    funext θ
    have h := integral_cexp_pausedBetween rate F hF (ι := Unit) (a := fun _ => s)
      (b := fun _ => t) (fun _ => hst) (fun _ => θ)
      (fun i j hij => absurd (Subsingleton.elim i j) hij)
    simp only [Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton] at h
    rw [charFun_apply_real, integral_map (measurable_pausedBetween s t).aemeasurable
      (by fun_prop), charFun_pauseLaw,
      Real.coe_toNNReal _ (mul_nonneg rate.coe_nonneg (sub_nonneg.mpr hst))]
    calc ∫ ω, cexp (θ * pausedBetween s t ω * I) ∂cellsLaw rate F
        = ∫ ω, cexp ((θ * pausedBetween s t ω : ℝ) * I) ∂cellsLaw rate F := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          push_cast
          rfl
      _ = cexp ((rate : ℝ) * (t - s) * (charFun F θ - 1)) := h
      _ = cexp (((rate * (t - s) : ℝ) : ℂ) * (charFun F θ - 1)) := by
          push_cast
          rfl

/-- **The paused time that begins between two true times has the law
`pauseLaw`.** -/
theorem hasLaw_pausedPath_sub (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) {s t : ℝ} (hst : s ≤ t) :
    HasLaw (fun ω : Cells => pausedPath ω t - pausedPath ω s)
      (pauseLaw (Real.toNNReal (rate * (t - s))) F) (cellsLaw rate F) := by
  have h : (fun ω : Cells => pausedPath ω t - pausedPath ω s) = pausedBetween s t :=
    funext fun ω => pausedPath_sub hst ω
  rw [h]
  exact hasLaw_pausedBetween rate F hF hst

/-- **The paused time that begins in periods that do not overlap is
independent.** -/
theorem hasIndepIncrements_pausedPath (rate : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iic 0) = 0) :
    HasIndepIncrements (fun t (ω : Cells) => pausedPath ω t) (cellsLaw rate F) := by
  intro n t ht
  have hle : ∀ i : Fin n, t i.castSucc ≤ t i.succ := fun i => ht (Fin.castSucc_lt_succ).le
  have hfam : (fun (i : Fin n) (ω : Cells) =>
        pausedPath ω (t i.succ) - pausedPath ω (t i.castSucc))
      = fun i ω => pausedBetween (t i.castSucc) (t i.succ) ω := by
    funext i ω
    exact pausedPath_sub (hle i) ω
  rw [hfam]
  have hdisj : ∀ i j : Fin n, i ≠ j → ∀ p : ℝ,
      ¬ ((t i.castSucc < p ∧ p ≤ t i.succ) ∧ (t j.castSucc < p ∧ p ≤ t j.succ)) := by
    rintro i j hij p ⟨⟨h1, h2⟩, h3, h4⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have := ht (Fin.succ_le_castSucc_iff.mpr hlt)
      linarith
    · have := ht (Fin.succ_le_castSucc_iff.mpr hgt)
      linarith
  rw [iIndepFun_iff_charFun_pi fun i => (measurable_pausedBetween _ _).aemeasurable]
  intro τ
  have hjoint := integral_cexp_pausedBetween rate F hF hle (fun i => τ i) hdisj
  have hmarg : ∀ i : Fin n,
      charFun ((cellsLaw rate F).map (pausedBetween (t i.castSucc) (t i.succ))) (τ i)
        = cexp ((rate : ℝ) * (t i.succ - t i.castSucc) * (charFun F (τ i) - 1)) := by
    intro i
    rw [(hasLaw_pausedBetween rate F hF (hle i)).map_eq, charFun_pauseLaw,
      Real.coe_toNNReal _ (mul_nonneg rate.coe_nonneg (sub_nonneg.mpr (hle i)))]
    push_cast
    rfl
  have hvec : Measurable fun ω : Cells =>
      WithLp.toLp 2 fun i : Fin n => pausedBetween (t i.castSucc) (t i.succ) ω :=
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (Measurable.of_eval fun i => measurable_pausedBetween _ _)
  rw [Finset.prod_congr rfl fun i _ => hmarg i, ← hjoint, charFun_apply,
    integral_map hvec.aemeasurable (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

end Unisono.Spec.GenerativeWorld
