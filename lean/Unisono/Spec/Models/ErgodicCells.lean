/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Dynamics.BirkhoffSum.Integrable
public import Mathlib.Dynamics.BirkhoffSum.Maximal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

/-!
# Long-run averages over independent cells

The random process of pauses is built from independent cells of true time,
all with one law (`Unisono.Spec.Models.PauseProcess`). A quantity such as the
backlog of a link at a true time depends on all earlier cells, so the values
of such a quantity at different times are not independent, and the strong law
of large numbers does not apply to them. This file proves what replaces it:
the long-run average of a bounded quantity, read at equally spaced times, is
its mean, in almost every outcome.

* `tendsto_birkhoffAverage_ae`: the ergodic theorem for a bounded function.
  For a map `T` that keeps the measure and is ergodic, the averages of
  `g (x)`, `g (T x)`, `g (T (T x))`, ... converge to the mean of `g`, for
  almost every `x`. The proof is the usual one from the maximal ergodic
  theorem of Mathlib.
* `ae_frequently_mem_of_ergodic`: almost every orbit of such a map enters a
  set of positive measure again and again.
* `shiftCells`: the outcomes of the cells, moved by a number of cells. Moving
  the cells keeps the law of independent cells with one law
  (`measurePreserving_shiftCells`) and is ergodic (`ergodic_shiftCells`). The
  proof of ergodicity: a set that depends on finitely many cells is
  independent of itself moved far enough
  (`measure_inter_preimage_shiftCells`), every measurable set is close in
  measure to such a set, and so a set that the move leaves in place has a
  measure equal to its own square (`preErgodic_of_mixing`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal symmDiff

/-! ## Long-run averages along an ergodic map -/

section Averages

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {T : α → α} {g : α → ℝ}
  {C a : ℝ}

/-- Starting one step later along the orbit changes the average of a bounded
function over `n` steps by at most `2 C / n`. -/
theorem abs_birkhoffAverage_apply_sub_le (hC : ∀ x, |g x| ≤ C) (n : ℕ) (x : α) :
    |birkhoffAverage ℝ T g n (T x) - birkhoffAverage ℝ T g n x| ≤ 2 * C / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hsum : birkhoffSum T g n (T x) = birkhoffSum T g n x + g (T^[n] x) - g x := by
    have h1 := birkhoffSum_succ_apply T g n x
    have h2 := birkhoffSum_succ_apply' T g n x
    linarith
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hdiff : birkhoffAverage ℝ T g n (T x) - birkhoffAverage ℝ T g n x
      = (g (T^[n] x) - g x) / n := by
    simp only [birkhoffAverage, smul_eq_mul]
    rw [hsum]
    ring
  rw [hdiff, abs_div, abs_of_pos hn']
  have h1 := abs_le.mp (hC (T^[n] x))
  have h2 := abs_le.mp (hC x)
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) hn'.le

/-- If two sequences differ by at most `c / n` at index `n`, and one exceeds
`a + ε` again and again, then the other exceeds `a + ε / 2` again and
again. -/
theorem frequently_lt_of_abs_sub_le {u v : ℕ → ℝ} {c a ε : ℝ} (hε : 0 < ε)
    (huv : ∀ n : ℕ, |u n - v n| ≤ c / n) (h : ∃ᶠ n in atTop, a + ε < u n) :
    ∃ᶠ n in atTop, a + ε / 2 < v n := by
  have hev : ∀ᶠ n : ℕ in atTop, c / n < ε / 2 :=
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat c)).2 _ (half_pos hε)
  refine (h.and_eventually hev).mono fun n hn => ?_
  have := abs_le.mp (huv n)
  linarith [hn.1, hn.2]

/-- The points whose averages of `g` along the orbit exceed `a` by one
positive amount again and again. -/
def frequentlyAbove (T : α → α) (g : α → ℝ) (a : ℝ) : Set α :=
  {x | ∃ ε > 0, ∃ᶠ n in atTop, a + ε < birkhoffAverage ℝ T g n x}

/-- The map sends the set `frequentlyAbove` onto itself, when `g` is
bounded. -/
theorem preimage_frequentlyAbove (hC : ∀ x, |g x| ≤ C) (a : ℝ) :
    T ⁻¹' frequentlyAbove T g a = frequentlyAbove T g a := by
  ext x
  constructor
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε / 2, half_pos hε, frequently_lt_of_abs_sub_le hε
      (fun n => abs_birkhoffAverage_apply_sub_le hC n x) h⟩
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε / 2, half_pos hε, frequently_lt_of_abs_sub_le (c := 2 * C) hε (fun n => ?_) h⟩
    rw [abs_sub_comm]
    exact abs_birkhoffAverage_apply_sub_le hC n x

theorem measurableSet_frequentlyAbove (hT : Measurable T) (hg : Measurable g) (a : ℝ) :
    MeasurableSet (frequentlyAbove T g a) := by
  have h : frequentlyAbove T g a
      = ⋃ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ _ : N ≤ n,
          {x | a + 1 / ((k : ℝ) + 1) < birkhoffAverage ℝ T g n x} := by
    ext x
    constructor
    · rintro ⟨ε, hε, h⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iInter.mpr fun N => ?_⟩
      obtain ⟨n, hn, hlt⟩ := (frequently_atTop.mp h) N
      exact Set.mem_iUnion₂.mpr ⟨n, hn, show a + 1 / ((k : ℝ) + 1) < _ by linarith⟩
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      refine ⟨1 / ((k : ℝ) + 1), by positivity, frequently_atTop.mpr fun N => ?_⟩
      obtain ⟨n, hn, hlt⟩ := Set.mem_iUnion₂.mp (Set.mem_iInter.mp hk N)
      exact ⟨n, hn, hlt⟩
  rw [h]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const (measurable_birkhoffAverage hT hg)

/-- A set that the map sends onto itself holds a point if and only if it
holds the points of its orbit. -/
theorem iterate_mem_iff_of_preimage_eq {B : Set α} (hB : T ⁻¹' B = B) (n : ℕ) (x : α) :
    T^[n] x ∈ B ↔ x ∈ B := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    exact Set.ext_iff.mp hB x

/-- On a set that the map sends onto itself, the sums along an orbit of a
function cut off outside the set are the sums of the function, cut off
outside the set. -/
theorem birkhoffSum_indicator_of_preimage_eq {B : Set α} (hB : T ⁻¹' B = B) (h : α → ℝ)
    (n : ℕ) (x : α) :
    birkhoffSum T (B.indicator h) n x = B.indicator (birkhoffSum T h n) x := by
  by_cases hx : x ∈ B
  · rw [Set.indicator_of_mem hx]
    exact Finset.sum_congr rfl fun k _ =>
      Set.indicator_of_mem ((iterate_mem_iff_of_preimage_eq hB k x).mpr hx) h
  · rw [Set.indicator_of_notMem hx]
    exact Finset.sum_eq_zero fun k _ =>
      Set.indicator_of_notMem (fun hk => hx ((iterate_mem_iff_of_preimage_eq hB k x).mp hk)) h

/-- **Averages along an ergodic map do not stay above the mean.** For a
bounded function `g` with mean below `a`, almost no point has averages along
its orbit that exceed `a` by one positive amount again and again. -/
theorem measure_frequentlyAbove_eq_zero [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    (hg : Measurable g) (hC : ∀ x, |g x| ≤ C) (ha : ∫ x, g x ∂μ < a) :
    μ (frequentlyAbove T g a) = 0 := by
  have hBinv : T ⁻¹' frequentlyAbove T g a = frequentlyAbove T g a :=
    preimage_frequentlyAbove hC a
  have hBmeas : MeasurableSet (frequentlyAbove T g a) :=
    measurableSet_frequentlyAbove hT.measurable hg a
  have hgint : Integrable g μ :=
    Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hhint : Integrable (fun x => g x - a) μ := hgint.sub (integrable_const a)
  -- The sums of `g - a`, cut off outside the set, have a positive value exactly on the set.
  have hset : {x | 0 < birkhoffSumSup T ((frequentlyAbove T g a).indicator fun x => g x - a) x}
      = frequentlyAbove T g a := by
    ext x
    constructor
    · intro hx
      by_contra hxB
      have hzero : birkhoffSumSup T ((frequentlyAbove T g a).indicator fun x => g x - a) x
          = 0 := by
        unfold birkhoffSumSup
        have h0 : ∀ n, birkhoffSum T ((frequentlyAbove T g a).indicator fun x => g x - a) n x
            = 0 := fun n => by
          rw [birkhoffSum_indicator_of_preimage_eq hBinv, Set.indicator_of_notMem hxB]
        simp [h0]
      have hx' : (0 : EReal)
          < birkhoffSumSup T ((frequentlyAbove T g a).indicator fun x => g x - a) x := hx
      rw [hzero] at hx'
      exact lt_irrefl _ hx'
    · intro hx
      obtain ⟨ε, hε, hfreq⟩ := hx
      obtain ⟨n, hn, hlt⟩ := (frequently_atTop.mp hfreq) 1
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hsum : birkhoffSum T (fun x => g x - a) n x = birkhoffSum T g n x - n * a := by
        simp only [birkhoffSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
      have hpos : 0 < birkhoffSum T (fun x => g x - a) n x := by
        rw [hsum]
        have h1 : a + ε < (n : ℝ)⁻¹ * birkhoffSum T g n x := hlt
        have h2 := mul_lt_mul_of_pos_left h1 hn'
        rw [mul_inv_cancel_left₀ hn'.ne'] at h2
        nlinarith [mul_pos hn' hε]
      show (0 : EReal)
        < birkhoffSumSup T ((frequentlyAbove T g a).indicator fun x => g x - a) x
      unfold birkhoffSumSup
      refine lt_of_lt_of_le ?_ (le_iSup _ n)
      rw [birkhoffSum_indicator_of_preimage_eq hBinv,
        Set.indicator_of_mem (show x ∈ frequentlyAbove T g a from ⟨ε, hε, hfreq⟩)]
      exact_mod_cast hpos
  have hmax := setIntegral_birkhoffSumSup_nonneg μ hT.toMeasurePreserving
    (hhint.indicator hBmeas)
  rw [hset, setIntegral_indicator hBmeas, Set.inter_self] at hmax
  rcases hT.toPreErgodic.prob_eq_zero_or_one hBmeas.nullMeasurableSet
    (by rw [hBinv]) with h0 | h1
  · exact h0
  · exfalso
    have hae : ∀ᵐ x ∂μ, x ∈ frequentlyAbove T g a :=
      ae_iff.mpr ((prob_compl_eq_zero_iff hBmeas).mpr h1)
    have hfull : ∫ x in frequentlyAbove T g a, (g x - a) ∂μ = ∫ x, (g x - a) ∂μ :=
      setIntegral_eq_integral_of_ae_compl_eq_zero
        (by filter_upwards [hae] with x hx hx' using absurd hx hx')
    rw [hfull, integral_sub hgint (integrable_const a)] at hmax
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hmax
    linarith

/-- For a bounded function `g` with mean below `a`, the averages of `g` along
almost every orbit of an ergodic map are at most `a` from some step on. -/
theorem ae_eventually_birkhoffAverage_le [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    (hg : Measurable g) (hC : ∀ x, |g x| ≤ C) (ha : ∫ x, g x ∂μ < a) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, birkhoffAverage ℝ T g n x ≤ a := by
  have hb : ∫ x, g x ∂μ < (∫ x, g x ∂μ + a) / 2 := by linarith
  have h0 := measure_frequentlyAbove_eq_zero hT hg hC hb
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
  by_contra hcon
  rw [not_eventually] at hcon
  refine hx ⟨(a - ∫ x, g x ∂μ) / 2, by linarith, hcon.mono fun n hn => ?_⟩
  have := not_le.mp hn
  linarith

/-- **The ergodic theorem for a bounded function.** For a map that keeps the
measure and is ergodic, the averages of a bounded measurable function along
almost every orbit converge to the mean of the function. -/
theorem tendsto_birkhoffAverage_ae [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    (hg : Measurable g) (hC : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hup : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      birkhoffAverage ℝ T g n x ≤ ∫ x, g x ∂μ + 1 / ((k : ℝ) + 1) := fun k =>
    ae_eventually_birkhoffAverage_le hT hg hC
      (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          linarith)
  have hlow : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      birkhoffAverage ℝ T (fun x => -g x) n x ≤ -∫ x, g x ∂μ + 1 / ((k : ℝ) + 1) := fun k =>
    ae_eventually_birkhoffAverage_le hT hg.neg (fun x => by rw [abs_neg]; exact hC x)
      (by rw [integral_neg]
          have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          linarith)
  filter_upwards [ae_all_iff.mpr hup, ae_all_iff.mpr hlow] with x hx1 hx2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hx1 k)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hx2 k)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
  have hneg : birkhoffAverage ℝ T (fun x => -g x) n x = -birkhoffAverage ℝ T g n x := by
    simp only [birkhoffAverage, birkhoffSum, Finset.sum_neg_distrib, smul_neg]
  rw [hneg] at h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- A property holds for `n + 1` again and again exactly when it holds for
`n` again and again. -/
theorem frequently_succ_iff {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p (n + 1)) ↔ ∃ᶠ n in atTop, p n := by
  simp only [frequently_atTop]
  constructor
  · intro h a
    obtain ⟨b, hb, hp⟩ := h a
    exact ⟨b + 1, by omega, hp⟩
  · intro h a
    obtain ⟨b, hb, hp⟩ := h (a + 1)
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    exact ⟨c, by omega, hp⟩

/-- **Almost every orbit of an ergodic map enters a set of positive measure
again and again.** -/
theorem ae_frequently_mem_of_ergodic [IsProbabilityMeasure μ] (hT : Ergodic T μ) {A : Set α}
    (hA : MeasurableSet A) (hpos : μ A ≠ 0) :
    ∀ᵐ x ∂μ, ∃ᶠ n in atTop, T^[n] x ∈ A := by
  -- The points whose orbit stays outside `A` from step `M` on.
  let late : ℕ → Set α := fun M => {x | ∀ n, M ≤ n → T^[n] x ∉ A}
  have hlate_meas : ∀ M, MeasurableSet (late M) := fun M => by
    have h : late M = ⋂ n : ℕ, ⋂ _ : M ≤ n, (T^[n] ⁻¹' A)ᶜ := by
      ext x
      simp only [late, Set.mem_iInter]
      rfl
    rw [h]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      ((hT.measurable.iterate n) hA).compl
  have hlate_mono : Monotone late := fun M M' hMM' x hx n hn => hx n (hMM'.trans hn)
  have hbad : {x | ¬ ∃ᶠ n in atTop, T^[n] x ∈ A} = ⋃ M, late M := by
    ext x
    simp only [late, Set.mem_iUnion]
    constructor
    · intro hx
      have hx' : ∀ᶠ n in atTop, T^[n] x ∉ A := not_frequently.mp hx
      obtain ⟨M, hM⟩ := eventually_atTop.mp hx'
      exact ⟨M, hM⟩
    · rintro ⟨M, hM⟩
      exact not_frequently.mpr (eventually_atTop.mpr ⟨M, hM⟩)
  have hbad_meas : MeasurableSet {x | ¬ ∃ᶠ n in atTop, T^[n] x ∈ A} := by
    rw [hbad]
    exact MeasurableSet.iUnion hlate_meas
  have hbad_inv : T ⁻¹' {x | ¬ ∃ᶠ n in atTop, T^[n] x ∈ A}
      = {x | ¬ ∃ᶠ n in atTop, T^[n] x ∈ A} := by
    ext x
    show (¬ ∃ᶠ n in atTop, T^[n] (T x) ∈ A) ↔ ¬ ∃ᶠ n in atTop, T^[n] x ∈ A
    rw [not_iff_not]
    exact frequently_succ_iff (p := fun n => T^[n] x ∈ A)
  -- The measure of the bad set is at most that of the complement of `A`.
  have hle : μ {x | ¬ ∃ᶠ n in atTop, T^[n] x ∈ A} ≤ μ Aᶜ := by
    rw [hbad]
    refine le_of_tendsto' (tendsto_measure_iUnion_atTop hlate_mono) fun M => ?_
    have hsub : late M ⊆ T^[M] ⁻¹' Aᶜ := fun x hx => hx M le_rfl
    calc μ (late M) ≤ μ (T^[M] ⁻¹' Aᶜ) := measure_mono hsub
      _ = μ Aᶜ := (hT.toMeasurePreserving.iterate M).measure_preimage
          hA.compl.nullMeasurableSet
  have hlt : μ Aᶜ < 1 := by
    rw [prob_compl_eq_one_sub hA]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos
  rcases hT.toPreErgodic.prob_eq_zero_or_one hbad_meas.nullMeasurableSet
    (by rw [hbad_inv]) with h0 | h1
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
    exact not_not.mp hx
  · exact absurd (h1 ▸ hle) (not_le.mpr hlt)

end Averages

/-! ## A map that mixes the sets of a generating ring is ergodic -/

section Mixing

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {T : α → α}

/-- **A map that mixes the sets of a generating ring is ergodic.** Let `T`
keep a probability measure, and let the measurable sets be generated by a
ring of sets. Suppose that every set `A` of the ring is independent of its
preimage under enough steps of `T`. Then every measurable set that `T` sends
onto itself has measure zero or one. -/
theorem preErgodic_of_mixing [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {𝒞 : Set (Set α)} (hring : IsSetRing 𝒞) (huniv : Set.univ ∈ 𝒞)
    (hgen : mα = MeasurableSpace.generateFrom 𝒞) (hmeas : ∀ A ∈ 𝒞, MeasurableSet A)
    (hmix : ∀ A ∈ 𝒞, ∃ N : ℕ, ∀ n ≥ N, μ (A ∩ T^[n] ⁻¹' A) = μ A * μ A) :
    PreErgodic T μ := by
  refine PreErgodic.of_preimage_eq_of_measurable hT.measurable hT.quasiMeasurePreserving
    fun s hs hinv => ?_
  -- The measure of `s` equals its own square.
  have hsq : μ.real s = μ.real s * μ.real s := by
    refine eq_of_forall_dist_le fun ε hε => ?_
    have hε4 : 0 < ε / 4 := by positivity
    obtain ⟨t, ht, hts⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ) hring
      ⟨{Set.univ}, Set.countable_singleton _, Set.singleton_subset_iff.mpr huniv, by simp⟩
      hgen hs (ENNReal.ofReal_pos.mpr hε4)
    have htm := hmeas t ht
    obtain ⟨N, hN⟩ := hmix t ht
    have hd : μ.real (t ∆ s) ≤ ε / 4 := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hts.le
      rwa [ENNReal.toReal_ofReal hε4.le] at h
    have h1 : |μ.real t - μ.real s| ≤ ε / 4 :=
      (abs_measureReal_sub_le_measureReal_symmDiff htm.nullMeasurableSet
        hs.nullMeasurableSet).trans hd
    have hinvN : T^[N] ⁻¹' s = s := Set.ext fun x => iterate_mem_iff_of_preimage_eq hinv N x
    have hpre : μ.real ((T^[N] ⁻¹' t) ∆ (T^[N] ⁻¹' s)) ≤ ε / 4 := by
      rw [← Set.preimage_symmDiff, measureReal_def,
        (hT.iterate N).measure_preimage (htm.symmDiff hs).nullMeasurableSet]
      exact hd
    have hss : (t ∩ T^[N] ⁻¹' t) ∆ (s ∩ T^[N] ⁻¹' s)
        ⊆ (t ∆ s) ∪ ((T^[N] ⁻¹' t) ∆ (T^[N] ⁻¹' s)) := by
      intro x hx
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at hx ⊢
      tauto
    have h2 : |μ.real (t ∩ T^[N] ⁻¹' t) - μ.real s| ≤ ε / 2 := by
      have hs2 : s ∩ T^[N] ⁻¹' s = s := by rw [hinvN, Set.inter_self]
      have hm : MeasurableSet (t ∩ T^[N] ⁻¹' t) := htm.inter ((hT.measurable.iterate N) htm)
      calc |μ.real (t ∩ T^[N] ⁻¹' t) - μ.real s|
          = |μ.real (t ∩ T^[N] ⁻¹' t) - μ.real (s ∩ T^[N] ⁻¹' s)| := by rw [hs2]
        _ ≤ μ.real ((t ∩ T^[N] ⁻¹' t) ∆ (s ∩ T^[N] ⁻¹' s)) :=
            abs_measureReal_sub_le_measureReal_symmDiff hm.nullMeasurableSet
              (hs2 ▸ hs).nullMeasurableSet
        _ ≤ μ.real ((t ∆ s) ∪ ((T^[N] ⁻¹' t) ∆ (T^[N] ⁻¹' s))) := measureReal_mono hss
        _ ≤ μ.real (t ∆ s) + μ.real ((T^[N] ⁻¹' t) ∆ (T^[N] ⁻¹' s)) := measureReal_union_le _ _
        _ ≤ ε / 2 := by linarith
    have h3 : μ.real (t ∩ T^[N] ⁻¹' t) = μ.real t * μ.real t := by
      rw [measureReal_def, hN N le_rfl, ENNReal.toReal_mul]
      rfl
    rw [h3] at h2
    have hx0 : 0 ≤ μ.real s := measureReal_nonneg
    have hx1 : μ.real s ≤ 1 := measureReal_le_one
    have hy0 : 0 ≤ μ.real t := measureReal_nonneg
    have hy1 : μ.real t ≤ 1 := measureReal_le_one
    have hprod : |(μ.real t - μ.real s) * (μ.real t + μ.real s)| ≤ ε / 4 * 2 := by
      rw [abs_mul]
      exact mul_le_mul h1 (by rw [abs_of_nonneg (by linarith)]; linarith) (abs_nonneg _)
        hε4.le
    have h1' := abs_le.mp h2
    have h2' := abs_le.mp hprod
    rw [Real.dist_eq, abs_le]
    constructor <;> nlinarith
  have hcases : μ.real s = 0 ∨ μ.real s = 1 := by
    have h : μ.real s * (1 - μ.real s) = 0 := by linarith
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  rw [eventuallyEmptyOrUniv_iff]
  rcases hcases with h0 | h1
  · right
    exact measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff (μ := μ) (s := s)).mp h0)
  · left
    have hone : μ s = 1 := (ENNReal.toReal_eq_one_iff _).mp h1
    exact ae_iff.mpr ((prob_compl_eq_zero_iff hs).mpr hone)

end Mixing

/-! ## Moving independent cells -/

section Shift

variable {S : Type*} [MeasurableSpace S]

/-- The outcomes of the cells, moved by `k` cells: cell `c` of the result is
cell `c + k` of the outcome. -/
def shiftCells (k : ℤ) (ω : ℤ → S) : ℤ → S := fun c => ω (c + k)

theorem measurable_shiftCells (k : ℤ) : Measurable (shiftCells (S := S) k) :=
  measurable_pi_iff.mpr fun c => measurable_pi_apply (c + k)

omit [MeasurableSpace S] in
/-- Moving the cells `n` times by `k` moves them by `n * k`. -/
theorem iterate_shiftCells (k : ℤ) (n : ℕ) (ω : ℤ → S) :
    (shiftCells k)^[n] ω = shiftCells (n * k) ω := by
  induction n with
  | zero =>
    funext c
    simp [shiftCells]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext c
    simp only [shiftCells]
    congr 1
    push_cast
    ring

/-- **Moving the cells keeps the law of independent cells with one law.** -/
theorem measurePreserving_shiftCells (ν : Measure S) [IsProbabilityMeasure ν] (k : ℤ) :
    MeasurePreserving (shiftCells k) (Measure.infinitePi fun _ : ℤ => ν)
      (Measure.infinitePi fun _ : ℤ => ν) := by
  refine ⟨measurable_shiftCells k, ?_⟩
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hpre : shiftCells k ⁻¹' Set.pi (s : Set ℤ) t
      = Set.pi ((s.map (addRightEmbedding k) : Finset ℤ) : Set ℤ) fun c => t (c - k) := by
    ext ω
    constructor
    · intro h c hc
      obtain ⟨c', hc', rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hc)
      have h' := h c' (Finset.mem_coe.mpr hc')
      simpa [shiftCells] using h'
    · intro h c hc
      have h' := h (c + k)
        (Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨c, Finset.mem_coe.mp hc, rfl⟩))
      simpa [shiftCells] using h'
  rw [Measure.map_apply (measurable_shiftCells k)
      (MeasurableSet.pi s.countable_toSet fun c _ => ht c), hpre,
    Measure.infinitePi_pi _ (fun c _ => ht (c - k)), Finset.prod_map]
  simp

/-- **A set that depends on finitely many cells is independent of itself
moved far enough.** -/
theorem measure_inter_preimage_shiftCells (ν : Measure S) [IsProbabilityMeasure ν] {k : ℤ}
    (hk : k ≠ 0) {A : Set (ℤ → S)} (hA : A ∈ measurableCylinders fun _ : ℤ => S) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Measure.infinitePi fun _ : ℤ => ν) (A ∩ (shiftCells k)^[n] ⁻¹' A)
        = (Measure.infinitePi fun _ : ℤ => ν) A * (Measure.infinitePi fun _ : ℤ => ν) A := by
  obtain ⟨I, U, hU, rfl⟩ := (mem_measurableCylinders A).mp hA
  refine ⟨(I ×ˢ I).sup (fun p : ℤ × ℤ => (p.2 - p.1).natAbs) + 1, fun n hn => ?_⟩
  have hdisj : Disjoint I (I.map (addRightEmbedding ((n : ℤ) * k))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx'
    have hle : (addRightEmbedding ((n : ℤ) * k) i - i).natAbs
        ≤ (I ×ˢ I).sup (fun p : ℤ × ℤ => (p.2 - p.1).natAbs) :=
      Finset.le_sup (f := fun p : ℤ × ℤ => (p.2 - p.1).natAbs)
        (b := (i, addRightEmbedding ((n : ℤ) * k) i)) (Finset.mem_product.mpr ⟨hi, hx⟩)
    have hk1 : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk
    have habs : (addRightEmbedding ((n : ℤ) * k) i - i).natAbs = n * k.natAbs := by
      simp [Int.natAbs_mul]
    rw [habs] at hle
    have hnk : n ≤ n * k.natAbs := Nat.le_mul_of_pos_right n hk1
    omega
  have hind := (iIndepFun_infinitePi (P := fun _ : ℤ => ν) (X := fun _ x => x)
    (fun _ => measurable_id)).indepFun_finset I (I.map (addRightEmbedding ((n : ℤ) * k)))
      hdisj fun c => measurable_pi_apply c
  let ψ : (↥(I.map (addRightEmbedding ((n : ℤ) * k))) → S) → (↥I → S) := fun g i =>
    g ⟨(i : ℤ) + (n : ℤ) * k, Finset.mem_map.mpr ⟨i, i.2, rfl⟩⟩
  have hψ : Measurable ψ := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hmul := (hind.comp measurable_id hψ).measure_inter_preimage_eq_mul U U hU hU
  have hB : (ψ ∘ fun (ω : ℤ → S) (i : ↥(I.map (addRightEmbedding ((n : ℤ) * k)))) => ω i)
      ⁻¹' U = (shiftCells k)^[n] ⁻¹' cylinder I U := by
    ext ω
    show ψ (fun i => ω i) ∈ U ↔ I.restrict ((shiftCells k)^[n] ω) ∈ U
    rw [iterate_shiftCells]
    rfl
  rw [hB] at hmul
  have hsame : (Measure.infinitePi fun _ : ℤ => ν) ((shiftCells k)^[n] ⁻¹' cylinder I U)
      = (Measure.infinitePi fun _ : ℤ => ν) (cylinder I U) :=
    ((measurePreserving_shiftCells ν k).iterate n).measure_preimage
      (hU.cylinder (s := I)).nullMeasurableSet
  rw [hsame] at hmul
  exact hmul

/-- **Moving independent cells with one law is ergodic.** -/
theorem ergodic_shiftCells (ν : Measure S) [IsProbabilityMeasure ν] {k : ℤ} (hk : k ≠ 0) :
    Ergodic (shiftCells k) (Measure.infinitePi fun _ : ℤ => ν) where
  toMeasurePreserving := measurePreserving_shiftCells ν k
  toPreErgodic := preErgodic_of_mixing (measurePreserving_shiftCells ν k)
    isSetRing_measurableCylinders (univ_mem_measurableCylinders _)
    generateFrom_measurableCylinders.symm (fun _ hA => .of_mem_measurableCylinders hA)
    fun _ hA => measure_inter_preimage_shiftCells ν hk hA

end Shift

end Unisono.Spec
