/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ErgodicCells

/-!
# The mean of long-run averages along a measure-preserving map

For a map `T` that preserves a probability measure and a function `g ≥ 0`
with a finite mean, the averages of `g` along an orbit need not converge to
the mean of `g`: the map need not be ergodic. But **the mean of the limit
superior of the averages is at most the mean of `g`**
(`lintegral_limsup_birkhoffAverage_le`). This is what bounds an expected
long-run average of a cost that is not bounded. `lintegral_limsup_average_le`
states it for a measurable function with values from zero to infinity, with
the sums along the orbit written out; it needs no finite mean.

The proof uses the maximal ergodic theorem on sets that the map sends onto
themselves:

* `preimage_frequentlyAbove_of_nonneg`: for `g ≥ 0` and `a ≥ 0`, the set of
  points whose averages exceed `a` by one positive amount again and again
  (`frequentlyAbove`) is sent onto itself.
* `mul_measureReal_le_setIntegral_of_subset`: on a measurable set
  `B` that the map sends onto itself and that lies in `frequentlyAbove a`,
  the mean of `g` over `B` is at least `a` times the measure of `B`.
* The limit superior is then cut into layers of height `ε`; on each layer
  the bound above applies, and the layers add up to at most the mean of `g`
  plus `ε`.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {T : α → α} {g : α → ℝ}

/-- The average over `n + 1` steps from `x`, in terms of the average over
`n` steps from `T x`. -/
theorem succ_mul_birkhoffAverage_succ (T : α → α) (g : α → ℝ) (n : ℕ) (x : α) :
    ((n : ℝ) + 1) * birkhoffAverage ℝ T g (n + 1) x
      = g x + n * birkhoffAverage ℝ T g n (T x) := by
  have h1 : ((n : ℝ) + 1) * birkhoffAverage ℝ T g (n + 1) x = birkhoffSum T g (n + 1) x := by
    unfold birkhoffAverage
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
    field_simp
  have h2 : (n : ℝ) * birkhoffAverage ℝ T g n (T x) = birkhoffSum T g n (T x) := by
    unfold birkhoffAverage
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · have hne : (n : ℝ) ≠ 0 := by positivity
      simp only [smul_eq_mul]
      field_simp
  rw [h1, h2, birkhoffSum_succ']
  rfl

/-- An average of a function that is not negative is not negative. -/
theorem birkhoffAverage_nonneg (hg0 : ∀ x, 0 ≤ g x) (n : ℕ) (x : α) :
    0 ≤ birkhoffAverage ℝ T g n x := by
  unfold birkhoffAverage
  exact smul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hg0 _)

/-- **The map sends the set `frequentlyAbove` onto itself**, for a function
that is not negative and `a ≥ 0`. -/
theorem preimage_frequentlyAbove_of_nonneg (hg0 : ∀ x, 0 ≤ g x) {a : ℝ} (ha : 0 ≤ a) :
    T ⁻¹' frequentlyAbove T g a = frequentlyAbove T g a := by
  ext x
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε / 2, half_pos hε, frequently_atTop.mpr fun N => ?_⟩
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * (a + ε) / ε)
    obtain ⟨n, hn, hlt⟩ := (frequently_atTop.mp h) (max N N₀)
    refine ⟨n + 1, by omega, ?_⟩
    have hrel := succ_mul_birkhoffAverage_succ T g n x
    have hn0 : (N₀ : ℝ) ≤ n := by exact_mod_cast (le_max_right N N₀).trans hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hgx := hg0 x
    have hbig : 2 * (a + ε) ≤ ε * ((n : ℝ) + 1) := by
      have h3 : 2 * (a + ε) / ε ≤ n := hN₀.trans hn0
      rw [div_le_iff₀ hε] at h3
      nlinarith
    -- (n + 1) * A = g x + n * B with B > a + ε.
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h4 : (n : ℝ) * (a + ε) ≤ (n : ℝ) * birkhoffAverage ℝ T g n (T x) :=
      mul_le_mul_of_nonneg_left hlt.le hnn
    by_contra hcon
    rw [not_lt] at hcon
    have h5 : ((n : ℝ) + 1) * birkhoffAverage ℝ T g (n + 1) x ≤ ((n : ℝ) + 1) * (a + ε / 2) :=
      mul_le_mul_of_nonneg_left hcon hn1.le
    nlinarith
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε / 2, half_pos hε, frequently_atTop.mpr fun N => ?_⟩
    obtain ⟨N₁, hN₁⟩ := exists_nat_ge (2 * g x / ε)
    obtain ⟨m, hm, hlt⟩ := (frequently_atTop.mp h) (max N N₁ + 1)
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    refine ⟨n, by omega, ?_⟩
    have hrel := succ_mul_birkhoffAverage_succ T g n x
    have hn1 : (N₁ : ℝ) ≤ n := by
      have : N₁ ≤ n := by omega
      exact_mod_cast this
    have hgx := hg0 x
    have hbig : 2 * g x ≤ ε * n := by
      have h3 : 2 * g x / ε ≤ n := hN₁.trans hn1
      rw [div_le_iff₀ hε] at h3
      linarith
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hA := birkhoffAverage_nonneg (T := T) hg0 (n + 1) x
    by_contra hcon
    rw [not_lt] at hcon
    have h5 : (n : ℝ) * birkhoffAverage ℝ T g n (T x) ≤ (n : ℝ) * (a + ε / 2) :=
      mul_le_mul_of_nonneg_left hcon hnn
    have h6 : ((n : ℝ) + 1) * (a + ε) ≤ ((n : ℝ) + 1) * birkhoffAverage ℝ T g (n + 1) x :=
      mul_le_mul_of_nonneg_left hlt.le (by positivity)
    nlinarith

/-- The sets `frequentlyAbove` shrink as the level grows. -/
theorem frequentlyAbove_antitone (T : α → α) (g : α → ℝ) {a a' : ℝ} (h : a ≤ a') :
    frequentlyAbove T g a' ⊆ frequentlyAbove T g a := by
  rintro x ⟨ε, hε, hf⟩
  exact ⟨ε, hε, hf.mono fun n hn => by linarith⟩

/-- **On a set that the map sends onto itself and on which the averages
exceed `a` again and again, the mean of the function is at least `a` times
the measure of the set.** -/
theorem mul_measureReal_le_setIntegral_of_subset [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hg : Integrable g μ) {a : ℝ} (ha : 0 ≤ a) {B : Set α}
    (hBm : MeasurableSet B) (hB : T ⁻¹' B = B) (hsub : B ⊆ frequentlyAbove T g a) :
    a * μ.real B ≤ ∫ x in B, g x ∂μ := by
  have hh : Integrable (B.indicator g) μ := hg.indicator hBm
  have hmax := mul_measureReal_lt_birkhoffAverageSup_le_integral μ hT hh a ha
  have havg : ∀ n x, birkhoffAverage ℝ T (B.indicator g) n x
      = B.indicator (birkhoffAverage ℝ T g n) x := by
    intro n x
    unfold birkhoffAverage
    rw [birkhoffSum_indicator_of_preimage_eq hB g n x]
    by_cases hx : x ∈ B
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hset : {x | (a : EReal) < birkhoffAverageSup T (B.indicator g) x} = B := by
    ext x
    constructor
    · intro hx
      by_contra hxB
      have hzero : birkhoffAverageSup T (B.indicator g) x = 0 := by
        unfold birkhoffAverageSup
        have : ∀ n, ((birkhoffAverage ℝ T (B.indicator g) n x : ℝ) : EReal) = 0 := by
          intro n
          rw [havg n x, Set.indicator_of_notMem hxB]
          rfl
        simp [this]
      have hx' : (a : EReal) < birkhoffAverageSup T (B.indicator g) x := hx
      rw [hzero] at hx'
      exact absurd hx' (not_lt.mpr (by exact_mod_cast ha))
    · intro hx
      obtain ⟨ε, hε, hf⟩ := hsub hx
      obtain ⟨n, hn⟩ := hf.exists
      have h1 : a < birkhoffAverage ℝ T (B.indicator g) n x := by
        rw [havg n x, Set.indicator_of_mem hx]
        linarith
      show (a : EReal) < birkhoffAverageSup T (B.indicator g) x
      unfold birkhoffAverageSup
      exact lt_of_lt_of_le (by exact_mod_cast h1) (le_iSup (fun n =>
        ((birkhoffAverage ℝ T (B.indicator g) n x : ℝ) : EReal)) n)
  rw [hset] at hmax
  have hint : ∫ x in B, B.indicator g x ∂μ = ∫ x in B, g x ∂μ :=
    setIntegral_congr_fun hBm fun x hx => Set.indicator_of_mem hx g
  rw [hint] at hmax
  exact hmax

/-- Outside `frequentlyAbove a` the limit superior of the averages is at
most `a`. -/
theorem limsup_le_of_notMem_frequentlyAbove {a : ℝ} {x : α}
    (hx : x ∉ frequentlyAbove T g a) :
    limsup (fun n => ENNReal.ofReal (birkhoffAverage ℝ T g n x)) atTop ≤ ENNReal.ofReal a := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hev : ∀ᶠ n in atTop, birkhoffAverage ℝ T g n x ≤ a + ε := by
    by_contra hcon
    rw [not_eventually] at hcon
    exact hx ⟨ε, hεr, hcon.mono fun n hn => not_le.mp hn⟩
  refine (limsup_le_of_le (h := hev.mono fun n hn => ENNReal.ofReal_le_ofReal hn)).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_add_le

/-- **The mean of the limit superior of the averages is at most the mean.**
For a map `T` that preserves the probability measure `μ` and a measurable
function `g ≥ 0` with a finite mean: the mean of the limit superior of the
averages of `g` along the orbits of `T` is at most the mean of `g`. -/
theorem lintegral_limsup_birkhoffAverage_le [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hgm : Measurable g) (hg : Integrable g μ)
    (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ x, limsup (fun n => ENNReal.ofReal (birkhoffAverage ℝ T g n x)) atTop ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  -- The layers.
  set FA : ℕ → Set α := fun j => frequentlyAbove T g (j * ε) with hFA
  set F : ℕ → Set α := fun j => FA j \ FA (j + 1) with hF
  set Finf : Set α := ⋂ j, FA j with hFinf
  have hjε : ∀ j : ℕ, (0 : ℝ) ≤ j * ε := fun j => by positivity
  have hFAm : ∀ j, MeasurableSet (FA j) :=
    fun j => measurableSet_frequentlyAbove hT.measurable hgm _
  have hFAinv : ∀ j, T ⁻¹' FA j = FA j :=
    fun j => preimage_frequentlyAbove_of_nonneg hg0 (hjε j)
  have hFAanti : ∀ {i j : ℕ}, i ≤ j → FA j ⊆ FA i := fun {i j} hij =>
    frequentlyAbove_antitone T g (by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      nlinarith)
  have hFm : ∀ j, MeasurableSet (F j) := fun j => (hFAm j).diff (hFAm (j + 1))
  have hFinv : ∀ j, T ⁻¹' F j = F j := fun j => by
    show T ⁻¹' (FA j \ FA (j + 1)) = FA j \ FA (j + 1)
    rw [Set.preimage_sdiff, hFAinv j, hFAinv (j + 1)]
  have hFinfm : MeasurableSet Finf := MeasurableSet.iInter hFAm
  have hFinfinv : T ⁻¹' Finf = Finf := by
    show T ⁻¹' (⋂ j, FA j) = ⋂ j, FA j
    rw [Set.preimage_iInter]
    exact Set.iInter_congr hFAinv
  have hFdisj : Pairwise (Function.onFun Disjoint F) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.mpr fun x hxi hxj => hxi.2 (hFAanti (by omega) hxj.1)
    · exact Set.disjoint_left.mpr fun x hxi hxj => hxj.2 (hFAanti (by omega) hxi.1)
  -- The limit superior is at most the layer function.
  have hpoint : ∀ x, limsup (fun n => ENNReal.ofReal (birkhoffAverage ℝ T g n x)) atTop
      ≤ (∑' j : ℕ, (F j).indicator (fun _ => ENNReal.ofReal (((j : ℝ) + 1) * ε)) x)
        + Finf.indicator (fun _ => (⊤ : ℝ≥0∞)) x := by
    intro x
    by_cases hxinf : x ∈ Finf
    · rw [Set.indicator_of_mem hxinf]
      simp
    · have hex : ∃ j, x ∉ FA j := by
        by_contra hcon
        push Not at hcon
        exact hxinf (Set.mem_iInter.mpr hcon)
      classical
      have hmin := Nat.find_spec hex
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0] at hmin
        have h1 := limsup_le_of_notMem_frequentlyAbove (T := T) (g := g) (a := ((0 : ℕ) : ℝ) * ε)
          hmin
        simp only [Nat.cast_zero, zero_mul, ENNReal.ofReal_zero] at h1
        exact h1.trans zero_le
      · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
        rw [hj] at hmin
        have hjin : x ∈ FA j := by
          by_contra hcon
          have := Nat.find_min' hex hcon
          omega
        have hxF : x ∈ F j := ⟨hjin, hmin⟩
        have h1 := limsup_le_of_notMem_frequentlyAbove (T := T) (g := g)
          (a := ((j + 1 : ℕ) : ℝ) * ε) hmin
        have h2 : ENNReal.ofReal (((j + 1 : ℕ) : ℝ) * ε)
            = (F j).indicator (fun _ => ENNReal.ofReal (((j : ℝ) + 1) * ε)) x := by
          rw [Set.indicator_of_mem hxF]
          push_cast
          rfl
        rw [h2] at h1
        exact h1.trans ((le_tsum (fun j : ℕ => (F j).indicator
          (fun _ => ENNReal.ofReal (((j : ℝ) + 1) * ε)) x) j).trans le_self_add)
  -- The top layer has measure zero.
  have hI : ∫ x, g x ∂μ = (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hg0) hgm.aestronglyMeasurable
  have hsetle : ∀ B : Set α, MeasurableSet B → ∫ x in B, g x ∂μ ≤ ∫ x, g x ∂μ := fun B _ =>
    setIntegral_le_integral hg (ae_of_all μ hg0)
  have hFinf0 : μ Finf = 0 := by
    by_contra hne
    have hpos : 0 < μ.real Finf := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos hne (measure_ne_top μ Finf)
    obtain ⟨j, hj⟩ := exists_nat_gt ((∫ x, g x ∂μ) / (ε * μ.real Finf))
    have h1 := mul_measureReal_le_setIntegral_of_subset hT hg (hjε j) hFinfm hFinfinv
      (Set.iInter_subset FA j)
    have h2 := hsetle Finf hFinfm
    rw [div_lt_iff₀ (mul_pos hεr hpos)] at hj
    nlinarith
  -- Each layer.
  have hlayer : ∀ j : ℕ, ENNReal.ofReal ((j : ℝ) * ε) * μ (F j)
      ≤ ∫⁻ x in F j, ENNReal.ofReal (g x) ∂μ := by
    intro j
    have h1 := mul_measureReal_le_setIntegral_of_subset hT hg (hjε j) (hFm j)
      (hFinv j) Set.sdiff_subset
    have h2 : ENNReal.ofReal (∫ x in F j, g x ∂μ) = ∫⁻ x in F j, ENNReal.ofReal (g x) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hg.integrableOn (ae_of_all _ hg0)
    rw [← h2]
    have h3 : ENNReal.ofReal ((j : ℝ) * ε) * μ (F j)
        = ENNReal.ofReal ((j : ℝ) * ε * μ.real (F j)) := by
      rw [ENNReal.ofReal_mul (hjε j), ofReal_measureReal]
    rw [h3]
    exact ENNReal.ofReal_le_ofReal h1
  calc ∫⁻ x, limsup (fun n => ENNReal.ofReal (birkhoffAverage ℝ T g n x)) atTop ∂μ
      ≤ ∫⁻ x, ((∑' j : ℕ, (F j).indicator (fun _ => ENNReal.ofReal (((j : ℝ) + 1) * ε)) x)
          + Finf.indicator (fun _ => (⊤ : ℝ≥0∞)) x) ∂μ := lintegral_mono hpoint
    _ = (∑' j : ℕ, ENNReal.ofReal (((j : ℝ) + 1) * ε) * μ (F j)) + ⊤ * μ Finf := by
        rw [lintegral_add_right _ (measurable_const.indicator hFinfm),
          lintegral_tsum fun j => (measurable_const.indicator (hFm j)).aemeasurable,
          lintegral_indicator_const hFinfm]
        congr 1
        exact tsum_congr fun j => lintegral_indicator_const (hFm j) _
    _ = ∑' j : ℕ, ENNReal.ofReal (((j : ℝ) + 1) * ε) * μ (F j) := by
        rw [hFinf0, mul_zero, add_zero]
    _ = ∑' j : ℕ, (ENNReal.ofReal ((j : ℝ) * ε) * μ (F j) + ε * μ (F j)) := by
        refine tsum_congr fun j => ?_
        rw [add_mul, one_mul, ENNReal.ofReal_add (hjε j) hεr.le, add_mul,
          ENNReal.ofReal_coe_nnreal]
    _ = (∑' j : ℕ, ENNReal.ofReal ((j : ℝ) * ε) * μ (F j)) + ∑' j : ℕ, (ε : ℝ≥0∞) * μ (F j) :=
        tsum_add
    _ ≤ (∑' j : ℕ, ∫⁻ x in F j, ENNReal.ofReal (g x) ∂μ) + ε * ∑' j : ℕ, μ (F j) := by
        rw [ENNReal.tsum_mul_left]
        exact add_le_add_left (tsum_le_tsum hlayer) _
    _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ + ε := by
        rw [← lintegral_iUnion hFm hFdisj, ← measure_iUnion hFdisj hFm]
        refine add_le_add (setLIntegral_le_lintegral _ _) ?_
        calc (ε : ℝ≥0∞) * μ (⋃ j, F j) ≤ ε * 1 := by gcongr; exact prob_le_one
          _ = ε := mul_one _

/-- **The mean of the limit superior of the averages along the orbits is at
most the mean**, for a measurable function with values from zero to
infinity: for a map `T` that preserves the probability measure `μ`, the mean
of the limit superior, as `n` grows, of the sum of `G` over the first `n`
points of an orbit divided by `n` is at most the mean of `G`. -/
theorem lintegral_limsup_average_le [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {G : α → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, limsup (fun n : ℕ => (∑ i ∈ Finset.range n, G (T^[i] x)) / n) atTop ∂μ
      ≤ ∫⁻ x, G x ∂μ := by
  by_cases htop : ∫⁻ x, G x ∂μ = ⊤
  · rw [htop]
    exact le_top
  · have hfin : ∀ᵐ x ∂μ, G x < ⊤ := ae_lt_top hG htop
    have hall : ∀ᵐ x ∂μ, ∀ i : ℕ, G (T^[i] x) < ⊤ := by
      rw [ae_all_iff]
      intro i
      exact (hT.iterate i).quasiMeasurePreserving.ae hfin
    have hgm : Measurable fun x => (G x).toReal := hG.ennreal_toReal
    have hg : Integrable (fun x => (G x).toReal) μ :=
      integrable_toReal_of_lintegral_ne_top hG.aemeasurable htop
    have hg0 : ∀ x, 0 ≤ (G x).toReal := fun x => ENNReal.toReal_nonneg
    have hmain := lintegral_limsup_birkhoffAverage_le hT hgm hg hg0
    have hleft : ∀ᵐ x ∂μ,
        limsup (fun n : ℕ => (∑ i ∈ Finset.range n, G (T^[i] x)) / n) atTop
          = limsup (fun n => ENNReal.ofReal
              (birkhoffAverage ℝ T (fun x => (G x).toReal) n x)) atTop := by
      filter_upwards [hall] with x hx
      congr 1
      funext n
      have hsum : ∑ i ∈ Finset.range n, G (T^[i] x)
          = ENNReal.ofReal (∑ i ∈ Finset.range n, (G (T^[i] x)).toReal) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => ENNReal.toReal_nonneg]
        exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_toReal (hx i).ne).symm
      rw [hsum]
      unfold birkhoffAverage birkhoffSum
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp
      · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
        rw [smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hn.le),
          ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast, mul_comm]
        rfl
    have hright : ∫⁻ x, ENNReal.ofReal ((G x).toReal) ∂μ = ∫⁻ x, G x ∂μ :=
      lintegral_congr_ae (hfin.mono fun x hx => ENNReal.ofReal_toReal hx.ne)
    rw [lintegral_congr_ae hleft, ← hright]
    exact hmain

end Unisono.Spec
