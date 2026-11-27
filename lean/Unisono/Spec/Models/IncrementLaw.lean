/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# A process with independent increments has one law

The generative model describes the paused time of a link or of a host by
three properties: it is zero at true time zero, its increments over periods
that do not overlap are independent, and the increment over each period has a
given law. This file shows that these properties fix the law of the whole
path, so that two random worlds of one member cannot differ in how their
pauses are distributed.

* `aemeasurable_path`: the path of a process that is continuous from the
  right, as a function of the outcome with values in the functions of time,
  is measurable up to a set of probability zero.
* `HasIncrementLaws`: a process that starts at zero and has independent
  increments with given laws.
* `HasIncrementLaws.map_restrict`: the joint law of the values of such a
  process at finitely many times is determined by the laws of the
  increments. The times, together with time zero, are put in increasing
  order (`sortedTimes`); the increments between neighbours are independent
  with the given laws; and each value is a sum of increments
  (`valuesOfIncrements`).
* `HasIncrementLaws.map_path_eq`: two such processes with the same laws of
  the increments have the same law of the path.
* `map_paths_eq`: the same for finitely many independent processes.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The path of a process that is continuous from the right -/

/-- Rational numbers above `t` that tend to `t`. -/
theorem exists_rat_seq_gt (t : ℝ) :
    ∃ q : ℕ → ℚ, (∀ n, t < q n) ∧ Tendsto (fun n => (q n : ℝ)) atTop (𝓝 t) := by
  have h : ∀ n : ℕ, ∃ q : ℚ, t < q ∧ (q : ℝ) < t + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
  choose q hq1 hq2 using h
  refine ⟨q, hq1, ?_⟩
  have hlim : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (hq1 n).le) (fun n => (hq2 n).le)

/-- **The path of a process that is continuous from the right is a random
variable.** If the value of the process at each time is measurable up to a
set of probability zero, and every path is continuous from the right, then
the path, as a function of the outcome with values in the functions of time,
is measurable up to a set of probability zero. -/
theorem aemeasurable_path {X : ℝ → Ω → ℝ} (hX : ∀ t, AEMeasurable (X t) P)
    (hright : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) :
    AEMeasurable (fun ω t => X t ω) P := by
  classical
  -- Outside a measurable set of probability zero, the values at the rational times are
  -- those of measurable functions.
  have hae : ∀ᵐ ω ∂P, ∀ q : ℚ, X q ω = (hX q).mk (X q) ω :=
    ae_all_iff.mpr fun q => (hX q).ae_eq_mk
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  have hZ : Measurable fun ω t => if ω ∈ N then (0 : ℝ) else X t ω := by
    refine measurable_pi_iff.mpr fun t => ?_
    obtain ⟨q, hq, hqt⟩ := exists_rat_seq_gt t
    have hW : ∀ n : ℕ, Measurable fun ω => if ω ∈ N then (0 : ℝ)
        else (hX (q n)).mk (X (q n)) ω := fun n =>
      Measurable.ite hNmeas measurable_const (hX (q n)).measurable_mk
    refine measurable_of_tendsto_metrizable hW (tendsto_pi_nhds.mpr fun ω => ?_)
    by_cases hω : ω ∈ N
    · simp only [ite_eq_left hω]
      exact tendsto_const_nhds
    · have hgood : ∀ r : ℚ, X r ω = (hX r).mk (X r) ω := by
        by_contra hcon
        exact hω (hsub hcon)
      have hlim : Tendsto (fun n => X (q n) ω) atTop (𝓝 (X t ω)) :=
        (hright ω t).tendsto.comp
          (tendsto_nhdsWithin_iff.mpr ⟨hqt, Filter.Eventually.of_forall fun n => (hq n).le⟩)
      simp only [ite_eq_right hω]
      exact hlim.congr fun n => hgood (q n)
  refine ⟨fun ω t => if ω ∈ N then (0 : ℝ) else X t ω, hZ, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN0] with ω hω
  funext t
  rw [ite_eq_right hω]

/-! ## The times of a finite set in increasing order -/

open Classical in
/-- The times of a finite set of times, together with time zero, in
increasing order; from the last one on, the sequence stays at it. -/
def sortedTimes (I : Finset ℝ) (n : ℕ) : ℝ :=
  (insert 0 I).orderEmbOfFin rfl ⟨min n ((insert 0 I).card - 1), by
    have := Finset.card_pos.mpr (Finset.insert_nonempty (0 : ℝ) I)
    omega⟩

theorem sortedTimes_monotone (I : Finset ℝ) : Monotone (sortedTimes I) := by
  classical
  intro a b hab
  exact ((insert 0 I).orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr (min_le_min_right _ hab))

open Classical in
/-- Every time of the set, and time zero, is one of the sorted times. -/
theorem exists_sortedTimes_eq {I : Finset ℝ} {x : ℝ} (hx : x ∈ insert 0 I) :
    ∃ a, a < (insert 0 I).card ∧ sortedTimes I a = x := by
  have hmem : x ∈ Set.range ((insert 0 I).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hx
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, a.2, ?_⟩
  unfold sortedTimes
  rw [← ha]
  congr 1
  apply Fin.ext
  have := a.2
  simp only
  omega

open Classical in
/-- The place of a time among the sorted times. -/
def timeIndex (I : Finset ℝ) (x : ℝ) : ℕ :=
  if hx : x ∈ insert 0 I then Classical.choose (exists_sortedTimes_eq hx) else 0

open Classical in
theorem timeIndex_lt {I : Finset ℝ} {x : ℝ} (hx : x ∈ insert 0 I) :
    timeIndex I x < (insert 0 I).card := by
  unfold timeIndex
  rw [dite_eq_left hx]
  exact (Classical.choose_spec (exists_sortedTimes_eq hx)).1

open Classical in
theorem sortedTimes_timeIndex {I : Finset ℝ} {x : ℝ} (hx : x ∈ insert 0 I) :
    sortedTimes I (timeIndex I x) = x := by
  unfold timeIndex
  rw [dite_eq_left hx]
  exact (Classical.choose_spec (exists_sortedTimes_eq hx)).2

open Classical in
/-- The values of a process at the times of `I`, from its increments between
neighbours among the sorted times: the sum of the increments up to the time,
minus the sum of the increments up to time zero. -/
def valuesOfIncrements (I : Finset ℝ) (v : Fin (insert 0 I).card → ℝ) (t : I) : ℝ :=
  (∑ l ∈ Finset.range (timeIndex I t), if h : l < (insert 0 I).card then v ⟨l, h⟩ else 0)
    - ∑ l ∈ Finset.range (timeIndex I 0), if h : l < (insert 0 I).card then v ⟨l, h⟩ else 0

open Classical in
theorem measurable_valuesOfIncrements (I : Finset ℝ) : Measurable (valuesOfIncrements I) := by
  have hterm : ∀ l : ℕ, Measurable fun v : Fin (insert 0 I).card → ℝ =>
      if h : l < (insert 0 I).card then v ⟨l, h⟩ else 0 := fun l => by
    by_cases h : l < (insert 0 I).card
    · simp only [dite_eq_left h]
      exact measurable_pi_apply _
    · simp only [dite_eq_right h]
      exact measurable_const
  refine measurable_pi_iff.mpr fun t => ?_
  exact (Finset.measurable_sum _ fun l _ => hterm l).sub
    (Finset.measurable_sum _ fun l _ => hterm l)

open Classical in
/-- The increments of a process between neighbours among the sorted times,
added up to a place, give the change of the process from the first sorted
time. -/
theorem sum_increments (I : Finset ℝ) (x : ℕ → ℝ) {a : ℕ} (ha : a ≤ (insert 0 I).card) :
    (∑ l ∈ Finset.range a,
      if h : l < (insert 0 I).card then
        (fun i : Fin (insert 0 I).card => x ((i : ℕ) + 1) - x i) ⟨l, h⟩ else 0)
      = x a - x 0 := by
  rw [← Finset.sum_range_sub x a]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [dite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hl) ha)]

/-! ## The law of the path -/

/-- The process `X` starts at zero and has independent increments, and its
increment from time `s` to a later time `t` has the law `L s t`. -/
structure HasIncrementLaws (L : ℝ → ℝ → Measure ℝ) (X : ℝ → Ω → ℝ) (P : Measure Ω) :
    Prop where
  zero : ∀ ω, X 0 ω = 0
  indep : HasIndepIncrements X P
  law : ∀ s t, s ≤ t → HasLaw (fun ω => X t ω - X s ω) (L s t) P

variable {L : ℝ → ℝ → Measure ℝ} {X : ℝ → Ω → ℝ}

/-- The value of such a process at each time is measurable up to a set of
probability zero. -/
theorem HasIncrementLaws.aemeasurable (h : HasIncrementLaws L X P) (t : ℝ) :
    AEMeasurable (X t) P := by
  rcases le_total 0 t with ht | ht
  · have h1 := (h.law 0 t ht).aemeasurable
    have e : (fun ω => X t ω - X 0 ω) = X t := funext fun ω => by rw [h.zero ω, sub_zero]
    rwa [e] at h1
  · have h1 : AEMeasurable (fun ω => -(X 0 ω - X t ω)) P := (h.law t 0 ht).aemeasurable.neg
    have e : (fun ω => -(X 0 ω - X t ω)) = X t := funext fun ω => by rw [h.zero ω]; ring
    rwa [e] at h1

open Classical in
/-- **The joint law of the values at finitely many times** of a process that
starts at zero and has independent increments with given laws: the image,
under `valuesOfIncrements`, of the product of the laws of the increments
between neighbours among the sorted times. -/
theorem HasIncrementLaws.map_restrict (h : HasIncrementLaws L X P) (I : Finset ℝ) :
    P.map (fun ω (t : I) => X t ω)
      = (Measure.pi fun i : Fin (insert 0 I).card =>
          L (sortedTimes I i) (sortedTimes I ((i : ℕ) + 1))).map (valuesOfIncrements I) := by
  have hind : iIndepFun (fun (i : Fin (insert 0 I).card) ω =>
      X (sortedTimes I ((i : ℕ) + 1)) ω - X (sortedTimes I i) ω) P :=
    (h.indep.nat (sortedTimes_monotone I)).precomp Fin.val_injective
  have hlaw : ∀ i : Fin (insert 0 I).card,
      HasLaw (fun ω => X (sortedTimes I ((i : ℕ) + 1)) ω - X (sortedTimes I i) ω)
        (L (sortedTimes I i) (sortedTimes I ((i : ℕ) + 1))) P := fun i =>
    h.law _ _ (sortedTimes_monotone I (Nat.le_succ i))
  have hjoint : P.map (fun ω (i : Fin (insert 0 I).card) =>
        X (sortedTimes I ((i : ℕ) + 1)) ω - X (sortedTimes I i) ω)
      = Measure.pi fun i : Fin (insert 0 I).card =>
          L (sortedTimes I i) (sortedTimes I ((i : ℕ) + 1)) := by
    rw [hind.map_fun_eq_pi_map fun i => (hlaw i).aemeasurable]
    congr 1
    funext i
    exact (hlaw i).map_eq
  have hval : (fun ω (t : I) => X t ω)
      = valuesOfIncrements I ∘ fun ω (i : Fin (insert 0 I).card) =>
          X (sortedTimes I ((i : ℕ) + 1)) ω - X (sortedTimes I i) ω := by
    funext ω t
    have ht : (t : ℝ) ∈ insert 0 I := Finset.mem_insert_of_mem t.2
    have h0 : (0 : ℝ) ∈ insert 0 I := Finset.mem_insert_self 0 I
    have e1 := sum_increments I (fun n => X (sortedTimes I n) ω) (timeIndex_lt ht).le
    have e2 := sum_increments I (fun n => X (sortedTimes I n) ω) (timeIndex_lt h0).le
    simp only [Function.comp_apply, valuesOfIncrements]
    rw [e1, e2, sortedTimes_timeIndex ht, sortedTimes_timeIndex h0, h.zero ω]
    ring
  rw [hval, ← hjoint]
  exact (AEMeasurable.map_map_of_aemeasurable (measurable_valuesOfIncrements I).aemeasurable
    (AEMeasurable.of_eval fun i => (hlaw i).aemeasurable)).symm

/-- **A process with independent increments has one law.** Two processes
that start at zero and have independent increments with the same laws have
the same law of the path. -/
theorem HasIncrementLaws.map_path_eq {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X' : ℝ → Ω' → ℝ}
    (h : HasIncrementLaws L X P) (h' : HasIncrementLaws L X' P')
    (hm : AEMeasurable (fun ω t => X t ω) P) (hm' : AEMeasurable (fun ω t => X' t ω) P') :
    P.map (fun ω t => X t ω) = P'.map (fun ω t => X' t ω) := by
  refine IsProjectiveLimit.unique
    (P := fun I : Finset ℝ => P'.map (fun ω (t : I) => X' t ω)) (fun I => ?_) fun I => ?_
  · rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hm]
    exact (h.map_restrict I).trans (h'.map_restrict I).symm
  · rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hm']
    rfl

/-- **Finitely many independent processes with independent increments have
one joint law.** -/
theorem map_paths_eq {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {J : Type*} [Fintype J]
    {L : J → ℝ → ℝ → Measure ℝ} {X : J → ℝ → Ω → ℝ} {X' : J → ℝ → Ω' → ℝ}
    (h : ∀ j, HasIncrementLaws (L j) (X j) P) (h' : ∀ j, HasIncrementLaws (L j) (X' j) P')
    (hm : ∀ j, AEMeasurable (fun ω t => X j t ω) P)
    (hm' : ∀ j, AEMeasurable (fun ω t => X' j t ω) P')
    (hind : iIndepFun (fun j ω t => X j t ω) P) (hind' : iIndepFun (fun j ω t => X' j t ω) P') :
    P.map (fun ω j t => X j t ω) = P'.map (fun ω j t => X' j t ω) := by
  rw [hind.map_fun_eq_pi_map hm, hind'.map_fun_eq_pi_map hm']
  congr 1
  funext j
  exact (h j).map_path_eq (h' j) (hm j) (hm' j)

end Unisono.Spec
