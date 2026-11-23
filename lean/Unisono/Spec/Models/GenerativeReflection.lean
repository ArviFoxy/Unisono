/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Limits
public import Unisono.Spec.Models.GenerativeTransfer

/-!
# Reflecting the links to the sender

A host that exchanges messages only with the sender cannot tell two worlds
apart: one in which the delay to the sender is short and the delay back is
long, and one in which the two delays are exchanged and the host's clock is
offset by the difference. This file builds the map of outcomes that
exchanges the two, for every receiving host at once, on the concrete random
world of a noiseless member (`Unisono.Spec.Models.GenerativeCanonical`).

* `reflect m f` exchanges the two delays between the sender and each
  receiving host, by replacing the split `u` of the pair by `1 - u`, and
  moves the offset of the host's clock so that the host observes the same.
  It does this for a host only when the moved offset stays within the range
  of offsets; otherwise it leaves the host's coordinates as they are.
* The reflection keeps the law of the outcomes
  (`measurePreserving_reflect`). The reason is that the split has a
  symmetric law and the offset a uniform one.
* The world of the reflected outcome is the world of the outcome with the
  hosts' timelines shifted along the links to and from the sender
  (`canonicalWorld_reflect`), by `reflectShift`.

Two general facts carry the proof. Changing two of several independent
numbers by a map that keeps the joint law of the two keeps the joint law of
all (`measurePreserving_updatePair`). A map that agrees with a
measure-preserving map on a set that this map sends to itself, and changes
nothing elsewhere, keeps the measure restricted to any set that contains the
first (`measurePreserving_restrict_of_eqOn`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Changing two of several independent numbers -/

section UpdatePair

variable {ι : Type} [DecidableEq ι]

/-- A family of numbers with the numbers at `a` and at `b` replaced by the
value of `Φ` at the pair of the two. -/
def updatePair (a b : ι) (Φ : ℝ × ℝ → ℝ × ℝ) (y : ι → ℝ) : ι → ℝ :=
  Function.update (Function.update y a (Φ (y a, y b)).1) b (Φ (y a, y b)).2

theorem updatePair_right (a b : ι) (Φ : ℝ × ℝ → ℝ × ℝ) (y : ι → ℝ) :
    updatePair a b Φ y b = (Φ (y a, y b)).2 := by
  simp [updatePair]

theorem updatePair_left {a b : ι} (hab : a ≠ b) (Φ : ℝ × ℝ → ℝ × ℝ) (y : ι → ℝ) :
    updatePair a b Φ y a = (Φ (y a, y b)).1 := by
  simp [updatePair, hab]

theorem updatePair_of_ne {a b p : ι} (hpa : p ≠ a) (hpb : p ≠ b) (Φ : ℝ × ℝ → ℝ × ℝ)
    (y : ι → ℝ) : updatePair a b Φ y p = y p := by
  simp [updatePair, hpa, hpb]

theorem measurable_updatePair (a b : ι) {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : Measurable Φ) :
    Measurable (updatePair a b Φ) := by
  have hpair : Measurable fun y : ι → ℝ => Φ (y a, y b) :=
    hΦ.comp ((measurable_pi_apply a).prodMk (measurable_pi_apply b))
  refine Measurable.of_eval fun p => ?_
  by_cases hpb : p = b
  · have hfun : (fun y : ι → ℝ => updatePair a b Φ y p) = fun y => (Φ (y a, y b)).2 := by
      funext y
      rw [hpb, updatePair_right]
    rw [hfun]
    exact hpair.snd
  · by_cases hpa : p = a
    · have hab : a ≠ b := fun e => hpb (hpa.trans e)
      have hfun : (fun y : ι → ℝ => updatePair a b Φ y p) = fun y => (Φ (y a, y b)).1 := by
        funext y
        rw [hpa, updatePair_left hab]
      rw [hfun]
      exact hpair.fst
    · have hfun : (fun y : ι → ℝ => updatePair a b Φ y p) = fun y => y p := by
        funext y
        rw [updatePair_of_ne hpa hpb]
      rw [hfun]
      exact measurable_pi_apply p

/-- **Changing two of several independent numbers keeps their joint law**,
when the change keeps the joint law of the two. -/
theorem measurePreserving_updatePair [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {a b : ι} (hab : a ≠ b) {Φ : ℝ × ℝ → ℝ × ℝ}
    (hΦ : MeasurePreserving Φ ((μ a).prod (μ b)) ((μ a).prod (μ b))) :
    MeasurePreserving (updatePair a b Φ) (Measure.pi μ) (Measure.pi μ) := by
  have hmeas : Measurable (updatePair a b Φ) := measurable_updatePair a b hΦ.measurable
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hind : iIndepFun (fun (i : ι) (y : ι → ℝ) => y i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have haS : a ∈ ({a, b} : Finset ι) := by simp
  have hbS : b ∈ ({a, b} : Finset ι) := by simp
  have hpairMeas : Measurable fun y : ι → ℝ => (y a, y b) :=
    (measurable_pi_apply a).prodMk (measurable_pi_apply b)
  have hpick : Measurable fun u : ↥({a, b} : Finset ι) → ℝ => (u ⟨a, haS⟩, u ⟨b, hbS⟩) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  -- The pair is independent of the other numbers.
  have hUV : IndepFun (fun y : ι → ℝ => (y a, y b))
      (fun (y : ι → ℝ) (i : ↥(({a, b} : Finset ι)ᶜ)) => y i) (Measure.pi μ) :=
    (hind.indepFun_finset {a, b} ({a, b} : Finset ι)ᶜ disjoint_compl_right
      fun i => measurable_pi_apply i).comp hpick measurable_id
  have hA : MeasurableSet (Φ ⁻¹' (s a ×ˢ s b)) := hΦ.measurable ((hs a).prod (hs b))
  have hB : MeasurableSet (Set.pi Set.univ fun i : ↥(({a, b} : Finset ι)ᶜ) => s i) :=
    MeasurableSet.univ_pi fun i => hs i
  have hpre : updatePair a b Φ ⁻¹' Set.pi Set.univ s
      = (fun y : ι → ℝ => (y a, y b)) ⁻¹' (Φ ⁻¹' (s a ×ˢ s b))
        ∩ (fun (y : ι → ℝ) (i : ↥(({a, b} : Finset ι)ᶜ)) => y i) ⁻¹'
            Set.pi Set.univ fun i : ↥(({a, b} : Finset ι)ᶜ) => s i := by
    ext y
    constructor
    · intro h
      have h' : ∀ p, updatePair a b Φ y p ∈ s p := fun p => h p (Set.mem_univ p)
      refine ⟨⟨?_, ?_⟩, fun i _ => ?_⟩
      · have h1 := h' a
        rwa [updatePair_left hab] at h1
      · have h1 := h' b
        rwa [updatePair_right] at h1
      · have hi : (i : ι) ∉ ({a, b} : Finset ι) := Finset.mem_compl.mp i.2
        have hia : (i : ι) ≠ a := fun e => hi (by rw [e]; exact haS)
        have hib : (i : ι) ≠ b := fun e => hi (by rw [e]; exact hbS)
        have h1 := h' i
        rwa [updatePair_of_ne hia hib] at h1
    · rintro ⟨⟨h1, h2⟩, h3⟩ p _
      by_cases hpb : p = b
      · rw [hpb, updatePair_right]
        exact h2
      · by_cases hpa : p = a
        · rw [hpa, updatePair_left hab]
          exact h1
        · rw [updatePair_of_ne hpa hpb]
          have hp : p ∈ ({a, b} : Finset ι)ᶜ := by simp [hpa, hpb]
          exact h3 ⟨p, hp⟩ (Set.mem_univ _)
  rw [hpre, hUV.measure_inter_preimage_eq_mul _ _ hA hB]
  -- The pair has the product of the two laws.
  have hpairLaw : (Measure.pi μ).map (fun y : ι → ℝ => (y a, y b)) = (μ a).prod (μ b) := by
    have hi : IndepFun (fun y : ι → ℝ => y a) (fun y : ι → ℝ => y b) (Measure.pi μ) :=
      hind.indepFun hab
    have ha : (Measure.pi μ).map (fun y : ι → ℝ => y a) = μ a :=
      (measurePreserving_eval μ a).map_eq
    have hb : (Measure.pi μ).map (fun y : ι → ℝ => y b) = μ b :=
      (measurePreserving_eval μ b).map_eq
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply a).aemeasurable
      (measurable_pi_apply b).aemeasurable).mp hi, ha, hb]
  have hPA : Measure.pi μ ((fun y : ι → ℝ => (y a, y b)) ⁻¹' (Φ ⁻¹' (s a ×ˢ s b)))
      = μ a (s a) * μ b (s b) := by
    rw [← Measure.map_apply hpairMeas hA, hpairLaw,
      hΦ.measure_preimage ((hs a).prod (hs b)).nullMeasurableSet, Measure.prod_prod]
  have hPB : Measure.pi μ ((fun (y : ι → ℝ) (i : ↥(({a, b} : Finset ι)ᶜ)) => y i) ⁻¹'
      Set.pi Set.univ fun i : ↥(({a, b} : Finset ι)ᶜ) => s i)
      = ∏ i ∈ ({a, b} : Finset ι)ᶜ, μ i (s i) := by
    have h1 : (fun (y : ι → ℝ) (i : ↥(({a, b} : Finset ι)ᶜ)) => y i) ⁻¹'
        (Set.pi Set.univ fun i : ↥(({a, b} : Finset ι)ᶜ) => s i)
        = Set.pi Set.univ fun i => if i ∈ ({a, b} : Finset ι)ᶜ then s i else Set.univ := by
      ext y
      constructor
      · intro h i _
        show y i ∈ if i ∈ ({a, b} : Finset ι)ᶜ then s i else Set.univ
        by_cases hi : i ∈ ({a, b} : Finset ι)ᶜ
        · rw [ite_eq_left hi]
          exact h ⟨i, hi⟩ (Set.mem_univ _)
        · rw [ite_eq_right hi]
          exact Set.mem_univ _
      · intro h i _
        have h2 : y i.1 ∈ if i.1 ∈ ({a, b} : Finset ι)ᶜ then s i.1 else Set.univ :=
          h i.1 (Set.mem_univ _)
        rwa [ite_eq_left i.2] at h2
    rw [h1, Measure.pi_pi]
    have h2 : ∀ i, μ i (if i ∈ ({a, b} : Finset ι)ᶜ then s i else Set.univ)
        = if i ∈ ({a, b} : Finset ι)ᶜ then μ i (s i) else 1 := by
      intro i
      split_ifs
      · rfl
      · exact measure_univ
    simp only [h2]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hPA, hPB, ← Finset.prod_mul_prod_compl ({a, b} : Finset ι) fun i => μ i (s i),
    Finset.prod_pair hab]

end UpdatePair

/-! ## A map that acts on part of a space -/

/-- A map `Φ` keeps the measure `ρ` restricted to a set `J` when it agrees,
on a set `G` inside `J`, with a map `S` that keeps `ρ` and sends `G` to
itself, and changes nothing outside `G`. -/
theorem measurePreserving_restrict_of_eqOn {X : Type} [MeasurableSpace X] {ρ : Measure X}
    {S Φ : X → X} (hS : MeasurePreserving S ρ ρ) {G J : Set X} (hG : MeasurableSet G)
    (hJ : MeasurableSet J) (hGJ : G ⊆ J) (hSG : S ⁻¹' G = G) (hΦ : Measurable Φ)
    (hin : ∀ x, x ∈ G → Φ x = S x) (hout : ∀ x, x ∉ G → Φ x = x) :
    MeasurePreserving Φ (ρ.restrict J) (ρ.restrict J) := by
  refine ⟨hΦ, ?_⟩
  ext A hA
  rw [Measure.map_apply hΦ hA, Measure.restrict_apply (hΦ hA), Measure.restrict_apply hA]
  have hmem : ∀ x, S x ∈ G ↔ x ∈ G := fun x => by
    have h : x ∈ S ⁻¹' G ↔ x ∈ G := by rw [hSG]
    exact h
  have h1 : Φ ⁻¹' A ∩ J = S ⁻¹' (A ∩ G) ∪ A ∩ (J \ G) := by
    ext x
    constructor
    · rintro ⟨hxA, hxJ⟩
      have h2 : Φ x ∈ A := hxA
      by_cases hx : x ∈ G
      · rw [hin x hx] at h2
        exact Or.inl ⟨h2, (hmem x).mpr hx⟩
      · rw [hout x hx] at h2
        exact Or.inr ⟨h2, hxJ, hx⟩
    · rintro (⟨hSA, hSG'⟩ | ⟨hxA, hxJ, hxG⟩)
      · have hx : x ∈ G := (hmem x).mp hSG'
        refine ⟨?_, hGJ hx⟩
        show Φ x ∈ A
        rw [hin x hx]
        exact hSA
      · refine ⟨?_, hxJ⟩
        show Φ x ∈ A
        rw [hout x hxG]
        exact hxA
  have h2 : A ∩ J = A ∩ G ∪ A ∩ (J \ G) := by
    ext x
    constructor
    · rintro ⟨hxA, hxJ⟩
      by_cases hx : x ∈ G
      · exact Or.inl ⟨hxA, hx⟩
      · exact Or.inr ⟨hxA, hxJ, hx⟩
    · rintro (⟨hxA, hx⟩ | ⟨hxA, hxJ, _⟩)
      · exact ⟨hxA, hGJ hx⟩
      · exact ⟨hxA, hxJ⟩
  have hd1 : Disjoint (S ⁻¹' (A ∩ G)) (A ∩ (J \ G)) :=
    Set.disjoint_left.mpr fun x hx1 hx2 => hx2.2.2 ((hmem x).mp hx1.2)
  have hd2 : Disjoint (A ∩ G) (A ∩ (J \ G)) :=
    Set.disjoint_left.mpr fun x hx1 hx2 => hx2.2.2 hx1.2
  rw [h1, h2, measure_union hd1 (hA.inter (hJ.diff hG)),
    measure_union hd2 (hA.inter (hJ.diff hG)),
    hS.measure_preimage (hA.inter hG).nullMeasurableSet]

namespace GenerativeWorld

/-! ## The reflection of one split and one offset -/

/-- The reflection of a pair `(v, θ)`: `v` is the coordinate of a split and
`θ` an offset. The split `u` of `v` is replaced by `1 - u` and the offset
moves by `κ * (u - 1 / 2)`, when the offset lies between `-Θ` and `Θ` before
and after the move; otherwise the pair stays as it is. -/
def reflectPair (κ Θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.2 ∈ Set.Icc (-Θ) Θ ∧ p.2 + κ * (splitOf p.1 - 1 / 2) ∈ Set.Icc (-Θ) Θ then
    (1 - p.1, p.2 + κ * (splitOf p.1 - 1 / 2))
  else p

/-- The reflection moves the offset by `κ / 2` times how far it moves the
split, in the opposite direction. -/
theorem reflectPair_shift (κ Θ v θ : ℝ) :
    (splitOf (reflectPair κ Θ (v, θ)).1 - splitOf v) * κ
      = 2 * (θ - (reflectPair κ Θ (v, θ)).2) := by
  unfold reflectPair
  split_ifs with h
  · dsimp only
    rw [splitOf_one_sub]
    ring
  · simp

theorem measurable_reflectPair (κ Θ : ℝ) : Measurable (reflectPair κ Θ) := by
  have hshift : Measurable fun p : ℝ × ℝ => p.2 + κ * (splitOf p.1 - 1 / 2) :=
    measurable_snd.add (((measurable_splitOf.comp measurable_fst).sub_const _).const_mul κ)
  show Measurable fun p : ℝ × ℝ =>
    if p.2 ∈ Set.Icc (-Θ) Θ ∧ p.2 + κ * (splitOf p.1 - 1 / 2) ∈ Set.Icc (-Θ) Θ then
      ((1 - p.1, p.2 + κ * (splitOf p.1 - 1 / 2)) : ℝ × ℝ)
    else p
  refine Measurable.ite ?_ ((measurable_const.sub measurable_fst).prodMk hshift) measurable_id
  exact (measurableSet_Icc.preimage measurable_snd).inter (measurableSet_Icc.preimage hshift)

/-- **The reflection keeps the joint law of a split and an offset**: the
Beta law with equal parameters of the split, and the uniform law of the
offset. -/
theorem measurePreserving_reflectPair {α : ℝ} (hα : 0 < α) (κ Θ : ℝ) :
    MeasurePreserving (reflectPair κ Θ)
      ((betaMeasure α α).prod (ProbabilityTheory.cond volume (Set.Icc (-Θ) Θ)))
      ((betaMeasure α α).prod (ProbabilityTheory.cond volume (Set.Icc (-Θ) Θ))) := by
  have := isProbabilityMeasureBeta hα hα
  have hshift : Measurable fun p : ℝ × ℝ => p.2 + κ * (splitOf p.1 - 1 / 2) :=
    measurable_snd.add (((measurable_splitOf.comp measurable_fst).sub_const _).const_mul κ)
  -- Without the condition on the offset, the map keeps the law of the split
  -- times the Lebesgue measure.
  have hS : MeasurePreserving (fun p : ℝ × ℝ => (1 - p.1, p.2 + κ * (splitOf p.1 - 1 / 2)))
      ((betaMeasure α α).prod volume) ((betaMeasure α α).prod volume) := by
    have hf : MeasurePreserving (fun v : ℝ => 1 - v) (betaMeasure α α) (betaMeasure α α) :=
      ⟨measurable_const.sub measurable_id, betaMeasure_map_one_sub α⟩
    exact hf.skew_product (g := fun v θ => θ + κ * (splitOf v - 1 / 2)) hshift
      (ae_of_all _ fun v => (measurePreserving_add_right volume _).map_eq)
  have hG : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Icc (-Θ) Θ
      ∧ p.2 + κ * (splitOf p.1 - 1 / 2) ∈ Set.Icc (-Θ) Θ} :=
    (measurableSet_Icc.preimage measurable_snd).inter (measurableSet_Icc.preimage hshift)
  have hSG : (fun p : ℝ × ℝ => (1 - p.1, p.2 + κ * (splitOf p.1 - 1 / 2))) ⁻¹'
      {p : ℝ × ℝ | p.2 ∈ Set.Icc (-Θ) Θ ∧ p.2 + κ * (splitOf p.1 - 1 / 2) ∈ Set.Icc (-Θ) Θ}
      = {p : ℝ × ℝ | p.2 ∈ Set.Icc (-Θ) Θ
          ∧ p.2 + κ * (splitOf p.1 - 1 / 2) ∈ Set.Icc (-Θ) Θ} := by
    ext p
    have hback : p.2 + κ * (splitOf p.1 - 1 / 2) + κ * (splitOf (1 - p.1) - 1 / 2) = p.2 := by
      rw [splitOf_one_sub]
      ring
    show (p.2 + κ * (splitOf p.1 - 1 / 2) ∈ Set.Icc (-Θ) Θ
        ∧ p.2 + κ * (splitOf p.1 - 1 / 2) + κ * (splitOf (1 - p.1) - 1 / 2) ∈ Set.Icc (-Θ) Θ)
      ↔ (p.2 ∈ Set.Icc (-Θ) Θ ∧ p.2 + κ * (splitOf p.1 - 1 / 2) ∈ Set.Icc (-Θ) Θ)
    rw [hback]
    exact and_comm
  have hpiece := measurePreserving_restrict_of_eqOn hS hG
    (MeasurableSet.univ.prod (measurableSet_Icc (a := -Θ) (b := Θ)))
    (fun p hp => ⟨Set.mem_univ _, hp.1⟩) hSG (measurable_reflectPair κ Θ)
    (fun p hp => by
      unfold reflectPair
      exact ite_eq_left hp)
    (fun p hp => by
      unfold reflectPair
      exact ite_eq_right hp)
  have h1 : (betaMeasure α α).prod ((volume : Measure ℝ).restrict (Set.Icc (-Θ) Θ))
      = ((betaMeasure α α).prod volume).restrict (Set.univ ×ˢ Set.Icc (-Θ) Θ) := by
    have h := Measure.prod_restrict (μ := betaMeasure α α) (ν := (volume : Measure ℝ))
      Set.univ (Set.Icc (-Θ) Θ)
    rwa [Measure.restrict_univ] at h
  have hμ : (betaMeasure α α).prod (ProbabilityTheory.cond volume (Set.Icc (-Θ) Θ))
      = (volume (Set.Icc (-Θ) Θ))⁻¹
        • ((betaMeasure α α).prod volume).restrict (Set.univ ×ˢ Set.Icc (-Θ) Θ) :=
    calc (betaMeasure α α).prod (ProbabilityTheory.cond volume (Set.Icc (-Θ) Θ))
        = (betaMeasure α α).prod
            ((volume (Set.Icc (-Θ) Θ))⁻¹ • (volume : Measure ℝ).restrict (Set.Icc (-Θ) Θ)) := rfl
      _ = (volume (Set.Icc (-Θ) Θ))⁻¹
            • (betaMeasure α α).prod ((volume : Measure ℝ).restrict (Set.Icc (-Θ) Θ)) :=
          Measure.prod_smul_right _
      _ = _ := by rw [h1]
  rw [hμ]
  exact hpiece.smul_measure _

/-! ## The ideal constant world with shifted timelines -/

section World

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- **Shifting the timelines of an ideal constant world along the links to
and from the sender gives the ideal constant world with the shifted offsets
and delays.** The offset of each clock falls by the shift of its host, the
delay of a link to or from the sender grows by the shift of the receiving
end minus that of the sending end, and the other delays stay. -/
theorem idealWorld_shiftStarKeepPeers (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (θ : H → ℝ) (d : H → H → ℝ)
    (hd : ∀ i j, 0 < d i j) (X : H → ℝ) (hXs : X m.sender = 0) (θ' : H → ℝ)
    (d' : H → H → ℝ) (hd' : ∀ i j, 0 < d' i j) (hθ : ∀ h, θ' h = θ h - X h)
    (hstarD : ∀ i j, (i = m.sender ∨ j = m.sender) → d' i j = d i j + X j - X i)
    (hpeerD : ∀ i j, ¬(i = m.sender ∨ j = m.sender) → d' i j = d i j)
    (hstar : ∀ i j s q a, (i = (idealWorld m f hex θ d hd).sender
        ∨ j = (idealWorld m f hex θ d hd).sender) →
      (idealWorld m f hex θ d hd).network.deliver i j s q = some a → s + X i < a + X j) :
    idealWorld m f hex θ' d' hd' = shiftStarKeepPeers (idealWorld m f hex θ d hd) X hstar := by
  have hs : θ' m.sender = θ m.sender := by rw [hθ, hXs, sub_zero]
  refine World.ext_fields rfl rfl rfl ?_ ?_ ?_ ?_ rfl
  · funext h
    refine Clock.ext_read fun t => ?_
    show t + θ' h = t - X h + θ h
    rw [hθ]
    ring
  · refine CaptureDevice.ext_fields (fun n => ?_) (fun _ => rfl) (fun b => ?_) (fun _ => rfl)
    · show _ - θ' m.sender + _ = _ - θ m.sender + _
      rw [hs]
    · show _ - θ' m.sender + _ = _ - θ m.sender + _
      rw [hs]
  · funext r
    refine PlaybackDevice.ext_fields (fun k => ?_) (fun _ => rfl) (fun b => ?_) (fun _ => rfl)
    · show _ - θ' (m.host r) + _ = _ - θ (m.host r) + _ + X (m.host r)
      rw [hθ]
      ring
    · show _ - θ' (m.host r) + _ - _ = _ - θ (m.host r) + _ - _ + X (m.host r)
      rw [hθ]
      ring
  · refine Network.ext_deliver fun i j s q => ?_
    show some (s + d' i j)
      = if i = m.sender ∨ j = m.sender then (some (s - X i + d i j)).map (· + X j)
        else some (s + d i j)
    by_cases hsj : i = m.sender ∨ j = m.sender
    · rw [ite_eq_left hsj, hstarD i j hsj]
      simp only [Option.map_some]
      congr 1
      ring
    · rw [ite_eq_right hsj, hpeerD i j hsj]

end World

/-! ## The reflection of every receiving host -/

section Hosts

variable {H : Type} {R : ℕ} [DecidableEq H]

instance : DecidableEq (Component H) := (componentEquiv H).decidableEq

/-- A receiving host: a host other than the sender's. -/
abbrev ReceivingHost (m : GenerativeWorld H R) : Type := {h : H // h ≠ m.sender}

/-- The coordinate of the split of the pair of the sender and a receiving
host. -/
def senderSplit (m : GenerativeWorld H R) (k : m.ReceivingHost) : Component H :=
  .split (pairOf m.sender k.1 k.2.symm)

omit [DecidableEq H] in
theorem senderSplit_injective (m : GenerativeWorld H R) : Function.Injective m.senderSplit := by
  intro k k' e
  have e' : s(m.sender, k.1) = s(m.sender, k'.1) :=
    congrArg Subtype.val (Component.split.inj e)
  rcases Sym2.eq_iff.mp e' with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact Subtype.ext h2
  · exact absurd h2 k.2

omit [DecidableEq H] in
theorem senderSplit_ne_offset (m : GenerativeWorld H R) (k : m.ReceivingHost) (h : H) :
    m.senderSplit k ≠ .offset h := by
  simp [senderSplit]

/-- Twice the least round-trip time between the sender and a receiving host,
with a sign: plus when the fixed order of the pair has the sender first, and
minus otherwise. Times the split of the pair's coordinate minus one half, it
is twice the amount by which the delay from the sender to the host exceeds
half the round-trip time. -/
def reflectScale (m : GenerativeWorld H R) (f : Member H R) (k : m.ReceivingHost) : ℝ :=
  if (refOrientation H (pairOf m.sender k.1 k.2.symm)).1 = (m.sender, k.1) then
    2 * f.roundTrip m.sender k.1
  else -(2 * f.roundTrip m.sender k.1)

/-- The reflection of one receiving host: of the split of its pair with the
sender and of the offset of its clock. -/
def reflectHost (m : GenerativeWorld H R) (f : Member H R) (k : m.ReceivingHost) :
    (Component H → ℝ) → Component H → ℝ :=
  updatePair (m.senderSplit k) (.offset k.1) (reflectPair (reflectScale m f k) f.offsetRange)

/-- The reflections of the receiving hosts of a list, one after another. -/
def reflectList (m : GenerativeWorld H R) (f : Member H R) :
    List m.ReceivingHost → (Component H → ℝ) → Component H → ℝ
  | [] => id
  | k :: l => reflectHost m f k ∘ reflectList m f l

/-- The reflections of a list of hosts change no coordinate of other
hosts. -/
theorem reflectList_of_ne (m : GenerativeWorld H R) (f : Member H R) (l : List m.ReceivingHost)
    (y : Component H → ℝ) (p : Component H)
    (hp : ∀ k ∈ l, p ≠ m.senderSplit k ∧ p ≠ .offset k.1) : reflectList m f l y p = y p := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    have h1 := hp k (List.mem_cons.mpr (Or.inl rfl))
    change updatePair (m.senderSplit k) (.offset k.1) _ (reflectList m f l y) p = y p
    rw [updatePair_of_ne h1.1 h1.2]
    exact ih fun k' hk' => hp k' (List.mem_cons.mpr (Or.inr hk'))

/-- The reflections of a list of distinct hosts reflect the two coordinates
of each of its hosts once. -/
theorem reflectList_apply (m : GenerativeWorld H R) (f : Member H R) (l : List m.ReceivingHost)
    (hl : l.Nodup) (k : m.ReceivingHost) (hk : k ∈ l) (y : Component H → ℝ) :
    reflectList m f l y (m.senderSplit k)
        = (reflectPair (reflectScale m f k) f.offsetRange
            (y (m.senderSplit k), y (.offset k.1))).1
      ∧ reflectList m f l y (.offset k.1)
        = (reflectPair (reflectScale m f k) f.offsetRange
            (y (m.senderSplit k), y (.offset k.1))).2 := by
  induction l with
  | nil => simp at hk
  | cons k₀ l ih =>
    obtain ⟨hk₀, hl'⟩ := List.nodup_cons.mp hl
    by_cases hkk : k = k₀
    · subst hkk
      have hfix : ∀ p : Component H, (p = m.senderSplit k ∨ p = .offset k.1) →
          reflectList m f l y p = y p := by
        intro p hp
        refine reflectList_of_ne m f l y p fun k' hk' => ?_
        have hne : k' ≠ k := fun e => hk₀ (e ▸ hk')
        rcases hp with rfl | rfl
        · exact ⟨fun e => hne (m.senderSplit_injective e).symm, m.senderSplit_ne_offset k _⟩
        · exact ⟨(m.senderSplit_ne_offset k' _).symm,
            fun e => hne (Subtype.ext (Component.offset.inj e).symm)⟩
      have hab : m.senderSplit k ≠ .offset k.1 := m.senderSplit_ne_offset k _
      change updatePair (m.senderSplit k) (.offset k.1) _ (reflectList m f l y) (m.senderSplit k)
          = _
        ∧ updatePair (m.senderSplit k) (.offset k.1) _ (reflectList m f l y) (.offset k.1) = _
      rw [updatePair_left hab, updatePair_right, hfix _ (Or.inl rfl), hfix _ (Or.inr rfl)]
      exact ⟨rfl, rfl⟩
    · have hkl : k ∈ l := (List.mem_cons.mp hk).resolve_left hkk
      have h1 : m.senderSplit k ≠ m.senderSplit k₀ := fun e => hkk (m.senderSplit_injective e)
      have h2 : m.senderSplit k ≠ .offset k₀.1 := m.senderSplit_ne_offset k _
      have h3 : (Component.offset k.1 : Component H) ≠ m.senderSplit k₀ :=
        (m.senderSplit_ne_offset k₀ _).symm
      have h4 : (Component.offset k.1 : Component H) ≠ .offset k₀.1 := fun e =>
        hkk (Subtype.ext (Component.offset.inj e))
      change updatePair (m.senderSplit k₀) (.offset k₀.1) _ (reflectList m f l y)
            (m.senderSplit k) = _
        ∧ updatePair (m.senderSplit k₀) (.offset k₀.1) _ (reflectList m f l y) (.offset k.1) = _
      rw [updatePair_of_ne h1 h2, updatePair_of_ne h3 h4]
      exact ih hl' hkl

variable [Fintype H]

theorem measurePreserving_reflectHost (m : GenerativeWorld H R) (f : Member H R)
    (k : m.ReceivingHost) :
    MeasurePreserving (reflectHost m f k) (Measure.pi (canonicalLaw m f))
      (Measure.pi (canonicalLaw m f)) :=
  measurePreserving_updatePair (canonicalLaw m f) (m.senderSplit_ne_offset k _)
    (measurePreserving_reflectPair m.shape_pos _ f.offsetRange)

theorem measurePreserving_reflectList (m : GenerativeWorld H R) (f : Member H R)
    (l : List m.ReceivingHost) :
    MeasurePreserving (reflectList m f l) (Measure.pi (canonicalLaw m f))
      (Measure.pi (canonicalLaw m f)) := by
  induction l with
  | nil => exact MeasurePreserving.id _
  | cons k l ih => exact (measurePreserving_reflectHost m f k).comp ih

/-- **The reflection**: of the split of the pair of the sender and every
receiving host, and of the offset of that host's clock. -/
def reflect (m : GenerativeWorld H R) (f : Member H R) :
    (Component H → ℝ) → Component H → ℝ :=
  reflectList m f (Finset.univ : Finset m.ReceivingHost).toList

/-- **The reflection keeps the law of the outcomes.** -/
theorem measurePreserving_reflect (m : GenerativeWorld H R) (f : Member H R) :
    MeasurePreserving (reflect m f) (Measure.pi (canonicalLaw m f))
      (Measure.pi (canonicalLaw m f)) :=
  measurePreserving_reflectList m f _

theorem reflect_apply (m : GenerativeWorld H R) (f : Member H R) (k : m.ReceivingHost)
    (y : Component H → ℝ) :
    reflect m f y (m.senderSplit k)
        = (reflectPair (reflectScale m f k) f.offsetRange
            (y (m.senderSplit k), y (.offset k.1))).1
      ∧ reflect m f y (.offset k.1)
        = (reflectPair (reflectScale m f k) f.offsetRange
            (y (m.senderSplit k), y (.offset k.1))).2 :=
  reflectList_apply m f _ (Finset.nodup_toList _) k (Finset.mem_toList.mpr (Finset.mem_univ k)) y

theorem reflect_of_ne (m : GenerativeWorld H R) (f : Member H R) (y : Component H → ℝ)
    (p : Component H) (hp : ∀ k : m.ReceivingHost, p ≠ m.senderSplit k ∧ p ≠ .offset k.1) :
    reflect m f y p = y p :=
  reflectList_of_ne m f _ y p fun k _ => hp k

/-- How far the reflection shifts the timeline of each host: the offset of
its clock before the reflection minus the offset after it. -/
def reflectShift (m : GenerativeWorld H R) (f : Member H R) (y : Component H → ℝ) (h : H) : ℝ :=
  y (.offset h) - reflect m f y (.offset h)

/-- The reflection leaves the sender's timeline in place. -/
theorem reflectShift_sender (m : GenerativeWorld H R) (f : Member H R) (y : Component H → ℝ) :
    reflectShift m f y m.sender = 0 := by
  have h : reflect m f y (.offset m.sender) = y (.offset m.sender) :=
    reflect_of_ne m f y _ fun k =>
      ⟨(m.senderSplit_ne_offset k _).symm, fun e => k.2 (Component.offset.inj e).symm⟩
  rw [reflectShift, h, sub_self]

/-- The reflection changes the least delay from the sender to a receiving
host by the shift of that host's timeline. -/
theorem reflect_split_sender (m : GenerativeWorld H R) (f : Member H R) (y : Component H → ℝ)
    {h : H} (hne : h ≠ m.sender) :
    ((canonicalDraw (reflect m f y)).split m.sender h - (canonicalDraw y).split m.sender h)
        * f.roundTrip m.sender h
      = reflectShift m f y h := by
  have hsh : m.sender ≠ h := hne.symm
  obtain ⟨e1, e2⟩ := reflect_apply m f ⟨h, hne⟩ y
  have e1' : reflect m f y (.split (pairOf m.sender h hsh))
      = (reflectPair (reflectScale m f ⟨h, hne⟩) f.offsetRange
          (y (.split (pairOf m.sender h hsh)), y (.offset h))).1 := e1
  have e2' : reflect m f y (.offset h)
      = (reflectPair (reflectScale m f ⟨h, hne⟩) f.offsetRange
          (y (.split (pairOf m.sender h hsh)), y (.offset h))).2 := e2
  have hR := reflectPair_shift (reflectScale m f ⟨h, hne⟩) f.offsetRange
    (y (.split (pairOf m.sender h hsh))) (y (.offset h))
  rw [← e1', ← e2'] at hR
  have hs : ∀ z : Component H → ℝ, (canonicalDraw z).split m.sender h
      = if (refOrientation H (pairOf m.sender h hsh)).1 = (m.sender, h) then
          splitOf (z (.split (pairOf m.sender h hsh)))
        else 1 - splitOf (z (.split (pairOf m.sender h hsh))) := fun z => by
    simp only [canonicalDraw, dite_eq_right hsh]
  rw [hs, hs, reflectShift]
  by_cases ho : (refOrientation H (pairOf m.sender h hsh)).1 = (m.sender, h)
  · have hκ : reflectScale m f ⟨h, hne⟩ = 2 * f.roundTrip m.sender h := by
      unfold reflectScale
      exact ite_eq_left ho
    rw [hκ] at hR
    rw [ite_eq_left ho, ite_eq_left ho]
    linear_combination (1 / 2 : ℝ) * hR
  · have hκ : reflectScale m f ⟨h, hne⟩ = -(2 * f.roundTrip m.sender h) := by
      unfold reflectScale
      exact ite_eq_right ho
    rw [hκ] at hR
    rw [ite_eq_right ho, ite_eq_right ho]
    linear_combination (1 / 2 : ℝ) * hR

/-- The reflection changes no split of two hosts other than the sender. -/
theorem reflect_split_peer (m : GenerativeWorld H R) (f : Member H R) (y : Component H → ℝ)
    {i j : H} (hi : i ≠ m.sender) (hj : j ≠ m.sender) :
    (canonicalDraw (reflect m f y)).split i j = (canonicalDraw y).split i j := by
  by_cases hij : i = j
  · subst hij
    simp [canonicalDraw]
  · have hfix : reflect m f y (.split (pairOf i j hij)) = y (.split (pairOf i j hij)) := by
      refine reflect_of_ne m f y _ fun k => ⟨fun e => ?_, by simp⟩
      have e' : s(i, j) = s(m.sender, k.1) := congrArg Subtype.val (Component.split.inj e)
      rcases Sym2.eq_iff.mp e' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hi h1
      · exact hj h2
    simp only [canonicalDraw, dite_eq_right hij, hfix]

/-- The reflection changes the least delay of each link to or from the
sender by the shift of the receiving end minus the shift of the sending
end. -/
theorem reflect_delay_star (m : GenerativeWorld H R) (f : Member H R) (y : Component H → ℝ)
    {i j : H} (hs : i = m.sender ∨ j = m.sender) :
    (canonicalDraw (reflect m f y)).split i j * f.roundTrip i j
      = (canonicalDraw y).split i j * f.roundTrip i j + reflectShift m f y j
        - reflectShift m f y i := by
  by_cases hi : i = m.sender
  · rw [hi]
    by_cases hj : j = m.sender
    · rw [hj]
      have h1 : ∀ z : Component H → ℝ, (canonicalDraw z).split m.sender m.sender = 1 / 2 :=
        fun z => by simp [canonicalDraw]
      rw [h1, h1]
      ring
    · have h := reflect_split_sender m f y hj
      rw [reflectShift_sender]
      linear_combination h
  · have hj : j = m.sender := hs.resolve_left hi
    rw [hj]
    have h := reflect_split_sender m f y hi
    have h1 := canonicalDraw_split_swap (reflect m f y) i m.sender
    have h2 := canonicalDraw_split_swap y i m.sender
    rw [reflectShift_sender, f.roundTrip_symm i m.sender]
    linear_combination (-1 : ℝ) * h + f.roundTrip m.sender i * h1 - f.roundTrip m.sender i * h2

/-- Every message on a link to or from the sender still arrives after it is
sent when the timelines are shifted by the reflection. -/
theorem reflectShift_star (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : Component H → ℝ) :
    ∀ i j s q a, (i = (canonicalWorld m f hex y).sender ∨ j = (canonicalWorld m f hex y).sender) →
      (canonicalWorld m f hex y).network.deliver i j s q = some a →
        s + reflectShift m f y i < a + reflectShift m f y j := by
  intro i j s q a hs hdel
  have hdel' : some (s + (canonicalDraw y).split i j * f.roundTrip i j) = some a := hdel
  have ha : a = s + (canonicalDraw y).split i j * f.roundTrip i j :=
    (Option.some.inj hdel').symm
  have hpos : 0 < (canonicalDraw (reflect m f y)).split i j * f.roundTrip i j :=
    mul_pos (canonicalDraw_split_mem _ i j).1 (f.roundTrip_pos i j)
  rw [reflect_delay_star m f y hs] at hpos
  rw [ha]
  linarith

/-- **The world of the reflected outcome is the world of the outcome with
the timelines shifted along the links to and from the sender.** -/
theorem canonicalWorld_reflect (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : Component H → ℝ) :
    canonicalWorld m f hex (reflect m f y)
      = shiftStarKeepPeers (canonicalWorld m f hex y) (reflectShift m f y)
          (reflectShift_star m f hex y) :=
  idealWorld_shiftStarKeepPeers m f hex (canonicalDraw y).offset _ _ (reflectShift m f y)
    (reflectShift_sender m f y) (canonicalDraw (reflect m f y)).offset _ _
    (fun h => by
      show reflect m f y (.offset h) = y (.offset h) - (y (.offset h) - reflect m f y (.offset h))
      ring)
    (fun i j hs => reflect_delay_star m f y hs)
    (fun i j hs => by
      obtain ⟨hi, hj⟩ := not_or.mp hs
      show (canonicalDraw (reflect m f y)).split i j * f.roundTrip i j
        = (canonicalDraw y).split i j * f.roundTrip i j
      rw [reflect_split_peer m f y hi hj])
    (reflectShift_star m f hex y)

end Hosts

end GenerativeWorld

end Unisono.Spec
