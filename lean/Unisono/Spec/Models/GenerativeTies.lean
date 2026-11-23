/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeReflection

/-!
# Requests from different hosts reach the sender at different times

In the concrete random world of a noiseless member, consider the requests of
the playback devices, each delayed by the least delay from its host to the
sender. In almost every outcome, no two of them from different hosts reach
the sender at the same time (`ae_requestArrival_ne`).

The reason is that the offset of a host's clock has a uniform law, which
gives no single number a positive probability, and is independent of
everything else that the two times depend on. The general fact is
`measure_pi_graph_eq_zero`: among independent numbers, one whose law gives no
single number a positive probability equals a function of the others with
probability zero.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The uniform law on a set of real numbers gives no single number a
positive probability. -/
theorem cond_volume_singleton (I : Set ℝ) (x : ℝ) :
    ProbabilityTheory.cond volume I {x} = 0 := by
  have h0 : (volume : Measure ℝ).restrict I {x} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  show ((volume I)⁻¹ • (volume : Measure ℝ).restrict I) {x} = 0
  simp only [FunLike.coe_smul, Pi.smul_apply, h0, smul_zero]

/-- **Among independent numbers, one whose law gives no single number a
positive probability equals a function of the others with probability
zero.** -/
theorem measure_pi_graph_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (a : ι) (hμ : ∀ x : ℝ, μ a {x} = 0)
    {G : (ι → ℝ) → ℝ} (hG : Measurable G) (hGa : ∀ y, G (Function.update y a 0) = G y) :
    Measure.pi μ {y | y a = G y} = 0 := by
  have hind : iIndepFun (fun (i : ι) (y : ι → ℝ) => y i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have haS : a ∈ ({a} : Finset ι) := Finset.mem_singleton_self a
  -- The outcome with the number at `a` set to zero, from the other numbers.
  let φ : (↥(({a} : Finset ι)ᶜ) → ℝ) → ι → ℝ := fun u i =>
    if h : i ∈ ({a} : Finset ι)ᶜ then u ⟨i, h⟩ else 0
  have hφ : Measurable φ := by
    refine Measurable.of_eval fun i => ?_
    by_cases h : i ∈ ({a} : Finset ι)ᶜ
    · have hc : (fun u : ↥(({a} : Finset ι)ᶜ) → ℝ => φ u i) = fun u => u ⟨i, h⟩ := by
        funext u
        simp only [φ, h, ↓reduceDIte]
      rw [hc]
      exact measurable_pi_apply _
    · have hc : (fun u : ↥(({a} : Finset ι)ᶜ) → ℝ => φ u i) = fun _ => 0 := by
        funext u
        simp only [φ, h, ↓reduceDIte]
      rw [hc]
      exact measurable_const
  have hV : ∀ y : ι → ℝ,
      φ (fun i : ↥(({a} : Finset ι)ᶜ) => y i) = Function.update y a 0 := by
    intro y
    funext i
    by_cases h : i = a
    · have hi : i ∉ ({a} : Finset ι)ᶜ := by simp [h]
      simp only [φ, hi, ↓reduceDIte]
      rw [h, Function.update_self]
    · have hi : i ∈ ({a} : Finset ι)ᶜ := by simp [h]
      simp only [φ, hi, ↓reduceDIte]
      rw [Function.update_of_ne h]
  have e : (φ ∘ fun (y : ι → ℝ) (i : ↥(({a} : Finset ι)ᶜ)) => y i)
      = fun y => Function.update y a 0 := funext hV
  have hmeasU : Measurable fun y : ι → ℝ => y a := measurable_pi_apply a
  have hmeasV : Measurable fun y : ι → ℝ => Function.update y a (0 : ℝ) := by
    rw [← e]
    exact hφ.comp (Measurable.of_eval fun i => measurable_pi_apply _)
  have hUV : IndepFun (fun y : ι → ℝ => y a) (fun y : ι → ℝ => Function.update y a (0 : ℝ))
      (Measure.pi μ) := by
    rw [← e]
    exact (hind.indepFun_finset {a} ({a} : Finset ι)ᶜ disjoint_compl_right
      fun i => measurable_pi_apply i).comp
      (φ := fun u : ↥({a} : Finset ι) → ℝ => u ⟨a, haS⟩) (measurable_pi_apply _) hφ
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hmeasU.aemeasurable
    hmeasV.aemeasurable).mp hUV
  have ha : (Measure.pi μ).map (fun y : ι → ℝ => y a) = μ a :=
    (measurePreserving_eval μ a).map_eq
  have hΓ : MeasurableSet {q : ℝ × (ι → ℝ) | q.1 = G q.2} :=
    measurableSet_eq_fun measurable_fst (hG.comp measurable_snd)
  have hE : {y : ι → ℝ | y a = G y}
      = (fun y : ι → ℝ => (y a, Function.update y a (0 : ℝ))) ⁻¹'
          {q : ℝ × (ι → ℝ) | q.1 = G q.2} := by
    ext y
    show y a = G y ↔ y a = G (Function.update y a 0)
    rw [hGa]
  rw [hE, ← Measure.map_apply (hmeasU.prodMk hmeasV) hΓ, hjoint, ha,
    Measure.prod_apply_symm hΓ]
  have hz : ∀ z : ι → ℝ,
      μ a ((fun x : ℝ => (x, z)) ⁻¹' {q : ℝ × (ι → ℝ) | q.1 = G q.2}) = 0 := by
    intro z
    have hs : (fun x : ℝ => (x, z)) ⁻¹' {q : ℝ × (ι → ℝ) | q.1 = G q.2} = {G z} := by
      ext x
      exact Iff.rfl
    rw [hs]
    exact hμ _
  simp only [hz, lintegral_zero]

namespace GenerativeWorld

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- The splits of the draw of an outcome do not depend on the offsets. -/
theorem canonicalDraw_split_update (y : Component H → ℝ) (h : H) (v : ℝ) :
    (canonicalDraw (Function.update y (.offset h) v)).split = (canonicalDraw y).split := by
  have hu : ∀ z, Function.update y (Component.offset h) v (.split z) = y (.split z) := fun z =>
    Function.update_of_ne (by simp) _ _
  funext i j
  simp only [canonicalDraw, hu]

/-- When the request of block `b` of speaker `r`'s device would reach the
sender in the world of an outcome: the true time of the request plus the
least delay from the speaker's host to the sender. -/
def requestArrival (m : GenerativeWorld H R) (f : Member H R) (y : Component H → ℝ)
    (r : Fin R) (b : ℕ) : ℝ :=
  f.speakerStart r - y (.offset (m.host r)) + ((b * m.blockSize : ℕ) : ℝ) / m.rate - m.lead
    + (canonicalDraw y).split (m.host r) m.sender * f.roundTrip (m.host r) m.sender

theorem measurable_requestArrival (m : GenerativeWorld H R) (f : Member H R) (r : Fin R)
    (b : ℕ) : Measurable fun y : Component H → ℝ => requestArrival m f y r b :=
  (((measurable_const.sub (measurable_pi_apply _)).add measurable_const).sub
    measurable_const).add ((measurable_canonicalDraw_split _ _).mul_const _)

variable [Fintype H]

/-- Two requests of speakers on different hosts reach the sender at
different times, in almost every outcome. -/
theorem ae_requestArrival_ne_of_ne (m : GenerativeWorld H R) (f : Member H R) {r₁ r₂ : Fin R}
    (hne : m.host r₁ ≠ m.host r₂) (b₁ b₂ : ℕ) :
    ∀ᵐ y ∂Measure.pi (canonicalLaw m f),
      requestArrival m f y r₁ b₁ ≠ requestArrival m f y r₂ b₂ := by
  -- The offset of the first host's clock that would make the two times equal.
  let G : (Component H → ℝ) → ℝ := fun y =>
    (f.speakerStart r₁ + ((b₁ * m.blockSize : ℕ) : ℝ) / m.rate - m.lead)
      + (canonicalDraw y).split (m.host r₁) m.sender * f.roundTrip (m.host r₁) m.sender
      - requestArrival m f y r₂ b₂
  have hG : Measurable G :=
    (measurable_const.add ((measurable_canonicalDraw_split _ _).mul_const _)).sub
      (measurable_requestArrival m f r₂ b₂)
  have hoff : (Component.offset (m.host r₂) : Component H) ≠ .offset (m.host r₁) := fun e =>
    hne (Component.offset.inj e).symm
  have hGa : ∀ y, G (Function.update y (.offset (m.host r₁)) 0) = G y := by
    intro y
    simp only [G, requestArrival, canonicalDraw_split_update,
      Function.update_of_ne hoff]
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_)
    (measure_pi_graph_eq_zero (canonicalLaw m f) (.offset (m.host r₁))
      (fun x => cond_volume_singleton _ x) hG hGa)
  have heq : requestArrival m f y r₁ b₁ = requestArrival m f y r₂ b₂ := not_not.mp hy
  show y (.offset (m.host r₁)) = G y
  simp only [G]
  unfold requestArrival at heq ⊢
  linarith

/-- **Requests from different hosts reach the sender at different times.**
In almost every outcome of the concrete random world, no two requests of
speakers on different hosts, each delayed by the least delay from its host to
the sender, reach the sender at the same time. -/
theorem ae_requestArrival_ne (m : GenerativeWorld H R) (f : Member H R) :
    ∀ᵐ y ∂Measure.pi (canonicalLaw m f), ∀ (r₁ r₂ : Fin R) (b₁ b₂ : ℕ),
      m.host r₁ ≠ m.host r₂ → requestArrival m f y r₁ b₁ ≠ requestArrival m f y r₂ b₂ := by
  refine ae_all_iff.mpr fun r₁ => ae_all_iff.mpr fun r₂ => ae_all_iff.mpr fun b₁ =>
    ae_all_iff.mpr fun b₂ => ?_
  by_cases hne : m.host r₁ ≠ m.host r₂
  · filter_upwards [ae_requestArrival_ne_of_ne m f hne b₁ b₂] with y hy _
    exact hy
  · exact Filter.Eventually.of_forall fun y h => absurd h hne

omit [Fintype H] in
/-- In the world of an outcome, the request of block `b` of speaker `r`'s
device, sent on to the sender, arrives at `requestArrival`. -/
theorem canonicalWorld_deliver_request (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : Component H → ℝ) (r : Fin R)
    (b q : ℕ) :
    (canonicalWorld m f hex y).network.deliver (m.host r) m.sender
        (((canonicalWorld m f hex y).speaker r).asked b) q
      = some (requestArrival m f y r b) :=
  rfl

end GenerativeWorld

end Unisono.Spec
