/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Optimality
public import Unisono.Spec.StarShift
public import Unisono.Spec.Models.GenerativeReflection

/-!
# A lower bound for solutions through the sender

In a noiseless member of the generative model, with any number of hosts and
speakers, every star solution of a class pays at least `starLowerBound` in
expected cost (`StarSolutions.le_expectedCost`). A star
solution is one whose hosts exchange messages only with the sender.

* `StarSolutions` is the class of solutions that the bound holds for: the
  star solutions whose cost is a measurable function of what is drawn, whose
  run has an event after every true time, in whose run no two messages from
  different hosts arrive at one host at the same time, and which play every
  frame from some frame on. The last three are required in almost every
  outcome of every random world of the members in question.
* `starLowerBound` is the mean, over the outcomes of the concrete random
  world, of the cost of half the shifts of the reflection
  (`Unisono.Spec.Models.GenerativeReflection`).

The proof pairs every outcome with its reflection. A star solution plays the
same in the worlds of the two outcomes, which differ by a shift of the
hosts' timelines, so its costs in the two add up to at least twice the cost
of half the shift (`Solution.cost_shiftStarKeepPeers_add_ge`). The
reflection keeps the law of the outcomes, so the two costs have the same
mean.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {Msg : Type} {m : GenerativeWorld H R}
  {f : Member H R} {lookahead : ℕ+} {c : Weights}

/-- A property of the world holds almost surely for the member `f`: in almost
every outcome of every random world of the member. -/
def AlmostSurely (m : GenerativeWorld H R) (f : Member H R) (p : World H R → Prop) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → Draw H) (world : Ω → World H R),
    m.Prior f P D → (∀ ω, m.Builds f (D ω) (world ω)) → ∀ᵐ ω ∂P, p (world ω)

/-- **The solutions that a solution through the sender is compared with**,
for the members in `members`, a lookahead and weights. -/
structure StarSolutions (m : GenerativeWorld H R) (members : Member H R → Prop)
    (lookahead : ℕ+) (c : Weights) (Msg : Type) (τ : Solution H R Msg) : Prop where
  /-- Hosts exchange messages only with the sender. -/
  star : τ.IsStar m.sender
  /-- The cost is a measurable function of what is drawn. -/
  measurable : m.measurableCost members lookahead c Msg τ
  /-- Almost surely, the run has an event after every true time. -/
  progress : ∀ f, members f → m.AlmostSurely f fun w =>
    ∀ T : Time, ∃ n, T < τ.eventTime w lookahead n
  /-- Almost surely, no two messages from different hosts arrive at one host
  at the same time. -/
  no_collision : ∀ f, members f → m.AlmostSurely f fun w => τ.NoCrossOriginCollision w lookahead
  /-- Almost surely, every speaker plays every frame from some frame on. -/
  plays : ∀ f, members f → m.AlmostSurely f fun w =>
    ∃ N, ∀ n, N ≤ n → ∀ r, (w.playTime (τ.plays w lookahead) r n).isSome

section Canonical

variable [Fintype H]

/-- For a noiseless member, a property holds almost surely exactly when it
holds in almost every outcome of the concrete random world. -/
theorem almostSurely_iff (m : GenerativeWorld H R) (f : Member H R) (hf : f.Noiseless)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (p : World H R → Prop) :
    m.AlmostSurely f p
      ↔ ∀ᵐ y ∂Measure.pi (canonicalLaw m f), p (canonicalWorld m f hex y) :=
  ⟨fun h => h _ _ canonicalDraw _ (canonicalDraw_prior m f hf) (canonicalWorld_builds m f hex),
    fun h _ _ _ _ _ hD hB => hD.ae_of_ae_canonical hf hB hex h⟩

/-- The cost of a solution whose cost is a measurable function of what is
drawn is measurable on the concrete random world of a noiseless member. -/
theorem aemeasurable_cost {members : Member H R → Prop} {τ : Solution H R Msg}
    (hτ : m.measurableCost members lookahead c Msg τ) (hmem : members f) (hf : f.Noiseless)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) :
    AEMeasurable (fun y => τ.cost (canonicalWorld m f hex y) lookahead c)
      (Measure.pi (canonicalLaw m f)) := by
  obtain ⟨F, hF, hFeq⟩ := hτ f hmem
  have h := hFeq _ (Measure.pi (canonicalLaw m f)) canonicalDraw (canonicalWorld m f hex)
    (canonicalDraw_prior m f hf) (canonicalWorld_builds m f hex)
  exact (hF.comp measurable_canonicalDraw).aemeasurable.congr (Filter.EventuallyEq.symm h)

/-- **The expected cost of a solution is the same in every random world of a
noiseless member**: its mean cost in the concrete random world. -/
theorem expectedCost_eq_canonical {members : Member H R → Prop} {τ : Solution H R Msg}
    (hτ : m.measurableCost members lookahead c Msg τ) (hmem : members f) (hf : f.Noiseless)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {world : Ω → World H R} (hW : m.Holds f P world) :
    τ.expectedCost P world lookahead c
      = ∫⁻ y, τ.cost (canonicalWorld m f hex y) lookahead c ∂Measure.pi (canonicalLaw m f) := by
  obtain ⟨D, hD, hB⟩ := hW
  exact hD.lintegral_eq_canonical hf hB hex (F := fun w => τ.cost w lookahead c)
    (aemeasurable_cost hτ hmem hf hex)

omit [Fintype H] in
/-- The capture device of the world of an outcome captures frames after
every true time. -/
theorem capture_unbounded_canonical (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : Component H → ℝ) (T : Time) :
    ∃ n, T ≤ (canonicalWorld m f hex y).source.capture n := by
  obtain ⟨n, hn⟩ := exists_nat_ge ((T - (f.captureStart - y (.offset m.sender))) * m.rate)
  refine ⟨n, ?_⟩
  show T ≤ f.captureStart - y (.offset m.sender) + (n : ℝ) / m.rate
  rw [← sub_le_iff_le_add', le_div_iff₀ m.rate_pos]
  exact hn

/-- A lower bound on the expected cost of every compared solution through
the sender, for a noiseless member: the mean, over the outcomes of the
concrete random world, of the cost of half the shifts of the reflection. -/
def starLowerBound (m : GenerativeWorld H R) (f : Member H R) (c : Weights) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (shiftCost c fun r => reflectShift m f y (m.host r) / 2)
    ∂Measure.pi (canonicalLaw m f)

/-- The lower bound holds on the concrete random world. -/
theorem StarSolutions.le_canonical {members : Member H R → Prop} {τ : Solution H R Msg}
    (hτ : m.StarSolutions members lookahead c Msg τ) (hmem : members f) (hf : f.Noiseless)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (hR : 0 < R) :
    starLowerBound m f c
      ≤ ∫⁻ y, τ.cost (canonicalWorld m f hex y) lookahead c ∂Measure.pi (canonicalLaw m f) := by
  have hcostm := aemeasurable_cost hτ.measurable hmem hf hex
  have hprog := (almostSurely_iff m f hf hex _).mp (hτ.progress f hmem)
  have hcoll := (almostSurely_iff m f hf hex _).mp (hτ.no_collision f hmem)
  have hplay := (almostSurely_iff m f hf hex _).mp (hτ.plays f hmem)
  have hT := measurePreserving_reflect m f
  have hprog' := hT.quasiMeasurePreserving.ae hprog
  -- In almost every outcome, the costs in the outcome and in its reflection
  -- add up to at least twice the cost of half the shift.
  have hpoint : ∀ᵐ y ∂Measure.pi (canonicalLaw m f),
      ENNReal.ofReal (2 * shiftCost c fun r => reflectShift m f y (m.host r) / 2)
        ≤ τ.cost (canonicalWorld m f hex y) lookahead c
          + τ.cost (canonicalWorld m f hex (reflect m f y)) lookahead c := by
    filter_upwards [hprog, hcoll, hplay, hprog'] with y h1 h2 h3 h4
    obtain ⟨N, hN⟩ := h3
    rw [canonicalWorld_reflect m f hex y] at h4 ⊢
    exact τ.cost_shiftStarKeepPeers_add_ge (canonicalWorld m f hex y) lookahead c hτ.star
      (reflectShift m f y) (reflectShift_sender m f y) (reflectShift_star m f hex y) h1 h4 h2
      hR N hN (capture_unbounded_canonical m f hex y)
  -- The reflection keeps the law, so the two costs have the same mean.
  have hinv : ∫⁻ y, τ.cost (canonicalWorld m f hex (reflect m f y)) lookahead c
        ∂Measure.pi (canonicalLaw m f)
      = ∫⁻ y, τ.cost (canonicalWorld m f hex y) lookahead c ∂Measure.pi (canonicalLaw m f) := by
    have h := lintegral_map' (μ := Measure.pi (canonicalLaw m f)) (g := reflect m f)
      (f := fun y => τ.cost (canonicalWorld m f hex y) lookahead c)
      (by rw [hT.map_eq]; exact hcostm) hT.measurable.aemeasurable
    rw [hT.map_eq] at h
    exact h.symm
  have hdouble : ∫⁻ y, ENNReal.ofReal (2 * shiftCost c fun r => reflectShift m f y (m.host r) / 2)
        ∂Measure.pi (canonicalLaw m f)
      = 2 * starLowerBound m f c := by
    rw [starLowerBound, ← lintegral_const_mul' (2 : ℝ≥0∞) _ ENNReal.ofNat_ne_top]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have h2 : 2 * starLowerBound m f c
      ≤ 2 * ∫⁻ y, τ.cost (canonicalWorld m f hex y) lookahead c
          ∂Measure.pi (canonicalLaw m f) := by
    rw [← hdouble]
    refine (lintegral_mono_ae hpoint).trans_eq ?_
    rw [lintegral_add_left' hcostm, hinv, two_mul]
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp h2

/-- **What no solution through the sender can avoid.** In every random world
of a noiseless member, with any number of hosts and speakers, the expected
cost of every compared star solution is at least `starLowerBound`. -/
theorem StarSolutions.le_expectedCost {members : Member H R → Prop}
    {τ : Solution H R Msg} (hτ : m.StarSolutions members lookahead c Msg τ) (hmem : members f)
    (hf : f.Noiseless) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (hR : 0 < R) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {world : Ω → World H R} (hW : m.Holds f P world) :
    starLowerBound m f c ≤ τ.expectedCost P world lookahead c := by
  rw [expectedCost_eq_canonical hτ.measurable hmem hf hex hW]
  exact hτ.le_canonical hmem hf hex hR

end Canonical

end Unisono.Spec.GenerativeWorld
