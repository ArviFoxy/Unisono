/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Optimality
public import Unisono.Spec.ShiftedPlayback
public import Unisono.Spec.StarShift
public import Unisono.Spec.Models.GenerativeReflection

/-!
# A lower bound for solutions through the sender

In a noiseless member of the generative model, with any number of hosts and
speakers, every star solution of a class pays at least `starLowerBound` in
expected cost (`StarSolutions.le_expectedCost`), when the weight of missed
samples is large enough for the member. A star solution is one whose hosts
exchange messages only with the sender.

* `StarSolutions` is the class of solutions that the bound holds for at a
  member, for a speed bound `u`: the star solutions whose cost in that
  member is a measurable function of what is drawn, and whose position
  advances by one frame per output sample within `u`, in every step of
  continuous playback, in almost every outcome of every random world of the
  member. The class asks nothing about which frames a solution plays,
  nothing about its run, and nothing of a solution in other members.
* `starLowerBound` is the mean, over the outcomes of the concrete random
  world, of the cost of half the shifts of the reflection
  (`Unisono.Spec.Models.GenerativeReflection`).

Without the speed bound no lower bound holds: a playback whose position
creeps forward without ever reaching the next frame plays no frame, counts
no missed sample and no discontinuity, and costs nothing.

The proof pairs every outcome with its reflection. A star solution plays the
same in the worlds of the two outcomes, which differ by a shift of the
hosts' timelines, so its costs in the two add up to at least twice the cost
of half the shift (`Solution.cost_shiftStar_add_ge_of_step`); the missed
samples pay for the frames that a speaker never plays. The reflection keeps
the law of the outcomes, so the two costs have the same mean.
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
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → Draw H R) (world : Ω → World H R),
    m.Prior f P D → (∀ ω, m.Builds f (D ω) (world ω)) → ∀ᵐ ω ∂P, p (world ω)

/-- **The solutions that a solution through the sender is compared with at
the member `f`**, for a lookahead, weights and a speed bound `u`. -/
structure StarSolutions (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+)
    (c : Weights) (u : ℝ) (Msg : Type) (τ : Solution H R Msg) : Prop where
  /-- Hosts exchange messages only with the sender. -/
  star : τ.IsStar m.sender
  /-- The cost in the member is a measurable function of what is drawn. -/
  measurable : m.measurableCost f lookahead c Msg τ
  /-- Almost surely, the position advances by one frame per output sample
  within `u`, in every step of continuous playback. -/
  withinStep : m.AlmostSurely f fun w => τ.WithinStep w lookahead u

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
theorem aemeasurable_cost {τ : Solution H R Msg}
    (hτ : m.measurableCost f lookahead c Msg τ) (hf : f.Noiseless)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) :
    AEMeasurable (fun y => τ.cost (canonicalWorld m f hex y) lookahead c)
      (Measure.pi (canonicalLaw m f)) := by
  obtain ⟨F, hF, hFeq⟩ := hτ
  have h := hFeq _ (Measure.pi (canonicalLaw m f)) canonicalDraw (canonicalWorld m f hex)
    (canonicalDraw_prior m f hf) (canonicalWorld_builds m f hex)
  exact (hF.comp measurable_canonicalDraw).aemeasurable.congr (Filter.EventuallyEq.symm h)

/-- **The expected cost of a solution is the same in every random world of a
noiseless member**: its mean cost in the concrete random world. -/
theorem expectedCost_eq_canonical {τ : Solution H R Msg}
    (hτ : m.measurableCost f lookahead c Msg τ) (hf : f.Noiseless)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {world : Ω → World H R} (hW : m.Holds f P world) :
    τ.expectedCost P world lookahead c
      = ∫⁻ y, τ.cost (canonicalWorld m f hex y) lookahead c ∂Measure.pi (canonicalLaw m f) := by
  obtain ⟨D, hD, hB⟩ := hW
  exact hD.lintegral_eq_canonical hf hB hex (F := fun w => τ.cost w lookahead c)
    (aemeasurable_cost hτ hf hex)

omit [Fintype H] in
/-- The capture device of the world of an outcome captures frames after
every true time. -/
theorem capture_unbounded_canonical (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : Component H R → ℝ) (T : Time) :
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

/-- The lower bound holds on the concrete random world, when the weight of
missed samples is large enough in every outcome. -/
theorem StarSolutions.le_canonical {τ : Solution H R Msg} {u : ℝ}
    (hτ : m.StarSolutions f lookahead c u Msg τ) (hf : f.Noiseless)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (hR : 0 < R) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hthr : ∀ y r, 6 * speakerShiftCost c (fun r => reflectShift m f y (m.host r) / 2) r
      ≤ (c.missed : ℝ) * (1 - u) * m.rate) :
    starLowerBound m f c
      ≤ ∫⁻ y, τ.cost (canonicalWorld m f hex y) lookahead c ∂Measure.pi (canonicalLaw m f) := by
  have hcostm := aemeasurable_cost hτ.measurable hf hex
  have hstep := (almostSurely_iff m f hf hex _).mp hτ.withinStep
  have hT := measurePreserving_reflect m f
  -- In almost every outcome, the costs in the outcome and in its reflection
  -- add up to at least twice the cost of half the shift.
  have hpoint : ∀ᵐ y ∂Measure.pi (canonicalLaw m f),
      ENNReal.ofReal (2 * shiftCost c fun r => reflectShift m f y (m.host r) / 2)
        ≤ τ.cost (canonicalWorld m f hex y) lookahead c
          + τ.cost (canonicalWorld m f hex (reflect m f y)) lookahead c := by
    filter_upwards [hstep] with y h1
    rw [canonicalWorld_reflect m f hex y]
    refine τ.cost_shiftStar_add_ge_of_step (canonicalWorld m f hex y) lookahead c hτ.star
      (reflectShift m f y) (reflectShift_sender m f y) (reflectShift_star m f hex y) hR
      m.rate_pos (t₀ := f.captureStart - (canonicalDraw y).offset m.sender) (fun n => rfl)
      (fun r => f.speakerStart (m.device r) - (canonicalDraw y).offset (m.host r))
      (fun r k => rfl) (fun r T => ?_) hu0 hu1 h1 (hthr y)
    -- Every playback device requests blocks without end.
    obtain ⟨b, hb⟩ := exists_nat_gt ((T + m.lead
      - (f.speakerStart (m.device r) - (canonicalDraw y).offset (m.host r))) * m.rate)
    refine ⟨b, ?_⟩
    show T < f.speakerStart (m.device r) - (canonicalDraw y).offset (m.host r)
      + ((b * m.blockSize : ℕ) : ℝ) / m.rate - m.lead
    have hbs : (b : ℝ) ≤ ((b * m.blockSize : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_right b m.blockSize_pos
    have h2 : (b : ℝ) / m.rate ≤ ((b * m.blockSize : ℕ) : ℝ) / m.rate :=
      div_le_div_of_nonneg_right hbs m.rate_pos.le
    have h3 : T + m.lead - (f.speakerStart (m.device r) - (canonicalDraw y).offset (m.host r))
        < (b : ℝ) / m.rate := by rwa [lt_div_iff₀ m.rate_pos]
    linarith
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

/-- **What no solution through the sender within a speed bound can avoid.**
Consider a noiseless member, with any number of hosts and speakers, and a
speed bound `u < 1`. Let the weight of missed samples be large enough in
every outcome: `6 * speakerShiftCost` of half the shifts of the reflection
is at most `c.missed * (1 - u) * m.rate`, for every speaker. Then in every
random world of the member the expected cost of every compared star solution
is at least `starLowerBound`. -/
theorem StarSolutions.le_expectedCost {τ : Solution H R Msg} {u : ℝ}
    (hτ : m.StarSolutions f lookahead c u Msg τ) (hf : f.Noiseless)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (hR : 0 < R) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hthr : ∀ y r, 6 * speakerShiftCost c (fun r => reflectShift m f y (m.host r) / 2) r
      ≤ (c.missed : ℝ) * (1 - u) * m.rate)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {world : Ω → World H R}
    (hW : m.Holds f P world) :
    starLowerBound m f c ≤ τ.expectedCost P world lookahead c := by
  rw [expectedCost_eq_canonical hτ.measurable hf hex hW]
  exact hτ.le_canonical hf hex hR hu0 hu1 hthr

end Canonical

end Unisono.Spec.GenerativeWorld
