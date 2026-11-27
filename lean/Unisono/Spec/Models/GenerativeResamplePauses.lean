/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeResample

/-!
# Drawing the pauses of all links again

In a random world of any member of the generative model, the paused times of
the links are independent of the rest of the draw: the splits, the clocks of
the hosts and of the audio devices, the errors of the reports, and the
paused times of the hosts. So the pauses of the links can be drawn again
from a second, independent outcome. The pauses of the hosts stay with the
rest of the draw, because a host handles the events of its audio devices
after its backlog: they decide when the devices' events are handled.

* `Draw.withLinks`: a draw with the links' paused times of another draw.
* `Prior.indepFun_withLinks`: the paused times of the links are independent
  of the rest of the draw.
* `resampleLinks`: on two copies of the probability space, the draw of the
  first outcome with the links' paused times of the second outcome.
* `Prior.map_resampleLinks`, `Prior.prior_resampleLinks`,
  `Prior.exists_resampleLinks`: this draw has the law of the draw, it is
  the draw of a random world of the same member, and it builds a world for
  every pair of outcomes.
* `expectedCost_resampleLinks`: the expected cost of a solution whose cost
  is a measurable function of what is drawn is the mean, over the first
  outcome, of its mean cost over the second outcome.

For a fixed first outcome, the worlds of the second random world have the
same clocks, the same pauses of the hosts and the same audio devices: every
time of capture, of handover, of request and of output is a number, and only
the pauses of the links are random. This is the
setting in which a pause can be compared with the room that a solution kept
for it. No bound on a cost is proved here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-- The draw `d` with the paused times of the links of the draw `e`. -/
def Draw.withLinks (d e : Draw H R) : Draw H R :=
  { d with linkPaused := e.linkPaused }

/-- Whether a component of a draw is the paused time of a link. -/
def Component.isLink : Component H R → Bool
  | .linkPaused _ _ => true
  | _ => false

/-- A draw with the paused times of another draw is a measurable function of
the two draws. -/
theorem measurable_withLinks :
    Measurable fun q : Draw H R × Draw H R => q.1.withLinks q.2 := by
  have h1 : Measurable fun q : Draw H R × Draw H R => q.1.split :=
    measurable_draw_split.comp measurable_fst
  have h2 : Measurable fun q : Draw H R × Draw H R => q.1.offset :=
    measurable_draw_offset.comp measurable_fst
  have h3 : Measurable fun q : Draw H R × Draw H R => q.1.logRate :=
    measurable_draw_logRate.comp measurable_fst
  have h4 : Measurable fun q : Draw H R × Draw H R => q.1.wander :=
    measurable_draw_wander.comp measurable_fst
  have h5 : Measurable fun q : Draw H R × Draw H R => q.2.linkPaused :=
    measurable_draw_linkPaused.comp measurable_snd
  have h6 : Measurable fun q : Draw H R × Draw H R => q.1.hostPaused :=
    measurable_draw_hostPaused.comp measurable_fst
  have h7 : Measurable fun q : Draw H R × Draw H R => q.1.deviceLogRate :=
    measurable_draw_deviceLogRate.comp measurable_fst
  have h8 : Measurable fun q : Draw H R × Draw H R => q.1.deviceWander :=
    measurable_draw_deviceWander.comp measurable_fst
  have h9 : Measurable fun q : Draw H R × Draw H R => q.1.reportError :=
    measurable_draw_reportError.comp measurable_fst
  exact measurable_draw h1 h2 h3 h4 h5 h6 h7 h8 h9

variable {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R} {f : Member H R}
  {P : Measure Ω} {D : Ω → Draw H R}

/-- **In a random world, the paused times of the links are independent of
the rest of the draw.** For any fixed draw `d₀`: the draw with the links'
paused times of `d₀` is independent of the draw `d₀` with the links' paused
times of the draw. -/
theorem Prior.indepFun_withLinks [DecidableEq H] (hD : m.Prior f P D)
    (hm : AEMeasurable D P) (d₀ : Draw H R) :
    IndepFun (fun ω => (D ω).withLinks d₀) (fun ω => d₀.withLinks (D ω)) P := by
  have hIJ : Disjoint {p : Component H R | p.isLink = false}
      {p : Component H R | p.isLink = true} :=
    Set.disjoint_left.mpr fun p (h1 : p.isLink = false) (h2 : p.isLink = true) => by
      rw [h1] at h2
      exact Bool.false_ne_true h2
  have h := iIndepFun.indepFun_set₀ hIJ (hD.independent (refOrientation H))
    (fun p => (measurable_component (refOrientation H) p).comp_aemeasurable hm)
  have hswap : ∀ ω i j, (D ω).split i j + (D ω).split j i = 1 := hD.split_swap
  rw [IndepFun_iff_Indep] at h ⊢
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · -- Every part of the rest of the draw is a function of the other components.
    let _ : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (p : {p : Component H R | p.isLink = false}) =>
        (D ω).component (refOrientation H) p) inferInstance
    have hCI : Measurable fun ω (p : {p : Component H R | p.isLink = false}) =>
        (D ω).component (refOrientation H) p := comap_measurable _
    have hcoord : ∀ (p : Component H R) (hp : p.isLink = false),
        Measurable fun ω => (D ω).component (refOrientation H) p := fun p hp =>
      measurable_pi_iff.mp hCI ⟨p, hp⟩
    have hU : Measurable fun ω => (D ω).withLinks d₀ := by
      refine measurable_draw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
        by_cases hij : i = j
        · have e : (fun ω => ((D ω).withLinks d₀).split i j) = fun _ => 1 / 2 :=
            funext fun ω => by
              have hs := hswap ω i j
              rw [← hij] at hs
              show (D ω).split i j = 1 / 2
              rw [← hij]
              linarith
          rw [e]
          exact measurable_const
        · have hc : Measurable fun ω =>
              (D ω).split (refOrientation H (pairOf i j hij)).1.1
                (refOrientation H (pairOf i j hij)).1.2 :=
            hcoord (.split (pairOf i j hij)) rfl
          rcases refOrientation_pairOf i j hij with hp | hp
          · have e : (fun ω => ((D ω).withLinks d₀).split i j)
                = fun ω => (D ω).split (refOrientation H (pairOf i j hij)).1.1
                    (refOrientation H (pairOf i j hij)).1.2 := funext fun ω => by
              rw [hp]
              rfl
            rw [e]
            exact hc
          · have e : (fun ω => ((D ω).withLinks d₀).split i j)
                = fun ω => 1 - (D ω).split (refOrientation H (pairOf i j hij)).1.1
                    (refOrientation H (pairOf i j hij)).1.2 := funext fun ω => by
              rw [hp]
              have hs := hswap ω i j
              show (D ω).split i j = 1 - (D ω).split j i
              linarith
            rw [e]
            exact measurable_const.sub hc
      · exact measurable_pi_iff.mpr fun h => hcoord (.offset h) rfl
      · exact measurable_pi_iff.mpr fun h => hcoord (.logRate h) rfl
      · exact measurable_pi_iff.mpr fun h => hcoord (.wander h) rfl
      · show Measurable fun _ : Ω => d₀.linkPaused
        exact measurable_const
      · exact measurable_pi_iff.mpr fun h => hcoord (.hostPaused h) rfl
      · exact measurable_pi_iff.mpr fun x => hcoord (.deviceLogRate x) rfl
      · exact measurable_pi_iff.mpr fun x => hcoord (.deviceWander x) rfl
      · exact measurable_pi_iff.mpr fun x => hcoord (.reportError x) rfl
    exact measurable_iff_comap_le.mp hU
  · -- The paused times are the components that were set aside.
    let _ : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (p : {p : Component H R | p.isLink = true}) =>
        (D ω).component (refOrientation H) p) inferInstance
    have hCJ : Measurable fun ω (p : {p : Component H R | p.isLink = true}) =>
        (D ω).component (refOrientation H) p := comap_measurable _
    have hcoord : ∀ (p : Component H R) (hp : p.isLink = true),
        Measurable fun ω => (D ω).component (refOrientation H) p := fun p hp =>
      measurable_pi_iff.mp hCJ ⟨p, hp⟩
    have hV : Measurable fun ω => d₀.withLinks (D ω) := by
      refine measurable_draw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · show Measurable fun _ : Ω => d₀.split
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.offset
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.logRate
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.wander
        exact measurable_const
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          hcoord (.linkPaused i j) rfl
      · show Measurable fun _ : Ω => d₀.hostPaused
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.deviceLogRate
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.deviceWander
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.reportError
        exact measurable_const
    exact measurable_iff_comap_le.mp hV

/-! ## The pauses of a second outcome -/

/-- The random draw `D` with the pauses of all links drawn again: on two
copies of the probability space, the draw of the first outcome with the
paused times of the links of the second outcome. -/
def resampleLinks (D : Ω → Draw H R) (ω : Ω × Ω) : Draw H R :=
  (D ω.1).withLinks (D ω.2)

/-- The draw with the pauses of all links drawn again is measurable up to a set of
probability zero. -/
theorem aemeasurable_resampleLinks [SFinite P] (hm : AEMeasurable D P) :
    AEMeasurable (resampleLinks D) (P.prod P) :=
  measurable_withLinks.comp_aemeasurable (hm.prodMap hm)

/-- **The draw with the pauses of all links drawn again has the law of the draw.** -/
theorem Prior.map_resampleLinks [DecidableEq H] (hD : m.Prior f P D)
    (hm : AEMeasurable D P) : (P.prod P).map (resampleLinks D) = P.map D := by
  have := hD.prob
  obtain ⟨d₀⟩ : Nonempty (Draw H R) := by
    have hne : Nonempty Ω := by
      by_contra hcon
      have hemp : IsEmpty Ω := not_nonempty_iff.mp hcon
      have h1 : P Set.univ = 0 := by
        rw [Set.univ_eq_empty_iff.mpr hemp, measure_empty]
      rw [measure_univ] at h1
      exact one_ne_zero h1
    exact ⟨D (Classical.choice hne)⟩
  have hA0 : Measurable fun d : Draw H R => d.withLinks d₀ :=
    measurable_withLinks.comp (measurable_id.prodMk measurable_const)
  have hB0 : Measurable fun d : Draw H R => d₀.withLinks d :=
    measurable_withLinks.comp (measurable_const.prodMk measurable_id)
  have hA : AEMeasurable (fun ω => (D ω).withLinks d₀) P := hA0.comp_aemeasurable hm
  have hB : AEMeasurable (fun ω => d₀.withLinks (D ω)) P := hB0.comp_aemeasurable hm
  have hind := hD.indepFun_withLinks hm d₀
  have h1 : (P.prod P).map (Prod.map (fun ω => (D ω).withLinks d₀)
        (fun ω => d₀.withLinks (D ω)))
      = P.map (fun ω => ((D ω).withLinks d₀, d₀.withLinks (D ω))) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hA hB).mp hind,
      Measure.map_prod_map_of_aemeasurable P P hA hB]
  have e1 : resampleLinks D
      = (fun q : Draw H R × Draw H R => q.1.withLinks q.2)
        ∘ Prod.map (fun ω => (D ω).withLinks d₀) (fun ω => d₀.withLinks (D ω)) := rfl
  have e2 : (fun q : Draw H R × Draw H R => q.1.withLinks q.2)
        ∘ (fun ω => ((D ω).withLinks d₀, d₀.withLinks (D ω)))
      = D := rfl
  rw [e1, ← AEMeasurable.map_map_of_aemeasurable measurable_withLinks.aemeasurable
      (hA.prodMap hB), h1,
    AEMeasurable.map_map_of_aemeasurable measurable_withLinks.aemeasurable (hA.prodMk hB),
    e2]

/-- **The draw with the pauses of all links drawn again is the draw of a random world
of the same member.** -/
theorem Prior.prior_resampleLinks [DecidableEq H] [Countable H] (hD : m.Prior f P D) :
    m.Prior f (P.prod P) (resampleLinks D) := by
  have := hD.prob
  have hm := hD.aemeasurable
  exact hD.of_map_eq hm inferInstance (aemeasurable_resampleLinks hm)
    (hD.map_resampleLinks hm) (fun ω i j => hD.split_swap ω.1 i j)
    (fun ω i j => hD.split_mem ω.1 i j) (fun ω h => hD.wander_continuous ω.1 h)
    (fun ω x => hD.deviceWander_continuous ω.1 x) (fun ω x => hD.reportError_continuous ω.1 x)
    (fun ω i j => hD.linkPaused_monotone ω.2 i j) (fun ω i j => hD.linkPaused_zero ω.2 i j)
    (fun ω i j t => hD.linkPaused_rightContinuous ω.2 i j t)
    (fun ω h => hD.hostPaused_monotone ω.1 h) (fun ω h => hD.hostPaused_zero ω.1 h)
    (fun ω h t => hD.hostPaused_rightContinuous ω.1 h t)

/-- **The draw with the pauses of all links drawn again builds a world**, for every
pair of outcomes: the world of the first outcome with the deliveries that
the pauses of the second outcome give. -/
theorem Prior.exists_resampleLinks [DecidableEq H] (hD : m.Prior f P D)
    {world : Ω → World H R} (hB : ∀ ω, m.Builds f (D ω) (world ω)) (ω : Ω × Ω) :
    ∃ w' : World H R, m.Builds f (resampleLinks D ω) w' :=
  (hB ω.1).exists_of_paused rfl rfl rfl rfl rfl rfl rfl
    (fun i j => hD.leastDelay_pos ω.1 i j) rfl
    fun i j t => (hB ω.2).bddAbove_link (hD.linkPaused_monotone ω.2 i j) t

/-- **The expected cost is a mean over the clocks and the pauses of the
hosts of a mean over the pauses of the links.** Take a solution whose cost
is a measurable function of what is drawn, a random world of the member, and
for every pair of outcomes a world built from the draw of the first outcome
with the links' pauses of the second.
The expected cost of the solution is the mean, over the first outcome, of
its mean cost over the second outcome in those worlds. -/
theorem expectedCost_resampleLinks [DecidableEq H] [Countable H] {Msg : Type}
    {lookahead : ℕ+} {c : Weights} {τ : Solution H R Msg}
    (hτ : m.measurableCost f lookahead c Msg τ) (hD : m.Prior f P D)
    {world : Ω → World H R} (hB : ∀ ω, m.Builds f (D ω) (world ω))
    {world₂ : Ω × Ω → World H R}
    (hB₂ : ∀ ω, m.Builds f (resampleLinks D ω) (world₂ ω)) :
    τ.expectedCost P world lookahead c
      = ∫⁻ ω₁, ∫⁻ ω₂, τ.cost (world₂ (ω₁, ω₂)) lookahead c ∂P ∂P := by
  have := hD.prob
  have hm := hD.aemeasurable
  obtain ⟨F, hF, hFeq⟩ := hτ
  have h1 : τ.expectedCost P world lookahead c = ∫⁻ ω, F (D ω) ∂P :=
    lintegral_congr_ae (hFeq Ω P D world hD hB)
  have h2 := hFeq (Ω × Ω) (P.prod P) (resampleLinks D) world₂ hD.prior_resampleLinks hB₂
  have hm₂ := aemeasurable_resampleLinks (P := P) hm
  have h3 : ∫⁻ ω, F (D ω) ∂P = ∫⁻ ω, F (resampleLinks D ω) ∂(P.prod P) := by
    rw [← lintegral_map' hF.aemeasurable hm, ← hD.map_resampleLinks hm,
      lintegral_map' hF.aemeasurable hm₂]
  have h4 : ∫⁻ ω, F (resampleLinks D ω) ∂(P.prod P)
      = ∫⁻ ω₁, ∫⁻ ω₂, F (resampleLinks D (ω₁, ω₂)) ∂P ∂P :=
    lintegral_prod _ (hF.comp_aemeasurable hm₂)
  rw [h1, h3, h4]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod h2] with ω₁ hω₁
  exact lintegral_congr_ae (hω₁.mono fun ω₂ h => h.symm)

end Unisono.Spec.GenerativeWorld
