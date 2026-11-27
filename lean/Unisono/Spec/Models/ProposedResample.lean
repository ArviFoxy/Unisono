/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ProposedDrawLaw

/-!
# Drawing again what the links do, in the proposed model

In a random world of any member of `Unisono.Spec.ProposedWorld`, what the
links do is independent of the rest of the draw. What the links do is their
jitter (its count and its levels), their pauses, their outages and their
single losses. The rest is the splits, the clocks of the hosts and of the
audio devices, the errors of the reports, and the pauses of the hosts. So
what the links do can be drawn again from a second, independent outcome.

* `Draw.withLinks`: a draw with what the links do in another draw.
* `Draw.Shaped.withLinks`: it has the properties that the prior asks of
  every outcome when both draws have them.
* `Prior.indepFun_withLinks`: what the links do is independent of the rest
  of the draw.
* `resampleLinks`: on two copies of the probability space, the draw of the
  first outcome with what the links do in the second outcome.
* `Prior.map_resampleLinks`, `Prior.prior_resampleLinks`: this draw has the
  law of the draw, and it is the draw of a random world of the same member.

For a fixed first outcome, the clocks, the pauses of the hosts and the audio
devices are fixed, and only what the links do is random. This is the setting
in which a disturbance of a link can be compared with the room that a
solution kept for it. No bound on a cost is proved here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open GenerativeWorld (Orientation refOrientation pairOf refOrientation_pairOf)

variable {H : Type} {R : ℕ}

/-- The draw `d` with what the links do in the draw `e`: their jitter, their
pauses, their outages and their single losses. -/
def Draw.withLinks (d e : Draw H R) : Draw H R :=
  { d with
    jitterCount := e.jitterCount
    jitterLevel := e.jitterLevel
    linkPaused := e.linkPaused
    outage := e.outage
    dropped := e.dropped }

/-- Whether a part of a draw is something that a link does. -/
def Part.isLink : Part H R → Bool
  | .jitterCount _ _ => true
  | .jitterLevel _ _ => true
  | .linkPaused _ _ => true
  | .outage _ _ => true
  | .dropped _ _ _ => true
  | _ => false

/-- A draw with what the links do in another draw is a measurable function
of the two draws. -/
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
  have h5 : Measurable fun q : Draw H R × Draw H R => q.1.deviceLogRate :=
    measurable_draw_deviceLogRate.comp measurable_fst
  have h6 : Measurable fun q : Draw H R × Draw H R => q.1.deviceWander :=
    measurable_draw_deviceWander.comp measurable_fst
  have h7 : Measurable fun q : Draw H R × Draw H R => q.1.reportError :=
    measurable_draw_reportError.comp measurable_fst
  have h8 : Measurable fun q : Draw H R × Draw H R => q.2.jitterCount :=
    measurable_draw_jitterCount.comp measurable_snd
  have h9 : Measurable fun q : Draw H R × Draw H R => q.2.jitterLevel :=
    measurable_draw_jitterLevel.comp measurable_snd
  have h10 : Measurable fun q : Draw H R × Draw H R => q.2.linkPaused :=
    measurable_draw_linkPaused.comp measurable_snd
  have h11 : Measurable fun q : Draw H R × Draw H R => q.2.outage :=
    measurable_draw_outage.comp measurable_snd
  have h12 : Measurable fun q : Draw H R × Draw H R => q.2.dropped :=
    measurable_draw_dropped.comp measurable_snd
  have h13 : Measurable fun q : Draw H R × Draw H R => q.1.hostPaused :=
    measurable_draw_hostPaused.comp measurable_fst
  exact measurable_draw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

/-- A draw with what the links do in another draw has the properties that
the prior asks of every outcome, when both draws have them. -/
theorem Draw.Shaped.withLinks {d e : Draw H R} (hd : d.Shaped) (he : e.Shaped) :
    (d.withLinks e).Shaped where
  split_swap := hd.split_swap
  split_mem := hd.split_mem
  wander_continuous := hd.wander_continuous
  deviceWander_continuous := hd.deviceWander_continuous
  reportError_continuous := hd.reportError_continuous
  jitterLevel_nonneg := he.jitterLevel_nonneg
  jitterCount_zero := he.jitterCount_zero
  jitterCount_monotone := he.jitterCount_monotone
  jitterCount_right := he.jitterCount_right
  linkPaused_zero := he.linkPaused_zero
  linkPaused_monotone := he.linkPaused_monotone
  linkPaused_right := he.linkPaused_right
  outage_zero := he.outage_zero
  outage_monotone := he.outage_monotone
  outage_right := he.outage_right
  hostPaused_zero := hd.hostPaused_zero
  hostPaused_monotone := hd.hostPaused_monotone
  hostPaused_right := hd.hostPaused_right

variable {Ω : Type} [MeasurableSpace Ω] {m : Told H R} {f : Member H R} {P : Measure Ω}
  {D : Ω → Draw H R}

/-- **In a random world, what the links do is independent of the rest of the
draw.** For any fixed draw `d₀`: the draw with what the links do in `d₀` is
independent of the draw `d₀` with what the links do in the draw. -/
theorem Prior.indepFun_withLinks [DecidableEq H] (hD : Prior m f P D)
    (hm : AEMeasurable D P) (d₀ : Draw H R) :
    IndepFun (fun ω => (D ω).withLinks d₀) (fun ω => d₀.withLinks (D ω)) P := by
  have hIJ : Disjoint {p : Part H R | p.isLink = false} {p : Part H R | p.isLink = true} :=
    Set.disjoint_left.mpr fun p (h1 : p.isLink = false) (h2 : p.isLink = true) => by
      rw [h1] at h2
      exact Bool.false_ne_true h2
  have h := iIndepFun.indepFun_set₀ hIJ (hD.independent (refOrientation H))
    (fun p => (measurable_part (refOrientation H) p).comp_aemeasurable hm)
  have hswap : ∀ ω i j, (D ω).split i j + (D ω).split j i = 1 := hD.split_swap
  rw [IndepFun_iff_Indep] at h ⊢
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · -- Every part of the rest of the draw is a function of the other parts.
    let _ : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (p : {p : Part H R | p.isLink = false}) =>
        (D ω).part (refOrientation H) p) inferInstance
    have hCI : Measurable fun ω (p : {p : Part H R | p.isLink = false}) =>
        (D ω).part (refOrientation H) p := comap_measurable _
    have hcoord : ∀ (p : Part H R) (hp : p.isLink = false),
        Measurable fun ω => (D ω).part (refOrientation H) p := fun p hp =>
      measurable_pi_iff.mp hCI ⟨p, hp⟩
    have hU : Measurable fun ω => (D ω).withLinks d₀ := by
      refine measurable_draw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
      · exact measurable_pi_iff.mpr fun h => measurable_pi_iff.mpr fun k =>
          hcoord (.wander h k) rfl
      · exact measurable_pi_iff.mpr fun x => hcoord (.deviceLogRate x) rfl
      · exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun k =>
          hcoord (.deviceWander x k) rfl
      · exact measurable_pi_iff.mpr fun x => hcoord (.reportError x) rfl
      · show Measurable fun _ : Ω => d₀.jitterCount
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.jitterLevel
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.linkPaused
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.outage
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.dropped
        exact measurable_const
      · exact measurable_pi_iff.mpr fun h => hcoord (.hostPaused h) rfl
    exact measurable_iff_comap_le.mp hU
  · -- What the links do is the parts that were set aside.
    let _ : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (p : {p : Part H R | p.isLink = true}) =>
        (D ω).part (refOrientation H) p) inferInstance
    have hCJ : Measurable fun ω (p : {p : Part H R | p.isLink = true}) =>
        (D ω).part (refOrientation H) p := comap_measurable _
    have hcoord : ∀ (p : Part H R) (hp : p.isLink = true),
        Measurable fun ω => (D ω).part (refOrientation H) p := fun p hp =>
      measurable_pi_iff.mp hCJ ⟨p, hp⟩
    have hV : Measurable fun ω => d₀.withLinks (D ω) := by
      refine measurable_draw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · show Measurable fun _ : Ω => d₀.split
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.offset
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.logRate
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.wander
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.deviceLogRate
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.deviceWander
        exact measurable_const
      · show Measurable fun _ : Ω => d₀.reportError
        exact measurable_const
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          hcoord (.jitterCount i j) rfl
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          hcoord (.jitterLevel i j) rfl
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          hcoord (.linkPaused i j) rfl
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          hcoord (.outage i j) rfl
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          measurable_pi_iff.mpr fun q => hcoord (.dropped i j q) rfl
      · show Measurable fun _ : Ω => d₀.hostPaused
        exact measurable_const
    exact measurable_iff_comap_le.mp hV

/-! ## What the links do in a second outcome -/

/-- The random draw `D` with what the links do drawn again: on two copies of
the probability space, the draw of the first outcome with what the links do
in the second outcome. -/
def resampleLinks (D : Ω → Draw H R) (ω : Ω × Ω) : Draw H R :=
  (D ω.1).withLinks (D ω.2)

/-- The draw with what the links do drawn again is measurable up to a set of
probability zero. -/
theorem aemeasurable_resampleLinks [SFinite P] (hm : AEMeasurable D P) :
    AEMeasurable (resampleLinks D) (P.prod P) :=
  measurable_withLinks.comp_aemeasurable (hm.prodMap hm)

/-- **The draw with what the links do drawn again has the law of the
draw.** -/
theorem Prior.map_resampleLinks [DecidableEq H] (hD : Prior m f P D)
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

/-- **The draw with what the links do drawn again is the draw of a random
world of the same member.** -/
theorem Prior.prior_resampleLinks [DecidableEq H] [Countable H] (hD : Prior m f P D) :
    Prior m f (P.prod P) (resampleLinks D) := by
  have := hD.prob
  have hm := hD.aemeasurable
  exact hD.of_map_eq hm inferInstance (aemeasurable_resampleLinks hm)
    (hD.map_resampleLinks hm) fun ω => (hD.shaped ω.1).withLinks (hD.shaped ω.2)

end Unisono.Spec.ProposedWorld
