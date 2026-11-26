/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ProposedResample
public import Unisono.Spec.Models.RandomIndex
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The value that the jitter of a link takes at its next redraw

In a random world of any member of `Unisono.Spec.ProposedWorld`, take a link
and a true time `a`. The value that the jitter of the link takes at its
first redraw after `a` (`Draw.nextLevel`) has the law of the link's jitter,
and it is independent of the draw with that value replaced by zero
(`Prior.nextLevel`). Nothing that happens before that redraw depends on the
value, so a solution cannot have prepared for it.

* `Draw.withLevels`: a draw with the values of the jitter of one link
  replaced by another sequence.
* `Prior.indepFun_withLevels`: the values of the jitter of a link are
  independent of the rest of the draw.
* `Draw.levelIndex`: the number of the value that the jitter of the link has
  at the true time `a`. `Draw.nextLevel`: the value with the next number.
  `Draw.withNextLevel`: the draw with that value replaced.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open GenerativeWorld (Orientation refOrientation pairOf refOrientation_pairOf)

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- The draw `d` with the values of the jitter of the link from `i₀` to `j₀`
replaced by the sequence `x`. -/
def Draw.withLevels (d : Draw H R) (i₀ j₀ : H) (x : ℤ → ℝ) : Draw H R :=
  { d with jitterLevel := fun i j => if i = i₀ ∧ j = j₀ then x else d.jitterLevel i j }

theorem Draw.withLevels_self (d : Draw H R) (i₀ j₀ : H) (x : ℤ → ℝ) :
    (d.withLevels i₀ j₀ x).jitterLevel i₀ j₀ = x := by
  show (if i₀ = i₀ ∧ j₀ = j₀ then x else d.jitterLevel i₀ j₀) = x
  rw [ite_eq_left ⟨rfl, rfl⟩]

theorem Draw.withLevels_of_ne (d : Draw H R) {i₀ j₀ i j : H} (x : ℤ → ℝ)
    (h : ¬(i = i₀ ∧ j = j₀)) : (d.withLevels i₀ j₀ x).jitterLevel i j = d.jitterLevel i j := by
  show (if i = i₀ ∧ j = j₀ then x else d.jitterLevel i j) = d.jitterLevel i j
  rw [ite_eq_right h]

/-- Replacing the values of the jitter of a link twice is replacing them by
the second sequence. -/
theorem Draw.withLevels_withLevels (d : Draw H R) (i₀ j₀ : H) (x y : ℤ → ℝ) :
    (d.withLevels i₀ j₀ x).withLevels i₀ j₀ y = d.withLevels i₀ j₀ y := by
  have e : (fun i j => if i = i₀ ∧ j = j₀ then y else (d.withLevels i₀ j₀ x).jitterLevel i j)
      = fun i j => if i = i₀ ∧ j = j₀ then y else d.jitterLevel i j := by
    funext i j
    by_cases h : i = i₀ ∧ j = j₀
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, Draw.withLevels_of_ne _ _ h]
  show ({ d.withLevels i₀ j₀ x with
      jitterLevel := fun i j =>
        if i = i₀ ∧ j = j₀ then y else (d.withLevels i₀ j₀ x).jitterLevel i j } : Draw H R)
    = d.withLevels i₀ j₀ y
  rw [e]
  rfl

/-- A draw with the values of the jitter of a link replaced is a measurable
function of the draw and of the new sequence. -/
theorem measurable_withLevels (i₀ j₀ : H) :
    Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.withLevels i₀ j₀ q.2 := by
  have h1 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.split :=
    measurable_draw_split.comp measurable_fst
  have h2 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.offset :=
    measurable_draw_offset.comp measurable_fst
  have h3 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.logRate :=
    measurable_draw_logRate.comp measurable_fst
  have h4 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.wander :=
    measurable_draw_wander.comp measurable_fst
  have h5 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.deviceLogRate :=
    measurable_draw_deviceLogRate.comp measurable_fst
  have h6 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.deviceWander :=
    measurable_draw_deviceWander.comp measurable_fst
  have h7 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.reportError :=
    measurable_draw_reportError.comp measurable_fst
  have h8 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.jitterCount :=
    measurable_draw_jitterCount.comp measurable_fst
  have h10 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.linkPaused :=
    measurable_draw_linkPaused.comp measurable_fst
  have h11 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.outage :=
    measurable_draw_outage.comp measurable_fst
  have h12 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.dropped :=
    measurable_draw_dropped.comp measurable_fst
  have h13 : Measurable fun q : Draw H R × (ℤ → ℝ) => q.1.hostPaused :=
    measurable_draw_hostPaused.comp measurable_fst
  refine measurable_draw h1 h2 h3 h4 h5 h6 h7 h8 ?_ h10 h11 h12 h13
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  by_cases h : i = i₀ ∧ j = j₀
  · have e : (fun q : Draw H R × (ℤ → ℝ) => (q.1.withLevels i₀ j₀ q.2).jitterLevel i j)
        = fun q => q.2 := funext fun q => by
      obtain ⟨rfl, rfl⟩ := h
      exact q.1.withLevels_self i j q.2
    rw [e]
    exact measurable_snd
  · have e : (fun q : Draw H R × (ℤ → ℝ) => (q.1.withLevels i₀ j₀ q.2).jitterLevel i j)
        = fun q => q.1.jitterLevel i j := funext fun q =>
      q.1.withLevels_of_ne q.2 h
    rw [e]
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_draw_jitterLevel)).comp measurable_fst

variable {Ω : Type} [MeasurableSpace Ω] {m : Told H R} {f : Member H R} {P : Measure Ω}
  {D : Ω → Draw H R}

/-- **In a random world, the values of the jitter of a link are independent
of the rest of the draw.** The rest of the draw is the draw with those
values replaced by zero. -/
theorem Prior.indepFun_withLevels (hD : Prior m f P D) (hm : AEMeasurable D P) (i₀ j₀ : H) :
    IndepFun (fun ω => (D ω).withLevels i₀ j₀ 0) (fun ω => (D ω).jitterLevel i₀ j₀) P := by
  have hIJ : Disjoint {p : Part H R | p ≠ Part.jitterLevel i₀ j₀} {Part.jitterLevel i₀ j₀} :=
    Set.disjoint_singleton_right.mpr fun h => h rfl
  have h := iIndepFun.indepFun_set₀ hIJ (hD.independent (refOrientation H))
    (fun p => (measurable_part (refOrientation H) p).comp_aemeasurable hm)
  have hswap : ∀ ω i j, (D ω).split i j + (D ω).split j i = 1 := hD.split_swap
  rw [IndepFun_iff_Indep] at h ⊢
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right h ?_) ?_
  · -- The values of the jitter of the link are the one part that was set aside.
    let _ : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (p : ({Part.jitterLevel i₀ j₀} : Set (Part H R))) =>
        (D ω).part (refOrientation H) p) inferInstance
    have hCI : Measurable fun ω (p : ({Part.jitterLevel i₀ j₀} : Set (Part H R))) =>
        (D ω).part (refOrientation H) p := comap_measurable _
    have hX : Measurable fun ω => (D ω).jitterLevel i₀ j₀ :=
      measurable_pi_iff.mp hCI ⟨Part.jitterLevel i₀ j₀, Set.mem_singleton _⟩
    exact measurable_iff_comap_le.mp hX
  · -- Every part of the rest of the draw is a function of the other parts.
    let _ : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (p : {p : Part H R | p ≠ Part.jitterLevel i₀ j₀}) =>
        (D ω).part (refOrientation H) p) inferInstance
    have hCJ : Measurable fun ω (p : {p : Part H R | p ≠ Part.jitterLevel i₀ j₀}) =>
        (D ω).part (refOrientation H) p := comap_measurable _
    have hcoord : ∀ (p : Part H R) (hp : p ≠ Part.jitterLevel i₀ j₀),
        Measurable fun ω => (D ω).part (refOrientation H) p := fun p hp =>
      measurable_pi_iff.mp hCJ ⟨p, hp⟩
    have hU : Measurable fun ω => (D ω).withLevels i₀ j₀ 0 := by
      refine measurable_draw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
        by_cases hij : i = j
        · have e : (fun ω => ((D ω).withLevels i₀ j₀ 0).split i j) = fun _ => 1 / 2 :=
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
            hcoord (.split (pairOf i j hij)) (by simp)
          rcases refOrientation_pairOf i j hij with hp | hp
          · have e : (fun ω => ((D ω).withLevels i₀ j₀ 0).split i j)
                = fun ω => (D ω).split (refOrientation H (pairOf i j hij)).1.1
                    (refOrientation H (pairOf i j hij)).1.2 := funext fun ω => by
              rw [hp]
              rfl
            rw [e]
            exact hc
          · have e : (fun ω => ((D ω).withLevels i₀ j₀ 0).split i j)
                = fun ω => 1 - (D ω).split (refOrientation H (pairOf i j hij)).1.1
                    (refOrientation H (pairOf i j hij)).1.2 := funext fun ω => by
              rw [hp]
              have hs := hswap ω i j
              show (D ω).split i j = 1 - (D ω).split j i
              linarith
            rw [e]
            exact measurable_const.sub hc
      · exact measurable_pi_iff.mpr fun h => hcoord (.offset h) (by simp)
      · exact measurable_pi_iff.mpr fun h => hcoord (.logRate h) (by simp)
      · exact measurable_pi_iff.mpr fun h => measurable_pi_iff.mpr fun k =>
          hcoord (.wander h k) (by simp)
      · exact measurable_pi_iff.mpr fun x => hcoord (.deviceLogRate x) (by simp)
      · exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun k =>
          hcoord (.deviceWander x k) (by simp)
      · exact measurable_pi_iff.mpr fun x => hcoord (.reportError x) (by simp)
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          hcoord (.jitterCount i j) (by simp)
      · refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
        by_cases hij : i = i₀ ∧ j = j₀
        · have e : (fun ω => ((D ω).withLevels i₀ j₀ 0).jitterLevel i j) = fun _ => 0 :=
            funext fun ω => by
              obtain ⟨rfl, rfl⟩ := hij
              exact (D ω).withLevels_self i j 0
          rw [e]
          exact measurable_const
        · have e : (fun ω => ((D ω).withLevels i₀ j₀ 0).jitterLevel i j)
              = fun ω => (D ω).jitterLevel i j := funext fun ω =>
            (D ω).withLevels_of_ne 0 hij
          rw [e]
          refine hcoord (.jitterLevel i j) fun hp => hij ?_
          have := Part.jitterLevel.inj hp
          exact this
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          hcoord (.linkPaused i j) (by simp)
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          hcoord (.outage i j) (by simp)
      · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
          measurable_pi_iff.mpr fun q => hcoord (.dropped i j q) (by simp)
      · exact measurable_pi_iff.mpr fun h => hcoord (.hostPaused h) (by simp)
    exact measurable_iff_comap_le.mp hU

/-! ## The value at the next redraw -/

/-- The number of the value that the jitter of the link from `i₀` to `j₀`
has at the true time `a`. -/
def Draw.levelIndex (d : Draw H R) (i₀ j₀ : H) (a : Time) : ℤ := ⌊d.jitterCount i₀ j₀ a⌋

/-- **The value that the jitter of the link takes at its first redraw after
the true time `a`.** -/
def Draw.nextLevel (d : Draw H R) (i₀ j₀ : H) (a : Time) : ℝ :=
  d.jitterLevel i₀ j₀ (d.levelIndex i₀ j₀ a + 1)

/-- The draw with the value that the jitter of the link takes at its first
redraw after `a` replaced by `x`. -/
def Draw.withNextLevel (d : Draw H R) (i₀ j₀ : H) (a : Time) (x : ℝ) : Draw H R :=
  d.withLevels i₀ j₀ (Function.update (d.jitterLevel i₀ j₀) (d.levelIndex i₀ j₀ a + 1) x)

/-- **The value at the next redraw has the law of the link's jitter and is
independent of the draw without it.** In a random world with hosts that can
be counted, for a link and a true time `a`: the value that the jitter of the
link takes at its first redraw after `a` has the law of the jitter of the
link, and it is independent of the draw with that value replaced by zero. -/
theorem Prior.nextLevel [Countable H] (hD : Prior m f P D) (i₀ j₀ : H) (a : Time) :
    HasLaw (fun ω => (D ω).nextLevel i₀ j₀ a) (f.jitterLaw i₀ j₀) P
      ∧ IndepFun (fun ω => (D ω).nextLevel i₀ j₀ a)
        (fun ω => (D ω).withNextLevel i₀ j₀ a 0) P := by
  have := hD.prob
  have hm := hD.aemeasurable
  have hrest : AEMeasurable (fun ω => (D ω).withLevels i₀ j₀ 0) P :=
    ((measurable_withLevels i₀ j₀).comp (measurable_id.prodMk measurable_const)).comp_aemeasurable
      hm
  have hindex : Measurable fun d : Draw H R => d.levelIndex i₀ j₀ a :=
    Int.measurable_floor.comp ((measurable_pi_apply a).comp ((measurable_pi_apply j₀).comp
      ((measurable_pi_apply i₀).comp measurable_draw_jitterCount)))
  -- The index is the same in the draw without the values of the link.
  have hsame : ∀ ω, ((D ω).withLevels i₀ j₀ 0).levelIndex i₀ j₀ a = (D ω).levelIndex i₀ j₀ a :=
    fun _ => rfl
  have hind : IndepFun (fun ω => (D ω).jitterLevel i₀ j₀)
      (fun ω => ((D ω).levelIndex i₀ j₀ a, (D ω).withLevels i₀ j₀ 0)) P := by
    have h0 := (hD.indepFun_withLevels hm i₀ j₀).symm
    exact h0.comp (φ := id) (ψ := fun y : Draw H R => (y.levelIndex i₀ j₀ a, y)) measurable_id
      (hindex.prodMk measurable_id)
  obtain ⟨hlaw, hindep⟩ := indepFun_randomIndex (hD.jitterLevel_law i₀ j₀)
    (hindex.comp_aemeasurable hm) hrest hind
  refine ⟨hlaw, ?_⟩
  have hG : Measurable fun q : (ℤ → ℝ) × ℤ × Draw H R => q.2.2.withLevels i₀ j₀ q.1 :=
    (measurable_withLevels i₀ j₀).comp
      ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
  have h2 := hindep.comp (φ := id) measurable_id hG
  have e : (fun ω => (D ω).withNextLevel i₀ j₀ a 0)
      = ((fun q : (ℤ → ℝ) × ℤ × Draw H R => q.2.2.withLevels i₀ j₀ q.1)
        ∘ fun ω => (Function.update ((D ω).jitterLevel i₀ j₀) ((D ω).levelIndex i₀ j₀ a + 1) 0,
          (D ω).levelIndex i₀ j₀ a, (D ω).withLevels i₀ j₀ 0)) := by
    funext ω
    exact ((D ω).withLevels_withLevels i₀ j₀ 0 _).symm
  rw [e]
  exact h2

end Unisono.Spec.ProposedWorld
