/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeLate
public import Unisono.Spec.Models.GenerativePauses
public import Unisono.Spec.Models.GenerativeTransfer

/-!
# All random worlds of a member with steady clocks have one law of the draw

A member with steady clocks has many random worlds: any probability space
with a draw that has the law of the member. This file proves that the draw
has the same law in all of them, in the form that a comparison of solutions
uses: the mean of a measurable function of the draw is the same in every
random world of the member.

* `Draw.ofParts`: a draw rebuilt from its numbers (the splits, the offsets
  and the mean rates of the clocks) and its paused times, with no wander and
  no error of a report. A draw whose clocks do not wander and whose reports
  are exact is rebuilt from its own parts (`Draw.ofParts_eq`).
* `Prior.map_scalars_eq`: the numbers of the draw have the same joint law in
  two random worlds of one member. They are independent, and each has the
  law that the member gives it.
* `Prior.map_parts_eq`: so do the numbers together with the paused times,
  which are independent of the numbers
  (`Prior.indepFun_scalars_paused`) and have one law in every random world
  (`Prior.map_paused_eq_pathLaw`).
* `Prior.lintegral_draw_eq`: the mean of a measurable function of the draw is
  the same in two random worlds of a member with steady clocks.
* `expectedCost_eq_of_steady`: so a solution whose cost is a
  measurable function of what is drawn has the same expected cost in every
  random world of such a member.

A lower bound on expected cost can therefore be proved in one random world of
the member, for example the one whose pauses are drawn cell by cell
(`steadyWorld`), and holds in all of them.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- A draw rebuilt from its numbers `u` and its paused times `x`, with no
wander of any clock and no error of any report. Each pair of hosts is taken
in its fixed order. -/
def Draw.ofParts (u : ScalarIndex H R → ℝ) (x : PauseIndex H → Time → ℝ) : Draw H R where
  split := fun i j =>
    if h : i = j then 1 / 2
    else if (refOrientation H (pairOf i j h)).1 = (i, j) then u (.inl (pairOf i j h))
    else 1 - u (.inl (pairOf i j h))
  offset := fun h => u (.inr (.inl h))
  logRate := fun h => u (.inr (.inr (.inl h)))
  wander := fun _ _ => 0
  linkPaused := fun i j => x (.inl (i, j))
  hostPaused := fun h => x (.inr h)
  deviceLogRate := fun y => u (.inr (.inr (.inr y)))
  deviceWander := fun _ _ => 0
  reportError := fun _ _ => 0

/-- **A draw without wander and without errors of reports is rebuilt from
its parts.** -/
theorem Draw.ofParts_eq (d : Draw H R) (hswap : ∀ i j, d.split i j + d.split j i = 1)
    (hwander : ∀ h t, d.wander h t = 0) (hdevwander : ∀ x t, d.deviceWander x t = 0)
    (herr : ∀ x t, d.reportError x t = 0) :
    Draw.ofParts (d.scalars (refOrientation H)) d.paused = d := by
  refine Draw.ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · funext i j
    by_cases h : i = j
    · subst h
      have h1 : (Draw.ofParts (d.scalars (refOrientation H)) d.paused).split i i = 1 / 2 := by
        simp [Draw.ofParts]
      rw [h1]
      linarith [hswap i i]
    · have hval : d.scalars (refOrientation H) (.inl (pairOf i j h))
          = d.split (refOrientation H (pairOf i j h)).1.1 (refOrientation H (pairOf i j h)).1.2 :=
        rfl
      simp only [Draw.ofParts, dite_eq_right h]
      rcases refOrientation_pairOf i j h with hp | hp
      · rw [ite_eq_left hp, hval, hp]
      · have hne : (refOrientation H (pairOf i j h)).1 ≠ (i, j) := by
          rw [hp]
          intro he
          exact h (Prod.ext_iff.mp he).2
        rw [ite_eq_right hne, hval, hp]
        change 1 - d.split j i = d.split i j
        linarith [hswap i j]
  · rfl
  · rfl
  · funext h t
    exact (hwander h t).symm
  · rfl
  · rfl
  · rfl
  · funext x t
    exact (hdevwander x t).symm
  · funext x t
    exact (herr x t).symm

/-- A draw rebuilt from its parts is a measurable function of the parts. -/
theorem measurable_ofParts :
    Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      Draw.ofParts q.1 q.2 := by
  refine measurable_comap_iff.mpr ?_
  have h1 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).split := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    by_cases h : i = j
    · have hc : (fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
          (Draw.ofParts q.1 q.2).split i j) = fun _ => 1 / 2 := by
        funext q
        simp [Draw.ofParts, h]
      rw [hc]
      exact measurable_const
    · have hu : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
          q.1 (.inl (pairOf i j h)) := (measurable_pi_apply _).comp measurable_fst
      by_cases hp : (refOrientation H (pairOf i j h)).1 = (i, j)
      · have hc : (fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
            (Draw.ofParts q.1 q.2).split i j) = fun q => q.1 (.inl (pairOf i j h)) := by
          funext q
          simp [Draw.ofParts, h, hp]
        rw [hc]
        exact hu
      · have hc : (fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
            (Draw.ofParts q.1 q.2).split i j) = fun q => 1 - q.1 (.inl (pairOf i j h)) := by
          funext q
          simp [Draw.ofParts, h, hp]
        rw [hc]
        exact measurable_const.sub hu
  have h2 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).offset :=
    Measurable.of_eval fun h =>
      (measurable_pi_apply (Sum.inr (Sum.inl h) : ScalarIndex H R)).comp measurable_fst
  have h3 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).logRate :=
    Measurable.of_eval fun h =>
      (measurable_pi_apply (Sum.inr (Sum.inr (Sum.inl h)) : ScalarIndex H R)).comp measurable_fst
  have h4 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).wander := measurable_const
  have h5 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).linkPaused :=
    Measurable.of_eval fun i => Measurable.of_eval fun j =>
      (measurable_pi_apply (Sum.inl (i, j) : PauseIndex H)).comp measurable_snd
  have h6 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).hostPaused :=
    Measurable.of_eval fun h =>
      (measurable_pi_apply (Sum.inr h : PauseIndex H)).comp measurable_snd
  have h7 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).deviceLogRate :=
    Measurable.of_eval fun y =>
      (measurable_pi_apply (Sum.inr (Sum.inr (Sum.inr y)) : ScalarIndex H R)).comp measurable_fst
  have h8 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).deviceWander := measurable_const
  have h9 : Measurable fun q : (ScalarIndex H R → ℝ) × (PauseIndex H → Time → ℝ) =>
      (Draw.ofParts q.1 q.2).reportError := measurable_const
  exact h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk (h6.prodMk (h7.prodMk
    (h8.prodMk h9)))))))

section Laws

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {m : GenerativeWorld H R}
  {f : Member H R} {P : Measure Ω} {P' : Measure Ω'} {D : Ω → Draw H R} {D' : Ω' → Draw H R}

omit [DecidableEq H] in
/-- **The numbers of the draw have one joint law.** In two random worlds of
one member, the splits, the offsets and the mean rates of the clocks, taken
together, have the same law. -/
theorem Prior.map_scalars_eq [Fintype H] (hD : m.Prior f P D) (hD' : m.Prior f P' D')
    (o : Orientation H) :
    P.map (fun ω => (D ω).scalars o) = P'.map (fun ω => (D' ω).scalars o) := by
  classical
  have hprob := hD.prob
  have hprob' := hD'.prob
  have hjoint : ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {D₀ : Ω₀ → Draw H R},
      m.Prior f P₀ D₀ →
      P₀.map (fun ω => (D₀ ω).scalars o)
        = Measure.pi fun s : ScalarIndex H R => P₀.map fun ω => (D₀ ω).scalars o s := by
    intro Ω₀ _ P₀ D₀ h₀
    have := h₀.prob
    have hind : iIndepFun (fun (s : ScalarIndex H R) ω => (D₀ ω).scalars o s) P₀ := by
      have h1 := ((h₀.independent o).precomp scalarComponent_injective).comp scalarCast
        measurable_scalarCast
      have e : (fun (s : ScalarIndex H R) ω => (D₀ ω).scalars o s)
          = fun s => scalarCast s ∘ fun ω => (D₀ ω).component o (scalarComponent s) := by
        funext s ω
        rcases s with z | h | h | x <;> rfl
      rw [e]
      exact h1
    have hae : ∀ s : ScalarIndex H R, AEMeasurable (fun ω => (D₀ ω).scalars o s) P₀ := by
      intro s
      have h2 := (measurable_scalarCast s).comp_aemeasurable (h₀.aemeasurable_scalar o s)
      have e : (fun ω => (D₀ ω).scalars o s)
          = scalarCast s ∘ fun ω => (D₀ ω).component o (scalarComponent s) := by
        funext ω
        rcases s with z | h | h | x <;> rfl
      rw [e]
      exact h2
    exact (iIndepFun_iff_map_fun_eq_pi_map hae).mp hind
  rw [hjoint hD, hjoint hD']
  congr 1
  funext s
  rcases s with z | h | h | x
  · have hz : s((o z).1.1, (o z).1.2) = z.1 := (o z).2
    have hne : (o z).1.1 ≠ (o z).1.2 := by
      intro h
      apply z.2
      rw [← hz]
      exact Sym2.mk_isDiag_iff.mpr h
    exact (hD.split_law _ _ hne).map_eq.trans (hD'.split_law _ _ hne).map_eq.symm
  · exact (hD.offset_law h).map_eq.trans (hD'.offset_law h).map_eq.symm
  · exact (hD.logRate_law h).map_eq.trans (hD'.logRate_law h).map_eq.symm
  · exact (hD.deviceLogRate_law x).map_eq.trans (hD'.deviceLogRate_law x).map_eq.symm

omit [DecidableEq H] in
/-- **The numbers and the paused times of the draw have one joint law.** In
two random worlds of one member, the numbers of the draw together with its
paused times have the same law. -/
theorem Prior.map_parts_eq [Fintype H] (hD : m.Prior f P D) (hD' : m.Prior f P' D')
    (o : Orientation H) :
    P.map (fun ω => ((D ω).scalars o, (D ω).paused))
      = P'.map (fun ω => ((D' ω).scalars o, (D' ω).paused)) := by
  have hprob := hD.prob
  have hprob' := hD'.prob
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hD.aemeasurable_scalars o)
      (aemeasurable_pi_iff.mpr fun x => hD.aemeasurable_paused x)).mp
      (hD.indepFun_scalars_paused o),
    (indepFun_iff_map_prod_eq_prod_map_map (hD'.aemeasurable_scalars o)
      (aemeasurable_pi_iff.mpr fun x => hD'.aemeasurable_paused x)).mp
      (hD'.indepFun_scalars_paused o),
    hD.map_scalars_eq hD' o, hD.map_paused_eq_pathLaw, hD'.map_paused_eq_pathLaw]

/-- **The draw has one law in every random world of a member with steady
clocks.** The mean of a measurable function of the draw is the same in two
random worlds of such a member. -/
theorem Prior.lintegral_draw_eq [Fintype H] (hD : m.Prior f P D) (hD' : m.Prior f P' D')
    (hf : f.SteadyClocks) {F : Draw H R → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (D ω) ∂P = ∫⁻ ω, F (D' ω) ∂P' := by
  have hrebuilt : ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {D₀ : Ω₀ → Draw H R},
      m.Prior f P₀ D₀ →
      ∫⁻ ω, F (D₀ ω) ∂P₀
        = ∫⁻ q, F (Draw.ofParts q.1 q.2)
            ∂P₀.map (fun ω => ((D₀ ω).scalars (refOrientation H), (D₀ ω).paused)) := by
    intro Ω₀ _ P₀ D₀ h₀
    have := h₀.prob
    have h1 : ∀ᵐ ω ∂P₀, ∀ h t, (D₀ ω).wander h t = 0 :=
      ae_all_iff.mpr fun h => h₀.wander_ae_eq_zero (hf.no_wander h)
    have h2 : ∀ᵐ ω ∂P₀, ∀ x t, (D₀ ω).deviceWander x t = 0 :=
      ae_all_iff.mpr fun x => h₀.deviceWander_ae_eq_zero (hf.no_deviceWander x)
    have h3 : ∀ᵐ ω ∂P₀, ∀ x t, (D₀ ω).reportError x t = 0 :=
      ae_all_iff.mpr fun x => h₀.reportError_ae_eq_zero (hf.no_reportError x)
    have hae : ∀ᵐ ω ∂P₀, F (D₀ ω)
        = F (Draw.ofParts ((D₀ ω).scalars (refOrientation H)) (D₀ ω).paused) := by
      filter_upwards [h1, h2, h3] with ω hw hdw herr
      rw [Draw.ofParts_eq (D₀ ω) (h₀.split_swap ω) hw hdw herr]
    rw [lintegral_congr_ae hae]
    exact (lintegral_map' (hF.comp measurable_ofParts).aemeasurable
      ((h₀.aemeasurable_scalars (refOrientation H)).prodMk
        (aemeasurable_pi_iff.mpr fun x => h₀.aemeasurable_paused x))).symm
  rw [hrebuilt hD, hrebuilt hD', hD.map_parts_eq hD' (refOrientation H)]

end Laws

/-- **A solution has one expected cost in all random worlds of a member with
steady clocks.** Let the cost of a solution, in a member with steady clocks,
be a measurable function of what is drawn (`measurableCost`). Then its
expected cost is the same in every random world of the member. -/
theorem expectedCost_eq_of_steady [Fintype H] {Msg : Type} {m : GenerativeWorld H R}
    {f : Member H R} (hf : f.SteadyClocks) {lookahead : ℕ+} {c : Weights}
    {τ : Solution H R Msg} (hτ : m.measurableCost f lookahead c Msg τ)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {D : Ω → Draw H R} {D' : Ω' → Draw H R} {world : Ω → World H R}
    {world' : Ω' → World H R} (hD : m.Prior f P D) (hB : ∀ ω, m.Builds f (D ω) (world ω))
    (hD' : m.Prior f P' D') (hB' : ∀ ω, m.Builds f (D' ω) (world' ω)) :
    τ.expectedCost P world lookahead c = τ.expectedCost P' world' lookahead c := by
  obtain ⟨F, hF, hFeq⟩ := hτ
  have h1 : τ.expectedCost P world lookahead c = ∫⁻ ω, F (D ω) ∂P :=
    lintegral_congr_ae (hFeq Ω P D world hD hB)
  have h2 : τ.expectedCost P' world' lookahead c = ∫⁻ ω, F (D' ω) ∂P' :=
    lintegral_congr_ae (hFeq Ω' P' D' world' hD' hB')
  rw [h1, h2]
  exact hD.lintegral_draw_eq hD' hf hF

end Unisono.Spec.GenerativeWorld
