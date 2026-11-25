/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeLate
public import Unisono.Spec.Models.GenerativeTransfer
public import Unisono.Spec.Models.IncrementParts
public import Mathlib.Probability.Moments.Covariance

/-!
# A random world is known by the law of its draw

The prior of the generative model says how the draw is distributed, and a
few things about every outcome: the two splits of a pair add up to one, the
wander is continuous, the paused times never decrease. This file shows that
nothing else matters.

* `measurable_draw` and the nine `measurable_draw_*`: a function with values
  in the draws is measurable exactly when the nine parts of the draw are.
* `Prior.aemeasurable`: in a random world, the draw is a random variable.
* `Prior.of_map_eq`: a random draw on another probability space that has the
  same law as the draw of a random world, and the same properties in every
  outcome, is the draw of a random world of the same member.
* `Draw.withLink`: a draw with the paused time of one link replaced.
* `Prior.indepFun_withLink`: in a random world, the paused time of a link is
  independent of the rest of the draw.

The second result is how new random worlds are made from one: by any change
of the draw that keeps its law, such as drawing a part of it again.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Functions of a random variable, under two equal laws -/

section Law

variable {Ω₁ Ω₂ 𝒟 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒟]
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {D₁ : Ω₁ → 𝒟} {D₂ : Ω₂ → 𝒟}

/-- Two random variables with the same law give the same law to every
measurable function of them. -/
theorem map_comp_of_map_eq {β : Type*} [MeasurableSpace β] {g : 𝒟 → β} (hg : Measurable g)
    (hm₁ : AEMeasurable D₁ P₁) (hm₂ : AEMeasurable D₂ P₂) (hlaw : P₂.map D₂ = P₁.map D₁) :
    P₂.map (fun ω => g (D₂ ω)) = P₁.map (fun ω => g (D₁ ω)) := by
  have e₂ : P₂.map (fun ω => g (D₂ ω)) = (P₂.map D₂).map g :=
    (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hm₂).symm
  have e₁ : P₁.map (fun ω => g (D₁ ω)) = (P₁.map D₁).map g :=
    (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hm₁).symm
  rw [e₂, e₁, hlaw]

/-- Whether measurable functions of a random variable are independent
depends only on its law. -/
theorem iIndepFun_comp_of_map_eq {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {G : ∀ i, 𝒟 → β i} (hG : ∀ i, Measurable (G i)) (hm₁ : AEMeasurable D₁ P₁)
    (hm₂ : AEMeasurable D₂ P₂) (hlaw : P₂.map D₂ = P₁.map D₁)
    (h : iIndepFun (fun i ω => G i (D₁ ω)) P₁) : iIndepFun (fun i ω => G i (D₂ ω)) P₂ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have key : ∀ A : Set 𝒟, MeasurableSet A → P₂ (D₂ ⁻¹' A) = P₁ (D₁ ⁻¹' A) := fun A hA => by
    rw [← Measure.map_apply_of_aemeasurable hm₂ hA, hlaw,
      Measure.map_apply_of_aemeasurable hm₁ hA]
  have hInter₂ : (⋂ i ∈ S, (fun ω => G i (D₂ ω)) ⁻¹' sets i)
      = D₂ ⁻¹' (⋂ i ∈ S, G i ⁻¹' sets i) := by
    rw [Set.preimage_iInter₂]
    rfl
  have hInter₁ : (⋂ i ∈ S, (fun ω => G i (D₁ ω)) ⁻¹' sets i)
      = D₁ ⁻¹' (⋂ i ∈ S, G i ⁻¹' sets i) := by
    rw [Set.preimage_iInter₂]
    rfl
  rw [hInter₂, key _ (Finset.measurableSet_biInter S fun i hi => hG i (hsets i hi)), ← hInter₁,
    h S hsets]
  exact Finset.prod_congr rfl fun i hi => (key _ (hG i (hsets i hi))).symm

end Law

variable {H : Type} {R : ℕ}

/-! ## The parts of a draw are measurable functions of it -/

/-- The nine parts of a draw, together, are a measurable function of the
draw. -/
theorem measurable_draw_tuple : Measurable fun d : Draw H R =>
    (d.split, d.offset, d.logRate, d.wander, d.linkPaused, d.hostPaused,
      d.deviceLogRate, d.deviceWander, d.reportError) :=
  comap_measurable _

theorem measurable_draw_split : Measurable fun d : Draw H R => d.split :=
  measurable_draw_tuple.fst

theorem measurable_draw_offset : Measurable fun d : Draw H R => d.offset :=
  measurable_draw_tuple.snd.fst

theorem measurable_draw_logRate : Measurable fun d : Draw H R => d.logRate :=
  measurable_draw_tuple.snd.snd.fst

theorem measurable_draw_wander : Measurable fun d : Draw H R => d.wander :=
  measurable_draw_tuple.snd.snd.snd.fst

theorem measurable_draw_linkPaused : Measurable fun d : Draw H R => d.linkPaused :=
  measurable_draw_tuple.snd.snd.snd.snd.fst

theorem measurable_draw_hostPaused : Measurable fun d : Draw H R => d.hostPaused :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.fst

theorem measurable_draw_deviceLogRate : Measurable fun d : Draw H R => d.deviceLogRate :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.fst

theorem measurable_draw_deviceWander : Measurable fun d : Draw H R => d.deviceWander :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.snd.fst

theorem measurable_draw_reportError : Measurable fun d : Draw H R => d.reportError :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.snd.snd

/-- **A function with values in the draws is measurable when the nine parts
of the draw are.** -/
theorem measurable_draw {α : Type*} [MeasurableSpace α] {g : α → Draw H R}
    (h1 : Measurable fun a => (g a).split) (h2 : Measurable fun a => (g a).offset)
    (h3 : Measurable fun a => (g a).logRate) (h4 : Measurable fun a => (g a).wander)
    (h5 : Measurable fun a => (g a).linkPaused) (h6 : Measurable fun a => (g a).hostPaused)
    (h7 : Measurable fun a => (g a).deviceLogRate)
    (h8 : Measurable fun a => (g a).deviceWander)
    (h9 : Measurable fun a => (g a).reportError) : Measurable g :=
  measurable_comap_iff.mpr (h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk
    (h6.prodMk (h7.prodMk (h8.prodMk h9))))))))

/-- Each component of a draw is a measurable function of the draw. -/
theorem measurable_component (o : Orientation H) (p : Component H R) :
    Measurable fun d : Draw H R => d.component o p := by
  cases p with
  | split z =>
    exact (measurable_pi_apply (o z).1.2).comp
      ((measurable_pi_apply (o z).1.1).comp measurable_draw_split)
  | offset h => exact (measurable_pi_apply h).comp measurable_draw_offset
  | logRate h => exact (measurable_pi_apply h).comp measurable_draw_logRate
  | wander h => exact (measurable_pi_apply h).comp measurable_draw_wander
  | linkPaused i j =>
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_draw_linkPaused)
  | hostPaused h => exact (measurable_pi_apply h).comp measurable_draw_hostPaused
  | deviceLogRate x => exact (measurable_pi_apply x).comp measurable_draw_deviceLogRate
  | deviceWander x => exact (measurable_pi_apply x).comp measurable_draw_deviceWander
  | reportError x => exact (measurable_pi_apply x).comp measurable_draw_reportError

variable {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R} {f : Member H R}
  {P : Measure Ω} {D : Ω → Draw H R}

/-! ## The draw of a random world is a random variable -/

/-- **In a random world, the draw is measurable up to a set of probability
zero.** -/
theorem Prior.aemeasurable [Countable H] (hD : m.Prior f P D) : AEMeasurable D P := by
  have hsplit : AEMeasurable (fun ω => (D ω).split) P := by
    refine aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j => ?_
    by_cases hij : i = j
    · have hc : (fun ω => (D ω).split i j) = fun _ => 1 / 2 := funext fun ω => by
        have h := hD.split_swap ω i j
        rw [← hij] at h ⊢
        linarith
      rw [hc]
      exact aemeasurable_const
    · exact (hD.split_law i j hij).aemeasurable
  have hoffset : AEMeasurable (fun ω => (D ω).offset) P :=
    aemeasurable_pi_iff.mpr fun h => (hD.offset_law h).aemeasurable
  have hlogRate : AEMeasurable (fun ω => (D ω).logRate) P :=
    aemeasurable_pi_iff.mpr fun h => (hD.logRate_law h).aemeasurable
  have hwander : AEMeasurable (fun ω => (D ω).wander) P :=
    aemeasurable_pi_iff.mpr fun h =>
      aemeasurable_path (fun t => (hD.wander_gaussian h).aemeasurable t)
        fun ω t => (hD.wander_continuous ω h).continuousWithinAt
  have hlink : AEMeasurable (fun ω => (D ω).linkPaused) P :=
    aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j =>
      hD.aemeasurable_paused (.inl (i, j))
  have hhost : AEMeasurable (fun ω => (D ω).hostPaused) P :=
    aemeasurable_pi_iff.mpr fun h => hD.aemeasurable_paused (.inr h)
  have hdevlog : AEMeasurable (fun ω => (D ω).deviceLogRate) P :=
    aemeasurable_pi_iff.mpr fun x => (hD.deviceLogRate_law x).aemeasurable
  have hdevwander : AEMeasurable (fun ω => (D ω).deviceWander) P :=
    aemeasurable_pi_iff.mpr fun x =>
      aemeasurable_path (fun t => (hD.deviceWander_gaussian x).aemeasurable t)
        fun ω t => (hD.deviceWander_continuous ω x).continuousWithinAt
  have herr : AEMeasurable (fun ω => (D ω).reportError) P :=
    aemeasurable_pi_iff.mpr fun x =>
      aemeasurable_path (fun t => (hD.reportError_gaussian x).aemeasurable t)
        fun ω t => (hD.reportError_continuous ω x).continuousWithinAt
  have htuple := hsplit.prodMk (hoffset.prodMk (hlogRate.prodMk (hwander.prodMk
    (hlink.prodMk (hhost.prodMk (hdevlog.prodMk (hdevwander.prodMk herr)))))))
  have hmk := htuple.measurable_mk
  refine ⟨fun ω =>
    { split := (htuple.mk _ ω).1
      offset := (htuple.mk _ ω).2.1
      logRate := (htuple.mk _ ω).2.2.1
      wander := (htuple.mk _ ω).2.2.2.1
      linkPaused := (htuple.mk _ ω).2.2.2.2.1
      hostPaused := (htuple.mk _ ω).2.2.2.2.2.1
      deviceLogRate := (htuple.mk _ ω).2.2.2.2.2.2.1
      deviceWander := (htuple.mk _ ω).2.2.2.2.2.2.2.1
      reportError := (htuple.mk _ ω).2.2.2.2.2.2.2.2 }, ?_, ?_⟩
  · exact measurable_draw hmk.fst hmk.snd.fst hmk.snd.snd.fst hmk.snd.snd.snd.fst
      hmk.snd.snd.snd.snd.fst hmk.snd.snd.snd.snd.snd.fst hmk.snd.snd.snd.snd.snd.snd.fst
      hmk.snd.snd.snd.snd.snd.snd.snd.fst hmk.snd.snd.snd.snd.snd.snd.snd.snd
  · filter_upwards [htuple.ae_eq_mk] with ω hω
    rw [← hω]

/-! ## A draw with the law of a random world -/

/-- **A random draw with the law of the draw of a random world is the draw
of a random world.** Let `D` be the draw of a random world of the member
`f`. A random draw `D'` on another probability space that has the same law
as `D`, and in every outcome the properties that the prior asks of every
outcome, is the draw of a random world of the same member. -/
theorem Prior.of_map_eq {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {D' : Ω' → Draw H R} (hD : m.Prior f P D) (hm : AEMeasurable D P)
    (hP' : IsProbabilityMeasure P') (hm' : AEMeasurable D' P') (hlaw : P'.map D' = P.map D)
    (hswap : ∀ ω i j, (D' ω).split i j + (D' ω).split j i = 1)
    (hmem : ∀ ω i j, (D' ω).split i j ∈ Set.Ioo (0 : ℝ) 1)
    (hwander : ∀ ω h, Continuous ((D' ω).wander h))
    (hdevice : ∀ ω x, Continuous ((D' ω).deviceWander x))
    (hreport : ∀ ω x, Continuous ((D' ω).reportError x))
    (hlinkMono : ∀ ω i j, Monotone ((D' ω).linkPaused i j))
    (hlinkZero : ∀ ω i j, (D' ω).linkPaused i j 0 = 0)
    (hlinkRight : ∀ ω i j t, ContinuousWithinAt ((D' ω).linkPaused i j) (Set.Ici t) t)
    (hhostMono : ∀ ω h, Monotone ((D' ω).hostPaused h))
    (hhostZero : ∀ ω h, (D' ω).hostPaused h 0 = 0)
    (hhostRight : ∀ ω h t, ContinuousWithinAt ((D' ω).hostPaused h) (Set.Ici t) t) :
    m.Prior f P' D' := by
  have hsplit : ∀ i j, Measurable fun d : Draw H R => d.split i j := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_draw_split)
  have hoff : ∀ h, Measurable fun d : Draw H R => d.offset h := fun h =>
    (measurable_pi_apply h).comp measurable_draw_offset
  have hlog : ∀ h, Measurable fun d : Draw H R => d.logRate h := fun h =>
    (measurable_pi_apply h).comp measurable_draw_logRate
  have hwan : ∀ h t, Measurable fun d : Draw H R => d.wander h t := fun h t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply h).comp measurable_draw_wander)
  have hlnk : ∀ i j t, Measurable fun d : Draw H R => d.linkPaused i j t := fun i j t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_draw_linkPaused))
  have hhst : ∀ h t, Measurable fun d : Draw H R => d.hostPaused h t := fun h t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply h).comp measurable_draw_hostPaused)
  have hdlog : ∀ x, Measurable fun d : Draw H R => d.deviceLogRate x := fun x =>
    (measurable_pi_apply x).comp measurable_draw_deviceLogRate
  have hdwan : ∀ x t, Measurable fun d : Draw H R => d.deviceWander x t := fun x t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply x).comp measurable_draw_deviceWander)
  have hrep : ∀ x t, Measurable fun d : Draw H R => d.reportError x t := fun x t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply x).comp measurable_draw_reportError)
  -- A law of a function of the draw is the same for `D'` as for `D`.
  have hlawOf : ∀ {g : Draw H R → ℝ} {μ : Measure ℝ}, Measurable g →
      HasLaw (fun ω => g (D ω)) μ P → HasLaw (fun ω => g (D' ω)) μ P' := fun hg h =>
    ⟨hg.comp_aemeasurable hm', (map_comp_of_map_eq hg hm hm' hlaw).trans h.map_eq⟩
  have hmean : ∀ {g : Draw H R → ℝ}, Measurable g →
      ∫ ω, g (D' ω) ∂P' = ∫ ω, g (D ω) ∂P := fun {g} hg => by
    rw [← integral_map hm' hg.aestronglyMeasurable, hlaw,
      integral_map hm hg.aestronglyMeasurable]
  have hcov : ∀ {g₁ g₂ : Draw H R → ℝ}, Measurable g₁ → Measurable g₂ →
      cov[fun ω => g₁ (D' ω), fun ω => g₂ (D' ω); P']
        = cov[fun ω => g₁ (D ω), fun ω => g₂ (D ω); P] := fun {g₁ g₂} h1 h2 => by
    rw [← covariance_map_fun h1.aestronglyMeasurable h2.aestronglyMeasurable hm', hlaw,
      covariance_map_fun h1.aestronglyMeasurable h2.aestronglyMeasurable hm]
  have hgauss : ∀ {X : Time → Draw H R → ℝ}, (∀ t, Measurable (X t)) →
      IsGaussianProcess (fun t ω => X t (D ω)) P →
        IsGaussianProcess (fun t ω => X t (D' ω)) P' := fun {X} hX h => by
    refine ⟨fun I => ?_⟩
    have hg : Measurable fun (d : Draw H R) (t : I) => X t d :=
      measurable_pi_iff.mpr fun t => hX t
    have e := map_comp_of_map_eq hg hm hm' hlaw
    refine ⟨hg.comp_aemeasurable hm', ?_⟩
    have h1 := (h.hasGaussianLaw I).isGaussian_map
    change IsGaussian (P'.map (fun ω => (fun (d : Draw H R) (t : I) => X t d) (D' ω)))
    rw [e]
    exact h1
  have hincr : ∀ {X : Time → Draw H R → ℝ}, (∀ t, Measurable (X t)) →
      HasIndepIncrements (fun t ω => X t (D ω)) P →
        HasIndepIncrements (fun t ω => X t (D' ω)) P' := fun {X} hX h n t ht =>
    iIndepFun_comp_of_map_eq
      (G := fun (k : Fin n) (d : Draw H R) => X (t k.succ) d - X (t k.castSucc) d)
      (fun k => (hX _).sub (hX _)) hm hm' hlaw (h n t ht)
  exact
    { prob := hP'
      split_swap := hswap
      split_mem := hmem
      split_law := fun i j hij => hlawOf (hsplit i j) (hD.split_law i j hij)
      offset_law := fun h => hlawOf (hoff h) (hD.offset_law h)
      logRate_law := fun h => hlawOf (hlog h) (hD.logRate_law h)
      wander_gaussian := fun h =>
        hgauss (X := fun t d => d.wander h t) (fun t => hwan h t) (hD.wander_gaussian h)
      wander_mean := fun h t => (hmean (hwan h t)).trans (hD.wander_mean h t)
      wander_covariance := fun h s t =>
        (hcov (hwan h s) (hwan h t)).trans (hD.wander_covariance h s t)
      wander_continuous := hwander
      deviceLogRate_law := fun x => hlawOf (hdlog x) (hD.deviceLogRate_law x)
      deviceWander_gaussian := fun x =>
        hgauss (X := fun t d => d.deviceWander x t) (fun t => hdwan x t)
          (hD.deviceWander_gaussian x)
      deviceWander_mean := fun x t => (hmean (hdwan x t)).trans (hD.deviceWander_mean x t)
      deviceWander_covariance := fun x s t =>
        (hcov (hdwan x s) (hdwan x t)).trans (hD.deviceWander_covariance x s t)
      deviceWander_continuous := hdevice
      reportError_gaussian := fun x =>
        hgauss (X := fun t d => d.reportError x t) (fun t => hrep x t)
          (hD.reportError_gaussian x)
      reportError_mean := fun x t => (hmean (hrep x t)).trans (hD.reportError_mean x t)
      reportError_covariance := fun x s t =>
        (hcov (hrep x s) (hrep x t)).trans (hD.reportError_covariance x s t)
      reportError_continuous := hreport
      linkPaused_monotone := hlinkMono
      linkPaused_zero := hlinkZero
      linkPaused_rightContinuous := hlinkRight
      linkPaused_increments := fun i j =>
        hincr (X := fun t d => d.linkPaused i j t) (fun t => hlnk i j t)
          (hD.linkPaused_increments i j)
      linkPaused_law := fun i j s t hst =>
        hlawOf ((hlnk i j t).sub (hlnk i j s)) (hD.linkPaused_law i j s t hst)
      hostPaused_monotone := hhostMono
      hostPaused_zero := hhostZero
      hostPaused_rightContinuous := hhostRight
      hostPaused_increments := fun h =>
        hincr (X := fun t d => d.hostPaused h t) (fun t => hhst h t)
          (hD.hostPaused_increments h)
      hostPaused_law := fun h s t hst =>
        hlawOf ((hhst h t).sub (hhst h s)) (hD.hostPaused_law h s t hst)
      independent := fun o =>
        iIndepFun_comp_of_map_eq (fun p => measurable_component o p) hm hm' hlaw
          (hD.independent o) }

/-! ## The paused time of one link, and the rest of the draw -/

variable [DecidableEq H]

/-- The draw `d` with the paused time of the link from `i₀` to `j₀` replaced
by the path `x`. -/
def Draw.withLink (d : Draw H R) (i₀ j₀ : H) (x : Time → ℝ) : Draw H R :=
  { d with linkPaused := fun i j => if i = i₀ ∧ j = j₀ then x else d.linkPaused i j }

theorem Draw.withLink_linkPaused_self (d : Draw H R) (i₀ j₀ : H) (x : Time → ℝ) :
    (d.withLink i₀ j₀ x).linkPaused i₀ j₀ = x := by
  show (if i₀ = i₀ ∧ j₀ = j₀ then x else d.linkPaused i₀ j₀) = x
  rw [ite_eq_left ⟨rfl, rfl⟩]

theorem Draw.withLink_linkPaused_of_ne (d : Draw H R) {i₀ j₀ i j : H} (x : Time → ℝ)
    (h : ¬(i = i₀ ∧ j = j₀)) : (d.withLink i₀ j₀ x).linkPaused i j = d.linkPaused i j := by
  show (if i = i₀ ∧ j = j₀ then x else d.linkPaused i j) = d.linkPaused i j
  rw [ite_eq_right h]

/-- Replacing the paused time of a link by itself changes nothing. -/
theorem Draw.withLink_self (d : Draw H R) (i₀ j₀ : H) :
    d.withLink i₀ j₀ (d.linkPaused i₀ j₀) = d := by
  refine Draw.ext_fields rfl rfl rfl rfl ?_ rfl rfl rfl rfl
  funext i j
  by_cases h : i = i₀ ∧ j = j₀
  · obtain ⟨rfl, rfl⟩ := h
    exact d.withLink_linkPaused_self i j _
  · exact d.withLink_linkPaused_of_ne _ h

/-- Replacing the paused time of a link twice is replacing it by the second
path. -/
theorem Draw.withLink_withLink (d : Draw H R) (i₀ j₀ : H) (x y : Time → ℝ) :
    (d.withLink i₀ j₀ x).withLink i₀ j₀ y = d.withLink i₀ j₀ y := by
  refine Draw.ext_fields rfl rfl rfl rfl ?_ rfl rfl rfl rfl
  funext i j
  by_cases h : i = i₀ ∧ j = j₀
  · obtain ⟨rfl, rfl⟩ := h
    rw [Draw.withLink_linkPaused_self, Draw.withLink_linkPaused_self]
  · rw [Draw.withLink_linkPaused_of_ne _ _ h, Draw.withLink_linkPaused_of_ne _ _ h,
      Draw.withLink_linkPaused_of_ne _ _ h]

/-- A draw with the paused time of a link replaced is a measurable function
of the draw and of the new path. -/
theorem measurable_withLink (i₀ j₀ : H) :
    Measurable fun q : Draw H R × (Time → ℝ) => q.1.withLink i₀ j₀ q.2 := by
  have h1 : Measurable fun q : Draw H R × (Time → ℝ) => q.1.split :=
    measurable_draw_split.comp measurable_fst
  have h2 : Measurable fun q : Draw H R × (Time → ℝ) => q.1.offset :=
    measurable_draw_offset.comp measurable_fst
  have h3 : Measurable fun q : Draw H R × (Time → ℝ) => q.1.logRate :=
    measurable_draw_logRate.comp measurable_fst
  have h4 : Measurable fun q : Draw H R × (Time → ℝ) => q.1.wander :=
    measurable_draw_wander.comp measurable_fst
  have h6 : Measurable fun q : Draw H R × (Time → ℝ) => q.1.hostPaused :=
    measurable_draw_hostPaused.comp measurable_fst
  have h7 : Measurable fun q : Draw H R × (Time → ℝ) => q.1.deviceLogRate :=
    measurable_draw_deviceLogRate.comp measurable_fst
  have h8 : Measurable fun q : Draw H R × (Time → ℝ) => q.1.deviceWander :=
    measurable_draw_deviceWander.comp measurable_fst
  have h9 : Measurable fun q : Draw H R × (Time → ℝ) => q.1.reportError :=
    measurable_draw_reportError.comp measurable_fst
  refine measurable_draw h1 h2 h3 h4 ?_ h6 h7 h8 h9
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  by_cases h : i = i₀ ∧ j = j₀
  · have e : (fun q : Draw H R × (Time → ℝ) => (q.1.withLink i₀ j₀ q.2).linkPaused i j)
        = fun q => q.2 := funext fun q => by
      obtain ⟨rfl, rfl⟩ := h
      exact q.1.withLink_linkPaused_self i j q.2
    rw [e]
    exact measurable_snd
  · have e : (fun q : Draw H R × (Time → ℝ) => (q.1.withLink i₀ j₀ q.2).linkPaused i j)
        = fun q => q.1.linkPaused i j := funext fun q =>
      q.1.withLink_linkPaused_of_ne q.2 h
    rw [e]
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_draw_linkPaused)).comp measurable_fst

/-- **In a random world, the paused time of a link is independent of the
rest of the draw.** The rest of the draw is the draw with the paused time of
that link replaced by zero. -/
theorem Prior.indepFun_withLink (hD : m.Prior f P D) (hm : AEMeasurable D P) (i₀ j₀ : H) :
    IndepFun (fun ω => (D ω).withLink i₀ j₀ 0) (fun ω => (D ω).linkPaused i₀ j₀) P := by
  have hIJ : Disjoint {p : Component H R | p ≠ Component.linkPaused i₀ j₀}
      {Component.linkPaused i₀ j₀} := Set.disjoint_singleton_right.mpr fun h => h rfl
  have h := iIndepFun.indepFun_set₀ hIJ (hD.independent (refOrientation H))
    (fun p => (measurable_component (refOrientation H) p).comp_aemeasurable hm)
  have hswap : ∀ ω i j, (D ω).split i j + (D ω).split j i = 1 := hD.split_swap
  rw [IndepFun_iff_Indep] at h ⊢
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right h ?_) ?_
  · -- The paused time of the link is the one component that was set aside.
    let _ : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (p : ({Component.linkPaused i₀ j₀} : Set (Component H R))) =>
        (D ω).component (refOrientation H) p) inferInstance
    have hCI : Measurable fun ω (p : ({Component.linkPaused i₀ j₀} : Set (Component H R))) =>
        (D ω).component (refOrientation H) p := comap_measurable _
    have hX : Measurable fun ω => (D ω).linkPaused i₀ j₀ :=
      measurable_pi_iff.mp hCI ⟨Component.linkPaused i₀ j₀, Set.mem_singleton _⟩
    exact measurable_iff_comap_le.mp hX
  · -- Every part of the rest of the draw is a function of the other components.
    let _ : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω (p : {p : Component H R | p ≠ Component.linkPaused i₀ j₀}) =>
        (D ω).component (refOrientation H) p) inferInstance
    have hCJ : Measurable fun ω (p : {p : Component H R | p ≠ Component.linkPaused i₀ j₀}) =>
        (D ω).component (refOrientation H) p := comap_measurable _
    have hcoord : ∀ (p : Component H R) (hp : p ≠ Component.linkPaused i₀ j₀),
        Measurable fun ω => (D ω).component (refOrientation H) p := fun p hp =>
      measurable_pi_iff.mp hCJ ⟨p, hp⟩
    have hU : Measurable fun ω => (D ω).withLink i₀ j₀ 0 := by
      refine measurable_draw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
        by_cases hij : i = j
        · have e : (fun ω => ((D ω).withLink i₀ j₀ 0).split i j) = fun _ => 1 / 2 :=
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
          · have e : (fun ω => ((D ω).withLink i₀ j₀ 0).split i j)
                = fun ω => (D ω).split (refOrientation H (pairOf i j hij)).1.1
                    (refOrientation H (pairOf i j hij)).1.2 := funext fun ω => by
              rw [hp]
              rfl
            rw [e]
            exact hc
          · have e : (fun ω => ((D ω).withLink i₀ j₀ 0).split i j)
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
      · exact measurable_pi_iff.mpr fun h => hcoord (.wander h) (by simp)
      · refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
        by_cases hij : i = i₀ ∧ j = j₀
        · have e : (fun ω => ((D ω).withLink i₀ j₀ 0).linkPaused i j) = fun _ => 0 :=
            funext fun ω => by
              obtain ⟨rfl, rfl⟩ := hij
              exact (D ω).withLink_linkPaused_self i j 0
          rw [e]
          exact measurable_const
        · have e : (fun ω => ((D ω).withLink i₀ j₀ 0).linkPaused i j)
              = fun ω => (D ω).linkPaused i j := funext fun ω =>
            (D ω).withLink_linkPaused_of_ne 0 hij
          rw [e]
          exact hcoord (.linkPaused i j) fun he => hij (by
            injection he with h1 h2
            exact ⟨h1, h2⟩)
      · exact measurable_pi_iff.mpr fun h => hcoord (.hostPaused h) (by simp)
      · exact measurable_pi_iff.mpr fun x => hcoord (.deviceLogRate x) (by simp)
      · exact measurable_pi_iff.mpr fun x => hcoord (.deviceWander x) (by simp)
      · exact measurable_pi_iff.mpr fun x => hcoord (.reportError x) (by simp)
    exact measurable_iff_comap_le.mp hU

end Unisono.Spec.GenerativeWorld
