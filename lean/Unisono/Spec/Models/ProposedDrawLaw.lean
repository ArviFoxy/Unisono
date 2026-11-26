/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ProposedWorld
public import Unisono.Spec.Models.GenerativeDrawLaw

/-!
# A random world of the proposed model is known by the law of its draw

The prior of `Unisono.Spec.ProposedWorld` says how the draw is distributed,
and a few things about the draw of every outcome (`Draw.Shaped`): the two
splits of a pair add up to one, the wander is continuous, the jitter is not
negative, the paths of episodes start at zero, never decrease and are
continuous from the right. This file shows that nothing else matters.

* `measurable_draw` and the thirteen `measurable_draw_*`: a function with
  values in the draws is measurable exactly when the thirteen parts of the
  draw are. `measurable_part`: each part of a draw is a measurable function
  of the draw.
* `Prior.shaped`: the draw of every outcome of a random world has the
  properties `Draw.Shaped`.
* `Prior.aemeasurable`: in a random world with hosts that can be counted,
  the draw is a random variable.
* `Prior.of_map_eq`: a random draw on another probability space that has the
  same law as the draw of a random world, and the properties `Draw.Shaped`
  in every outcome, is the draw of a random world of the same member.

The last result is how new random worlds are made from one: by any change of
the draw that keeps its law, such as drawing a part of it again.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open GenerativeWorld (Orientation)

variable {H : Type} {R : ℕ}

/-! ## The parts of a draw are measurable functions of it -/

/-- The thirteen parts of a draw, together, are a measurable function of the
draw. -/
theorem measurable_draw_tuple : Measurable fun d : Draw H R =>
    (d.split, d.offset, d.logRate, d.wander, d.deviceLogRate, d.deviceWander, d.reportError,
      d.jitterCount, d.jitterLevel, d.linkPaused, d.outage, d.dropped, d.hostPaused) :=
  comap_measurable _

theorem measurable_draw_split : Measurable fun d : Draw H R => d.split :=
  measurable_draw_tuple.fst

theorem measurable_draw_offset : Measurable fun d : Draw H R => d.offset :=
  measurable_draw_tuple.snd.fst

theorem measurable_draw_logRate : Measurable fun d : Draw H R => d.logRate :=
  measurable_draw_tuple.snd.snd.fst

theorem measurable_draw_wander : Measurable fun d : Draw H R => d.wander :=
  measurable_draw_tuple.snd.snd.snd.fst

theorem measurable_draw_deviceLogRate : Measurable fun d : Draw H R => d.deviceLogRate :=
  measurable_draw_tuple.snd.snd.snd.snd.fst

theorem measurable_draw_deviceWander : Measurable fun d : Draw H R => d.deviceWander :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.fst

theorem measurable_draw_reportError : Measurable fun d : Draw H R => d.reportError :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.fst

theorem measurable_draw_jitterCount : Measurable fun d : Draw H R => d.jitterCount :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.snd.fst

theorem measurable_draw_jitterLevel : Measurable fun d : Draw H R => d.jitterLevel :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.snd.snd.fst

theorem measurable_draw_linkPaused : Measurable fun d : Draw H R => d.linkPaused :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

theorem measurable_draw_outage : Measurable fun d : Draw H R => d.outage :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

theorem measurable_draw_dropped : Measurable fun d : Draw H R => d.dropped :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst

theorem measurable_draw_hostPaused : Measurable fun d : Draw H R => d.hostPaused :=
  measurable_draw_tuple.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd

/-- **A function with values in the draws is measurable when the thirteen
parts of the draw are.** -/
theorem measurable_draw {α : Type*} [MeasurableSpace α] {g : α → Draw H R}
    (h1 : Measurable fun a => (g a).split) (h2 : Measurable fun a => (g a).offset)
    (h3 : Measurable fun a => (g a).logRate) (h4 : Measurable fun a => (g a).wander)
    (h5 : Measurable fun a => (g a).deviceLogRate)
    (h6 : Measurable fun a => (g a).deviceWander)
    (h7 : Measurable fun a => (g a).reportError)
    (h8 : Measurable fun a => (g a).jitterCount)
    (h9 : Measurable fun a => (g a).jitterLevel)
    (h10 : Measurable fun a => (g a).linkPaused) (h11 : Measurable fun a => (g a).outage)
    (h12 : Measurable fun a => (g a).dropped) (h13 : Measurable fun a => (g a).hostPaused) :
    Measurable g :=
  measurable_comap_iff.mpr (h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk
    (h6.prodMk (h7.prodMk (h8.prodMk (h9.prodMk (h10.prodMk (h11.prodMk
      (h12.prodMk h13))))))))))))

/-- Each part of a draw is a measurable function of the draw. -/
theorem measurable_part (o : Orientation H) (p : Part H R) :
    Measurable fun d : Draw H R => d.part o p := by
  cases p with
  | split z =>
    exact (measurable_pi_apply (o z).1.2).comp
      ((measurable_pi_apply (o z).1.1).comp measurable_draw_split)
  | offset h => exact (measurable_pi_apply h).comp measurable_draw_offset
  | logRate h => exact (measurable_pi_apply h).comp measurable_draw_logRate
  | wander h k =>
    exact (measurable_pi_apply k).comp ((measurable_pi_apply h).comp measurable_draw_wander)
  | deviceLogRate x => exact (measurable_pi_apply x).comp measurable_draw_deviceLogRate
  | deviceWander x k =>
    exact (measurable_pi_apply k).comp
      ((measurable_pi_apply x).comp measurable_draw_deviceWander)
  | reportError x => exact (measurable_pi_apply x).comp measurable_draw_reportError
  | jitterCount i j =>
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_draw_jitterCount)
  | jitterLevel i j =>
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_draw_jitterLevel)
  | linkPaused i j =>
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_draw_linkPaused)
  | outage i j =>
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_draw_outage)
  | dropped i j q =>
    exact (measurable_pi_apply q).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_draw_dropped))
  | hostPaused h => exact (measurable_pi_apply h).comp measurable_draw_hostPaused

/-! ## What the prior asks of the draw of every outcome -/

/-- **The properties that the prior asks of the draw of every outcome.** -/
structure Draw.Shaped (d : Draw H R) : Prop where
  split_swap : ∀ i j, d.split i j + d.split j i = 1
  split_mem : ∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1
  wander_continuous : ∀ h k, Continuous (d.wander h k)
  deviceWander_continuous : ∀ x k, Continuous (d.deviceWander x k)
  reportError_continuous : ∀ x, Continuous (d.reportError x)
  jitterLevel_nonneg : ∀ i j n, 0 ≤ d.jitterLevel i j n
  jitterCount_zero : ∀ i j, d.jitterCount i j 0 = 0
  jitterCount_monotone : ∀ i j, Monotone (d.jitterCount i j)
  jitterCount_right : ∀ i j t, ContinuousWithinAt (d.jitterCount i j) (Set.Ici t) t
  linkPaused_zero : ∀ i j, d.linkPaused i j 0 = 0
  linkPaused_monotone : ∀ i j, Monotone (d.linkPaused i j)
  linkPaused_right : ∀ i j t, ContinuousWithinAt (d.linkPaused i j) (Set.Ici t) t
  outage_zero : ∀ i j, d.outage i j 0 = 0
  outage_monotone : ∀ i j, Monotone (d.outage i j)
  outage_right : ∀ i j t, ContinuousWithinAt (d.outage i j) (Set.Ici t) t
  hostPaused_zero : ∀ h, d.hostPaused h 0 = 0
  hostPaused_monotone : ∀ h, Monotone (d.hostPaused h)
  hostPaused_right : ∀ h t, ContinuousWithinAt (d.hostPaused h) (Set.Ici t) t

variable {Ω : Type} [MeasurableSpace Ω] {m : Told H R} {f : Member H R} {P : Measure Ω}
  {D : Ω → Draw H R}

/-- The draw of every outcome of a random world has the properties that the
prior asks of every outcome. -/
theorem Prior.shaped (hD : Prior m f P D) (ω : Ω) : (D ω).Shaped where
  split_swap := hD.split_swap ω
  split_mem := hD.split_mem ω
  wander_continuous := hD.wander_continuous ω
  deviceWander_continuous := hD.deviceWander_continuous ω
  reportError_continuous := hD.reportError_continuous ω
  jitterLevel_nonneg := hD.jitterLevel_nonneg ω
  jitterCount_zero := fun i j => (hD.jitterCount_law i j).zero ω
  jitterCount_monotone := fun i j => (hD.jitterCount_law i j).monotone ω
  jitterCount_right := fun i j t => (hD.jitterCount_law i j).rightContinuous ω t
  linkPaused_zero := fun i j => (hD.linkPaused_law i j).zero ω
  linkPaused_monotone := fun i j => (hD.linkPaused_law i j).monotone ω
  linkPaused_right := fun i j t => (hD.linkPaused_law i j).rightContinuous ω t
  outage_zero := fun i j => (hD.outage_law i j).zero ω
  outage_monotone := fun i j => (hD.outage_law i j).monotone ω
  outage_right := fun i j t => (hD.outage_law i j).rightContinuous ω t
  hostPaused_zero := fun h => (hD.hostPaused_law h).zero ω
  hostPaused_monotone := fun h => (hD.hostPaused_law h).monotone ω
  hostPaused_right := fun h t => (hD.hostPaused_law h).rightContinuous ω t

/-! ## The draw of a random world is a random variable -/

/-- The value of a path of episodes at each time is measurable up to a set of
probability zero. -/
theorem IsEpisodePath.aemeasurable_apply {rate : ℝ} {F : Measure ℝ} {X : Time → Ω → ℝ}
    (hX : IsEpisodePath rate F X P) (t : Time) : AEMeasurable (X t) P := by
  rcases le_total 0 t with ht | ht
  · have h := (hX.law 0 t ht).aemeasurable
    have e : (fun ω => X t ω - X 0 ω) = X t := by
      funext ω
      rw [hX.zero ω, sub_zero]
    rwa [e] at h
  · have h : AEMeasurable (fun ω => -(X 0 ω - X t ω)) P := (hX.law t 0 ht).aemeasurable.neg
    have e : (fun ω => -(X 0 ω - X t ω)) = X t := by
      funext ω
      rw [hX.zero ω, zero_sub, neg_neg]
    rwa [e] at h

/-- The path of episodes is a random variable. -/
theorem IsEpisodePath.aemeasurable_path {rate : ℝ} {F : Measure ℝ} {X : Time → Ω → ℝ}
    (hX : IsEpisodePath rate F X P) : AEMeasurable (fun ω t => X t ω) P :=
  Unisono.Spec.aemeasurable_path hX.aemeasurable_apply hX.rightContinuous

/-- **In a random world, the draw is measurable up to a set of probability
zero.** -/
theorem Prior.aemeasurable [Countable H] (hD : Prior m f P D) : AEMeasurable D P := by
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
    aemeasurable_pi_iff.mpr fun h => HasLaw.aemeasurable (hD.offset_law h)
  have hlogRate : AEMeasurable (fun ω => (D ω).logRate) P :=
    aemeasurable_pi_iff.mpr fun h => (hD.logRate_law h).aemeasurable
  have hwander : AEMeasurable (fun ω => (D ω).wander) P :=
    aemeasurable_pi_iff.mpr fun h => aemeasurable_pi_iff.mpr fun k =>
      Unisono.Spec.aemeasurable_path (fun t => (hD.wander_gaussian h k).aemeasurable t)
        fun ω t => (hD.wander_continuous ω h k).continuousWithinAt
  have hdevlog : AEMeasurable (fun ω => (D ω).deviceLogRate) P :=
    aemeasurable_pi_iff.mpr fun x => (hD.deviceLogRate_law x).aemeasurable
  have hdevwander : AEMeasurable (fun ω => (D ω).deviceWander) P :=
    aemeasurable_pi_iff.mpr fun x => aemeasurable_pi_iff.mpr fun k =>
      Unisono.Spec.aemeasurable_path (fun t => (hD.deviceWander_gaussian x k).aemeasurable t)
        fun ω t => (hD.deviceWander_continuous ω x k).continuousWithinAt
  have herr : AEMeasurable (fun ω => (D ω).reportError) P :=
    aemeasurable_pi_iff.mpr fun x =>
      Unisono.Spec.aemeasurable_path (fun t => (hD.reportError_gaussian x).aemeasurable t)
        fun ω t => (hD.reportError_continuous ω x).continuousWithinAt
  have hcount : AEMeasurable (fun ω => (D ω).jitterCount) P :=
    aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j =>
      (hD.jitterCount_law i j).aemeasurable_path
  have hlevel : AEMeasurable (fun ω => (D ω).jitterLevel) P :=
    aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j =>
      (hD.jitterLevel_law i j).aemeasurable
  have hlink : AEMeasurable (fun ω => (D ω).linkPaused) P :=
    aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j =>
      (hD.linkPaused_law i j).aemeasurable_path
  have hout : AEMeasurable (fun ω => (D ω).outage) P :=
    aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j =>
      (hD.outage_law i j).aemeasurable_path
  have hdrop : AEMeasurable (fun ω => (D ω).dropped) P :=
    aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j =>
      aemeasurable_pi_iff.mpr fun q => (hD.dropped_law i j q).aemeasurable
  have hhost : AEMeasurable (fun ω => (D ω).hostPaused) P :=
    aemeasurable_pi_iff.mpr fun h => (hD.hostPaused_law h).aemeasurable_path
  have htuple := hsplit.prodMk (hoffset.prodMk (hlogRate.prodMk (hwander.prodMk
    (hdevlog.prodMk (hdevwander.prodMk (herr.prodMk (hcount.prodMk (hlevel.prodMk
      (hlink.prodMk (hout.prodMk (hdrop.prodMk hhost)))))))))))
  have hmk := htuple.measurable_mk
  refine ⟨fun ω =>
    { split := (htuple.mk _ ω).1
      offset := (htuple.mk _ ω).2.1
      logRate := (htuple.mk _ ω).2.2.1
      wander := (htuple.mk _ ω).2.2.2.1
      deviceLogRate := (htuple.mk _ ω).2.2.2.2.1
      deviceWander := (htuple.mk _ ω).2.2.2.2.2.1
      reportError := (htuple.mk _ ω).2.2.2.2.2.2.1
      jitterCount := (htuple.mk _ ω).2.2.2.2.2.2.2.1
      jitterLevel := (htuple.mk _ ω).2.2.2.2.2.2.2.2.1
      linkPaused := (htuple.mk _ ω).2.2.2.2.2.2.2.2.2.1
      outage := (htuple.mk _ ω).2.2.2.2.2.2.2.2.2.2.1
      dropped := (htuple.mk _ ω).2.2.2.2.2.2.2.2.2.2.2.1
      hostPaused := (htuple.mk _ ω).2.2.2.2.2.2.2.2.2.2.2.2 }, ?_, ?_⟩
  · exact measurable_draw hmk.fst hmk.snd.fst hmk.snd.snd.fst hmk.snd.snd.snd.fst
      hmk.snd.snd.snd.snd.fst hmk.snd.snd.snd.snd.snd.fst hmk.snd.snd.snd.snd.snd.snd.fst
      hmk.snd.snd.snd.snd.snd.snd.snd.fst hmk.snd.snd.snd.snd.snd.snd.snd.snd.fst
      hmk.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst
      hmk.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst
      hmk.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.fst
      hmk.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd.snd
  · filter_upwards [htuple.ae_eq_mk] with ω hω
    rw [← hω]

/-! ## A draw with the law of a random world -/

/-- **A random draw with the law of the draw of a random world is the draw
of a random world.** Let `D` be the draw of a random world of the member
`f`. A random draw `D'` on another probability space that has the same law
as `D`, and in every outcome the properties that the prior asks of every
outcome, is the draw of a random world of the same member. -/
theorem Prior.of_map_eq {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {D' : Ω' → Draw H R} (hD : Prior m f P D) (hm : AEMeasurable D P)
    (hP' : IsProbabilityMeasure P') (hm' : AEMeasurable D' P') (hlaw : P'.map D' = P.map D)
    (hshape : ∀ ω, (D' ω).Shaped) : Prior m f P' D' := by
  have hsplit : ∀ i j, Measurable fun d : Draw H R => d.split i j := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_draw_split)
  have hoff : ∀ h, Measurable fun d : Draw H R => d.offset h := fun h =>
    (measurable_pi_apply h).comp measurable_draw_offset
  have hlog : ∀ h, Measurable fun d : Draw H R => d.logRate h := fun h =>
    (measurable_pi_apply h).comp measurable_draw_logRate
  have hwan : ∀ h k t, Measurable fun d : Draw H R => d.wander h k t := fun h k t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply k).comp
      ((measurable_pi_apply h).comp measurable_draw_wander))
  have hdlog : ∀ x, Measurable fun d : Draw H R => d.deviceLogRate x := fun x =>
    (measurable_pi_apply x).comp measurable_draw_deviceLogRate
  have hdwan : ∀ x k t, Measurable fun d : Draw H R => d.deviceWander x k t := fun x k t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply k).comp
      ((measurable_pi_apply x).comp measurable_draw_deviceWander))
  have hrep : ∀ x t, Measurable fun d : Draw H R => d.reportError x t := fun x t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply x).comp measurable_draw_reportError)
  have hcnt : ∀ i j t, Measurable fun d : Draw H R => d.jitterCount i j t := fun i j t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_draw_jitterCount))
  have hlev : ∀ i j, Measurable fun d : Draw H R => d.jitterLevel i j := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_draw_jitterLevel)
  have hlnk : ∀ i j t, Measurable fun d : Draw H R => d.linkPaused i j t := fun i j t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_draw_linkPaused))
  have hout : ∀ i j t, Measurable fun d : Draw H R => d.outage i j t := fun i j t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_draw_outage))
  have hdrp : ∀ i j q, Measurable fun d : Draw H R => d.dropped i j q := fun i j q =>
    (measurable_pi_apply q).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_draw_dropped))
  have hhst : ∀ h t, Measurable fun d : Draw H R => d.hostPaused h t := fun h t =>
    (measurable_pi_apply t).comp ((measurable_pi_apply h).comp measurable_draw_hostPaused)
  -- A law of a function of the draw is the same for `D'` as for `D`.
  have hlawOf : ∀ {β : Type} [MeasurableSpace β] {g : Draw H R → β} {μ : Measure β},
      Measurable g → HasLaw (fun ω => g (D ω)) μ P → HasLaw (fun ω => g (D' ω)) μ P' :=
    fun hg h => ⟨hg.comp_aemeasurable hm',
      (GenerativeWorld.map_comp_of_map_eq hg hm hm' hlaw).trans h.map_eq⟩
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
    have e := GenerativeWorld.map_comp_of_map_eq hg hm hm' hlaw
    refine ⟨hg.comp_aemeasurable hm', ?_⟩
    have h1 := (h.hasGaussianLaw I).isGaussian_map
    change IsGaussian (P'.map (fun ω => (fun (d : Draw H R) (t : I) => X t d) (D' ω)))
    rw [e]
    exact h1
  have hepisode : ∀ {rate : ℝ} {F : Measure ℝ} {X : Time → Draw H R → ℝ},
      (∀ t, Measurable (X t)) → (∀ ω, X 0 (D' ω) = 0) →
      (∀ ω, Monotone fun t => X t (D' ω)) →
      (∀ ω t, ContinuousWithinAt (fun s => X s (D' ω)) (Set.Ici t) t) →
      IsEpisodePath rate F (fun t ω => X t (D ω)) P →
        IsEpisodePath rate F (fun t ω => X t (D' ω)) P' :=
    fun {rate F X} hX h0 hmono hright h =>
      { zero := h0
        monotone := hmono
        rightContinuous := hright
        increments := fun n t ht =>
          GenerativeWorld.iIndepFun_comp_of_map_eq
            (G := fun (k : Fin n) (d : Draw H R) => X (t k.succ) d - X (t k.castSucc) d)
            (fun k => (hX _).sub (hX _)) hm hm' hlaw (h.increments n t ht)
        law := fun s t hst => hlawOf ((hX t).sub (hX s)) (h.law s t hst) }
  exact
    { prob := hP'
      split_swap := fun ω => (hshape ω).split_swap
      split_mem := fun ω => (hshape ω).split_mem
      split_law := fun i j hij => hlawOf (hsplit i j) (hD.split_law i j hij)
      offset_law := fun h => hlawOf (hoff h) (hD.offset_law h)
      logRate_law := fun h => hlawOf (hlog h) (hD.logRate_law h)
      wander_gaussian := fun h k =>
        hgauss (X := fun t d => d.wander h k t) (fun t => hwan h k t) (hD.wander_gaussian h k)
      wander_mean := fun h k t => (hmean (hwan h k t)).trans (hD.wander_mean h k t)
      wander_covariance := fun h k s t =>
        (hcov (hwan h k s) (hwan h k t)).trans (hD.wander_covariance h k s t)
      wander_continuous := fun ω => (hshape ω).wander_continuous
      deviceLogRate_law := fun x => hlawOf (hdlog x) (hD.deviceLogRate_law x)
      deviceWander_gaussian := fun x k =>
        hgauss (X := fun t d => d.deviceWander x k t) (fun t => hdwan x k t)
          (hD.deviceWander_gaussian x k)
      deviceWander_mean := fun x k t =>
        (hmean (hdwan x k t)).trans (hD.deviceWander_mean x k t)
      deviceWander_covariance := fun x k s t =>
        (hcov (hdwan x k s) (hdwan x k t)).trans (hD.deviceWander_covariance x k s t)
      deviceWander_continuous := fun ω => (hshape ω).deviceWander_continuous
      reportError_gaussian := fun x =>
        hgauss (X := fun t d => d.reportError x t) (fun t => hrep x t)
          (hD.reportError_gaussian x)
      reportError_mean := fun x t => (hmean (hrep x t)).trans (hD.reportError_mean x t)
      reportError_covariance := fun x s t =>
        (hcov (hrep x s) (hrep x t)).trans (hD.reportError_covariance x s t)
      reportError_continuous := fun ω => (hshape ω).reportError_continuous
      jitterCount_law := fun i j =>
        hepisode (X := fun t d => d.jitterCount i j t) (fun t => hcnt i j t)
          (fun ω => (hshape ω).jitterCount_zero i j)
          (fun ω => (hshape ω).jitterCount_monotone i j)
          (fun ω t => (hshape ω).jitterCount_right i j t) (hD.jitterCount_law i j)
      jitterLevel_law := fun i j => hlawOf (hlev i j) (hD.jitterLevel_law i j)
      jitterLevel_nonneg := fun ω => (hshape ω).jitterLevel_nonneg
      linkPaused_law := fun i j =>
        hepisode (X := fun t d => d.linkPaused i j t) (fun t => hlnk i j t)
          (fun ω => (hshape ω).linkPaused_zero i j)
          (fun ω => (hshape ω).linkPaused_monotone i j)
          (fun ω t => (hshape ω).linkPaused_right i j t) (hD.linkPaused_law i j)
      outage_law := fun i j =>
        hepisode (X := fun t d => d.outage i j t) (fun t => hout i j t)
          (fun ω => (hshape ω).outage_zero i j)
          (fun ω => (hshape ω).outage_monotone i j)
          (fun ω t => (hshape ω).outage_right i j t) (hD.outage_law i j)
      dropped_law := fun i j q => hlawOf (hdrp i j q) (hD.dropped_law i j q)
      hostPaused_law := fun h =>
        hepisode (X := fun t d => d.hostPaused h t) (fun t => hhst h t)
          (fun ω => (hshape ω).hostPaused_zero h)
          (fun ω => (hshape ω).hostPaused_monotone h)
          (fun ω t => (hshape ω).hostPaused_right h t) (hD.hostPaused_law h)
      independent := fun o =>
        GenerativeWorld.iIndepFun_comp_of_map_eq (fun p => measurable_part o p) hm hm' hlaw
          (hD.independent o) }

end Unisono.Spec.ProposedWorld
