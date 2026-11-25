/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeDrawLaw
public import Unisono.Spec.Models.GenerativeLinkPause

/-!
# Drawing again what a link pauses within a period

Take a random world of any member of the generative model, a link, and a
period from true time `a` to `b` that begins at or after true time zero.
The paused time of the link is the sum of two paths: its increments within
the period and its increments outside it (`pathWithin`, `pathOutside`).

* `Draw.linkOutside`: the draw without the paused time of the link that
  begins within the period.
* `Prior.indepFun_linkOutside`: what the link pauses within the
  period is independent of the draw without it. This holds in every random
  world of every member: the clocks may wander and the reports may have
  errors.
* `resample`: on two independent copies of the probability space, the draw
  of the first outcome with what the link pauses within the period taken
  from the second outcome.
* `Prior.map_resample`, `Prior.prior_resample`: this draw has the law of the draw,
  and it is the draw of a random world of the same member.
* `Prior.exists_resample`, `Builds.exists_linkOutside`: these
  draws build worlds, which have the hosts, clocks and audio devices of the
  world of the first outcome and other deliveries.

The second random world is a tool for statements about a solution in the
world without the pauses of a period: such a statement holds for almost
every outcome because it holds, in the second random world, on the outcomes
whose second copy has no pause in the period, and these have positive
probability. No bound on a cost is proved here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H]

/-! ## The draw without what a link pauses within a period -/

/-- The draw `d` without the paused time of the link from `i₀` to `j₀` that
begins within the period from `a` to `b`: the paused time of that link is
replaced by the path of its increments outside the period. -/
def Draw.linkOutside (d : Draw H R) (i₀ j₀ : H) (a b : ℝ) : Draw H R :=
  d.withLink i₀ j₀ (pathOutside a b (d.linkPaused i₀ j₀))

/-- The draw `d` with the path `x` added to the paused time of the link from
`i₀` to `j₀`. -/
def Draw.addLink (d : Draw H R) (i₀ j₀ : H) (x : Time → ℝ) : Draw H R :=
  d.withLink i₀ j₀ (d.linkPaused i₀ j₀ + x)

theorem Draw.linkOutside_self (d : Draw H R) (i₀ j₀ : H) (a b : ℝ) :
    (d.linkOutside i₀ j₀ a b).linkPaused i₀ j₀ = pathOutside a b (d.linkPaused i₀ j₀) :=
  d.withLink_linkPaused_self i₀ j₀ _

theorem Draw.linkOutside_of_ne (d : Draw H R) {i₀ j₀ i j : H} (a b : ℝ)
    (h : ¬(i = i₀ ∧ j = j₀)) : (d.linkOutside i₀ j₀ a b).linkPaused i j = d.linkPaused i j :=
  d.withLink_linkPaused_of_ne _ h

/-- **The draw is the draw without the pauses of the period, with them added
back.** -/
theorem Draw.linkOutside_addLink (d : Draw H R) (i₀ j₀ : H) (a b : ℝ) :
    (d.linkOutside i₀ j₀ a b).addLink i₀ j₀ (pathWithin a b (d.linkPaused i₀ j₀)) = d := by
  have e : pathOutside a b (d.linkPaused i₀ j₀) + pathWithin a b (d.linkPaused i₀ j₀)
      = d.linkPaused i₀ j₀ := funext fun t => pathOutside_add_pathWithin a b _ t
  unfold Draw.addLink Draw.linkOutside
  rw [Draw.withLink_withLink, Draw.withLink_linkPaused_self, e, Draw.withLink_self]

theorem Draw.addLink_zero (d : Draw H R) (i₀ j₀ : H) : d.addLink i₀ j₀ 0 = d := by
  unfold Draw.addLink
  rw [add_zero, Draw.withLink_self]

/-- The draw without the pauses of a period differs from the draw only in
the paused time of the one link, and only from the beginning of the period
on. -/
theorem Draw.sameExcept_linkOutside (d : Draw H R) (i₀ j₀ : H) {a b : ℝ}
    (hab : a ≤ b) : (d.linkOutside i₀ j₀ a b).SameExceptLinkFrom d i₀ j₀ a where
  split := rfl
  offset := rfl
  logRate := rfl
  wander := rfl
  deviceLogRate := rfl
  deviceWander := rfl
  reportError := rfl
  hostPaused := rfl
  linkPaused := fun i j hne =>
    (d.linkOutside_of_ne a b fun h => hne (Prod.ext h.1 h.2)).symm
  before := fun t ht => by
    rw [Draw.linkOutside_self, pathOutside_of_le hab _ ht.le]

theorem measurable_linkOutside (i₀ j₀ : H) (a b : ℝ) :
    Measurable fun d : Draw H R => d.linkOutside i₀ j₀ a b := by
  have hpath : Measurable fun d : Draw H R => d.linkPaused i₀ j₀ :=
    (measurable_pi_apply j₀).comp ((measurable_pi_apply i₀).comp measurable_draw_linkPaused)
  have hpair : Measurable fun d : Draw H R => (d, pathOutside a b (d.linkPaused i₀ j₀)) :=
    measurable_id.prodMk ((measurable_pathOutside a b).comp hpath)
  exact (measurable_withLink i₀ j₀).comp hpair

theorem measurable_addLink (i₀ j₀ : H) :
    Measurable fun q : Draw H R × (Time → ℝ) => q.1.addLink i₀ j₀ q.2 := by
  have hpath : Measurable fun d : Draw H R => d.linkPaused i₀ j₀ :=
    (measurable_pi_apply j₀).comp ((measurable_pi_apply i₀).comp measurable_draw_linkPaused)
  have hsum : Measurable fun q : Draw H R × (Time → ℝ) => q.1.linkPaused i₀ j₀ + q.2 :=
    measurable_pi_iff.mpr fun t =>
      (((measurable_pi_apply t).comp hpath).comp measurable_fst).add
        ((measurable_pi_apply t).comp measurable_snd)
  have hpair : Measurable fun q : Draw H R × (Time → ℝ) =>
      (q.1, q.1.linkPaused i₀ j₀ + q.2) := measurable_fst.prodMk hsum
  exact (measurable_withLink i₀ j₀).comp hpair

variable {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R} {f : Member H R}
  {P : Measure Ω} {D : Ω → Draw H R}

/-- **What a link pauses within a period is independent of the draw without
it.** In a random world of any member, for a link and a period from `a` to
`b` that begins at or after true time zero: the path of the paused time of
the link that begins within the period is independent of the draw without
that paused time, which holds every other part of the draw and the paused
time of the same link that begins outside the period. -/
theorem Prior.indepFun_linkOutside (hD : m.Prior f P D) (hm : AEMeasurable D P)
    (i₀ j₀ : H) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IndepFun (fun ω => pathWithin a b ((D ω).linkPaused i₀ j₀))
      (fun ω => (D ω).linkOutside i₀ j₀ a b) P := by
  have := hD.prob
  have hpath : Measurable fun d : Draw H R => d.linkPaused i₀ j₀ :=
    (measurable_pi_apply j₀).comp ((measurable_pi_apply i₀).comp measurable_draw_linkPaused)
  have hU0 : Measurable fun d : Draw H R => d.withLink i₀ j₀ 0 :=
    (measurable_withLink i₀ j₀).comp (measurable_id.prodMk measurable_const)
  have hU : AEMeasurable (fun ω => (D ω).withLink i₀ j₀ 0) P := hU0.comp_aemeasurable hm
  have hV : AEMeasurable (fun ω => (D ω).linkPaused i₀ j₀) P := hpath.comp_aemeasurable hm
  have hXt : ∀ t, AEMeasurable (fun ω => (D ω).linkPaused i₀ j₀ t) P := fun t =>
    ((measurable_pi_apply t).comp hpath).comp_aemeasurable hm
  have hparts := indepFun_pathWithin_pathOutside (X := fun t ω => (D ω).linkPaused i₀ j₀ t)
    (hD.linkPaused_increments i₀ j₀) hXt (fun ω => hD.linkPaused_zero ω i₀ j₀) ha hab
  have h := indepFun_comp_prodMk hU hV (measurable_pathWithin a b) (measurable_pathOutside a b)
    (hD.indepFun_withLink hm i₀ j₀) hparts
  have h2 := h.comp measurable_id (measurable_withLink i₀ j₀)
  have e : ((fun q : Draw H R × (Time → ℝ) => q.1.withLink i₀ j₀ q.2) ∘ fun ω =>
        ((D ω).withLink i₀ j₀ 0, pathOutside a b ((D ω).linkPaused i₀ j₀)))
      = fun ω => (D ω).linkOutside i₀ j₀ a b :=
    funext fun ω => (D ω).withLink_withLink i₀ j₀ 0 _
  rw [e] at h2
  exact h2

/-! ## The pauses of the period, drawn again -/

/-- The random draw `D` with what the link from `i₀` to `j₀` pauses within
the period from `a` to `b` drawn again: on two copies of the probability
space, the draw of the first outcome without the paused time of the link
that begins within the period, plus the paused time of the link that begins
within the period in the second outcome. -/
def resample (D : Ω → Draw H R) (i₀ j₀ : H) (a b : ℝ) (ω : Ω × Ω) : Draw H R :=
  ((D ω.1).linkOutside i₀ j₀ a b).addLink i₀ j₀ (pathWithin a b ((D ω.2).linkPaused i₀ j₀))

omit [MeasurableSpace Ω] in
/-- With the same outcome twice, the draw is unchanged. -/
theorem resample_self (D : Ω → Draw H R) (i₀ j₀ : H) (a b : ℝ) (ω : Ω) :
    resample D i₀ j₀ a b (ω, ω) = D ω :=
  (D ω).linkOutside_addLink i₀ j₀ a b

omit [MeasurableSpace Ω] in
/-- When the link does not pause within the period in the second outcome,
the draw is the draw of the first outcome without the pauses of the
period. -/
theorem resample_of_eq (D : Ω → Draw H R) (i₀ j₀ : H) {a b : ℝ} (hab : a ≤ b) {ω : Ω × Ω}
    (hmono : Monotone ((D ω.2).linkPaused i₀ j₀))
    (h : (D ω.2).linkPaused i₀ j₀ b = (D ω.2).linkPaused i₀ j₀ a) :
    resample D i₀ j₀ a b ω = (D ω.1).linkOutside i₀ j₀ a b := by
  have e : pathWithin a b ((D ω.2).linkPaused i₀ j₀) = 0 :=
    funext fun t => pathWithin_eq_zero hab hmono h t
  unfold resample
  rw [e, Draw.addLink_zero]

omit [MeasurableSpace Ω] in
theorem resample_linkPaused_self (D : Ω → Draw H R) (i₀ j₀ : H) (a b : ℝ) (ω : Ω × Ω) :
    (resample D i₀ j₀ a b ω).linkPaused i₀ j₀
      = pathOutside a b ((D ω.1).linkPaused i₀ j₀)
        + pathWithin a b ((D ω.2).linkPaused i₀ j₀) := by
  unfold resample Draw.addLink
  rw [Draw.withLink_linkPaused_self, Draw.linkOutside_self]

omit [MeasurableSpace Ω] in
theorem resample_linkPaused_of_ne (D : Ω → Draw H R) {i₀ j₀ i j : H} (a b : ℝ) (ω : Ω × Ω)
    (h : ¬(i = i₀ ∧ j = j₀)) :
    (resample D i₀ j₀ a b ω).linkPaused i j = (D ω.1).linkPaused i j := by
  unfold resample Draw.addLink
  rw [Draw.withLink_linkPaused_of_ne _ _ h, Draw.linkOutside_of_ne _ _ _ h]

/-- The two parts from which the draw is put together again, on two copies
of the probability space, are measurable up to a set of probability zero. -/
theorem aemeasurable_resample [SFinite P] (hm : AEMeasurable D P) (i₀ j₀ : H) (a b : ℝ) :
    AEMeasurable (resample D i₀ j₀ a b) (P.prod P) := by
  have hpath : Measurable fun d : Draw H R => d.linkPaused i₀ j₀ :=
    (measurable_pi_apply j₀).comp ((measurable_pi_apply i₀).comp measurable_draw_linkPaused)
  have hE : AEMeasurable (fun ω => (D ω).linkOutside i₀ j₀ a b) P :=
    (measurable_linkOutside i₀ j₀ a b).comp_aemeasurable hm
  have hW : AEMeasurable (fun ω => pathWithin a b ((D ω).linkPaused i₀ j₀)) P :=
    ((measurable_pathWithin a b).comp hpath).comp_aemeasurable hm
  exact (measurable_addLink i₀ j₀).comp_aemeasurable (hE.prodMap hW)

/-- **The draw with the pauses of the period drawn again has the law of the
draw.** -/
theorem Prior.map_resample (hD : m.Prior f P D) (hm : AEMeasurable D P) (i₀ j₀ : H)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (P.prod P).map (resample D i₀ j₀ a b) = P.map D := by
  have := hD.prob
  have hpath : Measurable fun d : Draw H R => d.linkPaused i₀ j₀ :=
    (measurable_pi_apply j₀).comp ((measurable_pi_apply i₀).comp measurable_draw_linkPaused)
  have hE : AEMeasurable (fun ω => (D ω).linkOutside i₀ j₀ a b) P :=
    (measurable_linkOutside i₀ j₀ a b).comp_aemeasurable hm
  have hW : AEMeasurable (fun ω => pathWithin a b ((D ω).linkPaused i₀ j₀)) P :=
    ((measurable_pathWithin a b).comp hpath).comp_aemeasurable hm
  have hind := (hD.indepFun_linkOutside hm i₀ j₀ ha hab).symm
  have h1 : (P.prod P).map (Prod.map (fun ω => (D ω).linkOutside i₀ j₀ a b)
        (fun ω => pathWithin a b ((D ω).linkPaused i₀ j₀)))
      = P.map (fun ω => ((D ω).linkOutside i₀ j₀ a b,
          pathWithin a b ((D ω).linkPaused i₀ j₀))) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hE hW).mp hind,
      Measure.map_prod_map_of_aemeasurable P P hE hW]
  have hΓ := measurable_addLink (R := R) i₀ j₀
  have e1 : resample D i₀ j₀ a b
      = (fun q : Draw H R × (Time → ℝ) => q.1.addLink i₀ j₀ q.2)
        ∘ Prod.map (fun ω => (D ω).linkOutside i₀ j₀ a b)
          (fun ω => pathWithin a b ((D ω).linkPaused i₀ j₀)) := rfl
  have e2 : (fun q : Draw H R × (Time → ℝ) => q.1.addLink i₀ j₀ q.2)
        ∘ (fun ω => ((D ω).linkOutside i₀ j₀ a b, pathWithin a b ((D ω).linkPaused i₀ j₀)))
      = D := funext fun ω => (D ω).linkOutside_addLink i₀ j₀ a b
  rw [e1, ← AEMeasurable.map_map_of_aemeasurable hΓ.aemeasurable (hE.prodMap hW), h1,
    AEMeasurable.map_map_of_aemeasurable hΓ.aemeasurable (hE.prodMk hW), e2]

/-- **The draw with the pauses of the period drawn again is the draw of a
random world of the same member.** -/
theorem Prior.prior_resample [Countable H] (hD : m.Prior f P D) (i₀ j₀ : H) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : m.Prior f (P.prod P) (resample D i₀ j₀ a b) := by
  have := hD.prob
  have hm := hD.aemeasurable
  refine hD.of_map_eq hm inferInstance (aemeasurable_resample hm i₀ j₀ a b)
    (hD.map_resample hm i₀ j₀ ha hab) (fun ω i j => hD.split_swap ω.1 i j)
    (fun ω i j => hD.split_mem ω.1 i j) (fun ω h => hD.wander_continuous ω.1 h)
    (fun ω x => hD.deviceWander_continuous ω.1 x) (fun ω x => hD.reportError_continuous ω.1 x)
    ?_ ?_ ?_ (fun ω h => hD.hostPaused_monotone ω.1 h) (fun ω h => hD.hostPaused_zero ω.1 h)
    (fun ω h t => hD.hostPaused_rightContinuous ω.1 h t)
  · intro ω i j
    by_cases h : i = i₀ ∧ j = j₀
    · obtain ⟨rfl, rfl⟩ := h
      rw [resample_linkPaused_self]
      exact (pathOutside_monotone hab (hD.linkPaused_monotone ω.1 i j)).add
        (pathWithin_monotone a b (hD.linkPaused_monotone ω.2 i j))
    · rw [resample_linkPaused_of_ne D a b ω h]
      exact hD.linkPaused_monotone ω.1 i j
  · intro ω i j
    by_cases h : i = i₀ ∧ j = j₀
    · obtain ⟨rfl, rfl⟩ := h
      rw [resample_linkPaused_self, Pi.add_apply, pathOutside_of_le hab _ ha,
        pathWithin_of_le hab _ ha, hD.linkPaused_zero ω.1 i j, add_zero]
    · rw [resample_linkPaused_of_ne D a b ω h]
      exact hD.linkPaused_zero ω.1 i j
  · intro ω i j t
    by_cases h : i = i₀ ∧ j = j₀
    · obtain ⟨rfl, rfl⟩ := h
      rw [resample_linkPaused_self]
      exact (pathOutside_rightContinuous a b (hD.linkPaused_rightContinuous ω.1 i j) t).add
        (pathWithin_rightContinuous a b (hD.linkPaused_rightContinuous ω.2 i j) t)
    · rw [resample_linkPaused_of_ne D a b ω h]
      exact hD.linkPaused_rightContinuous ω.1 i j t

/-! ## The worlds of the changed draws -/

/-- A backlog exists at a true time when the paused time that began since
each earlier true time exceeds the time since then by a bounded amount. -/
theorem isBacklog_of_bddAbove {X : Time → ℝ} {t : Time}
    (h : BddAbove {x | ∃ s ≤ t, x = X t - X s - (t - s)}) : IsBacklog X t (backlog X t) :=
  isLUB_csSup ⟨0, t, le_rfl, by simp⟩ h

/-- When a backlog exists at one true time, the bound that a backlog needs
holds at every true time. -/
theorem IsBacklog.bddAbove {X : Time → ℝ} (hmono : Monotone X) {t₀ : Time} {v : ℝ}
    (h : IsBacklog X t₀ v) (t : Time) : BddAbove {x | ∃ s ≤ t, x = X t - X s - (t - s)} := by
  refine ⟨max (v + (X t - X t₀ - (t - t₀))) (X t - X t₀), ?_⟩
  rintro x ⟨s, hs, rfl⟩
  rcases le_total s t₀ with hst | hst
  · have h1 : X t₀ - X s - (t₀ - s) ≤ v := h.1 ⟨s, hst, rfl⟩
    exact le_max_of_le_left (by linarith)
  · have h1 := hmono hst
    exact le_max_of_le_right (by linarith)

variable {d d' : Draw H R} {w : World H R}

omit [DecidableEq H] in
/-- In a world built from a draw, the bound that a backlog of a link needs
holds at every true time. -/
theorem Builds.bddAbove_link (hB : m.Builds f d w) {i j : H}
    (hmono : Monotone (d.linkPaused i j)) (t : Time) :
    BddAbove {x | ∃ s ≤ t, x = d.linkPaused i j t - d.linkPaused i j s - (t - s)} := by
  obtain ⟨_, _, _, _, hv₂, _, _⟩ := hB.network i j 0 0
  exact hv₂.bddAbove hmono t

omit [DecidableEq H] in
/-- In a world built from a draw, the bound that a backlog of a host needs
holds at every true time. -/
theorem Builds.bddAbove_host (hB : m.Builds f d w) (h : H) (t : Time) :
    BddAbove {x | ∃ s ≤ t, x = d.hostPaused h t - d.hostPaused h s - (t - s)} := by
  obtain ⟨v₁, _, _, hv₁, _, _, _⟩ := hB.network h h t 0
  exact ⟨v₁, hv₁.1⟩

omit [DecidableEq H] in
/-- **A draw that differs from the draw of a built world only in its paused
times builds a world.** Let `w` be the world built from the draw `d`, with
positive least delays. A draw `d'` with the same splits, clocks, audio
devices and errors of reports, whose paused times satisfy the bound that a
backlog needs at every true time, builds a world: the world `w` with the
deliveries that `d'` gives. -/
theorem Builds.exists_of_paused (hB : m.Builds f d w) (hsplit : d'.split = d.split)
    (hoffset : d'.offset = d.offset) (hlogRate : d'.logRate = d.logRate)
    (hwander : d'.wander = d.wander) (hdevlog : d'.deviceLogRate = d.deviceLogRate)
    (hdevwander : d'.deviceWander = d.deviceWander) (herr : d'.reportError = d.reportError)
    (hpos : ∀ i j, 0 < d.split i j * f.roundTrip i j)
    (hhost : ∀ h t,
      BddAbove {x | ∃ s ≤ t, x = d'.hostPaused h t - d'.hostPaused h s - (t - s)})
    (hlink : ∀ i j t,
      BddAbove {x | ∃ s ≤ t, x = d'.linkPaused i j t - d'.linkPaused i j s - (t - s)}) :
    ∃ w' : World H R, m.Builds f d' w' := by
  have hbh : ∀ h t, IsBacklog (d'.hostPaused h) t (backlog (d'.hostPaused h) t) := fun h t =>
    isBacklog_of_bddAbove (hhost h t)
  have hbl : ∀ i j t, IsBacklog (d'.linkPaused i j) t (backlog (d'.linkPaused i j) t) :=
    fun i j t => isBacklog_of_bddAbove (hlink i j t)
  have hread : ∀ x t, d'.reading x t = d.reading x t := by
    intro x t
    unfold Draw.reading
    rw [hoffset, hlogRate, hwander]
  have hdev : ∀ x t, d'.deviceReading x t = d.deviceReading x t := by
    intro x t
    unfold Draw.deviceReading
    rw [hdevlog, hdevwander]
  have hlt : ∀ i j s, s < d'.arrival f i j s := by
    intro i j s
    have h1 := (hbh i s).nonneg
    have h2 := (hbl i j (s + backlog (d'.hostPaused i) s)).nonneg
    have h3 := (hbh j (s + backlog (d'.hostPaused i) s + d'.split i j * f.roundTrip i j
      + backlog (d'.linkPaused i j) (s + backlog (d'.hostPaused i) s))).nonneg
    have h4 := hpos i j
    rw [← hsplit] at h4
    unfold Draw.arrival
    linarith
  refine ⟨{ w with
    network :=
      { deliver := fun i j s _ => some (d'.arrival f i j s)
        after := fun i j s _ a h => by
          rw [← Option.some.inj h]
          exact hlt i j s } }, ?_⟩
  exact
    { rate_eq := hB.rate_eq
      sender_eq := hB.sender_eq
      host_eq := hB.host_eq
      clock := fun h t => (hB.clock h t).trans (hread h t).symm
      network := fun i j s _ => ⟨_, _, _, hbh i s, hbl i j _, hbh j _, rfl⟩
      deviceClock := fun x => by
        obtain ⟨c, hc⟩ := hB.deviceClock x
        exact ⟨c, fun t => (hc t).trans (hdev x t).symm⟩
      capture_start := hB.capture_start
      capture := fun n => by
        simp only [hdev]
        exact hB.capture n
      capture_first := hB.capture_first
      capture_handed := hB.capture_handed
      capture_reported := fun b => by
        rw [herr]
        exact hB.capture_reported b
      speaker_start := hB.speaker_start
      speaker_out := fun r k => by
        simp only [hdev]
        exact hB.speaker_out r k
      speaker_first := hB.speaker_first
      speaker_asked := fun r b => by
        simp only [hdev]
        exact hB.speaker_asked r b
      speaker_reported := fun r b => by
        rw [herr]
        exact hB.speaker_reported r b
      target_eq := hB.target_eq }

/-- **The draw without the pauses of a period builds a world.** -/
theorem Builds.exists_linkOutside (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 < d.split i j * f.roundTrip i j)
    (hmono : ∀ i j, Monotone (d.linkPaused i j)) (i₀ j₀ : H) (a b : ℝ) :
    ∃ w' : World H R, m.Builds f (d.linkOutside i₀ j₀ a b) w' := by
  refine hB.exists_of_paused rfl rfl rfl rfl rfl rfl rfl hpos
    (fun h t => hB.bddAbove_host h t) fun i j t => ?_
  by_cases hij : i = i₀ ∧ j = j₀
  · obtain ⟨rfl, rfl⟩ := hij
    obtain ⟨B, hBnd⟩ := hB.bddAbove_link (hmono i j) t
    refine ⟨B, ?_⟩
    rintro x ⟨s, hs, rfl⟩
    rw [Draw.linkOutside_self]
    have h1 := hBnd ⟨s, hs, rfl⟩
    have h2 := pathOutside_sub_le a b (hmono i j) hs
    linarith
  · rw [Draw.linkOutside_of_ne _ _ _ hij]
    exact hB.bddAbove_link (hmono i j) t

/-- **The draw with the pauses of a period drawn again builds a world**, for
every pair of outcomes. -/
theorem Prior.exists_resample (hD : m.Prior f P D) {world : Ω → World H R}
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (i₀ j₀ : H) {a b : ℝ} (hab : a ≤ b) (ω : Ω × Ω) :
    ∃ w' : World H R, m.Builds f (resample D i₀ j₀ a b ω) w' := by
  refine (hB ω.1).exists_of_paused rfl rfl rfl rfl rfl rfl rfl
    (fun i j => hD.leastDelay_pos ω.1 i j) (fun h t => (hB ω.1).bddAbove_host h t)
    fun i j t => ?_
  by_cases hij : i = i₀ ∧ j = j₀
  · obtain ⟨rfl, rfl⟩ := hij
    obtain ⟨B, hBnd⟩ := (hB ω.1).bddAbove_link (hD.linkPaused_monotone ω.1 i j) t
    refine ⟨B + ((D ω.2).linkPaused i j b - (D ω.2).linkPaused i j a), ?_⟩
    rintro x ⟨s, hs, rfl⟩
    rw [resample_linkPaused_self]
    have h1 := hBnd ⟨s, hs, rfl⟩
    have h2 := pathOutside_sub_le a b (hD.linkPaused_monotone ω.1 i j) hs
    have h3 := pathWithin_le a b (hD.linkPaused_monotone ω.2 i j) t
    have h4 := pathWithin_nonneg hab (hD.linkPaused_monotone ω.2 i j) s
    simp only [Pi.add_apply]
    linarith
  · rw [resample_linkPaused_of_ne D a b ω hij]
    exact (hB ω.1).bddAbove_link (hD.linkPaused_monotone ω.1 i j) t

/-! ## From the second random world to the world without the pauses of the period -/

/-- With positive probability, no paused time begins in a period. -/
theorem pauseLaw_singleton_zero_pos (count : ℝ≥0) (F : Measure ℝ) :
    0 < pauseLaw count F {0} := by
  have h1 : (poissonMeasure count {0} • sumLaw F 0) {0} ≤ pauseLaw count F {0} :=
    Measure.le_sum (fun n : ℕ => poissonMeasure count {n} • sumLaw F n) 0 {0}
  refine lt_of_lt_of_le ?_ h1
  have h2 : (poissonMeasure count {0} • sumLaw F 0) {0} = poissonMeasure count {0} := by
    simp [sumLaw]
  rw [h2, poissonMeasure_singleton]
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- **What holds for almost every pair of outcomes holds without the pauses
of the period.** If a property of a draw holds for the draw with the pauses
of the period drawn again, for almost every pair of outcomes, then it holds
for the draw without the pauses of the period, for almost every outcome. The
pairs whose second outcome has no pause of the link in the period have
positive probability, and there the draw with the pauses drawn again is the
draw of the first outcome without them. -/
theorem Prior.ae_linkOutside (hD : m.Prior f P D) (i₀ j₀ : H) {a b : ℝ}
    (hab : a ≤ b) {p : Draw H R → Prop} (h : ∀ᵐ ω ∂(P.prod P), p (resample D i₀ j₀ a b ω)) :
    ∀ᵐ ω ∂P, p ((D ω).linkOutside i₀ j₀ a b) := by
  have := hD.prob
  have hlaw := hD.linkPaused_law i₀ j₀ a b hab
  have hE : 0 < P {ω | (D ω).linkPaused i₀ j₀ b - (D ω).linkPaused i₀ j₀ a = 0} := by
    have e : {ω | (D ω).linkPaused i₀ j₀ b - (D ω).linkPaused i₀ j₀ a = 0}
        = (fun ω => (D ω).linkPaused i₀ j₀ b - (D ω).linkPaused i₀ j₀ a) ⁻¹' {0} := rfl
    rw [e, ← Measure.map_apply_of_aemeasurable hlaw.aemeasurable (measurableSet_singleton 0),
      hlaw.map_eq]
    exact pauseLaw_singleton_zero_pos _ _
  have hsub : {ω | ¬p ((D ω).linkOutside i₀ j₀ a b)}
        ×ˢ {ω | (D ω).linkPaused i₀ j₀ b - (D ω).linkPaused i₀ j₀ a = 0}
      ⊆ {ω : Ω × Ω | ¬p (resample D i₀ j₀ a b ω)} := by
    rintro ⟨ω₁, ω₂⟩ ⟨h1, h2⟩
    have e := resample_of_eq D i₀ j₀ hab (ω := (ω₁, ω₂)) (hD.linkPaused_monotone ω₂ i₀ j₀)
      (sub_eq_zero.mp h2)
    show ¬p (resample D i₀ j₀ a b (ω₁, ω₂))
    rw [e]
    exact h1
  have hnull := measure_mono_null hsub (ae_iff.mp h)
  rw [Measure.prod_prod] at hnull
  rcases mul_eq_zero.mp hnull with h0 | h0
  · exact ae_iff.mpr h0
  · exact absurd h0 hE.ne'

/-- **The playback in the world without the pauses of a period is the same
measurable function of the draw.** Take a solution whose playback is a
measurable function of what is drawn (`measurablePlays`), a random world of
the member, a link, a period from `a` to `b` that begins at or after true
time zero, and for every outcome the world built from the draw without the
paused time of the link that begins within the period. For every speaker
and output sample there are a measurable set `S` of draws and a measurable
function `G` of the draw that describe what the speaker plays there, for
almost every outcome, both in the world of the outcome and in the world
without the pauses of the period: in each, the speaker plays the source
exactly when the draw of that world is in `S`, and then it plays the
position `G` of that draw. -/
theorem ae_plays_linkOutside [Countable H] {Msg : Type} {τ : Solution H R Msg}
    {lookahead : ℕ+} (hτ : measurablePlays m f lookahead Msg τ) (hD : m.Prior f P D)
    {world : Ω → World H R} (hB : ∀ ω, m.Builds f (D ω) (world ω)) (i₀ j₀ : H) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) {worldOut : Ω → World H R}
    (hOut : ∀ ω, m.Builds f ((D ω).linkOutside i₀ j₀ a b) (worldOut ω)) (r : Fin R) (k : ℕ) :
    ∃ (S : Set (Draw H R)) (G : Draw H R → ℝ), MeasurableSet S ∧ Measurable G ∧
      (∀ᵐ ω ∂P, ∀ x : ℝ,
        τ.plays (world ω) lookahead r k = some x ↔ D ω ∈ S ∧ G (D ω) = x) ∧
      ∀ᵐ ω ∂P, ∀ x : ℝ, τ.plays (worldOut ω) lookahead r k = some x
        ↔ (D ω).linkOutside i₀ j₀ a b ∈ S ∧ G ((D ω).linkOutside i₀ j₀ a b) = x := by
  obtain ⟨S, G, hS, hG, hSG⟩ := hτ r k
  refine ⟨S, G, hS, hG, hSG Ω P D world hD hB, ?_⟩
  have := hD.prob
  have hex := fun ω : Ω × Ω => hD.exists_resample hB i₀ j₀ hab ω
  have h2 := hSG (Ω × Ω) (P.prod P) (resample D i₀ j₀ a b)
    (fun ω => Classical.choose (hex ω)) (hD.prior_resample i₀ j₀ ha hab)
    (fun ω => Classical.choose_spec (hex ω))
  have h3 : ∀ᵐ ω ∂(P.prod P), (fun d : Draw H R => ∀ w : World H R, m.Builds f d w →
      ∀ x : ℝ, τ.plays w lookahead r k = some x ↔ d ∈ S ∧ G d = x)
        (resample D i₀ j₀ a b ω) := by
    filter_upwards [h2] with ω hω w hw
    rw [hw.unique (Classical.choose_spec (hex ω))]
    exact hω
  have h4 := Prior.ae_linkOutside
    (p := fun d : Draw H R => ∀ w : World H R, m.Builds f d w →
      ∀ x : ℝ, τ.plays w lookahead r k = some x ↔ d ∈ S ∧ G d = x) hD i₀ j₀ hab h3
  filter_upwards [h4] with ω hω
  exact hω (worldOut ω) (hOut ω)

end Unisono.Spec.GenerativeWorld
