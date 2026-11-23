/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeCanonical

/-!
# All random worlds of a noiseless member agree

A noiseless member of the generative model has many random worlds: any
probability space with a draw that has the law of the member. This file
shows that they all agree with the concrete random world of
`Unisono.Spec.Models.GenerativeCanonical`, whose outcomes are the
coordinates of the components.

* A draw determines the world built from it (`Builds.unique`).
* In almost every outcome, the draw of a noiseless member is the draw of its
  own coordinates (`Prior.ae_eq_canonicalDraw`), so the world is the
  concrete world of those coordinates (`Prior.ae_eq_canonicalWorld`).
* The coordinates have the law of the concrete probability space
  (`Prior.coordinates_law`).

Two consequences are used to compare solutions. A property that holds in
almost every outcome of the concrete random world holds in almost every
outcome of every random world of the member (`Prior.ae_of_ae_canonical`).
The mean of a function of the world is the same in every random world of the
member, when the function is measurable on the concrete probability space
(`Prior.lintegral_eq_canonical`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-! ## Worlds with the same parts are equal -/

theorem Clock.ext_read {a b : Clock} (h : ∀ t, a.read t = b.read t) : a = b := by
  obtain ⟨ra, _, _⟩ := a
  obtain ⟨rb, _, _⟩ := b
  obtain rfl : ra = rb := funext h
  rfl

theorem CaptureDevice.ext_fields {a b : CaptureDevice}
    (hc : ∀ n, a.capture n = b.capture n) (hf : ∀ k, a.first k = b.first k)
    (hh : ∀ k, a.handed k = b.handed k) (hr : ∀ k, a.reported k = b.reported k) : a = b := by
  obtain ⟨c₁, _, f₁, _, _, h₁, _, _, r₁⟩ := a
  obtain ⟨c₂, _, f₂, _, _, h₂, _, _, r₂⟩ := b
  obtain rfl : c₁ = c₂ := funext hc
  obtain rfl : f₁ = f₂ := funext hf
  obtain rfl : h₁ = h₂ := funext hh
  obtain rfl : r₁ = r₂ := funext hr
  rfl

theorem PlaybackDevice.ext_fields {a b : PlaybackDevice}
    (ho : ∀ k, a.out k = b.out k) (hf : ∀ k, a.first k = b.first k)
    (ha : ∀ k, a.asked k = b.asked k) (hr : ∀ k, a.reported k = b.reported k) : a = b := by
  obtain ⟨o₁, _, f₁, _, _, a₁, _, _, r₁⟩ := a
  obtain ⟨o₂, _, f₂, _, _, a₂, _, _, r₂⟩ := b
  obtain rfl : o₁ = o₂ := funext ho
  obtain rfl : f₁ = f₂ := funext hf
  obtain rfl : a₁ = a₂ := funext ha
  obtain rfl : r₁ = r₂ := funext hr
  rfl

theorem Network.ext_deliver {a b : Network H}
    (h : ∀ i j s q, a.deliver i j s q = b.deliver i j s q) : a = b := by
  obtain ⟨d₁, _⟩ := a
  obtain ⟨d₂, _⟩ := b
  obtain rfl : d₁ = d₂ := funext fun i => funext fun j => funext fun s => funext fun q => h i j s q
  rfl

/-- Two worlds with the same rate, hosts, clocks, devices, network and target
latencies are equal. -/
theorem World.ext_fields {w w' : World H R} (hrate : w.rate = w'.rate)
    (hsender : w.sender = w'.sender) (hhost : w.host = w'.host) (hclock : w.clock = w'.clock)
    (hsource : w.source = w'.source) (hspeaker : w.speaker = w'.speaker)
    (hnetwork : w.network = w'.network) (htarget : w.target = w'.target) : w = w' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := w
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := w'
  dsimp only at hrate hsender hhost hclock hsource hspeaker hnetwork htarget
  subst hrate hsender hhost hclock hsource hspeaker hnetwork htarget
  rfl

namespace GenerativeWorld

variable {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R} {f : Member H R}
  {P : Measure Ω} {D : Ω → Draw H}

theorem Draw.ext_fields {d d' : Draw H} (hsplit : d.split = d'.split)
    (hoffset : d.offset = d'.offset) (hlogRate : d.logRate = d'.logRate)
    (hwander : d.wander = d'.wander) (htraffic : d.traffic = d'.traffic) : d = d' := by
  obtain ⟨_, _, _, _, _⟩ := d
  obtain ⟨_, _, _, _, _⟩ := d'
  dsimp only at hsplit hoffset hlogRate hwander htraffic
  subst hsplit hoffset hlogRate hwander htraffic
  rfl

/-- **A draw determines the world built from it.** -/
theorem Builds.unique {d : Draw H} {w w' : World H R} (h : m.Builds f d w)
    (h' : m.Builds f d w') : w = w' := by
  have hsender : w.sender = w'.sender := h.sender_eq.trans h'.sender_eq.symm
  have hhost : w.host = w'.host := h.host_eq.trans h'.host_eq.symm
  have hclock : w.clock = w'.clock :=
    funext fun x => Clock.ext_read fun t => (h.clock x t).trans (h'.clock x t).symm
  have hinj : ∀ x, Function.Injective (w.clock x).read := fun x => (w.clock x).strictMono.injective
  refine World.ext_fields (h.rate_eq.trans h'.rate_eq.symm) hsender hhost hclock ?_ ?_ ?_ ?_
  · have hcap : ∀ n, w.source.capture n = w'.source.capture n := fun n => by
      apply hinj w.sender
      rw [h.capture n]
      have h2 := h'.capture n
      rw [← hsender, ← hclock] at h2
      exact h2.symm
    have hfirst : ∀ b, w.source.first b = w'.source.first b := fun b =>
      (h.capture_first b).trans (h'.capture_first b).symm
    refine CaptureDevice.ext_fields hcap hfirst (fun b => ?_) (fun b => ?_)
    · rw [h.capture_handed, h'.capture_handed, hfirst, hcap]
    · rw [h.capture_reported, h'.capture_reported, hfirst, hcap, hsender, hclock]
  · funext r
    have hout : ∀ k, (w.speaker r).out k = (w'.speaker r).out k := fun k => by
      apply hinj (w.host r)
      rw [h.speaker_out r k]
      have h2 := h'.speaker_out r k
      rw [← hhost, ← hclock] at h2
      exact h2.symm
    have hfirst : ∀ b, (w.speaker r).first b = (w'.speaker r).first b := fun b =>
      (h.speaker_first r b).trans (h'.speaker_first r b).symm
    refine PlaybackDevice.ext_fields hout hfirst (fun b => ?_) (fun b => ?_)
    · apply hinj (w.host r)
      have h1 := h.speaker_asked r b
      have h2 := h'.speaker_asked r b
      rw [← hhost, ← hclock, ← hfirst, ← hout] at h2
      linarith
    · rw [h.speaker_reported, h'.speaker_reported, hfirst, hout, hhost, hclock]
  · refine Network.ext_deliver fun i j s q => ?_
    obtain ⟨v, hv, hd⟩ := h.network i j s q
    obtain ⟨v', hv', hd'⟩ := h'.network i j s q
    rw [hd, hd', IsLUB.unique hv hv']
  · funext n
    rw [h.target_eq, h'.target_eq]

/-! ## The coordinates of a draw -/

/-- The coordinates of a draw: the split of every pair of distinct hosts,
taken in its fixed order, and the offset of every clock. The coordinates of
the mean rates, the wander and the traffic are zero. -/
def Draw.coordinates (d : Draw H) : Component H → ℝ
  | .split z => d.split (refOrientation H z).1.1 (refOrientation H z).1.2
  | .offset h => d.offset h
  | .logRate _ => 0
  | .wander _ => 0
  | .traffic _ _ => 0

/-- The number that each component of a draw contributes to its
coordinates. -/
def Component.scalar : (p : Component H) → p.Val → ℝ
  | .split _ => fun u => u
  | .offset _ => fun u => u
  | .logRate _ => fun _ => 0
  | .wander _ => fun _ => 0
  | .traffic _ _ => fun _ => 0

theorem Component.measurable_scalar (p : Component H) : Measurable p.scalar := by
  cases p with
  | split z => exact measurable_id
  | offset h => exact measurable_id
  | logRate h => exact measurable_const
  | wander h => exact measurable_const
  | traffic i j => exact measurable_const

theorem Draw.coordinates_eq_scalar (d : Draw H) (p : Component H) :
    d.coordinates p = p.scalar (d.component (refOrientation H) p) := by
  cases p <;> rfl

section Coordinates

variable [DecidableEq H]

/-- A draw with no mean-rate spread, no wander and no other traffic is the
draw of its own coordinates. -/
theorem canonicalDraw_coordinates (d : Draw H) (hswap : ∀ i j, d.split i j + d.split j i = 1)
    (hmem : ∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1) (hlog : ∀ h, d.logRate h = 0)
    (hwander : ∀ h t, d.wander h t = 0) (htraffic : ∀ i j t, d.traffic i j t = 0) :
    canonicalDraw d.coordinates = d := by
  have hof : ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 → splitOf u = u := fun u hu => by
    simp [splitOf, hu.1, hu.2]
  refine Draw.ext_fields ?_ ?_ ?_ ?_ ?_
  · funext i j
    by_cases h : i = j
    · subst h
      have h1 : (canonicalDraw d.coordinates).split i i = 1 / 2 := by simp [canonicalDraw]
      rw [h1]
      linarith [hswap i i]
    · have hval : d.coordinates (.split (pairOf i j h))
          = d.split (refOrientation H (pairOf i j h)).1.1 (refOrientation H (pairOf i j h)).1.2 :=
        rfl
      simp only [canonicalDraw, dite_eq_right h]
      rcases refOrientation_pairOf i j h with hp | hp
      · rw [ite_eq_left hp, hval, hp]
        exact hof _ (hmem i j)
      · have hne : (refOrientation H (pairOf i j h)).1 ≠ (i, j) := by
          rw [hp]
          intro he
          exact h (Prod.ext_iff.mp he).2
        rw [ite_eq_right hne, hval, hp]
        change 1 - splitOf (d.split j i) = d.split i j
        rw [hof _ (hmem j i)]
        linarith [hswap i j]
  · funext h
    rfl
  · funext h
    exact (hlog h).symm
  · funext h t
    exact (hwander h t).symm
  · funext i j t
    exact (htraffic i j t).symm

/-- Each split of the draw of an outcome is a measurable function of the
outcome. -/
theorem measurable_canonicalDraw_split (i j : H) :
    Measurable fun y : Component H → ℝ => (canonicalDraw y).split i j := by
  by_cases h : i = j
  · subst h
    have hc : (fun y : Component H → ℝ => (canonicalDraw y).split i i) = fun _ => 1 / 2 := by
      funext y
      simp [canonicalDraw]
    rw [hc]
    exact measurable_const
  · have hc : (fun y : Component H → ℝ => (canonicalDraw y).split i j)
        = fun y => if (refOrientation H (pairOf i j h)).1 = (i, j) then
            splitOf (y (.split (pairOf i j h)))
          else 1 - splitOf (y (.split (pairOf i j h))) := by
      funext y
      simp only [canonicalDraw, dite_eq_right h]
    rw [hc]
    exact Measurable.ite (MeasurableSet.const _)
      (measurable_splitOf.comp (measurable_pi_apply _))
      ((measurable_splitOf.comp (measurable_pi_apply _)).const_sub 1)

/-- The draw of an outcome is a measurable function of the outcome. -/
theorem measurable_canonicalDraw : Measurable (canonicalDraw (H := H)) := by
  refine measurable_comap_iff.mpr ?_
  have h1 : Measurable fun y : Component H → ℝ => (canonicalDraw y).split :=
    Measurable.of_eval fun i => Measurable.of_eval fun j => measurable_canonicalDraw_split i j
  have h2 : Measurable fun y : Component H → ℝ => (canonicalDraw y).offset :=
    Measurable.of_eval fun h => measurable_pi_apply _
  have h3 : Measurable fun _ : Component H → ℝ => fun _ : H => (0 : ℝ) := measurable_const
  have h4 : Measurable fun _ : Component H → ℝ => fun (_ : H) (_ : Time) => (0 : ℝ) :=
    measurable_const
  have h5 : Measurable fun _ : Component H → ℝ => fun (_ _ : H) (_ : Time) => (0 : ℝ) :=
    measurable_const
  exact h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk h5)))

variable [Fintype H]

/-- **The coordinates of the draw of a noiseless member have the law of the
concrete probability space.** -/
theorem Prior.coordinates_law (hD : m.Prior f P D) :
    HasLaw (fun ω => (D ω).coordinates) (Measure.pi (canonicalLaw m f)) P := by
  have := hD.prob
  have hind : iIndepFun (fun p ω => (D ω).coordinates p) P := by
    have h := (hD.independent (refOrientation H)).comp Component.scalar
      Component.measurable_scalar
    have hfun : (fun p ω => (D ω).coordinates p)
        = fun p => p.scalar ∘ fun ω => (D ω).component (refOrientation H) p := by
      funext p ω
      exact (D ω).coordinates_eq_scalar p
    rw [hfun]
    exact h
  have hzero : HasLaw (fun _ : Ω => (0 : ℝ)) (Measure.dirac 0) P :=
    ⟨aemeasurable_const, by simp [Measure.map_const]⟩
  have hlaw : ∀ p, HasLaw (fun ω => (D ω).coordinates p) (canonicalLaw m f p) P := by
    intro p
    cases p with
    | split z =>
      have hz : s(((refOrientation H z).1).1, ((refOrientation H z).1).2) = z.1 :=
        (refOrientation H z).2
      have hne : ((refOrientation H z).1).1 ≠ ((refOrientation H z).1).2 := by
        intro h
        apply z.2
        rw [← hz]
        exact Sym2.mk_isDiag_iff.mpr h
      exact hD.split_law _ _ hne
    | offset h => exact hD.offset_law h
    | logRate h => exact hzero
    | wander h => exact hzero
    | traffic i j => exact hzero
  have hae : ∀ p, AEMeasurable (fun ω => (D ω).coordinates p) P := fun p => (hlaw p).aemeasurable
  refine ⟨AEMeasurable.of_eval hae, ?_⟩
  refine ((iIndepFun_iff_map_fun_eq_pi_map hae).mp hind).trans ?_
  congr 1
  funext p
  exact (hlaw p).map_eq

/-- In almost every outcome, the draw of a noiseless member is the draw of
its own coordinates. -/
theorem Prior.ae_eq_canonicalDraw (hD : m.Prior f P D) (hf : f.Noiseless) :
    ∀ᵐ ω ∂P, canonicalDraw (D ω).coordinates = D ω := by
  have := hD.prob
  have hlog : ∀ᵐ ω ∂P, ∀ h, (D ω).logRate h = 0 :=
    ae_all_iff.mpr fun h => hD.logRate_ae_eq_zero hf.no_spread h
  have hwander : ∀ᵐ ω ∂P, ∀ h, ∀ t, (D ω).wander h t = 0 :=
    ae_all_iff.mpr fun h => hD.wander_ae_eq_zero (hf.no_wander h)
  have htraffic : ∀ᵐ ω ∂P, ∀ i j, ∀ s t, (D ω).traffic i j s = (D ω).traffic i j t :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hD.traffic_ae_const (hf.no_traffic i j)
  filter_upwards [hlog, hwander, htraffic] with ω h1 h2 h3
  exact canonicalDraw_coordinates (D ω) (hD.split_swap ω) (hD.split_mem ω) h1 h2
    fun i j t => by rw [h3 i j t 0, hD.traffic_zero ω i j]

variable {world : Ω → World H R}

/-- **Every random world of a noiseless member is the concrete one.** In
almost every outcome, the world is the concrete world of the coordinates of
its draw. -/
theorem Prior.ae_eq_canonicalWorld (hD : m.Prior f P D) (hf : f.Noiseless)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) :
    ∀ᵐ ω ∂P, world ω = canonicalWorld m f hex (D ω).coordinates := by
  filter_upwards [hD.ae_eq_canonicalDraw hf] with ω hω
  have h := canonicalWorld_builds m f hex (D ω).coordinates
  rw [hω] at h
  exact (hB ω).unique h

/-- A property of the draw and the world that holds in almost every outcome
of the concrete random world of a noiseless member holds in almost every
outcome of every random world of the member. -/
theorem Prior.ae_of_ae_canonicalDraw (hD : m.Prior f P D) (hf : f.Noiseless)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h)
    {p : Draw H → World H R → Prop}
    (h : ∀ᵐ y ∂Measure.pi (canonicalLaw m f), p (canonicalDraw y) (canonicalWorld m f hex y)) :
    ∀ᵐ ω ∂P, p (D ω) (world ω) := by
  have hlaw := hD.coordinates_law
  rw [← hlaw.map_eq] at h
  filter_upwards [ae_of_ae_map hlaw.aemeasurable h, hD.ae_eq_canonicalWorld hf hB hex,
    hD.ae_eq_canonicalDraw hf] with ω h1 h2 h3
  rw [h3] at h1
  rw [h2]
  exact h1

/-- A property of the world that holds in almost every outcome of the
concrete random world of a noiseless member holds in almost every outcome of
every random world of the member. -/
theorem Prior.ae_of_ae_canonical (hD : m.Prior f P D) (hf : f.Noiseless)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h)
    {p : World H R → Prop}
    (h : ∀ᵐ y ∂Measure.pi (canonicalLaw m f), p (canonicalWorld m f hex y)) :
    ∀ᵐ ω ∂P, p (world ω) :=
  hD.ae_of_ae_canonicalDraw hf hB hex (p := fun _ w => p w) h

/-- **The mean of a function of the world is the same in every random world
of a noiseless member.** It is the mean in the concrete random world, when
the function is measurable there. -/
theorem Prior.lintegral_eq_canonical (hD : m.Prior f P D) (hf : f.Noiseless)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h)
    {F : World H R → ℝ≥0∞}
    (hF : AEMeasurable (fun y => F (canonicalWorld m f hex y)) (Measure.pi (canonicalLaw m f))) :
    ∫⁻ ω, F (world ω) ∂P = ∫⁻ y, F (canonicalWorld m f hex y) ∂Measure.pi (canonicalLaw m f) := by
  have hlaw := hD.coordinates_law
  have h1 : ∫⁻ ω, F (world ω) ∂P = ∫⁻ ω, F (canonicalWorld m f hex (D ω).coordinates) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hD.ae_eq_canonicalWorld hf hB hex] with ω h
    rw [h]
  rw [h1, ← hlaw.map_eq]
  rw [← hlaw.map_eq] at hF
  exact (lintegral_map' hF hlaw.aemeasurable).symm

end Coordinates

end GenerativeWorld

end Unisono.Spec
