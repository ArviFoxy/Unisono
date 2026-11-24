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
  {P : Measure Ω} {D : Ω → Draw H R}

theorem Draw.ext_fields {d d' : Draw H R} (hsplit : d.split = d'.split)
    (hoffset : d.offset = d'.offset) (hlogRate : d.logRate = d'.logRate)
    (hwander : d.wander = d'.wander) (hlink : d.linkPaused = d'.linkPaused)
    (hhost : d.hostPaused = d'.hostPaused) (hdevlog : d.deviceLogRate = d'.deviceLogRate)
    (hdevwander : d.deviceWander = d'.deviceWander) (herr : d.reportError = d'.reportError) :
    d = d' := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := d
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := d'
  dsimp only at hsplit hoffset hlogRate hwander hlink hhost hdevlog hdevwander herr
  subst hsplit hoffset hlogRate hwander hlink hhost hdevlog hdevwander herr
  rfl

/-- **A draw determines the world built from it.** -/
theorem Builds.unique {d : Draw H R} {w w' : World H R} (h : m.Builds f d w)
    (h' : m.Builds f d w') : w = w' := by
  have hsender : w.sender = w'.sender := h.sender_eq.trans h'.sender_eq.symm
  have hhost : w.host = w'.host := h.host_eq.trans h'.host_eq.symm
  have hclock : w.clock = w'.clock :=
    funext fun x => Clock.ext_read fun t => (h.clock x t).trans (h'.clock x t).symm
  have hinj : ∀ x, Function.Injective (w.clock x).read := fun x => (w.clock x).strictMono.injective
  have hdinj : ∀ x, Function.Injective (d.deviceReading x) := fun x => by
    obtain ⟨c, hc⟩ := h.deviceClock x
    have heq : d.deviceReading x = c.read := funext fun t => (hc t).symm
    rw [heq]
    exact c.strictMono.injective
  refine World.ext_fields (h.rate_eq.trans h'.rate_eq.symm) hsender hhost hclock ?_ ?_ ?_ ?_
  · have hcap0 : w.source.capture 0 = w'.source.capture 0 := by
      apply hinj w.sender
      rw [h.capture_start]
      have h2 := h'.capture_start
      rw [← hsender, ← hclock] at h2
      exact h2.symm
    have hcap : ∀ n, w.source.capture n = w'.source.capture n := fun n => by
      apply hdinj none
      have h1 := h.capture n
      have h2 := h'.capture n
      rw [← hcap0] at h2
      linarith
    have hfirst : ∀ b, w.source.first b = w'.source.first b := fun b =>
      (h.capture_first b).trans (h'.capture_first b).symm
    refine CaptureDevice.ext_fields hcap hfirst (fun b => ?_) (fun b => ?_)
    · rw [h.capture_handed, h'.capture_handed, hfirst, hcap]
    · rw [h.capture_reported, h'.capture_reported, hfirst, hcap, hsender, hclock]
  · funext r
    have hout0 : (w.speaker r).out 0 = (w'.speaker r).out 0 := by
      apply hinj (w.host r)
      rw [h.speaker_start r]
      have h2 := h'.speaker_start r
      rw [← hhost, ← hclock] at h2
      exact h2.symm
    have hout : ∀ k, (w.speaker r).out k = (w'.speaker r).out k := fun k => by
      apply hdinj (some (m.device r))
      have h1 := h.speaker_out r k
      have h2 := h'.speaker_out r k
      rw [← hout0] at h2
      linarith
    have hfirst : ∀ b, (w.speaker r).first b = (w'.speaker r).first b := fun b =>
      (h.speaker_first r b).trans (h'.speaker_first r b).symm
    refine PlaybackDevice.ext_fields hout hfirst (fun b => ?_) (fun b => ?_)
    · apply hdinj (some (m.device r))
      have h1 := h.speaker_asked r b
      have h2 := h'.speaker_asked r b
      rw [← hfirst, ← hout] at h2
      linarith
    · rw [h.speaker_reported, h'.speaker_reported, hfirst, hout, hhost, hclock]
  · refine Network.ext_deliver fun i j s q => ?_
    obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, hd⟩ := h.network i j s q
    obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, hd'⟩ := h'.network i j s q
    have e₁ : v₁ = u₁ := IsLUB.unique hv₁ hu₁
    subst e₁
    have e₂ : v₂ = u₂ := IsLUB.unique hv₂ hu₂
    subst e₂
    have e₃ : v₃ = u₃ := IsLUB.unique hv₃ hu₃
    subst e₃
    rw [hd, hd']
  · funext n
    rw [h.target_eq, h'.target_eq]

/-! ## The coordinates of a draw -/

/-- The coordinates of a draw: the split of every pair of distinct hosts,
taken in its fixed order, and the offset of every clock. The coordinates of
the mean rates, the wander, the paused times and the errors of the reports
are zero. -/
def Draw.coordinates (d : Draw H R) : Component H R → ℝ
  | .split z => d.split (refOrientation H z).1.1 (refOrientation H z).1.2
  | .offset h => d.offset h
  | .logRate _ => 0
  | .wander _ => 0
  | .linkPaused _ _ => 0
  | .hostPaused _ => 0
  | .deviceLogRate _ => 0
  | .deviceWander _ => 0
  | .reportError _ => 0

/-- The number that each component of a draw contributes to its
coordinates. -/
def Component.scalar : (p : Component H R) → p.Val → ℝ
  | .split _ => fun u => u
  | .offset _ => fun u => u
  | .logRate _ => fun _ => 0
  | .wander _ => fun _ => 0
  | .linkPaused _ _ => fun _ => 0
  | .hostPaused _ => fun _ => 0
  | .deviceLogRate _ => fun _ => 0
  | .deviceWander _ => fun _ => 0
  | .reportError _ => fun _ => 0

theorem Component.measurable_scalar (p : Component H R) : Measurable p.scalar := by
  cases p with
  | split z => exact measurable_id
  | offset h => exact measurable_id
  | logRate h => exact measurable_const
  | wander h => exact measurable_const
  | linkPaused i j => exact measurable_const
  | hostPaused h => exact measurable_const
  | deviceLogRate x => exact measurable_const
  | deviceWander x => exact measurable_const
  | reportError x => exact measurable_const

theorem Draw.coordinates_eq_scalar (d : Draw H R) (p : Component H R) :
    d.coordinates p = p.scalar (d.component (refOrientation H) p) := by
  cases p <;> rfl

section Coordinates

variable [DecidableEq H]

/-- A draw with no mean-rate spread, no wander, no pause and no error of a
report is the draw of its own coordinates. -/
theorem canonicalDraw_coordinates (d : Draw H R) (hswap : ∀ i j, d.split i j + d.split j i = 1)
    (hmem : ∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1) (hlog : ∀ h, d.logRate h = 0)
    (hwander : ∀ h t, d.wander h t = 0) (hlink : ∀ i j t, d.linkPaused i j t = 0)
    (hhost : ∀ h t, d.hostPaused h t = 0) (hdevlog : ∀ x, d.deviceLogRate x = 0)
    (hdevwander : ∀ x t, d.deviceWander x t = 0) (herr : ∀ x t, d.reportError x t = 0) :
    canonicalDraw d.coordinates = d := by
  have hof : ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 → splitOf u = u := fun u hu => by
    simp [splitOf, hu.1, hu.2]
  refine Draw.ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    exact (hlink i j t).symm
  · funext h t
    exact (hhost h t).symm
  · funext x
    exact (hdevlog x).symm
  · funext x t
    exact (hdevwander x t).symm
  · funext x t
    exact (herr x t).symm

/-- Each split of the draw of an outcome is a measurable function of the
outcome. -/
theorem measurable_canonicalDraw_split (i j : H) :
    Measurable fun y : Component H R → ℝ => (canonicalDraw y).split i j := by
  by_cases h : i = j
  · subst h
    have hc : (fun y : Component H R → ℝ => (canonicalDraw y).split i i) = fun _ => 1 / 2 := by
      funext y
      simp [canonicalDraw]
    rw [hc]
    exact measurable_const
  · have hc : (fun y : Component H R → ℝ => (canonicalDraw y).split i j)
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
theorem measurable_canonicalDraw : Measurable (canonicalDraw (H := H) (R := R)) := by
  refine measurable_comap_iff.mpr ?_
  have h1 : Measurable fun y : Component H R → ℝ => (canonicalDraw y).split :=
    Measurable.of_eval fun i => Measurable.of_eval fun j => measurable_canonicalDraw_split i j
  have h2 : Measurable fun y : Component H R → ℝ => (canonicalDraw y).offset :=
    Measurable.of_eval fun h => measurable_pi_apply _
  have h3 : Measurable fun _ : Component H R → ℝ => fun _ : H => (0 : ℝ) := measurable_const
  have h4 : Measurable fun _ : Component H R → ℝ => fun (_ : H) (_ : Time) => (0 : ℝ) :=
    measurable_const
  have h5 : Measurable fun _ : Component H R → ℝ => fun (_ _ : H) (_ : Time) => (0 : ℝ) :=
    measurable_const
  have h6 : Measurable fun _ : Component H R → ℝ => fun (_ : H) (_ : Time) => (0 : ℝ) :=
    measurable_const
  have h7 : Measurable fun _ : Component H R → ℝ => fun _ : Option (Fin R) => (0 : ℝ) :=
    measurable_const
  have h8 : Measurable fun _ : Component H R → ℝ =>
      fun (_ : Option (Fin R)) (_ : Time) => (0 : ℝ) := measurable_const
  exact h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk (h6.prodMk
    (h7.prodMk (h8.prodMk h8)))))))

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
    | linkPaused i j => exact hzero
    | hostPaused h => exact hzero
    | deviceLogRate x => exact hzero
    | deviceWander x => exact hzero
    | reportError x => exact hzero
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
  have hlink : ∀ᵐ ω ∂P, ∀ i j, ∀ s t, (D ω).linkPaused i j s = (D ω).linkPaused i j t :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
      hD.linkPaused_ae_const (hf.no_linkPauses i j)
  have hhost : ∀ᵐ ω ∂P, ∀ h, ∀ s t, (D ω).hostPaused h s = (D ω).hostPaused h t :=
    ae_all_iff.mpr fun h => hD.hostPaused_ae_const (hf.no_hostPauses h)
  have hdevlog : ∀ᵐ ω ∂P, ∀ x, (D ω).deviceLogRate x = 0 :=
    ae_all_iff.mpr fun x => hD.deviceLogRate_ae_eq_zero hf.no_spread x
  have hdevwander : ∀ᵐ ω ∂P, ∀ x, ∀ t, (D ω).deviceWander x t = 0 :=
    ae_all_iff.mpr fun x => hD.deviceWander_ae_eq_zero (hf.no_deviceWander x)
  have herr : ∀ᵐ ω ∂P, ∀ x, ∀ t, (D ω).reportError x t = 0 :=
    ae_all_iff.mpr fun x => hD.reportError_ae_eq_zero (hf.no_reportError x)
  filter_upwards [hlog, hwander, hlink, hhost, hdevlog, hdevwander, herr]
    with ω h1 h2 h3 h4 h5 h6 h7
  exact canonicalDraw_coordinates (D ω) (hD.split_swap ω) (hD.split_mem ω) h1 h2
    (fun i j t => by rw [h3 i j t 0, hD.linkPaused_zero ω i j])
    (fun h t => by rw [h4 h t 0, hD.hostPaused_zero ω h]) h5 h6 h7

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
    {p : Draw H R → World H R → Prop}
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
