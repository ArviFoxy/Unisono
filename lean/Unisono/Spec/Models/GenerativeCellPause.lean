/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeCellMean

/-!
# The mean over what a link pauses within a period

In a random world of any member of the generative model, take a link and a
period from `a` to `b` that begins at or after true time zero. What the link
pauses within the period is independent of the draw without it
(`Prior.indepFun_linkOutside`), and it has the law `pauseLaw`.

* `Prior.lintegral_cell_ge`: the mean of a function of the draw without the
  pauses of the period and of the paused time that begins within the period
  is at least `exp (-count)` times the mean of: the function at no paused
  time, plus `count` times its mean over the length of one pause. Here
  `count` is the number of pauses that begin within the period on average.

The function may be any measurable function. It will be the cost that the
paused time of the period causes, as bounded from below by
`Builds.cell_stall_le`, together with the latency that the room costs. No
bound on a cost is proved here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {Ω : Type} [MeasurableSpace Ω]
  {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R}

/-- **The mean over what a link pauses within a period.** In a random world
of any member, for a link, a period from `a` to `b` with `0 ≤ a ≤ b`, a
measurable function `g` of the draw without the paused time of the link that
begins within the period, and a measurable function `Φ` of the value of `g`
and of that paused time: the mean of `Φ` is at least the mean, over the draw
without the pauses of the period, of `exp (-count)` times `Φ` at no paused
time plus `count` times the mean of `Φ` over the length of one pause, where
`count` is the number of pauses of the link that begin within the period on
average. -/
theorem Prior.lintegral_cell_ge (hD : m.Prior f P D) (hm : AEMeasurable D P) (i₀ j₀ : H)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {count : ℝ≥0}
    (hcount : count = Real.toNNReal (f.linkPauseRate i₀ j₀ * (b - a)))
    {g : Draw H R → Draw H R} (hg : Measurable g) {Φ : Draw H R × ℝ → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(count : ℝ)))
        * (Φ (g ((D ω).linkOutside i₀ j₀ a b), 0)
          + ENNReal.ofReal count * ∫⁻ x in {x : ℝ | x ≠ 0},
              Φ (g ((D ω).linkOutside i₀ j₀ a b), x) ∂(f.linkPauseLength i₀ j₀)) ∂P
      ≤ ∫⁻ ω, Φ (g ((D ω).linkOutside i₀ j₀ a b),
          (D ω).linkPaused i₀ j₀ b - (D ω).linkPaused i₀ j₀ a) ∂P := by
  have := hD.prob
  have := f.linkPauseLength_prob i₀ j₀
  have hlaw := hD.linkPaused_law i₀ j₀ a b hab
  rw [← hcount] at hlaw
  have hE : AEMeasurable (fun ω => g ((D ω).linkOutside i₀ j₀ a b)) P :=
    hg.comp_aemeasurable ((measurable_linkOutside i₀ j₀ a b).comp_aemeasurable hm)
  have hind : IndepFun (fun ω => g ((D ω).linkOutside i₀ j₀ a b))
      (fun ω => (D ω).linkPaused i₀ j₀ b - (D ω).linkPaused i₀ j₀ a) P := by
    have h1 := ((hD.indepFun_linkOutside hm i₀ j₀ ha hab).comp
      (measurable_pi_apply b) hg).symm
    have e : ((fun x : Time → ℝ => x b)
          ∘ fun ω => pathWithin a b ((D ω).linkPaused i₀ j₀))
        = fun ω => (D ω).linkPaused i₀ j₀ b - (D ω).linkPaused i₀ j₀ a :=
      funext fun ω => pathWithin_of_ge hab _ le_rfl
    rw [e] at h1
    exact h1
  rw [lintegral_prodMk_of_indepFun hE hlaw.aemeasurable hind hΦ, hlaw.map_eq]
  exact lintegral_mono fun ω =>
    lintegral_pauseLaw_ge count (f.linkPauseLength i₀ j₀)
      fun x => Φ (g ((D ω).linkOutside i₀ j₀ a b), x)

/-! ## One cell, with the clocks of a fixed outcome -/

omit [DecidableEq H] in
/-- The first capture block handed over at or after a true time depends only
on the capture device. -/
theorem blockFrom_congr {w w' : World H R} (h : w'.source = w.source) (T : Time) :
    w'.blockFrom T = w.blockFrom T := by
  unfold World.blockFrom
  rw [h]

/-- A draw whose link does not pause within the period is the draw without
the pauses of the period. -/
theorem Draw.linkOutside_eq_self (d : Draw H R) (i₀ j₀ : H) {a b : ℝ} (hab : a ≤ b)
    (hmono : Monotone (d.linkPaused i₀ j₀))
    (h : d.linkPaused i₀ j₀ b = d.linkPaused i₀ j₀ a) : d.linkOutside i₀ j₀ a b = d := by
  have e : pathWithin a b (d.linkPaused i₀ j₀) = 0 :=
    funext fun t => pathWithin_eq_zero hab hmono h t
  have h1 := d.linkOutside_addLink i₀ j₀ a b
  rw [e, Draw.addLink_zero] at h1
  exact h1

/-- The draw `d₁` with the pauses of the draw `e`, except the paused time of
the link from the sender to the host of speaker `r` that begins in cell `j`,
from `j * ℓ` to `(j + 1) * ℓ`. -/
def frameOutside (m : GenerativeWorld H R) (d₁ e : Draw H R) (r : Fin R) (ℓ : ℝ) (j : ℕ) :
    Draw H R :=
  d₁.withPaused (e.linkOutside m.sender (m.host r) ((j : ℝ) * ℓ) (((j : ℝ) + 1) * ℓ))

/-- The paused time of the link from the sender to the host of speaker `r`
that begins in cell `j`, in the draw `e`. -/
def cellIncrement (m : GenerativeWorld H R) (e : Draw H R) (r : Fin R) (ℓ : ℝ) (j : ℕ) : ℝ :=
  e.linkPaused m.sender (m.host r) (((j : ℝ) + 1) * ℓ)
    - e.linkPaused m.sender (m.host r) ((j : ℝ) * ℓ)

open Classical in
/-- **The mean cost of one cell, with the clocks of a fixed outcome.** Fix a
draw `d₁` with its world `w₁`: they give the clocks, the audio devices and
the least delays. Take a random world of the member for the pauses, and for
every outcome `ω` the world `w ω` built from `d₁` with the pauses of the
outcome, and the world `wOut ω` built from `d₁` with those pauses except the
paused time of the link from the sender to the host of speaker `r` that
begins in cell `j` (`frameOutside`). Consider a solution whose hosts
exchange messages only with the sender, whose position at speaker `r`
advances by at least `s`, with `0 ≤ s ≤ 1`, in every step of continuous
playback, in almost every world `w ω`, and whose playback in the worlds
`wOut ω` is described by measurable sets `S k` and measurable functions
`G k` of the draw. Let no playback block be requested between `j * ℓ + δ`
and `(j + 1) * ℓ + δ`, where `δ` is the least delay of the link, and let
`β₀` be the first block requested at or after `(j + 1) * ℓ + δ`.

Let `φ` be a measurable function of the room, `w'` a weight, and `SC` a
measurable set of draws. Then the mean of `φ` of the room before block `β₀`
in the world `w ω` (zero if negative), plus `w'` times the missed samples
and `s` times the discontinuities of the window of the cell, counted up to
`s * Nbar * blockSize`, where the draw without the pauses of the cell is in
`SC`, is at least `exp (-count)` times
the mean of: where that draw is in `SC`, the least over the rooms `ρ ≥ 0`
of `φ ρ` plus `count` times the mean over the length `x` of one pause of
`w'` times what such a pause costs at least with the room `ρ`; elsewhere,
the least of `φ`. Here `count` is the number of pauses of the link that
begin in the cell on average. -/
theorem Prior.cell_mean_ge {Msg : Type} (hD : m.Prior f P D) (hm : AEMeasurable D P)
    {d₁ : Draw H R} {w₁ : World H R} (hB₁ : m.Builds f d₁ w₁)
    (hpos₁ : ∀ i j, 0 ≤ d₁.split i j * f.roundTrip i j) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R} (hr : m.host r ≠ m.sender)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (j : ℕ) {Xmax : ℝ} {Nbar : ℕ}
    {w wOut : Ω → World H R} (hw : ∀ ω, m.Builds f (d₁.withPaused (D ω)) (w ω))
    (hOut : ∀ ω, m.Builds f (frameOutside m d₁ (D ω) r ℓ j) (wOut ω))
    (hslow : ∀ᵐ ω ∂P, ∀ k x y, σ.plays (w ω) lookahead r k = some x →
      σ.plays (w ω) lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {S : ℕ → Set (Draw H R)} {G : ℕ → Draw H R → ℝ} (hS : ∀ k, MeasurableSet (S k))
    (hG : ∀ k, Measurable (G k))
    (hdesc : ∀ k, ∀ᵐ ω ∂P, ∀ x : ℝ, σ.plays (wOut ω) lookahead r k = some x ↔
      frameOutside m d₁ (D ω) r ℓ j ∈ S k ∧ G k (frameOutside m d₁ (D ω) r ℓ j) = x)
    {δ : ℝ} (hδ : δ = d₁.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    {β₀ : ℕ} (hβ₀ : β₀ = firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ))
    (husable : ∀ b' < β₀, (w₁.speaker r).asked b' < (j : ℝ) * ℓ + δ) {top : ℝ}
    (htop : top = (w₁.blockFrom ((w₁.speaker r).asked β₀ - δ) : ℝ) * m.blockSize
      - ((lookahead : ℕ) : ℝ))
    {count : ℝ≥0}
    (hcount : count = Real.toNNReal
      (f.linkPauseRate m.sender (m.host r) * (((j : ℝ) + 1) * ℓ - (j : ℝ) * ℓ)))
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (w' : ℝ≥0∞) {SC : Set (Draw H R)}
    (hSC : MeasurableSet SC) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(count : ℝ)))
        * (if frameOutside m d₁ (D ω) r ℓ j ∈ SC then
            ⨅ ρ : {ρ : ℝ // 0 ≤ ρ}, φ ρ + ENNReal.ofReal count
              * ∫⁻ x in {x : ℝ | x ≠ 0}, w' * ENNReal.ofReal
                  (s * ((windowCount (w₁.speaker r).asked ℓ δ Xmax Nbar j x : ℝ)
                    * m.blockSize) - ρ - s) ∂(f.linkPauseLength m.sender (m.host r))
          else ⨅ ρ : {ρ : ℝ // 0 ≤ ρ}, φ ρ) ∂P
      ≤ ∫⁻ ω, (φ (max (room m f (d₁.withPaused (D ω)) (w ω) lookahead
            (σ.plays (w ω) lookahead r) r β₀) 0)
          + (if frameOutside m d₁ (D ω) r ℓ j ∈ SC then
              w' * ENNReal.ofReal
                (min (∑ k ∈ cellSamples (w₁.speaker r).asked ℓ δ Xmax Nbar m.blockSize j
                    (cellIncrement m (D ω) r ℓ j),
                  ((missedAt (σ.plays (w ω) lookahead r) k : ℝ)
                    + s * (discontinuityAt (σ.plays (w ω) lookahead r) k : ℝ)))
                  (s * ((Nbar : ℝ) * m.blockSize)))
            else 0)) ∂P := by
  have := hD.prob
  have := f.linkPauseLength_prob m.sender (m.host r)
  unfold frameOutside at hOut hdesc ⊢
  unfold cellIncrement
  have ha : (0 : ℝ) ≤ (j : ℝ) * ℓ := mul_nonneg (Nat.cast_nonneg j) hℓ
  have hab : (j : ℝ) * ℓ ≤ ((j : ℝ) + 1) * ℓ := by nlinarith
  have hne : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton (0 : ℝ)).compl
  have hg : Measurable fun e : Draw H R => d₁.withPaused e :=
    measurable_withPaused.comp (measurable_const.prodMk measurable_id)
  -- The room, as a function of the draw without the pauses of the cell.
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Draw H R → ℝ, ρ = fun e =>
      max (top - (lastPlayed (describedPlays S G e) (β₀ * m.blockSize)).getD 0) 0 := ⟨_, rfl⟩
  have hρ : Measurable ρ := by
    rw [hρdef]
    exact (measurable_const.sub (measurable_getD_lastPlayed hS hG _)).max measurable_const
  have hρ0 : ∀ e, 0 ≤ ρ e := fun e => by
    rw [hρdef]
    exact le_max_right _ _
  have hn : Measurable fun x : ℝ =>
      ((windowCount (w₁.speaker r).asked ℓ δ Xmax Nbar j x : ℕ) : ℝ) :=
    measurable_from_nat.comp
      (Monotone.measurable fun x y hxy => windowCount_mono _ ℓ δ Xmax Nbar j hxy)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Draw H R × ℝ → ℝ≥0∞, Φ = fun q =>
      (if q.2 = 0 then φ (ρ q.1) else 0)
        + (if q.1 ∈ SC then w' * ENNReal.ofReal
            (s * ((windowCount (w₁.speaker r).asked ℓ δ Xmax Nbar j q.2 : ℝ) * m.blockSize)
              - ρ q.1 - s) else 0) := ⟨_, rfl⟩
  have hΦapp : ∀ (e : Draw H R) (x : ℝ), Φ (e, x)
      = (if x = 0 then φ (ρ e) else 0)
        + (if e ∈ SC then w' * ENNReal.ofReal
            (s * ((windowCount (w₁.speaker r).asked ℓ δ Xmax Nbar j x : ℝ) * m.blockSize)
              - ρ e - s) else 0) := fun e x => by rw [hΦdef]
  have hΦ : Measurable Φ := by
    rw [hΦdef]
    refine Measurable.add ?_ ?_
    · exact Measurable.ite (measurable_snd (measurableSet_singleton (0 : ℝ)))
        ((hφ.comp hρ).comp measurable_fst) measurable_const
    · refine Measurable.ite (measurable_fst hSC) ?_ measurable_const
      refine measurable_const.mul (ENNReal.measurable_ofReal.comp ?_)
      exact ((measurable_const.mul ((hn.comp measurable_snd).mul measurable_const)).sub
        (hρ.comp measurable_fst)).sub measurable_const
  have key := hD.lintegral_cell_ge hm m.sender (m.host r) ha hab hcount hg hΦ
  refine le_trans (lintegral_mono fun ω => mul_le_mul' le_rfl ?_)
    (key.trans (lintegral_mono_ae ?_))
  · -- The level program of the cell is at most what the one-pause term gives.
    have h0 : φ (ρ (d₁.withPaused ((D ω).linkOutside m.sender (m.host r) ((j : ℝ) * ℓ)
          (((j : ℝ) + 1) * ℓ))))
        ≤ Φ (d₁.withPaused ((D ω).linkOutside m.sender (m.host r) ((j : ℝ) * ℓ)
          (((j : ℝ) + 1) * ℓ)), 0) := by
      rw [hΦapp, ite_eq_left rfl]
      exact le_self_add
    by_cases hC : d₁.withPaused ((D ω).linkOutside m.sender (m.host r) ((j : ℝ) * ℓ)
        (((j : ℝ) + 1) * ℓ)) ∈ SC
    · rw [ite_eq_left hC]
      refine (iInf_le _ ⟨ρ (d₁.withPaused ((D ω).linkOutside m.sender (m.host r)
        ((j : ℝ) * ℓ) (((j : ℝ) + 1) * ℓ))), hρ0 _⟩).trans ?_
      refine add_le_add h0 (mul_le_mul' le_rfl (setLIntegral_mono' hne fun x hx => ?_))
      rw [hΦapp, ite_eq_right hx, ite_eq_left hC, zero_add]
    · rw [ite_eq_right hC]
      exact (iInf_le _ ⟨ρ (d₁.withPaused ((D ω).linkOutside m.sender (m.host r)
        ((j : ℝ) * ℓ) (((j : ℝ) + 1) * ℓ))), hρ0 _⟩).trans (h0.trans le_self_add)
  · -- In almost every outcome, the cost of the cell is at least the function.
    filter_upwards [ae_all_iff.mpr hdesc, hslow] with ω hω hslowω
    have hpl : ∀ k, σ.plays (wOut ω) lookahead r k
        = describedPlays S G (d₁.withPaused ((D ω).linkOutside m.sender (m.host r)
          ((j : ℝ) * ℓ) (((j : ℝ) + 1) * ℓ))) k := fun k => eq_describedPlays (hω k)
    obtain ⟨-, -, -, hsrc, hspk, -⟩ := hB₁.same_devices (hOut ω) rfl rfl rfl rfl rfl rfl
    have hRout : max (room m f (d₁.withPaused ((D ω).linkOutside m.sender (m.host r)
          ((j : ℝ) * ℓ) (((j : ℝ) + 1) * ℓ))) (wOut ω) lookahead
          (σ.plays (wOut ω) lookahead r) r β₀) 0
        = ρ (d₁.withPaused ((D ω).linkOutside m.sender (m.host r) ((j : ℝ) * ℓ)
          (((j : ℝ) + 1) * ℓ))) := by
      have hlp := lastPlayed_congr (K := β₀ * m.blockSize) fun k _ => hpl k
      rw [hρdef]
      unfold room
      rw [hspk, blockFrom_congr hsrc, hlp, htop, hδ]
      rfl
    rw [hΦapp]
    refine add_le_add ?_ ?_
    · by_cases hI0 : (D ω).linkPaused m.sender (m.host r) (((j : ℝ) + 1) * ℓ)
          - (D ω).linkPaused m.sender (m.host r) ((j : ℝ) * ℓ) = 0
      · rw [ite_eq_left hI0]
        have hself := (D ω).linkOutside_eq_self m.sender (m.host r) hab
          (hD.linkPaused_monotone ω _ _) (sub_eq_zero.mp hI0)
        have hOutω := hOut ω
        rw [hself] at hOutω hRout
        have hww : w ω = wOut ω := (hw ω).unique hOutω
        rw [hself, hww, hRout]
      · rw [ite_eq_right hI0]
        exact bot_le
    · by_cases hC : d₁.withPaused ((D ω).linkOutside m.sender (m.host r) ((j : ℝ) * ℓ)
          (((j : ℝ) + 1) * ℓ)) ∈ SC
      · rw [ite_eq_left hC, ite_eq_left hC]
        refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (le_min ?_ ?_))
        have hsame : (d₁.withPaused ((D ω).linkOutside m.sender (m.host r) ((j : ℝ) * ℓ)
            (((j : ℝ) + 1) * ℓ))).SameExceptLinkFrom (d₁.withPaused (D ω)) m.sender
            (m.host r) ((j : ℝ) * ℓ) :=
          (d₁.withPaused (D ω)).sameExcept_linkOutside m.sender (m.host r) hab
        have hstall := (hOut ω).cell_stall_le (hw ω) hℓ hsame hpos₁
          (fun i j' => hD.linkPaused_monotone ω i j') (fun x => hD.hostPaused_monotone ω x)
          σ hstar lookahead hr hs0 hs1 hslowω (Xmax := Xmax) (Nbar := Nbar) (δ := δ)
          (I := (D ω).linkPaused m.sender (m.host r) (((j : ℝ) + 1) * ℓ)
            - (D ω).linkPaused m.sender (m.host r) ((j : ℝ) * ℓ)) hδ rfl
          (by
            rw [hspk, ← hβ₀]
            exact husable)
        rw [hspk, ← hβ₀, hRout] at hstall
        exact hstall
        have h1 : ((windowCount (w₁.speaker r).asked ℓ δ Xmax Nbar j
            ((D ω).linkPaused m.sender (m.host r) (((j : ℝ) + 1) * ℓ)
              - (D ω).linkPaused m.sender (m.host r) ((j : ℝ) * ℓ)) : ℕ) : ℝ)
            ≤ (Nbar : ℝ) := by
          exact_mod_cast windowCount_le _ ℓ δ Xmax Nbar j _
        have h2 := hρ0 (d₁.withPaused ((D ω).linkOutside m.sender (m.host r)
          ((j : ℝ) * ℓ) (((j : ℝ) + 1) * ℓ)))
        have h3 : (0 : ℝ) ≤ (m.blockSize : ℝ) := Nat.cast_nonneg _
        have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h3) hs0
        linarith
      · rw [ite_eq_right hC, ite_eq_right hC]

end Unisono.Spec.GenerativeWorld
