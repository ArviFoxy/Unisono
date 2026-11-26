/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ProposedResample

/-!
# The world of a draw whose links do something else

A world built from a draw of `Unisono.Spec.ProposedWorld` keeps its clocks
and its audio devices when what the links do is replaced: only its network
changes.

* `Draw.Shaped.lt_reaches`, `Draw.Shaped.reaches_le_observed`,
  `Draw.Shaped.reach_mem`: for a draw with the properties that the prior
  asks of every outcome, a message reaches the receiving host after it is
  sent, and the program handles it at that moment or later.
* `relinked`: a world with the network that a draw gives.
* `Builds.relinked`: if `w` is the world built from `d`, then `w` with the
  network of `d.withLinks e` is the world built from `d.withLinks e`.
* `expectedCost_resampleLinks`: the expected cost of a solution whose cost
  is a measurable function of what is drawn is the mean, over a first
  outcome, of its mean cost over a second outcome, in the worlds built from
  the draw of the first outcome with what the links do in the second.

For a fixed first outcome the clocks, the pauses of the hosts and the audio
devices are numbers, and only what the links do is random. No bound on a
cost is proved here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open GenerativeWorld (backlog)

variable {H : Type} {R : ℕ}

namespace Draw.Shaped

variable {d : Draw H R} (f : Member H R) (hd : d.Shaped)
include hd

/-- A message reaches the receiving host after it is sent. -/
theorem lt_reaches (i j : H) (s : Time) : s < d.reaches f i j s := by
  have h1 := backlog_nonneg (d.hostPaused i) s
  have h2 := backlog_nonneg (d.linkPaused i j) (d.leaves i s)
  have h3 : 0 < d.split i j * f.roundTrip i j :=
    mul_pos (hd.split_mem i j).1 (f.roundTrip_pos i j)
  have h4 : 0 ≤ d.jitter i j (d.released i j s) := hd.jitterLevel_nonneg i j _
  unfold Draw.reaches Draw.released Draw.leaves at *
  linarith

omit hd in
/-- The program of the receiving host handles a message when it reaches the
host, or later. -/
theorem reaches_le_observed (d : Draw H R) (i j : H) (s : Time) :
    d.reaches f i j s ≤ d.observed f i j s := by
  have := backlog_nonneg (d.hostPaused j) (d.reaches f i j s)
  unfold Draw.observed
  linarith

theorem reach_mem (i j : H) (s : Time) (q : ℕ) (a : Time)
    (h : d.delivery f i j s q = some a) :
    s < d.reaches f i j s ∧ d.reaches f i j s ≤ a := by
  classical
  unfold Draw.delivery at h
  split_ifs at h with hl
  have ha : d.observed f i j s = a := Option.some.inj h
  rw [← ha]
  exact ⟨hd.lt_reaches f i j s, reaches_le_observed f d i j s⟩

end Draw.Shaped

/-- **A world with the network that a draw gives.** Its clocks and audio
devices are those of `w`. -/
def relinked (f : Member H R) (d : Draw H R) (hd : d.Shaped) (w : World H R) : World H R :=
  { w with
    network :=
      { deliver := d.delivery f
        reach := fun i j s _ => d.reaches f i j s
        reach_mem := hd.reach_mem f } }

variable {m : Told H R} {f : Member H R}

/-- **Replacing what the links do keeps the clocks and the audio devices.**
If `w` is the world built from the draw `d`, then `w` with the network of the
draw `d.withLinks e` is the world built from `d.withLinks e`. -/
theorem Builds.relinked {d e : Draw H R} {w : World H R} (hB : Builds m f d w)
    (hs : (d.withLinks e).Shaped) :
    Builds m f (d.withLinks e) (relinked f (d.withLinks e) hs w) where
  rate_eq := hB.rate_eq
  sender_eq := hB.sender_eq
  host_eq := hB.host_eq
  clock := hB.clock
  capture_start := hB.capture_start
  capture := hB.capture
  capture_first := hB.capture_first
  capture_handed := hB.capture_handed
  capture_reported := hB.capture_reported
  speaker_start := hB.speaker_start
  speaker_out := hB.speaker_out
  speaker_first := hB.speaker_first
  speaker_asked := hB.speaker_asked
  speaker_reported := hB.speaker_reported
  target_eq := hB.target_eq
  deliver := fun _ _ _ _ => rfl
  reach := fun _ _ _ _ => rfl

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → Draw H R}

/-- **The expected cost is a mean over the clocks and the pauses of the
hosts of a mean over what the links do.** Take a solution whose cost is a
measurable function of what is drawn, a random world of the member, and for
every pair of outcomes a world built from the draw of the first outcome with
what the links do in the second. The expected cost of the solution is the
mean, over the first outcome, of its mean cost over the second outcome in
those worlds. -/
theorem expectedCost_resampleLinks [DecidableEq H] [Countable H] {Msg : Type}
    {lookahead : ℕ+} {c : Weights} {τ : Solution H R Msg}
    (hτ : measurableCost m f lookahead c Msg τ) (hD : Prior m f P D)
    {world : Ω → World H R} (hB : ∀ ω, Builds m f (D ω) (world ω))
    {world₂ : Ω × Ω → World H R}
    (hB₂ : ∀ ω, Builds m f (resampleLinks D ω) (world₂ ω)) :
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

end Unisono.Spec.ProposedWorld
