/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Undelayed
public import Unisono.Spec.Models.GenerativeLate

/-!
# How often a capture block is late

The message of a capture block to the host of a speaker is slow, at a level
`L`, when it takes longer than the least margin of the speaker
(`marginLeast`). This file proves that, in every random world of a member
with steady clocks, the long-run fraction of slow capture blocks is, in
almost every outcome, the probability `lateProbability` of the member for the
least delay and the least margin of the outcome.

* `blockDelay_eq_arrivalM`: how long the message of a capture block takes,
  from the measurable form of the arrival.
* `blockTimes`: the least delay to the host of a speaker, the least margin of
  the speaker, the true time at which the first capture block is handed over
  and the time between two handovers, as a function of the numbers of a
  draw. It is measurable (`measurable_blockTimes`).
* `ae_tendsto_slowBlocks`: the theorem. The capture device hands over its
  blocks at equally spaced true times that depend on the clocks, and the
  clocks are independent of the pauses
  (`GenerativeWorld.Prior.ae_lateFraction_scalars`).

The late rate of the controller counts output samples, of which each capture
block serves several. It is not derived here.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R}

/-- In a random world, the paused time of every link and host never
decreases. -/
theorem prior_paused_monotone {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} (hD : m.Prior f P D) (ω : Ω) (x : PauseIndex H) :
    Monotone ((D ω).paused x) := by
  rcases x with ij | h
  · exact hD.linkPaused_monotone ω _ _
  · exact hD.hostPaused_monotone ω h

/-- In a random world, the paused time of every link and host is continuous
from the right. -/
theorem prior_paused_rightContinuous {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} (hD : m.Prior f P D) (ω : Ω) (x : PauseIndex H) (t : ℝ) :
    ContinuousWithinAt ((D ω).paused x) (Set.Ici t) t := by
  rcases x with ij | h
  · exact hD.linkPaused_rightContinuous ω _ _ t
  · exact hD.hostPaused_rightContinuous ω h t

/-- How long the message of a capture block takes, from the measurable form
of the arrival. -/
theorem blockDelay_eq_arrivalM {d : Draw H R} {w : World H R} (hB : m.Builds f d w)
    (hmono : ∀ x, Monotone (d.paused x))
    (hright : ∀ x t, ContinuousWithinAt (d.paused x) (Set.Ici t) t) (r : Fin R) (c : ℕ) :
    blockDelay m f d w r c
      = arrivalM d.paused m.sender (m.host r)
          (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) (w.source.handed c)
        - w.source.handed c := by
  unfold blockDelay
  rw [hB.arrival_eq_arrivalM hmono hright]

/-- The least delay to the host of speaker `r`, the least margin of the
speaker at the level `L`, the true time at which the first capture block is
handed over, and the time between two handovers, from the numbers `u` of a
draw. The pair of the sender's host and the speaker's host is `z`, and `u`
gives the share of the direction from the sender. -/
def blockTimes (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+) (L : ℝ) (r : Fin R)
    (z : {z : Sym2 H // ¬ z.IsDiag}) (u : ScalarIndex H R → ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (u (.inl z) * f.roundTrip m.sender (m.host r),
    L / Real.exp (u (.inr (.inr (.inl m.sender))))
      + (u (.inl z) * f.roundTrip m.sender (m.host r)
        - (1 - u (.inl z)) * f.roundTrip (m.host r) m.sender) / 2
      - m.lead / Real.exp (u (.inr (.inr (.inr (some (m.device r))))))
      - ((m.blockSize : ℝ) - 1)
        / (m.rate * Real.exp (u (.inr (.inr (.inr (some (m.device r)))))))
      - (((lookahead : ℕ) : ℝ) + (m.blockSize : ℝ) - 1)
        / (m.rate * Real.exp (u (.inr (.inr (.inr none))))),
    (f.captureStart - u (.inr (.inl m.sender))) / Real.exp (u (.inr (.inr (.inl m.sender))))
      + ((m.blockSize : ℝ) - 1) / (m.rate * Real.exp (u (.inr (.inr (.inr none))))),
    (m.blockSize : ℝ) / (m.rate * Real.exp (u (.inr (.inr (.inr none))))))

theorem measurable_blockTimes (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+)
    (L : ℝ) (r : Fin R) (z : {z : Sym2 H // ¬ z.IsDiag}) :
    Measurable (blockTimes m f lookahead L r z) := by
  unfold blockTimes
  fun_prop

/-- `blockTimes` at the numbers of a draw, when the pair of the sender's
host and the speaker's host is taken in that order. -/
theorem blockTimes_scalars (lookahead : ℕ+) (L : ℝ) (r : Fin R) {d : Draw H R}
    {o : Orientation H} {z : {z : Sym2 H // ¬ z.IsDiag}}
    (ho : (o z).1 = (m.sender, m.host r))
    (hswap : d.split (m.host r) m.sender = 1 - d.split m.sender (m.host r)) :
    blockTimes m f lookahead L r z (d.scalars o)
      = (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r),
        marginLeast m f d lookahead L r,
        (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender)
          + ((m.blockSize : ℝ) - 1) / (m.rate * Real.exp (d.deviceLogRate none)),
        (m.blockSize : ℝ) / (m.rate * Real.exp (d.deviceLogRate none))) := by
  have hs : d.scalars o (.inl z) = d.split m.sender (m.host r) := by
    show d.split (o z).1.1 (o z).1.2 = _
    rw [ho]
  unfold blockTimes marginLeast latencyOf
  rw [hs, hswap]
  rfl

/-- **The long-run fraction of slow capture blocks is a probability of the
member.** In every random world of a member with steady clocks, consider a
speaker `r` whose host is not the sender's, and the level `L`. In almost
every outcome, the fraction of the first `n` capture blocks whose message to
the speaker's host takes longer than the least margin of the speaker
converges to `lateProbability`, for the least delay from the sender to the
speaker's host and the least margin of the outcome. -/
theorem ae_tendsto_slowBlocks [Fintype H] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D) (hf : f.SteadyClocks)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) (L : ℝ) (r : Fin R)
    (hnos : m.host r ≠ m.sender) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ c ∈ Finset.range n,
        if marginLeast m f (D ω) lookahead L r < blockDelay m f (D ω) (world ω) r c
        then (1 : ℝ) else 0) atTop
      (𝓝 (lateProbability f m.sender (m.host r)
        ((D ω).split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
        (marginLeast m f (D ω) lookahead L r))) := by
  classical
  obtain ⟨o, ho⟩ : ∃ o : Orientation H,
      (o (pairOf m.sender (m.host r) hnos.symm)).1 = (m.sender, m.host r) :=
    ⟨Function.update (refOrientation H) (pairOf m.sender (m.host r) hnos.symm)
      ⟨(m.sender, m.host r), rfl⟩, by rw [Function.update_self]⟩
  have h1 := hD.ae_lateFraction_scalars o m.sender (m.host r)
    (measurable_blockTimes m f lookahead L r (pairOf m.sender (m.host r) hnos.symm))
  filter_upwards [h1, hD.ae_constantRates hf hB] with ω hω hS
  have hswap : (D ω).split (m.host r) m.sender = 1 - (D ω).split m.sender (m.host r) := by
    have := hD.split_swap ω m.sender (m.host r)
    linarith
  have hΘ := blockTimes_scalars (f := f) lookahead L r ho hswap
  simp only [hΘ] at hω
  have hc : 0 < m.rate * Real.exp ((D ω).deviceLogRate none) :=
    mul_pos m.rate_pos (Real.exp_pos _)
  have hℓ : 0 < (m.blockSize : ℝ) / (m.rate * Real.exp ((D ω).deviceLogRate none)) :=
    div_pos (Nat.cast_pos.mpr m.blockSize_pos) hc
  refine (hω hℓ).congr fun n => ?_
  unfold lateFraction
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have hhand : (f.captureStart - (D ω).offset m.sender) / Real.exp ((D ω).logRate m.sender)
        + ((m.blockSize : ℝ) - 1) / (m.rate * Real.exp ((D ω).deviceLogRate none))
        + (c : ℝ) * ((m.blockSize : ℝ) / (m.rate * Real.exp ((D ω).deviceLogRate none)))
      = (world ω).source.handed c := by
    rw [hS.handed c]
    field_simp
    ring
  rw [hhand, ← blockDelay_eq_arrivalM (hB ω) (prior_paused_monotone hD ω)
    (prior_paused_rightContinuous hD ω) r c]

end Unisono.Solutions.Controller
