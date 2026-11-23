/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.Bounded
public import Unisono.Spec.Models.Delays
public import Unisono.Spec.Models.SecondOrder

/-!
# Composite stochastic world model class

`StochasticWorld` is the full-world probabilistic model class obtained by
combining:

1. `StationaryNetworkDisturbances`: per-link slow baseline, exponential-tail
   per-packet jitter, pauses, outages, individual packet drops, and joint
   stationarity and mixing.
2. `SecondOrderMoments`: IEEE 1139 band-limited power-law host clock and audio
   device spectra, correlated TX/RX plus uncorrelated per-packet link jitter
   decomposition, and white device timestamp errors.
3. Deterministic device/blocking bounds (`handoff`, `leadLeast`/`leadMost`,
   `blockLeast`/`blockMost`) so that playback requests and capture handoffs
   occur on well-behaved block schedules across every realization.

`StochasticWorld` is a *model class* (a set of structural and distributional
constraints satisfied by many probability distributions over `World`), not a
single generative law. End-to-end probabilistic theorems in `Unisono.Spec`
state their assumptions in terms of this model class (or its component classes
`StationaryNetworkDisturbances` and `SecondOrderMoments`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory

/-- Parameters of the composite full-world stochastic model class for hosts
`H` and `R` speakers. -/
structure StochasticWorld (H : Type) (R : ℕ) where
  /-- Network delay, pause, outage, and loss disturbances (per directed link). -/
  network : StationaryNetworkDisturbances H
  /-- First and second moments of clocks, link jitter, audio devices, and
  device timestamp errors. -/
  moments : SecondOrderMoments H R
  /-- Longest time from capture of a block's last frame to its handoff, in seconds. -/
  handoff : ℝ
  handoff_nonneg : 0 ≤ handoff
  /-- Shortest and longest playback request lead, in seconds. -/
  leadLeast : ℝ
  leadMost : ℝ
  leadLeast_pos : 0 < leadLeast
  leadLeast_le : leadLeast ≤ leadMost
  /-- Minimum and maximum frames/samples per capture or playback block. -/
  blockLeast : ℕ
  blockMost : ℕ
  blockLeast_pos : 0 < blockLeast
  blockLeast_le : blockLeast ≤ blockMost

/-- A random world `world : Ω → World H R` under measure `P` belongs to the
composite stochastic world model class `m`:

* There exists a link decomposition `d : Ω → H → H → Link` simultaneously
  satisfying `m.network.Holds P d` and `m.moments.Holds P world d` (which in
  particular requires `IsProbabilityMeasure P` and `(world ω).HasDelays (d ω)`).
* Every realization satisfies the deterministic handoff, request-lead, and
  block-size bounds. -/
structure StochasticWorld.Holds {H : Type} {R : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (m : StochasticWorld H R) (P : Measure Ω) (world : Ω → World H R) : Prop where
  /-- Underlying per-link delay decomposition shared by the network
  disturbance and second-order moment constraints. -/
  links : ∃ d : Ω → H → H → Link, m.network.Holds P d ∧ m.moments.Holds P world d
  /-- Capture handoff delay bound across all realizations. -/
  handoff : ∀ ω, (world ω).source.HandoffWithin m.handoff
  /-- Playback request lead bounds across all realizations. -/
  lead : ∀ ω r, ((world ω).speaker r).LeadWithin m.leadLeast m.leadMost
  /-- Capture block size bounds across all realizations. -/
  capture_blocks : ∀ ω, (world ω).source.BlocksWithin m.blockLeast m.blockMost
  /-- Playback block size bounds across all realizations. -/
  playback_blocks : ∀ ω r, ((world ω).speaker r).BlocksWithin m.blockLeast m.blockMost

/-- Any random world satisfying `StochasticWorld.Holds` in particular satisfies
`StationaryNetworkDisturbances.Random`. -/
theorem StochasticWorld.Holds.network_random {H : Type} {R : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {m : StochasticWorld H R} {P : Measure Ω} {world : Ω → World H R}
    (h : m.Holds P world) : m.network.Random P world := by
  obtain ⟨d, hnet, hmom⟩ := h.links
  exact ⟨hmom.prob, d, hmom.network, hnet⟩

end Unisono.Spec
