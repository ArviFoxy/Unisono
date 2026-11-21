/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.World

/-!
# A model of the world: worlds within bounds

A model of the world says which worlds can happen, and, when the world is
random, how likely each is. `Unisono.Spec.World` only says what one world
is; a result about the problem or about a solution holds under a model, and
the same solution can do differently under different models. Each model is
a file of its own in `Unisono/Spec/Models`.

This model bounds the clocks, the devices and the network, with no law of
chance: a result under it holds for every world within the bounds, the worst
case. A random world can be required to be within bounds almost surely
(`AlmostSurelyWithin`). Models with laws of chance, for the delays, the
losses and the wandering of the clocks, are added where a result needs
them.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ}

/-- A clock runs at true time's rate within the fraction `ε`: over any
interval it advances by the interval's length within `ε` of it. -/
def Clock.RateWithin (c : Clock) (ε : ℝ) : Prop :=
  ∀ s t, s ≤ t → |c.read t - c.read s - (t - s)| ≤ ε * (t - s)

/-- The capture device runs at the nominal rate `rate` within the fraction
`ε`: the time between two frames is `1 / rate` within `ε / rate`. -/
def CaptureDevice.RateWithin (d : CaptureDevice) (rate ε : ℝ) : Prop :=
  ∀ n, |d.capture (n + 1) - d.capture n - 1 / rate| ≤ ε / rate

/-- A playback device runs at the nominal rate `rate` within the fraction
`ε`. -/
def PlaybackDevice.RateWithin (d : PlaybackDevice) (rate ε : ℝ) : Prop :=
  ∀ k, |d.out (k + 1) - d.out k - 1 / rate| ≤ ε / rate

/-- A playback device asks for each block at least `lead` seconds before the
block's first output sample leaves. -/
def PlaybackDevice.LeadAtLeast (d : PlaybackDevice) (lead : ℝ) : Prop :=
  ∀ b, lead ≤ d.out (d.first b) - d.asked b

/-- The messages from host `i` to host `j` that arrive take between `least`
and `most` seconds. -/
def Network.DelaysWithin (net : Network H) (i j : H) (least most : ℝ) : Prop :=
  ∀ s q a, net.deliver i j s q = some a → least ≤ a - s ∧ a - s ≤ most

/-- Bounds that define a class of worlds. -/
structure Bounds (H : Type) where
  /-- How far a host's clock may run from true time's rate, as a fraction. -/
  clockRate : ℝ
  /-- How far a device may run from the nominal rate, as a fraction. -/
  deviceRate : ℝ
  /-- How far a device's report of a time may be from its host's clock at
  that time, in seconds. -/
  report : ℝ
  /-- The least time before a block's first output sample leaves that a
  playback device asks for the block, in seconds. -/
  lead : ℝ
  /-- The least and the most time that a message from one host to another
  takes, in seconds. -/
  delayLeast : H → H → ℝ
  delayMost : H → H → ℝ

/-- A world within bounds. -/
def World.WithinBounds (w : World H R) (B : Bounds H) : Prop :=
  (∀ h, (w.clock h).RateWithin B.clockRate)
    ∧ w.source.RateWithin w.rate B.deviceRate
    ∧ (∀ r, (w.speaker r).RateWithin w.rate B.deviceRate)
    ∧ (∀ n, |w.source.reported n - (w.clock w.sender).read (w.source.capture n)| ≤ B.report)
    ∧ (∀ r k, |(w.speaker r).reported k - (w.clock (w.host r)).read ((w.speaker r).out k)|
        ≤ B.report)
    ∧ (∀ r, (w.speaker r).LeadAtLeast B.lead)
    ∧ (∀ i j, w.network.DelaysWithin i j (B.delayLeast i j) (B.delayMost i j))

/-- A random world, `world ω` with `ω` drawn from `P`, is almost surely
within bounds. -/
def AlmostSurelyWithin {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (world : Ω → World H R) (B : Bounds H) : Prop :=
  ∀ᵐ ω ∂P, (world ω).WithinBounds B

end Unisono.Spec
