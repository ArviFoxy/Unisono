/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.World
public import Mathlib.Tactic.Linarith

/-!
# A deterministic model of the world: worlds within bounds

A model of the world says which worlds can happen and, when the world is
random, with which probabilities. `Unisono.Spec.World` only defines what one
world is; a statement about the problem or about a solution holds under a
model, and the same solution can perform differently under different models. Each
model is a file of its own in `Unisono/Spec/Models`.

This model is deterministic: it bounds the clocks, the devices and the
network, and a statement under it holds for every world within the bounds,
the worst case. The bounds include everything an upper bound on latency or
on missed samples needs: how many consecutive messages the network may drop,
how late a capture device may hand over a block, how early a playback
device may request one, and how large a block may be. A random world can be
required to be within bounds almost surely (`AlmostSurelyWithin`).

Two facts about clocks within bounds: an NTP-style estimate of the
difference of two clocks errs by at most half the largest difference of the
two delays, plus the clocks' rate error times the mean delay
(`offset_error`), and the difference of two clocks drifts by at most twice
their rate error per second (`offset_drift`).
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

/-- The capture device's timestamps are within `ε` seconds of its host's
clock: for each block, of the clock's reading when the block's first frame
is captured. -/
def CaptureDevice.ReportsWithin (d : CaptureDevice) (clock : Clock) (ε : ℝ) : Prop :=
  ∀ b, |d.reported b - clock.read (d.capture (d.first b))| ≤ ε

/-- A playback device's timestamps are within `ε` seconds of its host's
clock: for each block, of the clock's reading when the block's first output
sample leaves. -/
def PlaybackDevice.ReportsWithin (d : PlaybackDevice) (clock : Clock) (ε : ℝ) : Prop :=
  ∀ b, |d.reported b - clock.read (d.out (d.first b))| ≤ ε

/-- The capture device hands over each block at most `most` seconds after
the block's last frame is captured. -/
def CaptureDevice.HandoffWithin (d : CaptureDevice) (most : ℝ) : Prop :=
  ∀ b, d.handed b - d.capture (d.first (b + 1) - 1) ≤ most

/-- A playback device requests each block between `least` and `most` seconds
before the block's first output sample leaves. -/
def PlaybackDevice.LeadWithin (d : PlaybackDevice) (least most : ℝ) : Prop :=
  ∀ b, least ≤ d.out (d.first b) - d.asked b ∧ d.out (d.first b) - d.asked b ≤ most

/-- Every block of the capture device holds at most `most` frames. -/
def CaptureDevice.BlocksAtMost (d : CaptureDevice) (most : ℕ) : Prop :=
  ∀ b, d.first (b + 1) - d.first b ≤ most

/-- Every block of a playback device holds at most `most` output samples. -/
def PlaybackDevice.BlocksAtMost (d : PlaybackDevice) (most : ℕ) : Prop :=
  ∀ b, d.first (b + 1) - d.first b ≤ most

/-- The messages from host `i` to host `j` that arrive take between `least`
and `most` seconds. -/
def Network.DelaysWithin (net : Network H) (i j : H) (least most : ℝ) : Prop :=
  ∀ s q a, net.deliver i j s q = some a → least ≤ a - s ∧ a - s ≤ most

/-- Of any `m + 1` consecutive messages from host `i` to host `j`, at least
one arrives, whenever they are sent: `send k` is when message `q + k` is
sent. -/
def Network.LossesWithin (net : Network H) (i j : H) (m : ℕ) : Prop :=
  ∀ (q : ℕ) (send : ℕ → Time), ∃ k ≤ m, (net.deliver i j (send k) (q + k)).isSome

/-- Bounds that define a class of worlds. -/
structure Bounds (H : Type) where
  /-- How far a host's clock may run from true time's rate, as a fraction. -/
  clockRate : ℝ
  clockRate_nonneg : 0 ≤ clockRate
  clockRate_lt_one : clockRate < 1
  /-- How far a device may run from the nominal rate, as a fraction. -/
  deviceRate : ℝ
  deviceRate_nonneg : 0 ≤ deviceRate
  deviceRate_lt_one : deviceRate < 1
  /-- How far a device's timestamp may be from its host's clock, in
  seconds. -/
  report : ℝ
  report_nonneg : 0 ≤ report
  /-- The most time between the capture of a block's last frame and the
  block's handoff, in seconds. -/
  handoff : ℝ
  handoff_nonneg : 0 ≤ handoff
  /-- The least and the most time before a block's first output sample
  leaves that a playback device requests the block, in seconds. -/
  leadLeast : ℝ
  leadMost : ℝ
  leadLeast_pos : 0 < leadLeast
  leadLeast_le : leadLeast ≤ leadMost
  /-- The most frames, or output samples, in a block. -/
  blockMost : ℕ
  blockMost_pos : 0 < blockMost
  /-- The least and the most time that a message from one host to another
  takes, in seconds. -/
  delayLeast : H → H → ℝ
  delayMost : H → H → ℝ
  delayLeast_pos : ∀ i j, 0 < delayLeast i j
  delayLeast_le : ∀ i j, delayLeast i j ≤ delayMost i j
  /-- Of any `lossRun + 1` consecutive messages on a link, at least one
  arrives. -/
  lossRun : ℕ

/-- A world within bounds. -/
def World.WithinBounds (w : World H R) (B : Bounds H) : Prop :=
  (∀ h, (w.clock h).RateWithin B.clockRate)
    ∧ w.source.RateWithin w.rate B.deviceRate
    ∧ (∀ r, (w.speaker r).RateWithin w.rate B.deviceRate)
    ∧ w.source.ReportsWithin (w.clock w.sender) B.report
    ∧ (∀ r, (w.speaker r).ReportsWithin (w.clock (w.host r)) B.report)
    ∧ w.source.HandoffWithin B.handoff
    ∧ (∀ r, (w.speaker r).LeadWithin B.leadLeast B.leadMost)
    ∧ w.source.BlocksAtMost B.blockMost
    ∧ (∀ r, (w.speaker r).BlocksAtMost B.blockMost)
    ∧ (∀ i j, w.network.DelaysWithin i j (B.delayLeast i j) (B.delayMost i j))
    ∧ (∀ i j, w.network.LossesWithin i j B.lossRun)

/-- A random world, `world ω` with `ω` drawn from `P`, is almost surely
within bounds. -/
def AlmostSurelyWithin {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (world : Ω → World H R) (B : Bounds H) : Prop :=
  ∀ᵐ ω ∂P, (world ω).WithinBounds B

/-- A clock that runs within `ε` of true time's rate advances over an
interval by at least `1 - ε` and at most `1 + ε` times its length. -/
theorem Clock.advance_mem {c : Clock} {ε : ℝ} (hc : c.RateWithin ε) {s t : Time} (hst : s ≤ t) :
    (1 - ε) * (t - s) ≤ c.read t - c.read s ∧ c.read t - c.read s ≤ (1 + ε) * (t - s) := by
  have := abs_le.mp (hc s t hst)
  constructor <;> nlinarith [this.1, this.2]

/-- **The error of an NTP-style clock estimate.** A host asks at true time
`s₁` and reading `t₁ = C(s₁)`; the sender, whose clock is `S`, answers at
`s₂` with its reading `t₂ = S(s₂)`; the answer arrives at `s₄` and reading
`t₄ = C(s₄)`. When both clocks run within `ε` of true time's rate and the
question and the answer take between `dmin₁` and `dmax₁`, and between
`dmin₂` and `dmax₂` seconds, the estimate `t₂ - (t₁ + t₄) / 2` of the
sender's clock minus the host's errs from their true difference at `s₂` by
at most half the largest difference of the two delays, plus `ε` times
their mean. -/
theorem offset_error {C S : Clock} {ε : ℝ} (hC : C.RateWithin ε) {s₁ s₂ s₄ : Time}
    {dmin₁ dmax₁ dmin₂ dmax₂ : ℝ} (h₁ : dmin₁ ≤ s₂ - s₁) (h₁' : s₂ - s₁ ≤ dmax₁)
    (h₂ : dmin₂ ≤ s₄ - s₂) (h₂' : s₄ - s₂ ≤ dmax₂) (hpos₁ : 0 < dmin₁) (hpos₂ : 0 < dmin₂) :
    |(S.read s₂ - (C.read s₁ + C.read s₄) / 2) - (S.read s₂ - C.read s₂)|
      ≤ (max (dmax₁ - dmin₂) (dmax₂ - dmin₁) + ε * (dmax₁ + dmax₂)) / 2 := by
  have ha := Clock.advance_mem hC (show s₁ ≤ s₂ by linarith)
  have hb := Clock.advance_mem hC (show s₂ ≤ s₄ by linarith)
  have hm1 := le_max_left (dmax₁ - dmin₂) (dmax₂ - dmin₁)
  have hm2 := le_max_right (dmax₁ - dmin₂) (dmax₂ - dmin₁)
  have hε : 0 ≤ ε := by
    have := hC s₁ s₂ (by linarith)
    have hpos : 0 < s₂ - s₁ := by linarith
    nlinarith [abs_nonneg (C.read s₂ - C.read s₁ - (s₂ - s₁))]
  rw [abs_le]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

/-- **The drift of the difference of two clocks.** When both clocks run
within `ε` of true time's rate, their difference changes over an interval
by at most `2 ε` times its length. -/
theorem offset_drift {C S : Clock} {ε : ℝ} (hC : C.RateWithin ε) (hS : S.RateWithin ε)
    {s t : Time} (hst : s ≤ t) :
    |(S.read t - C.read t) - (S.read s - C.read s)| ≤ 2 * ε * (t - s) := by
  have ha := Clock.advance_mem hC hst
  have hb := Clock.advance_mem hS hst
  rw [abs_le]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

end Unisono.Spec
