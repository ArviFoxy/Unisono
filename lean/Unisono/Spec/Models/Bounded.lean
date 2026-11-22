/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.World
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.IntermediateValue

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
device may request one, and how small and how large a block may be. A random
world can be required to be within bounds almost surely
(`AlmostSurelyWithin`).

The model counts losses per message, not in time: of any `m + 1`
consecutive messages on a link one arrives, even when all of them are sent
at the same moment. It therefore describes isolated drops and not outages,
in which a link loses everything sent during some time, and it has no
pauses, in which a link holds messages back; a pause enters only through
the largest delay. The model of delays (`Unisono.Spec.Models.Delays`) has
both.

Facts about clocks and devices within bounds:

* An NTP-style estimate of the difference of two clocks errs by at most half
  the largest difference of the two delays, plus the clocks' rate error times
  the mean delay (`offset_error`), and the difference of two clocks drifts by
  at most twice their rate error per second (`offset_drift`,
  `offset_drift_abs`).
* A device takes between `(1 - ε) / rate` and `(1 + ε) / rate` seconds per
  frame or output sample, over any number of them (`capture_sub_mem`,
  `out_sub_mem`). The time of capture of a position changes at the same rates
  (`captured_sub_mem`), so positions with close capture times are close
  (`sub_le_of_captured`), and every true time is the capture time of some
  position (`exists_captured_eq`).
* Devices hand over and request blocks for ever (`handed_unbounded`,
  `asked_unbounded`).
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

/-- Every block of the capture device holds at least `least` and at most
`most` frames. -/
def CaptureDevice.BlocksWithin (d : CaptureDevice) (least most : ℕ) : Prop :=
  ∀ b, least ≤ d.first (b + 1) - d.first b ∧ d.first (b + 1) - d.first b ≤ most

/-- Every block of a playback device holds at least `least` and at most
`most` output samples. -/
def PlaybackDevice.BlocksWithin (d : PlaybackDevice) (least most : ℕ) : Prop :=
  ∀ b, least ≤ d.first (b + 1) - d.first b ∧ d.first (b + 1) - d.first b ≤ most

/-- The messages from host `i` to host `j` that arrive take between `least`
and `most` seconds. -/
def Network.DelaysWithin (net : Network H) (i j : H) (least most : ℝ) : Prop :=
  ∀ s q a, net.deliver i j s q = some a → least ≤ a - s ∧ a - s ≤ most

/-- Of any `m + 1` consecutive messages from host `i` to host `j`, at least
one arrives, whenever they are sent: `send k` is when message `q + k` is
sent. Losses are counted per message: the bound holds even for messages
sent at the same moment, so it rules out outages in time. -/
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
  /-- The fewest and the most frames, or output samples, in a block. -/
  blockLeast : ℕ
  blockMost : ℕ
  blockLeast_pos : 0 < blockLeast
  blockLeast_le : blockLeast ≤ blockMost
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
    ∧ w.source.BlocksWithin B.blockLeast B.blockMost
    ∧ (∀ r, (w.speaker r).BlocksWithin B.blockLeast B.blockMost)
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
at most half the largest difference of the two delays, plus `ε` times the
mean of `dmax₁` and `dmax₂`. -/
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

/-- A clock that runs within `ε` of true time's rate advances between any
two times by their distance within `ε` times it. -/
theorem Clock.read_sub_near {c : Clock} {ε : ℝ} (hc : c.RateWithin ε) (s t : Time) :
    |c.read t - c.read s - (t - s)| ≤ ε * |t - s| := by
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hc s t hst
  · have h := hc t s hts
    rw [abs_of_nonpos (sub_nonpos.mpr hts)]
    have e : |c.read t - c.read s - (t - s)| = |c.read s - c.read t - (s - t)| := by
      rw [← abs_neg]; ring_nf
    rw [e]
    linarith

/-- The difference of two clocks that run within `ε` of true time's rate
changes between any two times by at most `2 ε` times their distance. -/
theorem offset_drift_abs {C S : Clock} {ε : ℝ} (hC : C.RateWithin ε) (hS : S.RateWithin ε)
    (s t : Time) :
    |(S.read t - C.read t) - (S.read s - C.read s)| ≤ 2 * ε * |t - s| := by
  have h1 := Clock.read_sub_near hC s t
  have h2 := Clock.read_sub_near hS s t
  have e : (S.read t - C.read t) - (S.read s - C.read s)
      = (S.read t - S.read s - (t - s)) - (C.read t - C.read s - (t - s)) := by ring
  rw [e]
  calc |(S.read t - S.read s - (t - s)) - (C.read t - C.read s - (t - s))|
      ≤ |S.read t - S.read s - (t - s)| + |C.read t - C.read s - (t - s)| := abs_sub _ _
    _ ≤ ε * |t - s| + ε * |t - s| := add_le_add h2 h1
    _ = 2 * ε * |t - s| := by ring

/-- A capture device that runs within `ε` of the nominal rate takes between
`(1 - ε) / rate` and `(1 + ε) / rate` seconds per frame, over any number of
frames. -/
theorem CaptureDevice.capture_sub_mem {d : CaptureDevice} {rate ε : ℝ}
    (hd : d.RateWithin rate ε) {n m : ℕ} (hnm : n ≤ m) :
    (1 - ε) / rate * (m - n) ≤ d.capture m - d.capture n
      ∧ d.capture m - d.capture n ≤ (1 + ε) / rate * (m - n) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have h := abs_le.mp (hd m)
    have e1 : (1 - ε) / rate = 1 / rate - ε / rate := sub_div _ _ _
    have e2 : (1 + ε) / rate = 1 / rate + ε / rate := add_div _ _ _
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, h.1, h.2]

/-- A playback device that runs within `ε` of the nominal rate takes between
`(1 - ε) / rate` and `(1 + ε) / rate` seconds per output sample, over any
number of output samples. -/
theorem PlaybackDevice.out_sub_mem {d : PlaybackDevice} {rate ε : ℝ}
    (hd : d.RateWithin rate ε) {n m : ℕ} (hnm : n ≤ m) :
    (1 - ε) / rate * (m - n) ≤ d.out m - d.out n
      ∧ d.out m - d.out n ≤ (1 + ε) / rate * (m - n) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have h := abs_le.mp (hd m)
    have e1 : (1 - ε) / rate = 1 / rate - ε / rate := sub_div _ _ _
    have e2 : (1 + ε) / rate = 1 / rate + ε / rate := add_div _ _ _
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, h.1, h.2]

/-- **The time of capture of a position is bi-Lipschitz.** When the capture
device runs within `ε` of the nominal rate, the sound between two positions
`x ≤ y` was captured between `(1 - ε) / rate` and `(1 + ε) / rate` seconds
apart per frame. -/
theorem World.captured_sub_mem (w : World H R) {ε : ℝ} (hd : w.source.RateWithin w.rate ε)
    {x y : ℝ} (hxy : x ≤ y) :
    (1 - ε) / w.rate * (y - x) ≤ w.captured y - w.captured x
      ∧ w.captured y - w.captured x ≤ (1 + ε) / w.rate * (y - x) := by
  have hs : ∀ n, (1 - ε) / w.rate ≤ w.source.capture (n + 1) - w.source.capture n
      ∧ w.source.capture (n + 1) - w.source.capture n ≤ (1 + ε) / w.rate := by
    intro n
    have := CaptureDevice.capture_sub_mem hd (Nat.le_succ n)
    push_cast at this
    simpa using this
  have hab : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hxa : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  unfold World.captured
  rcases hab.eq_or_lt with heq | hlt
  · rw [← heq]
    obtain ⟨h1, h2⟩ := hs ⌊x⌋₊
    have hd0 : 0 ≤ y - x := sub_nonneg.mpr hxy
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hd0, mul_le_mul_of_nonneg_left h2 hd0]
  · have hy0 : 0 ≤ y := by
      by_contra hneg
      have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    have hyb : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
    have hint := CaptureDevice.capture_sub_mem hd (show ⌊x⌋₊ + 1 ≤ ⌊y⌋₊ from hlt)
    obtain ⟨ha1, ha2⟩ := hs ⌊x⌋₊
    obtain ⟨hb1, hb2⟩ := hs ⌊y⌋₊
    have hdy : 0 ≤ y - ⌊y⌋₊ := sub_nonneg.mpr hyb
    have hdx : 0 ≤ (⌊x⌋₊ : ℝ) + 1 - x := by linarith
    have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hint
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hb1 hdy, mul_le_mul_of_nonneg_left ha1 hdx, hint.1]
    · nlinarith [mul_le_mul_of_nonneg_left hb2 hdy, mul_le_mul_of_nonneg_left ha2 hdx, hint.2]

/-- The sound at a frame's position was captured when the frame was. -/
theorem World.captured_natCast (w : World H R) (n : ℕ) : w.captured n = w.source.capture n := by
  simp [World.captured]

/-- **Every true time is the capture time of some position.** When the
capture device runs within `ε < 1` of the nominal rate, the time of capture
of a position is continuous and unbounded both ways. -/
theorem World.exists_captured_eq (w : World H R) {ε : ℝ} (hd : w.source.RateWithin w.rate ε)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (τ : ℝ) : ∃ x, w.captured x = τ := by
  have hrate := w.rate_pos
  have hlo : 0 < (1 - ε) / w.rate := div_pos (by linarith) hrate
  have hhi : 0 ≤ (1 + ε) / w.rate := div_nonneg (by linarith) hrate.le
  have hlip : ∀ x y, dist (w.captured x) (w.captured y) ≤ (1 + ε) / w.rate * dist x y := by
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total x y with hxy | hyx
    · have := w.captured_sub_mem hd hxy
      rw [abs_sub_comm, abs_of_nonneg (by linarith [this.1, mul_nonneg hlo.le (sub_nonneg.mpr hxy)]),
        abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact this.2
    · have := w.captured_sub_mem hd hyx
      rw [abs_of_nonneg (by linarith [this.1, mul_nonneg hlo.le (sub_nonneg.mpr hyx)]),
        abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact this.2
  have hcont : Continuous w.captured :=
    (LipschitzWith.of_dist_le' hlip).continuous
  set M := |τ - w.source.capture 0| / ((1 - ε) / w.rate)
  have hM : 0 ≤ M := div_nonneg (abs_nonneg _) hlo.le
  have hM' : (1 - ε) / w.rate * M = |τ - w.source.capture 0| := by
    simp only [M]; field_simp
  have h0 : w.captured 0 = w.source.capture 0 := by
    simpa using w.captured_natCast 0
  have hup := (w.captured_sub_mem hd hM).1
  have hdown := (w.captured_sub_mem hd (show -M ≤ 0 by linarith)).1
  rw [h0] at hup hdown
  have habs := le_abs_self (τ - w.source.capture 0)
  have habs' := neg_abs_le (τ - w.source.capture 0)
  have hlow : w.captured (-M) ≤ τ := by nlinarith
  have hhigh : τ ≤ w.captured M := by nlinarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (show -M ≤ M by linarith) hcont.continuousOn
    ⟨hlow, hhigh⟩
  exact ⟨x, hx⟩

/-- Positions whose capture times are close are close: within the distance
of their capture times times `rate / (1 - ε)`. -/
theorem World.sub_le_of_captured (w : World H R) {ε : ℝ} (hd : w.source.RateWithin w.rate ε)
    (hε : ε < 1) (x y : ℝ) :
    |x - y| ≤ w.rate / (1 - ε) * |w.captured x - w.captured y| := by
  have hrate := w.rate_pos
  have hlo : 0 < (1 - ε) / w.rate := div_pos (by linarith) hrate
  have key : ∀ a b, a ≤ b → b - a ≤ w.rate / (1 - ε) * (w.captured b - w.captured a) := by
    intro a b hab
    have := (w.captured_sub_mem hd hab).1
    have e : w.rate / (1 - ε) * ((1 - ε) / w.rate * (b - a)) = b - a := by
      field_simp
    calc b - a = w.rate / (1 - ε) * ((1 - ε) / w.rate * (b - a)) := e.symm
      _ ≤ w.rate / (1 - ε) * (w.captured b - w.captured a) :=
        mul_le_mul_of_nonneg_left this (div_nonneg hrate.le (by linarith))
  rcases le_total x y with hxy | hyx
  · have h := key x y hxy
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
    calc y - x ≤ w.rate / (1 - ε) * (w.captured y - w.captured x) := h
      _ ≤ w.rate / (1 - ε) * |w.captured x - w.captured y| := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hrate.le (by linarith))
        rw [abs_sub_comm]; exact le_abs_self _
  · have h := key y x hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    calc x - y ≤ w.rate / (1 - ε) * (w.captured x - w.captured y) := h
      _ ≤ w.rate / (1 - ε) * |w.captured x - w.captured y| := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hrate.le (by linarith))
        exact le_abs_self _

/-- A capture device that runs within `ε < 1` of the nominal rate hands
over blocks for ever: after every true time it hands one over. -/
theorem CaptureDevice.handed_unbounded {d : CaptureDevice} {rate ε : ℝ} (hrate : 0 < rate)
    (hd : d.RateWithin rate ε) (hε : ε < 1) (T : ℝ) : ∃ b, T < d.handed b := by
  have hlo : 0 < (1 - ε) / rate := div_pos (by linarith) hrate
  obtain ⟨b, hb⟩ := exists_nat_gt ((T - d.capture 0) / ((1 - ε) / rate))
  refine ⟨b, ?_⟩
  have hcap := (CaptureDevice.capture_sub_mem hd (Nat.zero_le b)).1
  have hfirst : b ≤ d.first (b + 1) - 1 := by
    have := d.first_strictMono.id_le (b + 1)
    simp only [id] at this
    omega
  have hmono := d.capture_strictMono.monotone hfirst
  have hafter := d.handed_after b
  rw [div_lt_iff₀ hlo] at hb
  simp only [Nat.cast_zero, sub_zero] at hcap
  rw [mul_comm] at hcap
  linarith

/-- A playback device that runs within `ε < 1` of the nominal rate and
requests each block at most `most` seconds ahead requests blocks for ever:
after every true time it requests one. -/
theorem PlaybackDevice.asked_unbounded {d : PlaybackDevice} {rate ε least most : ℝ}
    (hrate : 0 < rate) (hd : d.RateWithin rate ε) (hε : ε < 1) (hlead : d.LeadWithin least most)
    (T : ℝ) : ∃ b, T < d.asked b := by
  have hlo : 0 < (1 - ε) / rate := div_pos (by linarith) hrate
  obtain ⟨b, hb⟩ := exists_nat_gt ((T + most - d.out 0) / ((1 - ε) / rate))
  refine ⟨b, ?_⟩
  have hout := (PlaybackDevice.out_sub_mem hd (Nat.zero_le b)).1
  have hmono : d.out b ≤ d.out (d.first b) :=
    d.out_strictMono.monotone (by simpa using d.first_strictMono.id_le b)
  have hl := (hlead b).2
  rw [div_lt_iff₀ hlo] at hb
  simp only [Nat.cast_zero, sub_zero] at hout
  rw [mul_comm] at hout
  linarith

/-- The time of capture of a position changes by at most `(1 + ε) / rate`
seconds per frame. -/
theorem World.captured_lipschitz (w : World H R) {ε : ℝ}
    (hd : w.source.RateWithin w.rate ε) (x y : ℝ) :
    |w.captured x - w.captured y| ≤ (1 + ε) / w.rate * |x - y| := by
  have hρ := w.rate_pos
  have key : ∀ a b, a ≤ b → |w.captured a - w.captured b| ≤ (1 + ε) / w.rate * |a - b| := by
    intro a b hab
    have h := w.captured_sub_mem hd hab
    rw [abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab), abs_le]
    have hpos : 0 ≤ (b - a) / w.rate := div_nonneg (sub_nonneg.mpr hab) hρ.le
    have e1 : (1 - ε) / w.rate * (b - a) = (1 - ε) * ((b - a) / w.rate) := by ring
    have e2 : (1 + ε) / w.rate * (b - a) = (1 + ε) * ((b - a) / w.rate) := by ring
    rw [e1, e2] at h
    rw [e2]
    constructor <;> nlinarith [h.1, h.2]
  rcases le_total x y with hxy | hyx
  · exact key x y hxy
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact key y x hyx

end Unisono.Spec
