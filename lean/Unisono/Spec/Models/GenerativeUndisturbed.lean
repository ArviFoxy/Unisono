/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeIdlePath
public import Unisono.Spec.Models.GenerativeClocks

/-!
# A stretch of time in which nothing disturbs the stream to a speaker

The stream from the sender to a speaker depends on four clocks: those of
the sender's host, of the speaker's host, of the capture device and of the
speaker's playback device. It depends on the pauses of the two hosts and of
the links between them in both directions, and on the errors of the capture
device's timestamps.

* `Draw.Regular d`: what every outcome of a random world of the model
  satisfies (`Prior.regular`): the paused times never decrease, the wander of
  every clock and the error of every device's reports are continuous in
  time, and every split lies strictly between zero and one.
* `RateBands`: a lower and an upper bound for the rate of each of the four
  clocks. `RateBands.driftUp` and `RateBands.driftDown` are the largest
  rates at which the sender's clock can run ahead of, or fall behind, a line
  whose slope against the host's clock lies between the least rate of the
  sender's clock divided by the largest rate of the host's clock and the
  largest divided by the least. `RateBands.ratioWidth` is the width of the
  interval in which the ratio of the host's clock to the playback device's
  clock lies.
* `Draw.Undisturbed d s h x B ρ a b`: from the true time `a` to `b`, the
  paths from host `s` to host `h` and back are idle (`Draw.PathIdle`), the
  rates of the clocks of `s`, of `h`, of the capture device and of the
  playback device `x` stay within the bands `B`, and the capture device's
  timestamps are at most `ρ` early.

Under `Draw.Undisturbed` each clock advances, over every part of the
stretch, by between its lower and its upper bound times the length of the
part (`Draw.Undisturbed.sender_sub` and the three statements after it).
A shorter stretch inside an undisturbed one is undisturbed
(`Draw.Undisturbed.mono`).

Nothing here is about a solution.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory

variable {H : Type} {R : ℕ}

/-- **A regular draw**: the paused times of the links and of the hosts never
decrease; the wander of every clock and the error of every device's reports
are continuous in time; every split lies strictly between zero and one. -/
structure Draw.Regular (d : Draw H R) : Prop where
  linkPaused_monotone : ∀ i j, Monotone (d.linkPaused i j)
  hostPaused_monotone : ∀ h, Monotone (d.hostPaused h)
  wander_continuous : ∀ h, Continuous (d.wander h)
  deviceWander_continuous : ∀ x, Continuous (d.deviceWander x)
  reportError_continuous : ∀ x, Continuous (d.reportError x)
  split_mem : ∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1
  split_swap : ∀ i j, d.split i j + d.split j i = 1

/-- **Every outcome of a random world of the model is a regular draw.** -/
theorem Prior.regular {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R}
    {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) (ω : Ω) :
    (D ω).Regular where
  linkPaused_monotone := hD.linkPaused_monotone ω
  hostPaused_monotone := hD.hostPaused_monotone ω
  wander_continuous := hD.wander_continuous ω
  deviceWander_continuous := hD.deviceWander_continuous ω
  reportError_continuous := hD.reportError_continuous ω
  split_mem := hD.split_mem ω
  split_swap := hD.split_swap ω

/-- In a regular draw the least delay of every direction is positive. -/
theorem Draw.Regular.leastDelay_pos {d : Draw H R} (hd : d.Regular) (f : Member H R)
    (i j : H) : 0 < d.split i j * f.roundTrip i j :=
  mul_pos (hd.split_mem i j).1 (f.roundTrip_pos i j)

/-- In a regular draw the least delays of the two directions of a pair add
up to the pair's least round trip. -/
theorem Draw.Regular.leastDelay_add {d : Draw H R} (hd : d.Regular) (f : Member H R)
    (i j : H) :
    d.split i j * f.roundTrip i j + d.split j i * f.roundTrip j i = f.roundTrip i j := by
  have h := hd.split_swap i j
  rw [f.roundTrip_symm j i]
  linear_combination f.roundTrip i j * h

/-- A lower and an upper bound for the rate of each of the four clocks that
the stream to a speaker depends on. -/
structure RateBands where
  /-- The least rate of the clock of the sender's host. -/
  senderLo : ℝ
  /-- The largest rate of the clock of the sender's host. -/
  senderHi : ℝ
  /-- The least rate of the clock of the speaker's host. -/
  hostLo : ℝ
  /-- The largest rate of the clock of the speaker's host. -/
  hostHi : ℝ
  /-- The least rate of the clock of the capture device. -/
  captureLo : ℝ
  /-- The largest rate of the clock of the capture device. -/
  captureHi : ℝ
  /-- The least rate of the clock of the speaker's playback device. -/
  outputLo : ℝ
  /-- The largest rate of the clock of the speaker's playback device. -/
  outputHi : ℝ

/-- The bands are valid: every lower bound is positive and at most its upper
bound. -/
structure RateBands.Valid (B : RateBands) : Prop where
  sender_pos : 0 < B.senderLo
  sender_le : B.senderLo ≤ B.senderHi
  host_pos : 0 < B.hostLo
  host_le : B.hostLo ≤ B.hostHi
  capture_pos : 0 < B.captureLo
  capture_le : B.captureLo ≤ B.captureHi
  output_pos : 0 < B.outputLo
  output_le : B.outputLo ≤ B.outputHi

/-- The largest rate, per second of true time, at which the sender's clock
can run ahead of a line whose slope against the host's clock lies between
the least rate of the sender's clock divided by the largest rate of the
host's clock and the largest divided by the least. -/
def RateBands.driftUp (B : RateBands) : ℝ :=
  B.senderHi - B.senderLo / B.hostHi * B.hostLo

/-- The largest rate, per second of true time, at which the sender's clock
can fall behind such a line. -/
def RateBands.driftDown (B : RateBands) : ℝ :=
  B.senderHi / B.hostLo * B.hostHi - B.senderLo

/-- The width of the interval in which the ratio of the host's clock to the
playback device's clock lies: the largest rate of the host's clock divided
by the least rate of the device's clock, minus the least divided by the
largest. -/
def RateBands.ratioWidth (B : RateBands) : ℝ :=
  B.hostHi / B.outputLo - B.hostLo / B.outputHi

/-- For valid bands the sender's clock cannot fall behind at a negative
rate. -/
theorem RateBands.driftDown_nonneg {B : RateBands} (hB : B.Valid) : 0 ≤ B.driftDown := by
  unfold RateBands.driftDown
  have h1 : B.senderLo ≤ B.senderHi / B.hostLo * B.hostHi := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hB.host_pos]
    have h2 := mul_le_mul hB.sender_le hB.host_le hB.host_pos.le
      (hB.sender_pos.le.trans hB.sender_le)
    linarith
  linarith

/-- For valid bands the sender's clock cannot run ahead at a negative
rate. -/
theorem RateBands.driftUp_nonneg {B : RateBands} (hB : B.Valid) : 0 ≤ B.driftUp := by
  unfold RateBands.driftUp
  have hHi : 0 < B.hostHi := lt_of_lt_of_le hB.host_pos hB.host_le
  have h1 : B.senderLo / B.hostHi * B.hostLo ≤ B.senderHi := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hHi]
    have h2 := mul_le_mul hB.sender_le hB.host_le hB.host_pos.le
      (hB.sender_pos.le.trans hB.sender_le)
    linarith
  linarith

/-- For valid bands the interval of the ratio has a width that is not
negative. -/
theorem RateBands.ratioWidth_nonneg {B : RateBands} (hB : B.Valid) :
    0 ≤ B.ratioWidth := by
  unfold RateBands.ratioWidth
  have hHi : 0 < B.outputHi := lt_of_lt_of_le hB.output_pos hB.output_le
  have h1 : B.hostLo / B.outputHi ≤ B.hostHi / B.outputLo := by
    rw [div_le_div_iff₀ hHi hB.output_pos]
    have h2 := mul_le_mul hB.host_le hB.output_le hB.output_pos.le
      (hB.host_pos.le.trans hB.host_le)
    linarith
  linarith

/-- **From the true time `a` to `b` nothing disturbs the stream** from host
`s` to the speaker with playback device `x` on host `h`: the paths from `s`
to `h` and from `h` to `s` are idle; the rates of the clocks of `s`, of `h`,
of the capture device and of the playback device `x` stay within the bands
`B`; and the capture device's timestamps are at most `ρ` early. -/
structure Draw.Undisturbed (d : Draw H R) (s h : H) (x : Fin R) (B : RateBands) (ρ : ℝ)
    (a b : Time) : Prop where
  /-- The path of the stream. -/
  forward : d.PathIdle s h a b
  /-- The path of the clock queries. -/
  backward : d.PathIdle h s a b
  sender : ∀ z ∈ Set.Icc a b, B.senderLo ≤ d.rate s z ∧ d.rate s z ≤ B.senderHi
  host : ∀ z ∈ Set.Icc a b, B.hostLo ≤ d.rate h z ∧ d.rate h z ≤ B.hostHi
  capture : ∀ z ∈ Set.Icc a b,
    B.captureLo ≤ d.deviceRate none z ∧ d.deviceRate none z ≤ B.captureHi
  output : ∀ z ∈ Set.Icc a b,
    B.outputLo ≤ d.deviceRate (some x) z ∧ d.deviceRate (some x) z ≤ B.outputHi
  report : ∀ z ∈ Set.Icc a b, -ρ ≤ d.reportError none z

/-- A link or a host that is idle over a period is idle over every shorter
period inside it, when its paused time never decreases. -/
theorem IdleOn.mono {X : Time → ℝ} (hmono : Monotone X) {a b a' b' : Time}
    (h : IdleOn X a b) (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) : IdleOn X a' b' := by
  have h1 : X b = X a := h.2
  have h2 : X a' = X a := le_antisymm (by rw [← h1]; exact hmono (hab.trans hb)) (hmono ha)
  have h3 : X b' = X a := le_antisymm (by rw [← h1]; exact hmono hb) (hmono (ha.trans hab))
  refine ⟨fun q hq => ?_, by rw [h2, h3]⟩
  have h4 := (h.isBacklog hmono ha (hab.trans hb)).1 ⟨(q : ℝ), hq, rfl⟩
  linarith

/-- A path that is idle over a period is idle over every shorter period
inside it. -/
theorem Draw.PathIdle.mono {d : Draw H R} (hd : d.Regular) {i j : H} {a b a' b' : Time}
    (h : d.PathIdle i j a b) (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) :
    d.PathIdle i j a' b' where
  source := h.source.mono (hd.hostPaused_monotone i) ha hab hb
  link := h.link.mono (hd.linkPaused_monotone i j) ha hab hb
  target := h.target.mono (hd.hostPaused_monotone j) ha hab hb

namespace Draw.Undisturbed

variable {d : Draw H R} {s h : H} {x : Fin R} {B : RateBands} {ρ : ℝ} {a b : Time}

/-- **A stretch inside an undisturbed stretch is undisturbed.** -/
theorem mono (hd : d.Regular) (hU : d.Undisturbed s h x B ρ a b) {a' b' : Time}
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) : d.Undisturbed s h x B ρ a' b' where
  forward := hU.forward.mono hd ha hab hb
  backward := hU.backward.mono hd ha hab hb
  sender := fun z hz => hU.sender z ⟨ha.trans hz.1, hz.2.trans hb⟩
  host := fun z hz => hU.host z ⟨ha.trans hz.1, hz.2.trans hb⟩
  capture := fun z hz => hU.capture z ⟨ha.trans hz.1, hz.2.trans hb⟩
  output := fun z hz => hU.output z ⟨ha.trans hz.1, hz.2.trans hb⟩
  report := fun z hz => hU.report z ⟨ha.trans hz.1, hz.2.trans hb⟩

/-- **The advance of the sender's clock** over a part of an undisturbed
stretch. -/
theorem sender_sub (hd : d.Regular) (hU : d.Undisturbed s h x B ρ a b) {y y' : Time}
    (hay : a ≤ y) (hyy' : y ≤ y') (hyb : y' ≤ b) :
    B.senderLo * (y' - y) ≤ d.reading s y' - d.reading s y
      ∧ d.reading s y' - d.reading s y ≤ B.senderHi * (y' - y) :=
  d.reading_sub_mem s (hd.wander_continuous s) hU.sender hay hyy' hyb

/-- **The advance of the clock of the speaker's host** over a part of an
undisturbed stretch. -/
theorem host_sub (hd : d.Regular) (hU : d.Undisturbed s h x B ρ a b) {y y' : Time}
    (hay : a ≤ y) (hyy' : y ≤ y') (hyb : y' ≤ b) :
    B.hostLo * (y' - y) ≤ d.reading h y' - d.reading h y
      ∧ d.reading h y' - d.reading h y ≤ B.hostHi * (y' - y) :=
  d.reading_sub_mem h (hd.wander_continuous h) hU.host hay hyy' hyb

/-- **The advance of the capture device's clock** over a part of an
undisturbed stretch. -/
theorem capture_sub (hd : d.Regular) (hU : d.Undisturbed s h x B ρ a b) {y y' : Time}
    (hay : a ≤ y) (hyy' : y ≤ y') (hyb : y' ≤ b) :
    B.captureLo * (y' - y) ≤ d.deviceReading none y' - d.deviceReading none y
      ∧ d.deviceReading none y' - d.deviceReading none y ≤ B.captureHi * (y' - y) :=
  d.deviceReading_sub_mem none (hd.deviceWander_continuous none) hU.capture hay hyy' hyb

/-- **The advance of the playback device's clock** over a part of an
undisturbed stretch. -/
theorem output_sub (hd : d.Regular) (hU : d.Undisturbed s h x B ρ a b) {y y' : Time}
    (hay : a ≤ y) (hyy' : y ≤ y') (hyb : y' ≤ b) :
    B.outputLo * (y' - y) ≤ d.deviceReading (some x) y' - d.deviceReading (some x) y
      ∧ d.deviceReading (some x) y' - d.deviceReading (some x) y ≤ B.outputHi * (y' - y) :=
  d.deviceReading_sub_mem (some x) (hd.deviceWander_continuous (some x)) hU.output hay hyy' hyb

end Draw.Undisturbed

end Unisono.Spec.GenerativeWorld
