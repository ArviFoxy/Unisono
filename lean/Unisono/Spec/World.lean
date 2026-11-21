/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.Filter.ENNReal

/-!
# The world

The part of the problem that no solution chooses: time, the devices, the
hosts' clocks and the network. A solution sees the world only through what
its hosts observe (`Unisono.Spec.Solution`). `docs/specification.md` says
the same in prose.

* **True time** is a real number of seconds. No device reads it.
* **The capture device** of the sender captures frame `n` of the source at
  true time `capture n`, and hands the frames to its host in blocks.
* **Speaker `r`** is a playback device. Its output sample `k` leaves the
  device at true time `out k`. The device asks its host for its output
  samples in blocks, before they leave.
* **Every host** has a clock, which goes forward at a rate of its own.
* **The network** carries messages between any two hosts. A message
  arrives some time after it is sent, or is lost.

All devices have the same nominal rate, frames a second; each runs at the
rate of its own oscillator.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- True time, in seconds. No device can read it. -/
abbrev Time := ℝ

/-- A clock: what it reads at each true time. It goes forward and does not
jump. -/
structure Clock where
  /-- The reading at each true time. -/
  read : Time → ℝ
  /-- A later time reads more. -/
  strictMono : StrictMono read
  /-- The reading does not jump. -/
  continuous : Continuous read

/-- The capture device of the sender. Frames are numbered from zero, the
first frame of the stream. -/
structure CaptureDevice where
  /-- When frame `n` is captured. -/
  capture : ℕ → Time
  /-- Frames are captured one after the other. -/
  capture_strictMono : StrictMono capture
  /-- The first frame of block `b`. Block `b` holds the frames from
  `first b` to just before `first (b + 1)`. -/
  first : ℕ → ℕ
  first_zero : first 0 = 0
  first_strictMono : StrictMono first
  /-- When block `b` is handed to the sender's host. -/
  handed : ℕ → Time
  handed_strictMono : StrictMono handed
  /-- A block is handed over once its last frame is captured. -/
  handed_after : ∀ b, capture (first (b + 1) - 1) ≤ handed b
  /-- What the device reports, as a reading of its host's clock, for when
  frame `n` was captured. It may be wrong. -/
  reported : ℕ → ℝ

/-- The playback device of a speaker. Output samples are numbered from zero,
the first one after the speaker starts. -/
structure PlaybackDevice where
  /-- When output sample `k` leaves the device, at its output. -/
  out : ℕ → Time
  /-- Output samples leave one after the other. -/
  out_strictMono : StrictMono out
  /-- The first output sample of block `b`. Block `b` holds the output
  samples from `first b` to just before `first (b + 1)`. -/
  first : ℕ → ℕ
  first_zero : first 0 = 0
  first_strictMono : StrictMono first
  /-- When the device asks for block `b`. -/
  asked : ℕ → Time
  asked_strictMono : StrictMono asked
  /-- A block is asked for before its first output sample leaves. -/
  asked_before : ∀ b, asked b < out (first b)
  /-- What the device reports, as a reading of its host's clock, for when
  output sample `k` leaves. It may be wrong. -/
  reported : ℕ → ℝ

/-- The network between hosts of type `H`. Whether a message arrives, and
when, may depend on when it is sent and on how many messages the same host
sent to the same host before it; it does not depend on what it carries. -/
structure Network (H : Type) where
  /-- When a message arrives that host `i` sends to host `j` at true time
  `s`, as its `q`-th message to `j` (counted from zero); `none` if it is
  lost. -/
  deliver : H → H → Time → ℕ → Option Time
  /-- A message arrives after it is sent. -/
  after : ∀ i j s q a, deliver i j s q = some a → s < a

/-- The world, for hosts of type `H` and `R` speakers. The hosts are the
sender and the hosts of the speakers; one host may drive several speakers,
and the sender may drive speakers as well. -/
structure World (H : Type) (R : ℕ) where
  /-- The nominal rate of every device, frames a second. -/
  rate : ℝ
  rate_pos : 0 < rate
  /-- The host of the capture device: the sender. -/
  sender : H
  /-- The host of each speaker. -/
  host : Fin R → H
  /-- There are no other hosts. -/
  hosts : ∀ h, h = sender ∨ ∃ r, host r = h
  /-- Each host's clock. -/
  clock : H → Clock
  /-- The capture device. -/
  source : CaptureDevice
  /-- Each speaker's playback device. -/
  speaker : Fin R → PlaybackDevice
  /-- The network. -/
  network : Network H

variable {H : Type} {R : ℕ}

/-- When the sound at position `x` of the source was captured, `x` counted
in frames: frame `n` at `capture n`, and the sound a fraction of the way
from frame `n` to frame `n + 1` the same fraction of the way between their
captures. -/
def World.captured (w : World H R) (x : ℝ) : Time :=
  w.source.capture ⌊x⌋₊
    + (x - ⌊x⌋₊) * (w.source.capture (⌊x⌋₊ + 1) - w.source.capture ⌊x⌋₊)

end Unisono.Spec
