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

Everything outside a solution's control: time, the devices, the hosts'
clocks, the network and the application's target latency. A solution
sees the world only through what its hosts observe (`Unisono.Spec.Solution`).
`docs/specification.tex` states the same in mathematical notation.

* **True time** is a real number of seconds. No device can read it.
* **The capture device** of the sender captures frame `n` of the source at
  true time `capture n` and hands the frames to its host in blocks. The
  host handles the handover of block `b` at true time `handed b`, when the
  block's last frame is captured or later: a host that is busy handles its
  events late.
* **Speaker `r`** is a playback device. Its output sample `k` leaves the
  device at true time `out k`. The device requests its output samples from
  its host in blocks. The host handles the request of block `b` at true
  time `asked b`. A host that is busy may handle a request after output
  samples of the block left the device; those output samples play nothing
  of the source.
* **Every host** has a clock that runs at its own rate.
* **The network** carries messages between any two hosts. A message reaches
  the receiving host some time after it is sent, or is lost. The kernel of
  the receiving host stamps the message with the reading of the host's clock
  at the moment at which the message reaches the host. The host's program
  handles the message at that moment or later: a host that is busy handles
  its events late.
* **The application** sets a target latency for each frame, for lip-sync
  mode.

All devices have the same nominal rate, in frames per second; each runs at
the rate of its own oscillator.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- True time, in seconds. No device can read it. -/
abbrev Time := ℝ

/-- A clock: what it reads at each true time. It is continuous and strictly
increasing. -/
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
  /-- Frames are captured one after another. -/
  capture_strictMono : StrictMono capture
  /-- The first frame of block `b`. Block `b` holds the frames from
  `first b` to just before `first (b + 1)`. -/
  first : ℕ → ℕ
  first_zero : first 0 = 0
  first_strictMono : StrictMono first
  /-- When the sender's host handles the handover of block `b`. -/
  handed : ℕ → Time
  /-- The host handles the handovers in the order of the blocks. A host
  that was busy may handle several of them at the same true time. -/
  handed_mono : Monotone handed
  /-- The host handles the handover of a block when the block's last frame
  is captured, or later. -/
  handed_after : ∀ b, capture (first (b + 1) - 1) ≤ handed b
  /-- The timestamp that the device reports for block `b`, as a reading of
  its host's clock: when the block's first frame was captured. It need not
  be exact. -/
  reported : ℕ → ℝ

/-- The playback device of a speaker. Output samples are numbered from zero,
the first one after the speaker starts. -/
structure PlaybackDevice where
  /-- When output sample `k` leaves the device, at its output. -/
  out : ℕ → Time
  /-- Output samples leave one after another. -/
  out_strictMono : StrictMono out
  /-- The first output sample of block `b`. Block `b` holds the output
  samples from `first b` to just before `first (b + 1)`. -/
  first : ℕ → ℕ
  first_zero : first 0 = 0
  first_strictMono : StrictMono first
  /-- When the speaker's host handles the device's request of block `b`. It
  may be after output samples of the block left the device; such an output
  sample plays nothing of the source (`State.handle`). -/
  asked : ℕ → Time
  /-- The host handles the requests in the order of the blocks. A host that
  was busy may handle several of them at the same true time. -/
  asked_mono : Monotone asked
  /-- The timestamp that the device reports for block `b`, as a reading of
  its host's clock: when the block's first output sample will leave. It
  need not be exact. -/
  reported : ℕ → ℝ

/-- The network between hosts of type `H`. Whether a message arrives, and
when, may depend on when it is sent and on how many messages the same host
sent to the same host before it; it does not depend on the payload. -/
structure Network (H : Type) where
  /-- When the program of host `j` handles the `q`-th message (counted from
  zero) that host `i` sends to host `j`, sent at true time `s`; `none` if the
  network drops it. -/
  deliver : H → H → Time → ℕ → Option Time
  /-- When that message reaches host `j`. The kernel of the host stamps the
  message with the reading of the host's clock at that moment. It has a
  meaning only for a message that is not dropped. -/
  reach : H → H → Time → ℕ → Time
  /-- A message reaches the host after it is sent, and the host's program
  handles it then or later. -/
  reach_mem : ∀ i j s q a, deliver i j s q = some a → s < reach i j s q ∧ reach i j s q ≤ a

/-- The program of the receiving host handles a message after the message
is sent. -/
theorem Network.after {H : Type} (net : Network H) (i j : H) (s : Time) (q : ℕ) (a : Time)
    (h : net.deliver i j s q = some a) : s < a :=
  lt_of_lt_of_le (net.reach_mem i j s q a h).1 (net.reach_mem i j s q a h).2

/-- The world, for hosts of type `H` and `R` speakers. The hosts are the
sender and the hosts of the speakers; one host may drive several speakers,
and the sender may drive speakers as well. -/
structure World (H : Type) (R : ℕ) where
  /-- The nominal rate of every device, in frames per second. -/
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
  /-- The target latency of frame `n` in lip-sync mode, in seconds: the time
  from the frame's capture to its playback that the application wants. The
  application gives it to the sender's host together with the frame. -/
  target : ℕ → ℝ

variable {H : Type} {R : ℕ}

/-- When the sound at position `x` of the source was captured, with `x`
counted in frames: frame `n` at `capture n`, and the sound a fraction of the
way from frame `n` to frame `n + 1` the same fraction of the way between
their captures. -/
def World.captured (w : World H R) (x : ℝ) : Time :=
  w.source.capture ⌊x⌋₊
    + (x - ⌊x⌋₊) * (w.source.capture (⌊x⌋₊ + 1) - w.source.capture ⌊x⌋₊)

end Unisono.Spec
