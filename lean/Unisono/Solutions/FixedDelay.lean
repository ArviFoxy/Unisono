/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Solution

/-!
# A baseline solution: fixed playout delay

Every speaker plays each frame of the source a fixed latency `L` after the
frame was captured, as well as it can tell from its host's clock. It is the
simplest complete solution, and the one that later solutions are compared
with.

* **The stream.** At each block that the capture device hands over, the
  sender sends the block's frames to the host of every speaker other than
  its own, with the block's first frame and its timestamp, a reading of the
  sender's clock. Each message is sent `copies` times, so that a link that
  drops at most `copies - 1` consecutive messages still delivers one.
* **The clocks.** At a request of one of its devices, a speaker's host
  other than the sender's asks the sender for its clock, unless it asked
  within the last `period` seconds of its own clock: it sends its reading
  `t₁`. The sender answers with `t₁` and its own reading `t₂` when the
  question arrived, unless it has already answered a question of that host
  whose reading is as late or later; so it answers each question once,
  whichever copy arrives first. When the answer arrives at the host's
  reading `t₄`, the host estimates the sender's clock minus its own as
  `t₂ - (t₁ + t₄) / 2`, as NTP does with the two readings of the sender
  taken at the same moment, and keeps the estimate of the latest question
  answered. Questions and answers are sent `copies` times as well. The
  sender's host itself uses its own clock.
* **The target.** When a speaker's device requests a block, the host
  estimates the reading of the sender's clock at which each output sample
  leaves: the device's timestamp of the block, plus the time of the sample
  within the block at the nominal rate, plus the clock estimate. Less `L`,
  that reading is when the sound the sample should play was captured; the
  latest block that arrived converts it to a position in frames, at the
  nominal rate.
* **The pace.** A speaker does not jump to its target. Each output sample
  advances the position by one frame, corrected towards the target by at
  most `slew` frames, so the position advances by between `1 - slew` and
  `1 + slew` frames per output sample. The correction is not smoothed: the
  advance can change by up to `2 slew` from one output sample to the next.
  A speaker continues from the position it chose for its previous output
  sample, whether or not that sample could play; it starts at its target
  when it chose no position there, at its first output sample or while it
  had no estimates.

Nothing is retransmitted on request; losses are covered by the copies.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- What the baseline's messages carry besides frames of the source. -/
inductive Payload where
  /-- A block of the source: its first frame, and the capture device's
  timestamp of that frame, a reading of the sender's clock. -/
  | block (first : ℕ) (stamp : ℝ)
  /-- A question for the sender's clock: the asking host's reading when it
  sends the question. -/
  | ask (sent : ℝ)
  /-- The sender's answer: the reading the question carried, and the
  sender's reading when the question arrived. -/
  | answer (sent : ℝ) (received : ℝ)

/-- The parameters of the baseline. -/
structure Params (H : Type) where
  /-- The sender's host. -/
  sender : H
  /-- The hosts of the speakers, to which the sender sends the stream. -/
  speakers : List H
  /-- The nominal rate, frames per second. -/
  rate : ℝ
  /-- The latency `L` at which every speaker plays every frame, seconds. -/
  latency : ℝ
  /-- How many times each message is sent. -/
  copies : ℕ
  /-- The least time between two questions of a host for the sender's clock,
  in seconds of the host's clock. -/
  period : ℝ
  /-- The largest correction of the position per output sample, frames. -/
  slew : ℝ

/-- What a host remembers from its view. -/
structure Memory (H : Type) (R : ℕ) where
  /-- The latest block of the source: its first frame and its timestamp. -/
  block : Option (ℕ × ℝ)
  /-- Of the latest question for the sender's clock that was answered: the
  host's reading when it sent the question, and the estimate of the
  sender's clock minus this host's clock. -/
  offset : Option (ℝ × ℝ)
  /-- The host's reading when it last asked the sender for its clock. -/
  asked : Option ℝ
  /-- At the sender: for each host, the reading carried by the latest of its
  questions that the sender answered. -/
  answered : H → Option ℝ
  /-- For each speaker: its last output sample and the position it chose
  for it. -/
  last : Fin R → Option (ℕ × ℝ)

/-- Before anything is observed. -/
def Memory.empty : Memory H R where
  block := none
  offset := none
  asked := none
  answered := fun _ => none
  last := fun _ => none

/-- A value moved into the interval from `-w` to `w`. -/
def clamp (w x : ℝ) : ℝ := max (-w) (min w x)

variable (p : Params H)

/-- The position that output sample `k` should play: the sound captured `L`
before the sample leaves, by the estimates. `first` is the block's first
output sample and `stamp` the device's timestamp of it. -/
def target (m : Memory H R) (first : ℕ) (stamp : ℝ) (k : ℕ) : Option ℝ :=
  match m.block, m.offset with
  | some (f, captured), some (_, offset) =>
      some (f + ((stamp + ((k : ℝ) - first) / p.rate + offset - p.latency) - captured)
        * p.rate)
  | _, _ => none

/-- The next position after `previous`: one frame on, corrected towards the
target by at most `slew` frames. -/
def advance (previous goal : ℝ) : ℝ :=
  previous + 1 + clamp p.slew (goal - previous - 1)

/-- The position chosen for output sample `k`, given the output sample and
position chosen last: one step on towards the target when the last was for
the output sample before, the target otherwise. -/
def choose (m : Memory H R) (first : ℕ) (stamp : ℝ) (previous : Option (ℕ × ℝ)) (k : ℕ) :
    Option ℝ :=
  match target p m first stamp k, previous with
  | some goal, some (j, x) => if j + 1 = k then some (advance p x goal) else some goal
  | some goal, none => some goal
  | none, _ => none

/-- The positions that speaker `r` chooses for the output samples `outputs`
of a block, in order, with the position it chose last: each continues from
the position chosen for the output sample before, and starts at the target
when there is none. -/
def positions (m : Memory H R) (r : Fin R) (outputs : List ℕ) (stamp : ℝ) :
    List (ℕ × Option ℝ) :=
  (outputs.foldl
    (fun (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ)) k =>
      let x := choose p m (outputs.headD 0) stamp acc.2 k
      (acc.1 ++ [(k, x)], x.map fun x => (k, x)))
    ([], m.last r)).1

/-- The last output sample of a block and the position chosen for it, if
there is one. -/
def lastChosen (decided : List (ℕ × Option ℝ)) : Option (ℕ × ℝ) :=
  match decided.getLast? with
  | some (k, some x) => some (k, x)
  | _ => none

/-- Whether the sender answers a question of host `i` that carries the
reading `sent`: it has not answered a question of that host whose reading is
as late or later. -/
def answers (m : Memory H R) (i : H) (sent : ℝ) : Bool :=
  match m.answered i with
  | some a => decide (a < sent)
  | none => true

variable [DecidableEq H]

/-- Whether host `h` asks the sender for its clock at a device request at
its reading `t`: it is not the sender's host, and it has not asked within
the last `period` seconds of its clock. -/
def asks (h : H) (m : Memory H R) (t : ℝ) : Bool :=
  h != p.sender && match m.asked with
    | some a => decide (a + p.period ≤ t)
    | none => true

/-- How a host's memory changes with an event that it observes. -/
def remember (h : H) (m : Memory H R) (e : Event H R Payload) : Memory H R :=
  match e.observation with
  | .handed frames stamp =>
      if h = p.sender then
        match frames.head? with
        | some (f, _) => { m with block := some (f, stamp), offset := some (0, 0) }
        | none => m
      else m
  | .received _ (.block f stamp) _ =>
      if h = p.sender then m
      else
        match m.block with
        | some (f', _) => if f' < f then { m with block := some (f, stamp) } else m
        | none => { m with block := some (f, stamp) }
  | .received i (.ask sent) _ =>
      if h = p.sender ∧ answers m i sent = true then
        { m with answered := Function.update m.answered i (some sent) }
      else m
  | .received _ (.answer sent received) _ =>
      if h = p.sender then m
      else
        let estimate := (sent, received - (sent + e.reading) / 2)
        match m.offset with
        | some (asked, _) => if asked < sent then { m with offset := some estimate } else m
        | none => { m with offset := some estimate }
  | .asked r outputs stamp =>
      { m with
        last := Function.update m.last r (lastChosen (positions p m r outputs stamp))
        asked := if asks p h m e.reading then some e.reading else m.asked }
  | _ => m

/-- What a host does at an event, with what it remembers from the events
before. -/
def act (h : H) (m : Memory H R) (e : Event H R Payload) : Action H Payload :=
  match e.observation with
  | .handed frames stamp =>
      if h = p.sender then
        match frames.head? with
        | some (f, _) =>
            { sends := (p.speakers.filter (· ≠ p.sender)).flatMap fun j =>
                List.replicate p.copies (j, Payload.block f stamp, (frames.map Prod.fst).toFinset)
              timers := []
              plays := fun _ => none }
        | none => ⟨[], [], fun _ => none⟩
      else ⟨[], [], fun _ => none⟩
  | .received i (.ask sent) _ =>
      if h = p.sender ∧ answers m i sent = true then
        { sends := List.replicate p.copies (i, Payload.answer sent e.reading, ∅)
          timers := []
          plays := fun _ => none }
      else ⟨[], [], fun _ => none⟩
  | .asked r outputs stamp =>
      let decided := positions p m r outputs stamp
      { sends := if asks p h m e.reading then
          List.replicate p.copies (p.sender, Payload.ask e.reading, ∅) else []
        timers := []
        plays := fun k => (decided.lookup k).join }
  | _ => ⟨[], [], fun _ => none⟩

/-- The baseline: each host acts on the last event of its view with what it
remembers from the events before. -/
def solution : Solution H R Payload := fun h view =>
  match view.getLast? with
  | some e => act p h (view.dropLast.foldl (remember p h) Memory.empty) e
  | none => ⟨[], [], fun _ => none⟩

end Unisono.Solutions.FixedDelay
