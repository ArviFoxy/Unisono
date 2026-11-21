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
  sender sends the block's frames to every speaker's host, with the block's
  first frame and its timestamp, a reading of the sender's clock. Each
  message is sent `copies` times, so that a link that drops at most
  `copies - 1` consecutive messages still delivers one.
* **The clocks.** At every request of one of its devices, a speaker's host
  other than the sender's asks the sender for its clock: it sends its own
  reading `t₁`, and the sender answers with `t₁` and its own reading `t₂`
  when the question arrived. When the answer arrives at the host's reading
  `t₄`, the host estimates the sender's clock minus its own as
  `t₂ - (t₁ + t₄) / 2`, as NTP does with the two readings of the sender
  taken at the same moment. It keeps the estimate of the latest question
  answered. Each question and each answer is sent `copies` times as well.
  The sender's host itself uses its own clock.
* **The target.** When a speaker's device requests a block, the host
  estimates the reading of the sender's clock at which each output sample
  leaves: the device's timestamp of the block, plus the time of the sample
  within the block at the nominal rate, plus the clock estimate. Less `L`,
  that reading is when the sound the sample should play was captured; the
  latest block that arrived converts it to a position in frames, at the
  nominal rate.
* **The pace.** A speaker does not jump to its target. Each output sample
  advances the position by one frame, corrected towards the target by at
  most `slew` frames, so that the speed stays within `slew` of one and
  changes smoothly; a speaker that has nothing to continue from starts at
  its target.

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
  /-- The largest correction of the position per output sample, frames. -/
  slew : ℝ

/-- What a host remembers from its view. -/
structure Memory (R : ℕ) where
  /-- The latest block of the source: its first frame and its timestamp. -/
  block : Option (ℕ × ℝ)
  /-- Of the latest question for the sender's clock that was answered: the
  host's reading when it sent the question, and the estimate of the
  sender's clock minus this host's clock. -/
  offset : Option (ℝ × ℝ)
  /-- For each speaker: its last output sample and the position it plays. -/
  last : Fin R → Option (ℕ × ℝ)

/-- Before anything is observed. -/
def Memory.empty : Memory R where
  block := none
  offset := none
  last := fun _ => none

/-- A value moved into the interval from `-w` to `w`. -/
def clamp (w x : ℝ) : ℝ := max (-w) (min w x)

variable (p : Params H)

/-- The position that output sample `k` should play: the sound captured `L`
before the sample leaves, by the estimates. `first` is the block's first
output sample and `stamp` the device's timestamp of it. -/
def target (m : Memory R) (first : ℕ) (stamp : ℝ) (k : ℕ) : Option ℝ :=
  match m.block, m.offset with
  | some (f, captured), some (_, offset) =>
      some (f + ((stamp + ((k : ℝ) - first) / p.rate + offset - p.latency) - captured)
        * p.rate)
  | _, _ => none

/-- The next position after `previous`: one frame on, corrected towards the
target by at most `slew` frames. -/
def advance (previous goal : ℝ) : ℝ :=
  previous + 1 + clamp p.slew (goal - previous - 1)

/-- The positions that speaker `r` plays at the output samples `outputs` of
a block, in order, with what it played last: each continues from the one
before when that one played the source, and starts at its target
otherwise. -/
def positions (m : Memory R) (r : Fin R) (outputs : List ℕ) (stamp : ℝ) :
    List (ℕ × Option ℝ) :=
  let first := outputs.headD 0
  (outputs.foldl
    (fun (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ)) k =>
      let x := match target p m first stamp k, acc.2 with
        | some goal, some (j, previous) =>
            if j + 1 = k then some (advance p previous goal) else some goal
        | some goal, none => some goal
        | none, _ => none
      (acc.1 ++ [(k, x)], x.map fun x => (k, x)))
    ([], m.last r)).1

/-- The last output sample of a block and the position it plays, if it
plays the source. -/
def lastPlayed (decided : List (ℕ × Option ℝ)) : Option (ℕ × ℝ) :=
  match decided.getLast? with
  | some (k, some x) => some (k, x)
  | _ => none

variable [DecidableEq H]

/-- How a host's memory changes with an event that it observes. -/
def remember (h : H) (m : Memory R) (e : Event H R Payload) : Memory R :=
  match e.observation with
  | .handed frames stamp =>
      if h = p.sender then
        { m with block := (frames.head?.map Prod.fst).map fun f => (f, stamp), offset := some (0, 0) }
      else m
  | .received _ (.block f stamp) _ =>
      match m.block with
      | some (f', _) => if f' < f then { m with block := some (f, stamp) } else m
      | none => { m with block := some (f, stamp) }
  | .received _ (.answer sent received) _ =>
      if h = p.sender then m
      else
        let estimate := (sent, received - (sent + e.reading) / 2)
        match m.offset with
        | some (asked, _) => if asked < sent then { m with offset := some estimate } else m
        | none => { m with offset := some estimate }
  | .asked r outputs stamp =>
      { m with last := Function.update m.last r (lastPlayed (positions p m r outputs stamp)) }
  | _ => m

/-- What a host does at an event, with what it remembers from the events
before. -/
def act (h : H) (m : Memory R) (e : Event H R Payload) : Action H Payload :=
  match e.observation with
  | .handed frames stamp =>
      if h = p.sender then
        match frames.head? with
        | some (f, _) =>
            { sends := p.speakers.flatMap fun j =>
                List.replicate p.copies (j, Payload.block f stamp, (frames.map Prod.fst).toFinset)
              timers := []
              plays := fun _ => none }
        | none => ⟨[], [], fun _ => none⟩
      else ⟨[], [], fun _ => none⟩
  | .received i (.ask sent) _ =>
      if h = p.sender then
        { sends := List.replicate p.copies (i, Payload.answer sent e.reading, ∅)
          timers := []
          plays := fun _ => none }
      else ⟨[], [], fun _ => none⟩
  | .asked r outputs stamp =>
      let decided := positions p m r outputs stamp
      { sends := if h = p.sender then []
          else List.replicate p.copies (p.sender, Payload.ask e.reading, ∅)
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
