/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Solution

/-!
# A baseline solution: fixed playout delay

Every speaker plays each frame of the source `L` seconds after the frame
was captured, as accurately as its host's clock allows. The baseline is the
simplest complete solution, and later solutions are compared with it. A
*receiving host* is a host that drives a speaker and is not the sender's
host.

* **The stream.** When the capture device hands over a block, the sender
  sends the block's frames to every receiving host, together with the
  block's first frame and its timestamp, which is a reading of the sender's
  clock. Each message is sent `copies` times, so a link that drops at most
  `copies - 1` consecutive messages still delivers one copy.
* **The clocks.** When one of its devices requests a block, a receiving
  host sends the sender a clock query that carries its clock reading `t₁`,
  unless it sent a query within the last `period` seconds of its own clock.
  The sender answers with `t₁` and its own reading `t₂` at the query's
  arrival, unless it has already answered a query from that host with a
  reading of at least `t₁`. The sender therefore answers each query once,
  on whichever copy arrives first. When the answer arrives at the host's
  reading `t₄`, the host estimates the sender's clock minus its own clock
  as `t₂ - (t₁ + t₄) / 2`. This is NTP's estimate with the sender's two
  readings taken at the same moment. The host keeps the estimate from the
  latest query that was answered. Queries and answers are also sent
  `copies` times. The sender's host uses its own clock.
* **The target.** When a speaker's device requests a block, the host
  estimates the sender's clock reading at which each output sample leaves:
  the device's timestamp of the block, plus the sample's offset within the
  block at the nominal rate, plus the clock estimate. That reading minus `L`
  is the capture time of the sound that the sample should play. The latest
  block that has arrived converts this capture time to a position in
  frames, at the nominal rate.
* **The pace.** A speaker does not jump to its target. At each output
  sample, the position advances by one frame plus a correction towards the
  target, clamped to `[-slew, slew]`. The position therefore advances by
  between `1 - slew` and `1 + slew` frames per output sample. The
  correction is not smoothed, so the advance can change by up to
  `2 * slew` from one output sample to the next. A speaker continues from
  the position it chose for its previous output sample, whether or not that
  sample could play. It starts at its target when it chose no position for
  the previous output sample: at its first output sample, and after output
  samples for which it had no block or no clock estimate.

Nothing is retransmitted on request; the copies cover losses.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- What the baseline's messages carry besides frames of the source. -/
inductive Payload where
  /-- A block of the source: its first frame, and the capture device's
  timestamp of that frame, which is a reading of the sender's clock. -/
  | block (first : ℕ) (stamp : ℝ)
  /-- A clock query: the querying host's clock reading when it sends the
  query. -/
  | ask (sent : ℝ)
  /-- The sender's answer to a clock query: the reading that the query
  carried, and the sender's clock reading when the query arrived. -/
  | answer (sent : ℝ) (received : ℝ)

/-- The parameters of the baseline. -/
structure Params (H : Type) where
  /-- The sender's host. -/
  sender : H
  /-- The hosts of the speakers, to which the sender sends the stream. -/
  speakers : List H
  /-- The nominal rate, in frames per second. -/
  rate : ℝ
  /-- The latency `L`: every speaker plays each frame `L` seconds after the
  frame was captured. -/
  latency : ℝ
  /-- How many times each message is sent. -/
  copies : ℕ
  /-- The polling period: the minimum time between two clock queries from a
  host, in seconds of that host's clock. -/
  period : ℝ
  /-- The slew: the largest correction of the position per output sample,
  in frames. -/
  slew : ℝ

/-- What a host remembers from its view. -/
structure Memory (H : Type) (R : ℕ) where
  /-- The latest block of the source: its first frame and its timestamp. -/
  block : Option (ℕ × ℝ)
  /-- The clock estimate from the latest answered query: the host's reading
  when it sent that query, and the estimate of the sender's clock minus
  this host's clock. -/
  offset : Option (ℝ × ℝ)
  /-- The host's clock reading when it last sent a clock query. -/
  asked : Option ℝ
  /-- At the sender: for each host, the reading carried by the latest query
  from that host that the sender answered. -/
  answered : H → Option ℝ
  /-- For each speaker: the last output sample of its latest request, with
  the position chosen for it, if one was chosen. -/
  last : Fin R → Option (ℕ × ℝ)

/-- The memory before any event. -/
def Memory.empty : Memory H R where
  block := none
  offset := none
  asked := none
  answered := fun _ => none
  last := fun _ => none

/-- Clamps `x` to the interval `[-w, w]`. -/
def clamp (w x : ℝ) : ℝ := max (-w) (min w x)

variable (p : Params H)

/-- The target position of output sample `k`: according to the host's
estimates, the position whose sound was captured `L` seconds before the
sample leaves. `first` is the block's first output sample, and `stamp` is
the device's timestamp of that sample. There is no target while the host
has no block or no clock estimate. -/
def target (m : Memory H R) (first : ℕ) (stamp : ℝ) (k : ℕ) : Option ℝ :=
  match m.block, m.offset with
  | some (f, captured), some (_, offset) =>
      some (f + ((stamp + ((k : ℝ) - first) / p.rate + offset - p.latency) - captured)
        * p.rate)
  | _, _ => none

/-- The position after `previous`: one frame further, plus a correction
towards `goal` clamped to `[-slew, slew]`. -/
def advance (previous goal : ℝ) : ℝ :=
  previous + 1 + clamp p.slew (goal - previous - 1)

/-- The position chosen for output sample `k`, given `previous`, the last
output sample that has a position and that position. If that sample is
`k - 1`, the position advances from it towards the target; otherwise the
position is the target. There is no position when there is no target. -/
def choose (m : Memory H R) (first : ℕ) (stamp : ℝ) (previous : Option (ℕ × ℝ)) (k : ℕ) :
    Option ℝ :=
  match target p m first stamp k, previous with
  | some goal, some (j, x) => if j + 1 = k then some (advance p x goal) else some goal
  | some goal, none => some goal
  | none, _ => none

/-- The positions that speaker `r` chooses for the output samples `outputs`
of a block, in order. `choose` computes each position from the previous
one, starting from the last position the speaker chose before this
block. -/
def positions (m : Memory H R) (r : Fin R) (outputs : List ℕ) (stamp : ℝ) :
    List (ℕ × Option ℝ) :=
  (outputs.foldl
    (fun (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ)) k =>
      let x := choose p m (outputs.headD 0) stamp acc.2 k
      (acc.1 ++ [(k, x)], x.map fun x => (k, x)))
    ([], m.last r)).1

/-- The last output sample of a block and the position chosen for it, if a
position was chosen. -/
def lastChosen (decided : List (ℕ × Option ℝ)) : Option (ℕ × ℝ) :=
  match decided.getLast? with
  | some (k, some x) => some (k, x)
  | _ => none

/-- Whether the sender answers a clock query from host `i` that carries the
reading `sent`. It does unless it has already answered a query from that
host with a reading of at least `sent`. -/
def answers (m : Memory H R) (i : H) (sent : ℝ) : Bool :=
  match m.answered i with
  | some a => decide (a < sent)
  | none => true

variable [DecidableEq H]

/-- Whether host `h` sends a clock query at a device request at its clock
reading `t`. It does when it is not the sender's host and has not sent a
query within the last `period` seconds of its clock. -/
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
  | .received _ (.block f stamp) _ _ =>
      if h = p.sender then m
      else
        match m.block with
        | some (f', _) => if f' < f then { m with block := some (f, stamp) } else m
        | none => { m with block := some (f, stamp) }
  | .received i (.ask sent) _ _ =>
      if h = p.sender ∧ answers m i sent = true then
        { m with answered := Function.update m.answered i (some sent) }
      else m
  | .received _ (.answer sent received) _ _ =>
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

/-- What a host does at an event, given what it remembers from the earlier
events. -/
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
  | .received i (.ask sent) _ _ =>
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

/-- The baseline: each host acts on the last event of its view, given what
it remembers from the earlier events. -/
def solution : Solution H R Payload := fun h view =>
  match view.getLast? with
  | some e => act p h (view.dropLast.foldl (remember p h) Memory.empty) e
  | none => ⟨[], [], fun _ => none⟩

end Unisono.Solutions.FixedDelay
