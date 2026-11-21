/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.World

/-!
# Solutions

What a solution can do, and from what it decides. A solution acts at every
host: it sends messages to other hosts, asks to be woken at a reading of the
host's clock, and, when a speaker's device asks for a block of output
samples, says what each of them plays.

A host acts at its **events**: the capture device hands over a block (at the
sender), a playback device asks for a block, a message arrives, or a
wake-up it asked for comes. At each event it decides from its **view**: the
events it has seen so far, each with the reading of its own clock. True time
is not in the view, and neither is anything that happens at another host
unless a message brought it.

A **run** is what happens when a solution runs in a world: the events of
each host with their true times, and what each speaker plays. `Consistent`
says when a record is a run: each event has one cause, every cause that
the world and the solution produce is an event, the network delivers what
it delivers, and what each host does is what the solution says for its
view.

Two limits hold whatever the solution: a host can send only frames of the
source that it holds, and a speaker can play content only from frames that
its host holds when the device asks for the block (`Consistent.plays`).
A third, the network's capacity, is a parameter (`WithinBudget`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal

variable {H : Type} {R : ℕ} {Msg : Type}

/-- What a host observes at one of its events. `Msg` is what messages
carry besides frames of the source; a solution chooses it. -/
inductive Observation (H : Type) (R : ℕ) (Msg : Type) where
  /-- The capture device hands over a block: its frames, each with what the
  device reports for when it was captured. -/
  | handed (frames : List (ℕ × ℝ))
  /-- Speaker `r`'s device asks for a block: its output samples, each with
  what the device reports for when it will leave. -/
  | asked (r : Fin R) (outputs : List (ℕ × ℝ))
  /-- A message arrives from host `i`: its contents, and the frames of the
  source whose data it carries. -/
  | received (i : H) (contents : Msg) (frames : Finset ℕ)
  /-- A wake-up that the host asked for comes. -/
  | woken

/-- An event as a host sees it: the reading of its own clock, and what it
observes. -/
structure Event (H : Type) (R : ℕ) (Msg : Type) where
  reading : ℝ
  observation : Observation H R Msg

/-- What a host does at one of its events. -/
structure Action (H : Type) (Msg : Type) where
  /-- The messages it sends: to which host, with what contents, carrying the
  data of which frames of the source. -/
  sends : List (H × Msg × Finset ℕ)
  /-- Readings of its clock at which it wants to be woken. -/
  wakes : List ℝ
  /-- When a playback device asks for a block: what each of its output
  samples plays, either the source's content at a position in frames, or
  `none` for anything else (silence, a concealment, anything). -/
  plays : ℕ → Option ℝ

/-- A solution: what each host does at an event, given its view, the events
it has seen so far, oldest first and this one last. -/
def Solution (H : Type) (R : ℕ) (Msg : Type) : Type :=
  H → List (Event H R Msg) → Action H Msg

/-- Why an event happens at a host. -/
inductive Cause (H : Type) (R : ℕ) where
  /-- The capture device hands over block `b`. -/
  | handed (b : ℕ)
  /-- Speaker `r`'s device asks for block `b`. -/
  | asked (r : Fin R) (b : ℕ)
  /-- The message of the `p`-th send at host `i`'s `e`-th event arrives. -/
  | message (i : H) (e : ℕ) (p : ℕ)
  /-- The `p`-th wake-up that the host asked for at its own `e`-th event
  comes. -/
  | woken (e : ℕ) (p : ℕ)

/-- A record of a run: the events of each host, in order, each with its true
time, what the host observes and why it happens; and what each speaker plays
at each output sample. -/
structure Run (H : Type) (R : ℕ) (Msg : Type) where
  /-- The true time of host `h`'s `e`-th event. -/
  time : H → ℕ → Time
  /-- What host `h` observes at its `e`-th event. -/
  seen : H → ℕ → Observation H R Msg
  /-- Why host `h`'s `e`-th event happens. -/
  cause : H → ℕ → Cause H R
  /-- What speaker `r` plays at output sample `k`: the source's content at a
  position in frames, or `none`. -/
  plays : Fin R → ℕ → Option ℝ

/-- The frames of block `b` of the capture device, each with what the device
reports for it. -/
def CaptureDevice.block (d : CaptureDevice) (b : ℕ) : List (ℕ × ℝ) :=
  (List.range' (d.first b) (d.first (b + 1) - d.first b)).map fun n => (n, d.reported n)

/-- The output samples of block `b` of a playback device, each with what the
device reports for it. -/
def PlaybackDevice.block (d : PlaybackDevice) (b : ℕ) : List (ℕ × ℝ) :=
  (List.range' (d.first b) (d.first (b + 1) - d.first b)).map fun k => (k, d.reported k)

namespace Run

variable (σ : Solution H R Msg) (w : World H R) (ρ : Run H R Msg)

/-- The view of host `h` at its `e`-th event: its events so far, as it sees
them, oldest first and this one last. -/
def view (h : H) (e : ℕ) : List (Event H R Msg) :=
  (List.range (e + 1)).map fun i => ⟨(w.clock h).read (ρ.time h i), ρ.seen h i⟩

/-- What host `h` does at its `e`-th event: what the solution says for its
view. -/
def action (h : H) (e : ℕ) : Action H Msg :=
  σ h (ρ.view w h e)

/-- How many messages host `i` sends to host `j` before the `p`-th send of
its `e`-th event. -/
def sequence [DecidableEq H] (i j : H) (e p : ℕ) : ℕ :=
  ((List.range e).map fun e' =>
      ((ρ.action σ w i e').sends.filter fun m => m.1 = j).length).sum
    + (((ρ.action σ w i e).sends.take p).filter fun m => m.1 = j).length

/-- Whether an observation brings the data of frame `n` of the source. -/
def brings : Observation H R Msg → ℕ → Prop
  | .handed frames, n => n ∈ frames.map Prod.fst
  | .received _ _ frames, n => n ∈ frames
  | _, _ => False

/-- Whether host `h` holds frame `n` of the source at its `e`-th event: an
event so far brought it. -/
def holds (h : H) (e n : ℕ) : Prop :=
  ∃ e' ≤ e, brings (ρ.seen h e') n

/-- What host `h`'s `e`-th event is follows from its cause: its true time
and what the host observes. -/
def Explains [DecidableEq H] (h : H) (e : ℕ) : Prop :=
  match ρ.cause h e with
  | .handed b =>
      h = w.sender ∧ ρ.time h e = w.source.handed b
        ∧ ρ.seen h e = .handed (w.source.block b)
  | .asked r b =>
      h = w.host r ∧ ρ.time h e = (w.speaker r).asked b
        ∧ ρ.seen h e = .asked r ((w.speaker r).block b)
  | .message i e' p =>
      ∃ contents frames, (ρ.action σ w i e').sends[p]? = some (h, contents, frames)
        ∧ w.network.deliver i h (ρ.time i e') (ρ.sequence σ w i h e' p) = some (ρ.time h e)
        ∧ ρ.seen h e = .received i contents frames
  | .woken e' p =>
      ∃ c, (ρ.action σ w h e').wakes[p]? = some c
        ∧ (w.clock h).read (ρ.time h e') < c
        ∧ (w.clock h).read (ρ.time h e) = c
        ∧ ρ.seen h e = .woken

/-- A record is a run of the solution `σ` in the world `w`. -/
structure Consistent [DecidableEq H] : Prop where
  /-- Each host's events come in the order of true time. -/
  ordered : ∀ h, Monotone (ρ.time h)
  /-- No two events of a host have the same cause. -/
  distinct : ∀ h, Function.Injective (ρ.cause h)
  /-- Each event is what its cause makes it. -/
  explained : ∀ h e, ρ.Explains σ w h e
  /-- Each block of the capture device is an event at the sender. -/
  handed : ∀ b, ∃ e, ρ.cause w.sender e = .handed b
  /-- Each request of a speaker's device is an event at the speaker's host. -/
  asked : ∀ r b, ∃ e, ρ.cause (w.host r) e = .asked r b
  /-- Each message that the network delivers is an event at the host it is
  sent to. -/
  delivered : ∀ i e p j contents frames a,
    (ρ.action σ w i e).sends[p]? = some (j, contents, frames) →
      w.network.deliver i j (ρ.time i e) (ρ.sequence σ w i j e p) = some a →
        ∃ e', ρ.cause j e' = .message i e p
  /-- Each wake-up asked for at a later reading of the clock is an event. -/
  woken : ∀ h e p c, (ρ.action σ w h e).wakes[p]? = some c →
    (w.clock h).read (ρ.time h e) < c → ∃ e', ρ.cause h e' = .woken e p
  /-- A host sends only frames that it holds. -/
  sendsHeld : ∀ i e j contents frames,
    (j, contents, frames) ∈ (ρ.action σ w i e).sends → ∀ n ∈ frames, ρ.holds i e n
  /-- What a speaker plays is decided when its device asks for the block, and
  content at position `x` can be played only if the speaker's host then holds
  the frames on either side of it. -/
  plays : ∀ r b e, ρ.cause (w.host r) e = .asked r b →
    ∀ k, (w.speaker r).first b ≤ k → k < (w.speaker r).first (b + 1) →
      ρ.plays r k = (ρ.action σ w (w.host r) e).plays k
        ∧ ∀ x, ρ.plays r k = some x →
            0 ≤ x ∧ ρ.holds (w.host r) e ⌊x⌋₊ ∧ ρ.holds (w.host r) e (⌊x⌋₊ + 1)

/-- How many messages host `i` sends to host `j`, and how many frames they
carry, at host `i`'s events whose true times lie in `[t, t + 1)`. -/
def sentWithin [DecidableEq H] (i j : H) (t : Time) : ℝ≥0∞ × ℝ≥0∞ :=
  (∑' e, if t ≤ ρ.time i e ∧ ρ.time i e < t + 1 then
      (((ρ.action σ w i e).sends.filter fun m => m.1 = j).length : ℝ≥0∞) else 0,
   ∑' e, if t ≤ ρ.time i e ∧ ρ.time i e < t + 1 then
      (((ρ.action σ w i e).sends.filter fun m => m.1 = j).map
        fun m => (m.2.2.card : ℝ≥0∞)).sum else 0)

/-- The run stays within the network's capacity: in any second, each host
sends each other host at most `messages` messages, carrying at most
`frames` frames of the source. -/
def WithinBudget [DecidableEq H] (messages frames : ℝ≥0∞) : Prop :=
  ∀ i j t, (ρ.sentWithin σ w i j t).1 ≤ messages ∧ (ρ.sentWithin σ w i j t).2 ≤ frames

end Run

/-- The runs of a solution in a world. -/
def Solution.runs [DecidableEq H] (σ : Solution H R Msg) (w : World H R) :
    Set (Run H R Msg) :=
  {ρ | ρ.Consistent σ w}

/-- A solution is admissible in a world for a capacity of the network: it has
a run there, and every run of it stays within the capacity. -/
def Solution.Admissible [DecidableEq H] (σ : Solution H R Msg) (w : World H R)
    (messages frames : ℝ≥0∞) : Prop :=
  (∃ ρ, ρ ∈ σ.runs w) ∧ ∀ ρ ∈ σ.runs w, ρ.WithinBudget σ w messages frames

end Unisono.Spec
