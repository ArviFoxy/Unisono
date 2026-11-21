/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.World

/-!
# Solutions, and the run of a solution in a world

What a solution can do, and what happens when it runs.

A host acts at its **events**: the capture device hands over a block (at the
sender), a playback device asks for a block, a message arrives, or a wake-up
that the host asked for comes. At each event the host decides from its
**view**: the events it has seen so far, each with the reading of its own
clock. True time is not in the view, and neither is anything that happens at
another host unless a message brought it.

At an event a host sends messages to any hosts, asks to be woken at
readings of its clock, and, when a speaker's device asks for a block, says
what each output sample of the block plays. A **solution** says what each
host does, given its view.

**The run** of a solution in a world is what happens, event after event, in
the order of true time (`Solution.states`): the world says when each device
event comes and when each message arrives; the solution says what each host
does. Every solution has exactly one run in every world. Events at the same
true time are taken in a fixed order: the capture device's first, then the
speakers' devices' in the order of the speakers, then messages and wake-ups
in the order they were sent or asked for.

Two limits hold whatever the solution.

* A host sends only frames of the source that it holds; frames it does not
  hold are left out of the message.
* A speaker resamples: each output sample plays the source at a position
  `x`, counted in frames, which in general is not a whole number. The
  resampler computes the sound at `x` from the frames less than `a` frames
  away from `x`, where `a` is the resampler's lookahead: one frame for linear
  interpolation, about half the filter length for a longer filter. The
  output sample plays the original sound only if its host holds all of
  those frames when the device asks for the block; otherwise it is a missed
  sample (`playable`).

The lookahead is a parameter of the run. A third limit, the network's
capacity, is a parameter as well (`Solution.WithinBudget`).

A solution that does infinitely many things before some moment never gets
past it: the run never reaches the devices' later requests, and every later
output sample is missed.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

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

/-- The frames of the source whose data an event brings: those the capture
device hands over, or those a message carries. -/
def Observation.frames : Observation H R Msg → Finset ℕ
  | .handed frames => (frames.map Prod.fst).toFinset
  | .received _ _ frames => frames
  | _ => ∅

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
  samples plays. `some x` is the sound of the source at position `x`,
  counted in frames: frame `n` when `x = n`, and sound between frames `n`
  and `n + 1` when `x` lies between them. `none` is anything else (silence,
  a concealment, anything). -/
  plays : ℕ → Option ℝ

/-- A solution: what each host does at an event, given its view, the events
it has seen so far, oldest first and this one last. -/
def Solution (H : Type) (R : ℕ) (Msg : Type) : Type :=
  H → List (Event H R Msg) → Action H Msg

/-- The frames of block `b` of the capture device, each with what the device
reports for it. -/
def CaptureDevice.block (d : CaptureDevice) (b : ℕ) : List (ℕ × ℝ) :=
  (List.range' (d.first b) (d.first (b + 1) - d.first b)).map fun n => (n, d.reported n)

/-- The output samples of block `b` of a playback device, each with what the
device reports for it. -/
def PlaybackDevice.block (d : PlaybackDevice) (b : ℕ) : List (ℕ × ℝ) :=
  (List.range' (d.first b) (d.first (b + 1) - d.first b)).map fun k => (k, d.reported k)

/-- The true time at which a clock reads `c`, if it ever does. -/
def Clock.timeAt (clock : Clock) (c : ℝ) : Option Time := by
  classical
  exact if h : ∃ t, clock.read t = c then some (Classical.choose h) else none

/-- What an output sample plays, when the solution says `x`, its host holds
the frames `held`, and the resampler's lookahead is `lookahead` frames: the
sound at `x` if every frame less than `lookahead` frames away from `x` is
held, and nothing of the source if not. With a lookahead of one frame, as
for linear interpolation, the sound at position 999.98 needs frames 999 and
1000. -/
def playable (lookahead : ℕ+) (held : Finset ℕ) : Option ℝ → Option ℝ
  | some x => by
      classical
      exact if 0 ≤ x ∧ ∀ n : ℕ, |(n : ℝ) - x| < (lookahead : ℕ) → n ∈ held then some x
        else none
  | none => none

/-- A message on its way: when it arrives, from which host, to which host,
its contents, and the frames of the source it carries. -/
structure InFlight (H : Type) (Msg : Type) where
  arrival : Time
  origin : H
  destination : H
  contents : Msg
  frames : Finset ℕ

/-- A wake-up asked for: when it comes, in true time, and at which host. -/
structure Wake (H : Type) where
  time : Time
  host : H

/-- A message sent, as the network's capacity counts it: when, from which
host, to which host, and how many frames of the source it carries. -/
structure Sent (H : Type) where
  time : Time
  origin : H
  destination : H
  frames : ℕ

/-- Where a run stands after some events. -/
structure State (H : Type) (R : ℕ) (Msg : Type) where
  /-- The events each host has seen, as it saw them, oldest first. -/
  views : H → List (Event H R Msg)
  /-- The next block of the capture device to be handed over. -/
  handedNext : ℕ
  /-- The next block that each speaker's device asks for. -/
  askedNext : Fin R → ℕ
  /-- The messages on their way. -/
  inFlight : List (InFlight H Msg)
  /-- The wake-ups asked for that have not come yet. -/
  wakes : List (Wake H)
  /-- How many messages each host has sent to each host. -/
  sentCount : H → H → ℕ
  /-- The frames of the source that each host holds. -/
  held : H → Finset ℕ
  /-- What each speaker plays at each output sample, as decided so far. -/
  plays : Fin R → ℕ → Option ℝ
  /-- The messages sent so far. -/
  sent : List (Sent H)

/-- Before anything happens. -/
def State.start : State H R Msg where
  views := fun _ => []
  handedNext := 0
  askedNext := fun _ => 0
  inFlight := []
  wakes := []
  sentCount := fun _ _ => 0
  held := fun _ => ∅
  plays := fun _ _ => none
  sent := []

/-- An event that is due: the capture device's next block, a speaker's
device's next request, the `p`-th message on its way, or the `p`-th wake-up
asked for. -/
inductive Due (R : ℕ) where
  | handed (b : ℕ)
  | asked (r : Fin R) (b : ℕ)
  | arrival (p : ℕ)
  | wake (p : ℕ)

/-- The first of a list by a key of a true time and a rank: the earliest,
and of those at the same time the one of the least rank. -/
def earliest {α : Type} (key : α → Time × ℕ) : List α → Option α
  | [] => none
  | a :: l =>
      match earliest key l with
      | none => some a
      | some b =>
          if (key a).1 < (key b).1 ∨ ((key a).1 = (key b).1 ∧ (key a).2 ≤ (key b).2)
          then some a else some b

namespace State

variable [DecidableEq H] (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
  (st : State H R Msg)

/-- The events that are due: the capture device's next block, each speaker's
device's next request, each message on its way, each wake-up asked for. -/
def due : List (Due R) :=
  Due.handed st.handedNext :: (List.finRange R).map (fun r => Due.asked r (st.askedNext r))
    ++ (List.range st.inFlight.length).map Due.arrival
    ++ (List.range st.wakes.length).map Due.wake

/-- When an event that is due comes, and its rank among events at the same
time. -/
def key : Due R → Time × ℕ
  | .handed b => (w.source.handed b, 0)
  | .asked r b => ((w.speaker r).asked b, 1 + r)
  | .arrival p => ((st.inFlight[p]?.map InFlight.arrival).getD 0, 1 + R + p)
  | .wake p => ((st.wakes[p]?.map Wake.time).getD 0, 1 + R + st.inFlight.length + p)

/-- Host `h` sends, at true time `t`, a message to host `j` with contents
`contents` and the data of the frames `frames`. The network delivers it or
loses it; either way it counts against the capacity. -/
def send (h : H) (t : Time) (j : H) (contents : Msg) (frames : Finset ℕ) : State H R Msg :=
  { st with
    sentCount := Function.update st.sentCount h
      (Function.update (st.sentCount h) j (st.sentCount h j + 1))
    inFlight := match w.network.deliver h j t (st.sentCount h j) with
      | some a => st.inFlight ++ [⟨a, h, j, contents, frames⟩]
      | none => st.inFlight
    sent := st.sent ++ [⟨t, h, j, frames.card⟩] }

/-- Host `h` sends, at true time `t`, the messages `sends`, each with only
those of its frames that are in `held`. -/
def sendAll (h : H) (t : Time) (held : Finset ℕ) (sends : List (H × Msg × Finset ℕ)) :
    State H R Msg :=
  sends.foldl (fun s m => s.send w h t m.1 m.2.1 (m.2.2.filter (· ∈ held))) st

/-- Host `h` meets an event at true time `t`, at which it observes `obs`: it
sees the event, holds the frames it brings, sends what the solution says
(each message with only the frames that the host holds), asks for its
wake-ups, and, at a request of a speaker's device, decides what each output
sample of the block plays. -/
def meet (h : H) (t : Time) (obs : Observation H R Msg) : State H R Msg :=
  let view := st.views h ++ [⟨(w.clock h).read t, obs⟩]
  let act := σ h view
  let held := st.held h ∪ obs.frames
  let afterSends := ({ st with
    views := Function.update st.views h view
    held := Function.update st.held h held } : State H R Msg).sendAll w h t held act.sends
  { afterSends with
    wakes := afterSends.wakes ++ act.wakes.filterMap fun c =>
      if (w.clock h).read t < c then ((w.clock h).timeAt c).map fun u => ⟨u, h⟩ else none
    plays := match obs with
      | .asked r outputs => fun r' k =>
          if r' = r ∧ k ∈ outputs.map Prod.fst then playable lookahead held (act.plays k)
          else afterSends.plays r' k
      | _ => afterSends.plays }

/-- The next event happens: the earliest that is due, met by its host. -/
def step : State H R Msg :=
  match earliest (st.key w) st.due with
  | some (.handed b) =>
      { st.meet σ w lookahead w.sender (w.source.handed b) (.handed (w.source.block b)) with
        handedNext := b + 1 }
  | some (.asked r b) =>
      { st.meet σ w lookahead (w.host r) ((w.speaker r).asked b)
          (.asked r ((w.speaker r).block b)) with
        askedNext := Function.update st.askedNext r (b + 1) }
  | some (.arrival p) =>
      match st.inFlight[p]? with
      | some m => ({ st with inFlight := st.inFlight.eraseIdx p }).meet σ w lookahead
          m.destination m.arrival (.received m.origin m.contents m.frames)
      | none => st
  | some (.wake p) =>
      match st.wakes[p]? with
      | some u => ({ st with wakes := st.wakes.eraseIdx p }).meet σ w lookahead u.host u.time
          .woken
      | none => st
  | none => st

end State

variable [DecidableEq H]

/-- The run of a solution in a world, for a resampler lookahead of
`lookahead` frames: where it stands after each number of events. -/
def Solution.states (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) :
    ℕ → State H R Msg
  | 0 => State.start
  | n + 1 => (σ.states w lookahead n).step σ w lookahead

/-- The true time of the event that the run meets at its step `n`. -/
def Solution.eventTime (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (n : ℕ) :
    Time :=
  match earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due with
  | some e => ((σ.states w lookahead n).key w e).1
  | none => 0

/-- What speaker `r` plays at output sample `k` in the run: what was decided
when its device asked for the block that holds `k`, or nothing of the source
if the run never got there. -/
def Solution.plays (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (r : Fin R)
    (k : ℕ) : Option ℝ := by
  classical
  exact if h : ∃ n, k < (w.speaker r).first ((σ.states w lookahead n).askedNext r) then
    (σ.states w lookahead (Nat.find h)).plays r k else none

/-- The run stays within the network's capacity: in any second, each host
sends each host at most `messages` messages, carrying at most `frames`
frames of the source. -/
def Solution.WithinBudget (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    (messages frames : ℕ) : Prop :=
  ∀ n i j (t : Time),
    let inWindow := (σ.states w lookahead n).sent.filter fun s =>
      s.origin = i ∧ s.destination = j ∧ t ≤ s.time ∧ s.time < t + 1
    inWindow.length ≤ messages ∧ (inWindow.map Sent.frames).sum ≤ frames

end Unisono.Spec
