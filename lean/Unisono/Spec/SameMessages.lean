/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Run

/-!
# Solutions that send the same messages

Two solutions that send the same messages and set the same timers at every
view have the same run, except for what the speakers play
(`Solution.states_withoutPlays`). The hosts observe the same events at the
same times, hold the same frames, and handle the same requests
(`Solution.views_eq_of_sends_eq`, `Solution.held_eq_of_sends_eq`,
`Solution.handled_eq_of_sends_eq`, `Solution.eventTime_eq_of_sends_eq`).

A solution that changes only what another solution plays can therefore use
everything that is proved about the other's messages.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- A state of a run with what the speakers play forgotten. -/
def State.withoutPlays (st : State H R Msg) : State H R Msg :=
  { st with plays := fun _ _ => none }

namespace State

variable (w : World H R)

omit [DecidableEq H] in
/-- Two states that agree when what is played is forgotten agree in
everything else. -/
theorem fields_of_withoutPlays_eq {st st' : State H R Msg}
    (h : st.withoutPlays = st'.withoutPlays) :
    st.views = st'.views ∧ st.handedNext = st'.handedNext ∧ st.askedNext = st'.askedNext
      ∧ st.inFlight = st'.inFlight ∧ st.timers = st'.timers ∧ st.sentCount = st'.sentCount
      ∧ st.held = st'.held ∧ st.sent = st'.sent := by
  have h1 := congrArg State.views h
  have h2 := congrArg State.handedNext h
  have h3 := congrArg State.askedNext h
  have h4 := congrArg State.inFlight h
  have h5 := congrArg State.timers h
  have h6 := congrArg State.sentCount h
  have h7 := congrArg State.held h
  have h8 := congrArg State.sent h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem sendAll_withoutPlays (h : H) (t : Time) (held : Finset ℕ) :
    ∀ (sends : List (H × Msg × Finset ℕ)) (st : State H R Msg),
      (st.sendAll w h t held sends).withoutPlays = st.withoutPlays.sendAll w h t held sends
  | [], _ => rfl
  | s :: l, st => by
      have h1 := sendAll_withoutPlays h t held l
        (st.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held)))
      have e : (st.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held))).withoutPlays
          = st.withoutPlays.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held)) := rfl
      rw [e] at h1
      exact h1

/-- The state after a host adds an event to its view and holds the frames
that the event brings. -/
def observe (st : State H R Msg) (h : H) (t : Time) (obs : Observation H R Msg) :
    State H R Msg :=
  { st with
    views := Function.update st.views h (st.views h ++ [⟨(w.clock h).read t, obs⟩])
    held := Function.update st.held h (st.held h ∪ obs.frames) }

/-- The state after a host sets timers at the readings `cs` of its clock. -/
def addTimers (st : State H R Msg) (h : H) (t : Time) (cs : List ℝ) : State H R Msg :=
  { st with
    timers := st.timers ++ cs.filterMap fun c =>
      if (w.clock h).read t < c then ((w.clock h).timeAt c).map fun u => ⟨u, h⟩ else none }

/-- Handling an event, with what is played forgotten: the host observes the
event, sends its messages and sets its timers. -/
theorem handle_withoutPlays_eq (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg)
    (h : H) (t : Time) (obs : Observation H R Msg) :
    (st.handle σ w lookahead h t obs).withoutPlays
      = (((st.observe w h t obs).withoutPlays.sendAll w h t (st.held h ∪ obs.frames)
            (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends).addTimers w h t
          (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).timers).withoutPlays := by
  rw [← sendAll_withoutPlays]
  rfl

/-- Handling an event changes everything but what is played in the same way
for two solutions that send the same messages and set the same timers. -/
theorem handle_withoutPlays (σ σ' : Solution H R Msg) (lookahead : ℕ+)
    (hs : ∀ h v, (σ h v).sends = (σ' h v).sends) (ht : ∀ h v, (σ h v).timers = (σ' h v).timers)
    {st st' : State H R Msg} (hst : st.withoutPlays = st'.withoutPlays) (h : H) (t : Time)
    (obs : Observation H R Msg) :
    (st.handle σ w lookahead h t obs).withoutPlays
      = (st'.handle σ' w lookahead h t obs).withoutPlays := by
  obtain ⟨hviews, -, -, -, -, -, hheld, -⟩ := fields_of_withoutPlays_eq hst
  have e0 : (st.observe w h t obs).withoutPlays = (st'.observe w h t obs).withoutPlays := by
    show st.withoutPlays.observe w h t obs = st'.withoutPlays.observe w h t obs
    rw [hst]
  rw [handle_withoutPlays_eq, handle_withoutPlays_eq, e0, hviews, hheld, hs h, ht h]

/-- A step of the run changes everything but what is played in the same way
for two solutions that send the same messages and set the same timers. -/
theorem step_withoutPlays (σ σ' : Solution H R Msg) (lookahead : ℕ+)
    (hs : ∀ h v, (σ h v).sends = (σ' h v).sends) (ht : ∀ h v, (σ h v).timers = (σ' h v).timers)
    {st st' : State H R Msg} (hst : st.withoutPlays = st'.withoutPlays) :
    (st.step σ w lookahead).withoutPlays = (st'.step σ' w lookahead).withoutPlays := by
  obtain ⟨-, e1, e2, e3, e4, -, -, -⟩ := fields_of_withoutPlays_eq hst
  have hkey : st.key w = st'.key w := by
    funext d
    cases d <;> simp only [key, e3, e4]
  have hdue : st.due = st'.due := by
    simp only [due, e1, e2, e3, e4]
  unfold step
  rw [hkey, hdue]
  cases hearly : earliest (st'.key w) st'.due with
  | none => exact hst
  | some d =>
    cases d with
    | handed b =>
      have h := handle_withoutPlays w σ σ' lookahead hs ht hst w.sender (w.source.handed b)
        (.handed ((w.source.block b).map fun n => (n, w.target n)) (w.source.reported b))
      exact congrArg (fun s : State H R Msg => ({ s with handedNext := b + 1 } : State H R Msg)) h
    | asked r b =>
      have h := handle_withoutPlays w σ σ' lookahead hs ht hst (w.host r) ((w.speaker r).asked b)
        (.asked r ((w.speaker r).block b) ((w.speaker r).reported b))
      rw [e2]
      exact congrArg (fun s : State H R Msg =>
        ({ s with askedNext := Function.update st'.askedNext r (b + 1) } : State H R Msg)) h
    | arrival p =>
      dsimp only
      rw [e3]
      cases hm : st'.inFlight[p]? with
      | none => exact hst
      | some m =>
        have hst' : ({ st with inFlight := st'.inFlight.eraseIdx p } : State H R Msg).withoutPlays
            = ({ st' with inFlight := st'.inFlight.eraseIdx p } : State H R Msg).withoutPlays :=
          congrArg (fun s : State H R Msg =>
            ({ s with inFlight := st'.inFlight.eraseIdx p } : State H R Msg)) hst
        exact handle_withoutPlays w σ σ' lookahead hs ht hst' m.destination m.arrival
          (.received m.origin m.contents m.frames ((w.clock m.destination).read m.reached))
    | timer p =>
      dsimp only
      rw [e4]
      cases hu : st'.timers[p]? with
      | none => exact hst
      | some u =>
        have hst' : ({ st with timers := st'.timers.eraseIdx p } : State H R Msg).withoutPlays
            = ({ st' with timers := st'.timers.eraseIdx p } : State H R Msg).withoutPlays :=
          congrArg (fun s : State H R Msg =>
            ({ s with timers := st'.timers.eraseIdx p } : State H R Msg)) hst
        exact handle_withoutPlays w σ σ' lookahead hs ht hst' u.host u.time .timer

end State

section Runs

variable (w : World H R) {σ σ' : Solution H R Msg} (lookahead : ℕ+)

/-- **Two solutions that send the same messages and set the same timers have
the same run, except for what the speakers play.** -/
theorem Solution.states_withoutPlays (hs : ∀ h v, (σ h v).sends = (σ' h v).sends)
    (ht : ∀ h v, (σ h v).timers = (σ' h v).timers) (n : ℕ) :
    (σ.states w lookahead n).withoutPlays = (σ'.states w lookahead n).withoutPlays := by
  induction n with
  | zero => rfl
  | succ n ih => exact State.step_withoutPlays w σ σ' lookahead hs ht ih

theorem Solution.views_eq_of_sends_eq (hs : ∀ h v, (σ h v).sends = (σ' h v).sends)
    (ht : ∀ h v, (σ h v).timers = (σ' h v).timers) (n : ℕ) :
    (σ.states w lookahead n).views = (σ'.states w lookahead n).views :=
  (State.fields_of_withoutPlays_eq (Solution.states_withoutPlays w lookahead hs ht n)).1

theorem Solution.held_eq_of_sends_eq (hs : ∀ h v, (σ h v).sends = (σ' h v).sends)
    (ht : ∀ h v, (σ h v).timers = (σ' h v).timers) (n : ℕ) :
    (σ.states w lookahead n).held = (σ'.states w lookahead n).held :=
  (State.fields_of_withoutPlays_eq (Solution.states_withoutPlays w lookahead hs ht n)).2.2.2.2.2.2.1

theorem Solution.askedNext_eq_of_sends_eq (hs : ∀ h v, (σ h v).sends = (σ' h v).sends)
    (ht : ∀ h v, (σ h v).timers = (σ' h v).timers) (n : ℕ) :
    (σ.states w lookahead n).askedNext = (σ'.states w lookahead n).askedNext :=
  (State.fields_of_withoutPlays_eq (Solution.states_withoutPlays w lookahead hs ht n)).2.2.1

/-- The two runs have the same earliest pending event at every step, with
the same key. -/
theorem Solution.earliest_eq_of_sends_eq (hs : ∀ h v, (σ h v).sends = (σ' h v).sends)
    (ht : ∀ h v, (σ h v).timers = (σ' h v).timers) (n : ℕ) :
    (σ.states w lookahead n).key w = (σ'.states w lookahead n).key w
      ∧ earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
        = earliest ((σ'.states w lookahead n).key w) (σ'.states w lookahead n).due := by
  obtain ⟨-, e1, e2, e3, e4, -, -, -⟩ :=
    State.fields_of_withoutPlays_eq (Solution.states_withoutPlays w lookahead hs ht n)
  have hkey : (σ.states w lookahead n).key w = (σ'.states w lookahead n).key w := by
    funext d
    cases d <;> simp only [State.key, e3, e4]
  have hdue : (σ.states w lookahead n).due = (σ'.states w lookahead n).due := by
    simp only [State.due, e1, e2, e3, e4]
  exact ⟨hkey, by rw [hkey, hdue]⟩

/-- The two runs handle the same event at every step. -/
theorem Solution.handled_eq_of_sends_eq (hs : ∀ h v, (σ h v).sends = (σ' h v).sends)
    (ht : ∀ h v, (σ h v).timers = (σ' h v).timers) (n : ℕ) :
    σ.handled w lookahead n = σ'.handled w lookahead n := by
  obtain ⟨-, -, -, e3, e4, -, -, -⟩ :=
    State.fields_of_withoutPlays_eq (Solution.states_withoutPlays w lookahead hs ht n)
  unfold Solution.handled
  rw [(Solution.earliest_eq_of_sends_eq w lookahead hs ht n).2, e3, e4]

/-- The two runs handle their events at the same true times. -/
theorem Solution.eventTime_eq_of_sends_eq (hs : ∀ h v, (σ h v).sends = (σ' h v).sends)
    (ht : ∀ h v, (σ h v).timers = (σ' h v).timers) (n : ℕ) :
    σ.eventTime w lookahead n = σ'.eventTime w lookahead n := by
  obtain ⟨hkey, hearly⟩ := Solution.earliest_eq_of_sends_eq w lookahead hs ht n
  unfold Solution.eventTime
  rw [hearly, hkey]

end Runs

end Unisono.Spec
