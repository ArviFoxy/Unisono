/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.SameMessages

/-!
# Solutions whose messages carry more

A solution may send the messages of another solution with more in each of
them: further fields in the payload. Let `π` take a payload of the richer
solution to the payload of the plainer one, by forgetting the further
fields. Suppose that at every view the richer solution sends, once `π` is
applied to its payloads, what the plainer one sends at the same view with
`π` applied to the payloads in it, and sets the same timers
(`Solution.SendsMore`). Then the two runs agree once the further fields are
forgotten (`Solution.states_forget`): the hosts observe the same events at
the same true times, hold the same frames and handle the same requests
(`Solution.views_forget`, `Solution.held_forget`, `Solution.handled_forget`,
`Solution.eventTime_forget`).

Everything that is proved about the messages of the plainer solution, such
as which block has arrived by the time of a request, therefore holds for
the richer one.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg Msg' : Type}

/-- What a host observes, with the payload of a message replaced by its
image under `π`. -/
def Observation.mapMsg (π : Msg' → Msg) : Observation H R Msg' → Observation H R Msg
  | .handed frames reported => .handed frames reported
  | .asked r outputs reported => .asked r outputs reported
  | .received i contents frames => .received i (π contents) frames
  | .timer => .timer

/-- Replacing a payload does not change the frames that an event brings. -/
theorem Observation.frames_mapMsg (π : Msg' → Msg) (obs : Observation H R Msg') :
    (obs.mapMsg π).frames = obs.frames := by
  cases obs <;> rfl

/-- An event, with the payload of its message replaced by its image under
`π`. -/
def Event.mapMsg (π : Msg' → Msg) (e : Event H R Msg') : Event H R Msg :=
  ⟨e.reading, e.observation.mapMsg π⟩

/-- A message in transit, with its payload replaced by its image under
`π`. -/
def InFlight.mapMsg (π : Msg' → Msg) (m : InFlight H Msg') : InFlight H Msg :=
  ⟨m.arrival, m.origin, m.destination, π m.contents, m.frames⟩

/-- The messages that an action sends, with their payloads replaced by their
images under `π`. -/
def mapSends (π : Msg' → Msg) (sends : List (H × Msg' × Finset ℕ)) :
    List (H × Msg × Finset ℕ) :=
  sends.map fun s => (s.1, π s.2.1, s.2.2)

/-- The solution `σ'` sends what the solution `σ` sends, with more in each
message: at every view, its messages with `π` applied to their payloads are
the messages that `σ` sends at the view with `π` applied to the payloads in
it, and it sets the same timers. -/
def Solution.SendsMore (σ' : Solution H R Msg') (σ : Solution H R Msg) (π : Msg' → Msg) :
    Prop :=
  ∀ (h : H) (v : List (Event H R Msg')),
    mapSends π (σ' h v).sends = (σ h (v.map (Event.mapMsg π))).sends
      ∧ (σ' h v).timers = (σ h (v.map (Event.mapMsg π))).timers

/-- A state of a run, with the payload of every message replaced by its
image under `π`. -/
def State.forget (π : Msg' → Msg) (st : State H R Msg') : State H R Msg where
  views := fun h => (st.views h).map (Event.mapMsg π)
  handedNext := st.handedNext
  askedNext := st.askedNext
  inFlight := st.inFlight.map (InFlight.mapMsg π)
  timers := st.timers
  sentCount := st.sentCount
  held := st.held
  plays := st.plays
  sent := st.sent

variable [DecidableEq H]

namespace State

variable (w : World H R) (π : Msg' → Msg)

theorem forget_send (st : State H R Msg') (h : H) (t : Time) (j : H) (c : Msg')
    (F : Finset ℕ) :
    (st.send w h t j c F).forget π = (st.forget π).send w h t j (π c) F := by
  unfold send forget
  cases w.network.deliver h j t (st.sentCount h j) <;> simp [InFlight.mapMsg]

theorem forget_sendAll (h : H) (t : Time) (held : Finset ℕ) :
    ∀ (sends : List (H × Msg' × Finset ℕ)) (st : State H R Msg'),
      (st.sendAll w h t held sends).forget π
        = (st.forget π).sendAll w h t held (mapSends π sends)
  | [], _ => rfl
  | s :: l, st => by
      have h1 := forget_sendAll h t held l
        (st.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held)))
      rw [forget_send] at h1
      exact h1

theorem forget_observe (st : State H R Msg') (h : H) (t : Time)
    (obs : Observation H R Msg') :
    (st.observe w h t obs).forget π = (st.forget π).observe w h t (obs.mapMsg π) := by
  have hv : (fun h' => (Function.update st.views h
        (st.views h ++ [⟨(w.clock h).read t, obs⟩]) h').map (Event.mapMsg π))
      = Function.update (fun h' => (st.views h').map (Event.mapMsg π)) h
        ((st.views h).map (Event.mapMsg π) ++ [⟨(w.clock h).read t, obs.mapMsg π⟩]) := by
    funext h'
    by_cases hh : h' = h
    · subst hh
      simp [Event.mapMsg]
    · simp [Function.update_of_ne hh]
  unfold observe forget
  simp only [hv, Observation.frames_mapMsg]

omit [DecidableEq H] in
theorem forget_addTimers (st : State H R Msg') (h : H) (t : Time) (cs : List ℝ) :
    (st.addTimers w h t cs).forget π = (st.forget π).addTimers w h t cs :=
  rfl

omit [DecidableEq H] in
theorem forget_withoutPlays (st : State H R Msg') :
    st.withoutPlays.forget π = (st.forget π).withoutPlays :=
  rfl

/-- Handling an event changes everything but what is played in the same way
for a solution and for one that sends more, once the further fields are
forgotten. -/
theorem forget_handle {σ' : Solution H R Msg'} {σ : Solution H R Msg}
    (hσ : σ'.SendsMore σ π) (lookahead : ℕ+) (st : State H R Msg') (h : H) (t : Time)
    (obs : Observation H R Msg') :
    ((st.handle σ' w lookahead h t obs).forget π).withoutPlays
      = ((st.forget π).handle σ w lookahead h t (obs.mapMsg π)).withoutPlays := by
  have hview : (st.views h ++ [(⟨(w.clock h).read t, obs⟩ : Event H R Msg')]).map
        (Event.mapMsg π)
      = (st.forget π).views h ++ [(⟨(w.clock h).read t, obs.mapMsg π⟩ : Event H R Msg)] := by
    simp [forget, Event.mapMsg]
  have hsends := hσ h (st.views h ++ [(⟨(w.clock h).read t, obs⟩ : Event H R Msg')])
  rw [hview] at hsends
  have hheld : (st.forget π).held h ∪ (obs.mapMsg π).frames = st.held h ∪ obs.frames := by
    rw [Observation.frames_mapMsg]
    rfl
  rw [← forget_withoutPlays, handle_withoutPlays_eq, handle_withoutPlays_eq, forget_withoutPlays,
    forget_addTimers, forget_sendAll, forget_withoutPlays, forget_observe, hsends.1, hsends.2,
    hheld]

theorem forget_key (st : State H R Msg') : (st.forget π).key w = st.key w := by
  funext d
  cases d with
  | handed b => rfl
  | asked r b => rfl
  | arrival p =>
    have harr : (InFlight.arrival ∘ InFlight.mapMsg π : InFlight H Msg' → Time)
        = InFlight.arrival := rfl
    have horig : ((fun m : InFlight H Msg => w.hostIndex m.origin) ∘ InFlight.mapMsg π :
        InFlight H Msg' → ℕ) = fun m => w.hostIndex m.origin := rfl
    simp [key, forget, harr, horig]
  | timer p => simp [key, forget]

omit [DecidableEq H] in
theorem forget_due (st : State H R Msg') : (st.forget π).due = st.due := by
  simp [due, forget]

/-- A step of the run changes everything but what is played in the same way
for a solution and for one that sends more, once the further fields are
forgotten. -/
theorem forget_step {σ' : Solution H R Msg'} {σ : Solution H R Msg}
    (hσ : σ'.SendsMore σ π) (lookahead : ℕ+) (st : State H R Msg') :
    ((st.step σ' w lookahead).forget π).withoutPlays
      = ((st.forget π).step σ w lookahead).withoutPlays := by
  unfold step
  rw [forget_key, forget_due]
  cases hearly : earliest (st.key w) st.due with
  | none => rfl
  | some d =>
    cases d with
    | handed b =>
      have h := forget_handle w π hσ lookahead st w.sender (w.source.handed b)
        (.handed ((w.source.block b).map fun n => (n, w.target n)) (w.source.reported b))
      exact congrArg (fun s : State H R Msg => ({ s with handedNext := b + 1 } : State H R Msg)) h
    | asked r b =>
      have h := forget_handle w π hσ lookahead st (w.host r) ((w.speaker r).asked b)
        (.asked r ((w.speaker r).block b) ((w.speaker r).reported b))
      exact congrArg (fun s : State H R Msg =>
        ({ s with askedNext := Function.update st.askedNext r (b + 1) } : State H R Msg)) h
    | arrival p =>
      dsimp only
      have hget : (st.forget π).inFlight[p]? = (st.inFlight[p]?).map (InFlight.mapMsg π) := by
        simp [forget]
      rw [hget]
      cases hm : st.inFlight[p]? with
      | none => rfl
      | some m =>
        have h := forget_handle w π hσ lookahead
          ({ st with inFlight := st.inFlight.eraseIdx p } : State H R Msg') m.destination
          m.arrival (.received m.origin m.contents m.frames)
        have he : ({ st with inFlight := st.inFlight.eraseIdx p } : State H R Msg').forget π
            = ({ st.forget π with
                inFlight := (st.forget π).inFlight.eraseIdx p } : State H R Msg) := by
          simp [forget, List.eraseIdx_map]
        rw [he] at h
        exact h
    | timer p =>
      dsimp only
      cases hu : st.timers[p]? with
      | none =>
        have hu' : (st.forget π).timers[p]? = none := hu
        rw [hu']
      | some u =>
        have hu' : (st.forget π).timers[p]? = some u := hu
        rw [hu']
        exact forget_handle w π hσ lookahead
          ({ st with timers := st.timers.eraseIdx p } : State H R Msg') u.host u.time .timer

end State

section Runs

variable (w : World H R) (π : Msg' → Msg) {σ' : Solution H R Msg'} {σ : Solution H R Msg}
  (lookahead : ℕ+)

/-- **A solution that sends more has the same run, once the further fields
are forgotten and apart from what the speakers play.** -/
theorem Solution.states_forget (hσ : σ'.SendsMore σ π) (n : ℕ) :
    ((σ'.states w lookahead n).forget π).withoutPlays
      = (σ.states w lookahead n).withoutPlays := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (State.forget_step w π hσ lookahead _).trans
      (State.step_withoutPlays w σ σ lookahead (fun _ _ => rfl) (fun _ _ => rfl) ih)

/-- The hosts of the two runs have the same views, once the further fields
are forgotten. -/
theorem Solution.views_forget (hσ : σ'.SendsMore σ π) (n : ℕ) (h : H) :
    ((σ'.states w lookahead n).views h).map (Event.mapMsg π)
      = (σ.states w lookahead n).views h :=
  congrFun (State.fields_of_withoutPlays_eq (Solution.states_forget w π lookahead hσ n)).1 h

/-- The hosts of the two runs hold the same frames. -/
theorem Solution.held_forget (hσ : σ'.SendsMore σ π) (n : ℕ) :
    (σ'.states w lookahead n).held = (σ.states w lookahead n).held :=
  (State.fields_of_withoutPlays_eq
    (Solution.states_forget w π lookahead hσ n)).2.2.2.2.2.2.1

theorem Solution.askedNext_forget (hσ : σ'.SendsMore σ π) (n : ℕ) :
    (σ'.states w lookahead n).askedNext = (σ.states w lookahead n).askedNext :=
  (State.fields_of_withoutPlays_eq (Solution.states_forget w π lookahead hσ n)).2.2.1

/-- The two runs have the same earliest pending event at every step, with
the same key. -/
theorem Solution.earliest_forget (hσ : σ'.SendsMore σ π) (n : ℕ) :
    (σ'.states w lookahead n).key w = (σ.states w lookahead n).key w
      ∧ earliest ((σ'.states w lookahead n).key w) (σ'.states w lookahead n).due
        = earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due := by
  obtain ⟨-, e1, e2, e3, e4, -, -, -⟩ :=
    State.fields_of_withoutPlays_eq (Solution.states_forget w π lookahead hσ n)
  have hkey : (σ'.states w lookahead n).key w = (σ.states w lookahead n).key w := by
    rw [← State.forget_key w π]
    funext d
    cases d <;> simp only [State.key, e3, e4]
  have hdue : (σ'.states w lookahead n).due = (σ.states w lookahead n).due := by
    rw [← State.forget_due π]
    simp only [State.due, e1, e2, e3, e4]
  exact ⟨hkey, by rw [hkey, hdue]⟩

/-- The two runs handle the same event at every step, once the further
fields are forgotten. -/
theorem Solution.handled_forget (hσ : σ'.SendsMore σ π) (n : ℕ) :
    (σ'.handled w lookahead n).map (fun x => (x.1, x.2.1, x.2.2.mapMsg π))
      = σ.handled w lookahead n := by
  obtain ⟨-, -, -, e3, e4, -, -, -⟩ :=
    State.fields_of_withoutPlays_eq (Solution.states_forget w π lookahead hσ n)
  unfold Solution.handled
  rw [(Solution.earliest_forget w π lookahead hσ n).2]
  cases earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due with
  | none => rfl
  | some d =>
    cases d with
    | handed b => rfl
    | asked r b => rfl
    | arrival p =>
      dsimp only
      rw [← e3]
      have hget : ((σ'.states w lookahead n).forget π).inFlight[p]?
          = ((σ'.states w lookahead n).inFlight[p]?).map (InFlight.mapMsg π) := by
        simp [State.forget]
      rw [hget]
      cases (σ'.states w lookahead n).inFlight[p]? <;> rfl
    | timer p =>
      dsimp only
      rw [← e4]
      change _ = Option.map (fun u : Timer H => (u.host, u.time, Observation.timer))
        (σ'.states w lookahead n).timers[p]?
      cases (σ'.states w lookahead n).timers[p]? <;> rfl

/-- The two runs handle their events at the same true times. -/
theorem Solution.eventTime_forget (hσ : σ'.SendsMore σ π) (n : ℕ) :
    σ'.eventTime w lookahead n = σ.eventTime w lookahead n := by
  obtain ⟨hkey, hearly⟩ := Solution.earliest_forget w π lookahead hσ n
  unfold Solution.eventTime
  rw [hearly, hkey]

end Runs

end Unisono.Spec
