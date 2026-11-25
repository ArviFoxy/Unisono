/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Limiter
public import Unisono.Spec.Held

/-!
# The events of its own devices in a host's view

A host observes the events of its own devices when they happen: the sender's
host observes each handover of the capture device, and the host of a speaker
observes each request of the speaker's playback device. Each observation
carries the reading of the host's clock at that moment.

These statements hold for every solution in every world:

* `Solution.handoversOf_views`: at every step of a run, the handovers in the
  sender's view are those of the blocks handed over so far, in order, each
  with the reading of the sender's clock when the block was handed over.
* `Solution.requestsOf_views`: the requests of speaker `r` in the view of
  its host are those made so far, in order, each with the reading of the
  host's clock when the request was made.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type}

/-- The event that the sender's host observes when the capture device hands
over block `b`. -/
def World.handedEvent (w : World H R) (b : ℕ) : Event H R Msg :=
  ⟨(w.clock w.sender).read (w.source.handed b),
    .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)⟩

/-- The number of frames of capture block `b`. -/
def World.blockLength (w : World H R) (b : ℕ) : ℕ := w.source.first (b + 1) - w.source.first b

/-- Every capture block has at least one frame. -/
theorem World.blockLength_pos (w : World H R) (b : ℕ) : 0 < w.blockLength b :=
  Nat.sub_pos_of_lt (w.source.first_strictMono (Nat.lt_succ_self b))

/-- The handovers in a view, oldest first: the events in which the capture
device hands over a block. -/
def handoversOf (l : List (Event H R Msg)) : List (Event H R Msg) :=
  l.filter fun e =>
    match e.observation with
    | .handed _ _ => true
    | _ => false

/-- The requests of the playback device of speaker `r` in a view, oldest
first. -/
def requestsOf (r : Fin R) (l : List (Event H R Msg)) : List (Event H R Msg) :=
  l.filter fun e =>
    match e.observation with
    | .asked r' _ _ => decide (r' = r)
    | _ => false

theorem handoversOf_append (l l' : List (Event H R Msg)) :
    handoversOf (l ++ l') = handoversOf l ++ handoversOf l' := by
  simp [handoversOf]

theorem requestsOf_append (r : Fin R) (l l' : List (Event H R Msg)) :
    requestsOf r (l ++ l') = requestsOf r l ++ requestsOf r l' := by
  simp [requestsOf]

variable [DecidableEq H] (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)

/-- **The handovers in the sender's view are those of the blocks handed
over so far**, in order, each with the reading of the sender's clock when
the block was handed over. This holds at every step of the run of every
solution in every world. -/
theorem Solution.handoversOf_views (n : ℕ) :
    handoversOf ((σ.states w lookahead n).views w.sender)
      = (List.range (σ.states w lookahead n).handedNext).map w.handedEvent := by
  induction n with
  | zero => simp [Solution.states, State.start, handoversOf]
  | succ n ih =>
    rw [σ.views_succ w lookahead n w.sender, handoversOf_append, ih]
    cases hE : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due with
    | none =>
      have hh : σ.handled w lookahead n = none := by
        unfold Solution.handled
        rw [hE]
      have hnext : (σ.states w lookahead (n + 1)).handedNext
          = (σ.states w lookahead n).handedNext := by
        rcases State.step_handedNext w σ lookahead (σ.states w lookahead n) with h | ⟨-, h⟩
        · exact h
        · rw [hE] at h
          simp at h
      rw [hh, hnext]
      simp [handoversOf]
    | some d =>
      cases d with
      | handed b =>
        have hh := σ.handled_of_handed w lookahead hE
        obtain ⟨h1, h2⟩ := σ.handedNext_of_earliest w lookahead hE
        rw [hh, h1, h2, List.range_succ, List.map_append]
        simp [handoversOf, World.handedEvent]
      | asked r b =>
        have hh : σ.handled w lookahead n = some (w.host r, (w.speaker r).asked b,
            .asked r ((w.speaker r).block b) ((w.speaker r).reported b)) := by
          unfold Solution.handled
          rw [hE]
        have hnext : (σ.states w lookahead (n + 1)).handedNext
            = (σ.states w lookahead n).handedNext := by
          rcases State.step_handedNext w σ lookahead (σ.states w lookahead n) with h | ⟨-, h⟩
          · exact h
          · rw [hE] at h
            simp at h
        rw [hh, hnext]
        by_cases hs : w.sender = w.host r <;> simp [handoversOf, hs]
      | arrival q =>
        have hnext : (σ.states w lookahead (n + 1)).handedNext
            = (σ.states w lookahead n).handedNext := by
          rcases State.step_handedNext w σ lookahead (σ.states w lookahead n) with h | ⟨-, h⟩
          · exact h
          · rw [hE] at h
            simp at h
        rw [hnext]
        cases hm : (σ.states w lookahead n).inFlight[q]? with
        | none =>
          have hh : σ.handled w lookahead n = none := by
            unfold Solution.handled
            rw [hE]
            simp [hm]
          rw [hh]
          simp [handoversOf]
        | some msg =>
          have hh : σ.handled w lookahead n = some (msg.destination, msg.arrival,
              .received msg.origin msg.contents msg.frames) := by
            unfold Solution.handled
            rw [hE]
            simp [hm]
          rw [hh]
          by_cases hs : w.sender = msg.destination <;> simp [handoversOf, hs]
      | timer q =>
        have hnext : (σ.states w lookahead (n + 1)).handedNext
            = (σ.states w lookahead n).handedNext := by
          rcases State.step_handedNext w σ lookahead (σ.states w lookahead n) with h | ⟨-, h⟩
          · exact h
          · rw [hE] at h
            simp at h
        rw [hnext]
        cases hm : (σ.states w lookahead n).timers[q]? with
        | none =>
          have hh : σ.handled w lookahead n = none := by
            unfold Solution.handled
            rw [hE]
            simp [hm]
          rw [hh]
          simp [handoversOf]
        | some u =>
          have hh : σ.handled w lookahead n = some (u.host, u.time, .timer) := by
            unfold Solution.handled
            rw [hE]
            simp [hm]
          rw [hh]
          by_cases hs : w.sender = u.host <;> simp [handoversOf, hs]

/-- **The requests of a speaker's device in the view of its host are those
made so far**, in order, each with the reading of the host's clock when the
request was made. This holds at every step of the run of every solution in
every world. -/
theorem Solution.requestsOf_views (r : Fin R) (n : ℕ) :
    requestsOf r ((σ.states w lookahead n).views (w.host r))
      = (List.range ((σ.states w lookahead n).askedNext r)).map (w.askedEvent r) := by
  induction n with
  | zero => simp [Solution.states, State.start, requestsOf]
  | succ n ih =>
    rw [σ.views_succ w lookahead n (w.host r), requestsOf_append, ih]
    have hsame : ∀ {d : Due R}, earliest ((σ.states w lookahead n).key w)
          (σ.states w lookahead n).due = some d → (∀ b, d ≠ .asked r b) →
        (σ.states w lookahead (n + 1)).askedNext r = (σ.states w lookahead n).askedNext r := by
      intro d hd hne
      rcases State.step_askedNext w σ lookahead (σ.states w lookahead n) r with h | ⟨-, h⟩
      · exact h
      · rw [hd] at h
        exact absurd (Option.some.inj h) (hne _)
    cases hE : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due with
    | none =>
      have hh : σ.handled w lookahead n = none := by
        unfold Solution.handled
        rw [hE]
      have hnext : (σ.states w lookahead (n + 1)).askedNext r
          = (σ.states w lookahead n).askedNext r := by
        rcases State.step_askedNext w σ lookahead (σ.states w lookahead n) r with h | ⟨-, h⟩
        · exact h
        · rw [hE] at h
          simp at h
      rw [hh, hnext]
      simp [requestsOf]
    | some d =>
      cases d with
      | handed b =>
        have hh := σ.handled_of_handed w lookahead hE
        rw [hh, hsame hE (by simp)]
        by_cases hs : w.host r = w.sender <;> simp [requestsOf, hs]
      | asked r' b =>
        have hh : σ.handled w lookahead n = some (w.host r', (w.speaker r').asked b,
            .asked r' ((w.speaker r').block b) ((w.speaker r').reported b)) := by
          unfold Solution.handled
          rw [hE]
        by_cases hr : r' = r
        · subst hr
          have hmem := (earliest_spec _ _ _ hE).1
          have hb : b = (σ.states w lookahead n).askedNext r' := by
            rcases (σ.states w lookahead n).mem_due hmem with h | ⟨r'', h⟩ | ⟨q, _, h⟩ | ⟨q, _, h⟩
            · simp at h
            · simp only [Due.asked.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rfl
            · simp at h
            · simp at h
          subst hb
          rw [hh, σ.askedNext_succ w lookahead hE, List.range_succ, List.map_append]
          simp [requestsOf, World.askedEvent]
        · rw [hh, hsame hE (by
            intro b' hb'
            simp only [Due.asked.injEq] at hb'
            exact hr hb'.1)]
          by_cases hs : w.host r = w.host r' <;> simp [requestsOf, hs, hr]
      | arrival q =>
        rw [hsame hE (by simp)]
        cases hm : (σ.states w lookahead n).inFlight[q]? with
        | none =>
          have hh : σ.handled w lookahead n = none := by
            unfold Solution.handled
            rw [hE]
            simp [hm]
          rw [hh]
          simp [requestsOf]
        | some msg =>
          have hh : σ.handled w lookahead n = some (msg.destination, msg.arrival,
              .received msg.origin msg.contents msg.frames) := by
            unfold Solution.handled
            rw [hE]
            simp [hm]
          rw [hh]
          by_cases hs : w.host r = msg.destination <;> simp [requestsOf, hs]
      | timer q =>
        rw [hsame hE (by simp)]
        cases hm : (σ.states w lookahead n).timers[q]? with
        | none =>
          have hh : σ.handled w lookahead n = none := by
            unfold Solution.handled
            rw [hE]
            simp [hm]
          rw [hh]
          simp [requestsOf]
        | some u =>
          have hh : σ.handled w lookahead n = some (u.host, u.time, .timer) := by
            unfold Solution.handled
            rw [hE]
            simp [hm]
          rw [hh]
          by_cases hs : w.host r = u.host <;> simp [requestsOf, hs]

open Classical in
/-- The sender's view when it handles the handover of block `b`, with that
handover as its last event; the empty list if the run never handles the
handover. -/
def Solution.handoverView (b : ℕ) : List (Event H R Msg) :=
  if h : ∃ i, σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))
  then (σ.states w lookahead (Classical.choose h)).views w.sender ++ [w.handedEvent b]
  else []

/-- At a step that handles the handover of block `b`, the sender's view
with the handover is `handoverView b`. -/
theorem Solution.handoverView_eq {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    σ.handoverView w lookahead b
      = (σ.states w lookahead i).views w.sender ++ [w.handedEvent b] := by
  classical
  have hex : ∃ i, σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)) :=
    ⟨i, hi⟩
  have hu : Classical.choose hex = i := σ.handed_step_unique w lookahead
    (σ.earliest_of_handled_handed w lookahead (Classical.choose_spec hex))
    (σ.earliest_of_handled_handed w lookahead hi)
  unfold Solution.handoverView
  rw [dite_eq_left hex, hu]

/-- **Between two consecutive handovers the sender observes no handover.**
When the run handles the handovers of blocks `b` and `b + 1`, the sender's
view at the later one is its view at the earlier one, followed by events
that are not handovers, followed by the handover of block `b + 1`. -/
theorem Solution.handoverView_succ {i i' b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (hi' : σ.handled w lookahead i' = some (w.sender, w.source.handed (b + 1),
      .handed ((w.source.block (b + 1)).map fun k => (k, w.target k))
        (w.source.reported (b + 1)))) :
    ∃ mid : List (Event H R Msg),
      σ.handoverView w lookahead (b + 1)
        = σ.handoverView w lookahead b ++ mid ++ [w.handedEvent (b + 1)]
      ∧ ∀ e ∈ mid, ∀ frames stamp, e.observation ≠ .handed frames stamp := by
  rw [σ.handoverView_eq w lookahead hi, σ.handoverView_eq w lookahead hi']
  have hE := σ.earliest_of_handled_handed w lookahead hi
  have hE' := σ.earliest_of_handled_handed w lookahead hi'
  obtain ⟨hn1, hn2⟩ := σ.handedNext_of_earliest w lookahead hE
  obtain ⟨hn1', -⟩ := σ.handedNext_of_earliest w lookahead hE'
  have hmono := σ.handedNext_mono w lookahead
  have hlt : i < i' := by
    by_contra hcon
    have h1 := hmono (not_lt.mp hcon)
    simp only at h1
    omega
  have hV1 : (σ.states w lookahead (i + 1)).views w.sender
      = (σ.states w lookahead i).views w.sender ++ [w.handedEvent b] := by
    rw [σ.views_succ w lookahead i w.sender, hi]
    simp [World.handedEvent]
  obtain ⟨mid, hmid, hev⟩ := Solution.views_append w σ lookahead
    (show i + 1 ≤ i' from hlt) w.sender
  refine ⟨mid, by rw [hmid, hV1], ?_⟩
  intro e he frames stamp hobs
  obtain ⟨j, hij, hji', t, obs, hj, rfl⟩ := hev e he
  dsimp only at hobs
  subst hobs
  obtain ⟨b', -, rfl, -, -⟩ := Solution.handled_handed w σ lookahead hj
  have hEj := σ.earliest_of_handled_handed w lookahead hj
  obtain ⟨hj1, hj2⟩ := σ.handedNext_of_earliest w lookahead hEj
  have h1 := hmono hij
  have h2 := hmono (show j + 1 ≤ i' from hji')
  simp only at h1 h2
  omega

/-- At the step that handles a request of speaker `r`'s device, the
requested block is the speaker's next block. -/
theorem Solution.askedNext_of_earliest {n : ℕ} {r : Fin R} {β : ℕ}
    (hE : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r β)) :
    (σ.states w lookahead n).askedNext r = β := by
  have hmem := (earliest_spec _ _ _ hE).1
  rcases (σ.states w lookahead n).mem_due hmem with h | ⟨r'', h⟩ | ⟨q, _, h⟩ | ⟨q, _, h⟩
  · simp at h
  · simp only [Due.asked.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp at h
  · simp at h

/-- **The requests in a host's view at a request.** At the step that handles
the request of block `β` of speaker `r`, the requests of that speaker's
device in the host's view, with the request being handled, are those of
blocks zero to `β`, in order. -/
theorem Solution.requestsOf_request {n : ℕ} {r : Fin R} {β : ℕ}
    (hE : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r β)) :
    requestsOf r ((σ.states w lookahead n).views (w.host r) ++ [w.askedEvent r β])
      = (List.range (β + 1)).map (w.askedEvent r) := by
  rw [requestsOf_append, σ.requestsOf_views w lookahead r n,
    σ.askedNext_of_earliest w lookahead hE, List.range_succ, List.map_append]
  simp [requestsOf, World.askedEvent]

/-- **The handovers in the sender's view at a handover.** When the run
handles the handover of block `b`, the handovers in the sender's view, with
the handover being handled, are those of blocks zero to `b`, in order. -/
theorem Solution.handoversOf_handoverView {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    handoversOf (σ.handoverView w lookahead b) = (List.range (b + 1)).map w.handedEvent := by
  have hE := σ.earliest_of_handled_handed w lookahead hi
  obtain ⟨hn, -⟩ := σ.handedNext_of_earliest w lookahead hE
  rw [σ.handoverView_eq w lookahead hi, handoversOf_append, σ.handoversOf_views w lookahead i,
    hn, List.range_succ, List.map_append]
  simp [handoversOf, World.handedEvent]

open Classical in
/-- The view of the host of speaker `r` when it handles the request of
block `β`, with that request as its last event; the empty list if the run
never handles the request. -/
def Solution.requestView (r : Fin R) (β : ℕ) : List (Event H R Msg) :=
  if h : ∃ n, earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r β)
  then (σ.states w lookahead (Classical.choose h)).views (w.host r) ++ [w.askedEvent r β]
  else []

/-- At a step that handles the request of block `β` of speaker `r`, the
host's view with the request is `requestView r β`. -/
theorem Solution.requestView_eq {n : ℕ} {r : Fin R} {β : ℕ}
    (hE : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r β)) :
    σ.requestView w lookahead r β
      = (σ.states w lookahead n).views (w.host r) ++ [w.askedEvent r β] := by
  classical
  have hex : ∃ n, earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r β) := ⟨n, hE⟩
  have hu : Classical.choose hex = n :=
    σ.asked_step_unique w lookahead
      (σ.askedNext_of_earliest w lookahead (Classical.choose_spec hex))
      (Classical.choose_spec hex) (σ.askedNext_of_earliest w lookahead hE) hE
  unfold Solution.requestView
  rw [dite_eq_left hex, hu]

end Unisono.Spec
