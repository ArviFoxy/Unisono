/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Checks

/-!
# Facts about the run of any solution

What the run of every solution satisfies, used to prove what a particular
solution achieves.

* Every host keeps the frames it holds (`Solution.held_mono`).
* A message in transit that arrives before the event of a later step has
  been handled by that step, so its destination holds its frames
  (`Solution.frames_arrive`).
* The messages a host sends at an event are numbered on each link in the
  order of its sends, and each one that the network delivers is in transit
  after the event (`State.sendAll_delivered`).
* A block handed over before some event of the run was handed over at an
  earlier step, at which its handoff was the earliest pending event
  (`Solution.lt_handedNext`, `Solution.exists_handed_step`).
* A message that a host's action sends while it handles an event, and that
  the network delivers, is in transit after the event
  (`State.handle_delivered`).
* At each step the host that handles the event adds it to its view, with its
  clock's reading, and every other view stays as it was
  (`Solution.handled`, `Solution.views_succ`).
* A message in transit after a step was in transit before it, or was sent
  by the host that handled the step's event and delivered by the network
  (`Solution.mem_inFlight_succ`).
* A handled handoff is the handoff of a block, and a handled arrival is the
  arrival of a message in transit (`Solution.handled_handed`,
  `Solution.handled_received`).
* A message in transit that arrives before the event of a later step is
  handled at a step between them (`Solution.handled_before`), and a host's
  view holds exactly the events it handled before, each with its clock's
  reading (`Solution.mem_views_of_handled`, `Solution.handled_of_mem_views`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type}

namespace State

variable [DecidableEq H] (w : World H R) (st : State H R Msg)

theorem send_held (h : H) (t : Time) (j : H) (c : Msg) (F : Finset ℕ) :
    (st.send w h t j c F).held = st.held := rfl

theorem sendAll_held (h : H) (t : Time) (held : Finset ℕ) (sends : List (H × Msg × Finset ℕ)) :
    (st.sendAll w h t held sends).held = st.held := by
  induction sends generalizing st with
  | nil => rfl
  | cons m l ih => exact ih (st.send w h t m.1 m.2.1 (m.2.2.filter (· ∈ held)))

theorem sendAll_inFlight_mem {h : H} {t : Time} {held : Finset ℕ}
    {sends : List (H × Msg × Finset ℕ)} {m : InFlight H Msg} (hm : m ∈ st.inFlight) :
    m ∈ (st.sendAll w h t held sends).inFlight := by
  induction sends generalizing st with
  | nil => exact hm
  | cons s l ih =>
    refine ih (st.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held))) ?_
    simp only [send]
    split
    · exact List.mem_append_left _ hm
    · exact hm

/-- A host that handles an event keeps every frame it held and adds the
frames that the event delivers. -/
theorem handle_held (σ : Solution H R Msg) (lookahead : ℕ+) (h : H) (t : Time)
    (obs : Observation H R Msg) (h' : H) :
    (st.handle σ w lookahead h t obs).held h' =
      if h' = h then st.held h ∪ obs.frames else st.held h' := by
  simp only [handle, sendAll_held]
  by_cases hh : h' = h
  · subst hh
    simp
  · simp [hh]

theorem handle_inFlight_mem (σ : Solution H R Msg) (lookahead : ℕ+) {h : H} {t : Time}
    {obs : Observation H R Msg} {m : InFlight H Msg} (hm : m ∈ st.inFlight) :
    m ∈ (st.handle σ w lookahead h t obs).inFlight := by
  simp only [handle]
  exact sendAll_inFlight_mem w _ hm

theorem held_subset_handle (σ : Solution H R Msg) (lookahead : ℕ+) (h : H) (t : Time)
    (obs : Observation H R Msg) (h' : H) :
    st.held h' ⊆ (st.handle σ w lookahead h t obs).held h' := by
  rw [handle_held]
  split_ifs with hh
  · subst hh
    exact Finset.subset_union_left
  · exact le_rfl

/-- A step of the run keeps every frame that each host holds. -/
theorem held_subset_step (σ : Solution H R Msg) (lookahead : ℕ+) (h' : H) :
    st.held h' ⊆ (st.step σ w lookahead).held h' := by
  unfold step
  split
  · exact held_subset_handle w st σ lookahead _ _ _ h'
  · exact held_subset_handle w st σ lookahead _ _ _ h'
  · split
    · refine Finset.Subset.trans ?_ (held_subset_handle w _ σ lookahead _ _ _ h')
      exact Finset.Subset.refl _
    · exact le_rfl
  · split
    · refine Finset.Subset.trans ?_ (held_subset_handle w _ σ lookahead _ _ _ h')
      exact Finset.Subset.refl _
    · exact le_rfl
  · exact le_rfl

/-- At each step of the run, a message in transit either stays in transit,
or the step handles it and its destination then holds its frames. -/
theorem step_inFlight (σ : Solution H R Msg) (lookahead : ℕ+) {m : InFlight H Msg}
    (hm : m ∈ st.inFlight) :
    m ∈ (st.step σ w lookahead).inFlight ∨ m.frames ⊆ (st.step σ w lookahead).held m.destination := by
  unfold step
  split
  · exact Or.inl (handle_inFlight_mem w st σ lookahead hm)
  · exact Or.inl (handle_inFlight_mem w st σ lookahead hm)
  · rename_i p _
    split
    · rename_i m' hm'
      by_cases hin : m ∈ st.inFlight.eraseIdx p
      · exact Or.inl (handle_inFlight_mem w _ σ lookahead hin)
      · right
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
        have hip : i = p := by
          by_contra hne
          exact hin (List.mem_eraseIdx_iff_getElem.mpr ⟨i, hi, hne, rfl⟩)
        subst hip
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hm'
        subst hm'
        rw [handle_held]
        simp [Observation.frames]
    · exact Or.inl hm
  · split
    · exact Or.inl (handle_inFlight_mem w _ σ lookahead hm)
    · exact Or.inl hm
  · exact Or.inl hm

end State

variable [DecidableEq H]

/-- **Every host keeps the frames it holds.** -/
theorem Solution.held_mono (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (h : H)
    {n k : ℕ} (hnk : n ≤ k) : (σ.states w lookahead n).held h ⊆ (σ.states w lookahead k).held h := by
  induction hnk with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (State.held_subset_step w _ σ lookahead h)

/-- **A message is handled before any later event.** If a message in transit
at step `n` arrives before the event of a later step `k`, it has been
handled by step `k`, so its destination holds its frames. -/
theorem Solution.frames_arrive (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {n k : ℕ} {m : InFlight H Msg} (hm : m ∈ (σ.states w lookahead n).inFlight) (hnk : n ≤ k)
    (harr : m.arrival < σ.eventTime w lookahead k) :
    m.frames ⊆ (σ.states w lookahead k).held m.destination := by
  have hinv : ∀ j, n ≤ j → m ∈ (σ.states w lookahead j).inFlight ∨
      m.frames ⊆ (σ.states w lookahead j).held m.destination := by
    intro j hj
    induction hj with
    | refl => exact Or.inl hm
    | step _ ih =>
      rcases ih with hin | hheld
      · exact State.step_inFlight w _ σ lookahead hin
      · exact Or.inr (hheld.trans (State.held_subset_step w _ σ lookahead _))
  rcases hinv k hnk with hin | hheld
  · have := (σ.eventTime_dueFrom w lookahead k).2.2.1 m hin
    exact absurd harr (not_lt.mpr this)
  · exact hheld

end Unisono.Spec

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] (w : World H R)

namespace State

theorem send_sentCount (st : State H R Msg) (h : H) (t : Time) (j : H) (c : Msg)
    (F : Finset ℕ) (j' : H) :
    (st.send w h t j c F).sentCount h j' = st.sentCount h j' + if j' = j then 1 else 0 := by
  simp only [send]
  by_cases hj : j' = j
  · subst hj
    simp
  · simp [hj]

/-- **The messages a host sends at an event, and their delivery.** Let the
`i`-th entry of `sends` go to host `j`. Its number on the link from the host
to `j` is `st.sentCount h j` plus the number of earlier entries to `j`. If
the network delivers the message, it is in transit after the event,
carrying those of its frames that the host holds. -/
theorem sendAll_delivered {h : H} {t : Time} {held : Finset ℕ} :
    ∀ (sends : List (H × Msg × Finset ℕ)) (st : State H R Msg) (i : ℕ) (hi : i < sends.length)
      {arr : Time},
      w.network.deliver h sends[i].1 t
          (st.sentCount h sends[i].1 + (sends.take i).countP (fun s => s.1 = sends[i].1))
        = some arr →
      (⟨arr, h, sends[i].1, sends[i].2.1, sends[i].2.2.filter (· ∈ held)⟩ : InFlight H Msg)
        ∈ (st.sendAll w h t held sends).inFlight
  | [], _, i, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | s :: l, st, 0, _, arr, hdel => by
      simp only [List.getElem_cons_zero, List.take_zero, List.countP_nil, add_zero] at hdel
      show _ ∈ ((st.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held))).sendAll w h t held l).inFlight
      apply sendAll_inFlight_mem
      simp only [send, hdel]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  | s :: l, st, i + 1, hi, arr, hdel => by
      have hi' : i < l.length := by simpa using hi
      simp only [List.getElem_cons_succ, List.take_succ_cons, List.countP_cons] at hdel ⊢
      show _ ∈ ((st.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held))).sendAll w h t held l).inFlight
      refine sendAll_delivered l _ i hi' ?_
      rw [send_sentCount]
      convert hdel using 2
      by_cases hs : l[i].1 = s.1
      · simp only [hs, ite_true, decide_true]
        omega
      · simp only [hs, Ne.symm hs, ite_false, decide_false, Bool.false_eq_true]
        omega

end State

end Unisono.Spec

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] (w : World H R)

namespace State

theorem handle_handedNext (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg) (h : H)
    (t : Time) (obs : Observation H R Msg) :
    (st.handle σ w lookahead h t obs).handedNext = st.handedNext := by
  simp only [handle, sendAll_handedNext]

/-- A step of the run either leaves the next block to be handed over
unchanged, or hands that block over and moves on to the following one. -/
theorem step_handedNext (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg) :
    (st.step σ w lookahead).handedNext = st.handedNext ∨
      ((st.step σ w lookahead).handedNext = st.handedNext + 1 ∧
        earliest (st.key w) st.due = some (.handed st.handedNext)) := by
  unfold step
  split
  · rename_i b hb
    have hmem := (earliest_spec _ _ _ hb).1
    have hbn : b = st.handedNext := by
      rcases st.mem_due hmem with h | ⟨r, h⟩ | ⟨p, _, h⟩ | ⟨p, _, h⟩ <;> simp_all
    subst hbn
    exact Or.inr ⟨rfl, hb⟩
  · exact Or.inl (handle_handedNext w σ lookahead _ _ _ _)
  · split
    · exact Or.inl (handle_handedNext w σ lookahead _ _ _ _)
    · exact Or.inl rfl
  · split
    · exact Or.inl (handle_handedNext w σ lookahead _ _ _ _)
    · exact Or.inl rfl
  · exact Or.inl rfl

end State

/-- If block `b` is handed over before the event of step `n`, the run has
handed it over by step `n` (`b < handedNext`). -/
theorem Solution.lt_handedNext (σ : Solution H R Msg) (lookahead : ℕ+) {n b : ℕ}
    (h : w.source.handed b < σ.eventTime w lookahead n) :
    b < (σ.states w lookahead n).handedNext := by
  by_contra hle
  have h1 := w.source.handed_mono (not_lt.mp hle)
  have h2 := (σ.eventTime_dueFrom w lookahead n).1
  linarith

/-- **The step at which a block is handed over.** When the run has handed
over block `b` by step `m`, it did so at a step `n` before `m`, at which the
earliest pending event was the handoff of block `b`. -/
theorem Solution.exists_handed_step (σ : Solution H R Msg) (lookahead : ℕ+) {m b : ℕ}
    (h : b < (σ.states w lookahead m).handedNext) :
    ∃ n < m, (σ.states w lookahead n).handedNext = b ∧
      earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due = some (.handed b) := by
  induction m with
  | zero => exact absurd h (Nat.not_lt_zero b)
  | succ m ih =>
    by_cases hm : b < (σ.states w lookahead m).handedNext
    · obtain ⟨n, hn, h1, h2⟩ := ih hm
      exact ⟨n, Nat.lt_succ_of_lt hn, h1, h2⟩
    · rcases State.step_handedNext w σ lookahead (σ.states w lookahead m) with heq | ⟨heq, hearly⟩
      · exact absurd (heq ▸ h) hm
      · have hb : (σ.states w lookahead m).handedNext = b := by
          have : (σ.states w lookahead (m + 1)).handedNext = (σ.states w lookahead m).handedNext + 1 := heq
          omega
        exact ⟨m, Nat.lt_succ_self m, hb, hb ▸ hearly⟩

/-- A message that a host's action sends while it handles an event, and that
the network delivers, is in transit after the event. -/
theorem State.handle_delivered {Msg : Type} (w : World H R) (σ : Solution H R Msg) (lookahead : ℕ+)
    (st : State H R Msg) (h : H) (t : Time) (obs : Observation H R Msg) (i : ℕ)
    (hi : i < (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends.length) {arr : Time}
    (hdel : w.network.deliver h (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends[i].1 t
      (st.sentCount h (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends[i].1
        + ((σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends.take i).countP
          (fun s => s.1 = (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends[i].1))
      = some arr) :
    (⟨arr, h, (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends[i].1,
      (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends[i].2.1,
      (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends[i].2.2.filter
        (· ∈ st.held h ∪ obs.frames)⟩ : InFlight H Msg)
      ∈ (st.handle σ w lookahead h t obs).inFlight := by
  simp only [State.handle]
  exact State.sendAll_delivered w _ _ i hi hdel

/-- The event that the run handles at its step `n`: the host, the true time,
and what the host observes; `none` when there is nothing to handle. -/
noncomputable def Solution.handled (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (n : ℕ) :
    Option (H × Time × Observation H R Msg) :=
  match earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due with
  | some (.handed b) => some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun m => (m, w.target m)) (w.source.reported b))
  | some (.asked r b) => some (w.host r, (w.speaker r).asked b,
      .asked r ((w.speaker r).block b) ((w.speaker r).reported b))
  | some (.arrival p) => (σ.states w lookahead n).inFlight[p]?.map fun m =>
      (m.destination, m.arrival, .received m.origin m.contents m.frames)
  | some (.timer p) => (σ.states w lookahead n).timers[p]?.map fun u => (u.host, u.time, .timer)
  | none => none

namespace State

variable (w : World H R)

theorem sendAll_views (st : State H R Msg) (h : H) (t : Time) (held : Finset ℕ)
    (sends : List (H × Msg × Finset ℕ)) :
    (st.sendAll w h t held sends).views = st.views := by
  induction sends generalizing st with
  | nil => rfl
  | cons m l ih => exact ih (st.send w h t m.1 m.2.1 (m.2.2.filter (· ∈ held)))

theorem handle_views (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg) (h : H)
    (t : Time) (obs : Observation H R Msg) (h' : H) :
    (st.handle σ w lookahead h t obs).views h'
      = st.views h' ++ if h' = h then [⟨(w.clock h).read t, obs⟩] else [] := by
  simp only [handle, sendAll_views]
  by_cases hh : h' = h
  · subst hh
    simp
  · simp [hh]

end State

/-- **A host's view grows by the event it handles.** At each step of the
run, the view of the host that handles the event gains the event, with its
clock's reading, and every other view stays as it was. -/
theorem Solution.views_succ (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (n : ℕ)
    (h : H) :
    (σ.states w lookahead (n + 1)).views h = (σ.states w lookahead n).views h ++
      match σ.handled w lookahead n with
      | some (h', t, obs) => if h = h' then [⟨(w.clock h').read t, obs⟩] else []
      | none => [] := by
  show ((σ.states w lookahead n).step σ w lookahead).views h = _
  unfold State.step Solution.handled
  split
  · rename_i b hb
    simp only [hb, State.handle_views]
  · rename_i r b hb
    simp only [hb, State.handle_views]
  · rename_i p hp
    simp only [hp]
    split
    · rename_i m hm
      simp only [hm, Option.map_some, State.handle_views]
    · rename_i hm
      simp [hm]
  · rename_i p hp
    simp only [hp]
    split
    · rename_i u hu
      simp only [hu, Option.map_some, State.handle_views]
    · rename_i hu
      simp [hu]
  · rename_i hnone
    simp [hnone]

section Provenance

variable (w : World H R)

namespace State

/-- A message in transit after a host sends at an event was in transit
before, or is one of the host's sends that the network delivered. -/
theorem mem_sendAll_inFlight {h : H} {t : Time} {held : Finset ℕ} :
    ∀ (sends : List (H × Msg × Finset ℕ)) (st : State H R Msg) {m : InFlight H Msg},
      m ∈ (st.sendAll w h t held sends).inFlight →
      m ∈ st.inFlight ∨ ∃ s ∈ sends, m.origin = h ∧ m.destination = s.1 ∧ m.contents = s.2.1 ∧
        m.frames = s.2.2.filter (· ∈ held) ∧ ∃ q, w.network.deliver h s.1 t q = some m.arrival
  | [], _, _, hm => Or.inl hm
  | s :: l, st, m, hm => by
      rcases mem_sendAll_inFlight l (st.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held))) hm with
        hm' | ⟨s', hs', h1, h2, h3, h4, h5⟩
      · simp only [send] at hm'
        split at hm'
        · rename_i arr harr
          rcases List.mem_append.mp hm' with hold | hnew
          · exact Or.inl hold
          · right
            rw [List.mem_singleton] at hnew
            subst hnew
            exact ⟨s, List.mem_cons_self .., rfl, rfl, rfl, rfl, _, harr⟩
        · exact Or.inl hm'
      · exact Or.inr ⟨s', List.mem_cons_of_mem _ hs', h1, h2, h3, h4, h5⟩

/-- A message in transit after a host handles an event was in transit
before, or is one of the sends of the host's action that the network
delivered. -/
theorem mem_handle_inFlight (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg)
    (h : H) (t : Time) (obs : Observation H R Msg) {m : InFlight H Msg}
    (hm : m ∈ (st.handle σ w lookahead h t obs).inFlight) :
    m ∈ st.inFlight ∨ ∃ s ∈ (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends,
      m.origin = h ∧ m.destination = s.1 ∧ m.contents = s.2.1 ∧
      m.frames = s.2.2.filter (· ∈ st.held h ∪ obs.frames) ∧
      ∃ q, w.network.deliver h s.1 t q = some m.arrival := by
  simp only [handle] at hm
  have := mem_sendAll_inFlight w _ _ hm
  exact this

end State

/-- **Where a message in transit comes from.** A message in transit after a
step of the run was in transit before it, or was sent by the host that
handled the step's event, as one of the sends of its action, and delivered
by the network. -/
theorem Solution.mem_inFlight_succ (σ : Solution H R Msg) (lookahead : ℕ+) (n : ℕ)
    {m : InFlight H Msg} (hm : m ∈ (σ.states w lookahead (n + 1)).inFlight) :
    m ∈ (σ.states w lookahead n).inFlight ∨
      ∃ h t obs, σ.handled w lookahead n = some (h, t, obs) ∧
        ∃ s ∈ (σ h ((σ.states w lookahead n).views h ++ [⟨(w.clock h).read t, obs⟩])).sends,
          m.origin = h ∧ m.destination = s.1 ∧ m.contents = s.2.1 ∧
          m.frames = s.2.2.filter (· ∈ (σ.states w lookahead n).held h ∪ obs.frames) ∧
          ∃ q, w.network.deliver h s.1 t q = some m.arrival := by
  change m ∈ ((σ.states w lookahead n).step σ w lookahead).inFlight at hm
  unfold State.step at hm
  unfold Solution.handled
  split at hm
  · rename_i b hb
    rw [hb]
    rcases State.mem_handle_inFlight w σ lookahead _ _ _ _ hm with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_, _, _, rfl, h⟩
  · rename_i r b hb
    rw [hb]
    rcases State.mem_handle_inFlight w σ lookahead _ _ _ _ hm with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_, _, _, rfl, h⟩
  · rename_i p hp
    rw [hp]
    split at hm
    · rename_i m' hm'
      simp only [hm', Option.map_some]
      rcases State.mem_handle_inFlight w σ lookahead _ _ _ _ hm with h | h
      · exact Or.inl (List.mem_of_mem_eraseIdx h)
      · exact Or.inr ⟨_, _, _, rfl, h⟩
    · exact Or.inl hm
  · rename_i p hp
    rw [hp]
    split at hm
    · rename_i u hu
      simp only [hu, Option.map_some]
      rcases State.mem_handle_inFlight w σ lookahead _ _ _ _ hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨_, _, _, rfl, h⟩
    · exact Or.inl hm
  · exact Or.inl hm

end Provenance

section Handled

variable (w : World H R)

/-- An event in which the capture device hands over a block is the handoff
of some block `b`, at its time, with its frames and timestamp. -/
theorem Solution.handled_handed (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ} {h : H} {t : Time}
    {frames : List (ℕ × ℝ)} {stamp : ℝ}
    (hn : σ.handled w lookahead n = some (h, t, .handed frames stamp)) :
    ∃ b, h = w.sender ∧ t = w.source.handed b ∧
      frames = (w.source.block b).map (fun m => (m, w.target m)) ∧ stamp = w.source.reported b := by
  unfold Solution.handled at hn
  split at hn
  · rename_i b _
    simp only [Option.some.injEq, Prod.mk.injEq, Observation.handed.injEq] at hn
    exact ⟨b, hn.1.symm, hn.2.1.symm, hn.2.2.1.symm, hn.2.2.2.symm⟩
  · simp at hn
  · obtain ⟨m, -, heq⟩ := Option.map_eq_some_iff.mp hn
    simp at heq
  · obtain ⟨u, -, heq⟩ := Option.map_eq_some_iff.mp hn
    simp at heq
  · simp at hn

/-- An event in which a message arrives is the arrival of a message in
transit, at its destination and at its arrival time. -/
theorem Solution.handled_received (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ} {h : H} {t : Time}
    {i : H} {c : Msg} {F : Finset ℕ}
    (hn : σ.handled w lookahead n = some (h, t, .received i c F)) :
    ∃ m ∈ (σ.states w lookahead n).inFlight, m.destination = h ∧ m.arrival = t ∧
      m.origin = i ∧ m.contents = c ∧ m.frames = F := by
  unfold Solution.handled at hn
  split at hn
  · simp at hn
  · simp at hn
  · obtain ⟨m, hm, heq⟩ := Option.map_eq_some_iff.mp hn
    simp only [Prod.mk.injEq, Observation.received.injEq] at heq
    obtain ⟨h1, h2, h3, h4, h5⟩ := heq
    exact ⟨m, List.mem_of_getElem? hm, h1, h2, h3, h4, h5⟩
  · obtain ⟨u, -, heq⟩ := Option.map_eq_some_iff.mp hn
    simp at heq
  · simp at hn

end Handled

section Views

variable (w : World H R)

namespace State

/-- A message in transit stays in transit at a step of the run, or the step
handles its arrival. -/
theorem step_inFlight_or_handled (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg)
    {m : InFlight H Msg} (hm : m ∈ st.inFlight) :
    m ∈ (st.step σ w lookahead).inFlight ∨
      ∃ p, earliest (st.key w) st.due = some (.arrival p) ∧ st.inFlight[p]? = some m := by
  unfold step
  split
  · exact Or.inl (handle_inFlight_mem w st σ lookahead hm)
  · exact Or.inl (handle_inFlight_mem w st σ lookahead hm)
  · rename_i p hp
    split
    · rename_i m' hm'
      by_cases hin : m ∈ st.inFlight.eraseIdx p
      · exact Or.inl (handle_inFlight_mem w _ σ lookahead hin)
      · right
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
        have hip : i = p := by
          by_contra hne
          exact hin (List.mem_eraseIdx_iff_getElem.mpr ⟨i, hi, hne, rfl⟩)
        subst hip
        exact ⟨i, hp, List.getElem?_eq_getElem hi⟩
    · exact Or.inl hm
  · split
    · exact Or.inl (handle_inFlight_mem w _ σ lookahead hm)
    · exact Or.inl hm
  · exact Or.inl hm

end State

/-- **A message is handled before any later event.** A message in transit at
step `n` that arrives before the event of a later step `k` is handled at a
step between them: its destination observes its arrival. -/
theorem Solution.handled_before (σ : Solution H R Msg) (lookahead : ℕ+) {n k : ℕ}
    {m : InFlight H Msg} (hm : m ∈ (σ.states w lookahead n).inFlight) (hnk : n ≤ k)
    (harr : m.arrival < σ.eventTime w lookahead k) :
    ∃ i, n ≤ i ∧ i < k ∧
      σ.handled w lookahead i = some (m.destination, m.arrival, .received m.origin m.contents m.frames) := by
  have hinv : ∀ j, n ≤ j → m ∈ (σ.states w lookahead j).inFlight ∨
      ∃ i, n ≤ i ∧ i < j ∧ σ.handled w lookahead i
        = some (m.destination, m.arrival, .received m.origin m.contents m.frames) := by
    intro j hj
    induction hj with
    | refl => exact Or.inl hm
    | step hle ih =>
      rcases ih with hin | ⟨i, hi1, hi2, hi3⟩
      · rcases State.step_inFlight_or_handled w σ lookahead _ hin with hin' | ⟨p, hp, hpm⟩
        · exact Or.inl hin'
        · right
          refine ⟨_, hle, Nat.lt_succ_self _, ?_⟩
          unfold Solution.handled
          rw [hp]
          simp [hpm]
      · exact Or.inr ⟨i, hi1, Nat.lt_succ_of_lt hi2, hi3⟩
  rcases hinv k hnk with hin | h
  · have := (σ.eventTime_dueFrom w lookahead k).2.2.1 m hin
    exact absurd harr (not_lt.mpr this)
  · exact h

/-- **A host's view holds every event it handled.** -/
theorem Solution.mem_views_of_handled (σ : Solution H R Msg) (lookahead : ℕ+) {i k : ℕ}
    {h : H} {t : Time} {obs : Observation H R Msg}
    (hi : σ.handled w lookahead i = some (h, t, obs)) (hik : i < k) :
    (⟨(w.clock h).read t, obs⟩ : Event H R Msg) ∈ (σ.states w lookahead k).views h := by
  induction hik with
  | refl =>
    rw [σ.views_succ w lookahead i h, hi]
    simp
  | step _ ih =>
    rw [σ.views_succ w lookahead _ h]
    exact List.mem_append_left _ ih

/-- **A host's view holds nothing else.** Every event in a host's view is
one that the host handled at an earlier step, with its clock's reading at
the time of the event. -/
theorem Solution.handled_of_mem_views (σ : Solution H R Msg) (lookahead : ℕ+) {k : ℕ} {h : H}
    {e : Event H R Msg} (he : e ∈ (σ.states w lookahead k).views h) :
    ∃ i < k, ∃ t obs, σ.handled w lookahead i = some (h, t, obs) ∧
      e = ⟨(w.clock h).read t, obs⟩ := by
  induction k with
  | zero => simp [Solution.states, State.start] at he
  | succ k ih =>
    rw [σ.views_succ w lookahead k h] at he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, t, obs, h1, h2⟩ := ih he
      exact ⟨i, Nat.lt_succ_of_lt hi, t, obs, h1, h2⟩
    · split at he
      · rename_i h' t obs hk
        split_ifs at he with hh
        · subst hh
          rw [List.mem_singleton] at he
          exact ⟨k, Nat.lt_succ_self k, t, obs, hk, he⟩
        · simp at he
      · simp at he

/-- The event that the run handles at a step occurs at the step's event
time. -/
theorem Solution.handled_time (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ} {h : H} {t : Time}
    {obs : Observation H R Msg} (hn : σ.handled w lookahead n = some (h, t, obs)) :
    σ.eventTime w lookahead n = t := by
  unfold Solution.handled at hn
  unfold Solution.eventTime
  split at hn
  · rename_i b he
    rw [he]
    simp only [Option.some.injEq, Prod.mk.injEq] at hn
    exact hn.2.1
  · rename_i r b he
    rw [he]
    simp only [Option.some.injEq, Prod.mk.injEq] at hn
    exact hn.2.1
  · rename_i p he
    rw [he]
    obtain ⟨m, hm, heq⟩ := Option.map_eq_some_iff.mp hn
    simp only [Prod.mk.injEq] at heq
    simp [State.key, hm, heq.2.1]
  · rename_i p he
    rw [he]
    obtain ⟨u, hu, heq⟩ := Option.map_eq_some_iff.mp hn
    simp only [Prod.mk.injEq] at heq
    simp [State.key, hu, heq.2.1]
  · simp at hn

/-- **The run's event times never decrease.** -/
theorem Solution.eventTime_mono (σ : Solution H R Msg) (lookahead : ℕ+) :
    Monotone (σ.eventTime w lookahead) :=
  monotone_nat_of_le_succ (σ.eventTime_le_succ w lookahead)

/-- **Each event of a view was handled at an earlier step.** If a host's
view at step `k` is `l₁ ++ e :: l₂`, then the host handled `e` at a step
`i < k` at which its view was `l₁`. -/
theorem Solution.handled_of_views_eq (σ : Solution H R Msg) (lookahead : ℕ+) {k : ℕ} {h : H}
    {l₁ l₂ : List (Event H R Msg)} {e : Event H R Msg}
    (hv : (σ.states w lookahead k).views h = l₁ ++ e :: l₂) :
    ∃ i < k, (σ.states w lookahead i).views h = l₁ ∧ ∃ t obs,
      σ.handled w lookahead i = some (h, t, obs) ∧ e = ⟨(w.clock h).read t, obs⟩ := by
  induction k generalizing l₂ with
  | zero => simp [Solution.states, State.start] at hv
  | succ k ih =>
    rw [σ.views_succ w lookahead k h] at hv
    have older : (σ.states w lookahead k).views h = l₁ ++ e :: l₂ →
        ∃ i < k + 1, (σ.states w lookahead i).views h = l₁ ∧ ∃ t obs,
          σ.handled w lookahead i = some (h, t, obs) ∧ e = ⟨(w.clock h).read t, obs⟩ := by
      intro hv'
      obtain ⟨i, hi, rest⟩ := ih hv'
      exact ⟨i, Nat.lt_succ_of_lt hi, rest⟩
    split at hv
    · rename_i h' t obs hk
      split_ifs at hv with hh
      · subst hh
        rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₂', x, rfl⟩
        · obtain ⟨h1, h2⟩ := List.append_inj' hv rfl
          refine ⟨k, Nat.lt_succ_self k, h1, t, obs, hk, ?_⟩
          simpa using h2.symm
        · have hv' : (σ.states w lookahead k).views h ++ [⟨(w.clock h).read t, obs⟩]
              = (l₁ ++ e :: l₂') ++ [x] := by
            rw [hv]; simp
          obtain ⟨i, hi, rest⟩ := ih (List.append_inj' hv' rfl).1
          exact ⟨i, Nat.lt_succ_of_lt hi, rest⟩
      · simp only [List.append_nil] at hv
        exact older hv
    · simp only [List.append_nil] at hv
      exact older hv

end Views

section Sent

/-- **What a step sends is in transit after it, if the network delivers
it.** Let step `n` handle an event of host `h` at true time `t`, and let the
`i`-th message that `h` sends go to host `j`. Its number on the link from
`h` to `j` is the number of messages sent on that link before it. If the
network delivers the message, it is in transit after the step, carrying
those of its frames that `h` holds. -/
theorem Solution.sent_inFlight (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ}
    {h : H} {t : Time} {obs : Observation H R Msg}
    (hn : σ.handled w lookahead n = some (h, t, obs)) {S : List (H × Msg × Finset ℕ)}
    (hS : (σ h ((σ.states w lookahead n).views h ++ [⟨(w.clock h).read t, obs⟩])).sends = S)
    {i : ℕ} (hi : i < S.length) {arr : Time}
    (hdel : w.network.deliver h S[i].1 t
      ((σ.states w lookahead n).sentCount h S[i].1 + (S.take i).countP (fun s => s.1 = S[i].1))
      = some arr) :
    (⟨arr, h, S[i].1, S[i].2.1,
      S[i].2.2.filter (· ∈ (σ.states w lookahead n).held h ∪ obs.frames)⟩ : InFlight H Msg)
      ∈ (σ.states w lookahead (n + 1)).inFlight := by
  subst hS
  set st := σ.states w lookahead n with hstdef
  show _ ∈ (st.step σ w lookahead).inFlight
  unfold Solution.handled at hn
  rw [← hstdef] at hn
  rcases he : earliest (st.key w) st.due with _ | d
  · rw [he] at hn
    simp at hn
  · rw [he] at hn
    unfold State.step
    rw [he]
    cases d with
    | handed b =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl, rfl⟩ := hn
      exact State.handle_delivered w σ lookahead st _ _ _ i hi hdel
    | asked r b =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl, rfl⟩ := hn
      exact State.handle_delivered w σ lookahead st _ _ _ i hi hdel
    | arrival p =>
      cases hm : st.inFlight[p]? with
      | none =>
        simp [hm] at hn
      | some m =>
        simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl, rfl⟩ := hn
        simp only [hm]
        exact State.handle_delivered w σ lookahead { st with inFlight := st.inFlight.eraseIdx p }
          _ _ _ i hi hdel
    | timer p =>
      cases hm : st.timers[p]? with
      | none =>
        simp [hm] at hn
      | some u =>
        simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl, rfl⟩ := hn
        simp only [hm]
        exact State.handle_delivered w σ lookahead { st with timers := st.timers.eraseIdx p }
          _ _ _ i hi hdel

end Sent

section Requests

namespace State

/-- Handling an event does not change the speakers' next requests. -/
theorem handle_askedNext (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg) (h : H)
    (t : Time) (obs : Observation H R Msg) :
    (st.handle σ w lookahead h t obs).askedNext = st.askedNext := by
  simp only [handle, sendAll_askedNext]

/-- A step of the run either leaves a speaker's next request unchanged, or
handles that request and moves on to the following one. -/
theorem step_askedNext (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg) (r : Fin R) :
    (st.step σ w lookahead).askedNext r = st.askedNext r ∨
      ((st.step σ w lookahead).askedNext r = st.askedNext r + 1 ∧
        earliest (st.key w) st.due = some (.asked r (st.askedNext r))) := by
  unfold step
  split
  · left
    simp only [handle_askedNext]
  · rename_i r' b hb
    have hmem := (earliest_spec _ _ _ hb).1
    have hbn : b = st.askedNext r' := by
      rcases st.mem_due hmem with h | ⟨r'', h⟩ | ⟨p, _, h⟩ | ⟨p, _, h⟩
      · simp at h
      · simp only [Due.asked.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · simp at h
      · simp at h
    subst hbn
    by_cases hr : r = r'
    · subst hr
      right
      simp [hb]
    · left
      simp [Function.update_of_ne hr]
  · split
    · left
      simp only [handle_askedNext]
    · left
      rfl
  · split
    · left
      simp only [handle_askedNext]
    · left
      rfl
  · left
    rfl

end State

/-- A speaker's next request never decreases. -/
theorem Solution.askedNext_mono (σ : Solution H R Msg) (lookahead : ℕ+) (r : Fin R) :
    Monotone fun n => (σ.states w lookahead n).askedNext r := by
  apply monotone_nat_of_le_succ
  intro n
  rcases State.step_askedNext w σ lookahead (σ.states w lookahead n) r with h | ⟨h, -⟩
  · exact h.symm.le
  · show (σ.states w lookahead n).askedNext r ≤ ((σ.states w lookahead n).step σ w lookahead).askedNext r
    omega

/-- **The step at which a request is handled.** When the run has handled
request `b` of speaker `r` by step `m`, it did so at a step `n` before `m`,
at which the earliest pending event was that request. -/
theorem Solution.exists_asked_step (σ : Solution H R Msg) (lookahead : ℕ+) {m : ℕ} {r : Fin R}
    {b : ℕ} (h : b < (σ.states w lookahead m).askedNext r) :
    ∃ n < m, (σ.states w lookahead n).askedNext r = b ∧
      earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due = some (.asked r b) := by
  induction m with
  | zero => exact absurd h (by simp [Solution.states, State.start])
  | succ m ih =>
    by_cases hm : b < (σ.states w lookahead m).askedNext r
    · obtain ⟨n, hn, h1, h2⟩ := ih hm
      exact ⟨n, Nat.lt_succ_of_lt hn, h1, h2⟩
    · rcases State.step_askedNext w σ lookahead (σ.states w lookahead m) r with heq | ⟨heq, hearly⟩
      · exact absurd (heq ▸ h) hm
      · have hb : (σ.states w lookahead m).askedNext r = b := by
          have : (σ.states w lookahead (m + 1)).askedNext r
              = (σ.states w lookahead m).askedNext r + 1 := heq
          omega
        exact ⟨m, Nat.lt_succ_self m, hb, hb ▸ hearly⟩

/-- **A speaker plays what its host decided at the request.** When step `n`
handles request `b` of speaker `r`, every output sample of the block that
has not left the device yet plays what the speaker's host decided then, if
the host holds the frames it needs. An output sample that left before the
request was handled plays nothing of the source. -/
theorem Solution.plays_of_asked_step (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ} {r : Fin R}
    {b : ℕ} (hb : (σ.states w lookahead n).askedNext r = b)
    (hearly : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r b))
    {k : ℕ} (hk : k ∈ (w.speaker r).block b) :
    σ.plays w lookahead r k
      = if (w.speaker r).asked b < (w.speaker r).out k then
          playable lookahead ((σ.states w lookahead n).held (w.host r))
            ((σ (w.host r) ((σ.states w lookahead n).views (w.host r)
              ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
                .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩])).plays k)
        else none := by
  have hkb : (w.speaker r).first b ≤ k ∧ k < (w.speaker r).first (b + 1) := by
    unfold PlaybackDevice.block at hk
    rw [List.mem_range'_1] at hk
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self b)
    omega
  have hnext : (σ.states w lookahead (n + 1)).askedNext r = b + 1 := by
    rcases State.step_askedNext w σ lookahead (σ.states w lookahead n) r with h | ⟨h, -⟩
    · exfalso
      have hstep : (σ.states w lookahead (n + 1)) = (σ.states w lookahead n).step σ w lookahead := rfl
      unfold State.step at hstep
      rw [hearly] at hstep
      have : (σ.states w lookahead (n + 1)).askedNext r = b + 1 := by
        rw [hstep]; simp
      have h' : (σ.states w lookahead (n + 1)).askedNext r = (σ.states w lookahead n).askedNext r := h
      omega
    · have h' : (σ.states w lookahead (n + 1)).askedNext r
          = (σ.states w lookahead n).askedNext r + 1 := h
      omega
  have hex : ∃ n', k < (w.speaker r).first ((σ.states w lookahead n').askedNext r) :=
    ⟨n + 1, by rw [hnext]; exact hkb.2⟩
  have hfind : Nat.find hex = n + 1 := by
    rw [Nat.find_eq_iff]
    refine ⟨by rw [hnext]; exact hkb.2, fun n' hn' => ?_⟩
    have hmono := Solution.askedNext_mono w σ lookahead r (Nat.lt_succ_iff.mp hn')
    simp only at hmono
    rw [hb] at hmono
    have := (w.speaker r).first_strictMono.monotone hmono
    omega
  unfold Solution.plays
  rw [dite_eq_left hex, hfind]
  show ((σ.states w lookahead n).step σ w lookahead).plays r k = _
  unfold State.step
  rw [hearly]
  simp only [State.handle, Observation.frames, Finset.union_empty, hk, and_self, ite_true]

/-- When step `n` handles request `b` of speaker `r` before output sample
`k` of the block leaves, the output sample plays what the speaker's host
decided then, if the host holds the frames it needs. -/
theorem Solution.plays_of_asked_step_of_lt (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ}
    {r : Fin R} {b : ℕ} (hb : (σ.states w lookahead n).askedNext r = b)
    (hearly : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r b))
    {k : ℕ} (hk : k ∈ (w.speaker r).block b)
    (hlt : (w.speaker r).asked b < (w.speaker r).out k) :
    σ.plays w lookahead r k = playable lookahead ((σ.states w lookahead n).held (w.host r))
      ((σ (w.host r) ((σ.states w lookahead n).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
          .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩])).plays k) := by
  rw [σ.plays_of_asked_step w lookahead hb hearly hk, ite_eq_left hlt]

/-- **An output sample that left before its request was handled plays
nothing of the source.** -/
theorem Solution.plays_eq_none_of_out_le (σ : Solution H R Msg) (lookahead : ℕ+) {r : Fin R}
    {b k : ℕ} (hk : k ∈ (w.speaker r).block b)
    (hle : (w.speaker r).out k ≤ (w.speaker r).asked b) :
    σ.plays w lookahead r k = none := by
  by_cases hex : ∃ m, b < (σ.states w lookahead m).askedNext r
  · obtain ⟨m, hm⟩ := hex
    obtain ⟨n, -, hb, hearly⟩ := σ.exists_asked_step w lookahead hm
    rw [σ.plays_of_asked_step w lookahead hb hearly hk, ite_eq_right (not_lt.mpr hle)]
  · unfold Solution.plays
    rw [dite_eq_right]
    rintro ⟨n', hn'⟩
    refine hex ⟨n', ?_⟩
    unfold PlaybackDevice.block at hk
    rw [List.mem_range'_1] at hk
    by_contra hnot
    have := (w.speaker r).first_strictMono.monotone (not_lt.mp hnot)
    omega

/-- **A speaker plays the source only at output samples whose request was
handled before they left.** -/
theorem Solution.asked_lt_out_of_plays (σ : Solution H R Msg) (lookahead : ℕ+) {r : Fin R}
    {b k : ℕ} {x : ℝ} (hk : k ∈ (w.speaker r).block b)
    (hp : σ.plays w lookahead r k = some x) :
    (w.speaker r).asked b < (w.speaker r).out k := by
  by_contra hnot
  rw [σ.plays_eq_none_of_out_le w lookahead hk (not_lt.mp hnot)] at hp
  exact absurd hp (by simp)

/-- The event handled at a step whose earliest pending event is request `b`
of speaker `r`: that request, at the speaker's host and at the request's
true time. -/
theorem Solution.handled_of_asked (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ} {r : Fin R}
    {b : ℕ} (hearly : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r b)) :
    σ.handled w lookahead n = some (w.host r, (w.speaker r).asked b,
      .asked r ((w.speaker r).block b) ((w.speaker r).reported b)) := by
  unfold Solution.handled
  rw [hearly]

/-- An event in which a device requests a block is handled at the step that
handles the speaker's next request. -/
theorem Solution.handled_asked (σ : Solution H R Msg) (lookahead : ℕ+) {i : ℕ} {h : H} {t : Time}
    {r : Fin R} {outs : List ℕ} {st : ℝ}
    (hi : σ.handled w lookahead i = some (h, t, .asked r outs st)) :
    earliest ((σ.states w lookahead i).key w) (σ.states w lookahead i).due
      = some (.asked r ((σ.states w lookahead i).askedNext r)) := by
  unfold Solution.handled at hi
  split at hi
  · simp at hi
  · rename_i r' b hb
    simp only [Option.some.injEq, Prod.mk.injEq, Observation.asked.injEq] at hi
    obtain ⟨-, -, rfl, -, -⟩ := hi
    have hmem := (earliest_spec _ _ _ hb).1
    rcases (σ.states w lookahead i).mem_due hmem with h | ⟨r'', h⟩ | ⟨p, _, h⟩ | ⟨p, _, h⟩
    · simp at h
    · simp only [Due.asked.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hb
    · simp at h
    · simp at h
  · obtain ⟨m, -, heq⟩ := Option.map_eq_some_iff.mp hi
    simp at heq
  · obtain ⟨u, -, heq⟩ := Option.map_eq_some_iff.mp hi
    simp at heq
  · simp at hi

/-- The step that handles a speaker's next request moves the speaker on to
the request after it. -/
theorem Solution.askedNext_succ (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ} {r : Fin R}
    (hearly : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r ((σ.states w lookahead n).askedNext r))) :
    (σ.states w lookahead (n + 1)).askedNext r = (σ.states w lookahead n).askedNext r + 1 := by
  show ((σ.states w lookahead n).step σ w lookahead).askedNext r = _
  unfold State.step
  rw [hearly]
  simp

/-- **A view only grows.** A host's view at a later step is its view at an
earlier step followed by the events it handled at the steps between. -/
theorem Solution.views_append (σ : Solution H R Msg) (lookahead : ℕ+) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : H) :
    ∃ l, (σ.states w lookahead k₂).views h = (σ.states w lookahead k₁).views h ++ l ∧
      ∀ e ∈ l, ∃ i, k₁ ≤ i ∧ i < k₂ ∧ ∃ t obs, σ.handled w lookahead i = some (h, t, obs)
        ∧ e = ⟨(w.clock h).read t, obs⟩ := by
  induction k₂, hk using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ k hk ih =>
    obtain ⟨l, hl, hev⟩ := ih
    rw [σ.views_succ w lookahead k h]
    split
    · rename_i h' t obs hkh
      split_ifs with hh
      · subst hh
        refine ⟨l ++ [⟨(w.clock h).read t, obs⟩], by rw [hl, List.append_assoc], ?_⟩
        intro e he
        rcases List.mem_append.mp he with he | he
        · obtain ⟨i, h1, h2, rest⟩ := hev e he
          exact ⟨i, h1, Nat.lt_succ_of_lt h2, rest⟩
        · rw [List.mem_singleton] at he
          exact ⟨k, hk, Nat.lt_succ_self k, t, obs, hkh, he⟩
      · refine ⟨l, by rw [hl, List.append_nil], fun e he => ?_⟩
        obtain ⟨i, h1, h2, rest⟩ := hev e he
        exact ⟨i, h1, Nat.lt_succ_of_lt h2, rest⟩
    · refine ⟨l, by rw [hl, List.append_nil], fun e he => ?_⟩
      obtain ⟨i, h1, h2, rest⟩ := hev e he
      exact ⟨i, h1, Nat.lt_succ_of_lt h2, rest⟩

/-- **No request of a speaker comes between two of its consecutive
requests.** While a speaker's next request stays the same, its host handles
no request of that speaker. -/
theorem Solution.no_request_between (σ : Solution H R Msg) (lookahead : ℕ+) {k₁ k₂ : ℕ} {r : Fin R}
    (hsame : (σ.states w lookahead k₁).askedNext r = (σ.states w lookahead k₂).askedNext r)
    {i : ℕ} (hi₁ : k₁ ≤ i) (hi₂ : i < k₂) {h : H} {t : Time} {outs : List ℕ} {st : ℝ} :
    σ.handled w lookahead i ≠ some (h, t, .asked r outs st) := by
  intro hi
  have hearly := σ.handled_asked w lookahead hi
  have hsucc := σ.askedNext_succ w lookahead hearly
  have m1 := Solution.askedNext_mono w σ lookahead r hi₁
  have m2 := Solution.askedNext_mono w σ lookahead r (show i + 1 ≤ k₂ by omega)
  simp only at m1 m2
  omega

end Requests

section Progress

/-- The total weight of the messages in a list that arrive by true time `T`,
where a message weighs `wt` of its payload. -/
noncomputable def weightBy (wt : Msg → ℕ) (T : Time) (l : List (InFlight H Msg)) : ℕ :=
  (l.map fun m => if m.arrival ≤ T then wt m.contents else 0).sum

namespace State

/-- Sending a message adds at most its weight to the messages in transit. -/
theorem send_weight (wt : Msg → ℕ) (T : Time) (st : State H R Msg) (h : H) (t : Time) (j : H)
    (c : Msg) (F : Finset ℕ) :
    weightBy wt T (st.send w h t j c F).inFlight ≤ weightBy wt T st.inFlight + wt c := by
  unfold send
  split
  · simp only [weightBy, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    split_ifs <;> omega
  · simp only
    omega

/-- Sending messages adds at most their weights to the messages in
transit. -/
theorem sendAll_weight (wt : Msg → ℕ) (T : Time) (st : State H R Msg) (h : H) (t : Time)
    (held : Finset ℕ) (sends : List (H × Msg × Finset ℕ)) :
    weightBy wt T (st.sendAll w h t held sends).inFlight
      ≤ weightBy wt T st.inFlight + (sends.map fun s => wt s.2.1).sum := by
  induction sends generalizing st with
  | nil => simp [sendAll]
  | cons s l ih =>
    have h1 := ih (st.send w h t s.1 s.2.1 (s.2.2.filter (· ∈ held)))
    have h2 := send_weight w wt T st h t s.1 s.2.1 (s.2.2.filter (· ∈ held))
    simp only [sendAll, List.foldl_cons] at h1 ⊢
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Handling an event adds to the messages in transit at most the weights of
what the host sends. -/
theorem handle_weight (σ : Solution H R Msg) (lookahead : ℕ+) (wt : Msg → ℕ) (T : Time)
    (st : State H R Msg) (h : H) (t : Time) (obs : Observation H R Msg) :
    weightBy wt T (st.handle σ w lookahead h t obs).inFlight
      ≤ weightBy wt T st.inFlight
        + ((σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends.map fun s => wt s.2.1).sum := by
  simp only [handle]
  exact sendAll_weight w wt T _ h t _ _

/-- A host that sets no timers leaves the pending timers unchanged. -/
theorem handle_timers (σ : Solution H R Msg) (lookahead : ℕ+) (st : State H R Msg) (h : H)
    (t : Time) (obs : Observation H R Msg)
    (htimers : (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).timers = []) :
    (st.handle σ w lookahead h t obs).timers = st.timers := by
  simp only [handle, htimers, List.filterMap_nil, List.append_nil]
  exact sendAll_timers w _ h t _ _

end State

omit [DecidableEq H] in
/-- Removing a message from a list reduces the list's weight by the
message's weight if the message arrives by `T`, and leaves the weight
unchanged otherwise. -/
theorem weightBy_eraseIdx (wt : Msg → ℕ) (T : Time) (l : List (InFlight H Msg)) {p : ℕ}
    (hp : p < l.length) :
    weightBy wt T (l.eraseIdx p) + (if l[p].arrival ≤ T then wt l[p].contents else 0)
      = weightBy wt T l := by
  unfold weightBy
  conv_rhs => rw [← List.take_append_drop p l]
  rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons hp]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  ring

/-- **A run whose messages die out advances past every true time.** Suppose
a solution sets no timers, and at every event the messages it sends weigh
less than the event: a handoff weighs `cH`, a request `cQ`, and an arrival
the weight of the arriving message. In a world where the capture device
hands over blocks without end and every speaker requests blocks without
end, the run has an event after every true time. -/
theorem Solution.progress (σ : Solution H R Msg) (lookahead : ℕ+) (wt : Msg → ℕ) (cH cQ : ℕ)
    (htimers : ∀ h view, (σ h view).timers = [])
    (hhanded : ∀ h view frames rep reading,
      ((σ h (view ++ [⟨reading, .handed frames rep⟩])).sends.map fun s => wt s.2.1).sum + 1 ≤ cH)
    (hasked : ∀ h view r outs rep reading,
      ((σ h (view ++ [⟨reading, .asked r outs rep⟩])).sends.map fun s => wt s.2.1).sum + 1 ≤ cQ)
    (hreceived : ∀ h view i c F reading,
      ((σ h (view ++ [⟨reading, .received i c F⟩])).sends.map fun s => wt s.2.1).sum + 1 ≤ wt c)
    (hhand : ∀ T, ∃ b, T < w.source.handed b) (hask : ∀ r T, ∃ b, T < (w.speaker r).asked b)
    (T : Time) : ∃ n, T < σ.eventTime w lookahead n := by
  obtain ⟨NH, hNH⟩ := hhand T
  choose NQ hNQ using fun r => hask r T
  -- What remains to happen by `T`: the handoffs, the requests and the messages
  -- that arrive by then, each weighing what it may lead to.
  let Φ : State H R Msg → ℕ := fun st =>
    cH * (NH - st.handedNext) + ∑ r, cQ * (NQ r - st.askedNext r) + weightBy wt T st.inFlight
  have htm : ∀ n, (σ.states w lookahead n).timers = [] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show ((σ.states w lookahead n).step σ w lookahead).timers = []
      set st := σ.states w lookahead n
      unfold State.step
      split
      · simp only
        rw [State.handle_timers w σ lookahead st _ _ _ (htimers _ _), ih]
      · simp only
        rw [State.handle_timers w σ lookahead st _ _ _ (htimers _ _), ih]
      · split
        · rw [State.handle_timers w σ lookahead _ _ _ _ (htimers _ _)]
          exact ih
        · exact ih
      · split
        · rename_i p _ u hu
          rw [ih] at hu
          simp at hu
        · exact ih
      · exact ih
  have hdec : ∀ n, σ.eventTime w lookahead n ≤ T →
      Φ (σ.states w lookahead (n + 1)) + 1 ≤ Φ (σ.states w lookahead n) := by
    intro n hn
    set st := σ.states w lookahead n with hst
    have hstep : σ.states w lookahead (n + 1) = st.step σ w lookahead := rfl
    obtain ⟨e₀, he₀⟩ := earliest_exists (st.key w) st.due_ne_nil
    have htime : σ.eventTime w lookahead n = (st.key w e₀).1 := by
      simp only [Solution.eventTime, ← hst, he₀]
    have hmem := (earliest_spec _ _ _ he₀).1
    rw [hstep]
    unfold State.step
    rw [he₀]
    rcases st.mem_due hmem with rfl | ⟨r, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · -- A handoff, which happens by `T`.
      have hb : st.handedNext < NH := by
        by_contra hge
        have := w.source.handed_mono (not_lt.mp hge)
        simp only [State.key] at htime
        linarith
      have hw := State.handle_weight w σ lookahead wt T st w.sender (w.source.handed st.handedNext)
        (.handed ((w.source.block st.handedNext).map fun m => (m, w.target m))
          (w.source.reported st.handedNext))
      have hs := hhanded w.sender (st.views w.sender)
        ((w.source.block st.handedNext).map fun m => (m, w.target m))
        (w.source.reported st.handedNext) ((w.clock w.sender).read
        (w.source.handed st.handedNext))
      simp only [Φ, State.handle_askedNext]
      have hmul : cH * (NH - st.handedNext) = cH * (NH - (st.handedNext + 1)) + cH := by
        rw [show NH - st.handedNext = (NH - (st.handedNext + 1)) + 1 by omega, Nat.mul_succ]
      omega
    · -- A request, which happens by `T`.
      have hb : st.askedNext r < NQ r := by
        by_contra hge
        have := (w.speaker r).asked_mono (not_lt.mp hge)
        have h2 := hNQ r
        simp only [State.key] at htime
        linarith
      have hw := State.handle_weight w σ lookahead wt T st (w.host r)
        ((w.speaker r).asked (st.askedNext r))
        (.asked r ((w.speaker r).block (st.askedNext r)) ((w.speaker r).reported (st.askedNext r)))
      have hs := hasked (w.host r) (st.views (w.host r)) r ((w.speaker r).block (st.askedNext r))
        ((w.speaker r).reported (st.askedNext r)) ((w.clock (w.host r)).read
        ((w.speaker r).asked (st.askedNext r)))
      have hsum : ∑ r', cQ * (NQ r' - Function.update st.askedNext r (st.askedNext r + 1) r') + cQ
          = ∑ r', cQ * (NQ r' - st.askedNext r') := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
        have hrest : ∑ r' ∈ Finset.univ.erase r,
              cQ * (NQ r' - Function.update st.askedNext r (st.askedNext r + 1) r')
            = ∑ r' ∈ Finset.univ.erase r, cQ * (NQ r' - st.askedNext r') := by
          refine Finset.sum_congr rfl fun r' hr' => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hr')]
        rw [hrest, Function.update_self,
          show NQ r - st.askedNext r = (NQ r - (st.askedNext r + 1)) + 1 by omega, Nat.mul_succ]
        ring
      simp only [Φ, State.handle_handedNext]
      omega
    · -- The arrival of a message, which happens by `T`.
      have harr : st.inFlight[p].arrival ≤ T := by
        simp only [State.key, List.getElem?_eq_getElem hp, Option.map_some,
          Option.getD_some] at htime
        linarith
      simp only [List.getElem?_eq_getElem hp]
      have hw := State.handle_weight w σ lookahead wt T { st with inFlight := st.inFlight.eraseIdx p }
        st.inFlight[p].destination st.inFlight[p].arrival
        (.received st.inFlight[p].origin st.inFlight[p].contents st.inFlight[p].frames)
      have hs := hreceived st.inFlight[p].destination (st.views st.inFlight[p].destination)
        st.inFlight[p].origin st.inFlight[p].contents st.inFlight[p].frames
        ((w.clock st.inFlight[p].destination).read st.inFlight[p].arrival)
      have he := weightBy_eraseIdx wt T st.inFlight hp
      simp only [harr, ite_true] at he
      simp only [Φ, State.handle_handedNext, State.handle_askedNext]
      simp only at hw
      omega
    · -- No timer is set.
      rw [htm n] at hp
      simp at hp
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hbound : ∀ n, Φ (σ.states w lookahead n) + n ≤ Φ (σ.states w lookahead 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hdec n (hcon n)
      omega
  have := hbound (Φ (σ.states w lookahead 0) + 1)
  omega

end Progress

end Unisono.Spec
