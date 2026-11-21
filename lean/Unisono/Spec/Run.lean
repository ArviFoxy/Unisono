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
  been handled by then: its destination holds its frames
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

/-- A host that handles an event holds every frame it held, and the frames
the event brings. -/
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

/-- A message in transit stays in transit at a step of the run, or is
handled there, and its destination then holds its frames. -/
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

/-- **A message is handled before any later event.** A message in transit at
step `n`, which arrives before the event of a later step `k`, has been
handled by then: its destination holds its frames. -/
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

/-- **The messages a host sends at an event, as the network delivers them.**
The `i`-th entry of `sends`, to host `j`, is the host's message to `j`
numbered `st.sentCount h j` plus the number of earlier entries to `j`; if
the network delivers that message, it is in transit after the event, with
the frames it carries that the host holds. -/
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

/-- A step of the run either leaves the next block to be handed over as it
is, or hands it over and moves on to the next. -/
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

/-- A block handed over before the event of step `n` was handed over by
then. -/
theorem Solution.lt_handedNext (σ : Solution H R Msg) (lookahead : ℕ+) {n b : ℕ}
    (h : w.source.handed b < σ.eventTime w lookahead n) :
    b < (σ.states w lookahead n).handedNext := by
  by_contra hle
  have h1 := w.source.handed_strictMono.monotone (not_lt.mp hle)
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

end Unisono.Spec
