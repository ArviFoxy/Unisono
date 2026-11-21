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
