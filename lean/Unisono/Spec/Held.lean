/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Run
public import Unisono.Spec.Topologies

/-!
# The frames that a host holds, and requests that coincide with arrivals

Two facts about the run of every solution.

* A host holds exactly the frames that the events in its view brought: the
  frames of the blocks that the capture device handed over to it and of the
  messages that arrived (`Solution.mem_held_iff`).
* A device request is handled before a message that arrives at the same true
  time. So a message that some step handles arrived strictly before every
  request that is pending at that step or at a later step
  (`Solution.received_lt_asked`).

Together they say what a host holds when a device requests a block: the
frames that arrived strictly before the request.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- **A host's frames grow by those of the event it handles.** At each step
of the run, the host that handles the event adds the frames that the event
brings to the frames it holds, and every other host holds what it held. -/
theorem Solution.held_succ (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (n : ℕ)
    (h : H) :
    (σ.states w lookahead (n + 1)).held h = (σ.states w lookahead n).held h ∪
      match σ.handled w lookahead n with
      | some (h', _, obs) => if h = h' then obs.frames else ∅
      | none => ∅ := by
  show ((σ.states w lookahead n).step σ w lookahead).held h = _
  unfold State.step Solution.handled
  split
  · rename_i b hb
    simp only [hb, State.handle_held]
    by_cases hh : h = w.sender
    · subst hh
      simp
    · simp [hh]
  · rename_i r b hb
    simp only [hb, State.handle_held]
    by_cases hh : h = w.host r
    · subst hh
      simp
    · simp [hh]
  · rename_i p hp
    simp only [hp]
    split
    · rename_i m hm
      simp only [hm, Option.map_some, State.handle_held]
      by_cases hh : h = m.destination
      · subst hh
        simp
      · simp [hh]
    · rename_i hm
      simp [hm]
  · rename_i p hp
    simp only [hp]
    split
    · rename_i u hu
      simp only [hu, Option.map_some, State.handle_held]
      by_cases hh : h = u.host
      · subst hh
        simp
      · simp [hh]
    · rename_i hu
      simp [hu]
  · rename_i hnone
    simp [hnone]

/-- **A host holds exactly the frames that its events brought.** At every
step of the run, a host holds frame `n` if and only if an event in its view
brought the frame: a block that the capture device handed over, or a message
that arrived. -/
theorem Solution.mem_held_iff (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (k : ℕ)
    (h : H) (n : ℕ) :
    n ∈ (σ.states w lookahead k).held h
      ↔ ∃ e ∈ (σ.states w lookahead k).views h, n ∈ e.observation.frames := by
  induction k with
  | zero => simp [Solution.states, State.start]
  | succ k ih =>
    rw [σ.held_succ w lookahead k h, σ.views_succ w lookahead k h, Finset.mem_union, ih]
    cases hh : σ.handled w lookahead k with
    | none => simp
    | some x =>
      obtain ⟨h', t, obs⟩ := x
      by_cases hc : h = h'
      · simp only [hc, ite_true, List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨e, he, hn⟩ | hn)
          · exact ⟨e, Or.inl he, hn⟩
          · exact ⟨_, Or.inr rfl, hn⟩
        · rintro ⟨e, he | rfl, hn⟩
          · exact Or.inl ⟨e, he, hn⟩
          · exact Or.inr hn
      · simp [hc]

/-- **A device request is handled before a message that arrives at the same
true time.** If step `i` handles the arrival of a message at true time `t`,
then `t` is before the next request of every speaker at every step from `i`
on. So the message arrived strictly before every request that a later step
handles. -/
theorem Solution.received_lt_asked (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {i k : ℕ} (hik : i ≤ k) {h : H} {t : Time} {j : H} {c : Msg} {F : Finset ℕ}
    (hi : σ.handled w lookahead i = some (h, t, .received j c F)) (r : Fin R) :
    t < (w.speaker r).asked ((σ.states w lookahead k).askedNext r) := by
  refine lt_of_lt_of_le ?_
    ((w.speaker r).asked_strictMono.monotone (Solution.askedNext_mono w σ lookahead r hik))
  unfold Solution.handled at hi
  split at hi
  · simp at hi
  · simp at hi
  · rename_i p hp
    obtain ⟨msg, hmsg, heq⟩ := Option.map_eq_some_iff.mp hi
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, harr, -⟩ := heq
    obtain ⟨-, hlex⟩ := earliest_spec_lex ((σ.states w lookahead i).key w)
      (σ.states w lookahead i).due _ hp
    have hkey : ((σ.states w lookahead i).key w (.arrival p)).1 = t := by
      simp [State.key, hmsg, harr]
    rcases hlex (.asked r ((σ.states w lookahead i).askedNext r))
      ((σ.states w lookahead i).asked_mem_due r) with h1 | ⟨-, h2⟩
    · rw [hkey] at h1
      exact h1
    · simp only [State.key] at h2
      have := r.isLt
      omega
  · obtain ⟨u, -, heq⟩ := Option.map_eq_some_iff.mp hi
    simp at heq
  · simp at hi

end Unisono.Spec
