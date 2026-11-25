/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.OwnEvents

/-!
# The events of a view are in the order of time

A host handles its events in the order of time, and its clock never runs
backwards. So the readings of the events in its view never decrease
(`Solution.views_pairwise`), also when the view is taken with the request
that the host handles next (`Solution.requestView_pairwise`). A rule that
takes "the newest" event of some kind from a view therefore takes the one
with the largest reading.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] (w : World H R)

/-- **The readings in a host's view never decrease**, in the run of any
solution in any world. -/
theorem Solution.views_pairwise (σ : Solution H R Msg) (lookahead : ℕ+) (k : ℕ) (h : H) :
    ((σ.states w lookahead k).views h).Pairwise fun e e' => e.reading ≤ e'.reading := by
  induction k with
  | zero => simp [Solution.states, State.start]
  | succ k ih =>
    rw [σ.views_succ w lookahead k h]
    split
    · rename_i h' t obs hk
      split_ifs with hh
      · subst hh
        refine List.pairwise_append.mpr ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro e he e' he'
        rw [List.mem_singleton] at he'
        subst he'
        obtain ⟨i, hi, ti, obsi, h1, rfl⟩ := σ.handled_of_mem_views w lookahead he
        have e1 := σ.handled_time w lookahead h1
        have e2 := σ.handled_time w lookahead hk
        have hle : ti ≤ t := by
          rw [← e1, ← e2]
          exact σ.eventTime_mono w lookahead hi.le
        exact (w.clock h).strictMono.monotone hle
      · rw [List.append_nil]
        exact ih
    · rw [List.append_nil]
      exact ih

/-- **The readings in a host's view with the request that it handles next
never decrease.** -/
theorem Solution.requestView_pairwise (σ : Solution H R Msg) (lookahead : ℕ+) {n : ℕ}
    {r : Fin R} {β : ℕ}
    (hE : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r β)) :
    ((σ.states w lookahead n).views (w.host r) ++ [w.askedEvent r β]).Pairwise
      fun e e' : Event H R Msg => e.reading ≤ e'.reading := by
  have hhandled := σ.handled_of_asked w lookahead hE
  have hview : (σ.states w lookahead (n + 1)).views (w.host r)
      = (σ.states w lookahead n).views (w.host r) ++ [w.askedEvent r β] := by
    rw [σ.views_succ w lookahead n (w.host r), hhandled]
    simp [World.askedEvent]
  rw [← hview]
  exact σ.views_pairwise w lookahead (n + 1) (w.host r)

end Unisono.Spec
