/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay
public import Unisono.Spec.Run
public import Unisono.Spec.Models.Bounded

/-!
# The baseline in a bounded world

What the baseline achieves in every world within the bounds of the bounded
model (`Unisono.Spec.Models.Bounded`).

* **The stream.** When the baseline sends each message more times than a
  link can drop in a row, every speaker's host holds the frames of a block
  at every step of the run whose event comes later than the block's handoff
  plus the longest delay from the sender (`block_arrives`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- In a list of sends that repeats each host's message `c` times, host by
host, the `c` messages to a host `j` that appears once are consecutive, and
the `k`-th of them comes after `k` earlier messages to `j`. -/
theorem replicate_entries {α : Type} [DecidableEq H] (c : ℕ) (x : H → α) :
    ∀ (l : List H), l.Nodup → ∀ {j : H}, j ∈ l → ∃ i0, ∀ k < c,
      ∃ hi : i0 + k < (l.flatMap fun j => List.replicate c (j, x j)).length,
        (l.flatMap fun j => List.replicate c (j, x j))[i0 + k] = (j, x j) ∧
        ((l.flatMap fun j => List.replicate c (j, x j)).take (i0 + k)).countP
          (fun s => s.1 = j) = k
  | [], _, _, hj => absurd hj (List.not_mem_nil)
  | a :: l, hl, j, hj => by
      rw [List.nodup_cons] at hl
      by_cases hja : j = a
      · subst hja
        refine ⟨0, fun k hk => ⟨by simp; omega, ?_, ?_⟩⟩
        · simp [List.flatMap_cons, List.getElem_append_left (by simpa using hk : k < (List.replicate c (j, x j)).length)]
        · simp only [zero_add, List.flatMap_cons]
          rw [List.take_append_of_le_length (by simpa using hk.le)]
          simp [List.take_replicate, List.countP_replicate, min_eq_left hk.le]
      · have hjl : j ∈ l := by
          rcases List.mem_cons.mp hj with h | h
          · exact absurd h hja
          · exact h
        obtain ⟨i0, hi0⟩ := replicate_entries c x l hl.2 hjl
        refine ⟨c + i0, fun k hk => ?_⟩
        obtain ⟨hi, hget, hcount⟩ := hi0 k hk
        refine ⟨by simp only [List.flatMap_cons, List.length_append, List.length_replicate]; omega,
          ?_, ?_⟩
        · simp only [List.flatMap_cons]
          rw [List.getElem_append_right (by simp only [List.length_replicate]; omega)]
          simp only [List.length_replicate, show c + i0 + k - c = i0 + k by omega]
          exact hget
        · simp only [List.flatMap_cons]
          rw [show c + i0 + k = (List.replicate c (a, x a)).length + (i0 + k) by simp; omega,
            List.take_length_add_append, List.countP_append, hcount]
          simp [List.countP_replicate, Ne.symm hja]

variable [DecidableEq H] (p : Params H)

/-- The baseline's action when the capture device hands over block `b` at
the sender's host: it sends the block's frames to every speaker's host, `c`
times each. -/
theorem solution_handed_sends (w : World H R) (hsender : p.sender = w.sender)
    (l : List (Event H R Payload)) (reading : ℝ) (b : ℕ) :
    ((solution p : Solution H R Payload) w.sender
        (l ++ [⟨reading, .handed ((w.source.block b).map fun n => (n, w.target n))
          (w.source.reported b)⟩])).sends
      = p.speakers.flatMap fun j => List.replicate p.copies
          (j, Payload.block (w.source.first b) (w.source.reported b), (w.source.block b).toFinset) := by
  have hne : 0 < w.source.first (b + 1) - w.source.first b :=
    Nat.sub_pos_of_lt (w.source.first_strictMono (Nat.lt_succ_self b))
  have hhead : ((w.source.block b).map fun n => (n, w.target n)).head?
      = some (w.source.first b, w.target (w.source.first b)) := by
    unfold CaptureDevice.block
    obtain ⟨m, hm⟩ : ∃ m, w.source.first (b + 1) - w.source.first b = m + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hne).symm⟩
    rw [hm, List.range'_succ]
    simp
  have hset : ((((w.source.block b).map fun n => (n, w.target n)).map Prod.fst).toFinset)
      = (w.source.block b).toFinset := by
    simp [List.map_map, Function.comp_def]
  simp only [solution, List.getLast?_append, List.getLast?_singleton, Option.some_or]
  simp only [act, hsender, ite_true, hhead, hset]

/-- **Every block reaches every speaker's host within the longest delay.** In
a world within bounds, when the baseline sends each message more times than
a link can drop in a row, every speaker host `j` holds the frames of block
`b` at every step of the run whose event comes later than the block's
handoff plus the longest delay from the sender to `j`. -/
theorem block_arrives (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies)
    {j : H} (hj : j ∈ p.speakers) {b k : ℕ}
    (hk : w.source.handed b + B.delayMost w.sender j
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    (w.source.block b).toFinset
      ⊆ ((solution p : Solution H R Payload).states w lookahead k).held j := by
  set σ : Solution H R Payload := solution p with hσ
  obtain ⟨-, -, -, -, -, -, -, -, -, hdelays, hlosses⟩ := hw
  have hdpos := B.delayLeast_pos w.sender j
  have hdle := B.delayLeast_le w.sender j
  have hlt : w.source.handed b < σ.eventTime w lookahead k := by linarith
  obtain ⟨n, hnk, hbn, hearly⟩ :=
    σ.exists_handed_step w lookahead (σ.lt_handedNext w lookahead hlt)
  set st := σ.states w lookahead n with hst
  set t := w.source.handed b with ht
  set obs : Observation H R Payload :=
    .handed ((w.source.block b).map fun m => (m, w.target m)) (w.source.reported b) with hobs
  set F := (w.source.block b).toFinset with hFdef
  set x : H → Payload × Finset ℕ :=
    fun _ => (Payload.block (w.source.first b) (w.source.reported b), F) with hx
  -- The run's state after the handoff.
  have hstep : σ.states w lookahead (n + 1)
      = { st.handle σ w lookahead w.sender t obs with handedNext := b + 1 } := by
    show st.step σ w lookahead = _
    unfold State.step
    rw [hearly]
  -- The link from the sender to `j` delivers one of the copies.
  obtain ⟨k', hk', hsome⟩ := hlosses w.sender j (st.sentCount w.sender j) (fun _ => t)
  obtain ⟨arr, harr⟩ := Option.isSome_iff_exists.mp hsome
  have hdelay := (hdelays w.sender j t _ arr harr).2
  -- That copy is in transit after the handoff.
  obtain ⟨i0, hi0⟩ := replicate_entries p.copies x p.speakers hnodup hj
  obtain ⟨hi, hget, hcount⟩ := hi0 k' (lt_of_le_of_lt hk' hcopies)
  set sends := (σ w.sender (st.views w.sender ++ [⟨(w.clock w.sender).read t, obs⟩])).sends
    with hsendsdef
  have hsends : sends = p.speakers.flatMap fun j => List.replicate p.copies (j, x j) :=
    solution_handed_sends p w hsender (st.views w.sender) ((w.clock w.sender).read t) b
  have hi' : i0 + k' < sends.length := hsends ▸ hi
  have hget' : sends[i0 + k'] = (j, x j) := (List.getElem_of_eq hsends hi').trans hget
  have hcount' : (sends.take (i0 + k')).countP (fun s => s.1 = j) = k' := by
    rw [hsends]; exact hcount
  have hdel := State.handle_delivered w σ lookahead st w.sender t obs (i0 + k') hi' (arr := arr)
    (by rw [hget']; simp only; rw [hcount']; exact harr)
  rw [hget'] at hdel
  have hF : (x j).2.filter (· ∈ st.held w.sender ∪ obs.frames) = F := by
    refine Finset.filter_true_of_mem fun m hm => Finset.mem_union_right _ ?_
    simpa [hobs, Observation.frames, List.map_map, Function.comp_def, hx, hFdef] using hm
  rw [hF] at hdel
  have hin : (⟨arr, w.sender, j, (x j).1, F⟩ : InFlight H Payload)
      ∈ (σ.states w lookahead (n + 1)).inFlight := by
    rw [hstep]
    exact hdel
  -- It is handled before the event of step `k`.
  exact σ.frames_arrive w lookahead hin hnk (by simp only; linarith)

end Unisono.Solutions.FixedDelay
