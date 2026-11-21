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

* **Copies.** For any solution, when a host sends more copies of a message
  to another host, as consecutive messages on the link, than the link can
  lose in a row, one copy arrives within the link's delays
  (`Solution.copy_inFlight`).

* **The stream.** When the baseline sends each message more times than a
  link can drop in a row, every speaker's host holds the frames of a block
  at every step of the run whose event comes later than the block's handoff
  plus the longest delay from the sender (`block_arrives`).
* **Where messages come from.** Every message of the baseline in transit
  was sent where it should have been: a block message at its block's
  handoff, a question with its origin's reading, an answer with the
  sender's reading when a question arrived (`origin_inFlight`).
* **The pace.** A position corrected towards its target by at most `w`
  frames per output sample stays within `B` frames of a trajectory when the
  targets do and the trajectory drifts from one frame per output sample by
  less than `w` (`advance_tracks`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- **One of the copies arrives.** In a world within bounds, when the host
of step `n` sends `c` copies of a message to host `j` as consecutive
messages on the link, and `c` exceeds the losses that a link may have in a
row, one copy is in transit after the step and arrives within the link's
least and longest delays. -/
theorem Solution.copy_inFlight (σ : Solution H R Msg) (w : World H R) (B : Bounds H)
    (hw : w.WithinBounds B) (lookahead : ℕ+) {n : ℕ} {h : H} {t : Time}
    {obs : Observation H R Msg} (hn : σ.handled w lookahead n = some (h, t, obs))
    {S : List (H × Msg × Finset ℕ)}
    (hS : (σ h ((σ.states w lookahead n).views h ++ [⟨(w.clock h).read t, obs⟩])).sends = S)
    {j : H} {msg : Msg} {F : Finset ℕ} {i0 c : ℕ} (hc : B.lossRun < c)
    (hcopies : ∀ k < c, ∃ hk : i0 + k < S.length, S[i0 + k] = (j, msg, F)
      ∧ (S.take (i0 + k)).countP (fun s => s.1 = j) = k) :
    ∃ arr, t + B.delayLeast h j ≤ arr ∧ arr ≤ t + B.delayMost h j
      ∧ (⟨arr, h, j, msg, F.filter (· ∈ (σ.states w lookahead n).held h ∪ obs.frames)⟩
        : InFlight H Msg) ∈ (σ.states w lookahead (n + 1)).inFlight := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hdelays, hlosses⟩ := hw
  obtain ⟨k, hk, hsome⟩ := hlosses h j ((σ.states w lookahead n).sentCount h j) (fun _ => t)
  obtain ⟨arr, harr⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hidx, hget, hcount⟩ := hcopies k (lt_of_le_of_lt hk hc)
  have hdel := hdelays h j t _ arr harr
  have hin := σ.sent_inFlight w lookahead hn hS hidx (arr := arr)
    (by rw [hget]; simp only; rw [hcount]; exact harr)
  rw [hget] at hin
  exact ⟨arr, by linarith [hdel.1], by linarith [hdel.2], hin⟩

end Unisono.Spec

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
the sender's host: it sends the block's frames to every speaker's host other
than its own, `c` times each. -/
theorem solution_handed_sends (w : World H R) (hsender : p.sender = w.sender)
    (l : List (Event H R Payload)) (reading : ℝ) (b : ℕ) :
    ((solution p : Solution H R Payload) w.sender
        (l ++ [⟨reading, .handed ((w.source.block b).map fun n => (n, w.target n))
          (w.source.reported b)⟩])).sends
      = (p.speakers.filter (· ≠ p.sender)).flatMap fun j => List.replicate p.copies
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
a link can drop in a row, every speaker host `j` other than the sender's
holds the frames of block `b` at every step of the run whose event comes
later than the block's handoff plus the longest delay from the sender to
`j`. -/
theorem block_arrives (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies)
    {j : H} (hj : j ∈ p.speakers) (hjs : j ≠ w.sender) {b k : ℕ}
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
  have hjf : j ∈ p.speakers.filter (· ≠ p.sender) := by
    rw [List.mem_filter, hsender]
    exact ⟨hj, by simpa using hjs⟩
  obtain ⟨i0, hi0⟩ := replicate_entries p.copies x _ (hnodup.filter _) hjf
  obtain ⟨hi, hget, hcount⟩ := hi0 k' (lt_of_le_of_lt hk' hcopies)
  set sends := (σ w.sender (st.views w.sender ++ [⟨(w.clock w.sender).read t, obs⟩])).sends
    with hsendsdef
  have hsends : sends = (p.speakers.filter (· ≠ p.sender)).flatMap fun j =>
      List.replicate p.copies (j, x j) :=
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

/-- What the baseline sends, by the event it acts on: the stream at a
handoff, at the sender; answers to questions, at the sender; questions, at
another host's device request. -/
theorem sends_cases (h : H) (l : List (Event H R Payload)) (e : Event H R Payload)
    {s : H × Payload × Finset ℕ} (hs : s ∈ ((solution p : Solution H R Payload) h (l ++ [e])).sends) :
    (∃ frames stamp f t', e.observation = .handed frames stamp ∧ h = p.sender ∧
        frames.head? = some (f, t') ∧ s.1 ∈ p.speakers ∧ s.2.1 = .block f stamp ∧
        s.2.2 = (frames.map Prod.fst).toFinset)
      ∨ (∃ i sent F, e.observation = .received i (.ask sent) F ∧ h = p.sender ∧
        s = (i, .answer sent e.reading, ∅))
      ∨ (∃ r outputs stamp, e.observation = .asked r outputs stamp ∧ h ≠ p.sender ∧
        s = (p.sender, .ask e.reading, ∅)) := by
  simp only [solution, List.getLast?_append, List.getLast?_singleton, Option.some_or] at hs
  unfold act at hs
  split at hs
  · rename_i frames stamp hobs
    split_ifs at hs with hh
    · split at hs
      · rename_i f t' hhead
        simp only [List.mem_flatMap, List.mem_replicate] at hs
        obtain ⟨j, hj, -, rfl⟩ := hs
        exact Or.inl ⟨frames, stamp, f, t', hobs, hh, hhead, (List.mem_filter.mp hj).1, rfl, rfl⟩
      · simp at hs
    · simp at hs
  · rename_i i sent F hobs
    split_ifs at hs with hh
    · simp only [List.mem_replicate] at hs
      exact Or.inr (Or.inl ⟨i, sent, F, hobs, hh.1, hs.2⟩)
    · simp at hs
  · rename_i r outputs stamp hobs
    split_ifs at hs with hask
    · simp only [List.mem_replicate] at hs
      refine Or.inr (Or.inr ⟨r, outputs, stamp, hobs, ?_, hs.2⟩)
      simp only [asks, Bool.and_eq_true, bne_iff_ne] at hask
      exact hask.1
    · simp at hs
  · simp at hs

omit [DecidableEq H] in
/-- The first frame of a block handed over is the block's first frame. -/
theorem block_head (w : World H R) (b : ℕ) :
    ((w.source.block b).map fun n => (n, w.target n)).head?
      = some (w.source.first b, w.target (w.source.first b)) := by
  have hne : 0 < w.source.first (b + 1) - w.source.first b :=
    Nat.sub_pos_of_lt (w.source.first_strictMono (Nat.lt_succ_self b))
  unfold CaptureDevice.block
  obtain ⟨m, hm⟩ : ∃ m, w.source.first (b + 1) - w.source.first b = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hne).symm⟩
  rw [hm, List.range'_succ]
  simp

/-- Where a message of the baseline comes from. A block message was sent by
the sender at the handoff of its block, with the block's frames; a question
was sent by its origin to the sender, at the reading of its origin's clock
that it carries; an answer was sent by the sender, at the reading of its
clock that it carries, when a question of its destination arrived. -/
def Origin (w : World H R) (m : InFlight H Payload) : Prop :=
  match m.contents with
  | .block f stamp => ∃ b, m.origin = w.sender ∧ f = w.source.first b ∧
      stamp = w.source.reported b ∧ m.frames = (w.source.block b).toFinset ∧
      ∃ q, w.network.deliver w.sender m.destination (w.source.handed b) q = some m.arrival
  | .ask sent => ∃ s₁ q, m.destination = w.sender ∧ sent = (w.clock m.origin).read s₁ ∧
      w.network.deliver m.origin w.sender s₁ q = some m.arrival
  | .answer sent received => ∃ s₁ s₂ q q', m.origin = w.sender ∧
      sent = (w.clock m.destination).read s₁ ∧ received = (w.clock w.sender).read s₂ ∧
      w.network.deliver m.destination w.sender s₁ q = some s₂ ∧
      w.network.deliver w.sender m.destination s₂ q' = some m.arrival

/-- **Every message of the baseline in transit comes from where it should.** -/
theorem origin_inFlight (w : World H R) (lookahead : ℕ+) (hsender : p.sender = w.sender) :
    ∀ n, ∀ m ∈ ((solution p : Solution H R Payload).states w lookahead n).inFlight, Origin w m := by
  set σ : Solution H R Payload := solution p
  intro n
  induction n with
  | zero => intro m hm; simp [Solution.states, State.start] at hm
  | succ n ih =>
    intro m hm
    rcases σ.mem_inFlight_succ w lookahead n hm with hold | ⟨h, t, obs, hn, s, hs, ho, hd, hc, hf, q, hq⟩
    · exact ih m hold
    · rcases sends_cases p h _ _ hs with
        ⟨frames, stamp, f, t', hobs, hh, hhead, -, hs1, hs2⟩ | ⟨i, sent, F, hobs, hh, rfl⟩ |
          ⟨r, outputs, stamp, hobs, hh, rfl⟩
      · simp only at hobs
        subst hobs
        obtain ⟨b, hbh, hbt, hbf, hbs⟩ := σ.handled_handed w lookahead hn
        rw [hbf, block_head] at hhead
        simp only [Option.some.injEq, Prod.mk.injEq] at hhead
        unfold Origin
        rw [hc, hs1]
        refine ⟨b, ho.trans hbh, hhead.1.symm, hbs, ?_, q, ?_⟩
        · have hT : (((w.source.block b).map fun n => (n, w.target n)).map Prod.fst).toFinset
              = (w.source.block b).toFinset := by
            simp [List.map_map, Function.comp_def]
          rw [hf, hs2, hbf]
          simp only [Observation.frames, hT]
          exact Finset.filter_true_of_mem fun x hx => Finset.mem_union_right _ hx
        · rw [← hbh, ← hbt, hd]
          exact hq
      · simp only at hobs hd hc hq
        subst hobs
        obtain ⟨mq, hmq, hdest, harr, hor, hcont, -⟩ := σ.handled_received w lookahead hn
        have hO := ih mq hmq
        unfold Origin at hO
        simp only [hcont] at hO
        obtain ⟨s₁, q₁, -, hsent, hdel₁⟩ := hO
        unfold Origin
        simp only [hc]
        refine ⟨s₁, t, q₁, q, ?_, ?_, ?_, ?_, ?_⟩
        · rw [ho, hh, hsender]
        · rw [hd, hsent, hor]
        · rw [hh, hsender]
        · rw [hd, ← hor, ← harr]
          exact hdel₁
        · rw [hd, ← hsender, ← hh]
          exact hq
      · simp only at hd hc hq
        unfold Origin
        simp only [hc]
        refine ⟨t, q, ?_, ?_, ?_⟩
        · rw [hd, hsender]
        · rw [ho]
        · rw [ho, ← hsender]
          exact hq

/-- **The pace follows the target.** Let a speaker's position `x` advance by
one frame per output sample, corrected towards the target `xs` by at most
`w` frames, and let the target stay within `B` frames of a trajectory `T`
that advances by one frame per output sample within `ν < w`. A position
that starts within `B` of the trajectory stays within `B` of it. -/
theorem advance_tracks {w ν B : ℝ} (hw : ν < w) (x xs T : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ k, K ≤ k → x (k + 1) = x k + 1 + clamp w (xs (k + 1) - x k - 1))
    (hband : ∀ k, K ≤ k → |xs k - T k| ≤ B)
    (hT : ∀ k, K ≤ k → |T (k + 1) - T k - 1| ≤ ν)
    (hstart : |x K - T K| ≤ B) :
    ∀ k, K ≤ k → |x k - T k| ≤ B := by
  intro k hk
  induction hk with
  | refl => exact hstart
  | step hle ih =>
    rename_i k
    have hb := abs_le.mp (hband (k + 1) (Nat.le_succ_of_le hle))
    have hν := abs_le.mp (hT k hle)
    have hd := abs_le.mp ih
    rw [hstep k hle]
    unfold clamp
    set a := xs (k + 1) - x k - 1
    rcases le_or_gt a w with ha | ha
    · rw [min_eq_right ha]
      rcases le_or_gt (-w) a with ha' | ha'
      · rw [max_eq_right ha']
        rw [abs_le]
        constructor <;> linarith
      · rw [max_eq_left ha'.le]
        rw [abs_le]
        constructor <;> linarith
    · rw [min_eq_left ha.le, max_eq_right (by linarith)]
      rw [abs_le]
      constructor <;> linarith

end Unisono.Solutions.FixedDelay
