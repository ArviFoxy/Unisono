/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelayMemory
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
* **The clocks.** A question for the sender's clock reaches the sender, the
  sender answers it or a later question of the same host, and the answer
  reaches the asking host: at every step whose event comes later than the
  question plus the longest delays to the sender and back, the host
  remembers an estimate from a question as late or later (`answer_reaches`).
  The estimate a host remembers is an NTP sample whose question and answer
  took between the least and the longest delays (`offset_sample`).
* **What a host remembers at a step.** A speaker host other than the
  sender's remembers a block handed over before the step, and no earlier than
  any block handed over more than the longest delay from the sender before it
  (`block_memory`). It remembers a clock estimate from a question that left
  no earlier than an earlier request less one period of the questions
  (`offset_recent`). At a request of a speaker it continues from the position
  chosen at the speaker's previous request (`last_at_next_request`).
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

/-- The `c` copies of a message in a list of `c` copies are consecutive
messages to their destination. -/
theorem replicate_copies {α : Type} (c : ℕ) (j : H) (x : α) : ∀ k < c,
    ∃ hk : 0 + k < (List.replicate c (j, x)).length,
      (List.replicate c (j, x))[0 + k] = (j, x) ∧
      ((List.replicate c (j, x)).take (0 + k)).countP (fun s => s.1 = j) = k := by
  intro k hk
  refine ⟨by simpa using hk, by simp, ?_⟩
  simp [List.take_replicate, List.countP_replicate, min_eq_left hk.le]

/-- **A question reaches the sender.** When a host asks for the sender's
clock at step `n`, at true time `s`, one copy of the question is in transit
after the step and reaches the sender within the link's delays. -/
theorem question_inFlight (w : World H R) (B : Bounds H) (hw : w.WithinBounds B)
    (lookahead : ℕ+) (hsender : p.sender = w.sender) (hcopies : B.lossRun < p.copies)
    {n : ℕ} {h : H} {s : Time} {r : Fin R} {outs : List ℕ} {st : ℝ}
    (hn : (solution p : Solution H R Payload).handled w lookahead n = some (h, s, .asked r outs st))
    (hask : asks p h (memoryOf p h (((solution p : Solution H R Payload).states w lookahead n).views h))
      ((w.clock h).read s) = true) :
    ∃ arr, s + B.delayLeast h w.sender ≤ arr ∧ arr ≤ s + B.delayMost h w.sender ∧
      (⟨arr, h, w.sender, Payload.ask ((w.clock h).read s), ∅⟩ : InFlight H Payload)
        ∈ ((solution p : Solution H R Payload).states w lookahead (n + 1)).inFlight := by
  have hS : ((solution p : Solution H R Payload) h
      (((solution p : Solution H R Payload).states w lookahead n).views h
        ++ [⟨(w.clock h).read s, .asked r outs st⟩])).sends
      = List.replicate p.copies (w.sender, (Payload.ask ((w.clock h).read s), (∅ : Finset ℕ))) := by
    rw [solution_append]
    simp only [act, hask, ite_true, hsender]
  obtain ⟨arr, h1, h2, hin⟩ := Solution.copy_inFlight (solution p) w B hw lookahead hn hS hcopies
    (replicate_copies p.copies w.sender _)
  exact ⟨arr, h1, h2, by simpa using hin⟩

/-- **The sender answers a question.** When the sender answers a question of
host `i` at step `n`, at true time `s₂`, one copy of the answer is in
transit after the step and reaches `i` within the link's delays. -/
theorem answer_inFlight (w : World H R) (B : Bounds H) (hw : w.WithinBounds B)
    (lookahead : ℕ+) (hsender : p.sender = w.sender) (hcopies : B.lossRun < p.copies)
    {n : ℕ} {s₂ : Time} {i : H} {sent : ℝ} {F : Finset ℕ}
    (hn : (solution p : Solution H R Payload).handled w lookahead n
      = some (w.sender, s₂, .received i (.ask sent) F))
    (hans : answers (memoryOf p w.sender
      (((solution p : Solution H R Payload).states w lookahead n).views w.sender)) i sent = true) :
    ∃ arr, s₂ + B.delayLeast w.sender i ≤ arr ∧ arr ≤ s₂ + B.delayMost w.sender i ∧
      (⟨arr, w.sender, i, Payload.answer sent ((w.clock w.sender).read s₂), ∅⟩ : InFlight H Payload)
        ∈ ((solution p : Solution H R Payload).states w lookahead (n + 1)).inFlight := by
  have hS : ((solution p : Solution H R Payload) w.sender
      (((solution p : Solution H R Payload).states w lookahead n).views w.sender
        ++ [⟨(w.clock w.sender).read s₂, .received i (.ask sent) F⟩])).sends
      = List.replicate p.copies (i, (Payload.answer sent ((w.clock w.sender).read s₂), (∅ : Finset ℕ))) := by
    rw [solution_append]
    simp only [act, hans, hsender, and_self, ite_true]
  obtain ⟨arr, h1, h2, hin⟩ := Solution.copy_inFlight (solution p) w B hw lookahead hn hS hcopies
    (replicate_copies p.copies i _)
  exact ⟨arr, h1, h2, by simpa using hin⟩

/-- **Every question that reaches the sender is answered.** When a question
of host `i` reaches the sender at step `n`, at true time `s₂`, the sender
answers at that step or answered, at an earlier step and time, a question of
`i` whose reading is as late or later. -/
theorem question_answered (w : World H R) (lookahead : ℕ+) (hsender : p.sender = w.sender)
    {n : ℕ} {s₂ : Time} {i : H} {sent : ℝ} {F : Finset ℕ}
    (hn : (solution p : Solution H R Payload).handled w lookahead n
      = some (w.sender, s₂, .received i (.ask sent) F)) :
    ∃ n₀ ≤ n, ∃ s₀ ≤ s₂, ∃ sent₀ F₀, sent ≤ sent₀ ∧
      (solution p : Solution H R Payload).handled w lookahead n₀
        = some (w.sender, s₀, .received i (.ask sent₀) F₀) ∧
      answers (memoryOf p w.sender
        (((solution p : Solution H R Payload).states w lookahead n₀).views w.sender)) i sent₀
        = true := by
  set σ : Solution H R Payload := solution p
  by_cases hans : answers (memoryOf p w.sender ((σ.states w lookahead n).views w.sender)) i sent = true
  · exact ⟨n, le_rfl, s₂, le_rfl, sent, F, le_rfl, hn, hans⟩
  · -- The sender answered a question of `i` with a later reading before.
    obtain ⟨a, ha, hle⟩ : ∃ a, (memoryOf p w.sender ((σ.states w lookahead n).views w.sender)).answered i
        = some a ∧ sent ≤ a := by
      unfold answers at hans
      split at hans
      · rename_i a ha
        simp only [decide_eq_true_eq, not_lt] at hans
        exact ⟨a, ha, hans⟩
      · simp at hans
    rw [← hsender] at ha
    obtain ⟨l₁, e, l₂, hl, ⟨F₀, he⟩, hans₀⟩ := answered_question p _ ha
    rw [hsender] at hl hans₀
    obtain ⟨n₀, hn₀, hv₀, t, obs, hh₀, rfl⟩ := σ.handled_of_views_eq w lookahead hl
    simp only at he
    subst he
    have ht₀ := σ.handled_time w lookahead hh₀
    have ht := σ.handled_time w lookahead hn
    have hmono := σ.eventTime_mono w lookahead hn₀.le
    refine ⟨n₀, hn₀.le, t, by rw [← ht₀, ← ht]; exact hmono, a, F₀, hle, hh₀, ?_⟩
    rw [hv₀]
    exact hans₀

/-- **A question's answer reaches the asking host.** In a world within
bounds, when a host asks for the sender's clock at step `n`, at true time
`s`, then at every step whose event comes later than `s` plus the longest
delays to the sender and back, the host remembers a clock estimate from a
question whose reading is as late or later. -/
theorem answer_reaches (w : World H R) (B : Bounds H) (hw : w.WithinBounds B)
    (lookahead : ℕ+) (hsender : p.sender = w.sender) (hcopies : B.lossRun < p.copies)
    {n : ℕ} {h : H} {s : Time} {r : Fin R} {outs : List ℕ} {st : ℝ}
    (hn : (solution p : Solution H R Payload).handled w lookahead n = some (h, s, .asked r outs st))
    (hask : asks p h (memoryOf p h (((solution p : Solution H R Payload).states w lookahead n).views h))
      ((w.clock h).read s) = true)
    {k : ℕ} (hk : s + B.delayMost h w.sender + B.delayMost w.sender h
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    ∃ t₁ θ, (memoryOf p h (((solution p : Solution H R Payload).states w lookahead k).views h)).offset
      = some (t₁, θ) ∧ (w.clock h).read s ≤ t₁ := by
  have hh : h ≠ p.sender := by
    have := hask
    simp only [asks, Bool.and_eq_true, bne_iff_ne] at this
    exact this.1
  have hd₁ := (B.delayLeast_pos h w.sender).trans_le (B.delayLeast_le h w.sender)
  have hd₂ := (B.delayLeast_pos w.sender h).trans_le (B.delayLeast_le w.sender h)
  obtain ⟨arr₁, -, harr₁, hin₁⟩ := question_inFlight p w B hw lookahead hsender hcopies hn hask
  have hnk : n + 1 ≤ k := by
    by_contra hcon
    have hmono := Solution.eventTime_mono w (solution p) lookahead (Nat.lt_succ_iff.mp (not_le.mp hcon))
    rw [Solution.handled_time w (solution p) lookahead hn] at hmono
    linarith
  obtain ⟨n₁, -, hn₁k, hh₁⟩ := Solution.handled_before w (solution p) lookahead hin₁ hnk
    (by simp only; linarith)
  simp only at hh₁
  obtain ⟨n₀, hn₀, s₀, hs₀, sent₀, F₀, hle, hh₀, hans₀⟩ :=
    question_answered p w lookahead hsender hh₁
  obtain ⟨arr₂, -, harr₂, hin₂⟩ := answer_inFlight p w B hw lookahead hsender hcopies hh₀ hans₀
  have h0k : n₀ + 1 ≤ k := by omega
  have harr₂k : arr₂ < (solution p : Solution H R Payload).eventTime w lookahead k := by linarith
  obtain ⟨n₂, -, hn₂k, hh₂⟩ := Solution.handled_before w (solution p) lookahead hin₂ h0k harr₂k
  have hmem := Solution.mem_views_of_handled w (solution p) lookahead hh₂ hn₂k
  obtain ⟨t₁, θ, hoff, hle'⟩ := offset_latest p h hh _ hmem rfl
  exact ⟨t₁, θ, hoff, hle.trans hle'⟩

/-- **The clock estimate that a host remembers is an NTP sample.** In a world
within bounds, when a host other than the sender's remembers at step `k` the
estimate `θ` of the question with reading `t₁`, that question left at a true
time `s₁` with `t₁` the host's reading then, it reached the sender at `s₂`,
and the answer reached the host at `s₄`, no later than the step's event, each
within the link's delays; `θ` is the estimate from the sender's reading at
`s₂` and the host's readings at `s₁` and `s₄`. -/
theorem offset_sample (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) {k : ℕ} {h : H} (hh : h ≠ w.sender) {t₁ θ : ℝ}
    (ho : (memoryOf p h (((solution p : Solution H R Payload).states w lookahead k).views h)).offset
      = some (t₁, θ)) :
    ∃ s₁ s₂ s₄, (w.clock h).read s₁ = t₁
      ∧ s₄ ≤ (solution p : Solution H R Payload).eventTime w lookahead k
      ∧ B.delayLeast h w.sender ≤ s₂ - s₁ ∧ s₂ - s₁ ≤ B.delayMost h w.sender
      ∧ B.delayLeast w.sender h ≤ s₄ - s₂ ∧ s₄ - s₂ ≤ B.delayMost w.sender h
      ∧ θ = (w.clock w.sender).read s₂ - ((w.clock h).read s₁ + (w.clock h).read s₄) / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hdelays, -⟩ := hw
  obtain ⟨e, he, i, t₂, F, heo, hθ⟩ := offset_received p h (hsender ▸ hh) _ ho
  obtain ⟨j, hj, s₄, obs, hhj, rfl⟩ := Solution.handled_of_mem_views w (solution p) lookahead he
  simp only at heo hθ
  subst heo
  obtain ⟨m, hm, hdest, harr, -, hcont, -⟩ := Solution.handled_received w (solution p) lookahead hhj
  have hO := origin_inFlight p w lookahead hsender j m hm
  unfold Origin at hO
  simp only [hcont] at hO
  obtain ⟨s₁, s₂, q, q', -, hs₁, hs₂, hdl₁, hdl₂⟩ := hO
  rw [hdest] at hs₁ hdl₁ hdl₂
  rw [harr] at hdl₂
  have hD₁ := hdelays h w.sender s₁ q s₂ hdl₁
  have hD₂ := hdelays w.sender h s₂ q' s₄ hdl₂
  have hj' : s₄ ≤ (solution p : Solution H R Payload).eventTime w lookahead k := by
    rw [← Solution.handled_time w (solution p) lookahead hhj]
    exact Solution.eventTime_mono w (solution p) lookahead hj.le
  refine ⟨s₁, s₂, s₄, hs₁.symm, hj', hD₁.1, hD₁.2, hD₂.1, hD₂.2, ?_⟩
  rw [hθ, hs₁, hs₂]

omit [DecidableEq H] in
/-- **The time that the baseline's target stands for.** Speaker `r`'s host
`h` gives output sample `k` of block `b` the time
`c(f) + (ô + (k - g) / ρ + θ̂ - L - ĉ)`, where `f` and `ĉ` are the first frame
and timestamp of a block `b'` of the source, `ô` and `g` the timestamp and
first output sample of block `b`, and `θ̂` an estimate of the sender's clock
minus the host's within `e` of their true difference at some time `s₂`. In a
world within bounds, that time is within
`2 ε_R + e + 2 ε_C |o(g) - s₂| + ε_C |o(g) - c(f)| + ε_D (k - g) / ρ` of
`o(k) - L`. -/
theorem target_time_error (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (r : Fin R)
    {b b' k : ℕ} (hk : (w.speaker r).first b ≤ k) {s₂ θ L e : ℝ}
    (hθ : |θ - ((w.clock w.sender).read s₂ - (w.clock (w.host r)).read s₂)| ≤ e) :
    |w.source.capture (w.source.first b')
        + ((w.speaker r).reported b + ((k : ℝ) - (w.speaker r).first b) / w.rate + θ - L
          - w.source.reported b')
        - ((w.speaker r).out k - L)|
      ≤ 2 * B.report + e
        + 2 * B.clockRate * |(w.speaker r).out ((w.speaker r).first b) - s₂|
        + B.clockRate * |(w.speaker r).out ((w.speaker r).first b)
            - w.source.capture (w.source.first b')|
        + B.deviceRate * ((k : ℝ) - (w.speaker r).first b) / w.rate := by
  obtain ⟨hclocks, -, hspeakers, hsrc, hsp, -, -, -, -, -, -⟩ := hw
  set g := (w.speaker r).first b
  set f := w.source.first b'
  set C := w.clock (w.host r)
  set S := w.clock w.sender
  set og := (w.speaker r).out g
  set cf := w.source.capture f
  have h₁ := abs_le.mp (hsp r b)
  have h₂ := abs_le.mp (hsrc b')
  have hθ' := abs_le.mp hθ
  have hdrift := abs_le.mp (offset_drift_abs (hclocks (w.host r)) (hclocks w.sender) s₂ og)
  have hS := abs_le.mp (Clock.read_sub_near (hclocks w.sender) cf og)
  have hout := PlaybackDevice.out_sub_mem (hspeakers r) hk
  have hrate := w.rate_pos
  have hkg : (0 : ℝ) ≤ (k : ℝ) - g := by
    have : (g : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have e1 : (1 - B.deviceRate) / w.rate * ((k : ℝ) - g)
      = ((k : ℝ) - g) / w.rate - B.deviceRate * ((k : ℝ) - g) / w.rate := by
    field_simp
  have e2 : (1 + B.deviceRate) / w.rate * ((k : ℝ) - g)
      = ((k : ℝ) - g) / w.rate + B.deviceRate * ((k : ℝ) - g) / w.rate := by
    field_simp
  rw [e1] at hout
  rw [e2] at hout
  rw [abs_le]
  constructor <;> linarith [hout.1, hout.2]

/-- One step of the pace: the distance to the trajectory ends within `B`, or
shrinks by at least `w - ν`. -/
theorem advance_step {w ν B D e δ : ℝ} (hw : ν < w) (he : |e| ≤ B) (hδ : |δ| ≤ ν) :
    |D - δ + clamp w (e + δ - D)| ≤ max B (|D| - (w - ν)) := by
  have he' := abs_le.mp he
  have hδ' := abs_le.mp hδ
  have hD := le_abs_self D
  have hD' := neg_abs_le D
  have m1 := le_max_left B (|D| - (w - ν))
  have m2 := le_max_right B (|D| - (w - ν))
  unfold clamp
  rcases le_or_gt (e + δ - D) w with h1 | h1
  · rw [min_eq_right h1]
    rcases le_or_gt (-w) (e + δ - D) with h2 | h2
    · rw [max_eq_right h2, abs_le]
      constructor <;> linarith
    · rw [max_eq_left h2.le, abs_le]
      constructor <;> linarith
  · rw [min_eq_left h1.le, max_eq_right (by linarith), abs_le]
    constructor <;> linarith

/-- **The pace reaches the target's band from anywhere.** Let a position `x`
advance by one frame per output sample, corrected towards the target `xs`
by at most `w` frames, and let the target stay within `B` frames of a
trajectory `T` that advances by one frame per output sample within
`ν < w`. Whatever its distance from the trajectory at the start, the
position is within `B` of it from some output sample on. -/
theorem advance_converges {w ν B : ℝ} (hw : ν < w) (x xs T : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ k, K ≤ k → x (k + 1) = x k + 1 + clamp w (xs (k + 1) - x k - 1))
    (hband : ∀ k, K ≤ k → |xs k - T k| ≤ B)
    (hT : ∀ k, K ≤ k → |T (k + 1) - T k - 1| ≤ ν) :
    ∃ K', K ≤ K' ∧ ∀ k, K' ≤ k → |x k - T k| ≤ B := by
  have hgap : 0 < w - ν := by linarith
  -- After `j` steps the distance is at most `B` or its start less `j (w - ν)`.
  have hdecay : ∀ j : ℕ, |x (K + j) - T (K + j)| ≤ max B (|x K - T K| - j * (w - ν)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hk : K ≤ K + j := Nat.le_add_right K j
      have hs := hstep (K + j) hk
      have hb := hband (K + j + 1) (by omega)
      have ht := hT (K + j) hk
      have key := advance_step (D := x (K + j) - T (K + j)) (e := xs (K + j + 1) - T (K + j + 1))
        (δ := T (K + j + 1) - T (K + j) - 1) hw hb ht
      have hx : x (K + (j + 1)) - T (K + (j + 1))
          = (x (K + j) - T (K + j)) - (T (K + j + 1) - T (K + j) - 1)
            + clamp w ((xs (K + j + 1) - T (K + j + 1)) + (T (K + j + 1) - T (K + j) - 1)
              - (x (K + j) - T (K + j))) := by
        rw [show K + (j + 1) = K + j + 1 by ring, hs]
        ring_nf
      rw [hx]
      refine key.trans ?_
      push_cast
      apply max_le (le_max_left _ _)
      rcases le_total B (|x K - T K| - j * (w - ν)) with hc | hc
      · rw [max_eq_right hc] at ih
        apply le_max_of_le_right
        linarith
      · rw [max_eq_left hc] at ih
        apply le_max_of_le_left
        linarith
  -- Enough steps bring the distance within `B`.
  obtain ⟨j, hj⟩ := exists_nat_ge (|x K - T K| / (w - ν))
  have hin : |x (K + j) - T (K + j)| ≤ B := by
    have h := hdecay j
    have hmul : |x K - T K| ≤ j * (w - ν) := by
      have := (div_le_iff₀ hgap).mp hj
      linarith
    have hB : 0 ≤ B := le_trans (abs_nonneg _) (hband K le_rfl)
    exact h.trans (max_le le_rfl (by linarith))
  refine ⟨K + j, Nat.le_add_right K j, ?_⟩
  exact advance_tracks hw x xs T (K + j) (fun k hk => hstep k (by omega))
    (fun k hk => hband k (by omega)) (fun k hk => hT k (by omega)) hin

/-- **A speaker continues at its next request from where it ended.** At the
step that handles request `b + 1` of speaker `r`, its host remembers for `r`
the output sample and position chosen last at request `b`. -/
theorem last_at_next_request (w : World H R) (lookahead : ℕ+) {n₁ n₂ : ℕ} {r : Fin R} {b : ℕ}
    (hb₁ : ((solution p : Solution H R Payload).states w lookahead n₁).askedNext r = b)
    (he₁ : earliest (((solution p : Solution H R Payload).states w lookahead n₁).key w)
      ((solution p : Solution H R Payload).states w lookahead n₁).due = some (.asked r b))
    (hb₂ : ((solution p : Solution H R Payload).states w lookahead n₂).askedNext r = b + 1)
    (hn : n₁ < n₂) :
    (memoryOf p (w.host r) (((solution p : Solution H R Payload).states w lookahead n₂).views (w.host r))).last r
      = lastChosen (positions p (memoryOf p (w.host r)
          (((solution p : Solution H R Payload).states w lookahead n₁).views (w.host r))) r
          ((w.speaker r).block b) ((w.speaker r).reported b)) := by
  set σ : Solution H R Payload := solution p
  have hh := σ.handled_of_asked w lookahead he₁
  have hsucc := σ.askedNext_succ w lookahead (hb₁ ▸ he₁)
  rw [hb₁] at hsucc
  have hv₁ : (σ.states w lookahead (n₁ + 1)).views (w.host r)
      = (σ.states w lookahead n₁).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
          .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩] := by
    rw [σ.views_succ w lookahead n₁ (w.host r), hh]
    simp
  obtain ⟨l, hl, hev⟩ := σ.views_append w lookahead (show n₁ + 1 ≤ n₂ by omega) (w.host r)
  rw [hl, hv₁, List.append_assoc, List.singleton_append]
  apply last_after_request p (w.host r) _ _ l rfl
  intro e he outs st heo
  obtain ⟨i, hi₁, hi₂, t, obs, hhi, rfl⟩ := hev e he
  simp only at heo
  subst heo
  exact σ.no_request_between w lookahead (hsucc.trans hb₂.symm) hi₁ hi₂ hhi

/-- **Every block's message reaches every other speaker's host.** In a world
within bounds, when the baseline sends each message more times than a link
can drop in a row, a message of block `b` reaches every speaker host `j`
other than the sender's within the longest delay, and is handled before
every step whose event comes later. -/
theorem block_handled (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies)
    {j : H} (hj : j ∈ p.speakers) (hjs : j ≠ w.sender) {b k : ℕ}
    (hk : w.source.handed b + B.delayMost w.sender j
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    ∃ i < k, ∃ arr F, arr ≤ w.source.handed b + B.delayMost w.sender j ∧
      (solution p : Solution H R Payload).handled w lookahead i
        = some (j, arr, .received w.sender (.block (w.source.first b) (w.source.reported b)) F) := by
  set σ : Solution H R Payload := solution p with hσ
  have hdpos := B.delayLeast_pos w.sender j
  have hdle := B.delayLeast_le w.sender j
  have hlt : w.source.handed b < σ.eventTime w lookahead k := by linarith
  obtain ⟨n, hnk, hbn, hearly⟩ :=
    σ.exists_handed_step w lookahead (σ.lt_handedNext w lookahead hlt)
  have hn : σ.handled w lookahead n = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun m => (m, w.target m)) (w.source.reported b)) := by
    unfold Solution.handled
    rw [hearly]
  set x : H → Payload × Finset ℕ :=
    fun _ => (Payload.block (w.source.first b) (w.source.reported b), (w.source.block b).toFinset)
  have hjf : j ∈ p.speakers.filter (· ≠ p.sender) := by
    rw [List.mem_filter, hsender]
    exact ⟨hj, by simpa using hjs⟩
  obtain ⟨i0, hi0⟩ := replicate_entries p.copies x _ (hnodup.filter _) hjf
  have hS := solution_handed_sends p w hsender ((σ.states w lookahead n).views w.sender)
    ((w.clock w.sender).read (w.source.handed b)) b
  obtain ⟨arr, -, harr, hin⟩ := Solution.copy_inFlight σ w B hw lookahead hn hS hcopies hi0
  have h1 : n + 1 ≤ k := by omega
  have h2 : arr < σ.eventTime w lookahead k := by linarith
  obtain ⟨i, -, hik, hhi⟩ := Solution.handled_before w σ lookahead hin h1 h2
  exact ⟨i, hik, arr, _, harr, hhi⟩

/-- **The block that a speaker's host remembers.** In a world within bounds,
at step `k` a speaker host `h` other than the sender's remembers the first
frame and timestamp of a block `b'` handed over before the step's event, and
no earlier than any block `b''` handed over more than the longest delay from
the sender to `h` before it. -/
theorem block_memory (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies)
    {h : H} (hh : h ∈ p.speakers) (hhs : h ≠ w.sender) {k b'' : ℕ}
    (hb'' : w.source.handed b'' + B.delayMost w.sender h
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    ∃ b', (memoryOf p h (((solution p : Solution H R Payload).states w lookahead k).views h)).block
        = some (w.source.first b', w.source.reported b')
      ∧ b'' ≤ b' ∧ w.source.handed b' < (solution p : Solution H R Payload).eventTime w lookahead k := by
  set σ : Solution H R Payload := solution p with hσ
  obtain ⟨i, hik, arr, F, -, hhi⟩ := block_handled p w B hw lookahead hsender hnodup hcopies hh hhs hb''
  have hmem := Solution.mem_views_of_handled w σ lookahead hhi hik
  have hns : h ≠ p.sender := hsender ▸ hhs
  obtain ⟨f', c', hblock, hle⟩ := block_latest p h hns _ hmem rfl
  obtain ⟨e, he, i', F', heo⟩ := block_received p h hns _ hblock
  obtain ⟨j, hj, t, obs, hhj, rfl⟩ := Solution.handled_of_mem_views w σ lookahead he
  simp only at heo
  subst heo
  obtain ⟨m, hm, hdest, harr, -, hcont, -⟩ := Solution.handled_received w σ lookahead hhj
  have hO := origin_inFlight p w lookahead hsender j m hm
  unfold Origin at hO
  simp only [hcont] at hO
  obtain ⟨b', -, hf, hc, -, q, hq⟩ := hO
  refine ⟨b', by rw [hblock, hf, hc], ?_, ?_⟩
  · rw [hf] at hle
    exact w.source.first_strictMono.le_iff_le.mp hle
  · have hafter := w.network.after _ _ _ _ _ hq
    rw [harr] at hafter
    have htj : t ≤ σ.eventTime w lookahead k := by
      rw [← Solution.handled_time w σ lookahead hhj]
      exact Solution.eventTime_mono w σ lookahead hj.le
    linarith

/-- **The clock estimate that a speaker's host remembers is recent.** In a
world within bounds, when step `n'` handles a request of a speaker whose host
`h` is not the sender's, at true time `a'`, then at every step whose event
comes later than `a'` plus the longest delays to the sender and back, `h`
remembers an estimate from a question that left at a true time `s` no
earlier than `a'` less the period of the questions on `h`'s clock. -/
theorem offset_recent (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hcopies : B.lossRun < p.copies)
    (hperiod : 0 ≤ p.period) {n' : ℕ} {h : H} (hhs : h ≠ w.sender) {a' : Time} {r : Fin R}
    {outs : List ℕ} {st : ℝ}
    (hn' : (solution p : Solution H R Payload).handled w lookahead n' = some (h, a', .asked r outs st))
    {k : ℕ} (hk : a' + B.delayMost h w.sender + B.delayMost w.sender h
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    ∃ t₁ θ s, (memoryOf p h (((solution p : Solution H R Payload).states w lookahead k).views h)).offset
        = some (t₁, θ) ∧ (w.clock h).read s ≤ t₁ ∧ a' - p.period / (1 - B.clockRate) ≤ s := by
  set σ : Solution H R Payload := solution p with hσ
  have hclocks := hw.1
  have hε := B.clockRate_lt_one
  have hgap : 0 ≤ p.period / (1 - B.clockRate) := div_nonneg hperiod (by linarith)
  by_cases hask : asks p h (memoryOf p h ((σ.states w lookahead n').views h)) ((w.clock h).read a') = true
  · obtain ⟨t₁, θ, ho, hle⟩ := answer_reaches p w B hw lookahead hsender hcopies hn' hask hk
    exact ⟨t₁, θ, a', ho, hle, by linarith⟩
  · -- The host asked within the last period, at a request of its view.
    have hns : h ≠ p.sender := hsender ▸ hhs
    obtain ⟨x, hx, hlt⟩ : ∃ x, (memoryOf p h ((σ.states w lookahead n').views h)).asked = some x
        ∧ (w.clock h).read a' < x + p.period := by
      simp only [asks, Bool.and_eq_true, bne_iff_ne, not_and] at hask
      have hask' := hask hns
      split at hask'
      · rename_i x hx
        simp only [decide_eq_true_eq, not_le] at hask'
        exact ⟨x, hx, hask'⟩
      · simp at hask'
    obtain ⟨l₁, e, l₂, hl, hex, ⟨r'', outs', st', heo⟩, hask₀⟩ := asked_request p h _ hx
    obtain ⟨i, hi, hvi, s, obs, hhi, rfl⟩ := Solution.handled_of_views_eq w σ lookahead hl
    simp only at hex heo
    subst heo
    rw [← hvi] at hask₀
    have hsa : s ≤ a' := by
      rw [← Solution.handled_time w σ lookahead hhi, ← Solution.handled_time w σ lookahead hn']
      exact Solution.eventTime_mono w σ lookahead hi.le
    obtain ⟨t₁, θ, ho, hle⟩ := answer_reaches p w B hw lookahead hsender hcopies hhi hask₀
      (by linarith)
    refine ⟨t₁, θ, s, ho, hle, ?_⟩
    -- The host's clock advanced by less than the period from `s` to `a'`.
    have hadv := (Clock.advance_mem (hclocks h) hsa).1
    rw [← hex] at hlt
    have hlt' : (1 - B.clockRate) * (a' - s) < p.period := by linarith
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', div_eq_mul_inv]
    have hpos : 0 < 1 - B.clockRate := by linarith
    rw [le_mul_inv_iff₀ hpos]
    linarith

end Unisono.Solutions.FixedDelay
