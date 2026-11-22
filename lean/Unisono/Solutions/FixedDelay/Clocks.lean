/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Views

/-!
# The baseline in a bounded world: the clocks

* A clock query reaches the sender (`query_inFlight`). The sender answers
  it, unless it has answered a newer query from the same host
  (`query_answered`, `answer_inFlight`). The answer reaches the querying
  host: at every step whose event occurs after the query's send time plus
  the longest delays to the sender and back, the host remembers an estimate
  from that query or a newer one (`answer_reaches`).
* The estimate that a host remembers is an NTP sample whose query and answer
  each took between the shortest and the longest delay of their link
  (`offset_sample`). After a device request at true time `a'`, the query
  behind the estimate was sent no earlier than `a'` minus one polling
  period converted to true time (`offset_recent`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- In a list of `c` copies of a message to host `j`, the `k`-th entry
(counting from zero) is preceded by exactly `k` messages to `j`. -/
theorem replicate_copies {α : Type} (c : ℕ) (j : H) (x : α) : ∀ k < c,
    ∃ hk : 0 + k < (List.replicate c (j, x)).length,
      (List.replicate c (j, x))[0 + k] = (j, x) ∧
      ((List.replicate c (j, x)).take (0 + k)).countP (fun s => s.1 = j) = k := by
  intro k hk
  refine ⟨by simpa using hk, by simp, ?_⟩
  simp [List.take_replicate, List.countP_replicate, min_eq_left hk.le]

/-- **A clock query reaches the sender.** When a host sends a clock query at
step `n`, at true time `s`, one copy of the query is in transit after the
step, and it reaches the sender within the link's delay bounds. -/
theorem query_inFlight (w : World H R) (B : Bounds H) (hw : w.WithinBounds B)
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

/-- **An answer reaches the querying host.** When the sender answers a clock
query from host `i` at step `n`, at true time `s₂`, one copy of the answer
is in transit after the step, and it reaches `i` within the link's delay
bounds. -/
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

/-- **Every clock query that reaches the sender is answered.** When a query
from host `i` reaches the sender at step `n`, at true time `s₂`, the sender
answers it at that step, or it answered a query from `i` with a reading at
least as large at an earlier step. -/
theorem query_answered (w : World H R) (lookahead : ℕ+) (hsender : p.sender = w.sender)
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
  · -- The sender has already answered a query from `i` with a later reading.
    obtain ⟨a, ha, hle⟩ : ∃ a, (memoryOf p w.sender ((σ.states w lookahead n).views w.sender)).answered i
        = some a ∧ sent ≤ a := by
      unfold answers at hans
      split at hans
      · rename_i a ha
        simp only [decide_eq_true_eq, not_lt] at hans
        exact ⟨a, ha, hans⟩
      · simp at hans
    rw [← hsender] at ha
    obtain ⟨l₁, e, l₂, hl, ⟨F₀, he⟩, hans₀⟩ := answered_query p _ ha
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

/-- **The answer to a clock query reaches the querying host.** Consider a
world that satisfies the bounds, and a host that sends a clock query at step
`n`, at true time `s`. At every step whose event occurs after `s` plus the
longest delays to the sender and back, the host remembers a clock estimate
from this query or from a query with a larger reading. -/
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
  obtain ⟨arr₁, -, harr₁, hin₁⟩ := query_inFlight p w B hw lookahead hsender hcopies hn hask
  have hnk : n + 1 ≤ k := by
    by_contra hcon
    have hmono := Solution.eventTime_mono w (solution p) lookahead (Nat.lt_succ_iff.mp (not_le.mp hcon))
    rw [Solution.handled_time w (solution p) lookahead hn] at hmono
    linarith
  obtain ⟨n₁, -, hn₁k, hh₁⟩ := Solution.handled_before w (solution p) lookahead hin₁ hnk
    (by simp only; linarith)
  simp only at hh₁
  obtain ⟨n₀, hn₀, s₀, hs₀, sent₀, F₀, hle, hh₀, hans₀⟩ :=
    query_answered p w lookahead hsender hh₁
  obtain ⟨arr₂, -, harr₂, hin₂⟩ := answer_inFlight p w B hw lookahead hsender hcopies hh₀ hans₀
  have h0k : n₀ + 1 ≤ k := by omega
  have harr₂k : arr₂ < (solution p : Solution H R Payload).eventTime w lookahead k := by linarith
  obtain ⟨n₂, -, hn₂k, hh₂⟩ := Solution.handled_before w (solution p) lookahead hin₂ h0k harr₂k
  have hmem := Solution.mem_views_of_handled w (solution p) lookahead hh₂ hn₂k
  obtain ⟨t₁, θ, hoff, hle'⟩ := offset_latest p h hh _ hmem rfl
  exact ⟨t₁, θ, hoff, hle.trans hle'⟩

/-- **The clock estimate that a host remembers is an NTP sample.** Consider
a world that satisfies the bounds, and a host `h` other than the sender's
host that remembers the estimate `(t₁, θ)` at step `k`. Then there are true
times `s₁`, `s₂` and `s₄` with the following properties. The query left `h`
at `s₁`, with reading `t₁ = C_h(s₁)`; it reached the sender at `s₂`; its
answer reached `h` at `s₄`, no later than the event of step `k`. The query
and the answer each took between the shortest and the longest delay of
their link, and `θ = C_sender(s₂) - (C_h(s₁) + C_h(s₄)) / 2`, where `C_h`
and `C_sender` are the clocks of `h` and of the sender. -/
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

/-- **The clock estimate that a host remembers is recent.** Consider a world
that satisfies the bounds, and a step `n'` that handles a device request at
a host `h` other than the sender's host, at true time `a'`. At every step
whose event occurs after `a'` plus the longest delays to the sender and
back, `h` remembers an estimate from a query sent no earlier than
`a' - period / (1 - ε_C)`, where `period` is the polling period and `ε_C`
bounds the clocks' rate error. -/
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
