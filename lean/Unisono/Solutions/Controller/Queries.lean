/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Views
public import Unisono.Solutions.FixedDelay.Clocks
public import Unisono.Solutions.FixedDelay.NoLoss
public import Unisono.Solutions.FixedDelay.Progress

/-!
# The baseline's clock queries in a world without loss

A host of the baseline sends a clock query to the sender at a device request,
when its clock has advanced by the polling period since its last query. This
file follows one query in a world in which no message is lost and a message
from `i` to `j` sent at true time `s` arrives at `A i j s`, whatever the
delays are.

* `exists_query`: a host with a speaker sends a query between any true time
  `T` and any request of the speaker at which its clock has advanced by the
  polling period since `T`.
* `exchange_of_query`: if every later query of the host reaches the sender
  later than this one, then the sender answers this query, and from some
  step on the host's view holds the exchange: the host's reading when it
  sent the query, the sender's reading when the query arrived, and the
  host's reading when the answer arrived. `exchange_of_query_before` says
  from which steps: every step whose event is later than the arrival of
  the answer.

The condition on later queries holds for a query that no pause delays on its
way to the sender, because a pause can only add to a delay.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- **A host sends a clock query in every long enough period.** Consider a
world whose devices hand over and request blocks without end, a speaker `r`
whose host is not the sender's, a true time `T`, and a request `b` of the
speaker at which the clock of its host has advanced by at least the polling
period since `T`. Then the host sends a clock query at a device request
between `T` and that request. -/
theorem exists_query (w : World H R) (lookahead : ℕ+)
    (hhand : ∀ T, ∃ b, T < w.source.handed b) (hask : ∀ r T, ∃ b, T < (w.speaker r).asked b)
    (hperiod : 0 ≤ p.period) (r : Fin R) (hhs : w.host r ≠ p.sender) {T : Time} {b : ℕ}
    (hb : (w.clock (w.host r)).read T + p.period
      ≤ (w.clock (w.host r)).read ((w.speaker r).asked b)) :
    ∃ n s r' outs st,
      (solution p : Solution H R Payload).handled w lookahead n
        = some (w.host r, s, .asked r' outs st)
      ∧ asks p (w.host r) (memoryOf p (w.host r)
          (((solution p : Solution H R Payload).states w lookahead n).views (w.host r)))
          ((w.clock (w.host r)).read s) = true
      ∧ T ≤ s ∧ s ≤ (w.speaker r).asked b := by
  set σ : Solution H R Payload := solution p with hσ
  obtain ⟨k, -, hke⟩ := request_step_of_unbounded p w lookahead hhand hask r b
  have hk := Solution.handled_of_asked w σ lookahead hke
  by_cases hasks : asks p (w.host r) (memoryOf p (w.host r) ((σ.states w lookahead k).views
      (w.host r))) ((w.clock (w.host r)).read ((w.speaker r).asked b)) = true
  · refine ⟨k, _, r, _, _, hk, hasks, ?_, le_rfl⟩
    have h1 : (w.clock (w.host r)).read T ≤ (w.clock (w.host r)).read ((w.speaker r).asked b) := by
      linarith
    exact (w.clock (w.host r)).strictMono.le_iff_le.mp h1
  · -- The host asked within the last period, at a request of its view.
    obtain ⟨x, hx, hlt⟩ : ∃ x, (memoryOf p (w.host r) ((σ.states w lookahead k).views
          (w.host r))).asked = some x
        ∧ (w.clock (w.host r)).read ((w.speaker r).asked b) < x + p.period := by
      simp only [asks, Bool.and_eq_true, bne_iff_ne, not_and] at hasks
      have hask' := hasks hhs
      split at hask'
      · rename_i x hx
        simp only [decide_eq_true_eq, not_le] at hask'
        exact ⟨x, hx, hask'⟩
      · simp at hask'
    obtain ⟨l₁, e, l₂, hl, hex, ⟨r'', outs', st', heo⟩, hask₀⟩ := asked_request p (w.host r) _ hx
    obtain ⟨i, hi, hvi, s, obs, hhi, rfl⟩ := Solution.handled_of_views_eq w σ lookahead hl
    simp only at hex heo
    subst heo
    rw [← hvi] at hask₀
    have hsa : s ≤ (w.speaker r).asked b := by
      rw [← Solution.handled_time w σ lookahead hhi, ← Solution.handled_time w σ lookahead hk]
      exact Solution.eventTime_mono w σ lookahead hi.le
    refine ⟨i, s, r'', outs', st', hhi, hask₀, ?_, hsa⟩
    have h1 : (w.clock (w.host r)).read T < (w.clock (w.host r)).read s := by
      rw [hex]
      linarith
    exact ((w.clock (w.host r)).strictMono.lt_iff_lt.mp h1).le

/-- **The exchange of a clock query is in the host's view once its answer
has arrived.** Consider a world in which no message is lost and a message
from `i` to `j` sent at `s` arrives at `A i j s`. A host `h` sends a clock
query at true time `s`, and every later query of `h` reaches the sender
later than this one. Then at every step of the run whose event is later
than the arrival of the answer, the view of `h` holds the exchange of this
query: the reading of `h` at `s`, the sender's reading when the query
arrived, and the reading of `h` when the answer arrived. -/
theorem exchange_of_query_before (w : World H R) (lookahead : ℕ+) {A : H → H → Time → Time}
    (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hsender : p.sender = w.sender) (hcopies : 0 < p.copies)
    {n : ℕ} {h : H} {s : Time} {r : Fin R} {outs : List ℕ} {st : ℝ}
    (hn : (solution p : Solution H R Payload).handled w lookahead n
      = some (h, s, .asked r outs st))
    (hask : asks p h (memoryOf p h
      (((solution p : Solution H R Payload).states w lookahead n).views h))
      ((w.clock h).read s) = true)
    (hstrict : ∀ s', s < s' → A h w.sender s < A h w.sender s') {k' : ℕ}
    (hk' : A w.sender h (A h w.sender s)
      < (solution p : Solution H R Payload).eventTime w lookahead k') :
    (⟨(w.clock h).read s, (w.clock w.sender).read (A h w.sender s),
        (w.clock h).read (A w.sender h (A h w.sender s))⟩ : Controller.Exchange)
      ∈ Controller.plainExchangesOf
        (((solution p : Solution H R Payload).states w lookahead k').views h) := by
  set σ : Solution H R Payload := solution p with hσ
  -- The query is in transit after step `n`.
  have hS : (σ h ((σ.states w lookahead n).views h
        ++ [⟨(w.clock h).read s, .asked r outs st⟩])).sends
      = List.replicate p.copies
          (w.sender, (Payload.ask ((w.clock h).read s), (∅ : Finset ℕ))) := by
    rw [hσ] at hask
    rw [hσ, solution_append]
    simp only [act, hask, ite_true, hsender]
  have hlen : 0 < (List.replicate p.copies
      (w.sender, (Payload.ask ((w.clock h).read s), (∅ : Finset ℕ)))).length := by
    simpa using hcopies
  have hin₁ := σ.sent_inFlight w lookahead hn hS hlen (arr := A h w.sender s)
    (by rw [List.getElem_replicate]; exact hA _ _ _ _)
  simp only [List.getElem_replicate, Finset.filter_empty] at hin₁
  -- It is handled by the sender.
  have hsn : σ.eventTime w lookahead n = s := Solution.handled_time w σ lookahead hn
  have hafter₁ : s < A h w.sender s := w.network.after _ _ _ _ _ (hA h w.sender s 0)
  have hafter₁' : A h w.sender s < A w.sender h (A h w.sender s) :=
    w.network.after _ _ _ _ _ (hA w.sender h (A h w.sender s) 0)
  have hk₁ : A h w.sender s < σ.eventTime w lookahead k' := hafter₁'.trans hk'
  have hnk₁ : n + 1 ≤ k' := by
    by_contra hcon
    have hmono := Solution.eventTime_mono w σ lookahead (Nat.lt_succ_iff.mp (not_le.mp hcon))
    rw [hsn] at hmono
    linarith
  obtain ⟨i₁, -, -, hh₁⟩ := Solution.handled_before w σ lookahead hin₁ hnk₁ hk₁
  simp only at hh₁
  -- The sender answers a query of `h` that is this one.
  obtain ⟨n₀, -, s₀, hs₀, sent₀, F₀, hle, hh₀, hans₀⟩ := query_answered p w lookahead hsender hh₁
  obtain ⟨mq, hmq, -, harr, hor, hcont, -⟩ := Solution.handled_received w σ lookahead hh₀
  have hO := origin_inFlight p w lookahead hsender n₀ mq hmq
  unfold Origin at hO
  simp only [hcont] at hO
  obtain ⟨s₁, q₁, -, hsent, hdel⟩ := hO
  rw [hor, hA, Option.some.injEq, harr] at hdel
  rw [hor] at hsent
  have hss₁ : s ≤ s₁ := by
    rw [hsent] at hle
    exact (w.clock h).strictMono.le_iff_le.mp hle
  have hs₁ : s₁ = s := by
    rcases eq_or_lt_of_le hss₁ with heq | hlt
    · exact heq.symm
    · have := hstrict s₁ hlt
      rw [hdel] at this
      linarith
  subst hs₁
  -- The answer is in transit after step `n₀`.
  have hS₂ : (σ w.sender ((σ.states w lookahead n₀).views w.sender
        ++ [⟨(w.clock w.sender).read s₀, .received h (.ask sent₀) F₀⟩])).sends
      = List.replicate p.copies
          (h, (Payload.answer sent₀ ((w.clock w.sender).read s₀), (∅ : Finset ℕ))) := by
    rw [hσ, solution_append]
    simp only [act, hans₀, hsender, and_self, ite_true]
  have hlen₂ : 0 < (List.replicate p.copies
      (h, (Payload.answer sent₀ ((w.clock w.sender).read s₀), (∅ : Finset ℕ)))).length := by
    simpa using hcopies
  have hin₂ := σ.sent_inFlight w lookahead hh₀ hS₂ hlen₂ (arr := A w.sender h s₀)
    (by rw [List.getElem_replicate]; exact hA _ _ _ _)
  simp only [List.getElem_replicate, Finset.filter_empty] at hin₂
  -- It is handled by the querying host.
  have hk₂ : A w.sender h s₀ < σ.eventTime w lookahead k' := by
    rw [← hdel]
    exact hk'
  have hs₀n : σ.eventTime w lookahead n₀ = s₀ := Solution.handled_time w σ lookahead hh₀
  have hafter₂ : s₀ < A w.sender h s₀ := w.network.after _ _ _ _ _ (hA w.sender h s₀ 0)
  have hnk₂ : n₀ + 1 ≤ k' := by
    by_contra hcon
    have hmono := Solution.eventTime_mono w σ lookahead (Nat.lt_succ_iff.mp (not_le.mp hcon))
    rw [hs₀n] at hmono
    linarith
  obtain ⟨i₂, -, hi₂, hh₂⟩ := Solution.handled_before w σ lookahead hin₂ hnk₂ hk₂
  simp only at hh₂
  have hmem := Solution.mem_views_of_handled w σ lookahead hh₂ hi₂
  have hex := Controller.plainExchangesOf_mem hmem (i := w.sender) (sent := sent₀)
    (received := (w.clock w.sender).read s₀) (F := ∅) rfl
  rw [hsent, ← hdel] at hex
  exact hex

/-- **A clock query that no later query overtakes yields an exchange.**
Consider a world in which no message is lost and a message from `i` to `j`
sent at `s` arrives at `A i j s`, and whose run advances past every true
time. A host `h` sends a clock query at true time `s`, and every later query
of `h` reaches the sender later than this one. Then, from some step on, the
view of `h` holds the exchange of this query: the reading of `h` at `s`, the
sender's reading when the query arrived, and the reading of `h` when the
answer arrived. -/
theorem exchange_of_query (w : World H R) (lookahead : ℕ+) {A : H → H → Time → Time}
    (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hsender : p.sender = w.sender) (hcopies : 0 < p.copies)
    (hprog : ∀ T, ∃ n, T < (solution p : Solution H R Payload).eventTime w lookahead n)
    {n : ℕ} {h : H} {s : Time} {r : Fin R} {outs : List ℕ} {st : ℝ}
    (hn : (solution p : Solution H R Payload).handled w lookahead n
      = some (h, s, .asked r outs st))
    (hask : asks p h (memoryOf p h
      (((solution p : Solution H R Payload).states w lookahead n).views h))
      ((w.clock h).read s) = true)
    (hstrict : ∀ s', s < s' → A h w.sender s < A h w.sender s') :
    ∃ k, ∀ k', k ≤ k' →
      (⟨(w.clock h).read s, (w.clock w.sender).read (A h w.sender s),
          (w.clock h).read (A w.sender h (A h w.sender s))⟩ : Controller.Exchange)
        ∈ Controller.plainExchangesOf (((solution p : Solution H R Payload).states w lookahead k').views h) := by
  obtain ⟨k₂, hk₂⟩ := hprog (A w.sender h (A h w.sender s))
  exact ⟨k₂, fun k' hk' => exchange_of_query_before p w lookahead hA hsender hcopies hn hask
    hstrict (lt_of_lt_of_le hk₂ (Solution.eventTime_mono w _ lookahead hk'))⟩

end Unisono.Solutions.FixedDelay
