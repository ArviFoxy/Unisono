/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Memory
public import Unisono.Spec.Run
public import Unisono.Spec.Topologies

/-!
# Where the baseline's messages come from

In any world, every message of the baseline that is in transit is one of two
kinds (`inFlight_provenance`):

* a message from the sender to another host: a block of the stream or an
  answer to a clock query;
* a clock query to the sender from another host, sent when a playback device
  of that host requested a block.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- An event in which a device requests a block happens at the host of its
speaker, when the device requests one of its blocks. -/
theorem Solution.handled_asked_time (w : World H R) (σ : Solution H R Msg) (lookahead : ℕ+)
    {n : ℕ} {h : H} {t : Time} {r : Fin R} {outs : List ℕ} {st : ℝ}
    (hn : σ.handled w lookahead n = some (h, t, .asked r outs st)) :
    h = w.host r ∧ ∃ b, t = (w.speaker r).asked b := by
  unfold Solution.handled at hn
  split at hn
  · simp at hn
  · rename_i r' b _
    simp only [Option.some.injEq, Prod.mk.injEq, Observation.asked.injEq] at hn
    obtain ⟨h1, h2, rfl, -, -⟩ := hn
    exact ⟨h1.symm, b, h2.symm⟩
  · obtain ⟨m, -, heq⟩ := Option.map_eq_some_iff.mp hn
    simp at heq
  · obtain ⟨u, -, heq⟩ := Option.map_eq_some_iff.mp hn
    simp at heq
  · simp at hn

end Unisono.Spec

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- What the baseline sends at an event: the sender sends blocks to other
hosts and answers to the hosts whose queries arrive, and another host sends
queries to the sender when one of its devices requests a block. -/
theorem act_sends (h : H) (mem : Memory H R) (e : Event H R Payload)
    {s : H × Payload × Finset ℕ} (hs : s ∈ (act p h mem e).sends) :
    (h = p.sender ∧ s.1 ≠ p.sender)
      ∨ (h = p.sender ∧ ∃ sent F ks, e.observation = .received s.1 (.ask sent) F ks)
      ∨ (h ≠ p.sender ∧ s.1 = p.sender
          ∧ ∃ r outs stamp, e.observation = .asked r outs stamp) := by
  unfold act at hs
  cases hobs : e.observation with
  | handed frames stamp =>
    simp only [hobs] at hs
    split_ifs at hs with hsend
    · cases hhead : frames.head? with
      | none => simp [hhead] at hs
      | some fs =>
        obtain ⟨f₀, t₀⟩ := fs
        simp only [hhead, List.mem_flatMap, List.mem_filter, List.mem_replicate,
          decide_eq_true_eq] at hs
        obtain ⟨j, ⟨-, hj⟩, -, rfl⟩ := hs
        exact Or.inl ⟨hsend, hj⟩
    · simp at hs
  | received i payload F _ =>
    cases payload with
    | block _ _ => simp [hobs] at hs
    | ask sent =>
      simp only [hobs] at hs
      split_ifs at hs with hc
      · rw [List.mem_replicate] at hs
        obtain ⟨-, rfl⟩ := hs
        exact Or.inr (Or.inl ⟨hc.1, sent, F, _, rfl⟩)
      · simp at hs
    | answer _ _ => simp [hobs] at hs
  | asked r outputs stamp =>
    simp only [hobs] at hs
    split_ifs at hs with ha
    · rw [List.mem_replicate] at hs
      obtain ⟨-, rfl⟩ := hs
      have hne : h ≠ p.sender := by
        unfold asks at ha
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
        exact ha.1
      exact Or.inr (Or.inr ⟨hne, rfl, r, outputs, stamp, rfl⟩)
    · simp at hs
  | timer => simp [hobs] at hs

/-- **Where the baseline's messages in transit come from.** A message to a
host other than the sender comes from the sender. A message to the sender
comes from another host, which sent it when a playback device of that host
requested a block. -/
theorem inFlight_provenance (w : World H R) (lookahead : ℕ+) (n : ℕ)
    {x : InFlight H Payload}
    (hx : x ∈ ((solution p : Solution H R Payload).states w lookahead n).inFlight) :
    (x.destination ≠ p.sender → x.origin = p.sender)
      ∧ (x.destination = p.sender → x.origin ≠ p.sender ∧ ∃ r b q, w.host r = x.origin ∧
          w.network.deliver x.origin p.sender ((w.speaker r).asked b) q = some x.arrival) := by
  induction n generalizing x with
  | zero => simp [Solution.states, State.start] at hx
  | succ n ih =>
    rcases Solution.mem_inFlight_succ w (solution p) lookahead n hx with hold |
      ⟨h, t, obs, hhandled, s, hs, ho, hd, -, -, q, hq, -⟩
    · exact ih hold
    · rw [solution_append] at hs
      rcases act_sends p h _ _ hs with ⟨hh, hne⟩ | ⟨hh, sent, F, ks, hobs⟩ |
        ⟨hh, hsd, r, outs, stamp, hobs⟩
      · exact ⟨fun _ => ho.trans hh, fun hdest => absurd (hd.symm.trans hdest) hne⟩
      · have hobs' : obs = .received s.1 (.ask sent) F ks := hobs
        rw [hobs'] at hhandled
        obtain ⟨x', hx', hdst', -, horig', -, -⟩ :=
          Solution.handled_received w (solution p) lookahead hhandled
        have hb := ((ih hx').2 (hdst'.trans hh)).1
        refine ⟨fun _ => ho.trans hh, fun hdest => absurd ?_ hb⟩
        rw [horig', ← hd]
        exact hdest
      · have hobs' : obs = .asked r outs stamp := hobs
        rw [hobs'] at hhandled
        obtain ⟨hhr, b, htb⟩ := Solution.handled_asked_time w (solution p) lookahead hhandled
        refine ⟨fun hdest => absurd (hd.trans hsd) hdest,
          fun _ => ⟨by rw [ho]; exact hh, r, b, q, ?_, ?_⟩⟩
        · rw [ho, hhr]
        · rw [ho, ← hsd, ← htb]
          exact hq

end Unisono.Solutions.FixedDelay
