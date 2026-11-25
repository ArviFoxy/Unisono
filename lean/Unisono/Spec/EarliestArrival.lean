/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.NoLoss
public import Unisono.Spec.Limits

/-!
# No frame overtakes a message sent at its handover

The sender's host gets a frame of the source when the capture device hands
over the block that holds it. This file proves that, for every solution
whose hosts exchange messages only with the sender, no other host holds the
frame before a message that the sender sends at that handover can arrive,
and that no speaker plays a position before the frames that the position
needs can have arrived.

The world is any world without loss in which the arrival time `A i j s` of a
message sent from host `i` to host `j` at true time `s` does not decrease
with `s` and is at least `s`. Nothing is assumed of the solution besides the
hosts that it exchanges messages with: it may send any payloads at any
times, and receiving hosts may send frames back to the sender.

* `Solution.frame_times`: the invariant of the run. For a frame of capture
  block `b`, every event that brings the frame to the sender's host occurs
  at or after the handover of `b`, and every event that brings it to another
  host `h` occurs at or after `A sender h (handed b)`. The same holds for the
  arrival of every message in transit that carries the frame.
* `Solution.arrival_le_of_held`: so a host other than the sender's that
  holds the frame handled, at an earlier step, the arrival of a message that
  carries it, at a true time of at least `A sender h (handed b)`.
* `Solution.arrival_lt_asked_of_plays`: if output sample `k` of a speaker
  whose host is not the sender's plays the position `x`, then for every
  frame that the resampler needs for `x`, in capture block `c`, the time
  `A sender h (handed c)` is strictly before the request of the playback
  block that holds `k`.

The controller of `Unisono.Solutions.Controller` sends each block when it is
handed over, so its speakers can play a position as early as any solution
through the sender can.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- **The invariant: a frame is nowhere before it can arrive.** Consider a
world without loss whose messages do not overtake one another and do not
arrive before they are sent, a solution whose hosts exchange messages only
with the sender, and a frame `n` of capture block `b`. Up to every step of
the run: an event that brings the frame to the sender's host occurs at or
after the handover of `b`; an event that brings it to another host `h`
occurs at or after `A sender h (handed b)`; and every message in transit
that carries the frame arrives at or after the corresponding time of its
destination. -/
theorem Solution.frame_times (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {A : H → H → Time → Time} (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hmono : ∀ i j, Monotone (A i j)) (hle : ∀ i j s, s ≤ A i j s)
    (hstar : σ.IsStar w.sender) {n b : ℕ} (hb : n ∈ w.source.block b) (k : ℕ) :
    (∀ i < k, ∀ h t obs, σ.handled w lookahead i = some (h, t, obs) → n ∈ obs.frames →
        (if h = w.sender then w.source.handed b else A w.sender h (w.source.handed b)) ≤ t)
    ∧ ∀ m ∈ (σ.states w lookahead k).inFlight, n ∈ m.frames →
        (if m.destination = w.sender then w.source.handed b
          else A w.sender m.destination (w.source.handed b)) ≤ m.arrival := by
  induction k with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    simp [Solution.states, State.start]
  | succ k ih =>
    obtain ⟨hP, hJ⟩ := ih
    -- The event of step `k`.
    have hPk : ∀ h t obs, σ.handled w lookahead k = some (h, t, obs) → n ∈ obs.frames →
        (if h = w.sender then w.source.handed b else A w.sender h (w.source.handed b)) ≤ t := by
      intro h t obs hk hn
      cases obs with
      | handed frames stamp =>
        obtain ⟨b', hh, ht, hfr, -⟩ := σ.handled_handed w lookahead hk
        have hnb : n ∈ w.source.block b' := by
          rw [hfr] at hn
          simpa [Observation.frames] using hn
        have hbb : b = b' := w.source.block_unique hb hnb
        rw [ite_eq_left hh, hbb, ht]
      | asked r outputs stamp => simp [Observation.frames] at hn
      | received j c F =>
        obtain ⟨m, hm, hdest, harr, -, -, hF⟩ := σ.handled_received w lookahead hk
        have h1 := hJ m hm (by rw [hF]; exact hn)
        rw [hdest, harr] at h1
        exact h1
      | timer => simp [Observation.frames] at hn
    have hP' : ∀ i < k + 1, ∀ h t obs, σ.handled w lookahead i = some (h, t, obs) →
        n ∈ obs.frames →
        (if h = w.sender then w.source.handed b else A w.sender h (w.source.handed b)) ≤ t := by
      intro i hi h t obs hih hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hP i hlt h t obs hih hn
      · exact hPk h t obs hih hn
    refine ⟨hP', fun m hm hn => ?_⟩
    rcases σ.mem_inFlight_succ w lookahead k hm with hold
      | ⟨h, t, obs, hk, s, hs, -, hdest, -, hfr, q, hq⟩
    · exact hJ m hold hn
    · -- The host that sends the message holds the frame at the time of sending.
      rw [hA] at hq
      have harr : m.arrival = A h s.1 t := (Option.some.inj hq).symm
      have hheld : n ∈ (σ.states w lookahead k).held h ∪ obs.frames := by
        rw [hfr] at hn
        exact (Finset.mem_filter.mp hn).2
      have hEh : (if h = w.sender then w.source.handed b
          else A w.sender h (w.source.handed b)) ≤ t := by
        rcases Finset.mem_union.mp hheld with h1 | h1
        · obtain ⟨e, he, hne⟩ := (σ.mem_held_iff w lookahead k h n).mp h1
          obtain ⟨i, hi, t', obs', hi', rfl⟩ := σ.handled_of_mem_views w lookahead he
          have h2 := hP i hi h t' obs' hi' hne
          have h3 : t' ≤ t := by
            rw [← σ.handled_time w lookahead hi', ← σ.handled_time w lookahead hk]
            exact σ.eventTime_mono w lookahead hi.le
          exact h2.trans h3
        · exact hPk h t obs hk h1
      have hadj := hstar h _ s.1 s.2.1 s.2.2 hs
      rw [hdest, harr]
      rcases hadj with hS | hS
      · rw [ite_eq_left hS] at hEh
        by_cases hd : s.1 = w.sender
        · rw [ite_eq_left hd]
          exact hEh.trans (hle _ _ _)
        · rw [ite_eq_right hd, hS]
          exact hmono _ _ hEh
      · rw [ite_eq_left hS]
        by_cases hh : h = w.sender
        · rw [ite_eq_left hh] at hEh
          exact hEh.trans (hle _ _ _)
        · rw [ite_eq_right hh] at hEh
          exact ((hle _ _ _).trans hEh).trans (hle _ _ _)

/-- **A host holds a frame only after a message sent at its handover can
have arrived.** In a world without loss whose messages do not overtake one
another and do not arrive before they are sent, consider a solution whose
hosts exchange messages only with the sender. If a host `h` other than the
sender's holds frame `n` of capture block `b` at step `k`, then at an
earlier step it handled the arrival of a message that carries the frame, at
a true time of at least `A sender h (handed b)`. -/
theorem Solution.arrival_le_of_held (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {A : H → H → Time → Time} (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hmono : ∀ i j, Monotone (A i j)) (hle : ∀ i j s, s ≤ A i j s)
    (hstar : σ.IsStar w.sender) {k : ℕ} {h : H} (hh : h ≠ w.sender) {n b : ℕ}
    (hb : n ∈ w.source.block b) (hn : n ∈ (σ.states w lookahead k).held h) :
    ∃ i < k, ∃ t j c F, σ.handled w lookahead i = some (h, t, .received j c F) ∧ n ∈ F
      ∧ A w.sender h (w.source.handed b) ≤ t := by
  obtain ⟨e, he, hne⟩ := (σ.mem_held_iff w lookahead k h n).mp hn
  obtain ⟨i, hi, t, obs, hi', rfl⟩ := σ.handled_of_mem_views w lookahead he
  have h2 := (σ.frame_times w lookahead hA hmono hle hstar hb k).1 i hi h t obs hi' hne
  rw [ite_eq_right hh] at h2
  cases obs with
  | handed frames stamp =>
    obtain ⟨-, hsender, -⟩ := σ.handled_handed w lookahead hi'
    exact absurd hsender hh
  | asked r outputs stamp => simp [Observation.frames] at hne
  | received j c F => exact ⟨i, hi, t, j, c, F, hi', hne, h2⟩
  | timer => simp [Observation.frames] at hne

/-- **No solution through the sender plays a position before its frames can
have arrived.** In a world without loss whose messages do not overtake one
another and do not arrive before they are sent, consider a solution whose
hosts exchange messages only with the sender, and a speaker `r` whose host
is not the sender's. If output sample `k` of the speaker plays the position
`x`, then `x` is not negative, and `k` belongs to a playback block `b` such
that, for every frame `n` less than `lookahead` frames away from `x`, in
capture block `c`, a message that the sender sends at the handover of `c`
arrives strictly before the request of `b`. -/
theorem Solution.arrival_lt_asked_of_plays (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) {A : H → H → Time → Time}
    (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hmono : ∀ i j, Monotone (A i j)) (hle : ∀ i j s, s ≤ A i j s)
    (hstar : σ.IsStar w.sender) {r : Fin R} (hr : w.host r ≠ w.sender) {k : ℕ} {x : ℝ}
    (hplay : σ.plays w lookahead r k = some x) :
    0 ≤ x ∧ ∃ b, k ∈ (w.speaker r).block b ∧ ∀ n c : ℕ, |(n : ℝ) - x| < (lookahead : ℕ) →
      n ∈ w.source.block c →
      A w.sender (w.host r) (w.source.handed c) < (w.speaker r).asked b := by
  obtain ⟨b, i, hkb, hnb, hearly, hact⟩ := exists_asked_of_plays_some σ w lookahead hplay
  have hp := σ.plays_of_asked_step_of_lt w lookahead hnb hearly hkb
    (σ.asked_lt_out_of_plays w lookahead hkb hplay)
  rw [hplay, hact] at hp
  simp only [playable] at hp
  split_ifs at hp with hc
  refine ⟨hc.1, b, hkb, fun n c hn hcn => ?_⟩
  obtain ⟨j, hj, t, o, m, F, hj', -, hjt⟩ :=
    σ.arrival_le_of_held w lookahead hA hmono hle hstar hr hcn (hc.2 n hn)
  have hlt := σ.received_lt_asked w lookahead hj.le hj' r
  rw [hnb] at hlt
  exact lt_of_le_of_lt hjt hlt

end Unisono.Spec
