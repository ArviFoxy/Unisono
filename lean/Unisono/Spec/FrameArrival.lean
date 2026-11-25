/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.EarliestArrival
public import Unisono.Spec.Stall

/-!
# No frame is at a host before the network can have brought it

`Unisono.Spec.EarliestArrival` proves, in a world without loss whose
messages do not overtake one another, that no host holds a frame before a
message sent at the frame's handover arrives. This file proves the same for
any network: messages may be lost, and a message sent later may arrive
earlier.

What is assumed of the network is a bound `E`: every message that the sender
sends to host `h` at or after a true time `T`, and that is not lost, is
handled by `h` at `E h T` or later, and `E h T` is not before `T`. What is
assumed of the solution is that it carries frames of the source only on
links from the sender or to the sender (`Solution.CarriesFramesOn`); its
hosts may exchange any other messages with any hosts.

* `Solution.frame_times_of_earliest`: the invariant of the run. For a frame
  of capture block `b`, every event that brings the frame to the sender's
  host occurs at or after the handover of `b`, and every event that brings
  it to another host `h` occurs at or after `E h (handed b)`. The same holds
  for the arrival of every message in transit that carries the frame.
* `Solution.earliest_le_of_held`: so a host other than the sender's that
  holds the frame handled, at an earlier step, the arrival of a message that
  carries it, at a true time of at least `E h (handed b)`.
* `Solution.earliest_lt_asked_of_plays`: if output sample `k` of a speaker
  whose host is not the sender's plays the position `x`, then for every
  frame that the resampler needs for `x`, in capture block `c`, the time
  `E h (handed c)` is strictly before the request of the playback block that
  holds `k`.
* `Solution.le_of_plays_before_earliest`: when `E` does not decrease with the
  true time and the request of playback block `β` is handled no later than
  `E h (handed c)`, every position played up to block `β` is at most the
  first frame of capture block `c` minus the lookahead.
* `Solution.stall_le_of_earliest`: so a stretch of output samples up to
  block `β` costs missed samples and discontinuities, except for the room
  from the position played last before the stretch to that bound
  (`Unisono.Spec.stall_le_of_le`).
* `Solution.stall_le_of_quiet`: the same for one quiet stretch: no message
  that the sender sends to the speaker's host at or after a true time `t₀`
  is handled before a true time `e`, capture block `c` is handed over at
  `t₀` or later, and the request of block `β` is handled at `e` or earlier.
  An outage, a pause of the link and a large jitter each give such a
  stretch.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- **A solution carries frames of the source only on the links of the graph
`adj`**: every message in which host `h` sends frames to host `dst`
satisfies `adj h dst`. Messages without frames may go anywhere. -/
def Solution.CarriesFramesOn (σ : Solution H R Msg) (adj : H → H → Prop) : Prop :=
  ∀ h view dst msg frames, (dst, msg, frames) ∈ (σ h view).sends → frames.Nonempty → adj h dst

/-- **The invariant: a frame is nowhere before the network can have brought
it.** Consider a world in which every message that the sender sends to a
host `h` at or after a true time `T`, and that is not lost, is handled at
`E h T` or later, with `T ≤ E h T`; a solution that carries frames only on
links from the sender or to the sender; and a frame `n` of capture block
`b`. Up to every step of the run: an event that brings the frame to the
sender's host occurs at or after the handover of `b`; an event that brings
it to another host `h` occurs at or after `E h (handed b)`; and every
message in transit that carries the frame arrives at or after the
corresponding time of its destination. -/
theorem Solution.frame_times_of_earliest (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) {E : H → Time → Time}
    (hE : ∀ h s q a, w.network.deliver w.sender h s q = some a → ∀ T ≤ s, E h T ≤ a)
    (hle : ∀ h T, T ≤ E h T)
    (hframes : σ.CarriesFramesOn fun h dst => h = w.sender ∨ dst = w.sender) {n b : ℕ}
    (hb : n ∈ w.source.block b) (k : ℕ) :
    (∀ i < k, ∀ h t obs, σ.handled w lookahead i = some (h, t, obs) → n ∈ obs.frames →
        (if h = w.sender then w.source.handed b else E h (w.source.handed b)) ≤ t)
    ∧ ∀ m ∈ (σ.states w lookahead k).inFlight, n ∈ m.frames →
        (if m.destination = w.sender then w.source.handed b
          else E m.destination (w.source.handed b)) ≤ m.arrival := by
  induction k with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    simp [Solution.states, State.start]
  | succ k ih =>
    obtain ⟨hP, hJ⟩ := ih
    -- The event of step `k`.
    have hPk : ∀ h t obs, σ.handled w lookahead k = some (h, t, obs) → n ∈ obs.frames →
        (if h = w.sender then w.source.handed b else E h (w.source.handed b)) ≤ t := by
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
      | received j c F _ =>
        obtain ⟨m, hm, hdest, harr, -, -, hF, -⟩ := σ.handled_received w lookahead hk
        have h1 := hJ m hm (by rw [hF]; exact hn)
        rw [hdest, harr] at h1
        exact h1
      | timer => simp [Observation.frames] at hn
    have hP' : ∀ i < k + 1, ∀ h t obs, σ.handled w lookahead i = some (h, t, obs) →
        n ∈ obs.frames →
        (if h = w.sender then w.source.handed b else E h (w.source.handed b)) ≤ t := by
      intro i hi h t obs hih hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hP i hlt h t obs hih hn
      · exact hPk h t obs hih hn
    refine ⟨hP', fun m hm hn => ?_⟩
    rcases σ.mem_inFlight_succ w lookahead k hm with hold
      | ⟨h, t, obs, hk, s, hs, -, hdest, -, hfr, q, hq, -⟩
    · exact hJ m hold hn
    · -- The host that sends the message holds the frame at the time of sending.
      have hmem : n ∈ s.2.2 ∧ n ∈ (σ.states w lookahead k).held h ∪ obs.frames := by
        rw [hfr] at hn
        exact Finset.mem_filter.mp hn
      have hEh : (if h = w.sender then w.source.handed b
          else E h (w.source.handed b)) ≤ t := by
        rcases Finset.mem_union.mp hmem.2 with h1 | h1
        · obtain ⟨e, he, hne⟩ := (σ.mem_held_iff w lookahead k h n).mp h1
          obtain ⟨i, hi, t', obs', hi', rfl⟩ := σ.handled_of_mem_views w lookahead he
          have h2 := hP i hi h t' obs' hi' hne
          have h3 : t' ≤ t := by
            rw [← σ.handled_time w lookahead hi', ← σ.handled_time w lookahead hk]
            exact σ.eventTime_mono w lookahead hi.le
          exact h2.trans h3
        · exact hPk h t obs hk h1
      have hafter : t < m.arrival := w.network.after _ _ _ _ _ hq
      have hadj := hframes h _ s.1 s.2.1 s.2.2 hs ⟨n, hmem.1⟩
      rw [hdest]
      rcases hadj with hS | hS
      · rw [ite_eq_left hS] at hEh
        by_cases hd : s.1 = w.sender
        · rw [ite_eq_left hd]
          exact hEh.trans hafter.le
        · rw [ite_eq_right hd]
          rw [hS] at hq
          exact hE s.1 t q m.arrival hq _ hEh
      · rw [ite_eq_left hS]
        by_cases hh : h = w.sender
        · rw [ite_eq_left hh] at hEh
          exact hEh.trans hafter.le
        · rw [ite_eq_right hh] at hEh
          exact ((hle _ _).trans hEh).trans hafter.le

/-- **A host holds a frame only after the network can have brought it.**
Under the conditions of `Solution.frame_times_of_earliest`, if a host `h`
other than the sender's holds frame `n` of capture block `b` at step `k`,
then at an earlier step it handled the arrival of a message that carries the
frame, at a true time of at least `E h (handed b)`. -/
theorem Solution.earliest_le_of_held (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {E : H → Time → Time}
    (hE : ∀ h s q a, w.network.deliver w.sender h s q = some a → ∀ T ≤ s, E h T ≤ a)
    (hle : ∀ h T, T ≤ E h T)
    (hframes : σ.CarriesFramesOn fun h dst => h = w.sender ∨ dst = w.sender) {k : ℕ} {h : H}
    (hh : h ≠ w.sender) {n b : ℕ} (hb : n ∈ w.source.block b)
    (hn : n ∈ (σ.states w lookahead k).held h) :
    ∃ i < k, ∃ t j c F ks, σ.handled w lookahead i = some (h, t, .received j c F ks) ∧ n ∈ F
      ∧ E h (w.source.handed b) ≤ t := by
  obtain ⟨e, he, hne⟩ := (σ.mem_held_iff w lookahead k h n).mp hn
  obtain ⟨i, hi, t, obs, hi', rfl⟩ := σ.handled_of_mem_views w lookahead he
  have h2 := (σ.frame_times_of_earliest w lookahead hE hle hframes hb k).1 i hi h t obs hi' hne
  rw [ite_eq_right hh] at h2
  cases obs with
  | handed frames stamp =>
    obtain ⟨-, hsender, -⟩ := σ.handled_handed w lookahead hi'
    exact absurd hsender hh
  | asked r outputs stamp => simp [Observation.frames] at hne
  | received j c F ks => exact ⟨i, hi, t, j, c, F, ks, hi', hne, h2⟩
  | timer => simp [Observation.frames] at hne

/-- **No solution plays a position before the network can have brought its
frames.** Under the conditions of `Solution.frame_times_of_earliest`,
consider a speaker `r` whose host is not the sender's. If output sample `k`
of the speaker plays the position `x`, then `x` is not negative, and `k`
belongs to a playback block `b` such that, for every frame `n` less than
`lookahead` frames away from `x`, in capture block `c`, the time
`E (host r) (handed c)` is strictly before the request of `b`. -/
theorem Solution.earliest_lt_asked_of_plays (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) {E : H → Time → Time}
    (hE : ∀ h s q a, w.network.deliver w.sender h s q = some a → ∀ T ≤ s, E h T ≤ a)
    (hle : ∀ h T, T ≤ E h T)
    (hframes : σ.CarriesFramesOn fun h dst => h = w.sender ∨ dst = w.sender) {r : Fin R}
    (hr : w.host r ≠ w.sender) {k : ℕ} {x : ℝ} (hplay : σ.plays w lookahead r k = some x) :
    0 ≤ x ∧ ∃ b, k ∈ (w.speaker r).block b ∧ ∀ n c : ℕ, |(n : ℝ) - x| < (lookahead : ℕ) →
      n ∈ w.source.block c → E (w.host r) (w.source.handed c) < (w.speaker r).asked b := by
  obtain ⟨b, i, hkb, hnb, hearly, hact⟩ := exists_asked_of_plays_some σ w lookahead hplay
  have hp := σ.plays_of_asked_step_of_lt w lookahead hnb hearly hkb
    (σ.asked_lt_out_of_plays w lookahead hkb hplay)
  rw [hplay, hact] at hp
  simp only [playable] at hp
  split_ifs at hp with hc
  refine ⟨hc.1, b, hkb, fun n c hn hcn => ?_⟩
  obtain ⟨j, hj, t, o, m, F, ks, hj', -, hjt⟩ :=
    σ.earliest_le_of_held w lookahead hE hle hframes hr hcn (hc.2 n hn)
  have hlt := σ.received_lt_asked w lookahead hj.le hj' r
  rw [hnb] at hlt
  exact lt_of_le_of_lt hjt hlt


/-- Every frame belongs to a block of the capture device. -/
theorem CaptureDevice.exists_mem_block (d : CaptureDevice) (n : ℕ) : ∃ b, n ∈ d.block b := by
  classical
  have hm := d.first_strictMono
  have hex : ∃ b, n < d.first (b + 1) :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (hm.id_le (n + 1))⟩
  refine ⟨Nat.find hex, ?_⟩
  have hspec := Nat.find_spec hex
  unfold CaptureDevice.block
  rw [List.mem_range'_1]
  constructor
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, d.first_zero]
      exact Nat.zero_le n
    · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel hpos] at hmin
      exact not_lt.mp hmin
  · have := (hm (Nat.lt_succ_self (Nat.find hex))).le
    omega

/-- **While no frame of a block can have arrived, only earlier positions can
be played.** Under the conditions of `Solution.frame_times_of_earliest`, let
the bound `E` not decrease with the true time, and consider a speaker `r`
whose host is not the sender's. If the request of playback block `β` is
handled no later than `E (host r) (handed c)`, so that no frame of capture
block `c` or of a later block can be at the host by that request, then every
position played at an output sample of a playback block up to `β` is at most
the first frame of block `c` minus the lookahead. -/
theorem Solution.le_of_plays_before_earliest (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) {E : H → Time → Time}
    (hE : ∀ h s q a, w.network.deliver w.sender h s q = some a → ∀ T ≤ s, E h T ≤ a)
    (hle : ∀ h T, T ≤ E h T) (hmono : ∀ h, Monotone (E h))
    (hframes : σ.CarriesFramesOn fun h dst => h = w.sender ∨ dst = w.sender) {r : Fin R}
    (hr : w.host r ≠ w.sender) {c β k : ℕ} {x : ℝ}
    (hc : (w.speaker r).asked β ≤ E (w.host r) (w.source.handed c))
    (hk : k < (w.speaker r).first (β + 1)) (hplay : σ.plays w lookahead r k = some x) :
    x ≤ (w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ) := by
  obtain ⟨hx0, b, hkb, hlt⟩ :=
    σ.earliest_lt_asked_of_plays w lookahead hE hle hframes hr hplay
  have hbβ : b ≤ β := by
    by_contra hcon
    have h1 : (w.speaker r).first (β + 1) ≤ (w.speaker r).first b :=
      (w.speaker r).first_strictMono.monotone (by omega)
    unfold PlaybackDevice.block at hkb
    rw [List.mem_range'_1] at hkb
    omega
  have hasked : (w.speaker r).asked b ≤ (w.speaker r).asked β := (w.speaker r).asked_mono hbβ
  -- The last frame that the position needs.
  have hL : (1 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := by exact_mod_cast lookahead.pos
  have hceil_pos : 0 < ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hcast : ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 : ℕ) : ℝ)
      = (⌈x + ((lookahead : ℕ) : ℝ)⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil_pos]
    simp
  have hceil1 := Nat.le_ceil (x + ((lookahead : ℕ) : ℝ))
  have hceil2 := Nat.ceil_lt_add_one (by linarith : 0 ≤ x + ((lookahead : ℕ) : ℝ))
  have habs : |((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 : ℕ) : ℝ) - x| < ((lookahead : ℕ) : ℝ) := by
    rw [hcast, abs_lt]
    constructor <;> linarith
  obtain ⟨c', hc'⟩ := w.source.exists_mem_block (⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1)
  have h1 := hlt _ c' habs hc'
  have hcc : c' < c := by
    by_contra hge
    have h2 := hmono (w.host r) (w.source.handed_mono (not_lt.mp hge))
    linarith
  have hnc : ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 < w.source.first c := by
    unfold CaptureDevice.block at hc'
    rw [List.mem_range'_1] at hc'
    have h3 : w.source.first (c' + 1) ≤ w.source.first c :=
      w.source.first_strictMono.monotone hcc
    have h4 := (w.source.first_strictMono (Nat.lt_succ_self c')).le
    omega
  have h5 : ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ ≤ w.source.first c := by omega
  have h6 : ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ (w.source.first c : ℝ) := by
    exact_mod_cast h5
  linarith

/-- **What every solution pays while no frame of a block can have arrived.**
Under the conditions of `Solution.le_of_plays_before_earliest`, let the
position of speaker `r` advance by at least `s` in every step of continuous
playback, with `0 ≤ s ≤ 1`. Then for output samples `k₀ ≤ K` with `K` in a
playback block up to `β`: `s` for each output sample from `k₀` to `K` is at
most the room from the position played last before `k₀` to the first frame
of block `c` minus the lookahead, plus the missed samples counted from `k₀`
to `K`, plus `s` times the discontinuities counted from `k₀` to `K - 1` and
one more. -/
theorem Solution.stall_le_of_earliest (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {E : H → Time → Time}
    (hE : ∀ h s q a, w.network.deliver w.sender h s q = some a → ∀ T ≤ s, E h T ≤ a)
    (hle : ∀ h T, T ≤ E h T) (hmono : ∀ h, Monotone (E h))
    (hframes : σ.CarriesFramesOn fun h dst => h = w.sender ∨ dst = w.sender) {r : Fin R}
    (hr : w.host r ≠ w.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {c β k₀ K : ℕ} (hK : k₀ ≤ K) (hKβ : K < (w.speaker r).first (β + 1))
    (hc : (w.speaker r).asked β ≤ E (w.host r) (w.source.handed c)) :
    s * ((K : ℝ) + 1 - k₀)
      ≤ max ((w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
        + ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt (σ.plays w lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt (σ.plays w lookahead r) k : ℝ)
          + 1) := by
  have hnn : ∀ k x, σ.plays w lookahead r k = some x → 0 ≤ x := fun k x hx =>
    (σ.earliest_lt_asked_of_plays w lookahead hE hle hframes hr hx).1
  have hle' : ∀ k, k ≤ K → ∀ x, σ.plays w lookahead r k = some x →
      x ≤ (w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ) := fun k hk x hx =>
    σ.le_of_plays_before_earliest w lookahead hE hle hmono hframes hr hc
      (lt_of_le_of_lt hk hKβ) hx
  have hD0 : (0 : ℝ) ≤ ∑ k ∈ Finset.Ico k₀ K,
      (discontinuityAt (σ.plays w lookahead r) k : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (K : ℝ) + 1 - k₀ := by
    have : (k₀ : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  by_cases hP : 0 ≤ (w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ)
  · -- The position played last before `k₀` is at most the bound.
    have hx₀ : (lastPlayed (σ.plays w lookahead r) k₀).getD 0
        ≤ (w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ) := by
      cases hl : lastPlayed (σ.plays w lookahead r) k₀ with
      | none => simpa using hP
      | some x =>
        obtain ⟨ht, hx⟩ := lastPlayed_some hl
        simp only [Option.getD_some]
        exact hle' _ (by omega) x hx
    have h1 := stall_le_of_le hs0 hs1 hnn hslow hK hx₀ fun k _ hkK x hx => hle' k hkK x hx
    have h2 := le_max_left ((w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ)
      - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
    linarith
  · -- Nothing can be played: every output sample of the stretch is missed.
    have hnone : ∀ k, k ≤ K → σ.plays w lookahead r k = none := by
      intro k hk
      by_contra hne
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
      have h1 := hle' k hk x hx
      have h2 := hnn k x hx
      exact hP (h2.trans h1)
    have hM : ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt (σ.plays w lookahead r) k : ℝ)
        = (K : ℝ) + 1 - k₀ := by
      have hone : ∀ k ∈ Finset.Ico k₀ (K + 1),
          (missedAt (σ.plays w lookahead r) k : ℝ) = 1 := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        rw [missedAt_of_none (hnone k (Nat.lt_succ_iff.mp hk.2))]
        norm_num
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
        Nat.cast_sub (Nat.le_succ_of_le hK)]
      push_cast
      ring
    have h2 := le_max_right ((w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ)
      - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
    have h3 := mul_le_mul_of_nonneg_right hs1 hn0
    have h4 : (0 : ℝ) ≤ s * (∑ k ∈ Finset.Ico k₀ K,
        (discontinuityAt (σ.plays w lookahead r) k : ℝ) + 1) :=
      mul_nonneg hs0 (by linarith)
    rw [hM]
    linarith


/-! ## A stretch during which nothing from the sender is handled -/

/-- **A bound from one quiet stretch.** If no message that the sender sends
at or after the true time `t₀` is handled before the true time `e`, then
nothing sent at or after `T` is handled before `quietBound t₀ e T`: `T` itself
when `T` is before `t₀`, and the later of `T` and `e` otherwise. -/
def quietBound (t₀ e T : Time) : Time := if T < t₀ then T else max T e

theorem le_quietBound (t₀ e T : Time) : T ≤ quietBound t₀ e T := by
  unfold quietBound
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem quietBound_mono (t₀ e : Time) : Monotone (quietBound t₀ e) := by
  intro T T' hTT'
  unfold quietBound
  split_ifs with h1 h2 h2
  · exact hTT'
  · exact hTT'.trans (le_max_left _ _)
  · exact absurd (lt_of_le_of_lt hTT' h2) h1
  · exact max_le_max hTT' le_rfl

/-- At or after the start of the quiet stretch the bound is at least its
end. -/
theorem le_quietBound_of_le {t₀ e T : Time} (hT : t₀ ≤ T) : e ≤ quietBound t₀ e T := by
  unfold quietBound
  rw [ite_eq_right (not_lt.mpr hT)]
  exact le_max_right _ _

/-- **What every solution pays for a quiet stretch.** Consider a solution
that carries frames only on links from the sender or to the sender, and a
speaker `r` whose host is not the sender's and whose position advances by at
least `s` in every step of continuous playback, with `0 ≤ s ≤ 1`. Suppose
that no message that the sender sends to the speaker's host at or after the
true time `t₀` is handled before the true time `e`, that capture block `c` is
handed over at `t₀` or later, and that the request of playback block `β` is
handled at `e` or earlier. Then for output samples `k₀ ≤ K` with `K` in a
playback block up to `β`: `s` for each output sample from `k₀` to `K` is at
most the room from the position played last before `k₀` to the first frame
of block `c` minus the lookahead, plus the missed samples counted from `k₀`
to `K`, plus `s` times the discontinuities counted from `k₀` to `K - 1` and
one more. -/
theorem Solution.stall_le_of_quiet (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    (hframes : σ.CarriesFramesOn fun h dst => h = w.sender ∨ dst = w.sender) {r : Fin R}
    (hr : w.host r ≠ w.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {t₀ e : Time}
    (hquiet : ∀ u q a, t₀ ≤ u → w.network.deliver w.sender (w.host r) u q = some a → e ≤ a)
    {c β k₀ K : ℕ} (hK : k₀ ≤ K) (hKβ : K < (w.speaker r).first (β + 1))
    (hc : t₀ ≤ w.source.handed c) (hβ : (w.speaker r).asked β ≤ e) :
    s * ((K : ℝ) + 1 - k₀)
      ≤ max ((w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
        + ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt (σ.plays w lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt (σ.plays w lookahead r) k : ℝ)
          + 1) := by
  classical
  refine σ.stall_le_of_earliest w lookahead
    (E := fun h T => if h = w.host r then quietBound t₀ e T else T) ?_ ?_ ?_ hframes hr hs0 hs1
    hslow hK hKβ ?_
  · intro h u q a ha T hT
    have hafter : u < a := w.network.after _ _ _ _ _ ha
    by_cases hh : h = w.host r
    · rw [ite_eq_left hh]
      subst hh
      unfold quietBound
      split_ifs with h1
      · linarith
      · exact max_le (by linarith) (hquiet u q a ((not_lt.mp h1).trans hT) ha)
    · rw [ite_eq_right hh]
      linarith
  · intro h T
    by_cases hh : h = w.host r
    · rw [ite_eq_left hh]
      exact le_quietBound t₀ e T
    · rw [ite_eq_right hh]
  · intro h
    by_cases hh : h = w.host r
    · simp only [hh, ite_true]
      exact quietBound_mono t₀ e
    · simp only [hh, ite_false]
      exact monotone_id
  · rw [ite_eq_left rfl]
    exact hβ.trans (le_quietBound_of_le hc)

end Unisono.Spec
