/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Views
public import Unisono.Spec.Held

/-!
# The baseline in a world without loss: what a receiving host holds

Consider a world whose network loses nothing and delivers a message from `i`
to `j` sent at true time `s` at a true time `A i j s`, whichever message of
the link it is. The delays need not be bounded. A *receiving host* is a host
that drives a speaker and is not the sender's host.

* The message of every block is in transit to every receiving host after the
  block's handover, and arrives at `A sender j (handed b)` (`block_inFlight`).
  A step whose event occurs after that time has handled it
  (`block_handled_of_noLoss`), and the host then holds the block's frames
  (`block_arrives_of_noLoss`).
* Only block messages carry frames (`inFlight_frames`), so every frame that
  a receiving host holds came in the message of its block
  (`held_of_noLoss`).
* **What a receiving host holds at a device request.** When a playback
  device requests a block, its host holds a frame if and only if the message
  of the frame's block arrived strictly before the request
  (`mem_held_iff_arrived`). A message that arrives at the very time of the
  request is handled after the request.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- A frame belongs to one block of the capture device only. -/
theorem CaptureDevice.block_unique (d : CaptureDevice) {n b b' : ℕ} (h : n ∈ d.block b)
    (h' : n ∈ d.block b') : b = b' := by
  unfold CaptureDevice.block at h h'
  rw [List.mem_range'_1] at h h'
  have hm := d.first_strictMono
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · have h1 : d.first (b + 1) ≤ d.first b' := hm.monotone hlt
    have h2 : d.first b ≤ d.first (b + 1) := (hm (Nat.lt_succ_self b)).le
    omega
  · exact heq
  · have h1 : d.first (b' + 1) ≤ d.first b := hm.monotone hgt
    have h2 : d.first b' ≤ d.first (b' + 1) := (hm (Nat.lt_succ_self b')).le
    omega

end Unisono.Spec

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- **The message of a block is in transit after the block's handover.** In
a world without loss, consider a block `b` handed over before the event of
step `k`, and a receiving host `j`. After an earlier step, the message of the
block to `j` is in transit, with the block's frames, and it arrives at
`A sender j (handed b)`. -/
theorem block_inFlight (w : World H R) (lookahead : ℕ+) {A : H → H → Time → Time}
    (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hsender : p.sender = w.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    {j : H} (hj : j ∈ p.speakers) (hjs : j ≠ w.sender) {b k : ℕ}
    (hk : w.source.handed b < (solution p : Solution H R Payload).eventTime w lookahead k) :
    ∃ n < k, (⟨A w.sender j (w.source.handed b), w.sender, j,
        Payload.block (w.source.first b) (w.source.reported b), (w.source.block b).toFinset⟩ :
          InFlight H Payload)
        ∈ ((solution p : Solution H R Payload).states w lookahead (n + 1)).inFlight := by
  set σ : Solution H R Payload := solution p with hσ
  obtain ⟨n, hnk, hbn, hearly⟩ :=
    σ.exists_handed_step w lookahead (σ.lt_handedNext w lookahead hk)
  have hn : σ.handled w lookahead n = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun m => (m, w.target m)) (w.source.reported b)) := by
    unfold Solution.handled
    rw [hearly]
  set x : H → Payload × Finset ℕ :=
    fun _ => (Payload.block (w.source.first b) (w.source.reported b), (w.source.block b).toFinset)
    with hx
  have hjf : j ∈ p.speakers.filter (· ≠ p.sender) := by
    rw [List.mem_filter, hsender]
    exact ⟨hj, by simpa using hjs⟩
  obtain ⟨i0, hi0⟩ := replicate_entries p.copies x _ (hnodup.filter _) hjf
  obtain ⟨hidx, hget, hcount⟩ := hi0 0 hcopies
  have hS := solution_handed_sends p w hsender ((σ.states w lookahead n).views w.sender)
    ((w.clock w.sender).read (w.source.handed b)) b
  have hin := σ.sent_inFlight w lookahead hn hS hidx (arr := A w.sender j (w.source.handed b))
    (by rw [hget]; exact hA _ _ _ _)
  rw [hget] at hin
  have hF : (x j).2.filter (· ∈ (σ.states w lookahead n).held w.sender
        ∪ (Observation.handed ((w.source.block b).map fun m => (m, w.target m))
            (w.source.reported b) : Observation H R Payload).frames)
      = (w.source.block b).toFinset := by
    refine Finset.filter_true_of_mem fun m hm => Finset.mem_union_right _ ?_
    simpa [Observation.frames, List.map_map, Function.comp_def, hx] using hm
  rw [hF] at hin
  exact ⟨n, hnk, hin⟩

/-- **A block that arrived is held.** In a world without loss, a receiving
host `j` holds the frames of block `b` at every step whose event occurs
after the block's message arrives. -/
theorem block_arrives_of_noLoss (w : World H R) (lookahead : ℕ+) {A : H → H → Time → Time}
    (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hsender : p.sender = w.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    {j : H} (hj : j ∈ p.speakers) (hjs : j ≠ w.sender) {b k : ℕ}
    (hk : A w.sender j (w.source.handed b)
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    (w.source.block b).toFinset
      ⊆ ((solution p : Solution H R Payload).states w lookahead k).held j := by
  have hlt : w.source.handed b < (solution p : Solution H R Payload).eventTime w lookahead k :=
    lt_trans (w.network.after _ _ _ _ _ (hA w.sender j _ 0)) hk
  obtain ⟨n, hnk, hin⟩ := block_inFlight p w lookahead hA hsender hnodup hcopies hj hjs hlt
  exact Solution.frames_arrive (solution p) w lookahead hin (Nat.succ_le_of_lt hnk) hk

/-- **A block that arrived was handled.** In a world without loss, the
message of block `b` to a receiving host `j` is handled before every step
whose event occurs after the message arrives. -/
theorem block_handled_of_noLoss (w : World H R) (lookahead : ℕ+) {A : H → H → Time → Time}
    (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hsender : p.sender = w.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    {j : H} (hj : j ∈ p.speakers) (hjs : j ≠ w.sender) {b k : ℕ}
    (hk : A w.sender j (w.source.handed b)
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    ∃ i < k, (solution p : Solution H R Payload).handled w lookahead i
      = some (j, A w.sender j (w.source.handed b),
        .received w.sender (.block (w.source.first b) (w.source.reported b))
          (w.source.block b).toFinset) := by
  have hlt : w.source.handed b < (solution p : Solution H R Payload).eventTime w lookahead k :=
    lt_trans (w.network.after _ _ _ _ _ (hA w.sender j _ 0)) hk
  obtain ⟨n, hnk, hin⟩ := block_inFlight p w lookahead hA hsender hnodup hcopies hj hjs hlt
  obtain ⟨i, -, hik, hhi⟩ := Solution.handled_before w (solution p) lookahead hin
    (Nat.succ_le_of_lt hnk) hk
  exact ⟨i, hik, hhi⟩

/-- **Only block messages carry frames.** A message of the baseline in
transit that is not a block message carries no frame. -/
theorem inFlight_frames (w : World H R) (lookahead : ℕ+) :
    ∀ n, ∀ m ∈ ((solution p : Solution H R Payload).states w lookahead n).inFlight,
      (∀ f st, m.contents ≠ .block f st) → m.frames = ∅ := by
  set σ : Solution H R Payload := solution p
  intro n
  induction n with
  | zero => intro m hm; simp [Solution.states, State.start] at hm
  | succ n ih =>
    intro m hm hnb
    rcases σ.mem_inFlight_succ w lookahead n hm with hold |
      ⟨h, t, obs, hn, s, hs, ho, hd, hc, hf, q, hq⟩
    · exact ih m hold hnb
    · rcases sends_cases p h _ _ hs with
        ⟨frames, stamp, f, t', hobs, hh, hhead, -, hs1, hs2⟩ | ⟨i, sent, F, hobs, hh, rfl⟩ |
          ⟨r, outputs, stamp, hobs, hh, rfl⟩
      · exact absurd (hc.trans hs1) (hnb f stamp)
      · rw [hf]
        simp
      · rw [hf]
        simp

/-- **Every frame that a receiving host holds came in the message of its
block.** In a world without loss, if a host `j` other than the sender's holds
frame `n` at step `k`, then `n` belongs to a block `b` whose message `j`
handled at an earlier step, at the true time `A sender j (handed b)`. -/
theorem held_of_noLoss (w : World H R) (lookahead : ℕ+) {A : H → H → Time → Time}
    (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hsender : p.sender = w.sender) {j : H} (hjs : j ≠ w.sender) {k n : ℕ}
    (hn : n ∈ ((solution p : Solution H R Payload).states w lookahead k).held j) :
    ∃ b, n ∈ w.source.block b ∧ ∃ i < k, ∃ F,
      (solution p : Solution H R Payload).handled w lookahead i
        = some (j, A w.sender j (w.source.handed b),
          .received w.sender (.block (w.source.first b) (w.source.reported b)) F) := by
  set σ : Solution H R Payload := solution p with hσ
  obtain ⟨e, he, hne⟩ := (σ.mem_held_iff w lookahead k j n).mp hn
  obtain ⟨i, hik, t, obs, hhi, rfl⟩ := Solution.handled_of_mem_views w σ lookahead he
  cases obs with
  | handed frames stamp =>
    obtain ⟨b, hb, -⟩ := Solution.handled_handed w σ lookahead hhi
    exact absurd hb hjs
  | asked r outs stamp => simp [Observation.frames] at hne
  | timer => simp [Observation.frames] at hne
  | received o c F =>
    simp only [Observation.frames] at hne
    obtain ⟨msg, hmsg, hdest, harr, horig, hcont, hfr⟩ :=
      Solution.handled_received w σ lookahead hhi
    have hO := origin_inFlight p w lookahead hsender i msg hmsg
    cases c with
    | block f st =>
      unfold Origin at hO
      simp only [hcont] at hO
      obtain ⟨b, hob, hf, hst, hfb, q, hq⟩ := hO
      rw [hdest, hA] at hq
      have harr' : A w.sender j (w.source.handed b) = t := (Option.some.inj hq).trans harr
      have ho : o = w.sender := horig.symm.trans hob
      subst ho hf hst harr'
      refine ⟨b, ?_, i, hik, F, hhi⟩
      rw [← hfr, hfb] at hne
      exact List.mem_toFinset.mp hne
    | ask sent =>
      have hempty := inFlight_frames p w lookahead i msg hmsg (by
        intro f st
        rw [hcont]
        simp)
      rw [← hfr, hempty] at hne
      simp at hne
    | answer sent received =>
      have hempty := inFlight_frames p w lookahead i msg hmsg (by
        intro f st
        rw [hcont]
        simp)
      rw [← hfr, hempty] at hne
      simp at hne

/-- **What a receiving host holds at a device request.** In a world without
loss, let step `k` handle request `β` of speaker `r`, whose host is a
receiving host. The host holds a frame of block `b` at that step if and only
if the message of block `b` arrived strictly before the request. -/
theorem mem_held_iff_arrived (w : World H R) (lookahead : ℕ+) {A : H → H → Time → Time}
    (hA : ∀ i j s q, w.network.deliver i j s q = some (A i j s))
    (hsender : p.sender = w.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    {r : Fin R} (hj : w.host r ∈ p.speakers) (hjs : w.host r ≠ w.sender) {k β : ℕ}
    (hβ : ((solution p : Solution H R Payload).states w lookahead k).askedNext r = β)
    (hearly : earliest (((solution p : Solution H R Payload).states w lookahead k).key w)
      ((solution p : Solution H R Payload).states w lookahead k).due = some (.asked r β))
    {n b : ℕ} (hn : n ∈ w.source.block b) :
    n ∈ ((solution p : Solution H R Payload).states w lookahead k).held (w.host r)
      ↔ A w.sender (w.host r) (w.source.handed b) < (w.speaker r).asked β := by
  set σ : Solution H R Payload := solution p with hσ
  have htime : σ.eventTime w lookahead k = (w.speaker r).asked β :=
    Solution.handled_time w σ lookahead (Solution.handled_of_asked w σ lookahead hearly)
  constructor
  · intro hheld
    obtain ⟨b', hn', i, hik, F, hhi⟩ := held_of_noLoss p w lookahead hA hsender hjs hheld
    obtain rfl : b' = b := w.source.block_unique hn' hn
    have hlt := Solution.received_lt_asked σ w lookahead hik.le hhi r
    rwa [hβ] at hlt
  · intro harr
    apply block_arrives_of_noLoss p w lookahead hA hsender hnodup hcopies hj hjs
      (by rw [htime]; exact harr)
    exact List.mem_toFinset.mpr hn

end Unisono.Solutions.FixedDelay
