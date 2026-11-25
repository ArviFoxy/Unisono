/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.IdleEstimate

/-!
# The capture schedule and the block check while nothing disturbs the stream

In a world built from a regular draw, let the stream to a speaker be
undisturbed from the true time `a₀` to `b₀` (`Draw.Undisturbed`). Only the
sender's side of that matters here: its host is idle, the rates of its
clock and of the capture device's clock stay within their bands, and the
capture device's timestamps are at most `ρ` early.

* `capture_sub_mem_of_undisturbed`: the time between two frames captured in
  the stretch is the nominal time between them divided by a rate of the
  capture device's clock within its band.
* `knotInput_eq_of_undisturbed`: for a block whose frames are all captured
  in the stretch, the input of the knot is the reading of the sender's clock
  at the capture of the block's last frame, when the schedule's bound covers
  the band of the two clocks and its slack covers `ρ`.
* `knot_eq_of_undisturbed`: **once a knot is at its input, the knots of the
  later blocks of the stretch are at their inputs**: each is the reading of
  the sender's clock at the capture of the block's last frame.
* `blockCheck_of_knot`: in the setting `KnotSetting`, the block check holds
  for an estimate `s` when the block whose stretch of the schedule holds `s`
  has its knot at its input, and the bounds of the level that the hosts are
  told contain those of the level rule within `scheduleSlack`.

Not proved here: how long the knots take to return to their inputs after a
disturbance.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld Unisono.Model.Descent

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} {B : RateBands} {ρ : ℝ} {a₀ b₀ : Time}

omit [DecidableEq H] in
/-- **The time between two frames captured while nothing disturbs the
stream**: at least the nominal time between them divided by the largest
rate of the capture device's clock, and at most that time divided by the
least rate. -/
theorem capture_sub_mem_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid) {n n' : ℕ}
    (hnn : n ≤ n') (han : a₀ ≤ w.source.capture n) (hnb : w.source.capture n' ≤ b₀) :
    ((n' : ℝ) - n) / m.rate / B.captureHi ≤ w.source.capture n' - w.source.capture n
      ∧ w.source.capture n' - w.source.capture n ≤ ((n' : ℝ) - n) / m.rate / B.captureLo := by
  have hmono := w.source.capture_strictMono.monotone hnn
  obtain ⟨h1, h2⟩ := hU.capture_sub hd han hmono hnb
  have e1 := hB.capture n'
  have e2 := hB.capture n
  have hadv : d.deviceReading none (w.source.capture n')
      - d.deviceReading none (w.source.capture n) = ((n' : ℝ) - n) / m.rate := by
    have e : ((n' : ℝ) - n) / m.rate = (n' : ℝ) / m.rate - (n : ℝ) / m.rate := by ring
    rw [e]
    linarith
  rw [hadv] at h1 h2
  have hHi : 0 < B.captureHi := lt_of_lt_of_le hBv.capture_pos hBv.capture_le
  constructor
  · rw [div_le_iff₀ hHi]
    linarith
  · rw [le_div_iff₀ hBv.capture_pos]
    linarith

omit [DecidableEq H] in
/-- **The input of a knot while nothing disturbs the stream.** Let the
frames of block `b` all be captured in the undisturbed stretch. With valid
settings of the knots whose nominal time is that of the model, whose bound
covers the largest rate of the sender's clock divided by the least rate of
the capture device's clock, and whose slack is at least `ρ`: the input of
the block's knot is the reading of the sender's clock at the capture of the
block's last frame. -/
theorem knotInput_eq_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    {kn : KnotSettings} (hkn : kn.Valid) (hnom : kn.nominal = 1 / m.rate)
    (hhi : B.senderHi / B.captureLo ≤ 1 + kn.bound) (hρ : ρ ≤ kn.slack) {b : ℕ}
    (hb₁ : a₀ ≤ w.source.capture (w.source.first b)) (hb₂ : w.lastCapture b ≤ b₀) :
    w.knotInput kn b = (w.clock w.sender).read (w.lastCapture b) := by
  obtain ⟨hn, hb0, -⟩ := hkn
  have hr := m.rate_pos
  have hlt : w.source.first b < w.source.first (b + 1) :=
    w.source.first_strictMono (Nat.lt_succ_self b)
  have hfirst : w.source.first b ≤ w.source.first (b + 1) - 1 := by omega
  have hc0c : w.source.capture (w.source.first b) ≤ w.lastCapture b :=
    w.source.capture_strictMono.monotone hfirst
  have hhand : w.source.handed b = w.lastCapture b :=
    hB.handed_of_idleOn (hd.hostPaused_monotone _) hU.forward.source (hb₁.trans hc0c) hb₂
  obtain ⟨-, hcap⟩ := capture_sub_mem_of_undisturbed hB hd hU hBv hfirst hb₁ hb₂
  obtain ⟨-, hs⟩ := hU.sender_sub hd hb₁ hc0c hb₂
  rw [← hB.clock, ← hB.clock] at hs
  have hrep := hU.report _ ⟨hb₁, hc0c.trans hb₂⟩
  have hstamp := hB.capture_reported b
  have hBLpos : (1 : ℝ) ≤ w.blockLength b := by exact_mod_cast w.blockLength_pos b
  have hBL : ((w.source.first (b + 1) - 1 : ℕ) : ℝ) - (w.source.first b : ℝ)
      = (w.blockLength b : ℝ) - 1 := by
    unfold World.blockLength
    rw [Nat.cast_sub (by omega), Nat.cast_sub hlt.le]
    push_cast
    ring
  rw [hBL] at hcap
  -- The block's frames on the sender's clock.
  have hsHi : 0 ≤ B.senderHi := hBv.sender_pos.le.trans hBv.sender_le
  have h1 : (w.clock w.sender).read (w.lastCapture b)
        - (w.clock w.sender).read (w.source.capture (w.source.first b))
      ≤ B.senderHi / B.captureLo * (((w.blockLength b : ℝ) - 1) * kn.nominal) := by
    have h2 := mul_le_mul_of_nonneg_left hcap hsHi
    have e : B.senderHi * (((w.blockLength b : ℝ) - 1) / m.rate / B.captureLo)
        = B.senderHi / B.captureLo * (((w.blockLength b : ℝ) - 1) * kn.nominal) := by
      rw [hnom]
      field_simp
    rw [e] at h2
    exact hs.trans h2
  have hN : 0 ≤ ((w.blockLength b : ℝ) - 1) * kn.nominal := mul_nonneg (by linarith) hn.le
  have h3 := mul_le_mul_of_nonneg_right hhi hN
  have h4 : (1 + kn.bound) * (((w.blockLength b : ℝ) - 1) * kn.nominal)
      ≤ w.blockLength b * kn.nominal * (1 + kn.bound) := by
    have h5 : ((w.blockLength b : ℝ) - 1) * kn.nominal ≤ w.blockLength b * kn.nominal := by
      nlinarith
    have := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ 1 + kn.bound)
    linarith
  show Unisono.Spec.knotInput kn (w.handedReading b) (w.source.reported b) (w.blockLength b) = _
  unfold Unisono.Spec.knotInput World.handedReading
  rw [hhand, hstamp]
  apply min_eq_left
  linarith

omit [DecidableEq H] in
/-- **Once a knot is at its input, the knots of the later blocks of the
stretch are at their inputs.** In the setting of
`knotInput_eq_of_undisturbed`, let the bound of the knots also cover the
least rate of the sender's clock divided by the largest rate of the capture
device's clock. Let the first frame of block `bk` be captured in the
stretch, and let the knot of `bk` be its input. Then for every block from
`bk` on whose last frame is captured in the stretch, the knot is the reading
of the sender's clock at the capture of the block's last frame. -/
theorem knot_eq_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    {kn : KnotSettings} (hkn : kn.Valid) (hnom : kn.nominal = 1 / m.rate)
    (hlo : 1 - kn.bound ≤ B.senderLo / B.captureHi)
    (hhi : B.senderHi / B.captureLo ≤ 1 + kn.bound) (hρ : ρ ≤ kn.slack) {bk : ℕ}
    (hbk : a₀ ≤ w.source.capture (w.source.first bk))
    (hk : w.knot kn bk = w.knotInput kn bk) {b : ℕ} (hb : bk ≤ b)
    (hbb : w.lastCapture b ≤ b₀) :
    w.knot kn b = (w.clock w.sender).read (w.lastCapture b) := by
  induction b, hb using Nat.le_induction with
  | base =>
    rw [hk]
    exact knotInput_eq_of_undisturbed hB hd hU hBv hkn hnom hhi hρ hbk hbb
  | succ b hb ih =>
    have hn := hkn.1
    have hr := m.rate_pos
    have hlt1 : w.source.first b < w.source.first (b + 1) :=
      w.source.first_strictMono (Nat.lt_succ_self b)
    have hlt2 : w.source.first (b + 1) < w.source.first (b + 1 + 1) :=
      w.source.first_strictMono (Nat.lt_succ_self (b + 1))
    have hfb : w.source.first bk ≤ w.source.first b := w.source.first_strictMono.monotone hb
    have hidx : w.source.first (b + 1) - 1 ≤ w.source.first (b + 1 + 1) - 1 := by omega
    have hmono : w.lastCapture b ≤ w.lastCapture (b + 1) :=
      w.source.capture_strictMono.monotone hidx
    have ihb := ih (hmono.trans hbb)
    have ha_b : a₀ ≤ w.lastCapture b :=
      hbk.trans (w.source.capture_strictMono.monotone (by omega))
    have hin := knotInput_eq_of_undisturbed hB hd hU hBv hkn hnom hhi hρ (b := b + 1)
      (hbk.trans (w.source.capture_strictMono.monotone (by omega))) hbb
    obtain ⟨hc1, hc2⟩ := capture_sub_mem_of_undisturbed hB hd hU hBv hidx ha_b hbb
    obtain ⟨hs1, hs2⟩ := hU.sender_sub hd ha_b hmono hbb
    rw [← hB.clock, ← hB.clock] at hs1 hs2
    have hBL : ((w.source.first (b + 1 + 1) - 1 : ℕ) : ℝ) - ((w.source.first (b + 1) - 1 : ℕ) : ℝ)
        = (w.blockLength (b + 1) : ℝ) := by
      unfold World.blockLength
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub hlt2.le]
      push_cast
      ring
    rw [hBL] at hc1 hc2
    change _ ≤ w.lastCapture (b + 1) - w.lastCapture b at hc1
    change w.lastCapture (b + 1) - w.lastCapture b ≤ _ at hc2
    have hcHi : 0 < B.captureHi := lt_of_lt_of_le hBv.capture_pos hBv.capture_le
    have hsHi : 0 ≤ B.senderHi := hBv.sender_pos.le.trans hBv.sender_le
    have hBn : 0 ≤ (w.blockLength (b + 1) : ℝ) * kn.nominal :=
      mul_nonneg (Nat.cast_nonneg _) hn.le
    have e1 : B.senderLo * ((w.blockLength (b + 1) : ℝ) / m.rate / B.captureHi)
        = w.blockLength (b + 1) * kn.nominal * (B.senderLo / B.captureHi) := by
      rw [hnom]
      field_simp
    have e2 : B.senderHi * ((w.blockLength (b + 1) : ℝ) / m.rate / B.captureLo)
        = w.blockLength (b + 1) * kn.nominal * (B.senderHi / B.captureLo) := by
      rw [hnom]
      field_simp
    have h1 := mul_le_mul_of_nonneg_left hc1 hBv.sender_pos.le
    have h2 := mul_le_mul_of_nonneg_left hc2 hsHi
    rw [e1] at h1
    rw [e2] at h2
    have h3 := mul_le_mul_of_nonneg_left hlo hBn
    have h4 := mul_le_mul_of_nonneg_left hhi hBn
    rw [← hin]
    apply w.knot_succ_eq_knotInput kn
    · rw [hin, ihb]
      linarith
    · rw [hin, ihb]
      linarith

/-- **The block check holds where the knot is at its input.** In the
setting `KnotSetting` with the knots of the timing settings `t`, with
`q.lo ≤ q.hi`, a start of the level between them, and bounds of the level,
as the hosts are told them, that contain `q.lo` and `q.hi` within
`scheduleSlack`: let `s` be a reading such that every block whose stretch of
the schedule holds `s` has its knot at its input. Then the block check holds
for `s` at every view of a host followed by an event that is not an
arrival. -/
theorem blockCheck_of_knot {p : FixedDelay.Params H} {rules : Rules H R}
    {A : H → H → Time → Time} {q : LevelSettings} {share : ℝ} {t : TimingSettings}
    (hK : KnotSetting p rules w A q share t.knots) (lookahead : ℕ+) (hlohi : q.lo ≤ q.hi)
    (hstart : q.start ∈ Set.Icc q.lo q.hi) (hlow : t.levelLow - t.scheduleSlack ≤ q.lo)
    (hhigh : q.hi ≤ t.levelHigh + t.scheduleSlack) {n : ℕ} {h : H} {s : ℝ}
    (hknot : ∀ b, dueEdge p rules w lookahead q share t.knots b ≤ s →
      s < dueEdge p rules w lookahead q share t.knots (b + 1) →
      w.knot t.knots b = w.knotInput t.knots b)
    {e₀ : Event H R Payload} (he₀ : ∀ i msg F, e₀.observation ≠ .received i msg F) :
    blockCheck t (((ruled p rules : Solution H R Payload).states w lookahead n).views h
      ++ [e₀]) s := by
  obtain ⟨need, hlev⟩ := hK.level
  have hcap := hK.capture
  have hsender := hK.noLoss.sender
  have hprog := hK.handovers lookahead
  intro e he i fr stamp capture period level slope F hobs hcov
  rcases List.mem_append.mp he with he | he
  swap
  · rw [List.mem_singleton] at he
    subst he
    exact absurd hobs (he₀ _ _ _)
  obtain ⟨b, t', -, -, -, hfr, hF, ⟨i', hi'⟩, hhd⟩ :=
    ruled_received_block p rules w hsender lookahead he hobs
  have hstamp := ruled_received_stamp p rules w hsender lookahead he hobs hfr
  have hcard : F.card = w.blockLength b := by
    rw [hF]
    unfold CaptureDevice.block
    rw [List.toFinset_card_of_nodup List.nodup_range', List.length_range']
    rfl
  -- The block's stretch of the schedule holds `s`, so its knot is at its input.
  rw [hhd, hcard] at hcov
  obtain ⟨hlo', hhi'⟩ :=
    (covers_iff hcap hlev hK.share_nonneg hK.share_lt_one hK.nominal_pos hprog b s).mp hcov
  have hkb := hknot b hlo' hhi'
  -- The header of the block.
  rw [runHeader_eq hcap hlev hprog b] at hhd
  obtain ⟨-, hcp, hpd, hlv, hsl⟩ := Header.mk.inj hhd
  -- The level at the right end of the block.
  obtain ⟨i'', hi''⟩ := hprog (b + 1)
  have hsucc := announcedAt_succ (ruled p rules : Solution H R Payload) w lookahead q share
    t.knots hi' hi''
  have hmem := announcedAt_fst_mem (ruled p rules : Solution H R Payload) w lookahead q share
    t.knots hlohi hstart hi''
  rw [hsucc] at hmem
  rw [hcp, hpd, hlv, hsl, hcard, hstamp]
  have e1 : w.handedReading b - w.blockLength b * w.knotPeriod t.knots b
      + w.blockLength b * w.knotPeriod t.knots b = w.handedReading b := by ring
  rw [e1]
  have e2 : Unisono.Spec.knotInput t.knots (w.handedReading b) (w.source.reported b)
      (w.blockLength b) = w.knotInput t.knots b := rfl
  rw [e2, ← hkb]
  obtain ⟨hm1, hm2⟩ := hmem
  constructor <;> linarith

end Unisono.Solutions.Controller
