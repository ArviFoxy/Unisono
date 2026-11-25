/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Target
public import Unisono.Solutions.FixedDelay.Pace
public import Unisono.Solutions.FixedDelay.Data
public import Unisono.Spec.AtLatency

/-!
# The baseline plays at its latency

The main theorem about the baseline in a world that satisfies the bounded
model (`plays_at_latency`). Suppose that

* no speaker is on the sender's host;
* the baseline sends each message more times than a link can drop in a row;
* its slew `w` satisfies `2 ε_D / (1 - ε_D) < w < 1`, where `ε_D` bounds the
  devices' rate errors;
* its latency `L` exceeds `latencyError` plus the worst-case delivery
  margin: the spans of two blocks and of the resampler's lookahead, the
  handoff delay, the longest delay from the sender, and the longest request
  lead.

Then, from some output sample on, every output sample `k` plays sound
captured within `latencyError` of `o(k) - L`, where `o(k)` is the true time
at which `k` leaves. So in the long run the baseline misses no samples and
has no discontinuities, and its latency, synchronization and tracking costs
are bounded (`guarantees`). A world of two hosts meets every hypothesis
(`plays_at_latency_example`), so the hypotheses can all hold at once.

The error `latencyError` is the target's error for the oldest estimates
that a host can use at a request (`targetError`), converted from the target
to the position that the pace keeps within the target's band. The proof
combines the parts for each speaker (`speaker_at_latency`). Speakers on the
sender's host are left to a later theorem; the baseline supports them with
an exact clock estimate.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

omit [DecidableEq H] in
/-- In a world that satisfies the bounds, consecutive requests of a speaker
are at most `m_B (1 + ε_D) / ρ + λ_max` seconds apart. Here `m_B` is the
largest block size, `ρ` the nominal rate, `ε_D` the bound on the devices'
rate errors, and `λ_max` the longest request lead. -/
theorem asked_gap (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (r : Fin R) (b : ℕ) :
    (w.speaker r).asked (b + 1) - (w.speaker r).asked b
      ≤ B.blockMost * (1 + B.deviceRate) / w.rate + B.leadMost := by
  obtain ⟨-, -, hspk, -, -, -, hlead, -, hblocks, -, -⟩ := hw
  have h1 := (hlead r (b + 1)).1
  have h2 := (hlead r b).2
  have hfirst : (w.speaker r).first b ≤ (w.speaker r).first (b + 1) :=
    (w.speaker r).first_strictMono.monotone (Nat.le_succ b)
  have hout := (PlaybackDevice.out_sub_mem (hspk r) hfirst).2
  have hsize := (hblocks r b).2
  have hcast : (((w.speaker r).first (b + 1) : ℕ) : ℝ) - (w.speaker r).first b ≤ B.blockMost := by
    have : (w.speaker r).first (b + 1) ≤ (w.speaker r).first b + B.blockMost := by omega
    have : (((w.speaker r).first (b + 1) : ℕ) : ℝ) ≤ (w.speaker r).first b + B.blockMost := by
      exact_mod_cast this
    linarith
  have hcoef : 0 ≤ (1 + B.deviceRate) / w.rate :=
    div_nonneg (by linarith [B.deviceRate_nonneg]) w.rate_pos.le
  have := mul_le_mul_of_nonneg_left hcast hcoef
  have hlp := B.leadLeast_pos
  have e : (B.blockMost : ℝ) * (1 + B.deviceRate) / w.rate
      = (1 + B.deviceRate) / w.rate * B.blockMost := by ring
  rw [e]
  linarith

omit [DecidableEq H] in
/-- In a world that satisfies the bounds, consecutive handoffs of the
capture device are at most `m_B (1 + ε_D) / ρ + η` seconds apart, where `η`
is the handoff delay. -/
theorem handed_gap (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (b : ℕ) :
    w.source.handed (b + 1) - w.source.handed b
      ≤ B.blockMost * (1 + B.deviceRate) / w.rate + B.handoff := by
  obtain ⟨-, hsrc, -, -, -, hhand, -, hblocks, -, -, -⟩ := hw
  have h1 := hhand (b + 1)
  have h2 := w.source.handed_after b
  have hf1 : 1 ≤ w.source.first (b + 1) := by
    have := w.source.first_strictMono (Nat.lt_succ_self b)
    simp only [Nat.succ_eq_add_one] at this
    omega
  have hle : w.source.first (b + 1) - 1 ≤ w.source.first (b + 1 + 1) - 1 := by
    have := w.source.first_strictMono (Nat.lt_succ_self (b + 1))
    simp only [Nat.succ_eq_add_one] at this
    omega
  have hcap := (CaptureDevice.capture_sub_mem hsrc hle).2
  have hsize := (hblocks (b + 1)).2
  have hcast : (((w.source.first (b + 1 + 1) - 1 : ℕ) : ℝ)) - ((w.source.first (b + 1) - 1 : ℕ) : ℝ)
      ≤ B.blockMost := by
    have : w.source.first (b + 1 + 1) - 1 ≤ (w.source.first (b + 1) - 1) + B.blockMost := by omega
    have : (((w.source.first (b + 1 + 1) - 1 : ℕ) : ℝ))
        ≤ ((w.source.first (b + 1) - 1 : ℕ) : ℝ) + B.blockMost := by exact_mod_cast this
    linarith
  have hcoef : 0 ≤ (1 + B.deviceRate) / w.rate :=
    div_nonneg (by linarith [B.deviceRate_nonneg]) w.rate_pos.le
  have := mul_le_mul_of_nonneg_left hcast hcoef
  have e : (B.blockMost : ℝ) * (1 + B.deviceRate) / w.rate
      = (1 + B.deviceRate) / w.rate * B.blockMost := by ring
  rw [e]
  linarith


omit [DecidableEq H] in
/-- **A last term below a threshold.** Let `a` be a sequence whose
consecutive terms differ by at most `G` and which eventually reaches
`x - D`. If `a 0 + D < x`, then some term satisfies
`a b₀ + D < x ≤ a b₀ + D + G`. -/
theorem exists_last_below {a : ℕ → ℝ} {G D x : ℝ} (hgap : ∀ b, a (b + 1) - a b ≤ G)
    (h0 : a 0 + D < x) (hbig : ∃ b, x ≤ a b + D) :
    ∃ b₀, a b₀ + D < x ∧ x ≤ a b₀ + D + G := by
  classical
  set N := Nat.find hbig with hN
  have hspec : x ≤ a N + D := Nat.find_spec hbig
  have hN0 : N ≠ 0 := by
    intro h0'
    rw [h0'] at hspec
    linarith
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, N = b₀ + 1 := ⟨N - 1, by omega⟩
  have hmin := Nat.find_min hbig (show b₀ < N by omega)
  rw [not_le] at hmin
  refine ⟨b₀, by linarith, ?_⟩
  rw [hb₀] at hspec
  have := hgap b₀
  linarith

omit [DecidableEq H] in
/-- The block of a playback device that holds output sample `k`. -/
theorem exists_block_of_sample (d : PlaybackDevice) (k : ℕ) :
    ∃ b, d.first b ≤ k ∧ k < d.first (b + 1) := by
  have hex : ∃ b, k < d.first (b + 1) :=
    ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (d.first_strictMono.id_le (k + 1))⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases hb : Nat.find hex with _ | b
  · rw [d.first_zero]; exact Nat.zero_le k
  · have := Nat.find_min hex (show b < Nat.find hex by omega)
    rw [not_lt] at this
    exact this

/-- **What a speaker plays is the position its host chose.** When step `n`
handles request `b` of speaker `r` before output sample `k` of the block
leaves, the output sample plays the position chosen for it, if the host
holds the frames it needs. -/
theorem plays_eq_chosen (w : World H R) (lookahead : ℕ+) {n : ℕ} {r : Fin R} {b : ℕ}
    (hb : ((solution p : Solution H R Payload).states w lookahead n).askedNext r = b)
    (he : earliest (((solution p : Solution H R Payload).states w lookahead n).key w)
      ((solution p : Solution H R Payload).states w lookahead n).due = some (.asked r b))
    {k : ℕ} (hk : k ∈ (w.speaker r).block b)
    (hlt : (w.speaker r).asked b < (w.speaker r).out k) :
    (solution p : Solution H R Payload).plays w lookahead r k
      = playable lookahead (((solution p : Solution H R Payload).states w lookahead n).held (w.host r))
        (chosen p (memoryOf p (w.host r)
            (((solution p : Solution H R Payload).states w lookahead n).views (w.host r)))
          ((w.speaker r).first b) ((w.speaker r).reported b)
          ((memoryOf p (w.host r)
            (((solution p : Solution H R Payload).states w lookahead n).views (w.host r))).last r)
          ((w.speaker r).first b) (k - (w.speaker r).first b)) := by
  rw [Solution.plays_of_asked_step_of_lt w (solution p) lookahead hb he hk hlt, solution_append]
  congr 1
  have hkb : (w.speaker r).first b ≤ k ∧ k < (w.speaker r).first (b + 1) := by
    unfold PlaybackDevice.block at hk
    rw [List.mem_range'_1] at hk
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self b)
    omega
  simp only [act]
  unfold PlaybackDevice.block
  rw [positions_block]
  have hlook := lookup_chosen (chosen p (memoryOf p (w.host r)
      (((solution p : Solution H R Payload).states w lookahead n).views (w.host r)))
      ((w.speaker r).first b) ((w.speaker r).reported b)
      ((memoryOf p (w.host r)
        (((solution p : Solution H R Payload).states w lookahead n).views (w.host r))).last r)
      ((w.speaker r).first b))
    ((w.speaker r).first b) ((w.speaker r).first (b + 1) - (w.speaker r).first b)
    (k - (w.speaker r).first b) (by omega)
  rw [show (w.speaker r).first b + (k - (w.speaker r).first b) = k by omega] at hlook
  rw [hlook]
  rfl

/-- The error of the baseline's target, in seconds of capture time. The
arguments are the clock estimate's error `ntp`, the age `a₁` of the
estimate's clock query at the request, and the time `a₂` from the handoff
of the block that the host extrapolates from to the request. The error is
the sum of twice the timestamp error, the estimate's error, the clocks'
drift over the age of the estimate and over the age of the block, the
playback device's rate error over a block, and the capture device's rate
error over the time from the block to the position. -/
noncomputable def targetError (B : Bounds H) (rate period latency ntp a₁ a₂ : ℝ) : ℝ :=
  (2 * B.report + ntp
    + 2 * B.clockRate * (B.leadMost + a₁ + period / (1 - B.clockRate))
    + B.clockRate * (B.leadMost + a₂ + B.handoff + (B.blockMost - 1) * (1 + B.deviceRate) / rate)
    + B.deviceRate * (B.blockMost - 1) / rate)
  + B.deviceRate * (latency + (B.blockMost - 1) * (1 + B.deviceRate) / rate
    + (B.leadMost + a₂ + B.handoff + (B.blockMost - 1) * (1 + B.deviceRate) / rate)
    + (2 * B.report + ntp
      + 2 * B.clockRate * (B.leadMost + a₁ + period / (1 - B.clockRate))
      + B.clockRate * (B.leadMost + a₂ + B.handoff + (B.blockMost - 1) * (1 + B.deviceRate) / rate)
      + B.deviceRate * (B.blockMost - 1) / rate))

omit [DecidableEq H] in
/-- `targetError` is monotone in the clock estimate's error and in the ages
of the clock estimate and of the block. -/
theorem targetError_mono (B : Bounds H) {rate period latency ntp ntp' a₁ a₁' a₂ a₂' : ℝ}
    (hntp : ntp ≤ ntp') (ha₁ : a₁ ≤ a₁') (ha₂ : a₂ ≤ a₂') :
    targetError B rate period latency ntp a₁ a₂ ≤ targetError B rate period latency ntp' a₁' a₂' := by
  have hC := B.clockRate_nonneg
  have hD := B.deviceRate_nonneg
  unfold targetError
  gcongr

/-- The error `E` of the baseline's fixed-latency playback in a world that
satisfies the bounds, when `dmin` and `dmax` bound the delays between the
sender and the speakers' hosts. It is the target's error for the largest
error of the clock estimate and for the oldest estimates, converted from
the target to the position that the pace keeps within the target's
band. -/
noncomputable def latencyError (p : Params H) (B : Bounds H) (rate dmin dmax : ℝ) : ℝ :=
  (1 + B.deviceRate) / (1 - B.deviceRate)
    * targetError B rate p.period p.latency ((dmax - dmin + B.clockRate * (2 * dmax)) / 2)
      (2 * dmax + (B.blockMost * (1 + B.deviceRate) / rate + B.leadMost))
      (dmax + (B.blockMost * (1 + B.deviceRate) / rate + B.handoff))

/-- At every sufficiently late request, every output sample `k` of the
block has a target whose sound was captured within the target's error of
`o(k) - L`, where `o(k)` is the true time at which `k` leaves. -/
theorem late_targets (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hrate : p.rate = w.rate) (hnodup : p.speakers.Nodup)
    (hcopies : B.lossRun < p.copies) (hperiod : 0 ≤ p.period) (hL : 0 ≤ p.latency)
    {dmin dmax : ℝ} (r : Fin R) (hh : w.host r ∈ p.speakers) (hhs : w.host r ≠ w.sender)
    (hdmin₁ : dmin ≤ B.delayLeast (w.host r) w.sender)
    (hdmin₂ : dmin ≤ B.delayLeast w.sender (w.host r))
    (hdmax₁ : B.delayMost (w.host r) w.sender ≤ dmax)
    (hdmax₂ : B.delayMost w.sender (w.host r) ≤ dmax) :
    ∃ bmin, ∀ b, bmin ≤ b → ∀ n,
      ((solution p : Solution H R Payload).states w lookahead n).askedNext r = b →
      earliest (((solution p : Solution H R Payload).states w lookahead n).key w)
        ((solution p : Solution H R Payload).states w lookahead n).due = some (.asked r b) →
      ∀ k ∈ (w.speaker r).block b, ∃ x,
        target p (memoryOf p (w.host r)
          (((solution p : Solution H R Payload).states w lookahead n).views (w.host r)))
          ((w.speaker r).first b) ((w.speaker r).reported b) k = some x ∧
        |w.captured x - ((w.speaker r).out k - p.latency)|
          ≤ targetError B w.rate p.period p.latency ((dmax - dmin + B.clockRate * (2 * dmax)) / 2)
            (2 * dmax + (B.blockMost * (1 + B.deviceRate) / w.rate + B.leadMost))
            (dmax + (B.blockMost * (1 + B.deviceRate) / w.rate + B.handoff)) := by
  have hw' := hw
  obtain ⟨-, hsrc, hspk, -, -, -, hlead, -, -, -, -⟩ := hw'
  have hρ := w.rate_pos
  have hεD1 := B.deviceRate_lt_one
  have hεC := B.clockRate_nonneg
  have hd₁ := (B.delayLeast_pos (w.host r) w.sender).trans_le (B.delayLeast_le (w.host r) w.sender)
  have hd₂ := (B.delayLeast_pos w.sender (w.host r)).trans_le (B.delayLeast_le w.sender (w.host r))
  set RTT := B.delayMost (w.host r) w.sender + B.delayMost w.sender (w.host r) with hRTT
  obtain ⟨bmin, hbmin⟩ := PlaybackDevice.asked_unbounded hρ (hspk r) hεD1 (hlead r)
    (max ((w.speaker r).asked 0 + RTT) (w.source.handed 0 + B.delayMost w.sender (w.host r)))
  refine ⟨bmin, fun b hb n hnb hne k hk => ?_⟩
  have hmono := (w.speaker r).asked_mono hb
  have hl₁ : (w.speaker r).asked 0 + RTT < (w.speaker r).asked b := by
    have := le_max_left ((w.speaker r).asked 0 + RTT) (w.source.handed 0 + B.delayMost w.sender (w.host r))
    linarith
  have hl₂ : w.source.handed 0 + B.delayMost w.sender (w.host r) < (w.speaker r).asked b := by
    have := le_max_right ((w.speaker r).asked 0 + RTT) (w.source.handed 0 + B.delayMost w.sender (w.host r))
    linarith
  -- The last request answered in time, and the last block arrived in time.
  obtain ⟨b₀, hb₀, hb₀'⟩ := exists_last_below (a := (w.speaker r).asked) (D := RTT)
    (G := B.blockMost * (1 + B.deviceRate) / w.rate + B.leadMost) (x := (w.speaker r).asked b)
    (asked_gap w B hw r) hl₁ ⟨b, by linarith⟩
  obtain ⟨b'', hb''₁, hb''₂⟩ := exists_last_below (a := w.source.handed)
    (D := B.delayMost w.sender (w.host r))
    (G := B.blockMost * (1 + B.deviceRate) / w.rate + B.handoff) (x := (w.speaker r).asked b)
    (handed_gap w B hw) hl₂
    (by
      obtain ⟨b', hb'⟩ := CaptureDevice.handed_unbounded hρ hsrc hεD1 ((w.speaker r).asked b)
      exact ⟨b', by linarith⟩)
  have hq : (w.speaker r).asked b₀ + B.delayMost (w.host r) w.sender
      + B.delayMost w.sender (w.host r) < (w.speaker r).asked b := by
    linarith [hb₀, hRTT]
  obtain ⟨x, hx, hbound⟩ := target_band p w B hw lookahead hsender hrate hnodup hcopies hperiod hL
    hh hhs (b₀ := b₀) (b'' := b'') hne hq hb''₁ hk
  refine ⟨x, hx, le_trans hbound (targetError_mono B ?_ ?_ ?_)⟩
  · -- The estimate's error.
    have hm : max (B.delayMost (w.host r) w.sender - B.delayLeast w.sender (w.host r))
        (B.delayMost w.sender (w.host r) - B.delayLeast (w.host r) w.sender) ≤ dmax - dmin :=
      max_le (by linarith) (by linarith)
    have hC : B.clockRate * (B.delayMost (w.host r) w.sender + B.delayMost w.sender (w.host r))
        ≤ B.clockRate * (2 * dmax) := mul_le_mul_of_nonneg_left (by linarith) hεC
    linarith
  · linarith
  · linarith

/-- **A speaker of the baseline plays at its latency.** Consider a world
that satisfies the bounds, a speaker whose host is not the sender's host,
and bounds `dmin` and `dmax` on the delays between the sender and that
host. Suppose the slew `w` satisfies `2 ε_D / (1 - ε_D) < w < 1`, and the
latency `L` exceeds `latencyError` plus the worst-case delivery margin of
`plays_at_latency`. Then, from some output sample on, the speaker plays
continuously, and each output sample `k` plays sound captured within
`latencyError` of `o(k) - L`. -/
theorem speaker_at_latency (w : World H R) (B : Bounds H) (hw : w.WithinBounds B)
    (lookahead : ℕ+) (hsender : p.sender = w.sender) (hrate : p.rate = w.rate)
    (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies) (hperiod : 0 ≤ p.period)
    (hL : 0 ≤ p.latency) {dmin dmax : ℝ} (r : Fin R) (hh : w.host r ∈ p.speakers)
    (hhs : w.host r ≠ w.sender)
    (hdmin₁ : dmin ≤ B.delayLeast (w.host r) w.sender)
    (hdmin₂ : dmin ≤ B.delayLeast w.sender (w.host r))
    (hdmax₁ : B.delayMost (w.host r) w.sender ≤ dmax)
    (hdmax₂ : B.delayMost w.sender (w.host r) ≤ dmax)
    (hslew : 2 * B.deviceRate / (1 - B.deviceRate) < p.slew) (hslew1 : p.slew < 1)
    (hlat : latencyError p B w.rate dmin dmax
      + (((lookahead : ℕ) : ℝ) + 2 * ((B.blockMost : ℝ) - 1)) * (1 + B.deviceRate) / w.rate
      + B.handoff + dmax + B.leadMost < p.latency) :
    ∃ K, ∀ k, K ≤ k → PlaysContinuously ((solution p : Solution H R Payload).plays w lookahead r) k ∧
      ∃ x, (solution p : Solution H R Payload).plays w lookahead r k = some x ∧
        |w.captured x - ((w.speaker r).out k - p.latency)| ≤ latencyError p B w.rate dmin dmax := by
  have hw' := hw
  obtain ⟨-, hsrc, hspk, -, -, -, hlead, -, hblocksr, -, -⟩ := hw'
  have hρ := w.rate_pos
  have hεD := B.deviceRate_nonneg
  have hεD1 := B.deviceRate_lt_one
  have h1ε : 0 < 1 - B.deviceRate := by linarith
  have hν : 0 ≤ 2 * B.deviceRate / (1 - B.deviceRate) := div_nonneg (by linarith) h1ε.le
  have hslew0 : 0 ≤ p.slew := hν.trans hslew.le
  set E := latencyError p B w.rate dmin dmax with hE
  set Et := targetError B w.rate p.period p.latency ((dmax - dmin + B.clockRate * (2 * dmax)) / 2)
    (2 * dmax + (B.blockMost * (1 + B.deviceRate) / w.rate + B.leadMost))
    (dmax + (B.blockMost * (1 + B.deviceRate) / w.rate + B.handoff)) with hEt
  have hEEt : E = (1 + B.deviceRate) / (1 - B.deviceRate) * Et := rfl
  -- The steps of the requests, and late enough requests.
  choose step hstepb hstepe using request_step p w B hw lookahead r
  obtain ⟨bmin, hlate⟩ := late_targets p w B hw lookahead hsender hrate hnodup hcopies hperiod hL r
    hh hhs hdmin₁ hdmin₂ hdmax₁ hdmax₂
  -- The block of each output sample.
  choose blk hblk using exists_block_of_sample (w.speaker r)
  have hfirst := (w.speaker r).first_strictMono
  have hblk_eq : ∀ k b, (w.speaker r).first b ≤ k → k < (w.speaker r).first (b + 1) → blk k = b := by
    intro k b h1 h2
    obtain ⟨h3, h4⟩ := hblk k
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hfirst.monotone (Nat.lt_iff_add_one_le.mp hlt)
      omega
    · have := hfirst.monotone (Nat.lt_iff_add_one_le.mp hlt)
      omega
  have hmemblk : ∀ k, k ∈ (w.speaker r).block (blk k) := by
    intro k
    unfold PlaybackDevice.block
    rw [List.mem_range'_1]
    have := hblk k
    omega
  -- The memory at each request, the targets and the positions chosen.
  set M : ℕ → Memory H R := fun b => memoryOf p (w.host r)
    (((solution p : Solution H R Payload).states w lookahead (step b)).views (w.host r)) with hM
  set tg : ℕ → Option ℝ := fun k => target p (M (blk k)) ((w.speaker r).first (blk k))
    ((w.speaker r).reported (blk k)) k with htg
  set ch : ℕ → Option ℝ := fun k => chosen p (M (blk k)) ((w.speaker r).first (blk k))
    ((w.speaker r).reported (blk k)) ((M (blk k)).last r) ((w.speaker r).first (blk k))
    (k - (w.speaker r).first (blk k)) with hch
  set xs : ℕ → ℝ := fun k => (tg k).getD 0 with hxs
  set X : ℕ → ℝ := fun k => (ch k).getD 0 with hX
  set K₀ := (w.speaker r).first bmin with hK₀
  have hlateblk : ∀ k, K₀ ≤ k → bmin ≤ blk k := by
    intro k hk
    by_contra hlt
    rw [not_le] at hlt
    have := hfirst.monotone (Nat.lt_iff_add_one_le.mp hlt)
    have := (hblk k).2
    omega
  -- Targets of late output samples.
  have htgk : ∀ k, K₀ ≤ k → tg k = some (xs k)
      ∧ |w.captured (xs k) - ((w.speaker r).out k - p.latency)| ≤ Et := by
    intro k hk
    obtain ⟨x, hx, hbound⟩ := hlate (blk k) (hlateblk k hk) (step (blk k)) (hstepb (blk k))
      (hstepe (blk k)) k (hmemblk k)
    have htgx : tg k = some x := hx
    have hxsx : xs k = x := by simp only [hxs, htgx, Option.getD_some]
    rw [hxsx]
    exact ⟨htgx, hbound⟩
  -- Positions of late output samples.
  have hchk : ∀ k, K₀ ≤ k → ch k = some (X k) := by
    intro k hk
    have hsome : (ch k).isSome := by
      apply chosen_isSome
      intro i hi
      have hk' : K₀ ≤ (w.speaker r).first (blk k) + i := by
        have := hlateblk k hk
        have := hfirst.monotone this
        omega
      have hblk' : blk ((w.speaker r).first (blk k) + i) = blk k :=
        hblk_eq _ _ (by omega) (by have := hblk k; omega)
      have := (htgk _ hk').1
      simp only [htg, hblk'] at this
      rw [this]
      rfl
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    simp only [hX, hx, Option.getD_some]
  -- Each request is handled after the one before.
  have hstep_lt : ∀ b, step b < step (b + 1) := by
    intro b
    by_contra hge
    rw [not_lt] at hge
    have := Solution.askedNext_mono w (solution p) lookahead r hge
    simp only at this
    rw [hstepb, hstepb] at this
    omega
  -- The positions follow the pace from `K₀` on.
  have hpace : ∀ k, K₀ ≤ k → X (k + 1) = X k + 1 + clamp p.slew (xs (k + 1) - X k - 1) := by
    intro k hk
    have hkb := hblk k
    have hxk := hchk k hk
    have htk1 := (htgk (k + 1) (by omega)).1
    have hxk1 := hchk (k + 1) (by omega)
    have hk' : chosen p (M (blk k)) ((w.speaker r).first (blk k)) ((w.speaker r).reported (blk k))
        ((M (blk k)).last r) ((w.speaker r).first (blk k)) (k - (w.speaker r).first (blk k))
        = some (X k) := hxk
    rcases Nat.lt_or_ge (k + 1) ((w.speaker r).first (blk k + 1)) with hin | hout
    · -- Within a block.
      have hb1 : blk (k + 1) = blk k := hblk_eq _ _ (by omega) hin
      have hgoal : target p (M (blk k)) ((w.speaker r).first (blk k)) ((w.speaker r).reported (blk k))
          ((w.speaker r).first (blk k) + (k - (w.speaker r).first (blk k)) + 1) = some (xs (k + 1)) := by
        rw [show (w.speaker r).first (blk k) + (k - (w.speaker r).first (blk k)) + 1 = k + 1 by omega]
        have := htk1
        simp only [htg, hb1] at this
        exact this
      have hsucc := chosen_succ p _ _ _ _ _ _ hk' hgoal
      have hch1 : ch (k + 1) = chosen p (M (blk k)) ((w.speaker r).first (blk k))
          ((w.speaker r).reported (blk k)) ((M (blk k)).last r) ((w.speaker r).first (blk k))
          (k - (w.speaker r).first (blk k) + 1) := by
        simp only [hch, hb1]
        congr 1
        omega
      rw [hch1, hsucc] at hxk1
      simp only [Option.some.injEq] at hxk1
      rw [← hxk1]
      rfl
    · -- At the start of the next block.
      have hk1 : k + 1 = (w.speaker r).first (blk k + 1) := by omega
      have hb1 : blk (k + 1) = blk k + 1 := by
        apply hblk_eq _ _ (by omega)
        have := hfirst (show blk k + 1 < blk k + 1 + 1 by omega)
        omega
      have hlast := last_at_next_request p w lookahead (hstepb (blk k)) (hstepe (blk k))
        (hstepb (blk k + 1)) (hstep_lt (blk k))
      have hlen : 0 < (w.speaker r).first (blk k + 1) - (w.speaker r).first (blk k) := by omega
      have hlc := lastChosen_block p (M (blk k)) r ((w.speaker r).reported (blk k))
        ((w.speaker r).first (blk k)) _ hlen
      have hlast' : (M (blk k + 1)).last r = some (k, X k) := by
        have e1 : (M (blk k + 1)).last r = lastChosen (positions p (M (blk k)) r
            ((w.speaker r).block (blk k)) ((w.speaker r).reported (blk k))) := hlast
        rw [e1]
        unfold PlaybackDevice.block
        rw [hlc, show (w.speaker r).first (blk k + 1) - (w.speaker r).first (blk k) - 1
          = k - (w.speaker r).first (blk k) by omega, hk']
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
        omega
      have hgoal : target p (M (blk k + 1)) ((w.speaker r).first (blk k + 1))
          ((w.speaker r).reported (blk k + 1)) (k + 1) = some (xs (k + 1)) := by
        have := htk1
        simp only [htg, hb1] at this
        exact this
      have hzero := chosen_zero_continues p (M (blk k + 1)) ((w.speaker r).first (blk k + 1))
        ((w.speaker r).reported (blk k + 1)) k (x := X k) hgoal
      have hch1 : ch (k + 1) = chosen p (M (blk k + 1)) ((w.speaker r).first (blk k + 1))
          ((w.speaker r).reported (blk k + 1)) (some (k, X k)) (k + 1) 0 := by
        simp only [hch, hb1, hlast']
        rw [← hk1, Nat.sub_self]
      rw [hch1, hzero] at hxk1
      simp only [Option.some.injEq] at hxk1
      rw [← hxk1]
      rfl
  -- The ideal trajectory, and the pace's convergence to the targets' band.
  choose T hT using fun k => w.exists_captured_eq hsrc hεD hεD1 ((w.speaker r).out k - p.latency)
  have hband : ∀ k, K₀ ≤ k → |xs k - T k| ≤ w.rate / (1 - B.deviceRate) * Et := by
    intro k hk
    have h1 := w.sub_le_of_captured hsrc hεD1 (xs k) (T k)
    rw [hT k] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (htgk k hk).2 (div_nonneg hρ.le h1ε.le))
  have hTstep : ∀ k, K₀ ≤ k → |T (k + 1) - T k - 1| ≤ 2 * B.deviceRate / (1 - B.deviceRate) :=
    fun k _ => trajectory_step w hsrc hεD hεD1 (w.speaker r) (hspk r) p.latency T hT k
  obtain ⟨K₁, hK₁, hconv⟩ := advance_converges hslew X xs T K₀ hpace hband hTstep
  -- The sound at the positions chosen was captured within `E`.
  have hcapX : ∀ k, K₁ ≤ k → |w.captured (X k) - ((w.speaker r).out k - p.latency)| ≤ E := by
    intro k hk
    rw [← hT k]
    calc |w.captured (X k) - w.captured (T k)|
        ≤ (1 + B.deviceRate) / w.rate * |X k - T k| := w.captured_lipschitz hsrc (X k) (T k)
      _ ≤ (1 + B.deviceRate) / w.rate * (w.rate / (1 - B.deviceRate) * Et) :=
          mul_le_mul_of_nonneg_left (hconv k hk) (div_nonneg (by linarith) hρ.le)
      _ = E := by
          rw [hEEt]
          field_simp
  -- Late positions are past the start of the stream.
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℕ, w.source.capture 0 + p.latency + E < (w.speaker r).out K₂ := by
    have hlo : 0 < (1 - B.deviceRate) / w.rate := div_pos h1ε hρ
    obtain ⟨K₂, hK₂⟩ := exists_nat_gt
      ((w.source.capture 0 + p.latency + E - (w.speaker r).out 0) / ((1 - B.deviceRate) / w.rate))
    refine ⟨K₂, ?_⟩
    have hout := (PlaybackDevice.out_sub_mem (hspk r) (Nat.zero_le K₂)).1
    rw [div_lt_iff₀ hlo] at hK₂
    simp only [Nat.cast_zero, sub_zero] at hout
    rw [mul_comm] at hout
    linarith
  set K := max K₁ K₂ with hKdef
  have hX0 : ∀ k, K ≤ k → 0 ≤ X k := by
    intro k hk
    have hcap := abs_le.mp (hcapX k (le_trans (le_max_left _ _) hk))
    have hout := (w.speaker r).out_strictMono.monotone (le_trans (le_max_right _ _) hk)
    by_contra hneg
    rw [not_le] at hneg
    have hm := (w.captured_sub_mem hsrc hneg.le).1
    have h0 : w.captured 0 = w.source.capture 0 := by simpa using w.captured_natCast 0
    have hlo : 0 ≤ (1 - B.deviceRate) / w.rate := div_nonneg h1ε.le hρ.le
    have := mul_nonneg hlo (show (0 : ℝ) ≤ 0 - X k by linarith)
    linarith
  -- Late output samples play the positions chosen.
  have hplays : ∀ k, K ≤ k → (solution p : Solution H R Payload).plays w lookahead r k = some (X k) := by
    intro k hk
    have hk₀ : K₀ ≤ k := le_trans hK₁ (le_trans (le_max_left _ _) hk)
    have hlt : (w.speaker r).asked (blk k) < (w.speaker r).out k := by
      have hmem := hmemblk k
      unfold PlaybackDevice.block at hmem
      rw [List.mem_range'_1] at hmem
      exact hw.asked_lt_of_le hmem.1
    rw [plays_eq_chosen p w lookahead (hstepb (blk k)) (hstepe (blk k)) (hmemblk k) hlt]
    have hck : chosen p (M (blk k)) ((w.speaker r).first (blk k)) ((w.speaker r).reported (blk k))
        ((M (blk k)).last r) ((w.speaker r).first (blk k)) (k - (w.speaker r).first (blk k))
        = some (X k) := hchk k hk₀
    rw [hck]
    apply playable_of_captured p w B hw lookahead hsender hnodup hcopies hh hhs (hX0 k hk)
    -- The frames around the position arrived before the request.
    have htime := Solution.handled_time w (solution p) lookahead
      (Solution.handled_of_asked w (solution p) lookahead (hstepe (blk k)))
    rw [htime]
    have hcap := (abs_le.mp (hcapX k (le_trans (le_max_left _ _) hk))).2
    have hleadb := (hlead r (blk k)).2
    have hkb := hblk k
    have hout := (PlaybackDevice.out_sub_mem (hspk r) hkb.1).2
    have hsize := (hblocksr r (blk k)).2
    have hb1 : (1 : ℝ) ≤ B.blockMost := by
      exact_mod_cast B.blockLeast_pos.trans_le B.blockLeast_le
    have hkg : (k : ℝ) - (w.speaker r).first (blk k) ≤ (B.blockMost : ℝ) - 1 := by
      have : k ≤ (w.speaker r).first (blk k) + (B.blockMost - 1) := by omega
      have : (k : ℝ) ≤ ((w.speaker r).first (blk k) : ℝ) + ((B.blockMost - 1 : ℕ) : ℝ) := by
        exact_mod_cast this
      have h3 : ((B.blockMost - 1 : ℕ) : ℝ) = (B.blockMost : ℝ) - 1 := by
        rw [Nat.cast_sub (by exact_mod_cast hb1 : 1 ≤ B.blockMost)]; simp
      linarith
    have hcoef : 0 ≤ (1 + B.deviceRate) / w.rate := div_nonneg (by linarith) hρ.le
    have hspan := mul_le_mul_of_nonneg_left hkg hcoef
    have e1 : (((lookahead : ℕ) : ℝ) + 2 * ((B.blockMost : ℝ) - 1)) * (1 + B.deviceRate) / w.rate
        = (((lookahead : ℕ) : ℝ) + ((B.blockMost : ℝ) - 1)) * (1 + B.deviceRate) / w.rate
          + (1 + B.deviceRate) / w.rate * ((B.blockMost : ℝ) - 1) := by ring
    rw [e1] at hlat
    linarith
  -- Late output samples play continuously.
  refine ⟨K, fun k hk => ⟨?_, X k, hplays k hk, hcapX k (le_trans (le_max_left _ _) hk)⟩⟩
  have hk₀ : K₀ ≤ k := le_trans hK₁ (le_trans (le_max_left _ _) hk)
  have hstep := hpace k hk₀
  have hcl := clamp_mem (x := xs (k + 1) - X k - 1) hslew0
  refine ⟨X k, X (k + 1), hplays k hk, hplays (k + 1) (by omega), ?_, ?_⟩
  · rw [hstep]; linarith [hcl.1]
  · rw [hstep]; linarith [hcl.2]

/-- **The baseline plays at its latency.** Consider a world that satisfies
the bounds, in which no speaker is on the sender's host, and let `dmin` and
`dmax` bound the delays between the sender and the speakers' hosts. Suppose
that
* the baseline sends each message more times than a link can drop in a row;
* its slew `w` satisfies `2 ε_D / (1 - ε_D) < w < 1`, where `ε_D` bounds the
  devices' rate errors;
* its latency `L` exceeds `latencyError` plus the worst-case delivery
  margin: the spans of two blocks and of the resampler's lookahead, the
  handoff delay, `dmax`, and the longest request lead.

Then the baseline's playback is at latency `L` within `latencyError` from
some output sample on. -/
theorem plays_at_latency (w : World H R) (B : Bounds H) (hw : w.WithinBounds B)
    (lookahead : ℕ+) (hsender : p.sender = w.sender) (hrate : p.rate = w.rate)
    (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies) (hperiod : 0 ≤ p.period)
    (hL : 0 ≤ p.latency) {dmin dmax : ℝ}
    (hhosts : ∀ r, w.host r ∈ p.speakers ∧ w.host r ≠ w.sender)
    (hdmin : ∀ r, dmin ≤ B.delayLeast (w.host r) w.sender ∧ dmin ≤ B.delayLeast w.sender (w.host r))
    (hdmax : ∀ r, B.delayMost (w.host r) w.sender ≤ dmax ∧ B.delayMost w.sender (w.host r) ≤ dmax)
    (hslew : 2 * B.deviceRate / (1 - B.deviceRate) < p.slew) (hslew1 : p.slew < 1)
    (hlat : latencyError p B w.rate dmin dmax
      + (((lookahead : ℕ) : ℝ) + 2 * ((B.blockMost : ℝ) - 1)) * (1 + B.deviceRate) / w.rate
      + B.handoff + dmax + B.leadMost < p.latency) :
    ∃ K, w.PlaysAtLatency ((solution p : Solution H R Payload).plays w lookahead) p.latency
      (latencyError p B w.rate dmin dmax) K := by
  choose K hK using fun r => speaker_at_latency p w B hw lookahead hsender hrate hnodup hcopies
    hperiod hL r (hhosts r).1 (hhosts r).2 (hdmin r).1 (hdmin r).2 (hdmax r).1 (hdmax r).2 hslew
    hslew1 hlat
  exact ⟨Finset.univ.sup K, fun r k hk => hK r k (le_trans (Finset.le_sup (Finset.mem_univ r)) hk)⟩

/-- **The baseline's guarantees.** Assume the hypotheses of
`plays_at_latency`. Let `E = latencyError`, and let `δ = (1 + ε_D) / ρ` be
the longest time between two output samples. Then in the long run the
baseline misses no samples and has no discontinuities. Its latency is at
most `L + E + δ`, and its synchronization cost is at most `(E + δ)²`. When
every target latency is within `D` of `L`, its tracking cost is at most
`(D + E + δ)²`. -/
theorem guarantees (w : World H R) (B : Bounds H) (hw : w.WithinBounds B)
    (lookahead : ℕ+) (hsender : p.sender = w.sender) (hrate : p.rate = w.rate)
    (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies) (hperiod : 0 ≤ p.period)
    (hL : 0 ≤ p.latency) {dmin dmax D : ℝ}
    (hhosts : ∀ r, w.host r ∈ p.speakers ∧ w.host r ≠ w.sender)
    (hdmin : ∀ r, dmin ≤ B.delayLeast (w.host r) w.sender ∧ dmin ≤ B.delayLeast w.sender (w.host r))
    (hdmax : ∀ r, B.delayMost (w.host r) w.sender ≤ dmax ∧ B.delayMost w.sender (w.host r) ≤ dmax)
    (hslew : 2 * B.deviceRate / (1 - B.deviceRate) < p.slew) (hslew1 : p.slew < 1)
    (hlat : latencyError p B w.rate dmin dmax
      + (((lookahead : ℕ) : ℝ) + 2 * ((B.blockMost : ℝ) - 1)) * (1 + B.deviceRate) / w.rate
      + B.handoff + dmax + B.leadMost < p.latency)
    (hD : ∀ n, |w.target n - p.latency| ≤ D) :
    w.missed ((solution p : Solution H R Payload).plays w lookahead) = 0
      ∧ w.discontinuities ((solution p : Solution H R Payload).plays w lookahead) = 0
      ∧ w.meanLatency ((solution p : Solution H R Payload).plays w lookahead)
        ≤ ENNReal.ofReal (p.latency + latencyError p B w.rate dmin dmax
          + (1 + B.deviceRate) / w.rate)
      ∧ w.sync ((solution p : Solution H R Payload).plays w lookahead)
        ≤ ENNReal.ofReal ((latencyError p B w.rate dmin dmax + (1 + B.deviceRate) / w.rate) ^ 2)
      ∧ w.tracking ((solution p : Solution H R Payload).plays w lookahead)
        ≤ ENNReal.ofReal ((D + latencyError p B w.rate dmin dmax
          + (1 + B.deviceRate) / w.rate) ^ 2) := by
  obtain ⟨K, hK⟩ := plays_at_latency p w B hw lookahead hsender hrate hnodup hcopies hperiod hL
    hhosts hdmin hdmax hslew hslew1 hlat
  obtain ⟨-, hsrc, hspk, -, -, -, -, -, -, -, -⟩ := hw
  have hδ : ∀ r k, K ≤ k → (w.speaker r).out (k + 1) - (w.speaker r).out k
      ≤ (1 + B.deviceRate) / w.rate := by
    intro r k _
    have := (abs_le.mp (hspk r k)).2
    rw [add_div]
    linarith
  have hc : ∀ n, w.source.capture (n + 1) - w.source.capture n ≤ (1 + B.deviceRate) / w.rate := by
    intro n
    have := (abs_le.mp (hsrc n)).2
    rw [add_div]
    linarith
  exact ⟨missed_eq_zero w _ hK, discontinuities_eq_zero w _ hK, meanLatency_le w _ hK hδ hc,
    sync_le w _ hK hδ hc, tracking_le w _ hK hδ hc hD⟩

/-- **The main theorem is not vacuous.** Consider a world of two hosts, the
sender (`false`) and one speaker's host (`true`). Its clocks and devices are
exact, both devices use blocks of one frame, the request lead is half a
second, and the network delivers every message after one second. With a
latency of three seconds, one copy of each message and a slew of one half,
the baseline meets every hypothesis of `plays_at_latency` in this world,
where `latencyError = 0`. In this world, the baseline therefore plays at
its latency with zero error. -/
theorem plays_at_latency_example :
    ∃ (w : World Bool 1) (B : Bounds Bool) (p : Params Bool) (lookahead : ℕ+),
      w.WithinBounds B ∧ latencyError p B w.rate 1 1 = 0 ∧
      ∃ K, w.PlaysAtLatency ((solution p : Solution Bool 1 Payload).plays w lookahead) p.latency
        (latencyError p B w.rate 1 1) K := by
  let w : World Bool 1 :=
    { rate := 1
      rate_pos := one_pos
      sender := false
      host := fun _ => true
      hosts := fun h => by
        cases h
        · exact Or.inl rfl
        · exact Or.inr ⟨0, rfl⟩
      clock := fun _ => ⟨id, strictMono_id, continuous_id⟩
      source :=
        { capture := fun n => n
          capture_strictMono := Nat.strictMono_cast
          first := id
          first_zero := rfl
          first_strictMono := strictMono_id
          handed := fun b => b
          handed_mono := Nat.mono_cast
          handed_after := fun b => by simp
          reported := fun b => b }
      speaker := fun _ =>
        { out := fun k => k + 1
          out_strictMono := fun a b h => by simpa using h
          first := id
          first_zero := rfl
          first_strictMono := strictMono_id
          asked := fun b => b + 1 / 2
          asked_mono := StrictMono.monotone fun a b h => by simpa using h
          reported := fun b => b + 1 }
      network := ⟨fun _ _ s _ => some (s + 1), fun _ _ s _ a h => by
        simp only [Option.some.injEq] at h; linarith⟩
      target := fun _ => 0 }
  let B : Bounds Bool :=
    { clockRate := 0
      clockRate_nonneg := le_rfl
      clockRate_lt_one := one_pos
      deviceRate := 0
      deviceRate_nonneg := le_rfl
      deviceRate_lt_one := one_pos
      report := 0
      report_nonneg := le_rfl
      handoff := 0
      handoff_nonneg := le_rfl
      leadLeast := 1 / 2
      leadMost := 1 / 2
      leadLeast_pos := by norm_num
      leadLeast_le := le_rfl
      blockLeast := 1
      blockMost := 1
      blockLeast_pos := one_pos
      blockLeast_le := le_rfl
      delayLeast := fun _ _ => 1
      delayMost := fun _ _ => 1
      delayLeast_pos := fun _ _ => one_pos
      delayLeast_le := fun _ _ => le_rfl
      lossRun := 0 }
  let p : Params Bool :=
    { sender := false
      speakers := [true]
      rate := 1
      latency := 3
      copies := 1
      period := 0
      slew := 1 / 2 }
  have hw : w.WithinBounds B := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h s t _
      simp [w, B]
    · intro n
      simp [w, B]
    · intro r k
      simp [w, B]
    · intro b
      simp [w, B]
    · intro r b
      simp [w, B]
    · intro b
      simp [w, B]
    · intro r b
      norm_num [w, B]
    · intro b
      simp [w, B]
    · intro r b
      simp [w, B]
    · intro i j s q a h
      simp only [w, B, Option.some.injEq] at h ⊢
      constructor <;> linarith
    · intro i j q send
      exact ⟨0, le_rfl, rfl⟩
  have hzero : latencyError p B w.rate 1 1 = 0 := by
    simp [latencyError, targetError, B, p]
  refine ⟨w, B, p, 1, hw, hzero, ?_⟩
  apply plays_at_latency p w B hw 1 rfl rfl (by simp [p]) (by simp [p, B]) le_rfl
    (by norm_num [p])
  · intro r
    exact ⟨by simp [w, p], by simp [w]⟩
  · intro r
    exact ⟨le_rfl, le_rfl⟩
  · intro r
    exact ⟨le_rfl, le_rfl⟩
  · norm_num [B, p]
  · norm_num [p]
  · rw [hzero]
    norm_num [B, p, w]

end Unisono.Solutions.FixedDelay
