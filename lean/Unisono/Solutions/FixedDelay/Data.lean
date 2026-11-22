/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Views

/-!
# The baseline in a bounded world: the data

A *receiving host* is a host that drives a speaker and is not the sender's
host. Let `ρ` be the nominal rate, `m_B` the largest block size, `ε_D` the
bound on the devices' rate errors, `s = (m_B - 1)(1 + ε_D) / ρ` the longest
span of a block, `η` the handoff delay, and `d_max` the longest delay from
the sender to a receiving host.

* A frame captured more than `s + η + d_max` before a step's event has
  reached the receiving host by that step (`frame_held`).
* A position is therefore playable at the receiving host when its sound was
  captured earlier still, by the time `a (1 + ε_D) / ρ` that the
  resampler's lookahead of `a` frames spans (`playable_of_captured`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

omit [DecidableEq H] in
/-- The block of the capture device that holds frame `m`. -/
theorem exists_block_of_frame (d : CaptureDevice) (m : ℕ) :
    ∃ β, d.first β ≤ m ∧ m < d.first (β + 1) := by
  have hex : ∃ β, m < d.first (β + 1) :=
    ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) (d.first_strictMono.id_le (m + 1))⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases hβ : Nat.find hex with _ | β
  · rw [d.first_zero]; exact Nat.zero_le m
  · have := Nat.find_min hex (show β < Nat.find hex by omega)
    rw [not_lt] at this
    exact this

/-- **A frame captured early enough has reached every receiving host.**
Consider a world that satisfies the bounds and a receiving host `j`. If
frame `m` was captured more than `s + η + d_max` before the event of step
`k`, then `j` holds frame `m` at step `k`. Here `s` is the longest span of a
block, `η` the handoff delay, and `d_max` the longest delay from the sender
to `j`. -/
theorem frame_held (w : World H R) (B : Bounds H)
    (hw : w.WithinBounds B) (lookahead : ℕ+) (hsender : p.sender = w.sender)
    (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies) {j : H} (hj : j ∈ p.speakers)
    (hjs : j ≠ w.sender) {m k : ℕ}
    (hm : w.source.capture m + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate + B.handoff
        + B.delayMost w.sender j
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    m ∈ ((solution p : Solution H R Payload).states w lookahead k).held j := by
  have hw' := hw
  obtain ⟨-, hsrc, -, -, -, hhand, -, hblocks, -, -, -⟩ := hw'
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_block_of_frame w.source m
  have hlast : w.source.first (β + 1) - 1 - m ≤ B.blockMost - 1 := by
    have := (hblocks β).2
    omega
  have hcap := (CaptureDevice.capture_sub_mem hsrc (show m ≤ w.source.first (β + 1) - 1 by omega)).2
  have hcast : ((w.source.first (β + 1) - 1 : ℕ) : ℝ) - m ≤ (B.blockMost : ℝ) - 1 := by
    have hb := B.blockLeast_pos.trans_le B.blockLeast_le
    have h1 : w.source.first (β + 1) - 1 ≤ m + (B.blockMost - 1) := by omega
    have h2 : ((w.source.first (β + 1) - 1 : ℕ) : ℝ) ≤ (m : ℝ) + ((B.blockMost - 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 : ((B.blockMost - 1 : ℕ) : ℝ) = (B.blockMost : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ B.blockMost)]
      simp
    linarith
  have hrate := w.rate_pos
  have hε := B.deviceRate_nonneg
  have hcoef : 0 ≤ (1 + B.deviceRate) / w.rate := div_nonneg (by linarith) hrate.le
  have hmul := mul_le_mul_of_nonneg_left hcast hcoef
  have hh := hhand β
  have hfm : (w.source.block β).toFinset ⊆
      ((solution p : Solution H R Payload).states w lookahead k).held j := by
    apply block_arrives p w B hw
      lookahead hsender hnodup hcopies hj hjs
    have e : (B.blockMost - 1 : ℝ) * (1 + B.deviceRate) / w.rate
        = (1 + B.deviceRate) / w.rate * (B.blockMost - 1) := by ring
    rw [e] at hm
    linarith
  apply hfm
  simp only [List.mem_toFinset, CaptureDevice.block, List.mem_range'_1]
  omega

/-- **A position is playable when the frames around it arrived in time.**
Consider a world that satisfies the bounds and a receiving host `j`. A
position `x ≥ 0` is playable at `j` at step `k` if its sound was captured
more than `(a + m_B - 1)(1 + ε_D) / ρ + η + d_max` before the event of step
`k`. Here `a` is the resampler's lookahead in frames, `m_B` the largest
block size, `ρ` the nominal rate, `ε_D` the bound on the devices' rate
errors, `η` the handoff delay, and `d_max` the longest delay from the sender
to `j`. -/
theorem playable_of_captured (w : World H R) (B : Bounds H)
    (hw : w.WithinBounds B) (lookahead : ℕ+) (hsender : p.sender = w.sender)
    (hnodup : p.speakers.Nodup) (hcopies : B.lossRun < p.copies) {j : H} (hj : j ∈ p.speakers)
    (hjs : j ≠ w.sender) {k : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hearly : w.captured x + ((lookahead : ℕ) + (B.blockMost - 1)) * (1 + B.deviceRate) / w.rate
        + B.handoff + B.delayMost w.sender j
      < (solution p : Solution H R Payload).eventTime w lookahead k) :
    playable lookahead ((solution p : Solution H R Payload).states w lookahead k |>.held j) (some x)
      = some x := by
  have hrate := w.rate_pos
  have hε := B.deviceRate_nonneg
  have hsrc := hw.2.1
  have hheld : ∀ n : ℕ, |(n : ℝ) - x| < (lookahead : ℕ) →
      n ∈ ((solution p : Solution H R Payload).states w lookahead k).held j := by
    intro n hn
    apply frame_held p w B hw lookahead hsender hnodup hcopies hj hjs
    have hnx : (n : ℝ) ≤ x + (lookahead : ℕ) := by
      have := (abs_lt.mp hn).2
      linarith
    have hmono : w.captured n ≤ w.captured (x + (lookahead : ℕ)) := by
      rcases le_total (n : ℝ) (x + (lookahead : ℕ)) with h | h
      · have := (w.captured_sub_mem hsrc h).1
        have hcoef : 0 ≤ (1 - B.deviceRate) / w.rate :=
          div_nonneg (by linarith [B.deviceRate_lt_one]) hrate.le
        nlinarith [mul_nonneg hcoef (sub_nonneg.mpr h)]
      · rw [le_antisymm hnx h]
    have hstep := (w.captured_sub_mem hsrc (show x ≤ x + (lookahead : ℕ) by
      have : (0 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)).2
    rw [w.captured_natCast] at hmono
    have e : (1 + B.deviceRate) / w.rate * (x + (lookahead : ℕ) - x)
        = ((lookahead : ℕ) : ℝ) * (1 + B.deviceRate) / w.rate := by ring
    rw [e] at hstep
    have e2 : (((lookahead : ℕ) : ℝ) + (B.blockMost - 1)) * (1 + B.deviceRate) / w.rate
        = ((lookahead : ℕ) : ℝ) * (1 + B.deviceRate) / w.rate
          + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate := by ring
    rw [e2] at hearly
    linarith
  simp only [playable]
  split_ifs with hc
  · rfl
  · exact absurd ⟨hx, hheld⟩ hc

end Unisono.Solutions.FixedDelay
