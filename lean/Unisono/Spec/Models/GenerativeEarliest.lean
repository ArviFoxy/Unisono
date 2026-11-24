/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.EarliestArrival
public import Unisono.Spec.Models.GenerativeDelivery

/-!
# What every solution through the sender needs before it can play

In the generative model, the capture device hands over blocks of `blockSize`
frames and each playback device requests blocks of `blockSize` output
samples. This file states, for every solution whose hosts exchange messages
only with the sender, when an output sample can play a position at the
earliest.

**Theorem** (`Prior.arrival_lt_of_plays`). In every outcome of every
random world of every member, let output sample `k` of a speaker whose host
is not the sender's play the position `x`. The last frame that the resampler
needs for `x` is frame `⌈x + lookahead⌉ - 1`, in capture block
`(⌈x + lookahead⌉ - 1) / blockSize`. A message that the sender sends when
that block is handed over arrives at the speaker's host strictly before the
device requests playback block `k / blockSize`.

The statement uses nothing of the clocks: it holds with wander of the clocks
and with errors of the timestamps. It is the condition under which the
controller of `Unisono.Solutions.Controller` plays the position that is due
(`Unisono.Solutions.Controller.plays_eq_of_margin`), now as a necessary
condition for every solution through the sender and every position.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] {m : GenerativeWorld H R}
  {f : Member H R} {d : Draw H R} {w : World H R}

/-- For a position `x` that is not negative, frame `⌈x + lookahead⌉ - 1` is
less than `lookahead` frames away from `x`: it is the last frame that the
resampler needs. -/
theorem abs_lastNeeded_sub_lt (lookahead : ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    |((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 : ℕ) : ℝ) - x| < ((lookahead : ℕ) : ℝ) := by
  have ha : (1 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := by exact_mod_cast lookahead.pos
  have hy : 0 < x + ((lookahead : ℕ) : ℝ) := by linarith
  have hceil : 1 ≤ ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := Nat.ceil_pos.mpr hy
  have hcast : ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 : ℕ) : ℝ)
      = (⌈x + ((lookahead : ℕ) : ℝ)⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil]
    simp
  have h1 := Nat.ceil_lt_add_one hy.le
  have h2 := Nat.le_ceil (x + ((lookahead : ℕ) : ℝ))
  rw [hcast, abs_lt]
  constructor <;> linarith

omit [DecidableEq H] in
/-- Frame `n` belongs to capture block `n / blockSize`. -/
theorem Builds.mem_block (hB : m.Builds f d w) (n : ℕ) :
    n ∈ w.source.block (n / m.blockSize) := by
  have h1 := Nat.div_mul_le_self n m.blockSize
  have h2 := Nat.lt_div_mul_add m.blockSize_pos (a := n)
  have e : (n / m.blockSize + 1) * m.blockSize
      = n / m.blockSize * m.blockSize + m.blockSize := by ring
  unfold CaptureDevice.block
  rw [List.mem_range'_1, hB.capture_first, hB.capture_first, e]
  generalize n / m.blockSize * m.blockSize = q at h1 h2 ⊢
  omega

omit [DecidableEq H] in
/-- The playback block that holds output sample `k` is block
`k / blockSize`. -/
theorem Builds.block_eq (hB : m.Builds f d w) {r : Fin R} {k b : ℕ}
    (hk : k ∈ (w.speaker r).block b) : b = k / m.blockSize := by
  have e : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
  unfold PlaybackDevice.block at hk
  rw [List.mem_range'_1, hB.speaker_first, hB.speaker_first, e] at hk
  have h2 : k < b * m.blockSize + m.blockSize := by
    have h3 := hk.2
    generalize b * m.blockSize = q at h3 ⊢
    omega
  exact (Nat.div_eq_of_lt_le hk.1 (by rw [e]; exact h2)).symm

/-- **What every solution through the sender needs before it can play**, in
one outcome. Consider a world built from a draw whose least delays are not
negative and whose paused times never decrease, and a solution whose hosts
exchange messages only with the sender. If output sample `k` of a speaker
whose host is not the sender's plays the position `x`, then `x` is not
negative, and a message that the sender sends at the handover of capture
block `(⌈x + lookahead⌉ - 1) / blockSize` arrives at the speaker's host
strictly before the request of playback block `k / blockSize`. -/
theorem Builds.arrival_lt_of_plays (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {k : ℕ} {x : ℝ} (hplay : σ.plays w lookahead r k = some x) :
    0 ≤ x ∧ d.arrival f m.sender (m.host r)
        (w.source.handed ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1) / m.blockSize))
      < (w.speaker r).asked (k / m.blockSize) := by
  have hstar' : σ.IsStar w.sender := by
    rw [hB.sender_eq]
    exact hstar
  have hr' : w.host r ≠ w.sender := by
    rw [hB.host_eq, hB.sender_eq]
    exact hr
  obtain ⟨hx0, b, hkb, hall⟩ := σ.arrival_lt_asked_of_plays w lookahead (A := d.arrival f)
    (fun i j s q => hB.deliver i j s q)
    (fun i j => hB.arrival_mono (hlink i j) (hhost i) (hhost j))
    (fun i j s => le_trans (by linarith [hpos i j]) (hB.le_arrival i j s)) hstar' hr' hplay
  refine ⟨hx0, ?_⟩
  have h1 := hall _ _ (abs_lastNeeded_sub_lt lookahead hx0) (hB.mem_block _)
  rw [hB.sender_eq, hB.host_eq, hB.block_eq hkb] at h1
  exact h1

/-- **What every solution through the sender needs before it can play.** In
every outcome of every random world of every member, consider a solution
whose hosts exchange messages only with the sender. If output sample `k` of
a speaker whose host is not the sender's plays the position `x`, then `x` is
not negative, and a message that the sender sends at the handover of capture
block `(⌈x + lookahead⌉ - 1) / blockSize` arrives at the speaker's host
strictly before the request of playback block `k / blockSize`. -/
theorem Prior.arrival_lt_of_plays {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) (ω : Ω) {r : Fin R}
    (hr : m.host r ≠ m.sender) {k : ℕ} {x : ℝ}
    (hplay : σ.plays (world ω) lookahead r k = some x) :
    0 ≤ x ∧ (D ω).arrival f m.sender (m.host r)
        ((world ω).source.handed ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1) / m.blockSize))
      < ((world ω).speaker r).asked (k / m.blockSize) :=
  (hB ω).arrival_lt_of_plays (fun i j => (hD.leastDelay_pos ω i j).le)
    (fun i j => hD.linkPaused_monotone ω i j) (fun h => hD.hostPaused_monotone ω h) σ hstar
    lookahead hr hplay

end Unisono.Spec.GenerativeWorld
