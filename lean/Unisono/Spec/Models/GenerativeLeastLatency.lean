/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeEarliest
public import Unisono.Spec.Models.GenerativeRates

/-!
# The least latency of a frame for a solution through the sender

In a world whose clocks run at constant rates, with exact timestamps and
with pauses of links and none of hosts, consider a solution whose hosts exchange
messages only with the sender, and a speaker whose host is not the sender's.
The speaker cannot play a position before three things have happened: the
capture device has captured the last frame that the resampler needs, the
message of that frame's block has taken at least the least delay of the
direction, and the playback device has requested the block of the output
sample, which it does a lead before the block's first output sample leaves.

`leastLatency` is the sum of those three times for a draw: the least delay
from the sender to the speaker's host, the request lead in true time, and
the time in which the capture device captures `lookahead - 1` frames.

* `ConstantRates.leastLatency_lt`: every position that the speaker
  plays leaves more than `leastLatency` after the sound at that position was
  captured.
* `ConstantRates.lt_latency`: every frame that the speaker
  plays has a latency above `leastLatency` minus the time between two output
  samples.

Both hold in one outcome, for every solution through the sender, whatever
pauses occur. They say nothing about the frames that a speaker does not
play, which cost missed samples and no latency.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] {m : GenerativeWorld H R}
  {f : Member H R} {d : Draw H R} {w : World H R}

/-- The least latency of speaker `r` for a solution through the sender, for
the draw `d` and a resampler lookahead of `lookahead` frames: the least
delay from the sender to the speaker's host, plus the request lead in true
time, plus the time in which the capture device captures `lookahead - 1`
frames. -/
def leastLatency (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (lookahead : ℕ+)
    (r : Fin R) : ℝ :=
  d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
    + m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
    + (((lookahead : ℕ) : ℝ) - 1) / (m.rate * Real.exp (d.deviceLogRate none))

/-- **Every position is played later than the least latency after its
capture.** Consider a world whose clocks run at constant rates, with exact
timestamps and with pauses of links and none of hosts, a solution whose hosts
exchange messages only with the sender, and a speaker whose host is not the
sender's. If output sample `k` plays the position `x`, it leaves more than
`leastLatency` after the sound at `x` was captured. -/
theorem ConstantRates.leastLatency_lt (hS : ConstantRates m f d w)
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {k : ℕ} {x : ℝ} (hplay : σ.plays w lookahead r k = some x) :
    leastLatency m f d lookahead r < (w.speaker r).out k - w.captured x := by
  obtain ⟨hx0, hlt⟩ := hS.builds.arrival_lt_of_plays (fun i j => (hS.delay_pos i j).le)
    hS.linkPaused_monotone hS.hostPaused_mono σ hstar lookahead hr hplay
  have hc : 0 < m.rate * Real.exp (d.deviceLogRate none) :=
    mul_pos m.rate_pos (Real.exp_pos _)
  have hla : (1 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := by
    have h1 : 1 ≤ (lookahead : ℕ) := lookahead.pos
    exact_mod_cast h1
  -- The last frame that the resampler needs, and its capture block.
  have hpos : 0 < ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := Nat.ceil_pos.mpr (by linarith)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N + 1 = ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ :=
    ⟨⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1, Nat.sub_add_cancel hpos⟩
  have hNsub : ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 = N := by omega
  rw [hNsub] at hlt
  have hceil : x + ((lookahead : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
    have h3 := Nat.le_ceil (x + ((lookahead : ℕ) : ℝ))
    rw [← hN] at h3
    push_cast at h3
    exact h3
  have hblock : (N : ℝ) + 1 ≤ (((N / m.blockSize : ℕ) : ℝ) + 1) * m.blockSize := by
    have h1 := Nat.lt_div_mul_add (a := N) m.blockSize_pos
    have e : (N / m.blockSize + 1) * m.blockSize
        = N / m.blockSize * m.blockSize + m.blockSize := by ring
    have h2 : N + 1 ≤ (N / m.blockSize + 1) * m.blockSize := by
      rw [e]
      omega
    exact_mod_cast h2
  have hhanded := hS.handed (N / m.blockSize)
  have harr := hS.builds.le_arrival m.sender (m.host r) (w.source.handed (N / m.blockSize))
  have hasked := hS.asked r (k / m.blockSize)
  have hout : (w.speaker r).out ((w.speaker r).first (k / m.blockSize))
      ≤ (w.speaker r).out k :=
    (w.speaker r).out_strictMono.monotone (by
      rw [hS.builds.speaker_first]
      exact Nat.div_mul_le_self k m.blockSize)
  have h6 : (x + ((lookahead : ℕ) : ℝ) - 1) / (m.rate * Real.exp (d.deviceLogRate none))
      ≤ ((((N / m.blockSize : ℕ) : ℝ) + 1) * m.blockSize - 1)
        / (m.rate * Real.exp (d.deviceLogRate none)) :=
    div_le_div_of_nonneg_right (by linarith) hc.le
  have e7 : (x + ((lookahead : ℕ) : ℝ) - 1) / (m.rate * Real.exp (d.deviceLogRate none))
      = x / (m.rate * Real.exp (d.deviceLogRate none))
        + (((lookahead : ℕ) : ℝ) - 1) / (m.rate * Real.exp (d.deviceLogRate none)) := by
    ring
  rw [hS.captured]
  unfold leastLatency
  linarith

/-- **Every frame that is played has a latency above the least latency**,
up to the time between two output samples. In the setting of
`ConstantRates.leastLatency_lt`, a frame that the speaker plays has
a latency above `leastLatency` minus the time between two output samples of
the speaker's playback device. -/
theorem ConstantRates.lt_latency (hS : ConstantRates m f d w)
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {n : ℕ} {l : ℝ}
    (hl : w.latency (σ.plays w lookahead) r n = some l) :
    leastLatency m f d lookahead r
        - 1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) < l := by
  classical
  unfold World.latency World.playTime Spec.playTime at hl
  split at hl
  · rename_i hex
    obtain ⟨x, y, hx, hy, hxy, hyx, hxn, hny⟩ := Nat.find_spec hex
    simp only [hx, hy, Option.map_some, Option.some.injEq] at hl
    have hfloor := hS.leastLatency_lt σ hstar lookahead hr hy
    have hc : 0 < m.rate * Real.exp (d.deviceLogRate none) :=
      mul_pos m.rate_pos (Real.exp_pos _)
    have hρ : 0 < m.rate * Real.exp (d.deviceLogRate (some (m.device r))) :=
      mul_pos m.rate_pos (Real.exp_pos _)
    have hstep : (w.speaker r).out (Nat.find hex + 1) - (w.speaker r).out (Nat.find hex)
        = 1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := by
      rw [hS.out r (Nat.find hex), hS.out r (Nat.find hex + 1)]
      push_cast
      ring
    have hfrac : 0 ≤ ((n : ℝ) - x) / (y - x)
        * ((w.speaker r).out (Nat.find hex + 1) - (w.speaker r).out (Nat.find hex)) := by
      rw [hstep]
      exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (one_div_pos.mpr hρ).le
    have hcap : w.source.capture n ≤ w.captured y := by
      rw [hS.capture n, hS.captured y]
      have := div_le_div_of_nonneg_right hny hc.le
      linarith
    rw [← hl]
    linarith
  · simp at hl

end Unisono.Spec.GenerativeWorld
