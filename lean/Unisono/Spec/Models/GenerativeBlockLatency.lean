/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeLeastLatency
public import Unisono.Spec.NewGround

/-!
# The latency of the frames of one playback block, against the room

A solution through the sender can ride out a pause of the link only with the
frames that its host holds beyond the position that it plays: its *room*.
The room is paid for with latency. This file states that trade for one
playback block, in one outcome.

Consider a world whose clocks run at constant rates, with exact timestamps
and with pauses of links and of hosts, a solution whose hosts exchange
messages only with the sender, and a speaker whose host is not the sender's,
whose position advances by at least `s` in every step of continuous
playback. Take a playback block `b` and a capture block `c` such that the
capture block before `c` was handed over earlier than the least delay before
the request of playback block `b + 1`. The room at that request is
`c * blockSize - lookahead` minus the position played last in blocks up to
`b`: only frames of capture blocks before `c` can have arrived by then.

**Theorem** (`ConstantRates.block_lt_latency`). Every frame that a step
inside playback block `b` passes on new ground is played with a latency
above the least latency (`leastLatency`) plus the time in which the capture
device captures as many frames as the room holds, minus

* two periods of the playback device's output samples,
* `blockSize` times the amount by which one period of the playback device
  exceeds the time in which the capture device captures `s` frames, when it
  does: within the block the position may fall behind the capture by that
  much per output sample,
* the time in which the capture device captures `s` frames for each step
  inside the block that is not continuous, and one frame for each missed
  sample counted in the block.

So a large room at the end of a block means that the frames of the block
were played late. The statement holds in one outcome, for every solution
through the sender. It is not yet a bound on the cost.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {plays : ℕ → Option ℝ}

/-- Between two output samples, the steps of continuous playback number at
most the steps. -/
theorem continuousBefore_le_add {k K : ℕ} (h : k ≤ K) :
    continuousBefore plays K ≤ continuousBefore plays k + (K - k) := by
  induction K, h using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    by_cases hc : PlaysContinuously plays K
    · rw [continuousBefore_succ_of hc]
      omega
    · rw [continuousBefore_succ_of_not hc]
      omega

namespace GenerativeWorld

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] {m : GenerativeWorld H R}
  {f : Member H R} {d : Draw H R} {w : World H R}

/-- **The frames of a playback block are played late by the room that is
left after it.** Consider a world whose clocks run at constant rates, with
exact timestamps and with pauses of links and of hosts, a solution whose
hosts exchange messages only with the sender, and a speaker `r` whose host
is not the sender's, whose position advances by at least `s`, with `0 ≤ s`,
in every step of continuous playback. Let `xLast` be the position played
last before playback block `b + 1`, and let `c` be a capture block such that
`c = 0`, or the capture block before `c` was handed over earlier than the
least delay before the request of playback block `b + 1`. Then every frame
that a step between two output samples of playback block `b` passes on new
ground is played with a latency above `leastLatency`, plus the time in which
the capture device captures `c * blockSize - lookahead - xLast` frames,
minus two periods of the playback device, minus `blockSize` times the
positive part of one period of the playback device less the time in which
the capture device captures `s` frames, minus the time in which the capture
device captures `s` frames for each step of the block that is not continuous
and one frame for each missed sample counted in the block. -/
theorem ConstantRates.block_lt_latency (hS : ConstantRates m f d w) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R} (hr : m.host r ≠ m.sender)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {b c : ℕ} {xLast : ℝ}
    (hlast : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) = some xLast)
    (hc : c = 0 ∨ w.source.handed (c - 1)
      < (w.speaker r).asked (b + 1)
        - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    {n : ℕ}
    (hn : n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
      ((b + 1) * m.blockSize - 1)) :
    ∃ l, w.latency (σ.plays w lookahead) r n = some l ∧
      leastLatency m f d lookahead r
          + ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ) - xLast)
            / (m.rate * Real.exp (d.deviceLogRate none))
          - 2 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          - (m.blockSize : ℝ)
            * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
              - s / (m.rate * Real.exp (d.deviceLogRate none))) 0
          - (s * (((m.blockSize : ℝ) - 1)
                - ((continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
                  - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
              + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
            / (m.rate * Real.exp (d.deviceLogRate none))
        < l := by
  have hc0 : 0 < m.rate * Real.exp (d.deviceLogRate none) :=
    mul_pos m.rate_pos (Real.exp_pos _)
  have hρ : 0 < m.rate * Real.exp (d.deviceLogRate (some (m.device r))) :=
    mul_pos m.rate_pos (Real.exp_pos _)
  have hBpos := m.blockSize_pos
  -- The last output sample of the block.
  obtain ⟨K, hK⟩ : ∃ K, K + 1 = (b + 1) * m.blockSize :=
    ⟨(b + 1) * m.blockSize - 1, Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos b) hBpos)⟩
  have hKe : (b + 1) * m.blockSize - 1 = K := by omega
  have hbK : b * m.blockSize + m.blockSize = K + 1 := by
    rw [hK]
    ring
  rw [hKe] at hn ⊢
  rw [← hK] at hlast ⊢
  -- The step that passes the frame.
  obtain ⟨j, haj, hjK, hng, hlo, hhi⟩ := exists_of_mem_newFrames _ _ n hn
  obtain ⟨x, y, hx, hy, h1, h2, h3⟩ := hng
  have hng : NewGround (σ.plays w lookahead r) j := ⟨x, y, hx, hy, h1, h2, h3⟩
  rw [hng.maxPlayed_eq hy] at hhi
  obtain ⟨l, hl, hle⟩ := w.le_latency_of_newGround (σ.plays w lookahead) hng hy hlo hhi
  refine ⟨l, hl, ?_⟩
  -- The position played last advances from the step to the end of the block.
  have hadv := add_le_lastPlayed hslow (lastPlayed_succ_some hy) K (Nat.succ_le_of_lt hjK)
    xLast hlast
  have hcont₁ := continuousBefore_le_add (plays := σ.plays w lookahead r)
    (show b * m.blockSize ≤ j + 1 by omega)
  have hcont₂ := continuousBefore_le_add (plays := σ.plays w lookahead r)
    (show b * m.blockSize ≤ K by omega)
  have hmiss := missedBefore_mono (σ.plays w lookahead r)
    (show b * m.blockSize ≤ j + 1 + 1 by omega)
  have hcont₁' : (continuousBefore (σ.plays w lookahead r) (j + 1) : ℝ)
      ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
        + ((j : ℝ) + 1 - (b * m.blockSize : ℕ)) := by
    have h := hcont₁
    have e : ((j + 1 - b * m.blockSize : ℕ) : ℝ) = (j : ℝ) + 1 - (b * m.blockSize : ℕ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have h' : (continuousBefore (σ.plays w lookahead r) (j + 1) : ℝ)
        ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
          + ((j + 1 - b * m.blockSize : ℕ) : ℝ) := by exact_mod_cast h
    rw [e] at h'
    exact h'
  have hcont₂' : (continuousBefore (σ.plays w lookahead r) K : ℝ)
      ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
        + ((m.blockSize : ℝ) - 1) := by
    have e : ((K - b * m.blockSize : ℕ) : ℝ) = (m.blockSize : ℝ) - 1 := by
      have h4 : K - b * m.blockSize + 1 = m.blockSize := by omega
      have h5 : ((K - b * m.blockSize : ℕ) : ℝ) + 1 = (m.blockSize : ℝ) := by
        exact_mod_cast h4
      linarith
    have h' : (continuousBefore (σ.plays w lookahead r) K : ℝ)
        ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
          + ((K - b * m.blockSize : ℕ) : ℝ) := by exact_mod_cast hcont₂
    rw [e] at h'
    exact h'
  have hmiss' : (missedBefore (σ.plays w lookahead r) (b * m.blockSize) : ℝ)
      ≤ missedBefore (σ.plays w lookahead r) (j + 1 + 1) := by exact_mod_cast hmiss
  -- Sizes within the block.
  have hjR : (j : ℝ) + 1 ≤ K := by exact_mod_cast Nat.succ_le_of_lt hjK
  have hKB : (K : ℝ) + 1 = (b * m.blockSize : ℕ) + (m.blockSize : ℝ) := by
    have : ((b * m.blockSize + m.blockSize : ℕ) : ℝ) = ((K + 1 : ℕ) : ℝ) := by
      rw [hbK]
    push_cast at this ⊢
    linarith
  have hajR : ((b * m.blockSize : ℕ) : ℝ) ≤ j := by exact_mod_cast haj
  -- Times.
  have houtj := hS.out r j
  have houtK := hS.out r (K + 1)
  push_cast at houtK
  have hcapn : w.source.capture n ≤ w.captured y := by
    rw [hS.capture n, hS.captured y]
    have := div_le_div_of_nonneg_right hhi hc0.le
    linarith
  have hcapy := hS.captured y
  have hfloor := hS.leastLatency_lt σ hstar lookahead hr hy
  have houtj1 := hS.out r (j + 1)
  push_cast at houtj1
  -- The drift of the position against the capture within the block.
  have hdrift : ((K : ℝ) - j - 1)
        * (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          - s / (m.rate * Real.exp (d.deviceLogRate none)))
      ≤ (m.blockSize : ℝ)
        * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          - s / (m.rate * Real.exp (d.deviceLogRate none))) 0 := by
    have h0 : 0 ≤ (K : ℝ) - j - 1 := by linarith
    have hB : (K : ℝ) - j - 1 ≤ m.blockSize := by linarith
    calc ((K : ℝ) - j - 1)
          * (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
            - s / (m.rate * Real.exp (d.deviceLogRate none)))
        ≤ ((K : ℝ) - j - 1)
          * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
            - s / (m.rate * Real.exp (d.deviceLogRate none))) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) h0
      _ ≤ (m.blockSize : ℝ)
          * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
            - s / (m.rate * Real.exp (d.deviceLogRate none))) 0 :=
          mul_le_mul_of_nonneg_right hB (le_max_right _ _)
  have hmax : (0 : ℝ) ≤ (m.blockSize : ℝ)
      * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
        - s / (m.rate * Real.exp (d.deviceLogRate none))) 0 :=
    mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  -- What the position played last gives, in time of the capture device.
  have hadv' := div_le_div_of_nonneg_right hadv hc0.le
  have hNC : (0 : ℝ) ≤ s * (((m.blockSize : ℝ) - 1)
      - ((continuousBefore (σ.plays w lookahead r) K : ℝ)
        - continuousBefore (σ.plays w lookahead r) (b * m.blockSize))) :=
    mul_nonneg hs0 (by linarith)
  have hcontStep : s * ((K : ℝ) - j - 1 - (((m.blockSize : ℝ) - 1)
        - ((continuousBefore (σ.plays w lookahead r) K : ℝ)
          - continuousBefore (σ.plays w lookahead r) (b * m.blockSize))))
      ≤ s * ((continuousBefore (σ.plays w lookahead r) K : ℝ)
        - continuousBefore (σ.plays w lookahead r) (j + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hs0
  have hcontStep' := div_le_div_of_nonneg_right hcontStep hc0.le
  have hmissB : (missedBefore (σ.plays w lookahead r) (K + 1) : ℝ)
        - missedBefore (σ.plays w lookahead r) (j + 1 + 1)
      ≤ (missedBefore (σ.plays w lookahead r) (K + 1) : ℝ)
        - missedBefore (σ.plays w lookahead r) (b * m.blockSize) := by linarith
  have hmissB' := div_le_div_of_nonneg_right hmissB hc0.le
  rcases Nat.eq_zero_or_pos c with h0 | hcpos
  · -- No capture block counts: the least latency alone is enough.
    subst h0
    obtain ⟨-, hplayed⟩ := lastPlayed_some hlast
    have hx0 := (hS.builds.arrival_lt_of_plays (fun i j => (hS.delay_pos i j).le)
      hS.linkPaused_monotone hS.hostPaused_monotone σ hstar lookahead hr hplayed).1
    have hla : (0 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := Nat.cast_nonneg _
    have hneg : ((0 : ℕ) : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ) - xLast ≤ 0 := by
      push_cast
      linarith
    have hneg' : (((0 : ℕ) : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ) - xLast)
        / (m.rate * Real.exp (d.deviceLogRate none)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hneg hc0.le
    have hmissnn : (0 : ℝ) ≤ (missedBefore (σ.plays w lookahead r) (K + 1) : ℝ)
        - missedBefore (σ.plays w lookahead r) (b * m.blockSize) := by
      have := missedBefore_mono (σ.plays w lookahead r)
        (show b * m.blockSize ≤ K + 1 by omega)
      have h' : (missedBefore (σ.plays w lookahead r) (b * m.blockSize) : ℝ)
          ≤ missedBefore (σ.plays w lookahead r) (K + 1) := by exact_mod_cast this
      linarith
    have hpen : (0 : ℝ) ≤ (s * (((m.blockSize : ℝ) - 1)
          - ((continuousBefore (σ.plays w lookahead r) K : ℝ)
            - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
        + ((missedBefore (σ.plays w lookahead r) (K + 1) : ℝ)
          - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
        / (m.rate * Real.exp (d.deviceLogRate none)) :=
      div_nonneg (by linarith) hc0.le
    have hper : (0 : ℝ) < 1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) :=
      one_div_pos.mpr hρ
    have e2 : 2 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
        = 2 * (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))) := by ring
    have estep : (w.speaker r).out (j + 1) - (w.speaker r).out j
        = 1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := by
      rw [houtj, houtj1]
      ring
    linarith
  · -- The last frame of the capture block before `c` was captured before the request.
    have hc' : w.source.handed (c - 1)
        < (w.speaker r).asked (b + 1)
          - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r) := by
      rcases hc with hc | hc
      · omega
      · exact hc
    obtain ⟨c', hcc⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have e1 : c - 1 = c' := by omega
    rw [e1, hS.handed c'] at hc'
    have hcR : (c : ℝ) = (c' : ℝ) + 1 := by
      rw [hcc]
      push_cast
      ring
    have hasked := hS.asked r (b + 1)
    rw [hS.builds.speaker_first r (b + 1), ← hK, houtK] at hasked
    rw [hcR]
    unfold leastLatency
    simp only [div_eq_mul_inv] at hc' hasked hadv' hcontStep' hmissB' hdrift houtj houtK hcapy ⊢
    linarith

end GenerativeWorld

end Unisono.Spec
