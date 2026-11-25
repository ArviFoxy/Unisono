/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeRoom
public import Unisono.Spec.BlockCounts

/-!
# The latency of the first blocks of a speaker, as the cost weights it

The latency objective weights the latency of each frame by the time until
the next frame is captured. `Builds.le_sum_min_add_loss` bounds the
latencies of the frames of one playback block without weights. This file
adds the weights and sums over the first `N` playback blocks of one speaker,
in one outcome of any member: the clocks may wander.

* `roomLatency`: the latency that the frames of a playback block have at
  least, as a function of the room before the next block.
* `ofReal_mul_min_le`: the weight of a frame against a reference period
  `p₀`. A weight `pc ≤ p₀` times a latency counted up to the cap is at most
  the latency times the period of the frame, plus the cap times the amount
  by which the period of the frame is shorter than `p₀`. A frame whose
  latency is at the cap may have been captured long before the block, when
  the capture clock ran faster, so its period has no lower bound from the
  clocks near the block.
* `Builds.sum_blocks_le_latency`: the sum over the first `N` playback
  blocks. The losses of the blocks are paid for by missed samples
  (`sum_blocks_losses_le`).

With constant rates and `p₀` the period of the capture device, the term for
shorter periods is zero. The statement holds in one outcome; it is not yet a
bound on expected cost.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open scoped ENNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {Msg : Type} {m : GenerativeWorld H R}
  {f : Member H R} {d : Draw H R} {w : World H R}

/-- The latency that the frames of playback block `b` of speaker `r` have at
least when the room before block `b + 1` is `room`: the least delay from the
sender, plus the time from the request of block `b + 1` to its first output
sample, plus `pc` for each frame of the room and of the lookahead but one,
minus `2 * pr` and `blockSize` times the positive part of `pr - s * pc`.
Here `pc` is at most the time between two frames captured near the block,
`pr` at least the time between two output samples of the block, and `s` the
least advance of the position in a step of continuous playback. -/
def roomLatency (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (lookahead : ℕ+) (r : Fin R) (s pc pr : ℝ) (b : ℕ) (room : ℝ) : ℝ :=
  d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
    + ((w.speaker r).out ((b + 1) * m.blockSize) - (w.speaker r).asked (b + 1))
    + pc * (room + ((lookahead : ℕ) : ℝ) - 1)
    - 2 * pr
    - (m.blockSize : ℝ) * max (pr - s * pc) 0

/-- **The weight of a frame against a reference period.** For a weight `pc`
that is at most the reference period `p₀`, and a frame whose period is
`per ≥ 0`: `pc` times a latency `L` counted up to the cap is at most `L`
times the period of the frame, plus the cap times the amount by which the
period is shorter than `p₀`. -/
theorem ofReal_mul_min_le {pc p₀ per cap : ℝ} (hpc : pc ≤ p₀) (hper : 0 ≤ per) (L : ℝ≥0∞) :
    ENNReal.ofReal pc * min L (ENNReal.ofReal cap)
      ≤ L * ENNReal.ofReal per + ENNReal.ofReal cap * ENNReal.ofReal (p₀ - per) := by
  have h1 : ENNReal.ofReal pc ≤ ENNReal.ofReal per + ENNReal.ofReal (p₀ - per) := by
    rcases le_total per p₀ with h | h
    · rw [← ENNReal.ofReal_add hper (sub_nonneg.mpr h)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · exact (ENNReal.ofReal_le_ofReal (hpc.trans h)).trans le_self_add
  calc ENNReal.ofReal pc * min L (ENNReal.ofReal cap)
      ≤ (ENNReal.ofReal per + ENNReal.ofReal (p₀ - per)) * min L (ENNReal.ofReal cap) :=
        mul_le_mul' h1 le_rfl
    _ = ENNReal.ofReal per * min L (ENNReal.ofReal cap)
        + ENNReal.ofReal (p₀ - per) * min L (ENNReal.ofReal cap) := add_mul _ _ _
    _ ≤ L * ENNReal.ofReal per + ENNReal.ofReal cap * ENNReal.ofReal (p₀ - per) := by
        refine add_le_add ?_ ?_
        · rw [mul_comm]
          exact mul_le_mul' (min_le_left _ _) le_rfl
        · rw [mul_comm]
          exact mul_le_mul' (min_le_right _ _) le_rfl

/-- **The room is not negative once the speaker has played.** In one outcome
of any member, for a solution whose hosts exchange messages only with the
sender and a speaker whose host is not the sender's: if the speaker has
played the source before playback block `b`, the room before block `b` is
not negative. The position played last needs frames of capture blocks whose
messages arrived before the request of an earlier block. -/
theorem Builds.room_nonneg (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {b : ℕ} {xLast : ℝ}
    (hlast : lastPlayed (σ.plays w lookahead r) (b * m.blockSize) = some xLast) :
    0 ≤ room m f d w lookahead (σ.plays w lookahead r) r b := by
  obtain ⟨htr, hplay⟩ := lastPlayed_some hlast
  have hex := hB.exists_le_handed ((w.speaker r).asked b
    - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
  have hc := w.le_handed_blockFrom hex
  have harr := hB.le_arrival m.sender (m.host r) (w.source.handed (w.blockFrom
    ((w.speaker r).asked b - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))))
  have hk : (b * m.blockSize - 1 - trailing (σ.plays w lookahead r) (b * m.blockSize))
      / m.blockSize ≤ b := by
    have h1 : b * m.blockSize - 1 - trailing (σ.plays w lookahead r) (b * m.blockSize)
        < b * m.blockSize := by omega
    exact ((Nat.div_lt_iff_lt_mul m.blockSize_pos).mpr h1).le
  have hle := hB.le_of_plays_before hpos hlink hhost σ hstar lookahead hr
    (c := w.blockFrom ((w.speaker r).asked b
      - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)))
    (β := b) (by linarith) hk hplay
  unfold room
  rw [hlast]
  simp only [Option.getD_some]
  linarith

/-- **The latency of the first playback blocks of a speaker, weighted as the
cost weights it.** In one outcome of any member, for a solution whose hosts
exchange messages only with the sender and a speaker whose host is not the
sender's, whose position is never negative and advances by at least `s > 0`
in every step of continuous playback. For each of the first `N` playback
blocks `b` let `pr b` be at least the time between two output samples of the
block, and `pc b`, with `0 ≤ pc b ≤ p₀`, at most the time between two frames
captured from `Gcap` before the block to the request of the next block. Then
the sum over the blocks of `pc b * s * (blockSize - 1)` times the smaller of
`roomLatency` and `Gcap` is at most the sum of three terms; `roomLatency` is
taken at the room before block `b + 1`, or at zero if that room is
negative, and counts as zero if it is negative. The first is the sum, over the
frames that the steps before output sample `N * blockSize` pass on new
ground, of the latency of the frame times the time until the next frame is
captured, plus `Gcap` times the amount by which that time is shorter than
`p₀`. The second is `p₀ * (1 + s) * Gcap` for each block. The third is a
multiple of the missed samples counted at the output samples up to
`N * blockSize`. -/
theorem Builds.sum_blocks_le_latency (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs : 0 < s)
    (hx0 : ∀ k x, σ.plays w lookahead r k = some x → 0 ≤ x)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {pc pr : ℕ → ℝ} {Gcap p₀ : ℝ} (hcap : 0 ≤ Gcap) (hp₀ : 0 ≤ p₀) (N : ℕ)
    (hpc0 : ∀ b < N, 0 ≤ pc b) (hpcle : ∀ b < N, pc b ≤ p₀)
    (hpr : ∀ b < N, ∀ k, b * m.blockSize ≤ k → k < (b + 1) * m.blockSize →
      (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ pr b)
    (hpc : ∀ b < N, ∀ i, (w.speaker r).out (b * m.blockSize) - Gcap < w.source.capture i →
      w.source.capture (i + 1) ≤ (w.speaker r).asked (b + 1) →
      pc b ≤ w.source.capture (i + 1) - w.source.capture i) :
    ∑ b ∈ Finset.range N, ENNReal.ofReal (pc b * (s * ((m.blockSize : ℝ) - 1)
        * min (max (roomLatency m f d w lookahead r s (pc b) (pr b) b
          (max (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)) 0)) 0) Gcap))
      ≤ ∑ n ∈ newFrames (σ.plays w lookahead r) 0 (N * m.blockSize),
          (w.latencyAt (σ.plays w lookahead) r n
              * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
            + ENNReal.ofReal Gcap
              * ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n)))
        + ENNReal.ofReal (p₀ * ((N : ℝ) * ((1 + s) * Gcap)
            + ((1 + 2 * s) * (2 + 1 / s) * Gcap
                + s * ((m.blockSize : ℝ) - 1) * p₀ * (2 * s + 1))
              * missedBefore (σ.plays w lookahead r) (N * m.blockSize + 1))) := by
  have hs0 : 0 ≤ s := hs.le
  have hB1 : (0 : ℝ) ≤ (m.blockSize : ℝ) - 1 := by
    have h1 : 1 ≤ m.blockSize := m.blockSize_pos
    have h2 : (1 : ℝ) ≤ (m.blockSize : ℝ) := by exact_mod_cast h1
    linarith
  -- The three counts of a block: steps that do not break new ground, steps that are not
  -- continuous, and missed samples.
  obtain ⟨cntA, hcntA⟩ : ∃ cntA : ℕ → ℝ, cntA = fun b => ((m.blockSize : ℝ) - 1)
      - newGroundCount (σ.plays w lookahead r) (b * m.blockSize) ((b + 1) * m.blockSize - 1) :=
    ⟨_, rfl⟩
  obtain ⟨cntC, hcntC⟩ : ∃ cntC : ℕ → ℝ, cntC = fun b => ((m.blockSize : ℝ) - 1)
      - ((continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
        - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)) := ⟨_, rfl⟩
  obtain ⟨cntM, hcntM⟩ : ∃ cntM : ℕ → ℝ, cntM = fun b =>
      (missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
        - missedBefore (σ.plays w lookahead r) (b * m.blockSize) := ⟨_, rfl⟩
  have hle : ∀ b : ℕ, b * m.blockSize ≤ (b + 1) * m.blockSize - 1 := fun b => by
    have e : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
    have := m.blockSize_pos
    omega
  have hsize : ∀ b : ℕ, (((b + 1) * m.blockSize - 1 - b * m.blockSize : ℕ) : ℝ)
      = (m.blockSize : ℝ) - 1 := fun b => by
    have e : (b + 1) * m.blockSize - 1 - b * m.blockSize + 1 = m.blockSize := by
      have e' : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
      have := m.blockSize_pos
      omega
    have e2 : (((b + 1) * m.blockSize - 1 - b * m.blockSize : ℕ) : ℝ) + 1
        = (m.blockSize : ℝ) := by exact_mod_cast e
    linarith
  have hA0 : ∀ b, 0 ≤ cntA b := fun b => by
    rw [hcntA]
    have h := newGroundCount_le (plays := σ.plays w lookahead r) _ (hle b)
    have h' : ((newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
          ((b + 1) * m.blockSize - 1) : ℕ) : ℝ)
        ≤ (((b + 1) * m.blockSize - 1 - b * m.blockSize : ℕ) : ℝ) := by exact_mod_cast h
    rw [hsize b] at h'
    simp only
    linarith
  have hC0 : ∀ b, 0 ≤ cntC b := fun b => by
    rw [hcntC]
    have h := continuousBefore_le_add (plays := σ.plays w lookahead r) (hle b)
    have h' : (continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
        ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
          + (((b + 1) * m.blockSize - 1 - b * m.blockSize : ℕ) : ℝ) := by exact_mod_cast h
    rw [hsize b] at h'
    simp only
    linarith
  have hM0 : ∀ b, 0 ≤ cntM b := fun b => by
    rw [hcntM]
    have h := missedBefore_mono (σ.plays w lookahead r)
      (show b * m.blockSize ≤ (b + 1) * m.blockSize from
        Nat.mul_le_mul_right _ (Nat.le_succ b))
    have h' : (missedBefore (σ.plays w lookahead r) (b * m.blockSize) : ℝ)
        ≤ missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) := by exact_mod_cast h
    simp only
    linarith
  -- The loss of a block, with the reference period in place of the block's own.
  obtain ⟨err, herr⟩ : ∃ err : ℕ → ℝ, err = fun b =>
      ((1 + 2 * s) * cntA b + (1 + s)) * Gcap
        + s * ((m.blockSize : ℝ) - 1) * (p₀ * (s * cntC b + cntM b)) := ⟨_, rfl⟩
  have herr0 : ∀ b, 0 ≤ err b := fun b => by
    rw [herr]
    have h1 : 0 ≤ ((1 + 2 * s) * cntA b + (1 + s)) * Gcap :=
      mul_nonneg (add_nonneg (mul_nonneg (by linarith) (hA0 b)) (by linarith)) hcap
    have h2 : 0 ≤ s * ((m.blockSize : ℝ) - 1) * (p₀ * (s * cntC b + cntM b)) :=
      mul_nonneg (mul_nonneg hs0 hB1)
        (mul_nonneg hp₀ (add_nonneg (mul_nonneg hs0 (hC0 b)) (hM0 b)))
    simp only
    linarith
  -- One block.
  have hblock : ∀ b ∈ Finset.range N,
      ENNReal.ofReal (pc b * (s * ((m.blockSize : ℝ) - 1)
          * min (max (roomLatency m f d w lookahead r s (pc b) (pr b) b
            (max (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)) 0)) 0) Gcap))
        ≤ ∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
              ((b + 1) * m.blockSize - 1),
            (w.latencyAt (σ.plays w lookahead) r n
                * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
              + ENNReal.ofReal Gcap
                * ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n)))
          + ENNReal.ofReal (p₀ * err b) := by
    intro b hb
    have hbN := Finset.mem_range.mp hb
    rcases lt_or_ge (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)) 0
      with hroom | hroom
    · -- Nothing was played before block `b + 1`: the loss of the block covers the bound.
      have hnone : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) = none := by
        cases hl : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) with
        | none => rfl
        | some x =>
          exact absurd (hB.room_nonneg hpos hlink hhost σ hstar lookahead hr hl)
            (not_le.mpr hroom)
      have hall := eq_none_of_lastPlayed_none hnone
      have hcount : newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
          ((b + 1) * m.blockSize - 1) = 0 :=
        newGroundCount_of_none _ _ fun k hk => hall k (by omega)
      have hAb : cntA b = (m.blockSize : ℝ) - 1 := by
        rw [hcntA]
        simp only
        rw [hcount]
        simp
      have hmin : min (max (roomLatency m f d w lookahead r s (pc b) (pr b) b
          (max (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)) 0)) 0) Gcap
          ≤ Gcap := min_le_right _ _
      have hmin0 : 0 ≤ min (max (roomLatency m f d w lookahead r s (pc b) (pr b) b
          (max (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)) 0)) 0) Gcap :=
        le_min (le_max_right _ _) hcap
      have hsB : (0 : ℝ) ≤ s * ((m.blockSize : ℝ) - 1) := mul_nonneg hs0 hB1
      have hT : 0 ≤ s * ((m.blockSize : ℝ) - 1) * (p₀ * (s * cntC b + cntM b)) :=
        mul_nonneg hsB (mul_nonneg hp₀ (add_nonneg (mul_nonneg hs0 (hC0 b)) (hM0 b)))
      have herrge : s * ((m.blockSize : ℝ) - 1) * Gcap ≤ err b := by
        rw [herr]
        simp only
        rw [hAb]
        have h1 : (0 : ℝ) ≤ ((m.blockSize : ℝ) - 1) * Gcap := mul_nonneg hB1 hcap
        have h2 : (0 : ℝ) ≤ s * (((m.blockSize : ℝ) - 1) * Gcap) := mul_nonneg hs0 h1
        have h3 : (0 : ℝ) ≤ (1 + s) * Gcap := mul_nonneg (by linarith) hcap
        have e : ((1 + 2 * s) * ((m.blockSize : ℝ) - 1) + (1 + s)) * Gcap
            = s * ((m.blockSize : ℝ) - 1) * Gcap + (s * (((m.blockSize : ℝ) - 1) * Gcap)
              + ((m.blockSize : ℝ) - 1) * Gcap + (1 + s) * Gcap) := by ring
        rw [e]
        linarith
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_add_self
      exact (mul_le_mul (hpcle b hbN) (mul_le_mul_of_nonneg_left hmin hsB)
        (mul_nonneg hsB hmin0) hp₀).trans (mul_le_mul_of_nonneg_left herrge hp₀)
    rw [max_eq_left hroom]
    have h := hB.le_sum_min_add_loss hpos hlink hhost σ hstar lookahead hr hs0 hslow b
      (hpc0 b hbN) hcap (hpr b hbN) (hpc b hbN)
    have hloc0 : 0 ≤ ((1 + 2 * s) * cntA b + (1 + s)) * Gcap
        + s * ((m.blockSize : ℝ) - 1) * (pc b * (s * cntC b + cntM b)) := by
      have h1 : 0 ≤ ((1 + 2 * s) * cntA b + (1 + s)) * Gcap :=
        mul_nonneg (add_nonneg (mul_nonneg (by linarith) (hA0 b)) (by linarith)) hcap
      have h2 : 0 ≤ s * ((m.blockSize : ℝ) - 1) * (pc b * (s * cntC b + cntM b)) :=
        mul_nonneg (mul_nonneg hs0 hB1)
          (mul_nonneg (hpc0 b hbN) (add_nonneg (mul_nonneg hs0 (hC0 b)) (hM0 b)))
      linarith
    have hlocle : ((1 + 2 * s) * cntA b + (1 + s)) * Gcap
        + s * ((m.blockSize : ℝ) - 1) * (pc b * (s * cntC b + cntM b)) ≤ err b := by
      rw [herr]
      have h1 : pc b * (s * cntC b + cntM b) ≤ p₀ * (s * cntC b + cntM b) :=
        mul_le_mul_of_nonneg_right (hpcle b hbN)
          (add_nonneg (mul_nonneg hs0 (hC0 b)) (hM0 b))
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hs0 hB1)
      simp only
      linarith
    have hprod : pc b * (((1 + 2 * s) * cntA b + (1 + s)) * Gcap
        + s * ((m.blockSize : ℝ) - 1) * (pc b * (s * cntC b + cntM b))) ≤ p₀ * err b :=
      mul_le_mul (hpcle b hbN) hlocle hloc0 hp₀
    rw [hcntA, hcntC, hcntM] at hprod
    rw [ENNReal.ofReal_mul (hpc0 b hbN)]
    calc ENNReal.ofReal (pc b) * ENNReal.ofReal (s * ((m.blockSize : ℝ) - 1)
          * min (max (roomLatency m f d w lookahead r s (pc b) (pr b) b
            (room m f d w lookahead (σ.plays w lookahead r) r (b + 1))) 0) Gcap)
        ≤ ENNReal.ofReal (pc b) * (∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
              ((b + 1) * m.blockSize - 1),
            min (w.latencyAt (σ.plays w lookahead) r n) (ENNReal.ofReal Gcap)
          + ENNReal.ofReal
            (((1 + 2 * s) * ((m.blockSize : ℝ) - 1
                  - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
                      ((b + 1) * m.blockSize - 1))
                + (1 + s)) * Gcap
              + s * ((m.blockSize : ℝ) - 1)
                * (pc b * (s * (((m.blockSize : ℝ) - 1)
                      - ((continuousBefore (σ.plays w lookahead r)
                            ((b + 1) * m.blockSize - 1) : ℝ)
                        - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                    + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                      - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))))) :=
          mul_le_mul' le_rfl h
      _ = ∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
              ((b + 1) * m.blockSize - 1),
            ENNReal.ofReal (pc b)
              * min (w.latencyAt (σ.plays w lookahead) r n) (ENNReal.ofReal Gcap)
          + ENNReal.ofReal (pc b * (((1 + 2 * s) * ((m.blockSize : ℝ) - 1
                  - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
                      ((b + 1) * m.blockSize - 1))
                + (1 + s)) * Gcap
              + s * ((m.blockSize : ℝ) - 1)
                * (pc b * (s * (((m.blockSize : ℝ) - 1)
                      - ((continuousBefore (σ.plays w lookahead r)
                            ((b + 1) * m.blockSize - 1) : ℝ)
                        - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                    + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                      - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))))) := by
          rw [mul_add, Finset.mul_sum, ENNReal.ofReal_mul (hpc0 b hbN)]
      _ ≤ _ := add_le_add
          (Finset.sum_le_sum fun n _ => ofReal_mul_min_le (hpcle b hbN)
            (sub_nonneg.mpr (w.source.capture_strictMono (Nat.lt_succ_self n)).le) _)
          (ENNReal.ofReal_le_ofReal hprod)
  -- The losses of all blocks are paid for by missed samples.
  obtain ⟨hl1, hl2, hl3⟩ := sum_blocks_losses_le (plays := σ.plays w lookahead r) hs hx0 hslow
    m.blockSize_pos N
  have hsumerr : ∑ b ∈ Finset.range N, err b
      ≤ (N : ℝ) * ((1 + s) * Gcap)
        + ((1 + 2 * s) * (2 + 1 / s) * Gcap
            + s * ((m.blockSize : ℝ) - 1) * p₀ * (2 * s + 1))
          * missedBefore (σ.plays w lookahead r) (N * m.blockSize + 1) := by
    have e : ∑ b ∈ Finset.range N, err b
        = (1 + 2 * s) * Gcap * ∑ b ∈ Finset.range N, cntA b + (N : ℝ) * ((1 + s) * Gcap)
          + s * ((m.blockSize : ℝ) - 1) * p₀ * s * ∑ b ∈ Finset.range N, cntC b
          + s * ((m.blockSize : ℝ) - 1) * p₀ * ∑ b ∈ Finset.range N, cntM b := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      have hconst : (N : ℝ) * ((1 + s) * Gcap) = ∑ _b ∈ Finset.range N, (1 + s) * Gcap := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hconst, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [herr]
      ring
    rw [e]
    rw [hcntA] at *
    rw [hcntC] at *
    rw [hcntM] at *
    have hk1 : (0 : ℝ) ≤ (1 + 2 * s) * Gcap := mul_nonneg (by linarith) hcap
    have hk2 : (0 : ℝ) ≤ s * ((m.blockSize : ℝ) - 1) * p₀ * s :=
      mul_nonneg (mul_nonneg (mul_nonneg hs0 hB1) hp₀) hs0
    have hk3 : (0 : ℝ) ≤ s * ((m.blockSize : ℝ) - 1) * p₀ :=
      mul_nonneg (mul_nonneg hs0 hB1) hp₀
    have g1 := mul_le_mul_of_nonneg_left hl1 hk1
    have g2 := mul_le_mul_of_nonneg_left hl2 hk2
    have g3 := mul_le_mul_of_nonneg_left hl3 hk3
    simp only at g1 g2 g3 ⊢
    linarith
  calc ∑ b ∈ Finset.range N, ENNReal.ofReal (pc b * (s * ((m.blockSize : ℝ) - 1)
          * min (max (roomLatency m f d w lookahead r s (pc b) (pr b) b
            (max (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)) 0)) 0) Gcap))
      ≤ ∑ b ∈ Finset.range N,
          (∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
                ((b + 1) * m.blockSize - 1),
              (w.latencyAt (σ.plays w lookahead) r n
                  * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
                + ENNReal.ofReal Gcap
                  * ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n)))
            + ENNReal.ofReal (p₀ * err b)) := Finset.sum_le_sum hblock
    _ = ∑ b ∈ Finset.range N,
          ∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
              ((b + 1) * m.blockSize - 1),
            (w.latencyAt (σ.plays w lookahead) r n
                * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
              + ENNReal.ofReal Gcap
                * ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n)))
        + ENNReal.ofReal (p₀ * ∑ b ∈ Finset.range N, err b) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg fun b _ => mul_nonneg hp₀ (herr0 b)]
    _ ≤ _ := add_le_add
        (sum_blocks_newFrames_le (plays := σ.plays w lookahead r) _ m.blockSize N)
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsumerr hp₀))

/-- **A frame that a step passes on new ground was captured before the
step.** In one outcome of any member, for a solution whose hosts exchange
messages only with the sender and a speaker whose host is not the sender's:
every frame that a step before output sample `K` passes on new ground is
captured before output sample `K` leaves. The step plays a position at or
beyond the frame, which needs a message that the sender sent after the
frame was captured. -/
theorem Builds.capture_lt_out (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {a K n : ℕ}
    (hn : n ∈ newFrames (σ.plays w lookahead r) a K) :
    w.source.capture n < (w.speaker r).out K := by
  obtain ⟨k, -, hkK, hng, -, hhi⟩ := exists_of_mem_newFrames a K n hn
  obtain ⟨x, y, hx, hy, h1, h2, h3⟩ := hng
  have hmax := NewGround.maxPlayed_eq ⟨x, y, hx, hy, h1, h2, h3⟩ hy
  rw [hmax] at hhi
  obtain ⟨-, hlt⟩ := hB.arrival_lt_of_plays hpos hlink hhost σ hstar lookahead hr hy
  have hL : (1 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (lookahead : ℕ) from lookahead.pos)
  have hceil : n + 1 ≤ ⌈y + ((lookahead : ℕ) : ℝ)⌉₊ := by
    have h4 : ((n + 1 : ℕ) : ℝ) ≤ y + ((lookahead : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_le.mp (h4.trans (Nat.le_ceil _))
  obtain ⟨last, hlast⟩ : ∃ last : ℕ, last = ⌈y + ((lookahead : ℕ) : ℝ)⌉₊ - 1 := ⟨_, rfl⟩
  rw [← hlast] at hlt
  have hnlast : n ≤ last := by omega
  have hhanded : w.source.capture n ≤ w.source.handed (last / m.blockSize) := by
    rw [hB.capture_handed, hB.capture_first]
    refine w.source.capture_strictMono.monotone ?_
    have h5 := Nat.lt_div_mul_add m.blockSize_pos (a := last)
    have e : (last / m.blockSize + 1) * m.blockSize
        = last / m.blockSize * m.blockSize + m.blockSize := by ring
    rw [e]
    generalize last / m.blockSize * m.blockSize = q at h5 ⊢
    omega
  have harr := hB.le_arrival m.sender (m.host r) (w.source.handed (last / m.blockSize))
  have hδ := hpos m.sender (m.host r)
  have hask := (w.speaker r).asked_before ((k + 1) / m.blockSize)
  have hout : (w.speaker r).out ((w.speaker r).first ((k + 1) / m.blockSize))
      ≤ (w.speaker r).out K := by
    refine (w.speaker r).out_strictMono.monotone ?_
    rw [hB.speaker_first]
    have h6 := Nat.div_mul_le_self (k + 1) m.blockSize
    generalize (k + 1) / m.blockSize * m.blockSize = q at h6 ⊢
    omega
  linarith

end Unisono.Spec.GenerativeWorld
