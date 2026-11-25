/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeRoom
public import Unisono.Spec.CellWindows

/-!
# What a pause that begins in a cell costs

True time is cut into cells of length `ℓ` (`Unisono.Spec.windowCount`,
`cellSamples`). This file states `Builds.stall_le_room` for one cell, in one
outcome of any member of the generative model.

* `Builds.exists_le_asked`: a speaker requests playback blocks without end.
* `Builds.cell_stall_le`: take the world with the paused time of the link
  from the sender to the host of a speaker that begins in cell `j`, and the
  world without it. If no playback block is requested between `j * ℓ` and
  `(j + 1) * ℓ`, each plus the least delay, then the missed samples and `s`
  times the discontinuities counted at the output samples of the window of
  the cell, in the world with the paused time, are at least `s` for each of
  those output samples, minus the room before the first block of the window
  in the world without it, and minus `s`.

The room is the room of the world without the paused time of the cell. That
world does not depend on what the link pauses within the cell, which is what
a bound on expected cost will use. No such bound is proved here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} {Msg : Type} {m : GenerativeWorld H R} {f : Member H R}
  {d d' : Draw H R} {w : World H R}

/-- **A speaker requests playback blocks without end**: for every true time
there is a playback block that is requested at or after it. -/
theorem Builds.exists_le_asked (hB : m.Builds f d w) (r : Fin R) (T : Time) :
    ∃ b, T ≤ (w.speaker r).asked b := by
  obtain ⟨dc, hdc⟩ := hB.deviceClock (some (m.device r))
  obtain ⟨n, hn⟩ := exists_nat_gt
    ((dc.read T - dc.read ((w.speaker r).out 0) + m.lead) * m.rate)
  refine ⟨n, ?_⟩
  by_contra hlt
  have h1 := dc.strictMono.monotone (not_le.mp hlt).le
  have h2 := hB.speaker_asked r n
  have h3 := hB.speaker_out r ((w.speaker r).first n)
  rw [← hdc ((w.speaker r).out ((w.speaker r).first n)), ← hdc ((w.speaker r).asked n)] at h2
  rw [← hdc ((w.speaker r).out ((w.speaker r).first n)), ← hdc ((w.speaker r).out 0)] at h3
  have e : (w.speaker r).first n = n * m.blockSize := hB.speaker_first r n
  have h4 : (n : ℝ) ≤ (((w.speaker r).first n : ℕ) : ℝ) := by
    rw [e]
    exact_mod_cast Nat.le_mul_of_pos_right n m.blockSize_pos
  have h5 : (n : ℝ) / m.rate ≤ (((w.speaker r).first n : ℕ) : ℝ) / m.rate :=
    div_le_div_of_nonneg_right h4 m.rate_pos.le
  have h6 := (lt_div_iff₀ m.rate_pos).mpr hn
  linarith

variable [DecidableEq H]

/-- **What the paused time that begins in a cell costs, against the room of
the world without it.** Take two draws that differ by pauses of the link
from the sender to the host of speaker `r` from `j * ℓ` on: `d` without and
`d'` with the paused time `I` that begins in cell `j`, from `j * ℓ` to
`(j + 1) * ℓ`. Let the least delays of `d'` be not negative and its paused
times never decrease, and let `δ` be the least delay from the sender to the
host. Consider a solution whose hosts exchange messages only with the
sender, whose position at speaker `r`, in the world with the paused time,
advances by at least `s` in every step of continuous playback, with
`0 ≤ s ≤ 1`. Suppose that every playback block before the first one
requested at or after `(j + 1) * ℓ + δ` is requested before `j * ℓ + δ`.
Then `s` for each output sample of the window of the cell, minus the room
before the first block of the window in the world without the paused time
(zero if negative), minus `s`, is at most the missed samples plus `s` times
the discontinuities counted at the output samples of the window in the
world with the paused time. -/
theorem Builds.cell_stall_le {w' : World H R} (hB : m.Builds f d w) (hB' : m.Builds f d' w')
    {r : Fin R} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {j : ℕ}
    (h : d.SameExceptLinkFrom d' m.sender (m.host r) ((j : ℝ) * ℓ))
    (hpos : ∀ i j, 0 ≤ d'.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d'.linkPaused i j)) (hhost : ∀ x, Monotone (d'.hostPaused x))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+)
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays w' lookahead r k = some x →
      σ.plays w' lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {Xmax : ℝ} {Nbar : ℕ} {δ I : ℝ}
    (hδ : δ = d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    (hI : I = d'.linkPaused m.sender (m.host r) (((j : ℝ) + 1) * ℓ)
      - d'.linkPaused m.sender (m.host r) ((j : ℝ) * ℓ))
    (husable : ∀ b' < firstFrom (w.speaker r).asked (((j : ℝ) + 1) * ℓ + δ),
      (w.speaker r).asked b' < (j : ℝ) * ℓ + δ) :
    s * ((windowCount (w.speaker r).asked ℓ δ Xmax Nbar j I : ℝ) * m.blockSize)
        - max (room m f d w lookahead (σ.plays w lookahead r) r
          (firstFrom (w.speaker r).asked (((j : ℝ) + 1) * ℓ + δ))) 0 - s
      ≤ ∑ k ∈ cellSamples (w.speaker r).asked ℓ δ Xmax Nbar m.blockSize j I,
          ((missedAt (σ.plays w' lookahead r) k : ℝ)
            + s * (discontinuityAt (σ.plays w' lookahead r) k : ℝ)) := by
  have hsum0 : 0 ≤ ∑ k ∈ cellSamples (w.speaker r).asked ℓ δ Xmax Nbar m.blockSize j I,
      ((missedAt (σ.plays w' lookahead r) k : ℝ)
        + s * (discontinuityAt (σ.plays w' lookahead r) k : ℝ)) :=
    Finset.sum_nonneg fun k _ =>
      add_nonneg (Nat.cast_nonneg _) (mul_nonneg hs0 (Nat.cast_nonneg _))
  have hmax0 := le_max_right (room m f d w lookahead (σ.plays w lookahead r) r
    (firstFrom (w.speaker r).asked (((j : ℝ) + 1) * ℓ + δ))) 0
  rcases Nat.eq_zero_or_pos (windowCount (w.speaker r).asked ℓ δ Xmax Nbar j I) with hn0 | hnpos
  · rw [hn0]
    simp only [Nat.cast_zero, zero_mul, mul_zero]
    linarith
  · have hex := hB.exists_le_asked r (((j : ℝ) + 1) * ℓ + δ)
    have hθb := le_asked_firstFrom hex
    have hlast := asked_le_of_windowCount_pos hnpos
    have hmin : min I Xmax ≤ I := min_le_left _ _
    obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : ℕ, β₀ = firstFrom (w.speaker r).asked (((j : ℝ) + 1) * ℓ + δ) :=
      ⟨_, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = windowCount (w.speaker r).asked ℓ δ Xmax Nbar j I :=
      ⟨_, rfl⟩
    have hcs : cellSamples (w.speaker r).asked ℓ δ Xmax Nbar m.blockSize j I
        = Finset.Ico (β₀ * m.blockSize) ((β₀ + n) * m.blockSize) := by
      unfold cellSamples
      rw [← hβ₀, ← hn]
    rw [← hβ₀] at husable hθb hlast hmax0 ⊢
    rw [← hn] at hlast hnpos ⊢
    rw [hcs] at hsum0 ⊢
    have hBpos := m.blockSize_pos
    have hmul : (β₀ + n) * m.blockSize = β₀ * m.blockSize + n * m.blockSize := Nat.add_mul _ _ _
    have hnB : m.blockSize ≤ n * m.blockSize := Nat.le_mul_of_pos_left _ hnpos
    have hK1 : (β₀ + n) * m.blockSize - 1 + 1 = (β₀ + n) * m.blockSize := by omega
    have hK : β₀ * m.blockSize ≤ (β₀ + n) * m.blockSize - 1 := by omega
    have hKβ : ((β₀ + n) * m.blockSize - 1) / m.blockSize ≤ β₀ + n - 1 := by
      have h1 : ((β₀ + n) * m.blockSize - 1) / m.blockSize < β₀ + n :=
        (Nat.div_lt_iff_lt_mul hBpos).mpr (by omega)
      omega
    have hθ : (j : ℝ) * ℓ ≤ ((j : ℝ) + 1) * ℓ := by nlinarith
    rw [hδ] at husable hθb hlast
    rw [hI] at hlast hmin
    have key := hB.stall_le_room hB' h hpos hlink hhost σ hstar lookahead hr hs0 hs1 hslow hθ
      hK hKβ husable hθb (by linarith)
    rw [hK1] at key
    have hKr : ((((β₀ + n) * m.blockSize - 1 : ℕ)) : ℝ) + 1
        = (((β₀ + n) * m.blockSize : ℕ) : ℝ) := by exact_mod_cast hK1
    have hlhs : s * ((((β₀ + n) * m.blockSize - 1 : ℕ) : ℝ) + 1 - ((β₀ * m.blockSize : ℕ) : ℝ))
        = s * ((n : ℝ) * m.blockSize) := by
      rw [hKr]
      push_cast
      ring
    rw [hlhs] at key
    have hdisc : ∑ k ∈ Finset.Ico (β₀ * m.blockSize) ((β₀ + n) * m.blockSize - 1),
          (discontinuityAt (σ.plays w' lookahead r) k : ℝ)
        ≤ ∑ k ∈ Finset.Ico (β₀ * m.blockSize) ((β₀ + n) * m.blockSize),
          (discontinuityAt (σ.plays w' lookahead r) k : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl (Nat.sub_le _ _)) fun _ _ _ => Nat.cast_nonneg _
    have hdisc' := mul_le_mul_of_nonneg_left hdisc hs0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith

end Unisono.Spec.GenerativeWorld
