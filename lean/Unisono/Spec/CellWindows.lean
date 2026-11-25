/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.BlockCounts

/-!
# The playback blocks that a pause in a short period can stall

True time from zero on is cut into cells of length `ℓ`: cell `j` is the
period from `j * ℓ` to `(j + 1) * ℓ`. A speaker requests its playback blocks
at the true times `asked b`, which increase with `b`. A pause of the link to
the speaker's host that begins in cell `j` delays messages that arrive from
`(j + 1) * ℓ + δ` on, where `δ` is the least delay of the link. This file is
the bookkeeping that pairs cells with playback blocks. Nothing in it is
random.

* `firstFrom asked T`: the first playback block requested at or after `T`.
* `windowCount`: how many playback blocks the paused time `x` that begins in
  cell `j` can stall: the blocks from the first one requested at or after
  `(j + 1) * ℓ + δ` that are requested no later than
  `j * ℓ + δ + min x Xmax`, at most `Nbar` of them. The caps `Xmax` and
  `Nbar` keep the windows short.
* `cellSamples`: the output samples of those blocks.
* `disjoint_cellSamples`, `sum_cellSamples_le`: the windows of two cells do
  not overlap when no paused time begins in the cells before the later one
  that are within `m` cells of it, and `Xmax ≤ (m + 1) * ℓ`. So a quantity
  summed over the windows of such cells is at most its sum over all output
  samples.
* `card_mul_le_of_firstFrom`: the cells whose windows start at playback
  block `b`, and that begin after block `b - 1` could notice them, take no
  more time together than the time between the two requests.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal

/-- The first number `b` with `T ≤ asked b`; zero if there is none. For the
true times `asked b` at which a speaker requests its playback blocks: the
first block that is requested at or after `T`. -/
def firstFrom (asked : ℕ → ℝ) (T : ℝ) : ℕ := by
  classical
  exact if h : ∃ b, T ≤ asked b then Nat.find h else 0

theorem le_asked_firstFrom {asked : ℕ → ℝ} {T : ℝ} (h : ∃ b, T ≤ asked b) :
    T ≤ asked (firstFrom asked T) := by
  classical
  unfold firstFrom
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem asked_lt_of_lt_firstFrom {asked : ℕ → ℝ} {T : ℝ} (h : ∃ b, T ≤ asked b) {b : ℕ}
    (hb : b < firstFrom asked T) : asked b < T := by
  classical
  unfold firstFrom at hb
  rw [dite_eq_left h] at hb
  exact not_le.mp (Nat.find_min h hb)

/-- How many playback blocks the paused time `x` that begins in cell `j` can
stall: the largest `n ≤ Nbar` such that the `n`-th block, counted from the
first block requested at or after `(j + 1) * ℓ + δ`, is requested no later
than `j * ℓ + δ + min x Xmax`; zero if there is no such block. -/
def windowCount (asked : ℕ → ℝ) (ℓ δ Xmax : ℝ) (Nbar j : ℕ) (x : ℝ) : ℕ := by
  classical
  exact Nat.findGreatest (fun n => n = 0 ∨
    asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + n - 1)
      ≤ (j : ℝ) * ℓ + δ + min x Xmax) Nbar

theorem windowCount_le (asked : ℕ → ℝ) (ℓ δ Xmax : ℝ) (Nbar j : ℕ) (x : ℝ) :
    windowCount asked ℓ δ Xmax Nbar j x ≤ Nbar := by
  classical
  unfold windowCount
  exact Nat.findGreatest_le _

/-- The last block of a window that is not empty is requested no later than
`j * ℓ + δ + min x Xmax`. -/
theorem asked_le_of_windowCount_pos {asked : ℕ → ℝ} {ℓ δ Xmax : ℝ} {Nbar j : ℕ} {x : ℝ}
    (h : 0 < windowCount asked ℓ δ Xmax Nbar j x) :
    asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + windowCount asked ℓ δ Xmax Nbar j x - 1)
      ≤ (j : ℝ) * ℓ + δ + min x Xmax := by
  classical
  unfold windowCount at h ⊢
  have hspec := Nat.findGreatest_spec (P := fun n => n = 0 ∨
    asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + n - 1)
      ≤ (j : ℝ) * ℓ + δ + min x Xmax) (Nat.zero_le Nbar) (Or.inl rfl)
  rcases hspec with h0 | h1
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp h)
  · exact h1

/-- More paused time stalls no fewer blocks. -/
theorem windowCount_mono (asked : ℕ → ℝ) (ℓ δ Xmax : ℝ) (Nbar j : ℕ) {x y : ℝ}
    (hxy : x ≤ y) :
    windowCount asked ℓ δ Xmax Nbar j x ≤ windowCount asked ℓ δ Xmax Nbar j y := by
  classical
  unfold windowCount
  refine Nat.findGreatest_mono_left (fun n hn => hn.imp id fun h => ?_) Nbar
  have hmin := min_le_min_right Xmax hxy
  linarith

/-- A window that is not empty needs paused time of at least the length of
the cell. -/
theorem le_min_of_windowCount_pos {asked : ℕ → ℝ} (hmono : StrictMono asked)
    {ℓ δ Xmax : ℝ} {Nbar j : ℕ} {x : ℝ} (hex : ∃ b, ((j : ℝ) + 1) * ℓ + δ ≤ asked b)
    (h : 0 < windowCount asked ℓ δ Xmax Nbar j x) : ℓ ≤ min x Xmax := by
  have h1 := asked_le_of_windowCount_pos h
  have h2 := le_asked_firstFrom hex
  have h3 : asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ))
      ≤ asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
        + windowCount asked ℓ δ Xmax Nbar j x - 1) := hmono.monotone (by omega)
  linarith

/-- The output samples of the playback blocks that the paused time `x` that
begins in cell `j` can stall, for playback blocks of `B` output samples. -/
def cellSamples (asked : ℕ → ℝ) (ℓ δ Xmax : ℝ) (Nbar B j : ℕ) (x : ℝ) : Finset ℕ :=
  Finset.Ico (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) * B)
    ((firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + windowCount asked ℓ δ Xmax Nbar j x) * B)

/-- **The windows of two cells do not overlap** when no paused time begins
in the cells before the later one that are within `m` cells of it, and
`Xmax ≤ (m + 1) * ℓ`. The paused time `I i` begins in cell `i`. -/
theorem disjoint_cellSamples {asked : ℕ → ℝ} (hmono : StrictMono asked) {ℓ δ Xmax : ℝ}
    (hℓ : 0 < ℓ) {m : ℕ} (hX : Xmax ≤ ((m : ℝ) + 1) * ℓ) {Nbar B : ℕ} (hB : 0 < B)
    (hex : ∀ T, ∃ b, T ≤ asked b) {I : ℕ → ℝ} {j j' : ℕ} (hjj' : j < j')
    (hclear : ∀ i, i < j' → j' ≤ i + m → I i ≤ 0) :
    Disjoint (cellSamples asked ℓ δ Xmax Nbar B j (I j))
      (cellSamples asked ℓ δ Xmax Nbar B j' (I j')) := by
  refine Finset.disjoint_left.mpr fun k hk hk' => ?_
  unfold cellSamples at hk hk'
  rw [Finset.mem_Ico] at hk hk'
  have hb2 : k / B < firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
      + windowCount asked ℓ δ Xmax Nbar j (I j) := (Nat.div_lt_iff_lt_mul hB).mpr hk.2
  have hb1 : firstFrom asked (((j : ℝ) + 1) * ℓ + δ) ≤ k / B :=
    (Nat.le_div_iff_mul_le hB).mpr hk.1
  have hb1' : firstFrom asked (((j' : ℝ) + 1) * ℓ + δ) ≤ k / B :=
    (Nat.le_div_iff_mul_le hB).mpr hk'.1
  have hnpos : 0 < windowCount asked ℓ δ Xmax Nbar j (I j) := by omega
  have h1 := asked_le_of_windowCount_pos hnpos
  have h2 : asked (k / B) ≤ asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
      + windowCount asked ℓ δ Xmax Nbar j (I j) - 1) := hmono.monotone (by omega)
  have h3 : asked (firstFrom asked (((j' : ℝ) + 1) * ℓ + δ)) ≤ asked (k / B) :=
    hmono.monotone hb1'
  have h4 := le_asked_firstFrom (hex (((j' : ℝ) + 1) * ℓ + δ))
  have hmin : min (I j) Xmax ≤ Xmax := min_le_right _ _
  have hreal : ((j' : ℝ) + 1) * ℓ ≤ ((j : ℝ) + m + 1) * ℓ := by linarith
  have hjm : j' ≤ j + m := by
    have h5 : (j' : ℝ) + 1 ≤ (j : ℝ) + m + 1 := le_of_mul_le_mul_right hreal hℓ
    have h6 : ((j' : ℕ) : ℝ) ≤ ((j + m : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h6
  have hI : I j ≤ 0 := hclear j hjj' hjm
  have hle := le_min_of_windowCount_pos hmono (hex (((j : ℝ) + 1) * ℓ + δ)) hnpos
  have hminl : min (I j) Xmax ≤ I j := min_le_left _ _
  linarith

/-- **A quantity summed over the windows of cells that do not overlap is at
most its sum over all output samples.** Let `J` be a finite set of cells
such that no paused time begins in the cells before a cell of `J` that are
within `m` cells of it, with `Xmax ≤ (m + 1) * ℓ`, and such that the window
of every cell of `J` ends by playback block `N`. Then the sum over the cells
of `J` of the sum of `g` over the output samples of the window is at most
the sum of `g` over the output samples before `N * B`. -/
theorem sum_cellSamples_le {asked : ℕ → ℝ} (hmono : StrictMono asked) {ℓ δ Xmax : ℝ}
    (hℓ : 0 < ℓ) {m : ℕ} (hX : Xmax ≤ ((m : ℝ) + 1) * ℓ) {Nbar B : ℕ} (hB : 0 < B)
    (hex : ∀ T, ∃ b, T ≤ asked b) {I : ℕ → ℝ} (g : ℕ → ℝ≥0∞) (J : Finset ℕ) {N : ℕ}
    (hclear : ∀ j ∈ J, ∀ i, i < j → j ≤ i + m → I i ≤ 0)
    (hN : ∀ j ∈ J, firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + Nbar ≤ N) :
    ∑ j ∈ J, ∑ k ∈ cellSamples asked ℓ δ Xmax Nbar B j (I j), g k
      ≤ ∑ k ∈ Finset.range (N * B), g k := by
  have hdisj : (J : Set ℕ).PairwiseDisjoint
      (fun j => cellSamples asked ℓ δ Xmax Nbar B j (I j)) := by
    intro j hj j' hj' hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact disjoint_cellSamples hmono hℓ hX hB hex h (hclear j' hj')
    · exact (disjoint_cellSamples hmono hℓ hX hB hex h (hclear j hj)).symm
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_le_sum_of_subset fun k hk => ?_
  rw [Finset.mem_biUnion] at hk
  obtain ⟨j, hj, hkj⟩ := hk
  unfold cellSamples at hkj
  rw [Finset.mem_Ico] at hkj
  rw [Finset.mem_range]
  have h1 := windowCount_le asked ℓ δ Xmax Nbar j (I j)
  have h2 := hN j hj
  exact lt_of_lt_of_le hkj.2 (Nat.mul_le_mul_right B (by omega))

/-- **The cells whose windows start at one playback block take no more time
together than the time between two requests.** Let `J` be a finite set of
cells whose windows start at playback block `b` and that begin, shifted by
`δ`, after the request of block `b - 1`. Their number times the length of a
cell is at most the time from the request of block `b - 1` to the request of
block `b`. -/
theorem card_mul_le_of_firstFrom {asked : ℕ → ℝ} (hmono : StrictMono asked)
    (hex : ∀ T, ∃ b, T ≤ asked b) {ℓ δ : ℝ} (hℓ : 0 < ℓ) {b : ℕ} (J : Finset ℕ)
    (hJ : ∀ j ∈ J, firstFrom asked (((j : ℝ) + 1) * ℓ + δ) = b
      ∧ asked (b - 1) < (j : ℝ) * ℓ + δ) :
    (J.card : ℝ) * ℓ ≤ asked b - asked (b - 1) := by
  rcases J.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact sub_nonneg.mpr (hmono.monotone (Nat.sub_le b 1))
  · have hlo := hJ (J.min' hne) (J.min'_mem hne)
    have hhi := hJ (J.max' hne) (J.max'_mem hne)
    have hhi' := le_asked_firstFrom (hex ((((J.max' hne : ℕ) : ℝ) + 1) * ℓ + δ))
    rw [hhi.1] at hhi'
    have hsub : J ⊆ Finset.Icc (J.min' hne) (J.max' hne) := fun j hj =>
      Finset.mem_Icc.mpr ⟨J.min'_le j hj, J.le_max' j hj⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hmm : J.min' hne ≤ J.max' hne := J.min'_le _ (J.max'_mem hne)
    have hcard' : (J.card : ℝ) ≤ ((J.max' hne : ℕ) : ℝ) + 1 - ((J.min' hne : ℕ) : ℝ) := by
      have h1 : ((J.card : ℕ) : ℝ) ≤ ((J.max' hne + 1 - J.min' hne : ℕ) : ℝ) := by
        exact_mod_cast hcard
      rw [Nat.cast_sub (by omega)] at h1
      push_cast at h1
      exact h1
    have hmul := mul_le_mul_of_nonneg_right hcard' hℓ.le
    linarith

end Unisono.Spec
