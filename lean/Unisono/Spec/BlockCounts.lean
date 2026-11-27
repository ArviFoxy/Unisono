/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.NewGround

/-!
# What the blocks of a playback lose, summed over the blocks

A bound for one playback block of `B` output samples has losses: the steps
between two output samples of the block that do not break new ground, those
that are not continuous, and the missed samples counted in the block
(`Unisono.Spec.NewGround`). This file sums each of the three over the first
`N` blocks and bounds the sums by the missed samples counted up to output
sample `N * B`, for the playback of one speaker whose positions are at least
zero and advance by at least `s > 0` in every step of continuous playback.

**Theorem** (`sum_blocks_losses_le`). Over the first `N` blocks,

* the steps inside the blocks that do not break new ground number at most
  `2 + 1 / s` times the missed samples,
* the steps inside the blocks that are not continuous number at most twice
  the missed samples,
* the missed samples counted in the blocks are at most the missed samples.

The reasons: a step that is not continuous counts a missed sample at one of
its two output samples (`le_continuousBefore_add`), and the steps of
continuous playback that do not break new ground recover, by `s` each, a
distance that only steps back create, which count the frames that they play
again (`replay_le_missed`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {plays : ℕ → Option ℝ}

/-- The position played last is at most the largest position played. -/
theorem getD_lastPlayed_le_maxPlayed (plays : ℕ → Option ℝ) (K : ℕ) :
    (lastPlayed plays K).getD 0 ≤ maxPlayed plays K := by
  cases hl : lastPlayed plays K with
  | none => simpa using maxPlayed_nonneg plays K
  | some x =>
    obtain ⟨ht, hx⟩ := lastPlayed_some hl
    simp only [Option.getD_some]
    exact le_maxPlayed hx (by omega)

/-- The count of the steps of continuous playback that do not break new
ground never decreases. -/
theorem replayBefore_mono (plays : ℕ → Option ℝ) : Monotone (replayBefore plays) := by
  refine monotone_nat_of_le_succ fun K => ?_
  by_cases h : PlaysContinuously plays K ∧ ¬ NewGround plays K
  · rw [replayBefore_succ_of h]
    exact Nat.le_succ _
  · rw [replayBefore_succ_of_not h]

/-- **The losses of the first `N` blocks are paid for by missed samples.**
Let every position be at least zero, and let the position advance by at
least `s > 0` in every step of continuous playback. Take blocks of `B ≥ 1`
output samples, and let `M` be the missed samples counted at the output
samples up to `N * B`. Summed over the first `N` blocks: the steps between
two output samples of a block that do not break new ground number at most
`(2 + 1 / s) * M`; those that are not continuous number at most `2 * M`; and
the missed samples counted in the blocks are at most `M`. -/
theorem sum_blocks_losses_le {s : ℝ} (hs : 0 < s)
    (hpos : ∀ k x, plays k = some x → 0 ≤ x)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {B : ℕ} (hB : 0 < B) (N : ℕ) :
    (∑ b ∈ Finset.range N,
        (((B : ℝ) - 1) - newGroundCount plays (b * B) ((b + 1) * B - 1))
      ≤ (2 + 1 / s) * missedBefore plays (N * B + 1))
    ∧ (∑ b ∈ Finset.range N,
        (((B : ℝ) - 1)
          - ((continuousBefore plays ((b + 1) * B - 1) : ℝ) - continuousBefore plays (b * B)))
      ≤ 2 * missedBefore plays (N * B + 1))
    ∧ (∑ b ∈ Finset.range N,
        ((missedBefore plays ((b + 1) * B) : ℝ) - missedBefore plays (b * B))
      ≤ missedBefore plays (N * B + 1)) := by
  -- Facts about one block.
  have hblock : ∀ b : ℕ, b * B ≤ (b + 1) * B - 1 ∧ (b + 1) * B - 1 + 1 = (b + 1) * B := by
    intro b
    have e : (b + 1) * B = b * B + B := by ring
    constructor <;> omega
  have hsize : ∀ b : ℕ, (((b + 1) * B : ℕ) : ℝ) = ((b * B : ℕ) : ℝ) + B := by
    intro b
    have e : (b + 1) * B = b * B + B := by ring
    rw [e]
    push_cast
    ring
  have hc1 : ∀ b : ℕ, (continuousBefore plays ((b + 1) * B) : ℝ)
      ≤ continuousBefore plays ((b + 1) * B - 1) + 1 := by
    intro b
    obtain ⟨K, hK⟩ : ∃ K, K + 1 = (b + 1) * B := ⟨(b + 1) * B - 1, (hblock b).2⟩
    have hKe : (b + 1) * B - 1 = K := by omega
    rw [hKe, ← hK]
    by_cases hc : PlaysContinuously plays K
    · rw [continuousBefore_succ_of hc]
      push_cast
      exact le_rfl
    · rw [continuousBefore_succ_of_not hc]
      linarith
  have hc2 : ∀ b : ℕ, (newGroundCount plays (b * B) ((b + 1) * B - 1) : ℝ)
      + replayBefore plays ((b + 1) * B - 1) + continuousBefore plays (b * B)
      = continuousBefore plays ((b + 1) * B - 1) + replayBefore plays (b * B) := by
    intro b
    have h := newGroundCount_add_replay (plays := plays) ((b + 1) * B - 1) (hblock b).1
    exact_mod_cast h
  have hc3 : ∀ b : ℕ, (replayBefore plays ((b + 1) * B - 1) : ℝ)
      ≤ replayBefore plays ((b + 1) * B) := by
    intro b
    exact_mod_cast replayBefore_mono plays (Nat.sub_le _ _)
  -- The steps that are not continuous.
  have hNC : ∀ n : ℕ, ∑ b ∈ Finset.range n,
      (((B : ℝ) - 1)
        - ((continuousBefore plays ((b + 1) * B - 1) : ℝ) - continuousBefore plays (b * B)))
      ≤ ((n * B : ℕ) : ℝ) - continuousBefore plays (n * B) := by
    intro n
    induction n with
    | zero => simp [continuousBefore]
    | succ n ih =>
      rw [Finset.sum_range_succ, hsize n]
      have := hc1 n
      linarith
  -- The steps that do not break new ground.
  have hO : ∀ n : ℕ, ∑ b ∈ Finset.range n,
      (((B : ℝ) - 1) - newGroundCount plays (b * B) ((b + 1) * B - 1))
      ≤ ((n * B : ℕ) : ℝ) - continuousBefore plays (n * B) + replayBefore plays (n * B) := by
    intro n
    induction n with
    | zero => simp [continuousBefore, replayBefore]
    | succ n ih =>
      rw [Finset.sum_range_succ, hsize n]
      have h1 := hc1 n
      have h2 := hc2 n
      have h3 := hc3 n
      linarith
  -- The missed samples of the blocks.
  have hμ : ∑ b ∈ Finset.range N,
      ((missedBefore plays ((b + 1) * B) : ℝ) - missedBefore plays (b * B))
      = (missedBefore plays (N * B) : ℝ) - missedBefore plays (0 * B) :=
    Finset.sum_range_sub (fun i => (missedBefore plays (i * B) : ℝ)) N
  have hm0 : (missedBefore plays (0 * B) : ℝ) = 0 := by simp [missedBefore]
  -- The counts up to output sample `N * B`.
  have hmono : (missedBefore plays (N * B) : ℝ) ≤ missedBefore plays (N * B + 1) := by
    exact_mod_cast missedBefore_mono plays (Nat.le_succ (N * B))
  have hnc : ((N * B : ℕ) : ℝ) ≤ continuousBefore plays (N * B) + missedBefore plays (N * B)
      + missedBefore plays (N * B + 1) := by
    exact_mod_cast le_continuousBefore_add plays (N * B)
  have hrep := replay_le_missed hpos hslow (N * B)
  have hdebt := getD_lastPlayed_le_maxPlayed plays (N * B + 1)
  have hreplay : (replayBefore plays (N * B) : ℝ) ≤ 1 / s * missedBefore plays (N * B + 1) := by
    have h1 : s * replayBefore plays (N * B) ≤ missedBefore plays (N * B + 1) := by linarith
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs]
    linarith
  have hM0 : (0 : ℝ) ≤ missedBefore plays (N * B + 1) := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · have := hO N
    have e : (2 + 1 / s) * (missedBefore plays (N * B + 1) : ℝ)
        = 2 * missedBefore plays (N * B + 1) + 1 / s * missedBefore plays (N * B + 1) := by
      ring
    rw [e]
    linarith
  · have := hNC N
    linarith
  · rw [hμ, hm0]
    linarith

end Unisono.Spec
