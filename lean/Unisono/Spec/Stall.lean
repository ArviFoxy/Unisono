/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Skips

/-!
# What a stretch without new frames costs

While no new frame reaches a host, a speaker on it can play only positions
up to a fixed one. This file counts what any playback pays for such a
stretch of output samples, in missed samples and in discontinuities.

Let every step of continuous playback advance the position by at least `s`
frames, with `0 ≤ s ≤ 1`. Take the output samples from `k₀` to `K`. Each of
them is of one of three kinds.

* It plays nothing of the source. It counts one missed sample.
* It plays the source and the next output sample continues it. The position
  then advances by at least `s`.
* It plays the source and the next output sample does not continue it. It
  counts one discontinuity.

The position moves back only where an output sample plays frames again, and
those frames are counted as missed samples.

**Theorem** (`stall_le`). The position played last before `k₀`, plus `s` for
each output sample from `k₀` to `K`, is at most the position played last up
to `K`, plus the missed samples counted from `k₀` to `K`, plus `s` times the
discontinuities counted from `k₀` to `K - 1` and one more.

**Theorem** (`stall_le_of_le`). So when every position played from `k₀` to
`K` is at most `P`, and the position played last before `k₀` is `x₀ ≤ P`,
the missed samples plus `s` times the discontinuities are at least
`s * (K - k₀) - (P - x₀)`: all of the stretch except what the frames between
`x₀` and `P` allow, played as slowly as the solution may.

Nothing is assumed of the playback besides the least advance `s` of a step
of continuous playback and that positions are not negative.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {plays : ℕ → Option ℝ}

/-! ## Discontinuities, by what the two output samples play -/

theorem discontinuityAt_of_none {k : ℕ} (h : plays k = none) :
    discontinuityAt plays k = 0 := by
  classical
  unfold discontinuityAt
  rw [ite_eq_right]
  rintro ⟨hsome, -⟩
  rw [h] at hsome
  exact absurd hsome (by simp)

theorem discontinuityAt_of_some_none {k : ℕ} {x : ℝ} (h : plays k = some x)
    (h' : plays (k + 1) = none) : discontinuityAt plays k = 1 := by
  classical
  unfold discontinuityAt
  rw [ite_eq_left]
  refine ⟨by rw [h]; rfl, ?_⟩
  rintro ⟨x', y', -, hy', -⟩
  rw [h'] at hy'
  exact absurd hy' (by simp)

theorem discontinuityAt_of_continuous {k : ℕ} {x y : ℝ} (h : plays k = some x)
    (h' : plays (k + 1) = some y) (hc : x < y ∧ y < x + 2) :
    discontinuityAt plays k = 0 := by
  classical
  unfold discontinuityAt
  rw [ite_eq_right]
  rintro ⟨-, hnot⟩
  exact hnot ⟨x, y, h, h', hc.1, hc.2⟩

theorem discontinuityAt_of_not_continuous {k : ℕ} {x y : ℝ} (h : plays k = some x)
    (h' : plays (k + 1) = some y) (hc : ¬ (x < y ∧ y < x + 2)) :
    discontinuityAt plays k = 1 := by
  classical
  unfold discontinuityAt
  rw [ite_eq_left]
  refine ⟨by rw [h]; rfl, ?_⟩
  rintro ⟨x', y', hx', hy', h1, h2⟩
  rw [h] at hx'
  rw [h'] at hy'
  obtain rfl := Option.some.inj hx'
  obtain rfl := Option.some.inj hy'
  exact hc ⟨h1, h2⟩

/-! ## The position played last -/

/-- **A position that moves back is paid for.** An output sample that plays
the position `y` counts at least as many missed samples as the position
played last before it lies above `y`. When nothing was played before it,
this says that `y` is not negative. -/
theorem getD_lastPlayed_le (hpos : ∀ k x, plays k = some x → 0 ≤ x) {K : ℕ} {y : ℝ}
    (hy : plays K = some y) :
    (lastPlayed plays K).getD 0 ≤ y + missedAt plays K := by
  have h0 : (0 : ℝ) ≤ missedAt plays K := Nat.cast_nonneg _
  cases hl : lastPlayed plays K with
  | none =>
    have h1 := hpos K y hy
    simp only [Option.getD_none]
    linarith
  | some x =>
    simp only [Option.getD_some]
    rcases le_or_gt x y with hxy | hxy
    · linarith
    · rw [missedAt_of_lastPlayed hy hl]
      push_cast
      have h1 : (0 : ℝ) ≤ ((⌊y - x - 1⌋ - (trailing plays K : ℤ)).toNat : ℝ) := Nat.cast_nonneg _
      have h3 : ((⌊1 - (y - x)⌋ : ℤ) : ℝ) ≤ ((⌊1 - (y - x)⌋.toNat : ℕ) : ℝ) := by
        exact_mod_cast Int.self_le_toNat _
      have h4 := Int.sub_one_lt_floor (1 - (y - x))
      linarith

/-- When every position played from `k₀` to `K` is at most `P`, and so is
the position played last before `k₀`, the position played last up to `K` is
at most `P`. -/
theorem getD_lastPlayed_le_of_le {P : ℝ} {k₀ : ℕ} (hx₀ : (lastPlayed plays k₀).getD 0 ≤ P) :
    ∀ K, k₀ ≤ K → (∀ k, k₀ ≤ k → k < K → ∀ x, plays k = some x → x ≤ P) →
      (lastPlayed plays K).getD 0 ≤ P := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => exact fun _ => hx₀
  | succ K hK ih =>
    intro hP
    cases hp : plays K with
    | none =>
      rw [lastPlayed_succ_none hp]
      exact ih fun k hk hkK x hx => hP k hk (Nat.lt_succ_of_lt hkK) x hx
    | some y =>
      rw [lastPlayed_succ_some hp]
      exact hP K hK (Nat.lt_succ_self K) y hp

/-! ## The stretch -/

/-- **What a stretch of output samples costs.** Let every step of continuous
playback advance the position by at least `s`, with `s ≤ 1`, and let
positions be not negative. For the output samples from `k₀` to `K`: the
position played last before `k₀`, plus `s` for each of them, is at most the
position played last up to `K`, plus the missed samples counted at them,
plus `s` times the discontinuities counted from `k₀` to `K - 1`, and `s`
once more if output sample `K` plays the source. -/
theorem stall_le {s : ℝ} (hs1 : s ≤ 1)
    (hpos : ∀ k x, plays k = some x → 0 ≤ x)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    (k₀ : ℕ) :
    ∀ K, k₀ ≤ K →
      (lastPlayed plays k₀).getD 0 + s * ((K : ℝ) + 1 - k₀)
        ≤ (lastPlayed plays (K + 1)).getD 0
          + ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt plays k : ℝ)
          + s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt plays k : ℝ)
            + if (plays K).isSome then 1 else 0) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    have e : (k₀ : ℝ) + 1 - k₀ = 1 := by ring
    rw [e, mul_one, Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty,
      Finset.sum_empty, zero_add, zero_add]
    cases hp : plays k₀ with
    | none =>
      have hb : (if (none : Option ℝ).isSome then (1 : ℝ) else 0) = 0 := by simp
      rw [lastPlayed_succ_none hp, missedAt_of_none hp, hb, mul_zero, add_zero]
      push_cast
      linarith
    | some y =>
      have hb : (if (some y : Option ℝ).isSome then (1 : ℝ) else 0) = 1 := by simp
      have hq := getD_lastPlayed_le hpos hp
      rw [lastPlayed_succ_some hp, hb, mul_one]
      simp only [Option.getD_some]
      linarith
  | succ K hK ih =>
    have hcast : (((K + 1 : ℕ) : ℝ) + 1 - k₀) = ((K : ℝ) + 1 - k₀) + 1 := by
      push_cast
      ring
    have hMsum : ∑ k ∈ Finset.Ico k₀ (K + 1 + 1), (missedAt plays k : ℝ)
        = ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt plays k : ℝ) + missedAt plays (K + 1) :=
      Finset.sum_Ico_succ_top (Nat.le_succ_of_le hK) _
    have hDsum : ∑ k ∈ Finset.Ico k₀ (K + 1), (discontinuityAt plays k : ℝ)
        = ∑ k ∈ Finset.Ico k₀ K, (discontinuityAt plays k : ℝ) + discontinuityAt plays K :=
      Finset.sum_Ico_succ_top hK _
    rw [hcast, hMsum, hDsum]
    have hM0 : (0 : ℝ) ≤ missedAt plays (K + 1) := Nat.cast_nonneg _
    -- What output sample `K + 1` adds.
    have hstep : (lastPlayed plays (K + 1)).getD 0
          + s * (if (plays K).isSome then 1 else 0) + s
        ≤ (lastPlayed plays (K + 1 + 1)).getD 0 + (missedAt plays (K + 1) : ℝ)
          + s * ((discontinuityAt plays K : ℝ)
            + if (plays (K + 1)).isSome then 1 else 0) := by
      cases hp : plays (K + 1) with
      | none =>
        have hb : (if (none : Option ℝ).isSome then (1 : ℝ) else 0) = 0 := by simp
        rw [lastPlayed_succ_none hp, missedAt_of_none hp, hb, add_zero]
        cases hq : plays K with
        | none =>
          have hb' : (if (none : Option ℝ).isSome then (1 : ℝ) else 0) = 0 := by simp
          rw [hb', discontinuityAt_of_none hq]
          push_cast
          linarith
        | some x =>
          have hb' : (if (some x : Option ℝ).isSome then (1 : ℝ) else 0) = 1 := by simp
          rw [hb', discontinuityAt_of_some_none hq hp]
          push_cast
          linarith
      | some y =>
        have hb : (if (some y : Option ℝ).isSome then (1 : ℝ) else 0) = 1 := by simp
        have hQ := getD_lastPlayed_le hpos hp
        rw [lastPlayed_succ_some hp, hb]
        simp only [Option.getD_some]
        cases hq : plays K with
        | none =>
          have hb' : (if (none : Option ℝ).isSome then (1 : ℝ) else 0) = 0 := by simp
          rw [hb', discontinuityAt_of_none hq]
          push_cast
          linarith
        | some x =>
          have hb' : (if (some x : Option ℝ).isSome then (1 : ℝ) else 0) = 1 := by simp
          have hl : lastPlayed plays (K + 1) = some x := lastPlayed_succ_some hq
          rw [hl] at hQ ⊢
          simp only [Option.getD_some] at hQ ⊢
          rw [hb']
          by_cases hc : x < y ∧ y < x + 2
          · have hadv := hslow K x y hq hp hc.1 hc.2
            rw [discontinuityAt_of_continuous hq hp hc]
            push_cast
            linarith
          · rw [discontinuityAt_of_not_continuous hq hp hc]
            push_cast
            linarith
    have e : s * (((K : ℝ) + 1 - k₀) + 1) = s * ((K : ℝ) + 1 - k₀) + s := by ring
    rw [e]
    linarith

/-- **What a stretch without new frames costs.** Let every step of
continuous playback advance the position by at least `s`, with `0 ≤ s ≤ 1`,
and let positions be not negative. Suppose that every position played from
output sample `k₀` to `K` is at most `P`, and that the position played last
before `k₀` is at most `P`. Then `s` for each output sample from `k₀` to `K`
is at most the room from that position to `P`, plus the missed samples
counted from `k₀` to `K`, plus `s` times the discontinuities counted from
`k₀` to `K - 1` and one more. -/
theorem stall_le_of_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hpos : ∀ k x, plays k = some x → 0 ≤ x)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {k₀ K : ℕ} (hK : k₀ ≤ K) {P : ℝ} (hx₀ : (lastPlayed plays k₀).getD 0 ≤ P)
    (hP : ∀ k, k₀ ≤ k → k ≤ K → ∀ x, plays k = some x → x ≤ P) :
    s * ((K : ℝ) + 1 - k₀)
      ≤ (P - (lastPlayed plays k₀).getD 0)
        + ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt plays k : ℝ)
        + s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt plays k : ℝ) + 1) := by
  have h1 := stall_le hs1 hpos hslow k₀ K hK
  have h2 : (lastPlayed plays (K + 1)).getD 0 ≤ P :=
    getD_lastPlayed_le_of_le hx₀ (K + 1) (Nat.le_succ_of_le hK)
      fun k hk hkK x hx => hP k hk (Nat.lt_succ_iff.mp hkK) x hx
  have h3 : (if (plays K).isSome then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have h4 := mul_le_mul_of_nonneg_left h3 hs0
  have e : s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt plays k : ℝ)
        + if (plays K).isSome then 1 else 0)
      = s * ∑ k ∈ Finset.Ico k₀ K, (discontinuityAt plays k : ℝ)
        + s * (if (plays K).isSome then 1 else 0) := by ring
  have e' : s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt plays k : ℝ) + 1)
      = s * ∑ k ∈ Finset.Ico k₀ K, (discontinuityAt plays k : ℝ) + s * 1 := by ring
  rw [e] at h1
  rw [e']
  linarith

end Unisono.Spec
