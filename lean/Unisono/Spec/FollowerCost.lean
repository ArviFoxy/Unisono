/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.FollowerSteps
public import Unisono.Spec.PlayedSteps
public import Unisono.Spec.Stall
public import Unisono.Spec.MissingSamples

/-!
# Missed samples and discontinuities of playback that follows a target

Statements about four sequences indexed by the output sample of one
speaker, with no world and no solution:

* `ξ k`, a position for every output sample: where the target is, whether
  or not it is known at that output sample;
* `X k`, the target as it is known: `ξ k`, or nothing;
* `c k`, what the follower gives (`followStep u J`), starting from the
  target at output sample zero;
* `p k`, what is played: `c k`, or nothing.

`Follows u J ξ X c` states the relations of the first three. A step of the
target from output sample `k` to the next is regular when the target
advances by one frame within `u`; `stepExcess u J ξ k` is zero for a
regular step, and otherwise the distance of the advance from one frame,
plus `J`.

For `0 ≤ u < 1 ≤ J`:

* `Follows.dist_le`: what the follower gives is within `J - u` of the
  target.
* `Follows.step_le`: from one output sample to the next, the follower
  advances by one frame within `u` plus the excess of the target's step.
* `Follows.sum_missedAt_le`: **the missed samples** counted at the output
  samples before `K` are at most `1 + u` times the number of those output
  samples that play nothing, plus `2 * J` times the number of
  discontinuities before `K`, plus twice the sum of the excesses of the
  target's steps before `K`.
* `Follows.sum_discontinuityAt_le`: **the discontinuities** counted at the
  output samples before `K` are at most the number of output samples up to
  `K` that play nothing, plus the sum of the excesses of the target's steps
  before `K`.

So playback that follows a target misses samples and breaks only where an
output sample plays nothing or where the target itself steps irregularly.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- What an irregular step of a target costs. If the target `ξ` advances
from output sample `k` to the next by one frame within `u`, zero; otherwise
the distance of its advance from one frame, plus `J`. -/
def stepExcess (u J : ℝ) (ξ : ℕ → ℝ) (k : ℕ) : ℝ :=
  if u < |ξ (k + 1) - ξ k - 1| then |ξ (k + 1) - ξ k - 1| + J else 0

/-- The follower `c` follows the target `X`, which at every output sample is
the position `ξ k` or nothing: it starts at the target, and each value is
the follower's step from the value before and the target. -/
structure Follows (u J : ℝ) (ξ : ℕ → ℝ) (X c : ℕ → Option ℝ) : Prop where
  target : ∀ k, X k = none ∨ X k = some (ξ k)
  start : c 0 = X 0
  step : ∀ k, c (k + 1) = followStep u J (c k) (X (k + 1))

variable {u J : ℝ} {ξ : ℕ → ℝ} {X c p : ℕ → Option ℝ}

theorem stepExcess_nonneg (hJ : 0 ≤ J) (ξ : ℕ → ℝ) (k : ℕ) : 0 ≤ stepExcess u J ξ k := by
  unfold stepExcess
  split_ifs
  · exact add_nonneg (abs_nonneg _) hJ
  · exact le_rfl

/-- The excess of a step is zero or at least `J`. -/
theorem stepExcess_eq_zero_or (ξ : ℕ → ℝ) (k : ℕ) :
    stepExcess u J ξ k = 0 ∨ J ≤ stepExcess u J ξ k := by
  unfold stepExcess
  split_ifs
  · right
    linarith [abs_nonneg (ξ (k + 1) - ξ k - 1)]
  · left
    rfl

/-- The distance of a step of the target from one frame is at most `u` plus
the excess of the step. -/
theorem abs_le_add_stepExcess (hu : 0 ≤ u) (hJ : 0 ≤ J) (ξ : ℕ → ℝ) (k : ℕ) :
    |ξ (k + 1) - ξ k - 1| ≤ u + stepExcess u J ξ k := by
  unfold stepExcess
  split_ifs with h
  · linarith [abs_nonneg (ξ (k + 1) - ξ k - 1)]
  · linarith [not_lt.mp h]

/-- Over several output samples, a sequence of positions advances by their
number within the sum of the distances of its steps from one frame. -/
theorem abs_sub_le_sum_steps (ξ : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    |ξ b - ξ a - ((b : ℝ) - a)| ≤ ∑ i ∈ Finset.Ico a b, |ξ (i + 1) - ξ i - 1| := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    have h1 : ξ (b + 1) - ξ a - (((b + 1 : ℕ) : ℝ) - a)
        = (ξ b - ξ a - ((b : ℝ) - a)) + (ξ (b + 1) - ξ b - 1) := by
      push_cast
      ring
    rw [h1]
    have h2 := abs_add_le (ξ b - ξ a - ((b : ℝ) - a)) (ξ (b + 1) - ξ b - 1)
    linarith

/-- Where the follower gives a position, the target is known. -/
theorem Follows.target_of_some (h : Follows u J ξ X c) {k : ℕ} {y : ℝ} (hy : c k = some y) :
    X k = some (ξ k) := by
  rcases h.target k with hn | hs
  · exfalso
    cases k with
    | zero =>
      rw [h.start, hn] at hy
      exact absurd hy (by simp)
    | succ k =>
      rw [h.step k, hn, followStep_none_right] at hy
      exact absurd hy (by simp)
  · exact hs

/-- **What the follower gives is within `J - u` of the target.** -/
theorem Follows.dist_le (h : Follows u J ξ X c) (huJ : u ≤ J) {k : ℕ} {y : ℝ}
    (hy : c k = some y) : |y - ξ k| ≤ J - u := by
  have hX := h.target_of_some hy
  cases k with
  | zero =>
    rw [h.start, hX] at hy
    obtain rfl := Option.some.inj hy
    rw [sub_self, abs_zero]
    linarith
  | succ k =>
    rw [h.step k, hX] at hy
    cases hck : c k with
    | none =>
      rw [hck, followStep_none_left] at hy
      obtain rfl := Option.some.inj hy
      rw [sub_self, abs_zero]
      linarith
    | some y₀ =>
      rw [hck] at hy
      obtain ⟨h1, -, h3⟩ := followStep_gap hy
      rcases le_or_gt |ξ (k + 1) - y₀ - 1| J with hle | hgt
      · exact le_trans h1 (max_le (by linarith) (by linarith))
      · rw [h3 hgt, sub_self, abs_zero]
        linarith

/-- **One step of the follower against the target's step.** From one output
sample to the next, the follower advances by one frame within `u` plus the
excess of the target's step. -/
theorem Follows.step_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (huJ : u ≤ J) {k : ℕ}
    {y y' : ℝ} (hy : c k = some y) (hy' : c (k + 1) = some y') :
    |y' - y - 1| ≤ u + stepExcess u J ξ k := by
  have hX := h.target_of_some hy'
  have hstep := h.step k
  rw [hy, hX] at hstep
  rw [hstep] at hy'
  obtain ⟨-, h2, h3⟩ := followStep_gap hy'
  have hJ0 : 0 ≤ J := le_trans hu huJ
  have hex := stepExcess_nonneg (u := u) hJ0 ξ k
  rcases le_or_gt |ξ (k + 1) - y - 1| J with hle | hgt
  · have := h2 hu hle
    linarith
  · rw [h3 hgt]
    have hd := h.dist_le huJ hy
    have htri : |ξ (k + 1) - y - 1| ≤ |ξ (k + 1) - ξ k - 1| + |y - ξ k| := by
      have e : ξ (k + 1) - y - 1 = (ξ (k + 1) - ξ k - 1) - (y - ξ k) := by ring
      rw [e]
      exact abs_sub _ _
    have hV : u < |ξ (k + 1) - ξ k - 1| := by linarith
    unfold stepExcess
    rw [ite_eq_left hV]
    linarith

/-- An output sample that plays the source after no earlier one did counts
no missed samples. -/
theorem missedAt_of_lastPlayed_none {plays : ℕ → Option ℝ} {K : ℕ} {y : ℝ}
    (hy : plays K = some y) (hx : lastPlayed plays K = none) : missedAt plays K = 0 := by
  classical
  have hnone := eq_none_of_lastPlayed_none hx
  have hno : ¬ ∃ j < K, (plays j).isSome = true := by
    rintro ⟨j, hj, hs⟩
    rw [hnone j hj] at hs
    exact absurd hs (by simp)
  simp [missedAt, hy, hno]

/-- **The missed samples of one output sample that plays the source.** Let
`t` be the number of output samples just before it that play nothing. The
missed samples counted at it are at most `u * t`, plus `2 * J` times the
number of discontinuities since the last output sample that played the
source, plus twice the sum of the excesses of the target's steps since
then. -/
theorem Follows.missedAt_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (hu1 : u < 1) (hJ : 1 ≤ J)
    (hp : ∀ k, p k = none ∨ p k = c k) {K : ℕ} {y : ℝ} (hy : p K = some y) :
    (missedAt p K : ℝ) ≤ u * trailing p K
      + 2 * J * ∑ k ∈ Finset.Ico (K - 1 - trailing p K) K, (discontinuityAt p k : ℝ)
      + 2 * ∑ i ∈ Finset.Ico (K - 1 - trailing p K) K, stepExcess u J ξ i := by
  have hJ0 : 0 ≤ J := by linarith
  have huJ : u ≤ J := by linarith
  have hsum0 : 0 ≤ ∑ i ∈ Finset.Ico (K - 1 - trailing p K) K, stepExcess u J ξ i :=
    Finset.sum_nonneg fun i _ => stepExcess_nonneg hJ0 ξ i
  have hdisc0 : 0 ≤ ∑ k ∈ Finset.Ico (K - 1 - trailing p K) K, (discontinuityAt p k : ℝ) :=
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ trailing p K := Nat.cast_nonneg _
  have hcK : c K = some y := by
    rcases hp K with hn | hc
    · rw [hn] at hy
      exact absurd hy (by simp)
    · rw [← hc]
      exact hy
  cases hlast : lastPlayed p K with
  | none =>
    rw [missedAt_of_lastPlayed_none hy hlast, Nat.cast_zero]
    nlinarith
  | some x =>
    obtain ⟨htK, hj⟩ := lastPlayed_some hlast
    have hcj : c (K - 1 - trailing p K) = some x := by
      rcases hp (K - 1 - trailing p K) with hn | hc
      · rw [hn] at hj
        exact absurd hj (by simp)
      · rw [← hc]
        exact hj
    have hmiss := missedAt_le_abs hy hlast
    rcases Nat.eq_zero_or_pos (trailing p K) with ht | ht
    · -- The output sample just before played the source.
      rw [ht] at hcj hmiss hdisc0 ⊢
      have hK : K - 1 - 0 + 1 = K := by omega
      have hcK' : c (K - 1 - 0 + 1) = some y := by
        rw [hK]
        exact hcK
      have hstep := h.step_le hu huJ hcj hcK'
      have hIco : Finset.Ico (K - 1 - 0) K = {K - 1 - 0} := by
        ext i
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      rw [hIco, Finset.sum_singleton] at hdisc0 ⊢
      rw [Finset.sum_singleton]
      simp only [Nat.cast_zero, zero_add, mul_zero] at hmiss ⊢
      rcases stepExcess_eq_zero_or (u := u) (J := J) ξ (K - 1 - 0) with he | he
      · rw [he] at hstep ⊢
        have hlt : (missedAt p K : ℝ) < 1 := by linarith
        have hzero : missedAt p K = 0 := by
          have : missedAt p K < 1 := by exact_mod_cast hlt
          omega
        rw [hzero, Nat.cast_zero]
        nlinarith
      · nlinarith
    · -- Output samples in between played nothing.
      have hle : K - 1 - trailing p K ≤ K := by omega
      have hnext : p (K - 1 - trailing p K + 1) = none :=
        eq_none_of_trailing (plays := p) (K := K) (by omega) (by omega)
      have hbreak : discontinuityAt p (K - 1 - trailing p K) = 1 :=
        discontinuityAt_of_some_none hj hnext
      have hone : (1 : ℝ)
          ≤ ∑ k ∈ Finset.Ico (K - 1 - trailing p K) K, (discontinuityAt p k : ℝ) := by
        have hmem : K - 1 - trailing p K ∈ Finset.Ico (K - 1 - trailing p K) K := by
          rw [Finset.mem_Ico]
          omega
        have hsingle := Finset.single_le_sum
          (f := fun k => (discontinuityAt p k : ℝ)) (fun i _ => Nat.cast_nonneg _) hmem
        simp only [hbreak, Nat.cast_one] at hsingle
        exact hsingle
      have hd1 := h.dist_le huJ hcK
      have hd2 := h.dist_le huJ hcj
      have htel := abs_sub_le_sum_steps ξ hle
      have hcast : ((K : ℝ) - ((K - 1 - trailing p K : ℕ) : ℝ)) = trailing p K + 1 := by
        have e : K = (K - 1 - trailing p K) + (trailing p K + 1) := by omega
        have e' : (K : ℝ) = ((K - 1 - trailing p K : ℕ) : ℝ) + ((trailing p K : ℝ) + 1) := by
          exact_mod_cast e
        linarith
      rw [hcast] at htel
      have hsteps : ∑ i ∈ Finset.Ico (K - 1 - trailing p K) K, |ξ (i + 1) - ξ i - 1|
          ≤ ∑ i ∈ Finset.Ico (K - 1 - trailing p K) K, (u + stepExcess u J ξ i) :=
        Finset.sum_le_sum fun i _ => abs_le_add_stepExcess hu hJ0 ξ i
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsteps
      have hcard : ((K - (K - 1 - trailing p K) : ℕ) : ℝ) = trailing p K + 1 := by
        have e : K - (K - 1 - trailing p K) = trailing p K + 1 := by omega
        rw [e]
        push_cast
        ring
      rw [hcard] at hsteps
      have htri : |y - x - ((trailing p K : ℝ) + 1)|
          ≤ |y - ξ K| + |ξ K - ξ (K - 1 - trailing p K) - ((trailing p K : ℝ) + 1)|
            + |x - ξ (K - 1 - trailing p K)| := by
        have e : y - x - ((trailing p K : ℝ) + 1)
            = (y - ξ K) + (ξ K - ξ (K - 1 - trailing p K) - ((trailing p K : ℝ) + 1))
              - (x - ξ (K - 1 - trailing p K)) := by ring
        rw [e]
        have h2 := abs_sub ((y - ξ K)
            + (ξ K - ξ (K - 1 - trailing p K) - ((trailing p K : ℝ) + 1)))
          (x - ξ (K - 1 - trailing p K))
        have h3 := abs_add_le (y - ξ K)
          (ξ K - ξ (K - 1 - trailing p K) - ((trailing p K : ℝ) + 1))
        linarith
      nlinarith

/-- **The missed samples of playback that follows a target.** For
`0 ≤ u < 1 ≤ J`, the missed samples counted at the output samples before
`K` are at most `1 + u` times the number of those output samples that play
nothing, plus `2 * J` times the number of discontinuities before `K`, plus
twice the sum of the excesses of the target's steps before `K`. -/
theorem Follows.sum_missedAt_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (hu1 : u < 1)
    (hJ : 1 ≤ J) (hp : ∀ k, p k = none ∨ p k = c k) (K : ℕ) :
    ∑ k ∈ Finset.range K, (missedAt p k : ℝ)
      ≤ (1 + u) * ∑ k ∈ Finset.range K, (missingAt p k : ℝ)
        + 2 * J * ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ)
        + 2 * ∑ i ∈ Finset.range K, stepExcess u J ξ i := by
  have hJ0 : 0 ≤ J := by linarith
  have hinv : ∀ K, ∑ k ∈ Finset.range K, (missedAt p k : ℝ)
      ≤ (1 + u) * ∑ k ∈ Finset.range K, (missingAt p k : ℝ) - u * trailing p K
        + 2 * J * ∑ k ∈ Finset.range (K - 1 - trailing p K), (discontinuityAt p k : ℝ)
        + 2 * ∑ i ∈ Finset.range (K - 1 - trailing p K), stepExcess u J ξ i := by
    intro K
    induction K with
    | zero => simp [trailing]
    | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      cases hK : p K with
      | none =>
        have e1 : missedAt p K = 1 := missedAt_of_none hK
        have e2 : missingAt p K = 1 := by simp [missingAt, hK]
        have e3 : K + 1 - 1 - (trailing p K + 1) = K - 1 - trailing p K := by omega
        rw [e1, e2, trailing_succ_none hK, e3]
        push_cast
        linarith
      | some y =>
        have e2 : missingAt p K = 0 := by simp [missingAt, hK]
        have e3 : K + 1 - 1 - 0 = K := by omega
        have hm := h.missedAt_le hu hu1 hJ hp hK
        have hle : K - 1 - trailing p K ≤ K := by omega
        have hsplit := Finset.sum_Ico_consecutive (fun i => stepExcess u J ξ i)
          (Nat.zero_le (K - 1 - trailing p K)) hle
        have hsplit' := Finset.sum_Ico_consecutive (fun k => (discontinuityAt p k : ℝ))
          (Nat.zero_le (K - 1 - trailing p K)) hle
        rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hsplit hsplit'
        rw [e2, trailing_succ_some hK, e3]
        push_cast
        nlinarith
  have h1 := hinv K
  have h2 : (0 : ℝ) ≤ u * trailing p K := mul_nonneg hu (Nat.cast_nonneg _)
  have h3 : ∑ i ∈ Finset.range (K - 1 - trailing p K), stepExcess u J ξ i
      ≤ ∑ i ∈ Finset.range K, stepExcess u J ξ i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      fun i _ _ => stepExcess_nonneg hJ0 ξ i
  have h4 : ∑ k ∈ Finset.range (K - 1 - trailing p K), (discontinuityAt p k : ℝ)
      ≤ ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      fun i _ _ => Nat.cast_nonneg _
  nlinarith

/-- **The discontinuity of one output sample.** It is at most one if the
next output sample plays nothing, plus the excess of the target's step. -/
theorem Follows.discontinuityAt_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (hu1 : u < 1)
    (hJ : 1 ≤ J) (hp : ∀ k, p k = none ∨ p k = c k) (k : ℕ) :
    (discontinuityAt p k : ℝ) ≤ missingAt p (k + 1) + stepExcess u J ξ k := by
  have hJ0 : 0 ≤ J := by linarith
  have huJ : u ≤ J := by linarith
  have hex := stepExcess_nonneg (u := u) hJ0 ξ k
  have hmis : (0 : ℝ) ≤ missingAt p (k + 1) := Nat.cast_nonneg _
  cases hk : p k with
  | none =>
    rw [discontinuityAt_of_none hk, Nat.cast_zero]
    linarith
  | some y =>
    have hck : c k = some y := by
      rcases hp k with hn | hc
      · rw [hn] at hk
        exact absurd hk (by simp)
      · rw [← hc]
        exact hk
    cases hk1 : p (k + 1) with
    | none =>
      have e : missingAt p (k + 1) = 1 := by simp [missingAt, hk1]
      rw [discontinuityAt_of_some_none hk hk1, e]
      push_cast
      linarith
    | some y' =>
      have hck1 : c (k + 1) = some y' := by
        rcases hp (k + 1) with hn | hc
        · rw [hn] at hk1
          exact absurd hk1 (by simp)
        · rw [← hc]
          exact hk1
      by_cases hcont : y < y' ∧ y' < y + 2
      · rw [discontinuityAt_of_continuous hk hk1 hcont, Nat.cast_zero]
        linarith
      · rw [discontinuityAt_of_not_continuous hk hk1 hcont, Nat.cast_one]
        have hstep := h.step_le hu huJ hck hck1
        have hbig : 1 ≤ |y' - y - 1| := by
          rw [not_and_or, not_lt, not_lt] at hcont
          rcases hcont with h1 | h1
          · rw [abs_of_nonpos (by linarith)]
            linarith
          · rw [abs_of_nonneg (by linarith)]
            linarith
        rcases stepExcess_eq_zero_or (u := u) (J := J) ξ k with he | he
        · rw [he] at hstep
          linarith
        · linarith

/-- **The discontinuities of playback that follows a target.** For
`0 ≤ u < 1 ≤ J`, the discontinuities counted at the output samples before
`K` are at most the number of the output samples up to `K` that play
nothing, plus the sum of the excesses of the target's steps before `K`. -/
theorem Follows.sum_discontinuityAt_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (hu1 : u < 1)
    (hJ : 1 ≤ J) (hp : ∀ k, p k = none ∨ p k = c k) (K : ℕ) :
    ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ)
      ≤ ∑ k ∈ Finset.range (K + 1), (missingAt p k : ℝ)
        + ∑ i ∈ Finset.range K, stepExcess u J ξ i := by
  have h1 : ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ)
      ≤ ∑ k ∈ Finset.range K, ((missingAt p (k + 1) : ℝ) + stepExcess u J ξ k) :=
    Finset.sum_le_sum fun k _ => h.discontinuityAt_le hu hu1 hJ hp k
  rw [Finset.sum_add_distrib] at h1
  have h2 : ∑ k ∈ Finset.range K, (missingAt p (k + 1) : ℝ)
      ≤ ∑ k ∈ Finset.range (K + 1), (missingAt p k : ℝ) := by
    rw [Finset.sum_range_succ' (fun k => (missingAt p k : ℝ)) K]
    have : (0 : ℝ) ≤ missingAt p 0 := Nat.cast_nonneg _
    linarith
  linarith

end Unisono.Spec
