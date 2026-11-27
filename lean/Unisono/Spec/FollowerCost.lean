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
target from one output sample to the next is regular when the target
advances by one frame within `u`. `stepOver u ξ k` is by how much the
advance differs from one frame beyond `u`: zero for a regular step.

The follower moves toward the target by at most `u` per output sample
beyond the one frame, and jumps to the target when the target is more than
`J` frames from one frame after its position (`jumpAt`). So what counts is
the sum of `stepOver`, not the number of irregular steps: a target that
steps irregularly by little costs little.

For `0 ≤ u < 1 ≤ J`:

* `Follows.dist_le`: what the follower gives is within `J - u` of the
  target.
* `Follows.followDist_succ_le`, `Follows.sum_jumpAt_le`: from one output
  sample to the next the distance of the follower from the target grows by
  at most `stepOver`, and falls to zero at a jump, which needs a distance of
  more than `J - u`. So `J - u` times the number of jumps before output
  sample `K` is at most the sum of `stepOver` before `K`.
* `Follows.sum_discontinuityAt_le`: **the discontinuities**. `J - u` times
  the discontinuities counted at the output samples before `K` is at most
  `J - u` times the number of output samples up to `K` that play nothing,
  plus the sum of `stepOver` before `K`.
* `Follows.sum_missedAt_le`: **the missed samples** counted at the output
  samples before `K` are at most `1 + u` times the number of those output
  samples that play nothing, plus `2 * J` times the number of
  discontinuities before `K`, plus the sum of `stepOver` before `K`.

So playback that follows a target misses samples and breaks only where an
output sample plays nothing, or in proportion to how far the target itself
steps irregularly.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- By how much a step of a target differs from one frame, beyond `u`. If
the target `ξ` advances from output sample `k` to the next by one frame
within `u`, zero; otherwise the distance of its advance from one frame,
minus `u`. -/
def stepOver (u : ℝ) (ξ : ℕ → ℝ) (k : ℕ) : ℝ :=
  max (|ξ (k + 1) - ξ k - 1| - u) 0

/-- The follower `c` follows the target `X`, which at every output sample is
the position `ξ k` or nothing: it starts at the target, and each value is
the follower's step from the value before and the target. -/
structure Follows (u J : ℝ) (ξ : ℕ → ℝ) (X c : ℕ → Option ℝ) : Prop where
  target : ∀ k, X k = none ∨ X k = some (ξ k)
  start : c 0 = X 0
  step : ∀ k, c (k + 1) = followStep u J (c k) (X (k + 1))

variable {u J : ℝ} {ξ : ℕ → ℝ} {X c p : ℕ → Option ℝ}

theorem stepOver_nonneg (u : ℝ) (ξ : ℕ → ℝ) (k : ℕ) : 0 ≤ stepOver u ξ k :=
  le_max_right _ _

/-- The distance of a step of the target from one frame is at most `u` plus
`stepOver` of the step. -/
theorem abs_le_add_stepOver (u : ℝ) (ξ : ℕ → ℝ) (k : ℕ) :
    |ξ (k + 1) - ξ k - 1| ≤ u + stepOver u ξ k := by
  have h := le_max_left (|ξ (k + 1) - ξ k - 1| - u) 0
  unfold stepOver
  linarith

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

/-- The distance of what the follower gives from the target at output
sample `k`; zero where the follower gives nothing. -/
def followDist (ξ : ℕ → ℝ) (c : ℕ → Option ℝ) (k : ℕ) : ℝ :=
  match c k with
  | some y => |y - ξ k|
  | none => 0

open Classical in
/-- Whether the follower jumps from output sample `k` to the next: it gives
a position at both, and the target at the next is more than `J` frames from
one frame after its position at `k`. One if it jumps, zero otherwise. -/
def jumpAt (J : ℝ) (ξ : ℕ → ℝ) (c : ℕ → Option ℝ) (k : ℕ) : ℕ :=
  match c k, c (k + 1) with
  | some y, some _ => if J < |ξ (k + 1) - y - 1| then 1 else 0
  | _, _ => 0

theorem followDist_nonneg (ξ : ℕ → ℝ) (c : ℕ → Option ℝ) (k : ℕ) : 0 ≤ followDist ξ c k := by
  unfold followDist
  cases c k with
  | none => exact le_rfl
  | some y => exact abs_nonneg _

theorem followDist_of_some {k : ℕ} {y : ℝ} (hy : c k = some y) :
    followDist ξ c k = |y - ξ k| := by
  unfold followDist
  rw [hy]

theorem followDist_of_none {k : ℕ} (hy : c k = none) : followDist ξ c k = 0 := by
  unfold followDist
  rw [hy]

/-- The follower does not jump to or from an output sample at which it
gives nothing. -/
theorem jumpAt_of_none {k : ℕ} (hy : c k = none ∨ c (k + 1) = none) :
    jumpAt J ξ c k = 0 := by
  unfold jumpAt
  rcases hy with hy | hy
  · rw [hy]
  · rw [hy]
    cases c k <;> rfl

theorem jumpAt_of_some {k : ℕ} {y y' : ℝ} (hy : c k = some y) (hy' : c (k + 1) = some y') :
    jumpAt J ξ c k = if J < |ξ (k + 1) - y - 1| then 1 else 0 := by
  unfold jumpAt
  rw [hy, hy']

/-- **One step of the distance of the follower from the target.** From one
output sample to the next, the distance grows by at most `stepOver` of the
target's step. At a jump it falls to zero, and it was more than `J - u`
with the step's `stepOver`. -/
theorem Follows.followDist_succ_le (h : Follows u J ξ X c) (k : ℕ) :
    followDist ξ c (k + 1) + (J - u) * jumpAt J ξ c k
      ≤ followDist ξ c k + stepOver u ξ k := by
  have hover := stepOver_nonneg u ξ k
  have hd0 := followDist_nonneg ξ c k
  cases hk1 : c (k + 1) with
  | none =>
    rw [followDist_of_none hk1, jumpAt_of_none (Or.inr hk1)]
    push_cast
    linarith
  | some y' =>
    have hX := h.target_of_some hk1
    cases hk : c k with
    | none =>
      have hstep := h.step k
      rw [hk, hX, followStep_none_left] at hstep
      rw [hstep] at hk1
      obtain rfl := Option.some.inj hk1
      rw [followDist_of_some hstep, jumpAt_of_none (Or.inl hk), sub_self, abs_zero]
      push_cast
      linarith
    | some y =>
      have hstep := h.step k
      rw [hk, hX] at hstep
      have hgap := hk1
      rw [hstep] at hgap
      obtain ⟨h1, -, h3⟩ := followStep_gap hgap
      have htri : |ξ (k + 1) - y - 1| ≤ |ξ (k + 1) - ξ k - 1| + |y - ξ k| := by
        have e : ξ (k + 1) - y - 1 = (ξ (k + 1) - ξ k - 1) - (y - ξ k) := by ring
        rw [e]
        exact abs_sub _ _
      have habs := abs_le_add_stepOver u ξ k
      rw [followDist_of_some hk1, followDist_of_some hk, jumpAt_of_some hk hk1]
      by_cases hJ : J < |ξ (k + 1) - y - 1|
      · rw [ite_eq_left hJ, h3 hJ, sub_self, abs_zero]
        push_cast
        linarith
      · rw [ite_eq_right hJ]
        push_cast
        have h2 : max (|ξ (k + 1) - y - 1| - u) 0 ≤ |y - ξ k| + stepOver u ξ k :=
          max_le (by linarith) (by linarith [abs_nonneg (y - ξ k)])
        linarith

/-- **The jumps of the follower.** `J - u` times the number of jumps before
output sample `K`, plus the distance of the follower from the target at
`K`, is at most the sum of `stepOver` of the target's steps before `K`. -/
theorem Follows.sum_jumpAt_le (h : Follows u J ξ X c) (K : ℕ) :
    followDist ξ c K + (J - u) * ∑ k ∈ Finset.range K, (jumpAt J ξ c k : ℝ)
      ≤ ∑ k ∈ Finset.range K, stepOver u ξ k := by
  induction K with
  | zero =>
    have h0 : followDist ξ c 0 = 0 := by
      cases hc : c 0 with
      | none => exact followDist_of_none hc
      | some y =>
        have hX := h.target_of_some hc
        rw [h.start, hX] at hc
        obtain rfl := Option.some.inj hc
        have hc' : c 0 = some (ξ 0) := by rw [h.start, hX]
        rw [followDist_of_some hc', sub_self, abs_zero]
    simp [h0]
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hs := h.followDist_succ_le K
    have e : (J - u) * (∑ k ∈ Finset.range K, (jumpAt J ξ c k : ℝ) + (jumpAt J ξ c K : ℝ))
        = (J - u) * ∑ k ∈ Finset.range K, (jumpAt J ξ c k : ℝ)
          + (J - u) * (jumpAt J ξ c K : ℝ) := by ring
    rw [e]
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

/-- What is played at an output sample is what the follower gives there. -/
theorem follower_of_played (hp : ∀ k, p k = none ∨ p k = c k) {k : ℕ} {y : ℝ}
    (hy : p k = some y) : c k = some y := by
  rcases hp k with hn | hc
  · rw [hn] at hy
    exact absurd hy (by simp)
  · rw [← hc]
    exact hy

/-- **The missed samples of one output sample that plays the source.** Let
`t` be the number of output samples just before it that play nothing. The
missed samples counted at it are at most `u * t`, plus `2 * J` times the
number of discontinuities since the last output sample that played the
source, plus the sum of `stepOver` of the target's steps since then. -/
theorem Follows.missedAt_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (hu1 : u < 1) (hJ : 1 ≤ J)
    (hp : ∀ k, p k = none ∨ p k = c k) {K : ℕ} {y : ℝ} (hy : p K = some y) :
    (missedAt p K : ℝ) ≤ u * trailing p K
      + 2 * J * ∑ k ∈ Finset.Ico (K - 1 - trailing p K) K, (discontinuityAt p k : ℝ)
      + ∑ i ∈ Finset.Ico (K - 1 - trailing p K) K, stepOver u ξ i := by
  have hJ0 : 0 ≤ J := by linarith
  have huJ : u ≤ J := by linarith
  have hsum0 : 0 ≤ ∑ i ∈ Finset.Ico (K - 1 - trailing p K) K, stepOver u ξ i :=
    Finset.sum_nonneg fun i _ => stepOver_nonneg u ξ i
  have hdisc0 : 0 ≤ ∑ k ∈ Finset.Ico (K - 1 - trailing p K) K, (discontinuityAt p k : ℝ) :=
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ trailing p K := Nat.cast_nonneg _
  have hcK : c K = some y := follower_of_played hp hy
  cases hlast : lastPlayed p K with
  | none =>
    rw [missedAt_of_lastPlayed_none hy hlast, Nat.cast_zero]
    nlinarith
  | some x =>
    obtain ⟨htK, hj⟩ := lastPlayed_some hlast
    have hcj : c (K - 1 - trailing p K) = some x := follower_of_played hp hj
    have hmiss := missedAt_le_abs hy hlast
    rcases Nat.eq_zero_or_pos (trailing p K) with ht | ht
    · -- The output sample just before played the source.
      rw [ht] at hcj hj hmiss hdisc0 hsum0 ⊢
      have hK : K - 1 - 0 + 1 = K := by omega
      have hcK' : c (K - 1 - 0 + 1) = some y := by
        rw [hK]
        exact hcK
      have hpK' : p (K - 1 - 0 + 1) = some y := by
        rw [hK]
        exact hy
      have hIco : Finset.Ico (K - 1 - 0) K = {K - 1 - 0} := by
        ext i
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      rw [hIco, Finset.sum_singleton] at hdisc0 hsum0 ⊢
      rw [Finset.sum_singleton]
      simp only [Nat.cast_zero, zero_add, mul_zero] at hmiss ⊢
      have hX := h.target_of_some hcK'
      have hstep := h.step (K - 1 - 0)
      rw [hcj, hX] at hstep
      have hgap := hcK'
      rw [hstep] at hgap
      obtain ⟨-, h2, h3⟩ := followStep_gap hgap
      rcases le_or_gt |ξ (K - 1 - 0 + 1) - x - 1| J with hle | hgt
      · -- No jump: the step is within `u`, and nothing is missed.
        have hsmall := h2 hu hle
        have hlt : (missedAt p K : ℝ) < 1 := by linarith
        have hzero : missedAt p K = 0 := by
          have : missedAt p K < 1 := by exact_mod_cast hlt
          omega
        rw [hzero, Nat.cast_zero]
        nlinarith
      · -- A jump: it is a discontinuity, of at most `J` plus `stepOver`.
        have hyx := h3 hgt
        have hd := h.dist_le huJ hcj
        have habs := abs_le_add_stepOver u ξ (K - 1 - 0)
        have htri : |ξ (K - 1 - 0 + 1) - x - 1|
            ≤ |ξ (K - 1 - 0 + 1) - ξ (K - 1 - 0) - 1| + |x - ξ (K - 1 - 0)| := by
          have e : ξ (K - 1 - 0 + 1) - x - 1
              = (ξ (K - 1 - 0 + 1) - ξ (K - 1 - 0) - 1) - (x - ξ (K - 1 - 0)) := by ring
          rw [e]
          exact abs_sub _ _
        have hnc : ¬ (x < y ∧ y < x + 2) := by
          rintro ⟨h4, h5⟩
          rw [hyx] at h4 h5
          have : |ξ (K - 1 - 0 + 1) - x - 1| < 1 := by
            rw [abs_lt]
            constructor <;> linarith
          linarith
        have hbreak : discontinuityAt p (K - 1 - 0) = 1 :=
          discontinuityAt_of_not_continuous hj hpK' hnc
        rw [hbreak, Nat.cast_one]
        rw [hyx] at hmiss
        linarith
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
          ≤ ∑ i ∈ Finset.Ico (K - 1 - trailing p K) K, (u + stepOver u ξ i) :=
        Finset.sum_le_sum fun i _ => abs_le_add_stepOver u ξ i
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
the sum of `stepOver` of the target's steps before `K`. -/
theorem Follows.sum_missedAt_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (hu1 : u < 1)
    (hJ : 1 ≤ J) (hp : ∀ k, p k = none ∨ p k = c k) (K : ℕ) :
    ∑ k ∈ Finset.range K, (missedAt p k : ℝ)
      ≤ (1 + u) * ∑ k ∈ Finset.range K, (missingAt p k : ℝ)
        + 2 * J * ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ)
        + ∑ i ∈ Finset.range K, stepOver u ξ i := by
  have hJ0 : 0 ≤ J := by linarith
  have hinv : ∀ K, ∑ k ∈ Finset.range K, (missedAt p k : ℝ)
      ≤ (1 + u) * ∑ k ∈ Finset.range K, (missingAt p k : ℝ) - u * trailing p K
        + 2 * J * ∑ k ∈ Finset.range (K - 1 - trailing p K), (discontinuityAt p k : ℝ)
        + ∑ i ∈ Finset.range (K - 1 - trailing p K), stepOver u ξ i := by
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
        have hsplit := Finset.sum_Ico_consecutive (fun i => stepOver u ξ i)
          (Nat.zero_le (K - 1 - trailing p K)) hle
        have hsplit' := Finset.sum_Ico_consecutive (fun k => (discontinuityAt p k : ℝ))
          (Nat.zero_le (K - 1 - trailing p K)) hle
        rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hsplit hsplit'
        rw [e2, trailing_succ_some hK, e3]
        push_cast
        nlinarith
  have h1 := hinv K
  have h2 : (0 : ℝ) ≤ u * trailing p K := mul_nonneg hu (Nat.cast_nonneg _)
  have h3 : ∑ i ∈ Finset.range (K - 1 - trailing p K), stepOver u ξ i
      ≤ ∑ i ∈ Finset.range K, stepOver u ξ i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      fun i _ _ => stepOver_nonneg u ξ i
  have h4 : ∑ k ∈ Finset.range (K - 1 - trailing p K), (discontinuityAt p k : ℝ)
      ≤ ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      fun i _ _ => Nat.cast_nonneg _
  nlinarith

/-- **The discontinuity of one output sample.** It is at most one if the
next output sample plays nothing, plus one if the follower jumps. -/
theorem Follows.discontinuityAt_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (hu1 : u < 1)
    (hp : ∀ k, p k = none ∨ p k = c k) (k : ℕ) :
    (discontinuityAt p k : ℝ) ≤ missingAt p (k + 1) + jumpAt J ξ c k := by
  have hmis : (0 : ℝ) ≤ missingAt p (k + 1) := Nat.cast_nonneg _
  have hjmp : (0 : ℝ) ≤ jumpAt J ξ c k := Nat.cast_nonneg _
  cases hk : p k with
  | none =>
    rw [discontinuityAt_of_none hk, Nat.cast_zero]
    linarith
  | some y =>
    have hck : c k = some y := follower_of_played hp hk
    cases hk1 : p (k + 1) with
    | none =>
      have e : missingAt p (k + 1) = 1 := by simp [missingAt, hk1]
      rw [discontinuityAt_of_some_none hk hk1, e]
      push_cast
      linarith
    | some y' =>
      have hck1 : c (k + 1) = some y' := follower_of_played hp hk1
      by_cases hcont : y < y' ∧ y' < y + 2
      · rw [discontinuityAt_of_continuous hk hk1 hcont, Nat.cast_zero]
        linarith
      · rw [discontinuityAt_of_not_continuous hk hk1 hcont, Nat.cast_one]
        have hbig : 1 ≤ |y' - y - 1| := by
          rw [not_and_or, not_lt, not_lt] at hcont
          rcases hcont with h1 | h1
          · rw [abs_of_nonpos (by linarith)]
            linarith
          · rw [abs_of_nonneg (by linarith)]
            linarith
        have hX := h.target_of_some hck1
        have hstep := h.step k
        rw [hck, hX] at hstep
        have hgap := hck1
        rw [hstep] at hgap
        obtain ⟨-, h2, -⟩ := followStep_gap hgap
        have hjump : J < |ξ (k + 1) - y - 1| := by
          by_contra hnot
          have := h2 hu (not_lt.mp hnot)
          linarith
        rw [jumpAt_of_some hck hck1, ite_eq_left hjump]
        push_cast
        linarith

/-- **The discontinuities of playback that follows a target.** For
`0 ≤ u < 1` and `u ≤ J`: `J - u` times the discontinuities counted at the
output samples before `K` is at most `J - u` times the number of the output
samples up to `K` that play nothing, plus the sum of `stepOver` of the
target's steps before `K`. -/
theorem Follows.sum_discontinuityAt_le (h : Follows u J ξ X c) (hu : 0 ≤ u) (hu1 : u < 1)
    (huJ : u ≤ J) (hp : ∀ k, p k = none ∨ p k = c k) (K : ℕ) :
    (J - u) * ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ)
      ≤ (J - u) * ∑ k ∈ Finset.range (K + 1), (missingAt p k : ℝ)
        + ∑ i ∈ Finset.range K, stepOver u ξ i := by
  have hJu : 0 ≤ J - u := by linarith
  have h1 : ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ)
      ≤ ∑ k ∈ Finset.range K, ((missingAt p (k + 1) : ℝ) + (jumpAt J ξ c k : ℝ)) :=
    Finset.sum_le_sum fun k _ => h.discontinuityAt_le hu hu1 hp k
  rw [Finset.sum_add_distrib] at h1
  have h2 : ∑ k ∈ Finset.range K, (missingAt p (k + 1) : ℝ)
      ≤ ∑ k ∈ Finset.range (K + 1), (missingAt p k : ℝ) := by
    rw [Finset.sum_range_succ' (fun k => (missingAt p k : ℝ)) K]
    have : (0 : ℝ) ≤ missingAt p 0 := Nat.cast_nonneg _
    linarith
  have h3 := h.sum_jumpAt_le K
  have h4 := followDist_nonneg ξ c K
  have h12 : ∑ k ∈ Finset.range K, (discontinuityAt p k : ℝ)
      ≤ ∑ k ∈ Finset.range (K + 1), (missingAt p k : ℝ)
        + ∑ k ∈ Finset.range K, (jumpAt J ξ c k : ℝ) := by linarith
  have h5 := mul_le_mul_of_nonneg_left h12 hJu
  rw [mul_add] at h5
  linarith

end Unisono.Spec
