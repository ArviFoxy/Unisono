/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.FollowerSteps

/-!
# The follower of a target that stays near a regular sequence

The position that a solution chooses for an output sample comes from
estimates, and an estimate changes a little from one request of a playback
device to the next. So the steps of the chosen position are not all within
the step bound `u` of one frame, even when nothing disturbs the stream.
This file shows that the follower (`followStep`) removes such changes.

Let `ref` be a sequence of positions whose steps are within `u - η` of one
frame, and let the chosen position stay within `ν` of `ref`, over a stretch
of output samples.

* `followStep_near`: one step without a jump brings the follower's distance
  from `ref` down by `η`, or to at most `ν`.
* `followStep_near_of_dist_le`: once that distance is at most `J - u - ν`,
  the next step is not a jump, the follower advances by one frame within
  `u`, and its distance from `ref` falls again.
* `followed_near_dist_le`: from any value at the start of the stretch, the
  distance is at most `max (J + ν + u - (j + 2) * η) (J - u - ν)` after
  `j + 1` output samples. A jump puts the follower on the chosen position,
  which is within `ν`.
* `followed_near_settles`: after `N + 1` output samples, where
  `2 * u + 2 * ν ≤ N * η`, the follower advances by one frame within `u` at
  every output sample of the stretch, and `j` output samples later its
  distance from `ref` is at most `max (J - u - ν - j * η) ν`.

So in such a stretch playback breaks at most at its first `N + 1` output
samples, and afterwards the played position is within `ν` of `ref` once
`(J - u - 2 * ν) / η` further output samples have passed.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- From a previous value and a chosen position the follower gives a
position. -/
theorem exists_followStep_eq_some (u J y x : ℝ) :
    ∃ z, followStep u J (some y) (some x) = some z := by
  cases h : followStep u J (some y) (some x) with
  | none => exact absurd (followStep_eq_none h) (by simp)
  | some z => exact ⟨z, rfl⟩

/-- **One step of the follower when the chosen position is near a regular
sequence.** Let the sequence go from `r` to `r'` by one frame within
`u - η`, let the chosen position `x'` be within `ν` of `r'`, and let the
follower hold `y`, with `x'` within `J` frames of one frame after `y`, so
that the step is not a jump. Then what the follower gives is at most
`max (|y - r| - η) ν` from `r'`. -/
theorem followStep_near {u J η ν y x' r r' z : ℝ} (hstep : |r' - r - 1| ≤ u - η)
    (hx : |x' - r'| ≤ ν) (h : followStep u J (some y) (some x') = some z)
    (hnojump : |x' - y - 1| ≤ J) : |z - r'| ≤ max (|y - r| - η) ν := by
  obtain ⟨hs1, hs2⟩ := abs_le.mp hstep
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have hle1 := le_abs_self (y - r)
  have hle2 := neg_abs_le (y - r)
  have hm1 := le_max_left (|y - r| - η) ν
  have hm2 := le_max_right (|y - r| - η) ν
  simp only [followStep] at h
  by_cases h3 : |x' - y - 1| ≤ u
  · rw [ite_eq_left h3] at h
    obtain rfl := Option.some.inj h
    exact hx.trans hm2
  · rw [ite_eq_right h3, ite_eq_left hnojump] at h
    obtain rfl := Option.some.inj h
    have h7 := not_le.mp h3
    by_cases h5 : y + 1 < x'
    · rw [ite_eq_left h5]
      have h6 : u < x' - y - 1 := by rwa [abs_of_pos (by linarith)] at h7
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    · rw [ite_eq_right h5]
      have h6 : u < -(x' - y - 1) := by rwa [abs_of_nonpos (by linarith)] at h7
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩

/-- **A step of the follower that is close enough to the sequence is not a
jump.** In the setting of `followStep_near`, for `η ≥ 0` and `u ≥ 0`, let
the follower's value `y` be at most `D` from `r`, with `D ≤ J - u - ν`.
Then what the follower gives is one frame after `y` within `u`, and at most
`max (D - η) ν` from `r'`. -/
theorem followStep_near_of_dist_le {u J η ν y x' r r' z D : ℝ} (hη : 0 ≤ η) (hu : 0 ≤ u)
    (hstep : |r' - r - 1| ≤ u - η) (hx : |x' - r'| ≤ ν) (hy : |y - r| ≤ D)
    (hD : D ≤ J - u - ν) (h : followStep u J (some y) (some x') = some z) :
    |z - y - 1| ≤ u ∧ |z - r'| ≤ max (D - η) ν := by
  have hnojump : |x' - y - 1| ≤ J := by
    have e : x' - y - 1 = (x' - r') + (r' - r - 1) + -(y - r) := by ring
    rw [e]
    have h1 := abs_add_le ((x' - r') + (r' - r - 1)) (-(y - r))
    have h2 := abs_add_le (x' - r') (r' - r - 1)
    rw [abs_neg] at h1
    linarith
  refine ⟨(followStep_gap h).2.1 hu hnojump, ?_⟩
  exact (followStep_near hstep hx h hnojump).trans
    (max_le_max (by linarith) le_rfl)

/-- **The follower's distance from a regular sequence, from any start.**
Over the output samples from `k₀` to `k₁`, let the follower `Y` take each
value from the one before and from the chosen position `X`; let the chosen
position exist after `k₀` and stay within `ν` of `ref`; and let `ref`
advance by one frame within `u - η`, with `η ≥ 0` and `u + 2 * ν ≤ J`. Then
`j + 1` output samples after `k₀` the follower has a value, at most
`max (J + ν + u - (j + 2) * η) (J - u - ν)` from `ref`, whatever it held at
`k₀`. -/
theorem followed_near_dist_le {u J η ν : ℝ} (hη : 0 ≤ η) (hJ : u + 2 * ν ≤ J)
    {X Y : ℕ → Option ℝ} {ref : ℕ → ℝ} {k₀ k₁ : ℕ}
    (hY : ∀ k, k₀ ≤ k → k < k₁ → Y (k + 1) = followStep u J (Y k) (X (k + 1)))
    (hX : ∀ k, k₀ < k → k ≤ k₁ → ∃ x, X k = some x ∧ |x - ref k| ≤ ν)
    (href : ∀ k, k₀ ≤ k → k < k₁ → |ref (k + 1) - ref k - 1| ≤ u - η) :
    ∀ j : ℕ, k₀ + (j + 1) ≤ k₁ → ∃ y, Y (k₀ + (j + 1)) = some y
      ∧ |y - ref (k₀ + (j + 1))| ≤ max (J + ν + u - ((j : ℝ) + 2) * η) (J - u - ν) := by
  have hν : ν ≤ J - u - ν := by linarith
  -- One step from a previous value, a jump or not.
  have hone : ∀ (k : ℕ) (y : ℝ), k₀ ≤ k → k < k₁ → Y k = some y →
      ∃ z, Y (k + 1) = some z ∧ (|z - ref (k + 1)| ≤ ν
        ∨ (|z - ref (k + 1)| ≤ max (|y - ref k| - η) ν ∧ |y - ref k| ≤ J + ν + (u - η))) := by
    intro k y hk0 hk1 hy
    obtain ⟨x', hx', hxν⟩ := hX (k + 1) (by omega) (by omega)
    have hstep := href k hk0 hk1
    have hYk := hY k hk0 hk1
    rw [hx', hy] at hYk
    obtain ⟨z, hz⟩ := exists_followStep_eq_some u J y x'
    rw [hz] at hYk
    refine ⟨z, hYk, ?_⟩
    by_cases hnj : |x' - y - 1| ≤ J
    · refine Or.inr ⟨followStep_near hstep hxν hz hnj, ?_⟩
      have e : y - ref k = -(x' - y - 1) + (x' - ref (k + 1)) + (ref (k + 1) - ref k - 1) := by
        ring
      rw [e]
      have h1 := abs_add_le (-(x' - y - 1) + (x' - ref (k + 1))) (ref (k + 1) - ref k - 1)
      have h2 := abs_add_le (-(x' - y - 1)) (x' - ref (k + 1))
      rw [abs_neg] at h2
      linarith
    · have hzx : z = x' := (followStep_gap hz).2.2 (not_le.mp hnj)
      rw [hzx]
      exact Or.inl hxν
  intro j
  induction j with
  | zero =>
    intro hk
    cases hprev : Y k₀ with
    | none =>
      obtain ⟨x', hx', hxν⟩ := hX (k₀ + 1) (by omega) (by omega)
      have hYk := hY k₀ le_rfl (by omega)
      rw [hx', hprev, followStep_none_left] at hYk
      exact ⟨x', hYk, hxν.trans (hν.trans (le_max_right _ _))⟩
    | some y =>
      obtain ⟨z, hz, h1 | ⟨h1, h2⟩⟩ := hone k₀ y le_rfl (by omega) hprev
      · exact ⟨z, hz, h1.trans (hν.trans (le_max_right _ _))⟩
      · refine ⟨z, hz, h1.trans (max_le (le_max_of_le_left ?_) (hν.trans (le_max_right _ _)))⟩
        push_cast
        linarith
  | succ j ih =>
    intro hk
    obtain ⟨y, hy, hyb⟩ := ih (by omega)
    obtain ⟨z, hz, h1 | ⟨h1, -⟩⟩ := hone (k₀ + (j + 1)) y (by omega) (by omega) hy
    · exact ⟨z, hz, h1.trans (hν.trans (le_max_right _ _))⟩
    · refine ⟨z, hz, h1.trans (max_le ?_ (hν.trans (le_max_right _ _)))⟩
      rcases le_max_iff.mp hyb with h3 | h3
      · refine le_max_of_le_left ?_
        push_cast
        linarith
      · exact le_max_of_le_right (by linarith)

/-- **The follower settles on a chosen position that stays near a regular
sequence.** In the setting of `followed_near_dist_le`, with `u ≥ 0`, let
`N` output samples be enough for `2 * u + 2 * ν ≤ N * η`. Then at every
output sample of the stretch that is `N + 1 + j` after `k₀`:

* the follower has a value, at most `max (J - u - ν - j * η) ν` from `ref`;
* if the stretch goes on, the follower's next value is one frame after this
  one within `u`: playback does not break. -/
theorem followed_near_settles {u J η ν : ℝ} (hη : 0 ≤ η) (hu : 0 ≤ u) (hJ : u + 2 * ν ≤ J)
    {X Y : ℕ → Option ℝ} {ref : ℕ → ℝ} {k₀ k₁ : ℕ}
    (hY : ∀ k, k₀ ≤ k → k < k₁ → Y (k + 1) = followStep u J (Y k) (X (k + 1)))
    (hX : ∀ k, k₀ < k → k ≤ k₁ → ∃ x, X k = some x ∧ |x - ref k| ≤ ν)
    (href : ∀ k, k₀ ≤ k → k < k₁ → |ref (k + 1) - ref k - 1| ≤ u - η)
    {N : ℕ} (hN : 2 * u + 2 * ν ≤ N * η) :
    ∀ j : ℕ, k₀ + (N + 1 + j) ≤ k₁ → ∃ y, Y (k₀ + (N + 1 + j)) = some y
      ∧ |y - ref (k₀ + (N + 1 + j))| ≤ max (J - u - ν - (j : ℝ) * η) ν
      ∧ (k₀ + (N + 1 + j) < k₁ →
          ∃ y', Y (k₀ + (N + 1 + j) + 1) = some y' ∧ |y' - y - 1| ≤ u) := by
  have hν : ν ≤ J - u - ν := by linarith
  -- The next value, from a value that is close enough.
  have hnext : ∀ (k : ℕ) (y D : ℝ), k₀ ≤ k → k < k₁ → Y k = some y → |y - ref k| ≤ D →
      D ≤ J - u - ν →
      ∃ z, Y (k + 1) = some z ∧ |z - y - 1| ≤ u ∧ |z - ref (k + 1)| ≤ max (D - η) ν := by
    intro k y D hk0 hk1 hy hyD hD
    obtain ⟨x', hx', hxν⟩ := hX (k + 1) (by omega) (by omega)
    have hYk := hY k hk0 hk1
    rw [hx', hy] at hYk
    obtain ⟨z, hz⟩ := exists_followStep_eq_some u J y x'
    rw [hz] at hYk
    obtain ⟨h1, h2⟩ := followStep_near_of_dist_le hη hu (href k hk0 hk1) hxν hyD hD hz
    exact ⟨z, hYk, h1, h2⟩
  -- The bound, without the next value.
  have hbound : ∀ j : ℕ, k₀ + (N + 1 + j) ≤ k₁ → ∃ y, Y (k₀ + (N + 1 + j)) = some y
      ∧ |y - ref (k₀ + (N + 1 + j))| ≤ max (J - u - ν - (j : ℝ) * η) ν := by
    intro j
    induction j with
    | zero =>
      intro hk
      obtain ⟨y, hy, hyb⟩ := followed_near_dist_le hη hJ hY hX href N (by omega)
      refine ⟨y, hy, hyb.trans (max_le (le_max_of_le_left ?_) (le_max_of_le_left ?_))⟩
      · push_cast
        nlinarith
      · push_cast
        linarith
    | succ j ih =>
      intro hk
      obtain ⟨y, hy, hyb⟩ := ih (by omega)
      have hD : max (J - u - ν - (j : ℝ) * η) ν ≤ J - u - ν :=
        max_le (by nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hη]) hν
      obtain ⟨z, hz, -, hzb⟩ := hnext (k₀ + (N + 1 + j)) y _ (by omega) (by omega) hy hyb hD
      refine ⟨z, hz, hzb.trans (max_le ?_ (le_max_right _ _))⟩
      rcases le_max_iff.mp (le_refl (max (J - u - ν - (j : ℝ) * η) ν)) with h3 | h3
      · refine le_max_of_le_left ?_
        push_cast
        linarith
      · exact le_max_of_le_right (by linarith)
  intro j hk
  obtain ⟨y, hy, hyb⟩ := hbound j hk
  refine ⟨y, hy, hyb, fun hlt => ?_⟩
  have hD : max (J - u - ν - (j : ℝ) * η) ν ≤ J - u - ν :=
    max_le (by nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hη]) hν
  obtain ⟨z, hz, hstep, -⟩ := hnext (k₀ + (N + 1 + j)) y _ (by omega) hlt hy hyb hD
  exact ⟨z, hz, hstep⟩

end Unisono.Spec
