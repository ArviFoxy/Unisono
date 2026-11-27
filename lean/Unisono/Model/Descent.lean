/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Choosing a value step by step, without a model of what comes

A value is chosen again and again, and after each choice a cost of that
choice becomes known. The rule studied here moves the value a small step
against the slope of each cost that becomes known, and keeps it between two
bounds. Its total cost exceeds the total cost of the best fixed value by a
bounded amount plus a share of the number of choices that is proportional
to the step. Nothing is assumed about where the costs come from: the
statement holds for every sequence of costs that are convex in the value,
so it needs no law of the disturbances.

It is meant for the level of the playback: the value is the level, a choice
is made for each stretch of the stream, and the cost of a stretch is known
once the hosts that play have reported what the stretch needed.

* `clampTo`, `clampTo_mem`, `abs_clampTo_sub_le`: moving a value into an
  interval, which brings it no further from any point of the interval.
* `abs_succ_sub_le`: the rule moves the value by at most the step times the
  bound on the slopes.
* `sum_sub_le`: the total cost. The slope of the cost of choice `t` is used
  only `d` choices later, which allows for the time that the reports take.
* `needCost`, `needSlope`, `needCost_sub_le`, `sum_needCost_sub_le`: the
  case of a cost that grows in proportion to the value and to what a need
  exceeds the value by.

No world model is involved, and nothing here is about a solution of the
specification yet.
-/

@[expose] public noncomputable section

namespace Unisono.Model.Descent

/-- The value `v` moved into the interval from `lo` to `hi`: `lo` if it is
below, `hi` if it is above. -/
def clampTo (lo hi v : ℝ) : ℝ :=
  max lo (min hi v)

theorem clampTo_mem {lo hi : ℝ} (h : lo ≤ hi) (v : ℝ) : clampTo lo hi v ∈ Set.Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- Moving a value into an interval brings it no further from any point of
the interval. -/
theorem abs_clampTo_sub_le {lo hi z : ℝ} (hz : z ∈ Set.Icc lo hi) (v : ℝ) :
    |clampTo lo hi v - z| ≤ |v - z| := by
  obtain ⟨hz1, hz2⟩ := hz
  unfold clampTo
  rcases le_total v lo with h1 | h1
  · rw [max_eq_left ((min_le_right _ _).trans h1), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total v hi with h2 | h2
    · rw [min_eq_right h2, max_eq_right h1]
    · rw [min_eq_left h2, max_eq_right (hz1.trans hz2), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith

section Rule

variable {lo hi η G x₀ : ℝ} {d : ℕ} {x g : ℕ → ℝ}

/-- The values that the rule chooses stay in the interval. -/
theorem mem_of_rule (hlohi : lo ≤ hi) (hx₀ : x₀ ∈ Set.Icc lo hi)
    (hinit : ∀ t, t ≤ d → x t = x₀)
    (hstep : ∀ t, x (t + d + 1) = clampTo lo hi (x (t + d) - η * g t)) (t : ℕ) :
    x t ∈ Set.Icc lo hi := by
  by_cases ht : t ≤ d
  · rw [hinit t ht]
    exact hx₀
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + d + 1 := ⟨t - d - 1, by omega⟩
    rw [hstep]
    exact clampTo_mem hlohi _

/-- **The rule moves the value by at most the step times the bound on the
slopes.** The first `d + 1` values are `x₀`; after that, value `t + d + 1`
is value `t + d` minus `η` times the slope `g t`, moved into the interval
from `lo` to `hi`. If every slope is at most `G` in absolute value, two
values in a row differ by at most `η * G`. -/
theorem abs_succ_sub_le (hη : 0 ≤ η) (hlohi : lo ≤ hi) (hx₀ : x₀ ∈ Set.Icc lo hi)
    (hinit : ∀ t, t ≤ d → x t = x₀)
    (hstep : ∀ t, x (t + d + 1) = clampTo lo hi (x (t + d) - η * g t))
    (hg : ∀ t, |g t| ≤ G) (j : ℕ) : |x (j + 1) - x j| ≤ η * G := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0)
  by_cases hj : j + 1 ≤ d
  · rw [hinit (j + 1) hj, hinit j (by omega), sub_self, abs_zero]
    exact mul_nonneg hη hG
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + d := ⟨j - d, by omega⟩
    rw [hstep]
    refine (abs_clampTo_sub_le (mem_of_rule hlohi hx₀ hinit hstep (t + d)) _).trans ?_
    have e : x (t + d) - η * g t - x (t + d) = -(η * g t) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left (hg t) hη

/-- **The total cost of the rule against that of a fixed value.** Let the
values `x t` follow the rule of `abs_succ_sub_le` with the step `η > 0`,
and let `f t` be the cost of choice `t`. Let the slope `g t` bound the cost
of `x t` against that of a fixed value `z` of the interval from above:
`f t (x t) - f t z ≤ g t * (x t - z)`, as a slope of a convex cost does. Let
every slope be at most `G` in absolute value. Then over the first `T`
choices the rule costs at most what `z` costs, plus
`(x₀ - z) ^ 2 / (2 * η)`, plus `η * G ^ 2 * (1 / 2 + d)` for each choice.

The first term does not grow with `T`, so per choice the rule is within
`η * G ^ 2 * (1 / 2 + d)` of every fixed value in the long run. -/
theorem sum_sub_le (hη : 0 < η) (hlohi : lo ≤ hi) (hx₀ : x₀ ∈ Set.Icc lo hi)
    (hinit : ∀ t, t ≤ d → x t = x₀)
    (hstep : ∀ t, x (t + d + 1) = clampTo lo hi (x (t + d) - η * g t))
    (hg : ∀ t, |g t| ≤ G) {f : ℕ → ℝ → ℝ} {z : ℝ} (hz : z ∈ Set.Icc lo hi)
    (hsub : ∀ t, f t (x t) - f t z ≤ g t * (x t - z)) (T : ℕ) :
    ∑ t ∈ Finset.range T, (f t (x t) - f t z)
      ≤ (x₀ - z) ^ 2 / (2 * η) + η * G ^ 2 * T * (1 / 2 + d) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0)
  have hmove := abs_succ_sub_le hη.le hlohi hx₀ hinit hstep hg
  -- A value and the one `i` choices later differ by at most `i` steps.
  have hdrift : ∀ i t, |x t - x (t + i)| ≤ i * (η * G) := by
    intro i
    induction i with
    | zero =>
      intro t
      simp
    | succ i ih =>
      intro t
      have h1 := ih t
      have h2 := hmove (t + i)
      have h3 : |x t - x (t + (i + 1))| ≤ |x t - x (t + i)| + |x (t + i + 1) - x (t + i)| := by
        have e : x t - x (t + (i + 1)) = (x t - x (t + i)) - (x (t + i + 1) - x (t + i)) := by
          rw [show t + (i + 1) = t + i + 1 from rfl]
          ring
        rw [e]
        exact abs_sub _ _
      push_cast
      linarith
  -- One choice.
  have hone : ∀ t, f t (x t) - f t z
      ≤ ((x (t + d) - z) ^ 2 - (x (t + d + 1) - z) ^ 2) / (2 * η)
        + η * G ^ 2 * (1 / 2 + d) := by
    intro t
    have hgt := hg t
    have hg2 : g t ^ 2 ≤ G ^ 2 := by
      rw [← sq_abs (g t)]
      exact pow_le_pow_left₀ (abs_nonneg _) hgt 2
    have hsq : (x (t + d + 1) - z) ^ 2 ≤ (x (t + d) - η * g t - z) ^ 2 := by
      rw [hstep, ← sq_abs (clampTo lo hi (x (t + d) - η * g t) - z),
        ← sq_abs (x (t + d) - η * g t - z)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_clampTo_sub_le hz _) 2
    have hlin : g t * (x (t + d) - z)
        ≤ ((x (t + d) - z) ^ 2 - (x (t + d + 1) - z) ^ 2) / (2 * η) + η * G ^ 2 / 2 := by
      rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hη.le (mul_nonneg hη.le (sub_nonneg.mpr hg2))]
    have hlag : g t * (x t - x (t + d)) ≤ G * (d * (η * G)) := by
      have h1 : g t * (x t - x (t + d)) ≤ |g t| * |x t - x (t + d)| := by
        rw [← abs_mul]
        exact le_abs_self _
      exact h1.trans (mul_le_mul hgt (hdrift d t) (abs_nonneg _) hG)
    have hsplit : g t * (x t - z) = g t * (x (t + d) - z) + g t * (x t - x (t + d)) := by
      ring
    have h := hsub t
    rw [hsplit] at h
    have e : η * G ^ 2 * (1 / 2 + (d : ℝ)) = η * G ^ 2 / 2 + G * (d * (η * G)) := by ring
    rw [e]
    linarith
  -- All the choices: the squares cancel in pairs.
  have hall : ∀ T : ℕ, ∑ t ∈ Finset.range T, (f t (x t) - f t z)
      + (x (T + d) - z) ^ 2 / (2 * η)
      ≤ (x₀ - z) ^ 2 / (2 * η) + η * G ^ 2 * T * (1 / 2 + d) := by
    intro T
    induction T with
    | zero =>
      rw [Finset.sum_range_zero, Nat.zero_add, hinit d le_rfl]
      simp
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have h1 := hone T
      have e1 : ((x (T + d) - z) ^ 2 - (x (T + d + 1) - z) ^ 2) / (2 * η)
          = (x (T + d) - z) ^ 2 / (2 * η) - (x (T + d + 1) - z) ^ 2 / (2 * η) := by ring
      rw [e1] at h1
      have e2 : T + 1 + d = T + d + 1 := by omega
      rw [e2]
      push_cast
      have e3 : η * G ^ 2 * ((T : ℝ) + 1) * (1 / 2 + (d : ℝ))
          = η * G ^ 2 * T * (1 / 2 + d) + η * G ^ 2 * (1 / 2 + d) := by ring
      rw [e3]
      linarith
  have hnn : 0 ≤ (x (T + d) - z) ^ 2 / (2 * η) := by positivity
  linarith [hall T]

end Rule

/-- **What a stretch costs at the value `l` when its need is `y`**: `a` for
each unit of the value, and `c` for each unit by which the need exceeds the
value. For the level of a playback: `a` is what a second of latency costs
over the stretch, and `c` what a second of missed audio costs. -/
def needCost (a c y l : ℝ) : ℝ :=
  a * l + c * max (y - l) 0

/-- A slope of `needCost` at `l`: `a`, minus `c` where the need exceeds the
value. -/
def needSlope (a c y l : ℝ) : ℝ :=
  a - if l < y then c else 0

/-- The slope of `needCost` is at most `max a c` in absolute value, for
`a ≥ 0` and `c ≥ 0`. -/
theorem abs_needSlope_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (y l : ℝ) :
    |needSlope a c y l| ≤ max a c := by
  unfold needSlope
  split_ifs
  · rw [abs_le]
    constructor
    · linarith [le_max_right a c]
    · linarith [le_max_left a c]
  · rw [sub_zero, abs_of_nonneg ha]
    exact le_max_left a c

/-- **`needCost` lies above its slope line**: against any other value `z`,
the cost at `l` exceeds the cost at `z` by at most the slope at `l` times
`l - z`, for `c ≥ 0`. -/
theorem needCost_sub_le {c : ℝ} (hc : 0 ≤ c) (a y l z : ℝ) :
    needCost a c y l - needCost a c y z ≤ needSlope a c y l * (l - z) := by
  unfold needCost needSlope
  have hz : y - z ≤ max (y - z) 0 := le_max_left _ _
  have hz0 : 0 ≤ max (y - z) 0 := le_max_right _ _
  split_ifs with h
  · rw [max_eq_left (by linarith)]
    nlinarith
  · rw [max_eq_right (by linarith)]
    nlinarith

/-- **The rule applied to needs.** Let the values `x t` follow the rule of
`abs_succ_sub_le` with the step `η > 0` and the slopes of `needCost` for
the needs `y t`, each used `d` choices later, with `a ≥ 0` and `c ≥ 0`. Then
over the first `T` stretches the rule costs at most what any fixed value
`z` of the interval costs, plus `(x₀ - z) ^ 2 / (2 * η)`, plus
`η * (max a c) ^ 2 * (1 / 2 + d)` for each stretch. Nothing is assumed about
the needs. -/
theorem sum_needCost_sub_le {lo hi η x₀ a c : ℝ} {d : ℕ} {x y : ℕ → ℝ} (hη : 0 < η)
    (hlohi : lo ≤ hi) (ha : 0 ≤ a) (hc : 0 ≤ c) (hx₀ : x₀ ∈ Set.Icc lo hi)
    (hinit : ∀ t, t ≤ d → x t = x₀)
    (hstep : ∀ t, x (t + d + 1)
      = clampTo lo hi (x (t + d) - η * needSlope a c (y t) (x t)))
    {z : ℝ} (hz : z ∈ Set.Icc lo hi) (T : ℕ) :
    ∑ t ∈ Finset.range T, (needCost a c (y t) (x t) - needCost a c (y t) z)
      ≤ (x₀ - z) ^ 2 / (2 * η) + η * max a c ^ 2 * T * (1 / 2 + d) :=
  sum_sub_le (g := fun t => needSlope a c (y t) (x t)) (f := fun t => needCost a c (y t)) hη
    hlohi hx₀ hinit hstep (fun t => abs_needSlope_le ha hc (y t) (x t)) hz
    (fun t => needCost_sub_le hc a (y t) (x t) z) T

end Unisono.Model.Descent
