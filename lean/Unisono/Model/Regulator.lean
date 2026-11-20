/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The regulator, cycle by cycle

The state of the regulator before a cycle of the device is a pair: the
distance `E` by which the position that is read is behind the schedule, and
the correction `v`, the number of frames that the last cycle read beyond what
the schedule advanced. With `a` the gain per second times the length of a
cycle, one cycle is

    v' = (1 - √2 a) v + a² E,        E' = E - v'.

This file is about that recursion over the real numbers. The code computes it
in whole numbers; how far that is from the recursion here is not stated yet.
-/

@[expose] public noncomputable section

namespace Unisono.Model.Regulator

/-- One cycle: the state is the distance behind the schedule and the
correction. -/
def step (a : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - ((1 - Real.sqrt 2 * a) * x.2 + a ^ 2 * x.1),
    (1 - Real.sqrt 2 * a) * x.2 + a ^ 2 * x.1)

/-- A quadratic form of the state that every cycle scales by the same factor.
It is the area spanned by a state and the state after it. -/
def energy (a : ℝ) (x : ℝ × ℝ) : ℝ :=
  a ^ 2 * x.1 ^ 2 + (a ^ 2 - Real.sqrt 2 * a) * x.1 * x.2
    + (1 - Real.sqrt 2 * a) * x.2 ^ 2

/-- A cycle multiplies the energy by `1 - √2 a`, exactly. -/
theorem energy_step (a : ℝ) (x : ℝ × ℝ) :
    energy a (step a x) = (1 - Real.sqrt 2 * a) * energy a x := by
  simp only [energy, step]
  ring

/-- After `k` cycles the energy is `(1 - √2 a)^k` times what it was. -/
theorem energy_iterate (a : ℝ) (x : ℝ × ℝ) (k : ℕ) :
    energy a ((step a)^[k] x) = (1 - Real.sqrt 2 * a) ^ k * energy a x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', energy_step, ih]
    ring

theorem sqrt_two_le : Real.sqrt 2 ≤ 3 / 2 := by
  rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- For a gain of a cycle of at most one half, the energy bounds the distance:
the form is positive definite. -/
theorem distance_le_energy (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 2) (x : ℝ × ℝ) :
    a ^ 2 * x.1 ^ 2 ≤ 12 * energy a x := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 := sqrt_two_le
  set s := Real.sqrt 2 with hsdef
  -- `w` is the factor by which a cycle scales the energy; it is positive
  have hsa : s * a ≤ 3 / 4 := by nlinarith
  have hw : 0 < 1 - s * a := by linarith
  -- times `w`, the difference is a square plus a multiple of the squared distance
  have key : (1 - s * a) * (12 * energy a x - a ^ 2 * x.1 ^ 2)
      = 12 * ((1 - s * a) * x.2 + (a ^ 2 - s * a) * x.1 / 2) ^ 2
        + a ^ 2 * (5 - 5 * (s * a) - 3 * a ^ 2 + 3 * (2 - s ^ 2)) * x.1 ^ 2 := by
    simp only [energy, ← hsdef]
    ring
  have hbracket : 0 ≤ 5 - 5 * (s * a) - 3 * a ^ 2 + 3 * (2 - s ^ 2) := by
    rw [hs]
    nlinarith
  have hnonneg : 0 ≤ (1 - s * a) * (12 * energy a x - a ^ 2 * x.1 ^ 2) := by
    rw [key]
    positivity
  have := nonneg_of_mul_nonneg_right hnonneg hw
  linarith

/-- From any state, the squared distance after `k` cycles is at most twelve
times the energy at the start, shrunk by `(1 - √2 a)^k`. -/
theorem distance_after (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 2) (x : ℝ × ℝ) (k : ℕ) :
    a ^ 2 * ((step a)^[k] x).1 ^ 2 ≤ 12 * (1 - Real.sqrt 2 * a) ^ k * energy a x := by
  have h := distance_le_energy a ha ha' ((step a)^[k] x)
  rw [energy_iterate] at h
  linarith

/-- From rest, where the correction is zero, as after a start or a jump: the
distance after `k` cycles is at most `√12 (1 - √2 a)^(k/2)` times the distance
at the start. Squared, to stay with whole powers. -/
theorem distance_from_rest (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 2) (E : ℝ) (k : ℕ) :
    ((step a)^[k] (E, 0)).1 ^ 2 ≤ 12 * (1 - Real.sqrt 2 * a) ^ k * E ^ 2 := by
  have h := distance_after a ha ha' (E, 0) k
  have he : energy a (E, 0) = a ^ 2 * E ^ 2 := by
    simp [energy]
  rw [he] at h
  have ha2 : 0 < a ^ 2 := by positivity
  have : a ^ 2 * ((step a)^[k] (E, 0)).1 ^ 2
      ≤ a ^ 2 * (12 * (1 - Real.sqrt 2 * a) ^ k * E ^ 2) := by
    linarith
  exact le_of_mul_le_mul_left this ha2

/-! ## A schedule whose pace is wrong -/

/-- One cycle when the schedule advances `d` frames more in each cycle than
the receiver is told. -/
def stepWith (a d : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - ((1 - Real.sqrt 2 * a) * x.2 + a ^ 2 * x.1) + d,
    (1 - Real.sqrt 2 * a) * x.2 + a ^ 2 * x.1)

/-- With a pace that is wrong by `d` frames a cycle, the state moves as it
does without the error, around the point where the distance is `√2 d / a` and
the correction is `d`. The distance therefore tends to `√2 d / a`: in time,
`√2` times the error of the rate over the gain per second. -/
theorem stepWith_shift (a d : ℝ) (ha : a ≠ 0) (y : ℝ × ℝ) :
    stepWith a d (y.1 + Real.sqrt 2 * d / a, y.2 + d)
      = ((step a y).1 + Real.sqrt 2 * d / a, (step a y).2 + d) := by
  simp only [stepWith, step, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-! ## The limit of the pace -/

/-- One cycle when the correction is held within `L` either way. -/
def stepLimited (a L : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - max (-L) (min L ((1 - Real.sqrt 2 * a) * x.2 + a ^ 2 * x.1)),
    max (-L) (min L ((1 - Real.sqrt 2 * a) * x.2 + a ^ 2 * x.1)))

/-- A cycle whose correction is at the upper limit starts at least
`√2 L / a` behind the schedule, and ends `L` nearer to it. So the limit holds
for no more cycles in a row than the distance holds limits. -/
theorem at_limit (a L : ℝ) (ha : 0 < a) (ha' : a ≤ 1 / 2) (hL : 0 < L) (x : ℝ × ℝ)
    (hv : x.2 ≤ L) (h : (stepLimited a L x).2 = L) :
    Real.sqrt 2 * L / a ≤ x.1 ∧ (stepLimited a L x).1 = x.1 - L := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs1 := sqrt_two_le
  have hsa : Real.sqrt 2 * a ≤ 3 / 4 := by nlinarith
  simp only [stepLimited] at h ⊢
  refine ⟨?_, by rw [h]⟩
  -- the correction before the limit is at least `L`
  have hfree : L ≤ (1 - Real.sqrt 2 * a) * x.2 + a ^ 2 * x.1 := by
    by_contra hcon
    have hlt := lt_of_not_ge hcon
    rw [min_eq_right hlt.le] at h
    have : max (-L) ((1 - Real.sqrt 2 * a) * x.2 + a ^ 2 * x.1) < L :=
      max_lt (by linarith) hlt
    linarith
  -- and the correction before it was at most `L`
  have hkeep : (1 - Real.sqrt 2 * a) * x.2 ≤ (1 - Real.sqrt 2 * a) * L :=
    mul_le_mul_of_nonneg_left hv (by linarith)
  rw [div_le_iff₀ ha]
  nlinarith

end Unisono.Model.Regulator
