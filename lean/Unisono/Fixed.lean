/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import UnisonoCore
public import Unisono.Scalar

/-!
# Fixed-point arithmetic

What the functions of `unisono_core::fixed` compute, stated on the integers.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Fixed

/-- `x` limited to the range of a signed 64-bit integer. -/
def clamp64 (x : ℤ) : ℤ := max (-2^63) (min x (2^63 - 1))

/-- `x / 2^s` rounded to the nearest integer, a tie toward positive infinity. -/
def roundShift (x : ℤ) (s : ℕ) : ℤ := ⌊(x : ℚ) / 2^s + 1/2⌋

/-- `roundShift` as a division of integers that rounds toward negative infinity. -/
theorem roundShift_eq_ediv (x : ℤ) (s : ℕ) :
    roundShift x s = (2 * x + 2^s) / 2^(s+1) := by
  unfold roundShift
  have h : (x : ℚ) / 2^s + 1/2 = ((2 * x + 2^s : ℤ) : ℚ) / ((2^(s+1) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  rw [h, Rat.floor_intCast_div_natCast]
  push_cast
  rfl

/-- The rounded value is within half a unit of the exact quotient. -/
theorem roundShift_error (x : ℤ) (s : ℕ) :
    |(roundShift x s : ℚ) - (x : ℚ) / 2^s| ≤ 1/2 := by
  unfold roundShift
  have h1 := Int.floor_le ((x : ℚ) / 2^s + 1/2)
  have h2 := Int.lt_floor_add_one ((x : ℚ) / 2^s + 1/2)
  rw [abs_le]
  constructor <;> linarith

@[step]
theorem saturate_spec (x : Std.I128) :
    fixed.saturate x ⦃ r => r.val = clamp64 x.val ⦄ := by
  unfold fixed.saturate
  step*
  all_goals
    have hi : i.val = 2^63 - 1 := by simp [i_post, I64.rMax]
    simp only [clamp64]
  · have := I64.max_val
    scalar_tac
  · have hi1 : i1.val = -2^63 := by simp [i1_post, I64.rMin]
    have := I64.min_val
    scalar_tac
  · have hi1 : i1.val = -2^63 := by simp [i1_post, I64.rMin]
    rw [I128.cast_I64_val x (by scalar_tac)]
    scalar_tac

theorem roundShift_zero (x : ℤ) : roundShift x 0 = x := by
  rw [roundShift_eq_ediv]
  omega

/-- For a positive shift, rounding adds half a unit and then rounds toward negative infinity. -/
theorem roundShift_eq_add_half (x : ℤ) (s : ℕ) (hs : 0 < s) :
    roundShift x s = (x + 2^(s-1)) / 2^s := by
  rw [roundShift_eq_ediv]
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have h2 : (2:ℤ) * x + 2^(k+1) = 2 * (x + 2^k) := by ring
  have h3 : (2:ℤ)^(k+1+1) = 2 * 2^(k+1) := by ring
  rw [h2, h3, Int.mul_ediv_mul_of_pos _ _ (by norm_num : (0:ℤ) < 2)]
  simp

/-- The value that `mul_shift` hands to `saturate`, for a shift that is already limited. -/
theorem rounded_product_val (a b : Std.I64) (s : Std.U32) (half : Std.I128)
    (hs : s.val ≤ 64)
    (hhalf : half.val = if s.val = 0 then 0 else 2^(s.val - 1)) :
    (core.num.I128.wrapping_shr
        (core.num.I128.wrapping_add
          (core.num.I128.wrapping_mul (IScalar.cast .I128 a) (IScalar.cast .I128 b)) half)
        s).val
      = roundShift (a.val * b.val) s.val := by
  have hab := I64.mul_val_bounds a b
  have hprod : (core.num.I128.wrapping_mul (IScalar.cast .I128 a) (IScalar.cast .I128 b)).val
      = a.val * b.val := by
    rw [I128.wrapping_mul_val _ _ (by simp; omega)]; simp
  have hhalf_bounds : 0 ≤ half.val ∧ half.val ≤ 2^63 := by
    rw [hhalf]
    split
    · norm_num
    · constructor
      · positivity
      · exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : s.val - 1 ≤ 63)
  rw [I128.wrapping_shr_val _ _ (by omega), I128.wrapping_add_val _ _ (by rw [hprod]; omega),
    hprod, hhalf]
  split
  · rename_i h0
    simp [h0, roundShift_zero]
  · rw [roundShift_eq_add_half _ _ (by omega)]

@[step]
theorem mul_shift_spec (a b : Std.I64) (shift : Std.U32) :
    fixed.mul_shift a b shift ⦃ r =>
      r.val = clamp64 (roundShift (a.val * b.val) (min shift.val 64)) ⦄ := by
  unfold fixed.mul_shift
  have hmax : fixed.MAX_SHIFT.val = 64 := by simp [fixed.MAX_SHIFT]
  split <;> step* <;> split <;> step*
  · have hx : x.val = 63 := by
      rw [x_post, U32.wrapping_sub_val _ _ (by scalar_tac)]
      scalar_tac
    have key := rounded_product_val a b fixed.MAX_SHIFT (core.num.I128.wrapping_shl 1#i128 x)
      (by omega) (by rw [I128.wrapping_shl_one_val _ (by omega), hx, hmax]; rfl)
    have hmin : min shift.val 64 = 64 := by scalar_tac
    rw [r_post, i3_post, i2_post, product_post, i_post, i1_post, key, hmax, hmin]
  · have hs : shift.val = 0 := by scalar_tac
    have key := rounded_product_val a b shift 0#i128 (by omega) (by simp [hs])
    have hmin : min shift.val 64 = shift.val := by omega
    rw [r_post, i3_post, i2_post, product_post, i_post, i1_post, key, hmin]
  · have hs : shift.val ≤ 64 := by scalar_tac
    have hpos : 0 < shift.val := by scalar_tac
    have hx : x.val = shift.val - 1 := by
      rw [x_post, U32.wrapping_sub_val _ _ (by scalar_tac)]
      scalar_tac
    have key := rounded_product_val a b shift (core.num.I128.wrapping_shl 1#i128 x)
      hs (by rw [I128.wrapping_shl_one_val _ (by omega), hx]; simp; omega)
    have hmin : min shift.val 64 = shift.val := by omega
    rw [r_post, i3_post, i2_post, product_post, i_post, i1_post, key, hmin]

end Unisono.Fixed
