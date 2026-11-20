/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Aeneas

/-!
# Machine integers whose operations do not wrap

The core writes its arithmetic with the wrapping operations of Rust, and the
translation gives each of them its value modulo a power of two. The lemmas
here state the value of such an operation as plain integer arithmetic, under
the hypothesis that the plain result fits the type.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Arith

namespace Unisono

theorem I64.max_val : (core.num.I64.MAX).val = 2^63 - 1 := by rfl

theorem I64.min_val : (core.num.I64.MIN).val = -2^63 := by rfl

theorem U32.wrapping_sub_val (x y : U32) (h : y.val ≤ x.val) :
    (core.num.U32.wrapping_sub x y).val = x.val - y.val := by
  have hx := x.hBounds
  simp only [core.num.U32.wrapping_sub_val_eq, UScalar.size] at *
  simp at *
  omega

/-- The product of two 64-bit integers is at most `2^126` in magnitude. -/
theorem I64.mul_val_bounds (a b : I64) :
    -2^126 ≤ a.val * b.val ∧ a.val * b.val ≤ 2^126 := by
  have ha := a.hBounds
  have hb := b.hBounds
  simp at ha hb
  constructor <;> nlinarith

/-- A 128-bit integer that fits 64 bits keeps its value when cast. -/
theorem I128.cast_I64_val (x : I128) (h : -2^63 ≤ x.val ∧ x.val ≤ 2^63 - 1) :
    (IScalar.cast .I64 x).val = x.val := by
  simp only [IScalar.cast_val_eq]
  apply Int.bmod_pow2_eq_of_inBounds' <;> simp <;> omega

theorem I128.wrapping_mul_val (x y : I128)
    (h : -2^127 ≤ x.val * y.val ∧ x.val * y.val < 2^127) :
    (core.num.I128.wrapping_mul x y).val = x.val * y.val := by
  simp only [core.num.I128.wrapping_mul_val_eq]
  apply Int.bmod_pow2_eq_of_inBounds' <;> simp <;> omega

theorem I128.wrapping_add_val (x y : I128)
    (h : -2^127 ≤ x.val + y.val ∧ x.val + y.val < 2^127) :
    (core.num.I128.wrapping_add x y).val = x.val + y.val := by
  simp only [core.num.I128.wrapping_add_val_eq]
  apply Int.bmod_pow2_eq_of_inBounds' <;> simp <;> omega

/-- An arithmetic shift to the right is a division that rounds toward negative infinity. -/
theorem I128.wrapping_shr_val (x : I128) (s : U32) (h : s.val < 128) :
    (core.num.I128.wrapping_shr x s).val = x.val / 2^s.val := by
  simp only [IScalar.val, core.num.I128.wrapping_shr_bv_eq]
  have : s.val % 128 = s.val := Nat.mod_eq_of_lt h
  simp [this, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]

theorem I128.wrapping_shl_one_val (s : U32) (h : s.val < 127) :
    (core.num.I128.wrapping_shl 1#i128 s).val = 2^s.val := by
  simp only [IScalar.val, core.num.I128.wrapping_shl_bv_eq]
  have hmod : s.val % 128 = s.val := Nat.mod_eq_of_lt (by omega)
  have hlt : (2:ℤ)^s.val < 2^127 := by
    exact_mod_cast Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
  have hpos : (0:ℤ) < 2^s.val := by positivity
  simp [hmod, BitVec.toInt_shiftLeft]
  rw [Int.shiftLeft_eq, one_mul]
  exact Int.bmod_pow2_eq_of_inBounds' 128 _ (by norm_num) (by omega) (by omega)

end Unisono
