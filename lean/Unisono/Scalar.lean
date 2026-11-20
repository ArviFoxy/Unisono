/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Aeneas
import all Aeneas.Std.Scalar.SaturatingOps

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

/-! ## Saturating operations

The library gives these operations as bit patterns. Here are their values,
and the facts that let a proof step over a call of one of them. -/

theorem clamp_bmod (n : ℕ) (hn : n ≠ 0) (v : ℤ) :
    (max (-2^(n-1)) (min (2^(n-1) - 1) v)).bmod (2^n)
      = max (-2^(n-1)) (min (2^(n-1) - 1) v) := by
  apply Int.bmod_pow2_eq_of_inBounds' n _ hn
  · exact le_max_left _ _
  · have h1 : min (2^(n-1) - 1) v ≤ (2:ℤ)^(n-1) - 1 := min_le_left _ _
    have h2 : (0:ℤ) < 2^(n-1) := by positivity
    have h3 : max (-2^(n-1)) (min (2^(n-1) - 1) v) ≤ (2:ℤ)^(n-1) - 1 := max_le (by omega) h1
    omega

theorem I64.saturating_sub_val (x y : I64) :
    (core.num.I64.saturating_sub x y).val = max (-2^63) (min (2^63 - 1) (x.val - y.val)) := by
  simp only [core.num.I64.saturating_sub, IScalar.saturating_sub, IScalar.val, BitVec.toInt_ofInt]
  have := clamp_bmod 64 (by norm_num) (x.bv.toInt - y.bv.toInt)
  simpa [IScalar.min, IScalar.max, I64.min, I64.max, I64.numBits] using this

theorem I64.saturating_add_val (x y : I64) :
    (core.num.I64.saturating_add x y).val = max (-2^63) (min (2^63 - 1) (x.val + y.val)) := by
  simp only [core.num.I64.saturating_add, IScalar.saturating_add, IScalar.val, BitVec.toInt_ofInt]
  have := clamp_bmod 64 (by norm_num) (x.bv.toInt + y.bv.toInt)
  simpa [IScalar.min, IScalar.max, I64.min, I64.max, I64.numBits] using this

theorem I128.saturating_sub_val (x y : I128) :
    (core.num.I128.saturating_sub x y).val
      = max (-2^127) (min (2^127 - 1) (x.val - y.val)) := by
  simp only [core.num.I128.saturating_sub, IScalar.saturating_sub, IScalar.val,
    BitVec.toInt_ofInt]
  have := clamp_bmod 128 (by norm_num) (x.bv.toInt - y.bv.toInt)
  simpa [IScalar.min, IScalar.max, I128.min, I128.max, I128.numBits] using this

theorem I128.saturating_add_val (x y : I128) :
    (core.num.I128.saturating_add x y).val
      = max (-2^127) (min (2^127 - 1) (x.val + y.val)) := by
  simp only [core.num.I128.saturating_add, IScalar.saturating_add, IScalar.val,
    BitVec.toInt_ofInt]
  have := clamp_bmod 128 (by norm_num) (x.bv.toInt + y.bv.toInt)
  simpa [IScalar.min, IScalar.max, I128.min, I128.max, I128.numBits] using this

theorem usize_max_succ : UScalar.max UScalarTy.Usize + 1 = 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalar.max_def]
  have h : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
  omega

theorem usize_max_eq : UScalar.max UScalarTy.Usize = Usize.max := by
  rw [UScalar.max_def, Usize.max_def, Usize.numBits_def]

/-- A saturating addition that stays in range is the addition. -/
theorem Usize.saturating_add_val (x y : Usize) (h : x.val + y.val ≤ Usize.max) :
    (core.num.Usize.saturating_add x y).val = x.val + y.val := by
  have hm := usize_max_succ
  simp only [core.num.Usize.saturating_add, UScalar.saturating_add, UScalar.val] at *
  rw [BitVec.toNat_ofNat, usize_max_eq, min_eq_right h]
  apply Nat.mod_eq_of_lt
  rw [usize_max_eq] at hm
  omega

/-- A saturating subtraction of unsigned numbers is the subtraction of
natural numbers, which stops at zero. -/
theorem Usize.saturating_sub_val (x y : Usize) :
    (core.num.Usize.saturating_sub x y).val = x.val - y.val := by
  have hx := x.bv.isLt
  simp only [core.num.Usize.saturating_sub, UScalar.saturating_sub, UScalar.val] at *
  rw [BitVec.toNat_ofNat, Nat.zero_max]
  apply Nat.mod_eq_of_lt
  omega

@[step]
theorem I64.saturating_sub_step (x y : I64) :
    lift (core.num.I64.saturating_sub x y) ⦃ r => r = core.num.I64.saturating_sub x y ⦄ := by
  simp [lift]

@[step]
theorem I64.saturating_add_step (x y : I64) :
    lift (core.num.I64.saturating_add x y) ⦃ r => r = core.num.I64.saturating_add x y ⦄ := by
  simp [lift]

@[step]
theorem I128.saturating_sub_step (x y : I128) :
    lift (core.num.I128.saturating_sub x y) ⦃ r => r = core.num.I128.saturating_sub x y ⦄ := by
  simp [lift]

@[step]
theorem I128.saturating_add_step (x y : I128) :
    lift (core.num.I128.saturating_add x y) ⦃ r => r = core.num.I128.saturating_add x y ⦄ := by
  simp [lift]

@[step]
theorem Usize.saturating_add_step (x y : Usize) :
    lift (core.num.Usize.saturating_add x y) ⦃ r => r = core.num.Usize.saturating_add x y ⦄ := by
  simp [lift]

@[step]
theorem Usize.saturating_sub_step (x y : Usize) :
    lift (core.num.Usize.saturating_sub x y) ⦃ r => r = core.num.Usize.saturating_sub x y ⦄ := by
  simp [lift]

end Unisono
