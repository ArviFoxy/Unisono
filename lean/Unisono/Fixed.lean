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

/-- Rust divides integers rounding toward zero. With the remainder, that gives
the quotient rounded toward negative infinity. -/
theorem ediv_of_tdiv (a b : ℤ) (hb : 0 < b) :
    a / b = if a.tmod b < 0 then a.tdiv b - 1 else a.tdiv b := by
  have h := Int.mul_tdiv_add_tmod a b
  have h1 : a.tmod b < b := Int.tmod_lt_of_pos a hb
  have h2 : -b < a.tmod b := Int.lt_tmod_of_pos a hb
  split
  · exact ((Int.ediv_emod_unique hb).mpr
      ⟨by linarith, by omega, by omega⟩ : a / b = a.tdiv b - 1 ∧ a % b = a.tmod b + b).1
  · exact ((Int.ediv_emod_unique hb).mpr
      ⟨by linarith, by omega, by omega⟩ : a / b = a.tdiv b ∧ a % b = a.tmod b).1

/-- `div_floor_wide` divides by a positive 128-bit number rounding toward
negative infinity, and gives zero for a divisor that is not positive. -/
@[step]
theorem div_floor_wide_spec (a b : Std.I128) :
    fixed.div_floor_wide a b ⦃ r => (0 < b.val → r.val = a.val / b.val) ∧ (b.val ≤ 0 → r.val = 0) ⦄ := by
  unfold fixed.div_floor_wide
  split
  · simp
    scalar_tac
  · have hb : 0 < b.val := by scalar_tac
    have hq := I128.checked_div_bv_spec a b
    have hr := I128.checked_rem_bv_spec a b
    simp only [lift, I128.checked_div_eq, I128.checked_rem_eq]
    cases hq' : core.num.checked_div_IScalar a b <;>
      cases hr' : core.num.checked_rem_IScalar a b <;>
      simp only [hq', hr'] at hq hr ⊢ <;> simp only [bind_ok]
    · omega
    · rcases hq with h | ⟨_, h⟩ <;> omega
    · omega
    · rename_i q r
      obtain ⟨-, -, hqv, -⟩ := hq
      obtain ⟨-, hrv, -⟩ := hr
      have hfloor := ediv_of_tdiv a.val b.val hb
      split
      · have hrneg : a.val.tmod b.val < 0 := by rw [← hrv]; scalar_tac
        have hroom : -2^127 < q.val := by
          have ha : -2^127 ≤ a.val := by scalar_tac
          have hsum := Int.mul_tdiv_add_tmod a.val b.val
          rw [hqv]
          by_contra hcon
          have : b.val * a.val.tdiv b.val ≤ a.val.tdiv b.val := by nlinarith
          omega
        have h1 : (1#i128).val = 1 := by rfl
        have hv := I128.wrapping_sub_val q 1#i128 (by rw [h1]; scalar_tac)
        simp only [WP.spec_ok]
        refine ⟨fun _ => ?_, fun h => by omega⟩
        rw [hv, h1, hfloor, hqv]
        simp only [hrneg, ↓reduceIte]
      · have hrpos : ¬ a.val.tmod b.val < 0 := by rw [← hrv]; scalar_tac
        simp only [WP.spec_ok]
        refine ⟨fun _ => ?_, fun h => by omega⟩
        rw [hfloor, hqv]
        simp only [hrpos, ↓reduceIte]

/-- `div_floor` divides by a positive number rounding toward negative
infinity, which is what `/` on the integers does, and gives zero for a divisor
that is not positive. -/
@[step]
theorem div_floor_spec (a : Std.I128) (b : Std.I64) :
    fixed.div_floor a b ⦃ r => (0 < b.val → r.val = a.val / b.val) ∧ (b.val ≤ 0 → r.val = 0) ⦄ := by
  unfold fixed.div_floor
  step as ⟨i, hi⟩
  have hd : i.val = b.val := by rw [hi, I64.cast_I128_val]
  apply WP.spec_mono (div_floor_wide_spec a i)
  intro r hr
  simpa [hd] using hr

/-- `rem_euclid_wide` returns the Euclidean remainder `a % b` in `0..b` for
positive `b`, and `none` when `b` is zero. -/
@[step]
theorem rem_euclid_wide_spec (a : Std.I128) (b : Std.Usize) :
    fixed.rem_euclid_wide a b ⦃ r =>
      (b.val = 0 → r = none)
      ∧ (0 < b.val → ∃ p, r = some p ∧ (p.val : ℤ) = a.val % (b.val : ℤ) ∧ p.val < b.val) ⦄ := by
  unfold fixed.rem_euclid_wide
  split
  · rename_i h0
    have hb0 : b.val = 0 := by scalar_tac
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => by omega⟩
  · rename_i hne
    have hbpos : 0 < b.val := by scalar_tac
    have hbmax : b.val ≤ Usize.max := by scalar_tac
    step as ⟨divisor, hdiv⟩
    have hdv : divisor.val = b.val := by rw [hdiv, Usize.hcast_I128_val]
    have hdp : (0 : ℤ) < divisor.val := by omega
    have hdb : divisor.val < 2 ^ 127 := by scalar_tac
    have hr := I128.checked_rem_bv_spec a divisor
    simp only [lift, I128.checked_rem_eq]
    cases hr' : core.num.checked_rem_IScalar a divisor <;>
      simp only [hr'] at hr ⊢ <;> simp only [bind_ok]
    · omega
    · rename_i rem
      obtain ⟨-, hrv, -⟩ := hr
      have h1 : a.val.tmod divisor.val < divisor.val := Int.tmod_lt_of_pos a.val hdp
      have h2 : -divisor.val < a.val.tmod divisor.val := Int.lt_tmod_of_pos a.val hdp
      have hsum := Int.mul_tdiv_add_tmod a.val divisor.val
      have hnonneg :
          (if rem < 0#i128 then ok (core.num.I128.wrapping_add rem divisor) else ok rem)
            ⦃ nn => nn.val = a.val % (b.val : ℤ) ∧ 0 ≤ nn.val ∧ nn.val < (b.val : ℤ) ⦄ := by
        split
        · rename_i hlt
          have hneg : rem.val < 0 := by scalar_tac
          have hadd : (core.num.I128.wrapping_add rem divisor).val = rem.val + divisor.val := by
            rw [I128.wrapping_add_val _ _ (by rw [hrv]; omega)]
          have heq : a.val % divisor.val = a.val.tmod divisor.val + divisor.val :=
            ((Int.ediv_emod_unique hdp).mpr
              ⟨by linarith, by omega, by omega⟩ :
                a.val / divisor.val = a.val.tdiv divisor.val - 1
                  ∧ a.val % divisor.val = a.val.tmod divisor.val + divisor.val).2
          rw [WP.spec_ok, hadd, hrv, ← heq, hdv]
          exact ⟨rfl, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
        · rename_i hge
          have hpos : 0 ≤ rem.val := by scalar_tac
          have heq : a.val % divisor.val = a.val.tmod divisor.val :=
            ((Int.ediv_emod_unique hdp).mpr
              ⟨by linarith, by omega, by omega⟩ :
                a.val / divisor.val = a.val.tdiv divisor.val
                  ∧ a.val % divisor.val = a.val.tmod divisor.val).2
          rw [WP.spec_ok, hrv, ← heq, hdv]
          exact ⟨rfl, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
      apply WP.spec_bind hnonneg
      intro nn ⟨hnn_mod, hnn0, hnnlt⟩
      rw [WP.spec_ok]
      have hpv : ((IScalar.hcast .Usize nn).val : ℤ) = nn.val :=
        I128.hcast_Usize_val nn hnn0 (by omega)
      exact ⟨fun h => by omega, fun _ => ⟨IScalar.hcast .Usize nn, rfl, by rw [hpv, hnn_mod], by omega⟩⟩

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

/-! ## The square root

One round of `fixed.root` tries one bit of the root. Before it, `Q` is the
root found so far, a multiple of twice the weight `q` of the bit that is
tried, with `Q² ≤ x < (Q + 2q)²`; `rest` is `x - Q²`, `found` is `2 Q q` and
`bit` is `q²`. The round sets the bit when `(Q + q)² ≤ x`, which it tells by
comparing `rest` with `2 Q q + q²`. The lemmas below give the values that the
round computes; none of its sums leaves the range of the numbers. -/

private theorem shr_one_val (v : Std.I128) :
    (core.num.I128.wrapping_shr v 1#u32).val = v.val / 2 := by
  rw [I128.wrapping_shr_val _ _ (by decide)]
  rfl

private theorem shr_two_val (v : Std.I128) :
    (core.num.I128.wrapping_shr v 2#u32).val = v.val / 4 := by
  rw [I128.wrapping_shr_val _ _ (by decide)]
  rfl

/-- The number that a round compares the rest with. -/
private theorem trial_bounds (Q q : ℤ) (hQ0 : 0 ≤ Q) (hq1 : 1 ≤ q)
    (hfit : Q + 2 * q ≤ 2 ^ 64) :
    0 ≤ 2 * Q * q + q * q ∧ 2 * Q * q + q * q < 2 ^ 127 := by
  have h1 : Q * q ≤ (2 ^ 64 - 2 * q) * q :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : 0 ≤ Q * q := mul_nonneg hQ0 (by linarith)
  have h3 : 0 ≤ (3 * q - 2 ^ 64) ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  · nlinarith

/-- The root found after a round that sets its bit, times the weight of the
bit. -/
private theorem found_bounds (Q q : ℤ) (hQ0 : 0 ≤ Q) (hq1 : 1 ≤ q)
    (hfit : Q + 2 * q ≤ 2 ^ 64) :
    0 ≤ Q * q + q * q ∧ Q * q + q * q < 2 ^ 127 := by
  have h1 : Q * q ≤ (2 ^ 64 - 2 * q) * q :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : 0 ≤ Q * q := mul_nonneg hQ0 (by linarith)
  have h3 : 0 ≤ (q - 2 ^ 63) ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  · nlinarith

private theorem trial_val (found bit : Std.I128) (Q q : ℤ) (hQ0 : 0 ≤ Q) (hq1 : 1 ≤ q)
    (hfit : Q + 2 * q ≤ 2 ^ 64) (hfound : found.val = 2 * Q * q) (hbit : bit.val = q * q) :
    (core.num.I128.wrapping_add found bit).val = 2 * Q * q + q * q := by
  have hb := trial_bounds Q q hQ0 hq1 hfit
  rw [I128.wrapping_add_val _ _ (by rw [hfound, hbit]; constructor <;> linarith), hfound, hbit]

private theorem half_val (found : Std.I128) (Q q : ℤ) (hfound : found.val = 2 * Q * q) :
    (core.num.I128.wrapping_shr found 1#u32).val = Q * q := by
  rw [shr_one_val, hfound, mul_assoc]
  exact Int.mul_ediv_cancel_left _ (by decide)

/-- The weight of the bits not yet tried before a round is twice their weight
after it. -/
private theorem weight_split (n : ℕ) (h : n < 64) :
    (2 : ℤ) ^ (64 - n) = 2 * 2 ^ (64 - (n + 1)) := by
  have hsplit : 64 - n = (64 - (n + 1)) + 1 := by omega
  conv_lhs => rw [hsplit, pow_succ]
  ring

/-- What holds before each round of the root of `x`, of the root `Q` found so
far and the weight `p` of the bits not yet tried. -/
private def RootState (x : ℤ) (rest found bit : ℤ) (Q p : ℤ) : Prop :=
  0 ≤ Q ∧ 1 ≤ p ∧ Q + p ≤ 2 ^ 64 ∧ rest = x - Q * Q ∧ found = Q * p ∧ bit = p * p / 4
    ∧ Q * Q ≤ x ∧ x < (Q + p) * (Q + p)

/-- A round that sets its bit. -/
private theorem state_set (x Q q : ℤ) (hQ0 : 0 ≤ Q) (hq1 : 1 ≤ q)
    (hfit : Q + 2 * q ≤ 2 ^ 64) (hhigh : x < (Q + 2 * q) * (Q + 2 * q))
    (hset : 2 * Q * q + q * q ≤ x - Q * Q) :
    RootState x (x - Q * Q - (2 * Q * q + q * q)) (Q * q + q * q) (q * q / 4) (Q + q) q := by
  refine ⟨by linarith, hq1, by linarith, by ring, by ring, rfl, by nlinarith, ?_⟩
  have : (Q + q + q) * (Q + q + q) = (Q + 2 * q) * (Q + 2 * q) := by ring
  rw [this]
  exact hhigh

/-- A round that leaves its bit unset. -/
private theorem state_unset (x Q q : ℤ) (hQ0 : 0 ≤ Q) (hq1 : 1 ≤ q)
    (hfit : Q + 2 * q ≤ 2 ^ 64) (hlow : Q * Q ≤ x)
    (hunset : x - Q * Q < 2 * Q * q + q * q) :
    RootState x (x - Q * Q) (Q * q) (q * q / 4) Q q := by
  refine ⟨hQ0, hq1, by linarith, rfl, rfl, rfl, hlow, by nlinarith⟩

/-- **The square root is the root, rounded down.** For a positive `x`,
`fixed.root` returns the largest integer whose square is at most `x`; for
any other `x` it returns zero. -/
@[step]
theorem root_spec (x : Std.I128) :
    fixed.root x ⦃ r => 0 ≤ r.val ∧ (x.val ≤ 0 → r.val = 0)
      ∧ (0 < x.val → r.val * r.val ≤ x.val ∧ x.val < (r.val + 1) * (r.val + 1)) ⦄ := by
  unfold fixed.root
  split
  · rename_i hle
    have hx : x.val ≤ 0 := by scalar_tac
    rw [WP.spec_ok]
    exact ⟨le_refl _, fun _ => rfl, fun h => absurd h (not_lt.mpr hx)⟩
  · rename_i hle
    have hx : 0 < x.val := by scalar_tac
    have hxmax : x.val < 2 ^ 127 := by scalar_tac
    unfold fixed.root_loop
    apply loop.spec_decr_nat
      (measure := fun s : Std.I128 × Std.I128 × Std.I128 × Std.U32 => 64 - s.2.2.2.val)
      (inv := fun s : Std.I128 × Std.I128 × Std.I128 × Std.U32 =>
        s.2.2.2.val ≤ 64 ∧ ∃ Q : ℤ,
          RootState x.val s.1.val s.2.1.val s.2.2.1.val Q (2 ^ (64 - s.2.2.2.val)))
    · rintro ⟨rest, found, bit, round⟩ ⟨hround, Q, hstate⟩
      dsimp only at hround hstate
      unfold fixed.root_loop.body
      simp only
      split
      · have hlt : round.val < 64 := by scalar_tac
        have hnext : (core.num.U32.saturating_add round 1#u32).val = round.val + 1 :=
          U32.saturating_add_one_val round 64 hlt (by scalar_tac)
        have hweight := weight_split round.val hlt
        have hq1 : (1 : ℤ) ≤ 2 ^ (64 - (round.val + 1)) := one_le_pow₀ (by norm_num)
        rw [hweight] at hstate
        obtain ⟨q, hq⟩ : ∃ q : ℤ, q = 2 ^ (64 - (round.val + 1)) := ⟨_, rfl⟩
        rw [← hq] at hstate hq1
        obtain ⟨hQ0, -, hfit, hrest, hfound, hbit, hlow, hhigh⟩ := hstate
        have hfound' : found.val = 2 * Q * q := by rw [hfound]; ring
        have hbit' : bit.val = q * q := by
          rw [hbit]
          have : 2 * q * (2 * q) = 4 * (q * q) := by ring
          rw [this]
          exact Int.mul_ediv_cancel_left _ (by decide)
        have htrial := trial_val found bit Q q hQ0 hq1 hfit hfound' hbit'
        have hhalf := half_val found Q q hfound'
        have hquarter : (core.num.I128.wrapping_shr bit 2#u32).val = q * q / 4 := by
          rw [shr_two_val, hbit']
        simp only [lift, bind_ok]
        split
        · rename_i hge
          have hset : 2 * Q * q + q * q ≤ x.val - Q * Q := by
            rw [← htrial, ← hrest]; scalar_tac
          have hb := trial_bounds Q q hQ0 hq1 hfit
          have hf := found_bounds Q q hQ0 hq1 hfit
          have hsquare := mul_self_nonneg Q
          have hsub : (core.num.I128.wrapping_sub rest
              (core.num.I128.wrapping_add found bit)).val
              = x.val - Q * Q - (2 * Q * q + q * q) := by
            rw [I128.wrapping_sub_val _ _ (by rw [htrial, hrest]; constructor <;> linarith),
              htrial, hrest]
          have hadd : (core.num.I128.wrapping_add (core.num.I128.wrapping_shr found 1#u32)
              bit).val = Q * q + q * q := by
            rw [I128.wrapping_add_val _ _ (by rw [hhalf, hbit']; constructor <;> linarith),
              hhalf, hbit']
          simp only [bind_ok, Std.uncurry, WP.spec_ok]
          refine ⟨⟨by rw [hnext]; omega, Q + q, ?_⟩, by rw [hnext]; omega⟩
          rw [hsub, hadd, hquarter, hnext, ← hq]
          exact state_set x.val Q q hQ0 hq1 hfit hhigh hset
        · rename_i hge
          have hunset : x.val - Q * Q < 2 * Q * q + q * q := by
            rw [← htrial, ← hrest]; scalar_tac
          simp only [bind_ok, Std.uncurry, WP.spec_ok]
          refine ⟨⟨by rw [hnext]; omega, Q, ?_⟩, by rw [hnext]; omega⟩
          rw [hhalf, hquarter, hnext, hrest, ← hq]
          exact state_unset x.val Q q hQ0 hq1 hfit hlow hunset
      · have hend : round.val = 64 := by scalar_tac
        rw [hend] at hstate
        obtain ⟨hQ0, -, -, -, hfound, -, hlow, hhigh⟩ := hstate
        have hQ : found.val = Q := by rw [hfound]; norm_num
        rw [WP.spec_ok]
        dsimp only
        rw [hQ]
        exact ⟨hQ0, fun h => absurd hx (not_lt.mpr h), fun _ => ⟨hlow, by simpa using hhigh⟩⟩
    · have hzero : (0#u32).val = 0 := rfl
      have hnone : (0#i128).val = 0 := rfl
      have hbit : fixed.LARGEST_POWER_OF_FOUR.val = 2 ^ 126 := by
        unfold fixed.LARGEST_POWER_OF_FOUR
        rfl
      dsimp only
      rw [hzero, hnone, hbit]
      refine ⟨by norm_num, 0, le_refl _, by norm_num, by norm_num, by ring, by norm_num,
        by norm_num, by simpa using hx.le, ?_⟩
      norm_num
      linarith

/-! ## Saturating products and overflow-free scaled division -/

/-- `x` limited to the range of a signed 128-bit integer. -/
def clamp128 (x : ℤ) : ℤ := max (-2^127) (min x (2^127 - 1))

/-- `saturating_mul_i128` computes `a * b` clamped to the range of `i128`. -/
@[step]
theorem saturating_mul_i128_spec (a b : Std.I128) :
    fixed.saturating_mul_i128 a b ⦃ r => r.val = clamp128 (a.val * b.val) ⦄ := by
  unfold fixed.saturating_mul_i128
  have hm := I128.checked_mul_bv_spec a b
  simp only [lift, I128.checked_mul_eq]
  cases h : core.num.checked_mul_IScalar a b with
  | some prod =>
    rw [h] at hm
    obtain ⟨hv, _⟩ := hm
    simp only [bind_ok, WP.spec_ok, clamp128]
    have hp : -2^127 ≤ prod.val ∧ prod.val ≤ 2^127 - 1 := by scalar_tac
    omega
  | none =>
    rw [h] at hm
    simp only [bind_ok]
    split
    · rename_i hsame
      have hpos : 0 ≤ a.val * b.val := by
        by_cases ha : a < 0#i128
        · have hb : b < 0#i128 := by simpa [ha] using hsame
          have ha' : a.val < 0 := by scalar_tac
          have hb' : b.val < 0 := by scalar_tac
          nlinarith
        · have hb : ¬ b < 0#i128 := by simpa [ha] using hsame
          have ha' : 0 ≤ a.val := by scalar_tac
          have hb' : 0 ≤ b.val := by scalar_tac
          nlinarith
      simp only [WP.spec_ok, clamp128, I128.max_val]
      have hgt : 2^127 - 1 < a.val * b.val := by
        by_contra hle
        exact hm ⟨by simp [I128.min, I128.numBits]; omega, by simp [I128.max, I128.numBits]; omega⟩
      omega
    · rename_i hdiff
      have hneg : a.val * b.val ≤ 0 := by
        by_cases ha : a < 0#i128
        · have hb : ¬ b < 0#i128 := by simpa [ha] using hdiff
          have ha' : a.val < 0 := by scalar_tac
          have hb' : 0 ≤ b.val := by scalar_tac
          nlinarith
        · have hb : b < 0#i128 := by simpa [ha] using hdiff
          have ha' : 0 ≤ a.val := by scalar_tac
          have hb' : b.val < 0 := by scalar_tac
          nlinarith
      simp only [WP.spec_ok, clamp128, I128.min_val]
      have hlt : a.val * b.val < -2^127 := by
        by_contra hge
        exact hm ⟨by simp [I128.min, I128.numBits]; omega, by simp [I128.max, I128.numBits]; omega⟩
      omega

/-- `saturating_mul_i64` computes `a * b` clamped to the range of `i64`. -/
@[step]
theorem saturating_mul_i64_spec (a b : Std.I64) :
    fixed.saturating_mul_i64 a b ⦃ r => r.val = clamp64 (a.val * b.val) ⦄ := by
  unfold fixed.saturating_mul_i64
  have hab := I64.mul_val_bounds a b
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step with saturate_spec i2 as ⟨r, hr⟩
  have hiv : i.val = a.val := by rw [hi, I64.cast_I128_val]
  have hi1v : i1.val = b.val := by rw [hi1, I64.cast_I128_val]
  have hi2v : i2.val = a.val * b.val := by
    rw [hi2, I128.wrapping_mul_val _ _ (by rw [hiv, hi1v]; omega), hiv, hi1v]
  rw [hr, hi2v]

private theorem scale_div_pow2_loop_spec (den : Std.I128) (shift : Std.U32) (rem0 : Std.I128)
    (hden : 0 < den.val) (hshift : shift.val ≤ 64)
    (hrem0 : 0 ≤ rem0.val ∧ rem0.val < den.val) :
    fixed.scale_div_pow2_loop den shift rem0 0#i128 0#u32 ⦃ frac =>
      frac.val = (rem0.val * 2 ^ shift.val) / den.val
      ∧ 0 ≤ frac.val ∧ frac.val < 2 ^ shift.val ⦄ := by
  unfold fixed.scale_div_pow2_loop
  apply loop.spec_decr_nat
    (measure := fun s : Std.I128 × Std.I128 × Std.U32 => shift.val - s.2.2.val)
    (inv := fun s : Std.I128 × Std.I128 × Std.U32 =>
      s.2.2.val ≤ shift.val
      ∧ 0 ≤ s.1.val ∧ s.1.val < den.val
      ∧ 0 ≤ s.2.1.val ∧ s.2.1.val < 2 ^ s.2.2.val
      ∧ s.2.1.val * den.val + s.1.val = rem0.val * 2 ^ s.2.2.val)
  · rintro ⟨rem, frac, bit⟩ ⟨hbit, hr0, hrlt, hf0, hflt, hinv⟩
    dsimp only at hbit hr0 hrlt hf0 hflt hinv
    unfold fixed.scale_div_pow2_loop.body
    simp only
    split
    · have hlt : bit.val < shift.val := by scalar_tac
      have hden_max : den.val < 2 ^ 127 := by scalar_tac
      have hpow_le : (2 : ℤ) ^ (bit.val + 1) ≤ 2 ^ 64 := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : bit.val + 1 ≤ 64)
      have hpow_b : (2 : ℤ) ^ (bit.val + 1) = 2 * 2 ^ bit.val := by rw [pow_succ]; ring
      have hfrac_hi : frac.val * 2 < 2 ^ 64 := by omega
      have hfrac_shl : (core.num.I128.wrapping_shl frac 1#u32).val = frac.val * 2 := by
        have h1 : (1#u32).val = 1 := rfl
        rw [I128.wrapping_shl_val frac 1#u32 (by decide) (by rw [h1]; norm_num; omega)]
        norm_num
      have hhalf : (core.num.I128.wrapping_sub den rem).val = den.val - rem.val :=
        I128.wrapping_sub_val den rem (by omega)
      have hnext : (core.num.U32.saturating_add bit 1#u32).val = bit.val + 1 :=
        U32.saturating_add_one_val bit shift.val hlt (by scalar_tac)
      simp only [lift, bind_ok]
      split
      · rename_i hge
        have hge' : den.val - rem.val ≤ rem.val := by rw [← hhalf]; scalar_tac
        have hrem2 : (core.num.I128.wrapping_sub rem (core.num.I128.wrapping_sub den rem)).val
            = 2 * rem.val - den.val := by
          rw [I128.wrapping_sub_val _ _ (by rw [hhalf]; omega), hhalf]; omega
        have hfrac3 : (core.num.I128.wrapping_add (core.num.I128.wrapping_shl frac 1#u32) 1#i128).val
            = frac.val * 2 + 1 := by
          have h1 : (1#i128).val = 1 := rfl
          rw [I128.wrapping_add_val _ _ (by rw [hfrac_shl, h1]; omega), hfrac_shl, h1]
        simp only [bind_ok, Std.uncurry, WP.spec_ok]
        refine ⟨⟨by omega, by rw [hrem2]; omega, by rw [hrem2]; omega,
          by rw [hfrac3]; omega, by rw [hfrac3, hnext, hpow_b]; omega, ?_⟩, by omega⟩
        rw [hfrac3, hrem2, hnext, hpow_b]
        linarith
      · rename_i hlt_half
        have hlt' : rem.val < den.val - rem.val := by rw [← hhalf]; scalar_tac
        have hrem2 : (core.num.I128.wrapping_add rem rem).val = 2 * rem.val := by
          rw [I128.wrapping_add_val rem rem (by omega)]; omega
        simp only [bind_ok, Std.uncurry, WP.spec_ok]
        refine ⟨⟨by omega, by rw [hrem2]; omega, by rw [hrem2]; omega,
          by rw [hfrac_shl]; omega, by rw [hfrac_shl, hnext, hpow_b]; omega, ?_⟩, by omega⟩
        rw [hfrac_shl, hrem2, hnext, hpow_b]
        linarith
    · have heq : bit.val = shift.val := by scalar_tac
      rw [heq] at hflt hinv
      rw [WP.spec_ok]
      have hdiv : (rem0.val * 2 ^ shift.val) / den.val = frac.val := by
        have hu : (rem0.val * 2 ^ shift.val) / den.val = frac.val
            ∧ (rem0.val * 2 ^ shift.val) % den.val = rem.val :=
          (Int.ediv_emod_unique hden).mpr ⟨by linarith, hr0, hrlt⟩
        exact hu.1
      exact ⟨hdiv.symm, hf0, hflt⟩
  · have h0u : (0#u32).val = 0 := rfl
    have h0i : (0#i128).val = 0 := rfl
    dsimp only
    rw [h0u, h0i]
    exact ⟨Nat.zero_le _, hrem0.1, hrem0.2, le_refl _, by norm_num, by ring⟩

/-- `scale_div_pow2` returns `floor((num * 2^(min shift 64)) / den)` clamped to
`i128`, or `0` when `den ≤ 0`, without intermediate overflow. -/
@[step]
theorem scale_div_pow2_spec (num : Std.I128) (shift : Std.U32) (den : Std.I128) :
    fixed.scale_div_pow2 num shift den ⦃ r =>
      (den.val ≤ 0 → r.val = 0)
      ∧ (0 < den.val → r.val = clamp128 ((num.val * 2 ^ min shift.val 64) / den.val)) ⦄ := by
  unfold fixed.scale_div_pow2
  have hmax : fixed.MAX_SHIFT.val = 64 := by simp [fixed.MAX_SHIFT]
  split
  · rename_i hle
    have hden : den.val ≤ 0 := by scalar_tac
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun hpos => absurd hpos (not_lt.mpr hden)⟩
  · rename_i hgt
    have hden : 0 < den.val := by scalar_tac
    have hs_eq :
        (if shift > fixed.MAX_SHIFT then ok fixed.MAX_SHIFT else ok shift) =
          ok (if shift > fixed.MAX_SHIFT then fixed.MAX_SHIFT else shift) := by
      split <;> rfl
    rw [hs_eq]
    simp only [bind_ok]
    set s : Std.U32 := if shift > fixed.MAX_SHIFT then fixed.MAX_SHIFT else shift
    have hs_val : s.val = min shift.val 64 := by
      dsimp only [s]; split <;> scalar_tac
    have hs_le : s.val ≤ 64 := by omega
    have hpow_pos : (0 : ℤ) < 2 ^ s.val := by positivity
    have hq := I128.checked_div_bv_spec num den
    have hr := I128.checked_rem_bv_spec num den
    simp only [lift, I128.checked_div_eq, I128.checked_rem_eq]
    cases hq' : core.num.checked_div_IScalar num den <;>
      cases hr' : core.num.checked_rem_IScalar num den <;>
      simp only [hq', hr'] at hq hr ⊢ <;> simp only [bind_ok]
    · omega
    · rcases hq with h | ⟨_, h⟩ <;> omega
    · omega
    · rename_i tq tr
      obtain ⟨-, -, htqv, -⟩ := hq
      obtain ⟨-, htrv, -⟩ := hr
      have h1 : num.val.tmod den.val < den.val := Int.tmod_lt_of_pos num.val hden
      have h2 : -den.val < num.val.tmod den.val := Int.lt_tmod_of_pos num.val hden
      have hsum := Int.mul_tdiv_add_tmod num.val den.val
      have hqr :
          (if tr < 0#i128 then
              ok (core.num.I128.wrapping_sub tq 1#i128, core.num.I128.wrapping_add tr den)
            else ok (tq, tr))
            ⦃ pair => pair.1.val = num.val / den.val ∧ pair.2.val = num.val % den.val
              ∧ 0 ≤ pair.2.val ∧ pair.2.val < den.val ⦄ := by
        split
        · rename_i hneg
          have htr_neg : num.val.tmod den.val < 0 := by rw [← htrv]; scalar_tac
          have hroom : -2^127 < tq.val := by
            have hnum : -2^127 ≤ num.val := by scalar_tac
            rw [htqv]
            by_contra hcon
            have : den.val * num.val.tdiv den.val ≤ num.val.tdiv den.val := by nlinarith
            omega
          have hu : num.val / den.val = num.val.tdiv den.val - 1
              ∧ num.val % den.val = num.val.tmod den.val + den.val :=
            (Int.ediv_emod_unique hden).mpr ⟨by linarith, by omega, by omega⟩
          have hsub : (core.num.I128.wrapping_sub tq 1#i128).val = tq.val - 1 := by
            have h1i : (1#i128).val = 1 := rfl
            rw [I128.wrapping_sub_val tq 1#i128 (by rw [h1i]; scalar_tac), h1i]
          have hadd : (core.num.I128.wrapping_add tr den).val = tr.val + den.val :=
            I128.wrapping_add_val tr den (by rw [htrv]; scalar_tac)
          simp only [WP.spec_ok]
          exact ⟨by rw [hsub, htqv]; exact hu.1.symm, by rw [hadd, htrv]; exact hu.2.symm,
            by rw [hadd, htrv]; omega, by rw [hadd, htrv]; omega⟩
        · rename_i hpos
          have htr_nn : 0 ≤ num.val.tmod den.val := by rw [← htrv]; scalar_tac
          have hu : num.val / den.val = num.val.tdiv den.val
              ∧ num.val % den.val = num.val.tmod den.val :=
            (Int.ediv_emod_unique hden).mpr ⟨by linarith, by omega, by omega⟩
          simp only [WP.spec_ok]
          exact ⟨by rw [htqv]; exact hu.1.symm, by rw [htrv]; exact hu.2.symm,
            by rw [htrv]; omega, by rw [htrv]; omega⟩
      apply WP.spec_bind hqr
      rintro ⟨q, rem⟩ ⟨hqv, hrv, hr0, hrlt⟩
      simp only [Std.uncurry]
      -- Compute exact `max_q` and `min_q` values and the identity for `(num * 2^s) / den`.
      have hsplit_div : (num.val * 2 ^ s.val) / den.val
          = q.val * 2 ^ s.val + (rem.val * 2 ^ s.val) / den.val := by
        have hdecomp : num.val = den.val * q.val + rem.val := by
          rw [hqv, hrv]; exact (Int.mul_ediv_add_emod num.val den.val).symm
        have hmul : num.val * 2 ^ s.val = (q.val * 2 ^ s.val) * den.val + rem.val * 2 ^ s.val := by
          rw [hdecomp]; ring
        rw [hmul, Int.mul_add_ediv_right _ _ (by omega : den.val ≠ 0)]
      have hfrac_bounds :
          0 ≤ (rem.val * 2 ^ s.val) / den.val ∧ (rem.val * 2 ^ s.val) / den.val < 2 ^ s.val := by
        constructor
        · exact Int.ediv_nonneg (mul_nonneg hr0 hpow_pos.le) hden.le
        · exact Int.ediv_lt_of_lt_mul hden (by nlinarith)
      have hmax_q : (core.num.I128.wrapping_shr core.num.I128.MAX s).val
          = (2^127 - 1) / 2^s.val := by
        rw [I128.wrapping_shr_val _ _ (by omega), I128.max_val]
      have hmin_q : (core.num.I128.wrapping_shr core.num.I128.MIN s).val
          = (-2^127) / 2^s.val := by
        rw [I128.wrapping_shr_val _ _ (by omega), I128.min_val]
      have hpow_127 : (2 : ℤ) ^ 127 = 2 ^ (127 - s.val) * 2 ^ s.val := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      have hmax_q_mul : ((2 : ℤ)^127 - 1) / 2^s.val * 2^s.val = 2^127 - 2^s.val := by
        have h1 : (2 : ℤ)^127 - 1 = (2^(127 - s.val) - 1) * 2^s.val + (2^s.val - 1) := by
          linarith [hpow_127]
        have hu : ((2 : ℤ)^127 - 1) / 2^s.val = 2^(127 - s.val) - 1
            ∧ ((2 : ℤ)^127 - 1) % 2^s.val = 2^s.val - 1 :=
          (Int.ediv_emod_unique hpow_pos).mpr ⟨by linarith, by omega, by omega⟩
        rw [hu.1]; linarith [hpow_127]
      have hmin_q_mul : (-(2 : ℤ)^127) / 2^s.val * 2^s.val = -2^127 := by
        have h1 : -(2 : ℤ)^127 = (-2^(127 - s.val)) * 2^s.val + 0 := by linarith [hpow_127]
        have hu : (-(2 : ℤ)^127) / 2^s.val = -2^(127 - s.val)
            ∧ (-(2 : ℤ)^127) % 2^s.val = 0 :=
          (Int.ediv_emod_unique hpow_pos).mpr ⟨by linarith, le_refl _, hpow_pos⟩
        rw [hu.1]; linarith [hpow_127]
      split
      · rename_i hgt_max
        have hqg : (2^127 - 1) / 2^s.val + 1 ≤ q.val := by rw [← hmax_q]; scalar_tac
        have hge_max : 2^127 ≤ q.val * 2^s.val := by nlinarith [hmax_q_mul]
        rw [WP.spec_ok]
        refine ⟨fun h => by omega, fun _ => ?_⟩
        rw [I128.max_val, ← hs_val, hsplit_div]
        simp only [clamp128]
        omega
      · rename_i hle_max
        have hqle : q.val ≤ (2^127 - 1) / 2^s.val := by rw [← hmax_q]; scalar_tac
        split
        · rename_i hlt_min
          have hql : q.val ≤ (-2^127) / 2^s.val - 1 := by rw [← hmin_q]; scalar_tac
          have hle_min : q.val * 2^s.val + (rem.val * 2^s.val) / den.val < -2^127 := by
            nlinarith [hmin_q_mul]
          rw [WP.spec_ok]
          refine ⟨fun h => by omega, fun _ => ?_⟩
          rw [I128.min_val, ← hs_val, hsplit_div]
          simp only [clamp128]
          omega
        · rename_i hge_min
          have hqge : (-2^127) / 2^s.val ≤ q.val := by rw [← hmin_q]; scalar_tac
          have hq_lo : -2^127 ≤ q.val * 2^s.val := by nlinarith [hmin_q_mul]
          have hq_hi : q.val * 2^s.val ≤ 2^127 - 2^s.val := by nlinarith [hmax_q_mul]
          step with scale_div_pow2_loop_spec den s rem hden hs_le ⟨hr0, hrlt⟩
            as ⟨frac, hfrac_eq, hf0, hflt⟩
          have hfrac_eq' : frac.val = (rem.val * 2 ^ s.val) / den.val := hfrac_eq
          have hflt' : frac.val < 2 ^ s.val := hflt
          have hshl : (core.num.I128.wrapping_shl q s).val = q.val * 2^s.val :=
            I128.wrapping_shl_val q s (by omega) (by omega)
          have hadd : (core.num.I128.wrapping_add (core.num.I128.wrapping_shl q s) frac).val
              = q.val * 2^s.val + frac.val := by
            rw [I128.wrapping_add_val _ _ (by rw [hshl]; omega), hshl]
          refine ⟨fun h => by omega, fun _ => ?_⟩
          rw [hadd, hfrac_eq', ← hs_val, hsplit_div]
          simp only [clamp128]
          omega

end Unisono.Fixed
