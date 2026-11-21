/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed
public import Unisono.Relation
public import Mathlib.Tactic.Linarith

/-!
# The position that is due

A schedule says of one frame, with index `index`, when it was captured and
the latency it is to have, and how fast the frames after it follow: `rate`
frames a second, faster by `drift` parts per billion, with a latency that
changes by `level_slope` nanoseconds per second of stream. The frame `x`
places after `index` is therefore due at

    capture + level + x · 10⁹ · (10⁹ + level_slope) / (rate · (10⁹ + drift))

nanoseconds, and the position that is due at the time `t` is

    x = (t - capture - level) · rate · (10⁹ + drift) / (10⁹ · (10⁹ + level_slope)).

`due_spec` says that `timing.due` returns this position, rounded down to a
multiple of `2⁻³²` frame: nothing in it wraps, and no rounding is left over
from one part of the computation to the next. The time that has passed is
held within the range of 64 bits, which is 292 years either way.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Due

/-- A number of 128 bits that fits 64 bits without a sign, as such a number. -/
private theorem hcast_u64_val (x : Std.I128) (h0 : 0 ≤ x.val) (h1 : x.val < 2 ^ 64) :
    ((IScalar.hcast .U64 x).val : ℤ) = x.val := by
  rw [IScalar.hcast_val_eq]
  have hmod : x.val % 2 ^ UScalarTy.U64.numBits = x.val := Int.emod_eq_of_lt h0 h1
  rw [hmod]
  exact Int.toNat_of_nonneg h0

/-- A number below `2³²` moved up by 32 bits. -/
private theorem shl_32_val (x : Std.U64) (h : x.val < 2 ^ 32) :
    (core.num.U64.wrapping_shl x 32#u32).val = x.val * 2 ^ 32 := by
  have hbv : (core.num.U64.wrapping_shl x 32#u32).bv = x.bv.shiftLeft 32 := by
    rw [core.num.U64.wrapping_shl_bv_eq]
    rfl
  have hx : x.bv.toNat < 2 ^ 32 := h
  show (core.num.U64.wrapping_shl x 32#u32).bv.toNat = x.bv.toNat * 2 ^ 32
  rw [hbv, BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by omega)

private theorem u64_bounds (x : Std.U64) : (0 : ℤ) ≤ x.val ∧ (x.val : ℤ) < 2 ^ 64 := by
  scalar_tac

private theorem nonneg_of_not_lt (x : Std.I128) (h : ¬ x < 0#i128) : 0 ≤ x.val := by
  scalar_tac

private theorem le_of_not_gt (x y : Std.I128) (h : ¬ x > y) : x.val ≤ y.val := by
  scalar_tac

/-- The bounds of a product, from bounds of the sizes of its factors. -/
private theorem mul_bounds {x y a b : ℤ} (hx : |x| ≤ a) (hy : |y| ≤ b) :
    -(a * b) ≤ x * y ∧ x * y ≤ a * b :=
  abs_le.mp (by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx))

/-- How far the position that is due at `time` lies from the schedule's
frame, in units of `2⁻³²` frame, rounded down. -/
def dueUnits (s : timing.Schedule) (time : ℤ) : ℤ :=
  Unisono.Fixed.clamp64 (time - s.capture.val - s.level.val)
      * (s.rate.val * (10 ^ 9 + s.drift.val)) * 2 ^ 32
    / (10 ^ 9 * (10 ^ 9 + s.level_slope.val))

/-- **The position that the code takes to be due is the one that the
schedule says, rounded down to `2⁻³²` frame.** A schedule whose pace or
whose level's pace is not positive gives none. Otherwise a position that is
returned has the frame `index + whole` and the fraction `part / 2³²`, where
`whole · 2³² + part` is `dueUnits`. -/
theorem due_spec (s : timing.Schedule) (time : Std.I64) :
    timing.due s time ⦃ r =>
      ((10 ^ 9 + s.drift.val ≤ 0 ∨ 10 ^ 9 + s.level_slope.val ≤ 0) → r = none)
      ∧ ∀ p, r = some p →
          ∃ whole part : ℤ, 0 ≤ part ∧ part < 2 ^ 32
            ∧ (p.frame.val : ℤ) = s.index.val + whole
            ∧ (p.fraction.val : ℤ) = part * 2 ^ 32
            ∧ whole * 2 ^ 32 + part = dueUnits s time.val ⦄ := by
  unfold timing.due
  have hbillion : timing.BILLION.val = 10 ^ 9 := by simp [timing.BILLION]
  have hdrift : -2 ^ 31 ≤ s.drift.val ∧ s.drift.val < 2 ^ 31 := by scalar_tac
  have hslope : -2 ^ 31 ≤ s.level_slope.val ∧ s.level_slope.val < 2 ^ 31 := by scalar_tac
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨pace, hpace⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨stretch, hstretch⟩
  have hiv : i.val = 10 ^ 9 := by rw [hi, I64.cast_I128_val, hbillion]
  have hi1v : i1.val = s.drift.val := by rw [hi1, I32.cast_I128_val]
  have hpacev : pace.val = 10 ^ 9 + s.drift.val := by
    rw [hpace, I128.wrapping_add_val _ _ (by rw [hiv, hi1v]; constructor <;> linarith), hiv, hi1v]
  have hi2v : i2.val = 10 ^ 9 := by rw [hi2, I64.cast_I128_val, hbillion]
  have hi3v : i3.val = s.level_slope.val := by rw [hi3, I32.cast_I128_val]
  have hstretchv : stretch.val = 10 ^ 9 + s.level_slope.val := by
    rw [hstretch, I128.wrapping_add_val _ _ (by rw [hi2v, hi3v]; constructor <;> linarith),
      hi2v, hi3v]
  split
  · rename_i hle
    have : pace.val ≤ 0 := by scalar_tac
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun p hp => by cases hp⟩
  rename_i hpos
  have hpace0 : 0 < pace.val := by scalar_tac
  split
  · rename_i hle
    have : stretch.val ≤ 0 := by scalar_tac
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun p hp => by cases hp⟩
  rename_i hpos2
  have hstretch0 : 0 < stretch.val := by scalar_tac
  -- the time that has passed
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  step as ⟨i7, hi7⟩
  step as ⟨i8, hi8⟩
  have hi4v : i4.val = time.val := by rw [hi4, I64.cast_I128_val]
  have hi5v : i5.val = s.capture.val := by rw [hi5, I64.cast_I128_val]
  have hi7v : i7.val = s.level.val := by rw [hi7, I64.cast_I128_val]
  have htime : -2 ^ 63 ≤ time.val ∧ time.val < 2 ^ 63 := by scalar_tac
  have hcapture : -2 ^ 63 ≤ s.capture.val ∧ s.capture.val < 2 ^ 63 := by scalar_tac
  have hlevel : -2 ^ 63 ≤ s.level.val ∧ s.level.val < 2 ^ 63 := by scalar_tac
  have hi6v : i6.val = time.val - s.capture.val := by
    rw [hi6, I128.wrapping_sub_val _ _ (by rw [hi4v, hi5v]; constructor <;> linarith), hi4v, hi5v]
  have hi8v : i8.val = time.val - s.capture.val - s.level.val := by
    rw [hi8, I128.wrapping_sub_val _ _ (by rw [hi6v, hi7v]; constructor <;> linarith), hi6v, hi7v]
  step with Unisono.Fixed.saturate_spec as ⟨elapsed, helapsed⟩
  rw [hi8v] at helapsed
  have hel : -2 ^ 63 ≤ elapsed.val ∧ elapsed.val < 2 ^ 63 := by scalar_tac
  -- frames per nanosecond, as a fraction
  step as ⟨i9, hi9⟩
  have hi9v : i9.val = s.rate.val := by rw [hi9, U32.hcast_I128_val]
  have hrate : (0 : ℤ) ≤ s.rate.val ∧ (s.rate.val : ℤ) < 2 ^ 32 := by scalar_tac
  have hfp : -(2 ^ 32 * 2 ^ 32) ≤ (s.rate.val : ℤ) * pace.val
      ∧ (s.rate.val : ℤ) * pace.val ≤ 2 ^ 32 * 2 ^ 32 :=
    mul_bounds (abs_le.mpr ⟨by linarith, by linarith⟩)
      (abs_le.mpr ⟨by linarith, by rw [hpacev]; linarith⟩)
  have hfp0 : 0 ≤ (s.rate.val : ℤ) * pace.val := mul_nonneg hrate.1 hpace0.le
  step as ⟨frames_per, hframes⟩
  have hframesv : frames_per.val = s.rate.val * pace.val := by
    rw [hframes, I128.wrapping_mul_val _ _ (by rw [hi9v]; constructor <;> linarith), hi9v]
  step as ⟨i10, hi10⟩
  have hi10v : i10.val = 10 ^ 9 := by rw [hi10, I64.cast_I128_val, hbillion]
  have hst32 : stretch.val < 2 ^ 32 := by rw [hstretchv]; linarith
  step as ⟨i11, hi11⟩
  have hi11v : i11.val = 10 ^ 9 * stretch.val := by
    rw [hi11, I128.wrapping_mul_val _ _ (by rw [hi10v]; constructor <;> linarith), hi10v]
  step with Unisono.Fixed.saturate_spec as ⟨divisor, hdivisor⟩
  have hdiv : divisor.val = 10 ^ 9 * stretch.val := by
    rw [hdivisor, hi11v]
    simp only [Unisono.Fixed.clamp64]
    omega
  have hdiv0 : 0 < divisor.val := by rw [hdiv]; linarith
  have hdiv1 : divisor.val < 2 ^ 62 := by rw [hdiv]; linarith
  -- the whole frames
  step as ⟨i12, hi12⟩
  have hi12v : i12.val = elapsed.val := by rw [hi12, I64.cast_I128_val]
  have hprod := mul_bounds (x := elapsed.val) (y := (s.rate.val : ℤ) * pace.val)
    (a := 2 ^ 63) (b := 2 ^ 32 * 2 ^ 32) (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, hfp.2⟩)
  step as ⟨product, hproduct⟩
  -- The rate is below 2^32, so the product stays strictly within the range
  -- of 128 bits, with room for a divisor.
  have hfplt : (s.rate.val : ℤ) * pace.val ≤ (2 ^ 32 - 1) * 2 ^ 32 :=
    mul_le_mul (by linarith) (by linarith) hpace0.le (by norm_num)
  have hprodlt : elapsed.val * ((s.rate.val : ℤ) * pace.val) < 2 ^ 127 - 2 ^ 94 := by
    have h1 : elapsed.val * ((s.rate.val : ℤ) * pace.val)
        ≤ 2 ^ 63 * ((s.rate.val : ℤ) * pace.val) :=
      mul_le_mul_of_nonneg_right (by linarith) hfp0
    linarith
  have hprodgt : -2 ^ 127 + 2 ^ 94 < elapsed.val * ((s.rate.val : ℤ) * pace.val) := by
    have h1 : -2 ^ 63 * ((s.rate.val : ℤ) * pace.val)
        ≤ elapsed.val * ((s.rate.val : ℤ) * pace.val) :=
      mul_le_mul_of_nonneg_right (by linarith) hfp0
    linarith
  have hproductv : product.val = elapsed.val * (s.rate.val * pace.val) := by
    rw [hproduct, I128.wrapping_mul_val _ _
      (by rw [hi12v, hframesv]; exact ⟨by linarith, by linarith⟩), hi12v, hframesv]
  step with Unisono.Fixed.div_floor_spec as ⟨whole, hwhole, _⟩
  have hwholev : whole.val = product.val / divisor.val := hwhole hdiv0
  have hfloor1 : whole.val * divisor.val ≤ product.val := by
    rw [hwholev]; exact Int.ediv_mul_le _ hdiv0.ne'
  have hfloor2 : product.val < whole.val * divisor.val + divisor.val := by
    rw [hwholev]
    have := Int.lt_ediv_add_one_mul_self product.val hdiv0
    linarith
  have hproductb : -2 ^ 127 + 2 ^ 94 < product.val ∧ product.val < 2 ^ 127 - 2 ^ 94 := by
    rw [hproductv]; exact ⟨hprodgt, hprodlt⟩
  -- the part of a frame
  step as ⟨i13, hi13⟩
  have hi13v : i13.val = divisor.val := by rw [hi13, I64.cast_I128_val]
  step as ⟨i14, hi14⟩
  have hi14v : i14.val = whole.val * divisor.val := by
    rw [hi14, I128.wrapping_mul_val _ _ (by rw [hi13v]; constructor <;> linarith), hi13v]
  step as ⟨rest, hrest⟩
  have hrestv : rest.val = product.val - whole.val * divisor.val := by
    rw [hrest, I128.wrapping_sub_val _ _ (by rw [hi14v]; constructor <;> linarith), hi14v]
  have hrest0 : 0 ≤ rest.val := by rw [hrestv]; linarith
  have hrest1 : rest.val < divisor.val := by rw [hrestv]; linarith
  step as ⟨i15, hi15⟩
  have hshift : (32#u32).val = 32 := rfl
  have hi15v : i15.val = rest.val * 2 ^ 32 := by
    rw [hi15, I128.wrapping_shl_val _ _ (by rw [hshift]; norm_num)
      (by rw [hshift]; constructor <;> linarith), hshift]
  step with Unisono.Fixed.div_floor_spec as ⟨fraction, hfraction, _⟩
  have hfractionv : fraction.val = rest.val * 2 ^ 32 / divisor.val := by
    rw [hfraction hdiv0, hi15v]
  have hfrac0 : 0 ≤ fraction.val := by
    rw [hfractionv]; exact Int.ediv_nonneg (by positivity) hdiv0.le
  have hfrac1 : fraction.val < 2 ^ 32 := by
    rw [hfractionv]
    exact Int.ediv_lt_of_lt_mul hdiv0 (by linarith)
  -- the frame
  step as ⟨i16, hi16⟩
  have hi16v : i16.val = s.index.val := by rw [hi16, U64.hcast_I128_val]
  have hindex := u64_bounds s.index
  have hwholeb : -2 ^ 127 + 2 ^ 64 ≤ whole.val ∧ whole.val < 2 ^ 127 - 2 ^ 64 := by
    have hpl : -(2 ^ 63 * (2 ^ 32 * 2 ^ 32)) ≤ product.val := by rw [hproductv]; exact hprod.1
    have hpu : product.val ≤ 2 ^ 63 * (2 ^ 32 * 2 ^ 32) := by rw [hproductv]; exact hprod.2
    rcases le_or_gt 0 whole.val with hw | hw
    · have := le_mul_of_one_le_right hw (by linarith : (1 : ℤ) ≤ divisor.val)
      constructor <;> linarith
    · have := mul_le_of_one_le_right hw.le (by linarith : (1 : ℤ) ≤ divisor.val)
      constructor <;> linarith
  step as ⟨frame, hframe⟩
  have hframev : frame.val = s.index.val + whole.val := by
    rw [hframe, I128.wrapping_add_val _ _ (by rw [hi16v]; constructor <;> linarith), hi16v]
  -- what is returned says what was computed
  have hunits : whole.val * 2 ^ 32 + fraction.val = dueUnits s time.val := by
    have hsplit : product.val * 2 ^ 32
        = rest.val * 2 ^ 32 + whole.val * 2 ^ 32 * divisor.val := by rw [hrestv]; ring
    have hquot : product.val * 2 ^ 32 / divisor.val
        = rest.val * 2 ^ 32 / divisor.val + whole.val * 2 ^ 32 := by
      rw [hsplit, Int.add_mul_ediv_right _ _ hdiv0.ne']
    unfold dueUnits
    rw [← helapsed, ← hpacev, ← hstretchv, ← hdiv, ← hproductv, hquot, hfractionv]
    ring
  split
  · rw [WP.spec_ok]
    exact ⟨fun h => by rcases h with h | h <;> linarith, fun p hp => by cases hp⟩
  rename_i hneg
  have hframe0 : 0 ≤ frame.val := nonneg_of_not_lt frame hneg
  step as ⟨i17, hi17⟩
  have hi17v : i17.val = 2 ^ 64 - 1 := by
    rw [hi17, U64.hcast_I128_val]
    rfl
  split
  · rw [WP.spec_ok]
    exact ⟨fun h => by rcases h with h | h <;> linarith, fun p hp => by cases hp⟩
  rename_i hbig
  have hframe1 : frame.val < 2 ^ 64 := by
    have : frame.val ≤ i17.val := le_of_not_gt frame i17 hbig
    linarith
  step as ⟨i18, hi18⟩
  step as ⟨i19, hi19⟩
  step as ⟨i20, hi20⟩
  have hi18v : (i18.val : ℤ) = frame.val := by rw [hi18]; exact hcast_u64_val frame hframe0 hframe1
  have hi19v : (i19.val : ℤ) = fraction.val := by
    rw [hi19]; exact hcast_u64_val fraction hfrac0 (by linarith)
  have hi19lt : i19.val < 2 ^ 32 := by
    have : (i19.val : ℤ) < 2 ^ 32 := by rw [hi19v]; exact hfrac1
    exact_mod_cast this
  have hi20v : (i20.val : ℤ) = fraction.val * 2 ^ 32 := by
    rw [hi20, shl_32_val i19 hi19lt]
    push_cast
    rw [hi19v]
  refine ⟨fun h => by rcases h with h | h <;> linarith, fun p hp => ?_⟩
  cases hp
  exact ⟨whole.val, fraction.val, hfrac0, hfrac1, by rw [hi18v, hframev], hi20v, hunits⟩

end Unisono.Due
