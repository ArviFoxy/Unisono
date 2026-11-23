/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed
public import Unisono.Player
public import Unisono.Model.Gains

/-!
# The regulator's law against the best law

`unisono_core::player` computes, in whole numbers, how much further than the
schedule advances a cycle is to read. This file states how far that number is
from what the best law of `Unisono.Model.Regulation` says for the same state:
the law for the weight `a⁴`, where `a` is the gain of the cycle as the code
rounds it (`cycleGain`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Player

private theorem shr_val (x : Std.I128) (s : Std.U32) (n : ℕ) (hs : s.val = n) (hn : n < 128) :
    (core.num.I128.wrapping_shr x s).val = x.val / 2 ^ n := by
  rw [I128.wrapping_shr_val _ _ (by omega), hs]

/-- The gain of a cycle of `duration` nanoseconds as a real number: the `a`
of the model. -/
noncomputable def realGain (p : player.Player) (duration : ℤ) : ℝ :=
  (cycleGain p duration : ℝ) / 2 ^ 32

/-- A root as `fixed.root` returns it, of a number that is not negative. -/
private theorem root_bounds {r x : ℤ} (hx : 0 ≤ x) (hzero : x ≤ 0 → r = 0)
    (hpos : 0 < x → r * r ≤ x ∧ x < (r + 1) * (r + 1)) :
    r * r ≤ x ∧ x < (r + 1) * (r + 1) := by
  rcases hx.lt_or_eq with h | h
  · exact hpos h
  · have hr : r = 0 := hzero (by omega)
    rw [hr, ← h]
    norm_num

private theorem lt_of_mul_self_lt {r b : ℤ} (hb : 0 ≤ b) (h : r * r < b * b) : r < b := by
  by_contra hcon
  have hle : b ≤ r := not_lt.mp hcon
  nlinarith

open Unisono.Model.Regulation in
/-- **The gains that the code computes are close to the gains of the best
law.** For the gain `a` of the cycle and `d = modulus a`: the gain on the
distance ahead, in units of `2⁻³²`, is within four units of `d²`, and the
gain on the distance behind, in units of `2⁻⁴⁸`, is within
`a² / 2³¹ + 2⁻⁴⁸` of `a² d`. -/
theorem gains_spec (p : player.Player) (duration : Std.I64) :
    player.Player.gains p duration ⦃ g =>
      0 ≤ g.ahead.val ∧ g.ahead.val ≤ 2 ^ 38 ∧ -2 ^ 51 ≤ g.behind.val ∧ g.behind.val ≤ 2 ^ 51
      ∧ |(g.ahead.val : ℝ) / 2 ^ 32 - modulus (realGain p duration.val) ^ 2| ≤ 4 / 2 ^ 32
      ∧ |(g.behind.val : ℝ) / 2 ^ 48
            - realGain p duration.val ^ 2 * modulus (realGain p duration.val)|
          ≤ realGain p duration.val ^ 2 / 2 ^ 31 + 1 / 2 ^ 48 ⦄ := by
  unfold player.Player.gains
  have hsixteen : player.SIXTEEN.val = 2 ^ 68 := by simp [player.SIXTEEN]
  step as ⟨gain, hgain⟩
  obtain ⟨hG0, hG1⟩ := cycleGain_bounds p duration.val
  rw [← hgain] at hG0 hG1
  -- `a²`
  have hGG0 : 0 ≤ gain.val * gain.val := mul_self_nonneg _
  have hGG1 : gain.val * gain.val ≤ 2 ^ 32 * 2 ^ 32 := mul_le_mul hG1 hG1 hG0 (by norm_num)
  step as ⟨square, hsquare⟩
  have hS : square.val = gain.val * gain.val := by
    rw [hsquare, I128.wrapping_mul_val _ _ (by constructor <;> linarith)]
  have hS0 : 0 ≤ square.val := by rw [hS]; exact hGG0
  have hS1 : square.val ≤ 2 ^ 64 := by rw [hS]; linarith
  step as ⟨coarse, hcoarse⟩
  have hC : coarse.val = square.val / 2 ^ 32 := by
    rw [hcoarse, shr_val _ _ 32 rfl (by norm_num)]
  have hC0 : 0 ≤ coarse.val := by omega
  have hC1 : coarse.val ≤ 2 ^ 32 := by omega
  have hCf1 : coarse.val * 2 ^ 32 ≤ square.val := by omega
  have hCf2 : square.val < (coarse.val + 1) * 2 ^ 32 := by omega
  -- the root of `a⁴ + 16`
  have hCC0 : 0 ≤ coarse.val * coarse.val := mul_self_nonneg _
  have hCC1 : coarse.val * coarse.val ≤ 2 ^ 32 * 2 ^ 32 := mul_le_mul hC1 hC1 hC0 (by norm_num)
  step as ⟨i, hi⟩
  have hiv : i.val = coarse.val * coarse.val := by
    rw [hi, I128.wrapping_mul_val _ _ (by constructor <;> linarith)]
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = coarse.val * coarse.val + 2 ^ 68 := by
    rw [hi1, I128.wrapping_add_val _ _ (by rw [hiv, hsixteen]; constructor <;> linarith),
      hiv, hsixteen]
  step as ⟨wide, hW0, hWzero, hWpos⟩
  obtain ⟨hW1, hW2⟩ := hWpos (by rw [hi1v]; linarith)
  rw [hi1v] at hW1 hW2
  have hWlt : wide.val < 2 ^ 35 := lt_of_mul_self_lt (by norm_num) (by linarith)
  -- `y`
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = coarse.val + wide.val := by
    rw [hi2, I128.wrapping_add_val _ _ (by constructor <;> linarith)]
  step as ⟨sum, hsum⟩
  have hY : sum.val = (coarse.val + wide.val) / 2 := by
    rw [hsum, shr_val _ _ 1 rfl (by norm_num), hi2v]
    rfl
  have hY0 : 0 ≤ sum.val := by omega
  have hY1 : sum.val ≤ 2 ^ 35 := by omega
  have hYf1 : 2 * sum.val ≤ coarse.val + wide.val := by omega
  have hYf2 : coarse.val + wide.val ≤ 2 * sum.val + 1 := by omega
  -- the root of `a² y`
  have hSY0 : 0 ≤ square.val * sum.val := mul_nonneg hS0 hY0
  have hSY1 : square.val * sum.val ≤ 2 ^ 64 * 2 ^ 35 := mul_le_mul hS1 hY1 hY0 (by norm_num)
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = square.val * sum.val := by
    rw [hi3, I128.wrapping_mul_val _ _ (by constructor <;> linarith)]
  step as ⟨spread, hP0, hPzero, hPpos⟩
  obtain ⟨hP1, hP2⟩ := root_bounds (by rw [hi3v]; exact hSY0) hPzero hPpos
  rw [hi3v] at hP1 hP2
  have hPlt : spread.val < 2 ^ 50 := lt_of_mul_self_lt (by norm_num) (by linarith)
  -- `d`
  step as ⟨i4, hi4⟩
  have hi4v : i4.val = sum.val * 2 ^ 16 := by
    have hshift : (16#u32).val = 16 := rfl
    rw [hi4, I128.wrapping_shl_val _ _ (by rw [hshift]; norm_num)
      (by rw [hshift]; constructor <;> linarith), hshift]
  step as ⟨i5, hi5⟩
  have hi5v : i5.val = sum.val * 2 ^ 16 - spread.val := by
    rw [hi5, I128.wrapping_sub_val _ _ (by rw [hi4v]; constructor <;> linarith), hi4v]
  step as ⟨modulus, hmodulus⟩
  have hM : modulus.val = (sum.val * 2 ^ 16 - spread.val) / 2 := by
    rw [hmodulus, shr_val _ _ 1 rfl (by norm_num), hi5v]
    rfl
  have hM0 : -2 ^ 51 ≤ modulus.val := by omega
  have hM1 : modulus.val ≤ 2 ^ 51 := by omega
  have hMf1 : 2 * modulus.val ≤ sum.val * 2 ^ 16 - spread.val := by omega
  have hMf2 : sum.val * 2 ^ 16 - spread.val ≤ 2 * modulus.val + 1 := by omega
  -- `d²`
  have hMM0 : 0 ≤ modulus.val * modulus.val := mul_self_nonneg _
  have hMM1 : modulus.val * modulus.val ≤ 2 ^ 51 * 2 ^ 51 := by
    linarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 2 ^ 51 - modulus.val)
      (by linarith : (0 : ℤ) ≤ 2 ^ 51 + modulus.val)]
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = modulus.val * modulus.val := by
    rw [hi6, I128.wrapping_mul_val _ _ (by constructor <;> linarith)]
  step as ⟨i7, hi7⟩
  have hA : i7.val = modulus.val * modulus.val / 2 ^ 64 := by
    rw [hi7, shr_val _ _ 64 rfl (by norm_num), hi6v]
  have hA0 : 0 ≤ i7.val := by omega
  have hA1 : i7.val ≤ 2 ^ 38 := by omega
  have hAf1 : i7.val * 2 ^ 64 ≤ modulus.val * modulus.val := by omega
  have hAf2 : modulus.val * modulus.val < (i7.val + 1) * 2 ^ 64 := by omega
  -- `a² d`
  have hSM0 : -(2 ^ 64 * 2 ^ 51) ≤ square.val * modulus.val := by
    linarith [mul_le_mul_of_nonneg_left hM0 hS0]
  have hSM1 : square.val * modulus.val ≤ 2 ^ 64 * 2 ^ 51 := by
    linarith [mul_le_mul_of_nonneg_left hM1 hS0]
  step as ⟨i8, hi8⟩
  have hi8v : i8.val = square.val * modulus.val := by
    rw [hi8, I128.wrapping_mul_val _ _ (by constructor <;> linarith)]
  step as ⟨i9, hi9⟩
  have hB : i9.val = square.val * modulus.val / 2 ^ 64 := by
    rw [hi9, shr_val _ _ 64 rfl (by norm_num), hi8v]
  have hB0 : -2 ^ 51 ≤ i9.val := by omega
  have hB1 : i9.val ≤ 2 ^ 51 := by omega
  have hBf1 : i9.val * 2 ^ 64 ≤ square.val * modulus.val := by omega
  have hBf2 : square.val * modulus.val < (i9.val + 1) * 2 ^ 64 := by omega
  -- against the law
  obtain ⟨-, hclose1, hclose2⟩ := Unisono.Model.Gains.gains_of_integers hG0 hG1 hS hCf1 hCf2
    hW0 hW1 hW2 hYf1 hYf2 hP0 hP1 hP2 hMf1 hMf2 hAf1 hAf2 hBf1 hBf2
  unfold realGain
  rw [← hgain]
  exact ⟨hA0, hA1, hB0, hB1, hclose1, hclose2⟩

private theorem mul_bounds {x y a b : ℤ} (hx : |x| ≤ a) (hy : |y| ≤ b) :
    -(a * b) ≤ x * y ∧ x * y ≤ a * b :=
  abs_le.mp (by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx))

open Unisono.Model.Regulation in
/-- **What the code plans for a cycle is close to what the best law plans.**
Before a cycle the position is `behind` the schedule, in units of `2⁻³²`
frame, and the cycle would read `ahead` further than the schedule advances at
the pace of the cycle before, in units of `2⁻⁴⁸` frame. With `a` the gain of
the cycle and `d = modulus a`, the best law for the weight `a⁴` has the cycle
read `d² · ahead + a² d · behind` further than the schedule advances. The
code returns a whole number `z` of units of `2⁻⁴⁸` frame, brought within the
range of 64 bits, which is within

    4 / 2³² · |ahead| + (a² / 2³¹ + 2⁻⁴⁸) · |behind| + 2 · 2⁻⁴⁸

frames of that, the two distances taken in frames. -/
theorem regulate_spec (p : player.Player) (behind ahead duration : Std.I64) :
    player.Player.regulate p behind ahead duration ⦃ r => ∃ z : ℤ,
      r.val = Unisono.Fixed.clamp64 z
      ∧ |(z : ℝ) / 2 ^ 48
          - (modulus (realGain p duration.val) ^ 2 * ((ahead.val : ℝ) / 2 ^ 48)
            + realGain p duration.val ^ 2 * modulus (realGain p duration.val)
              * ((behind.val : ℝ) / 2 ^ 32))|
        ≤ 4 / 2 ^ 32 * (|(ahead.val : ℝ)| / 2 ^ 48)
          + (realGain p duration.val ^ 2 / 2 ^ 31 + 1 / 2 ^ 48)
            * (|(behind.val : ℝ)| / 2 ^ 32)
          + 2 / 2 ^ 48 ⦄ := by
  unfold player.Player.regulate
  step with gains_spec as ⟨gains, hA0, hA1, hB0, hB1, hcloseA, hcloseB⟩
  have habsA : |gains.ahead.val| ≤ 2 ^ 38 := abs_le.mpr ⟨by linarith, hA1⟩
  have habsB : |gains.behind.val| ≤ 2 ^ 51 := abs_le.mpr ⟨hB0, hB1⟩
  have habsv : |ahead.val| ≤ 2 ^ 63 := abs_le.mpr ⟨by scalar_tac, by scalar_tac⟩
  have habse : |behind.val| ≤ 2 ^ 63 := abs_le.mpr ⟨by scalar_tac, by scalar_tac⟩
  obtain ⟨hAv0, hAv1⟩ := mul_bounds habsA habsv
  obtain ⟨hBe0, hBe1⟩ := mul_bounds habsB habse
  -- the distance ahead, times its gain
  step as ⟨i, hi⟩
  have hiv : i.val = ahead.val := by rw [hi, I64.cast_I128_val]
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = gains.ahead.val * ahead.val := by
    rw [hi1, I128.wrapping_mul_val _ _ (by rw [hiv]; constructor <;> linarith), hiv]
  step as ⟨kept, hkept⟩
  have hK : kept.val = gains.ahead.val * ahead.val / 2 ^ 32 := by
    rw [hkept, shr_val _ _ 32 rfl (by norm_num), hi1v]
  have hK0 : -2 ^ 70 ≤ kept.val := by omega
  have hK1 : kept.val ≤ 2 ^ 70 := by omega
  have hKf1 : kept.val * 2 ^ 32 ≤ gains.ahead.val * ahead.val := by omega
  have hKf2 : gains.ahead.val * ahead.val < (kept.val + 1) * 2 ^ 32 := by omega
  -- the distance behind, times its gain
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = behind.val := by rw [hi2, I64.cast_I128_val]
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = gains.behind.val * behind.val := by
    rw [hi3, I128.wrapping_mul_val _ _ (by rw [hi2v]; constructor <;> linarith), hi2v]
  step as ⟨added, hadded⟩
  have hD : added.val = gains.behind.val * behind.val / 2 ^ 32 := by
    rw [hadded, shr_val _ _ 32 rfl (by norm_num), hi3v]
  have hD0 : -2 ^ 83 ≤ added.val := by omega
  have hD1 : added.val ≤ 2 ^ 83 := by omega
  have hDf1 : added.val * 2 ^ 32 ≤ gains.behind.val * behind.val := by omega
  have hDf2 : gains.behind.val * behind.val < (added.val + 1) * 2 ^ 32 := by omega
  -- their sum
  step as ⟨i4, hi4⟩
  have hi4v : i4.val = kept.val + added.val := by
    rw [hi4, I128.wrapping_add_val _ _ (by constructor <;> linarith)]
  apply WP.spec_mono (Unisono.Fixed.saturate_spec i4)
  intro r hr
  refine ⟨kept.val + added.val, by rw [hr, hi4v], ?_⟩
  exact Unisono.Model.Gains.law_close hKf1 hKf2 hDf1 hDf2 hcloseA hcloseB

/-! ## Twin closeness and equal-gain linearity for `ModalPlayer` -/

/-- Construct a single-mode `Player` carrying `gain_q16`, used to transfer
`gains_spec` and `regulate_spec` to both branches (`common_gain` and
`diff_gain`) of `ModalPlayer`. -/
def playerOfGain (gain_q16 : Std.U32) : player.Player :=
  { regulation := { gain := gain_q16, limit := 0#u32, jump := 0#u32 }
    running := false
    position := { frame := 0#u64, fraction := 0#u64 }
    pace := 0#i64
    slope := 0#i32 }

open Unisono.Model.Regulation in
/-- **Both branches of `ModalPlayer` compute gains close to the best law.**
Because `player.gains_for gain_q16 duration` is identical to `Player.gains` at
`gain_q16`, both the common-mode branch (`common_gain`) and the differential-mode
branch (`diff_gain`) of `ModalPlayer` inherit `gains_spec`. -/
theorem gains_for_spec (gain_q16 : Std.U32) (duration : Std.I64) :
    player.gains_for gain_q16 duration ⦃ g =>
      0 ≤ g.ahead.val ∧ g.ahead.val ≤ 2 ^ 38 ∧ -2 ^ 51 ≤ g.behind.val ∧ g.behind.val ≤ 2 ^ 51
      ∧ |(g.ahead.val : ℝ) / 2 ^ 32 - modulus (realGain (playerOfGain gain_q16) duration.val) ^ 2|
          ≤ 4 / 2 ^ 32
      ∧ |(g.behind.val : ℝ) / 2 ^ 48
            - realGain (playerOfGain gain_q16) duration.val ^ 2
              * modulus (realGain (playerOfGain gain_q16) duration.val)|
          ≤ realGain (playerOfGain gain_q16) duration.val ^ 2 / 2 ^ 31 + 1 / 2 ^ 48 ⦄ := by
  have heq : player.gains_for gain_q16 duration = player.Player.gains (playerOfGain gain_q16) duration :=
    gains_for_eq_player_gains (playerOfGain gain_q16) duration
  rw [heq]
  exact gains_spec (playerOfGain gain_q16) duration

open Unisono.Model.Regulation in
/-- **Both branches of `ModalPlayer` evaluate `Regulation.law` to within integer
rounding.** Applies directly to `common_gain` and `diff_gain`. -/
theorem regulate_for_spec (gain_q16 : Std.U32) (behind ahead duration : Std.I64) :
    player.regulate_for gain_q16 behind ahead duration ⦃ r => ∃ z : ℤ,
      r.val = Unisono.Fixed.clamp64 z
      ∧ |(z : ℝ) / 2 ^ 48
          - (modulus (realGain (playerOfGain gain_q16) duration.val) ^ 2 * ((ahead.val : ℝ) / 2 ^ 48)
            + realGain (playerOfGain gain_q16) duration.val ^ 2
              * modulus (realGain (playerOfGain gain_q16) duration.val)
              * ((behind.val : ℝ) / 2 ^ 32))|
        ≤ 4 / 2 ^ 32 * (|(ahead.val : ℝ)| / 2 ^ 48)
          + (realGain (playerOfGain gain_q16) duration.val ^ 2 / 2 ^ 31 + 1 / 2 ^ 48)
            * (|(behind.val : ℝ)| / 2 ^ 32)
          + 2 / 2 ^ 48 ⦄ := by
  have heq : player.regulate_for gain_q16 behind ahead duration =
      player.Player.regulate (playerOfGain gain_q16) behind ahead duration :=
    regulate_for_eq_player_regulate (playerOfGain gain_q16) behind ahead duration
  rw [heq]
  exact regulate_spec (playerOfGain gain_q16) behind ahead duration

private theorem ediv_add_bounds_pow32 (a b : ℤ) :
    (a + b) / 2 ^ 32 - 1 ≤ a / 2 ^ 32 + b / 2 ^ 32
    ∧ a / 2 ^ 32 + b / 2 ^ 32 ≤ (a + b) / 2 ^ 32 := by
  omega

/-- **Equal-gain modal equivalence (`g_com = g_diff`):** when both modal branches
use the same gain `gain_q16` and neither branch nor their combined error saturates
64-bit arithmetic, the sum of the common-mode and differential-mode control outputs
`regulate_for g b_com a_com dur + regulate_for g b_diff a_diff dur` equals the
single-mode control output `regulate_for g (b_com + b_diff) (a_com + a_diff) dur`
up to at most `2` units of `2⁻⁴⁸` frames from integer floor rounding of the two
32-bit shifts. -/
theorem regulate_for_equal_gain_linear (gain_q16 : Std.U32)
    (b_com a_com b_diff a_diff b_tot a_tot duration : Std.I64)
    (hb : b_tot.val = b_com.val + b_diff.val)
    (ha : a_tot.val = a_com.val + a_diff.val) :
    (do
      let g ← player.gains_for gain_q16 duration
      let r_com ← player.regulate_for gain_q16 b_com a_com duration
      let r_diff ← player.regulate_for gain_q16 b_diff a_diff duration
      let r_tot ← player.regulate_for gain_q16 b_tot a_tot duration
      ok (g, r_com, r_diff, r_tot))
      ⦃ q =>
        let g := q.1
        let z_com := g.ahead.val * a_com.val / 2 ^ 32 + g.behind.val * b_com.val / 2 ^ 32
        let z_diff := g.ahead.val * a_diff.val / 2 ^ 32 + g.behind.val * b_diff.val / 2 ^ 32
        let z_tot := g.ahead.val * a_tot.val / 2 ^ 32 + g.behind.val * b_tot.val / 2 ^ 32
        q.2.1.val = Fixed.clamp64 z_com
        ∧ q.2.2.1.val = Fixed.clamp64 z_diff
        ∧ q.2.2.2.val = Fixed.clamp64 z_tot
        ∧ z_tot - 2 ≤ z_com + z_diff ∧ z_com + z_diff ≤ z_tot ⦄ := by
  have heval : ∀ (g : player.Gains) (b a : Std.I64),
      0 ≤ g.ahead.val → g.ahead.val ≤ 2 ^ 38 → -2 ^ 51 ≤ g.behind.val → g.behind.val ≤ 2 ^ 51 →
      player.gains_for gain_q16 duration = ok g →
      player.regulate_for gain_q16 b a duration
        ⦃ r => r.val = Fixed.clamp64 (g.ahead.val * a.val / 2 ^ 32 + g.behind.val * b.val / 2 ^ 32) ⦄ := by
    intro g b a hA0 hA1 hB0 hB1 hg
    unfold player.regulate_for
    rw [hg, bind_ok]
    have habsA : |g.ahead.val| ≤ 2 ^ 38 := abs_le.mpr ⟨by linarith, hA1⟩
    have habsB : |g.behind.val| ≤ 2 ^ 51 := abs_le.mpr ⟨hB0, hB1⟩
    have habsa : |a.val| ≤ 2 ^ 63 := abs_le.mpr ⟨by scalar_tac, by scalar_tac⟩
    have habsb : |b.val| ≤ 2 ^ 63 := abs_le.mpr ⟨by scalar_tac, by scalar_tac⟩
    obtain ⟨hAa0, hAa1⟩ := mul_bounds habsA habsa
    obtain ⟨hBb0, hBb1⟩ := mul_bounds habsB habsb
    step as ⟨i, hi⟩
    have hiv : i.val = a.val := by rw [hi, I64.cast_I128_val]
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = g.ahead.val * a.val := by
      rw [hi1, I128.wrapping_mul_val _ _ (by rw [hiv]; constructor <;> linarith), hiv]
    step as ⟨kept, hkept⟩
    have hK : kept.val = g.ahead.val * a.val / 2 ^ 32 := by
      rw [hkept, shr_val _ _ 32 rfl (by norm_num), hi1v]
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = b.val := by rw [hi2, I64.cast_I128_val]
    step as ⟨i3, hi3⟩
    have hi3v : i3.val = g.behind.val * b.val := by
      rw [hi3, I128.wrapping_mul_val _ _ (by rw [hi2v]; constructor <;> linarith), hi2v]
    step as ⟨added, hadded⟩
    have hD : added.val = g.behind.val * b.val / 2 ^ 32 := by
      rw [hadded, shr_val _ _ 32 rfl (by norm_num), hi3v]
    step as ⟨i4, hi4⟩
    have hi4v : i4.val = kept.val + added.val := by
      have hK0 : -2 ^ 70 ≤ kept.val := by omega
      have hK1 : kept.val ≤ 2 ^ 70 := by omega
      have hD0 : -2 ^ 83 ≤ added.val := by omega
      have hD1 : added.val ≤ 2 ^ 83 := by omega
      rw [hi4, I128.wrapping_add_val _ _ (by constructor <;> linarith)]
    apply WP.spec_mono (Fixed.saturate_spec i4)
    intro r hr; rw [hr, hi4v, hK, hD]
  have hspec := gains_for_spec gain_q16 duration
  cases hg : player.gains_for gain_q16 duration with
  | div => rw [hg] at hspec; simp [WP.spec_div] at hspec
  | vis e k => rw [hg] at hspec; simp [WP.spec_vis] at hspec
  | ret g =>
    rw [hg] at hspec; simp only [WP.spec_ok] at hspec
    obtain ⟨hA0, hA1, hB0, hB1, _, _⟩ := hspec
    rw [bind_ok]
    step with heval g b_com a_com hA0 hA1 hB0 hB1 hg as ⟨r_com, hr_com⟩
    step with heval g b_diff a_diff hA0 hA1 hB0 hB1 hg as ⟨r_diff, hr_diff⟩
    step with heval g b_tot a_tot hA0 hA1 hB0 hB1 hg as ⟨r_tot, hr_tot⟩
    have hmul_a : g.ahead.val * a_tot.val = g.ahead.val * a_com.val + g.ahead.val * a_diff.val := by
      rw [ha, mul_add]
    have hmul_b : g.behind.val * b_tot.val = g.behind.val * b_com.val + g.behind.val * b_diff.val := by
      rw [hb, mul_add]
    have hda := ediv_add_bounds_pow32 (g.ahead.val * a_com.val) (g.ahead.val * a_diff.val)
    have hdb := ediv_add_bounds_pow32 (g.behind.val * b_com.val) (g.behind.val * b_diff.val)
    refine ⟨hr_com, hr_diff, hr_tot, ?_, ?_⟩ <;> rw [hmul_a, hmul_b] <;> omega

end Unisono.Player
