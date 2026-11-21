/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Model.Regulation

/-!
# The gains of the law, computed in whole numbers

The best law for the weight `a⁴` multiplies the pace by `d²` and the distance
by `a² d`, where `d = modulus a` (`Unisono.Model.Regulation`). The code
computes the two numbers in whole numbers: `a` in units of `2⁻³²`, every
division and every square root rounded down. This file states how far the
numbers it arrives at are from `d²` and `a² d`.

The computation, for the whole number `G` that stands for `a = G / 2³²`, with
`⌊ ⌋` for rounding down:

    S = G²                         a²          in units of 2⁻⁶⁴
    C = ⌊S / 2³²⌋                  a²          in units of 2⁻³²
    W = ⌊√(C² + 2⁶⁸)⌋              √(a⁴ + 16)  in units of 2⁻³²
    Y = ⌊(C + W) / 2⌋              y           in units of 2⁻³²
    P = ⌊√(S Y)⌋                   √(a² y)     in units of 2⁻⁴⁸
    M = ⌊(2¹⁶ Y - P) / 2⌋          d           in units of 2⁻⁴⁸
    A = ⌊M² / 2⁶⁴⌋                 d²          in units of 2⁻³²
    B = ⌊S M / 2⁶⁴⌋                a² d        in units of 2⁻⁴⁸

Here `y = (a² + √(a⁴ + 16)) / 2` is the sum of `d` and its inverse, and
`d = (y - √(y² - 4)) / 2` with `y² - 4 = a² y`.

`gains_close` follows the rounding through the computation in real numbers;
`gains_of_integers` states the result for the whole numbers: `A` is within
four units of `d²`, and `B` is within `a² / 2³¹ + 2⁻⁴⁸` of `a² d`.
-/

@[expose] public noncomputable section

namespace Unisono.Model.Gains

open Unisono.Model.Regulation

private theorem le_of_sq_le {x z : ℝ} (hz : 0 ≤ z) (h : x ^ 2 ≤ z ^ 2) : x ≤ z := by
  by_contra hcon
  have hlt : z < x := not_le.mp hcon
  nlinarith

private theorem lt_of_sq_lt {x z : ℝ} (hz : 0 ≤ z) (h : x ^ 2 < z ^ 2) : x < z := by
  by_contra hcon
  have hle : z ≤ x := not_lt.mp hcon
  nlinarith

/-- **The rounding, followed through the computation.** `u` and `t` are the
two units, `2⁻³²` and `2⁻⁴⁸` in the code. `R` is `√(a⁴ + 16)` and `s` is
`√(a² y)`; `c`, `w`, `yI`, `pI`, `mI`, `A` and `B` are the numbers that the
computation arrives at for `a²`, `R`, `y`, `s`, `d`, `d²` and `a² d`, each
rounded down to its unit. -/
theorem gains_close {a R y s d u t c w yI pI mI A B : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1 / 4) (ht0 : 0 < t) (htu : t ≤ u)
    (hR0 : 0 ≤ R) (hR : R ^ 2 = a ^ 4 + 16) (hy : y = (a ^ 2 + R) / 2)
    (hs0 : 0 ≤ s) (hs : s ^ 2 = a ^ 2 * y) (hd : d = (y - s) / 2)
    (hc0 : 0 ≤ c) (hc1 : c ≤ a ^ 2) (hc2 : a ^ 2 < c + u)
    (hw0 : 0 ≤ w) (hw1 : w ^ 2 ≤ c ^ 2 + 16) (hw2 : c ^ 2 + 16 < (w + u) ^ 2)
    (hy1 : 2 * yI ≤ c + w) (hy2 : c + w ≤ 2 * yI + u)
    (hp0 : 0 ≤ pI) (hp1 : pI ^ 2 ≤ a ^ 2 * yI) (hp2 : a ^ 2 * yI < (pI + t) ^ 2)
    (hm1 : 2 * mI ≤ yI - pI) (hm2 : yI - pI ≤ 2 * mI + t)
    (hA1 : A ≤ mI ^ 2) (hA2 : mI ^ 2 < A + u)
    (hB1 : B ≤ a ^ 2 * mI) (hB2 : a ^ 2 * mI < B + t) :
    0 ≤ d ∧ d ≤ 1 ∧ |mI - d| ≤ 2 * u ∧ |A - d ^ 2| ≤ 4 * u
      ∧ |B - a ^ 2 * d| ≤ 2 * u * a ^ 2 + t := by
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have ha21 : a ^ 2 ≤ 1 := pow_le_one₀ ha0 ha1
  have ha4 : 0 ≤ a ^ 4 := by positivity
  have hR4 : 4 ≤ R := le_of_sq_le hR0 (by rw [hR]; linarith)
  have hy2' : 2 ≤ y := by linarith
  have hquad : y ^ 2 - 4 = a ^ 2 * y := by
    rw [hy]
    linear_combination (1 / 4 : ℝ) * hR
  -- `d` lies between 0 and 1
  have hsy : s ≤ y :=
    le_of_sq_le (by linarith)
      (by rw [hs]; linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y - a ^ 2) (by linarith : (0 : ℝ) ≤ y)])
  have hys : y - 2 ≤ s := le_of_sq_le hs0 (by rw [hs, ← hquad]; linarith)
  have hd0 : 0 ≤ d := by linarith
  have hd1 : d ≤ 1 := by linarith
  -- the root of `a⁴ + 16`
  have hc4 : c ^ 2 ≤ a ^ 4 := by linarith [mul_le_mul hc1 hc1 hc0 ha2]
  have hwR : w ≤ R := le_of_sq_le hR0 (by rw [hR]; linarith)
  have hcw : c < w + u := lt_of_sq_lt (by linarith) (by linarith [sq_nonneg c])
  have hgap0 : 0 ≤ a ^ 2 - c := by linarith
  have hgapu : a ^ 2 - c ≤ u := by linarith
  have hRw : R < w + 2 * u := by
    have h1 : c * (a ^ 2 - c) ≤ (w + u) * u := mul_le_mul hcw.le hgapu hgap0 (by linarith)
    have h2 : (a ^ 2 - c) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hgap0 hgapu 2
    exact lt_of_sq_lt (by linarith) (by rw [hR]; linarith)
  -- `y`
  have hyIy : yI ≤ y := by linarith
  have hyyI : y < yI + 2 * u := by linarith
  -- the root of `a² y`
  have hps : pI ≤ s :=
    le_of_sq_le hs0 (by rw [hs]; linarith [mul_nonneg ha2 (sub_nonneg.mpr hyIy)])
  have hsa : 7 / 5 * a ≤ s :=
    le_of_sq_le hs0 (by rw [hs]; linarith [mul_nonneg ha2 (by linarith : (0 : ℝ) ≤ y - 2)])
  have hua : u * a ≤ u := mul_le_of_le_one_right hu0.le ha1
  have hua0 : 0 ≤ u * a := mul_nonneg hu0.le ha0
  have hsp : s < pI + t + u * a := by
    by_cases hsmall : s - u * a ≤ 0
    · linarith
    · have hpos : 0 < s - u * a := not_le.mp hsmall
      have h3 : 0 ≤ 2 * s - u * a - 2 * a := by
        linarith [mul_le_mul_of_nonneg_right hu1 ha0]
      have h4 : a ^ 2 * (y - yI) ≤ a ^ 2 * (2 * u) :=
        mul_le_mul_of_nonneg_left (by linarith) ha2
      have h5 : (s - u * a) ^ 2 ≤ a ^ 2 * yI := by linarith [mul_nonneg hua0 h3]
      have h6 : s - u * a < pI + t := lt_of_sq_lt (by linarith) (by linarith)
      linarith
  -- `d`
  have hmlow : d - u - t / 2 < mI := by linarith
  have hmhigh : mI < d + u := by linarith
  have hm : |mI - d| ≤ 2 * u := abs_le.mpr ⟨by linarith, by linarith⟩
  -- `d²`
  have hud : u * d ≤ u := mul_le_of_le_one_right hu0.le hd1
  have hud0 : 0 ≤ u * d := mul_nonneg hu0.le hd0
  have huu : u * u ≤ u * (1 / 4) := mul_le_mul_of_nonneg_left hu1 hu0.le
  have hsqhigh : mI ^ 2 < d ^ 2 + 4 * u := by
    have h1 : mI ^ 2 < (d + 3 / 2 * u) ^ 2 := sq_lt_sq' (by linarith) (by linarith)
    linarith
  have hsqlow : d ^ 2 - 3 * u ≤ mI ^ 2 := by
    by_cases hcase : 3 / 2 * u ≤ d
    · have h0 : 0 ≤ d - 3 / 2 * u := by linarith
      have hle : d - 3 / 2 * u ≤ mI := by linarith
      have h1 : (d - 3 / 2 * u) ^ 2 ≤ mI ^ 2 := pow_le_pow_left₀ h0 hle 2
      linarith [sq_nonneg u]
    · have hlt : d < 3 / 2 * u := not_le.mp hcase
      have h1 : d * d ≤ 3 / 2 * u * d := mul_le_mul_of_nonneg_right hlt.le hd0
      linarith [sq_nonneg mI]
  have hA : |A - d ^ 2| ≤ 4 * u := abs_le.mpr ⟨by linarith, by linarith⟩
  -- `a² d`
  have hBhigh : a ^ 2 * mI ≤ a ^ 2 * (d + u) := mul_le_mul_of_nonneg_left hmhigh.le ha2
  have hBlow : a ^ 2 * (d - 2 * u) ≤ a ^ 2 * mI :=
    mul_le_mul_of_nonneg_left (by linarith) ha2
  have hua2 : 0 ≤ u * a ^ 2 := mul_nonneg hu0.le ha2
  have hB : |B - a ^ 2 * d| ≤ 2 * u * a ^ 2 + t := abs_le.mpr ⟨by linarith, by linarith⟩
  exact ⟨hd0, hd1, hm, hA, hB⟩

/-- **The gains in whole numbers are close to the gains of the law.** For the
whole numbers of the computation at the head of this file, `A / 2³²` is
within `4 / 2³²` of `d²` and `B / 2⁴⁸` is within `a² / 2³¹ + 2⁻⁴⁸` of `a² d`,
where `a = G / 2³²` and `d = modulus a`. The roots and the quotients are
given by what they are rounded down from. -/
theorem gains_of_integers {G S C W Y P M A B : ℤ}
    (hG0 : 0 ≤ G) (hG1 : G ≤ 2 ^ 32) (hS : S = G * G)
    (hC1 : C * 2 ^ 32 ≤ S) (hC2 : S < (C + 1) * 2 ^ 32)
    (hW0 : 0 ≤ W) (hW1 : W * W ≤ C * C + 2 ^ 68) (hW2 : C * C + 2 ^ 68 < (W + 1) * (W + 1))
    (hY1 : 2 * Y ≤ C + W) (hY2 : C + W ≤ 2 * Y + 1)
    (hP0 : 0 ≤ P) (hP1 : P * P ≤ S * Y) (hP2 : S * Y < (P + 1) * (P + 1))
    (hM1 : 2 * M ≤ Y * 2 ^ 16 - P) (hM2 : Y * 2 ^ 16 - P ≤ 2 * M + 1)
    (hA1 : A * 2 ^ 64 ≤ M * M) (hA2 : M * M < (A + 1) * 2 ^ 64)
    (hB1 : B * 2 ^ 64 ≤ S * M) (hB2 : S * M < (B + 1) * 2 ^ 64) :
    |(M : ℝ) / 2 ^ 48 - modulus ((G : ℝ) / 2 ^ 32)| ≤ 2 / 2 ^ 32
      ∧ |(A : ℝ) / 2 ^ 32 - modulus ((G : ℝ) / 2 ^ 32) ^ 2| ≤ 4 / 2 ^ 32
      ∧ |(B : ℝ) / 2 ^ 48 - ((G : ℝ) / 2 ^ 32) ^ 2 * modulus ((G : ℝ) / 2 ^ 32)|
          ≤ ((G : ℝ) / 2 ^ 32) ^ 2 / 2 ^ 31 + 1 / 2 ^ 48 := by
  have hC0 : 0 ≤ C := by
    have hsq : 0 ≤ G * G := mul_self_nonneg G
    by_contra hcon
    have : C + 1 ≤ 0 := by omega
    nlinarith
  -- the whole numbers as real numbers
  have rG0 : (0 : ℝ) ≤ G := by exact_mod_cast hG0
  have rG1 : (G : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hG1
  have rC0 : (0 : ℝ) ≤ C := by exact_mod_cast hC0
  have rC1 : (C : ℝ) * 2 ^ 32 ≤ G * G := by rw [hS] at hC1; exact_mod_cast hC1
  have rC2 : (G : ℝ) * G < (C + 1) * 2 ^ 32 := by rw [hS] at hC2; exact_mod_cast hC2
  have rW0 : (0 : ℝ) ≤ W := by exact_mod_cast hW0
  have rW1 : (W : ℝ) * W ≤ C * C + 2 ^ 68 := by exact_mod_cast hW1
  have rW2 : (C : ℝ) * C + 2 ^ 68 < (W + 1) * (W + 1) := by exact_mod_cast hW2
  have rY1 : 2 * (Y : ℝ) ≤ C + W := by exact_mod_cast hY1
  have rY2 : (C : ℝ) + W ≤ 2 * Y + 1 := by exact_mod_cast hY2
  have rP0 : (0 : ℝ) ≤ P := by exact_mod_cast hP0
  have rP1 : (P : ℝ) * P ≤ G * G * Y := by rw [hS] at hP1; exact_mod_cast hP1
  have rP2 : (G : ℝ) * G * Y < (P + 1) * (P + 1) := by rw [hS] at hP2; exact_mod_cast hP2
  have rM1 : 2 * (M : ℝ) ≤ Y * 2 ^ 16 - P := by exact_mod_cast hM1
  have rM2 : (Y : ℝ) * 2 ^ 16 - P ≤ 2 * M + 1 := by exact_mod_cast hM2
  have rA1 : (A : ℝ) * 2 ^ 64 ≤ M * M := by exact_mod_cast hA1
  have rA2 : (M : ℝ) * M < (A + 1) * 2 ^ 64 := by exact_mod_cast hA2
  have rB1 : (B : ℝ) * 2 ^ 64 ≤ G * G * M := by rw [hS] at hB1; exact_mod_cast hB1
  have rB2 : (G : ℝ) * G * M < (B + 1) * 2 ^ 64 := by rw [hS] at hB2; exact_mod_cast hB2
  -- the numbers of the law
  set a : ℝ := G / 2 ^ 32 with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one (by positivity)]; exact rG1
  have hroot : Real.sqrt (a ^ 4 + 16) ^ 2 = a ^ 4 + 16 := Real.sq_sqrt (by positivity)
  have hroot0 : 0 ≤ Real.sqrt (a ^ 4 + 16) := Real.sqrt_nonneg _
  have hfour : 4 ≤ Real.sqrt (a ^ 4 + 16) := by
    by_contra hcon
    have hlt : Real.sqrt (a ^ 4 + 16) < 4 := not_le.mp hcon
    have ha4 : 0 ≤ a ^ 4 := by positivity
    nlinarith
  have hsum : modulusSum a = (a ^ 2 + Real.sqrt (a ^ 4 + 16)) / 2 := rfl
  have hquad : modulusSum a ^ 2 - 4 = a ^ 2 * modulusSum a := by
    rw [hsum]
    linear_combination (1 / 4 : ℝ) * hroot
  have hspread : Real.sqrt (modulusSum a ^ 2 - 4) ^ 2 = a ^ 2 * modulusSum a := by
    rw [Real.sq_sqrt (by rw [hquad, hsum]; positivity), hquad]
  have hclose := gains_close (a := a) (R := Real.sqrt (a ^ 4 + 16)) (y := modulusSum a)
    (s := Real.sqrt (modulusSum a ^ 2 - 4)) (d := modulus a)
    (u := 1 / 2 ^ 32) (t := 1 / 2 ^ 48)
    (c := C / 2 ^ 32) (w := W / 2 ^ 32) (yI := Y / 2 ^ 32) (pI := P / 2 ^ 48)
    (mI := M / 2 ^ 48) (A := A / 2 ^ 32) (B := B / 2 ^ 48)
    ha0 ha1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hroot0 hroot hsum (Real.sqrt_nonneg _) hspread rfl
    (by positivity) (by rw [ha]; linarith) (by rw [ha]; linarith)
    (by positivity) (by linarith) (by linarith)
    (by linarith) (by linarith)
    (by positivity) (by rw [ha]; linarith) (by rw [ha]; linarith)
    (by linarith) (by linarith)
    (by linarith) (by linarith)
    (by rw [ha]; linarith) (by rw [ha]; linarith)
  obtain ⟨-, -, hm, hA, hB⟩ := hclose
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **What a cycle is to read, computed in whole numbers, is close to what the
law says.** `K` and `D` are the two products of the code, each rounded down:
the gain `A`, in units of `2⁻³²`, times the distance `v` ahead, in units of
`2⁻⁴⁸` frame, and the gain `B`, in units of `2⁻⁴⁸`, times the distance `e`
behind, in units of `2⁻³²` frame. When `A` and `B` are within `εA` and `εB`
of the gains `α` and `β`, the sum `K + D`, in units of `2⁻⁴⁸` frame, is
within `εA |v| + εB |e| + 2 · 2⁻⁴⁸` frames of `α v + β e`. -/
theorem law_close {A B K D v e : ℤ} {α β εA εB : ℝ}
    (hK1 : K * 2 ^ 32 ≤ A * v) (hK2 : A * v < (K + 1) * 2 ^ 32)
    (hD1 : D * 2 ^ 32 ≤ B * e) (hD2 : B * e < (D + 1) * 2 ^ 32)
    (hA : |(A : ℝ) / 2 ^ 32 - α| ≤ εA) (hB : |(B : ℝ) / 2 ^ 48 - β| ≤ εB) :
    |((K + D : ℤ) : ℝ) / 2 ^ 48 - (α * ((v : ℝ) / 2 ^ 48) + β * ((e : ℝ) / 2 ^ 32))|
      ≤ εA * (|(v : ℝ)| / 2 ^ 48) + εB * (|(e : ℝ)| / 2 ^ 32) + 2 / 2 ^ 48 := by
  have rK1 : (K : ℝ) * 2 ^ 32 ≤ A * v := by exact_mod_cast hK1
  have rK2 : (A : ℝ) * v < (K + 1) * 2 ^ 32 := by exact_mod_cast hK2
  have rD1 : (D : ℝ) * 2 ^ 32 ≤ B * e := by exact_mod_cast hD1
  have rD2 : (B : ℝ) * e < (D + 1) * 2 ^ 32 := by exact_mod_cast hD2
  -- the rounding of the two products
  have hK : |(K : ℝ) / 2 ^ 48 - (A : ℝ) / 2 ^ 32 * ((v : ℝ) / 2 ^ 48)| ≤ 1 / 2 ^ 48 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hD : |(D : ℝ) / 2 ^ 48 - (B : ℝ) / 2 ^ 48 * ((e : ℝ) / 2 ^ 32)| ≤ 1 / 2 ^ 48 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  -- the distance of the gains from those of the law
  have hv : |((A : ℝ) / 2 ^ 32 - α) * ((v : ℝ) / 2 ^ 48)| ≤ εA * (|(v : ℝ)| / 2 ^ 48) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 48)]
    exact mul_le_mul_of_nonneg_right hA (by positivity)
  have he : |((B : ℝ) / 2 ^ 48 - β) * ((e : ℝ) / 2 ^ 32)| ≤ εB * (|(e : ℝ)| / 2 ^ 32) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 32)]
    exact mul_le_mul_of_nonneg_right hB (by positivity)
  have hsplit : ((K + D : ℤ) : ℝ) / 2 ^ 48 - (α * ((v : ℝ) / 2 ^ 48) + β * ((e : ℝ) / 2 ^ 32))
      = ((K : ℝ) / 2 ^ 48 - (A : ℝ) / 2 ^ 32 * ((v : ℝ) / 2 ^ 48))
        + ((D : ℝ) / 2 ^ 48 - (B : ℝ) / 2 ^ 48 * ((e : ℝ) / 2 ^ 32))
        + (((A : ℝ) / 2 ^ 32 - α) * ((v : ℝ) / 2 ^ 48))
        + (((B : ℝ) / 2 ^ 48 - β) * ((e : ℝ) / 2 ^ 32)) := by
    push_cast
    ring
  rw [hsplit]
  have h1 := abs_add_le
    (((K : ℝ) / 2 ^ 48 - (A : ℝ) / 2 ^ 32 * ((v : ℝ) / 2 ^ 48))
      + ((D : ℝ) / 2 ^ 48 - (B : ℝ) / 2 ^ 48 * ((e : ℝ) / 2 ^ 32))
      + (((A : ℝ) / 2 ^ 32 - α) * ((v : ℝ) / 2 ^ 48)))
    (((B : ℝ) / 2 ^ 48 - β) * ((e : ℝ) / 2 ^ 32))
  have h2 := abs_add_le
    (((K : ℝ) / 2 ^ 48 - (A : ℝ) / 2 ^ 32 * ((v : ℝ) / 2 ^ 48))
      + ((D : ℝ) / 2 ^ 48 - (B : ℝ) / 2 ^ 48 * ((e : ℝ) / 2 ^ 32)))
    (((A : ℝ) / 2 ^ 32 - α) * ((v : ℝ) / 2 ^ 48))
  have h3 := abs_add_le
    ((K : ℝ) / 2 ^ 48 - (A : ℝ) / 2 ^ 32 * ((v : ℝ) / 2 ^ 48))
    ((D : ℝ) / 2 ^ 48 - (B : ℝ) / 2 ^ 48 * ((e : ℝ) / 2 ^ 32))
  linarith

/-- What the best law for the weight `a⁴` has a cycle read further than the
schedule advances, from the state `x` of the distance behind and the pace: the
pace `x.2` and the law's change of it. It is the number that the code's is
held against in `law_close`. -/
theorem planned {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    x.2 + law (gainFor a) x = modulus a ^ 2 * x.2 + a ^ 2 * modulus a * x.1 := by
  simp only [law]
  rw [gainE_gainFor ha]
  simp only [gainFor]
  ring

/-- **What a distance from the law costs.** A cycle whose change of the pace
is `ε` away from the law's costs, with all the cycles after it under the law,
`ε² / (1 - g)` more than the least: for the gain of `a` that is `ε² / d²`. -/
theorem cost_of_distance {a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) (ε : ℝ) :
    cost (gainFor a) x (law (gainFor a) x + ε)
        + value (gainFor a) (next x (law (gainFor a) x + ε) 0)
      = value (gainFor a) x + ε ^ 2 / modulus a ^ 2 := by
  rw [cost_add_value (gainFor_pos ha) (gainFor_lt_one ha)]
  simp only [gainFor]
  ring

end Unisono.Model.Gains
