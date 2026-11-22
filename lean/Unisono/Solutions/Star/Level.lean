/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The latency level from the holds

A hold is an episode in which a link keeps the messages sent on it and
releases them when it ends. While a hold lasts, the frames that a receiver
needs arrive late. Suppose the latency level leaves a margin of `m` seconds
above what the other delays use. Then a hold of length `h` makes the
receiver miss the output samples of `(h - m)⁺` seconds, where `x⁺` is the
larger of `x` and zero. When holds start at the rate `λ` per second with
lengths distributed as `μ`, the mean time missed per second is
`λ ∫ (h - m)⁺ dμ`, by Campbell's formula for stationary marked point
processes, as long as holds do not overlap and playback resumes on time
after each of them.

Choosing the level trades latency against missed playback. With a price `a`
per second of latency and a price `b` per second of missed playback, a
margin `m` costs `a m + b ∫ (h - m)⁺ dν` beyond the other delays, where
`ν = λ μ`. When several receivers play at one common level, their measures
add, each shifted by what the other delays use at that receiver, and the
cost has the same form.

The margin `m` is best when `ν {h > m} ≤ a / b ≤ ν {h ≥ m}`
(`margin_best`): the rate of holds longer than the margin is the ratio of
the two prices. The best margin is therefore a quantile of the hold lengths,
and only the tail of their distribution matters.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Star

open MeasureTheory

/-- **The best margin is a quantile of the holds.** Let `ν` be a finite
measure of hold lengths with a finite mean, and let the prices satisfy
`b ν {h > m} ≤ a ≤ b ν {h ≥ m}`. Then the margin `m` costs no more than any
other margin `x`: `a m + b ∫ (h - m)⁺ dν ≤ a x + b ∫ (h - x)⁺ dν`. -/
theorem margin_best (ν : Measure ℝ) [IsFiniteMeasure ν] (hint : Integrable (fun h => h) ν)
    {a b m : ℝ} (hb : 0 ≤ b) (hlow : b * ν.real {h | m < h} ≤ a)
    (hhigh : a ≤ b * ν.real {h | m ≤ h}) (x : ℝ) :
    a * m + b * ∫ h, max (h - m) 0 ∂ν ≤ a * x + b * ∫ h, max (h - x) 0 ∂ν := by
  have hpos : ∀ y : ℝ, Integrable (fun h => max (h - y) 0) ν :=
    fun y => (hint.sub (integrable_const y)).pos_part
  rcases le_total m x with hmx | hxm
  · -- A larger margin saves at most the rate of the longer holds.
    have hs : MeasurableSet {h : ℝ | m < h} := measurableSet_Ioi
    have hind : Integrable ({h : ℝ | m < h}.indicator 1) ν :=
      (integrable_const (1 : ℝ)).indicator hs
    have hpt : ∀ h, max (h - m) 0 - (x - m) * {h : ℝ | m < h}.indicator 1 h
        ≤ max (h - x) 0 := by
      intro h
      by_cases hh : m < h
      · rw [Set.indicator_of_mem (show h ∈ {h : ℝ | m < h} from hh), Pi.one_apply,
          max_eq_left (by linarith)]
        linarith [le_max_left (h - x) 0]
      · rw [Set.indicator_of_notMem (show h ∉ {h : ℝ | m < h} from hh),
          max_eq_right (by linarith)]
        linarith [le_max_right (h - x) 0]
    have hmono : ∫ h, (max (h - m) 0 - (x - m) * {h : ℝ | m < h}.indicator 1 h) ∂ν
        ≤ ∫ h, max (h - x) 0 ∂ν :=
      integral_mono ((hpos m).sub (hind.const_mul (x - m))) (hpos x) hpt
    rw [integral_sub (hpos m) (hind.const_mul (x - m)), integral_const_mul,
      integral_indicator_one hs] at hmono
    nlinarith [mul_le_mul_of_nonneg_left hmono hb,
      mul_nonneg (sub_nonneg.2 hmx) (sub_nonneg.2 hlow)]
  · -- A smaller margin costs at least the rate of the holds that reach it.
    have hs : MeasurableSet {h : ℝ | m ≤ h} := measurableSet_Ici
    have hind : Integrable ({h : ℝ | m ≤ h}.indicator 1) ν :=
      (integrable_const (1 : ℝ)).indicator hs
    have hpt : ∀ h, max (h - m) 0 + (m - x) * {h : ℝ | m ≤ h}.indicator 1 h
        ≤ max (h - x) 0 := by
      intro h
      by_cases hh : m ≤ h
      · rw [Set.indicator_of_mem (show h ∈ {h : ℝ | m ≤ h} from hh), Pi.one_apply,
          max_eq_left (by linarith)]
        linarith [le_max_left (h - x) 0]
      · rw [Set.indicator_of_notMem (show h ∉ {h : ℝ | m ≤ h} from hh),
          max_eq_right (by linarith)]
        linarith [le_max_right (h - x) 0]
    have hmono : ∫ h, (max (h - m) 0 + (m - x) * {h : ℝ | m ≤ h}.indicator 1 h) ∂ν
        ≤ ∫ h, max (h - x) 0 ∂ν :=
      integral_mono ((hpos m).add (hind.const_mul (m - x))) (hpos x) hpt
    rw [integral_add (hpos m) (hind.const_mul (m - x)), integral_const_mul,
      integral_indicator_one hs] at hmono
    nlinarith [mul_le_mul_of_nonneg_left hmono hb,
      mul_nonneg (sub_nonneg.2 hxm) (sub_nonneg.2 hhigh)]

end Unisono.Solutions.Star
