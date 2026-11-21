/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The highest line under a set of samples

A packet is delayed and never early, so the value of a sample is the quantity
of interest plus an error that is never negative. The samples then lie on or
above the true relation, and its estimate is a line that lies on or below
every sample and is as high as it can be at a chosen time `c`. Such a line
passes through two samples, one on each side of `c`.

Sample `j` of a finite set `s` has a time `t j` and a value `z j`.
-/

@[expose] public noncomputable section

namespace Unisono.Model.SupportLine

/-- A line, by its value at a time and its slope. -/
structure Line where
  /-- The time at which `value` is the line's value. -/
  time : ℝ
  /-- The value at `time`. -/
  value : ℝ
  /-- The slope. -/
  slope : ℝ

/-- The value of the line at time `x`. -/
def Line.eval (l : Line) (x : ℝ) : ℝ := l.value + l.slope * (x - l.time)

variable {ι : Type*} (s : Finset ι) (t z : ι → ℝ)

/-- The line lies on or below every sample. -/
def Under (l : Line) : Prop := ∀ j ∈ s, l.eval (t j) ≤ z j

/-- The line through samples `p` and `q`. -/
def through (p q : ι) : Line := ⟨t p, z p, (z q - z p) / (t q - t p)⟩

theorem through_eval_left (p q : ι) : (through t z p q).eval (t p) = z p := by
  simp [through, Line.eval]

theorem through_eval_right (p q : ι) (h : t p ≠ t q) : (through t z p q).eval (t q) = z q := by
  have : t q - t p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [through, Line.eval]
  field_simp
  ring

/-- A line's value between two times is at most the larger of two bounds that
hold at those times, when the bounds are themselves values of a line. This is
the one fact about lines that the results below use: a line that is at most
another line at two times is at most that line between them. -/
theorem eval_le_between (l m : Line) (x₁ x₂ c : ℝ) (h₁ : x₁ ≤ c) (h₂ : c ≤ x₂) (h : x₁ < x₂)
    (hl₁ : l.eval x₁ ≤ m.eval x₁) (hl₂ : l.eval x₂ ≤ m.eval x₂) :
    l.eval c ≤ m.eval c := by
  simp only [Line.eval] at *
  -- write c as a mixture of x₁ and x₂
  obtain ⟨μ, hμ0, hμ1, hc⟩ : ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ c = (1 - μ) * x₁ + μ * x₂ := by
    refine ⟨(c - x₁) / (x₂ - x₁), div_nonneg (by linarith) (by linarith), ?_, ?_⟩
    · rw [div_le_one (by linarith)]; linarith
    · have : x₂ - x₁ ≠ 0 := by linarith
      field_simp
      ring
  have e : ∀ k : Line, k.value + k.slope * (c - k.time)
      = (1 - μ) * (k.value + k.slope * (x₁ - k.time))
        + μ * (k.value + k.slope * (x₂ - k.time)) := by
    intro k; rw [hc]; ring
  rw [e l, e m]
  have h1 : 0 ≤ 1 - μ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hl₁ h1, mul_le_mul_of_nonneg_left hl₂ hμ0]

/-- The line through two samples on either side of `c` that lies under all
samples is the highest at `c` of all lines under the samples. -/
theorem highest (p q : ι) (hp : p ∈ s) (hq : q ∈ s) (c : ℝ)
    (hpc : t p ≤ c) (hcq : c ≤ t q) (hpq : t p < t q)
    (l : Line) (hl : Under s t z l) :
    l.eval c ≤ (through t z p q).eval c := by
  refine eval_le_between l (through t z p q) (t p) (t q) c hpc hcq hpq ?_ ?_
  · rw [through_eval_left]; exact hl p hp
  · rw [through_eval_right t z p q hpq.ne]; exact hl q hq

/-- The error of the highest line under the samples, at the time `c` where it
is highest.

`e` is the estimate: a line under all samples that is highest at `c`. `truth`
is a line that the true relation stays within `b` of, on the times of the
samples. Every sample is on or above the true relation, which is what a delay
that is never negative gives. Two samples, `p'` at or before `c` and `q'` at
or after it, are within `ε` of the true relation. Then the estimate is within
`ε + b` of the line `truth` at `c`, on the high side, and within `b` on the
low side. Nothing is assumed about the other samples: a packet that waited in
a queue, or through a pause, lies above the line and does not move it. -/
theorem error_at_centre (e truth : Line) (rel : ι → ℝ) (b ε c : ℝ)
    (he : Under s t z e)
    (hbest : ∀ l, Under s t z l → l.eval c ≤ e.eval c)
    (hnear : ∀ j ∈ s, |rel j - truth.eval (t j)| ≤ b)
    (habove : ∀ j ∈ s, rel j ≤ z j)
    (p' q' : ι) (hp' : p' ∈ s) (hq' : q' ∈ s)
    (hpc : t p' ≤ c) (hcq : c ≤ t q') (hpq : t p' < t q')
    (hcleanp : z p' ≤ rel p' + ε) (hcleanq : z q' ≤ rel q' + ε) :
    truth.eval c - b ≤ e.eval c ∧ e.eval c ≤ truth.eval c + (ε + b) := by
  constructor
  · -- the line `truth` lowered by `b` is under all samples, so the estimate is at least as high
    have hlow : Under s t z ⟨truth.time, truth.value - b, truth.slope⟩ := by
      intro j hj
      have h1 := (abs_le.mp (hnear j hj)).1
      have h2 := habove j hj
      simp only [Line.eval] at *
      linarith
    have := hbest _ hlow
    simp only [Line.eval] at *
    linarith
  · -- the estimate is under the two clean samples, which are close to `truth`
    have key := eval_le_between e ⟨truth.time, truth.value + (ε + b), truth.slope⟩
      (t p') (t q') c hpc hcq hpq ?_ ?_
    · simp only [Line.eval] at *
      linarith
    · have h1 := he p' hp'
      have h2 := (abs_le.mp (hnear p' hp')).2
      simp only [Line.eval] at *
      linarith
    · have h1 := he q' hq'
      have h2 := (abs_le.mp (hnear q' hq')).2
      simp only [Line.eval] at *
      linarith

/-- The error of the highest line under the samples at a time `x` after the
time `c` where it is highest, which is where a schedule needs it.

Under the hypotheses of `error_at_centre`, with the two samples near the true
relation strictly before and after `c`, the error at `c` grows by the lever of
the extrapolation: by `(ε + 2 * b)` for every length `c - t p'` (on the low
side) or `t q' - c` (on the high side) that `x` lies beyond `c`. -/
theorem error_ahead (e truth : Line) (rel : ι → ℝ) (b ε c x : ℝ)
    (he : Under s t z e)
    (hbest : ∀ l, Under s t z l → l.eval c ≤ e.eval c)
    (hnear : ∀ j ∈ s, |rel j - truth.eval (t j)| ≤ b)
    (habove : ∀ j ∈ s, rel j ≤ z j)
    (p' q' : ι) (hp' : p' ∈ s) (hq' : q' ∈ s)
    (hpc : t p' < c) (hcq : c < t q')
    (hcleanp : z p' ≤ rel p' + ε) (hcleanq : z q' ≤ rel q' + ε)
    (hx : c ≤ x) :
    truth.eval x - b - (ε + 2 * b) * (x - c) / (c - t p') ≤ e.eval x
    ∧ e.eval x ≤ truth.eval x + (ε + b) + (ε + 2 * b) * (x - c) / (t q' - c) := by
  obtain ⟨hlo, hhi⟩ := error_at_centre s t z e truth rel b ε c he hbest hnear habove
    p' q' hp' hq' hpc.le hcq.le (by linarith) hcleanp hcleanq
  have hdq : 0 < t q' - c := by linarith
  have hdp : 0 < c - t p' := by linarith
  -- the difference of two lines is a line: its value at `x` from its values at two times
  have hq : e.eval x - truth.eval x
      = (e.eval c - truth.eval c)
        + ((e.eval (t q') - truth.eval (t q')) - (e.eval c - truth.eval c)) * (x - c)
          / (t q' - c) := by
    simp only [Line.eval]
    field_simp
    ring
  have hp : e.eval x - truth.eval x
      = (e.eval c - truth.eval c)
        + ((e.eval c - truth.eval c) - (e.eval (t p') - truth.eval (t p'))) * (x - c)
          / (c - t p') := by
    simp only [Line.eval]
    field_simp
    ring
  -- at the two samples near the true relation the estimate is not far above the line
  have hgq : e.eval (t q') - truth.eval (t q') ≤ ε + b := by
    have h1 := he q' hq'
    have h2 := (abs_le.mp (hnear q' hq')).2
    linarith
  have hgp : e.eval (t p') - truth.eval (t p') ≤ ε + b := by
    have h1 := he p' hp'
    have h2 := (abs_le.mp (hnear p' hp')).2
    linarith
  constructor
  · have : -((ε + 2 * b) * (x - c) / (c - t p'))
        ≤ ((e.eval c - truth.eval c) - (e.eval (t p') - truth.eval (t p'))) * (x - c)
          / (c - t p') := by
      rw [← neg_div]
      apply div_le_div_of_nonneg_right _ hdp.le
      nlinarith
    linarith
  · have : ((e.eval (t q') - truth.eval (t q')) - (e.eval c - truth.eval c)) * (x - c)
          / (t q' - c)
        ≤ (ε + 2 * b) * (x - c) / (t q' - c) := by
      apply div_le_div_of_nonneg_right _ hdq.le
      nlinarith
    linarith

/-- Adding a line to every value, and to a line under the values, keeps it
under them. With `highest`, this is why a change of the sender's clock by an
offset and a rate moves every receiver's estimate by the same line. -/
theorem under_add (l m : Line) (hm : m.time = l.time) (hl : Under s t z l) :
    Under s t (fun j => z j + m.eval (t j))
      ⟨l.time, l.value + m.value, l.slope + m.slope⟩ := by
  intro j hj
  have := hl j hj
  simp only [Line.eval, hm] at *
  linarith

/-! ## In what sense the estimate is the best

Two statements, for a line through two samples on either side of `c` that
lies under all samples.

A line that the samples allow is one that lies on or below every sample,
since a sample is never below the truth. The estimate is such a line, and at
`c` it is the highest of them: so its value there is the least number that
no line the samples allow exceeds. An estimate that is never below the truth
cannot be lower.

When `c` is the mean of the times of the samples, the estimate also has the
smallest sum of the distances by which the samples lie above a line, among
the lines under the samples. That sum is what the likelihood of a line
depends on when the excesses of the samples are independent and exponential,
whatever their rate; so the estimate is then the most likely line. -/

/-- The value of the estimate at `c` is the largest value at `c` of a line
under the samples. -/
theorem estimate_isGreatest (p q : ι) (hp : p ∈ s) (hq : q ∈ s) (c : ℝ)
    (hpc : t p ≤ c) (hcq : c ≤ t q) (hpq : t p < t q)
    (hunder : Under s t z (through t z p q)) :
    IsGreatest {v | ∃ l, Under s t z l ∧ l.eval c = v} ((through t z p q).eval c) := by
  refine ⟨⟨_, hunder, rfl⟩, ?_⟩
  rintro v ⟨l, hl, rfl⟩
  exact highest s t z p q hp hq c hpc hcq hpq l hl

/-- The values of a line at the times of the samples add up to the number of
samples times its value at the mean of the times. -/
theorem sum_eval (l : Line) (hs : s.Nonempty) :
    ∑ j ∈ s, l.eval (t j) = s.card * l.eval ((∑ j ∈ s, t j) / s.card) := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hs).ne'
  simp only [Line.eval, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_sub_distrib]
  field_simp

/-- **The most likely line.** When the estimate is highest at the mean of the
times of the samples, the samples lie above it by no more, added up, than
above any other line under the samples. -/
theorem excess_le (p q : ι) (hp : p ∈ s) (hq : q ∈ s)
    (hpc : t p ≤ (∑ j ∈ s, t j) / s.card) (hcq : (∑ j ∈ s, t j) / s.card ≤ t q)
    (hpq : t p < t q) (l : Line) (hl : Under s t z l) :
    ∑ j ∈ s, (z j - (through t z p q).eval (t j)) ≤ ∑ j ∈ s, (z j - l.eval (t j)) := by
  have hs : s.Nonempty := ⟨p, hp⟩
  have hhigh := highest s t z p q hp hq _ hpc hcq hpq l hl
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_eval s t _ hs, sum_eval s t l hs]
  nlinarith

end Unisono.Model.SupportLine
