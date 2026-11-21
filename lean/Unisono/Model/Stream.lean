/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A frame at the receivers of a stream

The quantities of one frame, for receivers `r` of a finite set: the level
`ℓ` that the sender holds for the frame, and for each receiver its timing
error `e r`, positive when the frame leaves late, the delay `D r` with which
the frame is delivered, and the lead `lead r` by which the receiver has to
have it before it is due.

Three statements that the rest of the model rests on.

* A receiver misses the frame exactly when the level is below what the frame
  needs there (`margin_neg_iff`).
* The group of receivers misses the frame exactly when the level is below
  the largest need over the receivers (`group_misses_iff`). So the gaps and
  the missed frames of the group depend on the level and on that largest
  need, and on nothing else.
* The squared timing errors of the receivers add up to their squared
  distances from their mean, which is what is heard as receivers being out
  of step with each other, plus the squared mean for each receiver, which is
  latency (`sum_sq_errors`).

And one about choosing the level and the paces apart. The need of a frame
contains the timing error of the receiver, so the part of the cost that the
level answers is not free of what the regulators do. But timing errors within
`ε` move the need of the group by no more than `ε` (`groupNeed_errors`): what
the group misses at a level with them lies between what it would miss
without them at the levels `ε` above and `ε` below (`group_misses_errors`).
-/

@[expose] public noncomputable section

namespace Unisono.Model.Stream

variable {ι : Type*}

/-- By how much a frame is there before the receiver has to have it. -/
def margin (ℓ : ℝ) (e D lead : ι → ℝ) (r : ι) : ℝ := ℓ + e r - D r - lead r

/-- What a frame needs at a receiver: the level at which it is just there in
time. -/
def need (e D lead : ι → ℝ) (r : ι) : ℝ := D r + lead r - e r

/-- A receiver misses a frame exactly when the level is below what the frame
needs there. -/
theorem margin_neg_iff (ℓ : ℝ) (e D lead : ι → ℝ) (r : ι) :
    margin ℓ e D lead r < 0 ↔ ℓ < need e D lead r := by
  simp only [margin, need]
  constructor <;> intro h <;> linarith

variable [Fintype ι]

/-- What a frame needs of the group: the largest need over the receivers. -/
def groupNeed [Nonempty ι] (e D lead : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (need e D lead)

/-- **The group misses a frame exactly when the level is below the largest
need.** At least one receiver has nothing to play for the frame if and only
if the level is below what the frame needs of the group. -/
theorem group_misses_iff [Nonempty ι] (ℓ : ℝ) (e D lead : ι → ℝ) :
    (∃ r, margin ℓ e D lead r < 0) ↔ ℓ < groupNeed e D lead := by
  simp only [margin_neg_iff, groupNeed, Finset.lt_sup'_iff, Finset.mem_univ, true_and]

/-- The mean of the timing errors of the receivers. -/
def meanError (e : ι → ℝ) : ℝ := (∑ r, e r) / Fintype.card ι

/-- **Out of step, and late together.** The squared timing errors add up to
the squared distances of the errors from their mean, plus the squared mean
once for each receiver. -/
theorem sum_sq_errors [Nonempty ι] (e : ι → ℝ) :
    ∑ r, e r ^ 2 = ∑ r, (e r - meanError e) ^ 2 + Fintype.card ι * meanError e ^ 2 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hexpand : ∀ r, (e r - meanError e) ^ 2
      = e r ^ 2 - 2 * meanError e * e r + meanError e ^ 2 := fun r => by ring
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : ∑ r, e r = Fintype.card ι * meanError e := by
    simp only [meanError]
    field_simp
  rw [hsum]
  ring

/-- **Timing errors move the need of the group by no more than their size.** -/
theorem groupNeed_errors [Nonempty ι] {ε : ℝ} (e D lead : ι → ℝ) (h : ∀ r, |e r| ≤ ε) :
    groupNeed e D lead ≤ groupNeed 0 D lead + ε
      ∧ groupNeed 0 D lead ≤ groupNeed e D lead + ε := by
  constructor
  · refine Finset.sup'_le _ _ fun r _ => ?_
    have h1 : need 0 D lead r ≤ groupNeed 0 D lead :=
      Finset.le_sup' (need 0 D lead) (Finset.mem_univ r)
    have h2 := abs_le.mp (h r)
    simp only [need, Pi.zero_apply] at h1 ⊢
    linarith
  · refine Finset.sup'_le _ _ fun r _ => ?_
    have h1 : need e D lead r ≤ groupNeed e D lead :=
      Finset.le_sup' (need e D lead) (Finset.mem_univ r)
    have h2 := abs_le.mp (h r)
    simp only [need, Pi.zero_apply] at h1 ⊢
    linarith

/-- **The level and the paces can be chosen apart, up to the size of the
timing errors.** With timing errors within `ε`, a frame that the group would
miss at the level `ℓ + ε` without them is missed at `ℓ`, and a frame missed
at `ℓ` would be missed at `ℓ - ε` without them. -/
theorem group_misses_errors [Nonempty ι] {ε : ℝ} (ℓ : ℝ) (e D lead : ι → ℝ)
    (h : ∀ r, |e r| ≤ ε) :
    (ℓ + ε < groupNeed 0 D lead → ℓ < groupNeed e D lead)
      ∧ (ℓ < groupNeed e D lead → ℓ - ε < groupNeed 0 D lead) := by
  obtain ⟨h1, h2⟩ := groupNeed_errors e D lead h
  exact ⟨fun hlt => by linarith, fun hlt => by linarith⟩

/-! ## When a frame is due

A schedule names one frame, captured at `capture` and to be played `level`
after that, and says how the frames after it follow: `rate` frames a second
at a pace of `pace` billionths, with a level whose time runs at `stretch`
billionths of the stream's. Times are in nanoseconds. -/

/-- When the frame `x` places after the schedule's frame is due. -/
def dueTime (capture level rate pace stretch x : ℝ) : ℝ :=
  capture + level + x * (10 ^ 9 * stretch) / (rate * pace)

/-- **The position that is due at a time.** The frame that is due at `t` lies
`(t - capture - level) · rate · pace / (10⁹ · stretch)` places after the
schedule's frame: that position is due at `t`. The code computes it, rounded
down to `2⁻³²` frame (`Unisono.Due.due_spec`). -/
theorem dueTime_position {capture level rate pace stretch : ℝ} (t : ℝ)
    (hrate : 0 < rate) (hpace : 0 < pace) (hstretch : 0 < stretch) :
    dueTime capture level rate pace stretch
        ((t - capture - level) * (rate * pace) / (10 ^ 9 * stretch)) = t := by
  have h1 : rate * pace ≠ 0 := (mul_pos hrate hpace).ne'
  have h2 : (10 : ℝ) ^ 9 * stretch ≠ 0 := (mul_pos (by norm_num) hstretch).ne'
  simp only [dueTime]
  field_simp
  ring

end Unisono.Model.Stream
