/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Relation
public import Unisono.Model.SupportLine
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The line that the estimator stores, against the best line

`Unisono.Relation.fit_spec` says of a line that the estimator newly stores,
when its slope is within the limit: it passes through two kept samples, one
not after the mean of the times of the kept samples and one not before it,
and no kept sample lies below it (`LineThrough`). That statement is about
whole numbers. This file reads the samples and the line as real numbers and
draws the conclusions of `Unisono.Model.SupportLine` for the line of the
code:

* it lies under every kept sample, and at the mean of the times, rounded
  down to a whole nanosecond, no line under the kept samples is higher
  (`through_best`);
* the kept samples lie above it by no more, added up, than above any other
  line under them, but for the number of samples times the difference of the
  two slopes, in nanoseconds: the mean was rounded by less than one
  (`through_excess`).
-/

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result
open unisono_core
open Unisono.Model.SupportLine

namespace Unisono.Relation

/-- The times of the samples of a list, as real numbers. -/
def times (kept : List relation.Sample) (i : Fin kept.length) : ℝ := (kept[i.1].time.val : ℝ)

/-- The values of the samples of a list, as real numbers. -/
def values (kept : List relation.Sample) (i : Fin kept.length) : ℝ := (kept[i.1].value.val : ℝ)

/-- A stored line as a line of real numbers. -/
def realLine (l : relation.Line) : Line :=
  ⟨(l.time.val : ℝ), (l.value.val : ℝ), (l.rise.val : ℝ) / (l.run.val : ℝ)⟩

/-- A line through two samples around a time, under all samples, read in
real numbers: it is the line of `Unisono.Model.SupportLine.through` for two
places of the list, the time lies between them, and it is under all
samples. -/
theorem through_real {l : relation.Line} {kept : List relation.Sample} {c : ℤ}
    (h : LineThrough l kept c) :
    ∃ p q : Fin kept.length,
      realLine l = through (times kept) (values kept) p q
        ∧ times kept p ≤ (c : ℝ) ∧ (c : ℝ) ≤ times kept q ∧ times kept p < times kept q
        ∧ Under Finset.univ (times kept) (values kept) (realLine l) := by
  obtain ⟨a, ha, b, hb, hac, hcb, hab, htime, hvalue, hrise, hrun, hside⟩ := h
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
  have hline : realLine l = through (times kept) (values kept) ⟨i, hi⟩ ⟨j, hj⟩ := by
    simp only [realLine, through, times, values, hia, hjb, htime, hvalue, hrise, hrun]
    push_cast
    rfl
  have hrunpos : (0 : ℝ) < (b.time.val : ℝ) - (a.time.val : ℝ) := by
    have : (a.time.val : ℝ) < (b.time.val : ℝ) := by exact_mod_cast hab
    linarith
  refine ⟨⟨i, hi⟩, ⟨j, hj⟩, hline, ?_, ?_, ?_, ?_⟩
  · simp only [times, hia]
    exact_mod_cast hac
  · simp only [times, hjb]
    exact_mod_cast hcb
  · simp only [times, hia, hjb]
    exact_mod_cast hab
  · intro k _
    have hk : kept[k.1] ∈ kept := List.getElem_mem k.2
    have hs : (0 : ℝ) ≤ ((b.time.val : ℝ) - a.time.val) * ((kept[k.1].value.val : ℝ) - a.value.val)
        - ((b.value.val : ℝ) - a.value.val) * ((kept[k.1].time.val : ℝ) - a.time.val) := by
      have := hside _ hk
      simp only [sideZ] at this
      exact_mod_cast this
    simp only [realLine, Line.eval, times, values, htime, hvalue, hrise, hrun]
    push_cast
    have hdiv : ((b.value.val : ℝ) - a.value.val) / ((b.time.val : ℝ) - a.time.val)
          * ((kept[k.1].time.val : ℝ) - a.time.val)
        ≤ (kept[k.1].value.val : ℝ) - a.value.val := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hrunpos]
      linarith
    linarith

/-- **The stored line is the highest at the mean of the times.** It lies
under every sample, and at `c` no line under the samples is higher. -/
theorem through_best {l : relation.Line} {kept : List relation.Sample} {c : ℤ}
    (h : LineThrough l kept c) :
    Under Finset.univ (times kept) (values kept) (realLine l)
      ∧ ∀ m : Line, Under Finset.univ (times kept) (values kept) m →
          m.eval c ≤ (realLine l).eval c := by
  obtain ⟨p, q, hline, hpc, hcq, hpq, hunder⟩ := through_real h
  refine ⟨hunder, fun m hm => ?_⟩
  rw [hline]
  exact highest Finset.univ (times kept) (values kept) p q (Finset.mem_univ _)
    (Finset.mem_univ _) c hpc hcq hpq m hm

/-- **The stored line is the most likely line, up to the rounding of the
mean.** When the time `c` is within one nanosecond of the mean of the times
of the samples, the samples lie above the stored line by no more, added up,
than above any other line under them, but for the number of samples times
the difference of the two slopes. -/
theorem through_excess {l : relation.Line} {kept : List relation.Sample} {c : ℤ}
    (h : LineThrough l kept c)
    (hmean : |(∑ i, times kept i) / (kept.length : ℝ) - (c : ℝ)| ≤ 1)
    (m : Line) (hm : Under Finset.univ (times kept) (values kept) m) :
    ∑ i, (values kept i - (realLine l).eval (times kept i))
      ≤ ∑ i, (values kept i - m.eval (times kept i))
        + kept.length * |m.slope - (realLine l).slope| := by
  obtain ⟨p, q, hline, hpc, hcq, hpq, -⟩ := through_real h
  have hnear := excess_near Finset.univ (times kept) (values kept) p q (Finset.mem_univ _)
    (Finset.mem_univ _) c hpc hcq hpq m hm
  rw [← hline] at hnear
  simp only [Finset.card_univ, Fintype.card_fin] at hnear
  have hslope : |m.slope - (realLine l).slope|
        * |(∑ i, times kept i) / (kept.length : ℝ) - (c : ℝ)|
      ≤ |m.slope - (realLine l).slope| := by
    have := mul_le_mul_of_nonneg_left hmean (abs_nonneg (m.slope - (realLine l).slope))
    linarith
  have hlen : (0 : ℝ) ≤ kept.length := by positivity
  have := mul_le_mul_of_nonneg_left hslope hlen
  linarith

/-- The time at which the fit makes the line highest is the mean of the
times of the kept samples, rounded down: within one nanosecond of it. -/
theorem anchor_near_mean {M : Std.Usize} (e : relation.Estimator M)
    (hkept : (keptList e).length = e.len.val) (hpos : 0 < e.len.val) :
    |(∑ i, times (keptList e) i) / ((keptList e).length : ℝ) - (anchor e : ℝ)| ≤ 1 := by
  have hlen : 0 < (keptList e).length := by omega
  obtain ⟨first, hfirst⟩ : ∃ first, (keptList e)[0]? = some first :=
    ⟨(keptList e)[0], List.getElem?_eq_getElem hlen⟩
  have hanchor : anchor e
      = first.time.val + timesFrom first.time.val (keptList e) / e.len.val := by
    simp only [anchor, hfirst]
  -- the sum of the times, in whole numbers
  have hsum : (∑ i, times (keptList e) i)
      = (timesFrom first.time.val (keptList e) : ℝ) + (keptList e).length * first.time.val := by
    have h1 : (∑ i : Fin (keptList e).length, times (keptList e) i)
        = (((keptList e).map fun s => (s.time.val : ℝ))).sum :=
      Fin.sum_univ_fun_getElem (keptList e) (fun s => (s.time.val : ℝ))
    rw [h1]
    simp only [timesFrom]
    induction keptList e with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast at ih ⊢
      linarith
  -- rounding down
  have hn : (0 : ℤ) < (e.len.val : ℤ) := by exact_mod_cast hpos
  have hfloor1 := Int.ediv_mul_le (timesFrom first.time.val (keptList e)) hn.ne'
  have hfloor2 := Int.lt_ediv_add_one_mul_self (timesFrom first.time.val (keptList e)) hn
  have hnr : (0 : ℝ) < (e.len.val : ℝ) := by exact_mod_cast hpos
  have r1 : ((timesFrom first.time.val (keptList e) / (e.len.val : ℤ) : ℤ) : ℝ) * (e.len.val : ℝ)
      ≤ (timesFrom first.time.val (keptList e) : ℝ) := by exact_mod_cast hfloor1
  have r2 : (timesFrom first.time.val (keptList e) : ℝ)
      < (((timesFrom first.time.val (keptList e) / (e.len.val : ℤ) : ℤ) : ℝ) + 1)
        * (e.len.val : ℝ) := by exact_mod_cast hfloor2
  rw [hsum, hanchor, hkept]
  push_cast
  have hmean : ((timesFrom first.time.val (keptList e) : ℝ) + (e.len.val : ℝ) * first.time.val)
        / (e.len.val : ℝ)
      = (timesFrom first.time.val (keptList e) : ℝ) / (e.len.val : ℝ) + first.time.val := by
    field_simp
  rw [hmean, abs_le]
  constructor
  · have : ((timesFrom first.time.val (keptList e) / (e.len.val : ℤ) : ℤ) : ℝ)
        ≤ (timesFrom first.time.val (keptList e) : ℝ) / (e.len.val : ℝ) := by
      rw [le_div_iff₀ hnr]; exact r1
    linarith
  · have : (timesFrom first.time.val (keptList e) : ℝ) / (e.len.val : ℝ)
        < ((timesFrom first.time.val (keptList e) / (e.len.val : ℤ) : ℤ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hnr]; exact r2
    linarith

end Unisono.Relation
