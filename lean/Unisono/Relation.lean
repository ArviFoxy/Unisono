/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed

/-!
# The estimator of a clock relation

What the functions of `unisono_core::relation` compute.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Relation

/-- A sample whose time and value are small enough that differences of two
such numbers, and products of two such differences, are computed without
saturation. The bound is a quarter of the range of a 64-bit integer: 146 years
in nanoseconds. -/
def Small (s : relation.Sample) : Prop :=
  -2^61 ≤ s.time.val ∧ s.time.val ≤ 2^61 ∧ -2^61 ≤ s.value.val ∧ s.value.val ≤ 2^61

/-- Where sample `c` lies against the line from `a` to `b`, over the integers:
positive above, zero on, negative below, when `a` is earlier than `b`. -/
def sideZ (a b c : relation.Sample) : ℤ :=
  (b.time.val - a.time.val) * (c.value.val - a.value.val)
    - (b.value.val - a.value.val) * (c.time.val - a.time.val)

theorem side_total (a b c : relation.Sample) : relation.side a b c ⦃ _ => True ⦄ := by
  unfold relation.side
  step*

/-- The difference of two numbers of small samples is computed without saturation. -/
theorem sub_small (x y : Std.I64) (hx : -2^61 ≤ x.val ∧ x.val ≤ 2^61)
    (hy : -2^61 ≤ y.val ∧ y.val ≤ 2^61) :
    (core.num.I64.saturating_sub x y).val = x.val - y.val := by
  rw [I64.saturating_sub_val, max_eq_right, min_eq_right] <;> omega

/-- The product of two differences of numbers of small samples. -/
theorem mul_small (x y : Std.I64) (hx : -2^62 ≤ x.val ∧ x.val ≤ 2^62)
    (hy : -2^62 ≤ y.val ∧ y.val ≤ 2^62) :
    (core.num.I128.wrapping_mul (IScalar.cast .I128 x) (IScalar.cast .I128 y)).val
      = x.val * y.val
    ∧ -2^124 ≤ x.val * y.val ∧ x.val * y.val ≤ 2^124 := by
  have hb : -2^124 ≤ x.val * y.val ∧ x.val * y.val ≤ 2^124 := by
    constructor <;> nlinarith
  refine ⟨?_, hb⟩
  rw [I128.wrapping_mul_val _ _ (by simp; omega)]
  simp

@[step]
theorem side_spec (a b c : relation.Sample) (ha : Small a) (hb : Small b) (hc : Small c) :
    relation.side a b c ⦃ r => r.val = sideZ a b c ⦄ := by
  unfold relation.side
  step*
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  have hrun : run.val = b.time.val - a.time.val := by
    rw [run_post]; exact sub_small _ _ ⟨hb1, hb2⟩ ⟨ha1, ha2⟩
  have hrise : rise.val = b.value.val - a.value.val := by
    rw [rise_post]; exact sub_small _ _ ⟨hb3, hb4⟩ ⟨ha3, ha4⟩
  have hacross : across.val = c.time.val - a.time.val := by
    rw [across_post]; exact sub_small _ _ ⟨hc1, hc2⟩ ⟨ha1, ha2⟩
  have hup : up.val = c.value.val - a.value.val := by
    rw [up_post]; exact sub_small _ _ ⟨hc3, hc4⟩ ⟨ha3, ha4⟩
  obtain ⟨hleft, hl1, hl2⟩ := mul_small run up (by omega) (by omega)
  obtain ⟨hright, hr1, hr2⟩ := mul_small rise across (by omega) (by omega)
  rw [I128.saturating_sub_val, left_post, right_post, i_post, i1_post, i2_post, i3_post,
    hleft, hright, max_eq_right, min_eq_right]
  · simp only [sideZ, hrun, hrise, hacross, hup]
  · omega
  · rw [min_eq_right] <;> omega

/-- The samples an estimator keeps, oldest first. -/
def keptList {M : Std.Usize} (e : relation.Estimator M) : List relation.Sample :=
  e.kept.val.take e.len.val

@[step]
theorem sample_spec {M : Std.Usize} (e : relation.Estimator M) (i : Std.Usize) :
    relation.Estimator.sample e i ⦃ o => o = (keptList e)[i.val]? ⦄ := by
  unfold relation.Estimator.sample
  step*
  · have : e.len.val ≤ i.val := by scalar_tac
    simp [keptList, this]
  · have hlt : i.val < e.len.val := by scalar_tac
    have hs : s[i]? = (keptList e)[i.val]? := by
      rw [s_post]
      simp [keptList, hlt]
    simp only [core.slice.Slice.get, core.slice.index.Usize.get, hs]
    cases (keptList e)[i.val]? <;> simp

/-- `is_under` answers whether every kept sample lies on or above the line
from `a` to `b`. -/
theorem is_under_spec {M : Std.Usize} (e : relation.Estimator M) (a b : relation.Sample)
    (hsmall : ∀ s ∈ keptList e, Small s) (ha : Small a) (hb : Small b) :
    relation.Estimator.is_under e a b
      ⦃ r => (r = true ↔ ∀ s ∈ keptList e, 0 ≤ sideZ a b s) ⦄ := by
  unfold relation.Estimator.is_under relation.Estimator.is_under_loop
  apply loop.spec_decr_nat (measure := fun i : Std.Usize => e.len.val - i.val)
    (inv := fun i : Std.Usize =>
      ∀ k, k < i.val → ∀ s, (keptList e)[k]? = some s → 0 ≤ sideZ a b s)
  · intro i hinv
    unfold relation.Estimator.is_under_loop.body
    split
    · have hlt : i.val < e.len.val := by scalar_tac
      step as ⟨o, ho⟩
      split
      · -- no sample at this place: go on
        step as ⟨i1, hi1⟩
        have hv : i1.val = i.val + 1 := by
          rw [hi1]; exact Usize.saturating_add_val _ _ (by scalar_tac)
        refine ⟨?_, by omega⟩
        intro k hk s hs
        by_cases hki : k < i.val
        · exact hinv k hki s hs
        · have : k = i.val := by omega
          subst this
          rw [← ho] at hs
          cases hs
      · -- a sample: test its side
        rename_i _ sample
        have hmem : sample ∈ keptList e := List.mem_of_getElem? ho.symm
        have hsmall' : Small sample := hsmall sample hmem
        step as ⟨r, hr⟩
        split
        · -- below the line: the answer is no
          have hneg : sideZ a b sample < 0 := by scalar_tac
          simp only [WP.spec_ok]
          constructor
          · intro h; cases h
          · intro h
            have := h sample hmem
            omega
        · step as ⟨i1, hi1⟩
          have hv : i1.val = i.val + 1 := by
            rw [hi1]; exact Usize.saturating_add_val _ _ (by scalar_tac)
          have hpos : 0 ≤ sideZ a b sample := by scalar_tac
          refine ⟨?_, by omega⟩
          intro k hk s hs
          by_cases hki : k < i.val
          · exact hinv k hki s hs
          · have : k = i.val := by omega
            subst this
            rw [← ho] at hs
            cases hs
            exact hpos
    · -- past the last kept sample: the answer is yes
      have hge : e.len.val ≤ i.val := by scalar_tac
      simp only [WP.spec_ok, true_iff]
      intro s hs
      obtain ⟨k, hk, hks⟩ := List.getElem_of_mem hs
      have hklen : k < e.len.val := by
        have := hk
        simp only [keptList, List.length_take] at this
        omega
      exact hinv k (by omega) s (by rw [List.getElem?_eq_getElem hk, hks])
  · intro k hk
    simp at hk

end Unisono.Relation
