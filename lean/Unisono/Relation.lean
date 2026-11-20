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

theorem set_opt_some {α : Type} (l : List α) (i : ℕ) (x : α) :
    l.set_opt i (some x) = l.set i x := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ n => simp [ih]

theorem set_opt_none {α : Type} (l : List α) (i : ℕ) : l.set_opt i none = l := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    cases i with
    | zero => simp
    | succ n => simp [ih]

/-- Two estimators that differ at most in the samples they keep and in how
many. -/
def SameBesidesKept {M : Std.Usize} (e' e : relation.Estimator M) : Prop :=
  e'.span = e.span ∧ e'.limit = e.limit ∧ e'.window = e.window
  ∧ e'.lowest = e.lowest ∧ e'.line = e.line

theorem SameBesidesKept.refl {M : Std.Usize} (e : relation.Estimator M) :
    SameBesidesKept e e := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SameBesidesKept.trans {M : Std.Usize} {a b c : relation.Estimator M}
    (h1 : SameBesidesKept a b) (h2 : SameBesidesKept b c) : SameBesidesKept a c := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5⟩

/-- `put` writes a sample at a place of the room for kept samples, if the
place exists, and changes nothing else. -/
@[step]
theorem put_spec {M : Std.Usize} (e : relation.Estimator M) (i : Std.Usize)
    (x : relation.Sample) :
    relation.Estimator.put e i x ⦃ r =>
      r.1 = decide (i.val < M.val)
      ∧ r.2.kept.val = (if i.val < M.val then e.kept.val.set i.val x else e.kept.val)
      ∧ r.2.len = e.len ∧ SameBesidesKept r.2 e ⦄ := by
  unfold relation.Estimator.put
  simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
    core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
  have hlen : e.kept.val.length = M.val := by scalar_tac
  have hsl : (Array.to_slice e.kept).val = e.kept.val := by simp [Array.to_slice]
  by_cases hi : i.val < M.val
  · have hget : (Array.to_slice e.kept)[i]? = some (e.kept.val[i.val]'(by omega)) := by
      rw [Slice.getElem?_Usize_eq, hsl]
      exact List.getElem?_eq_getElem (by omega)
    simp only [hget, WP.spec_ok, hi, decide_true, ite_true, true_and]
    refine ⟨?_, SameBesidesKept.refl e⟩
    rw [Array.from_slice_val _ _ (by simp [Slice.set_opt, hsl, hlen])]
    simp [Slice.set_opt, hsl, set_opt_some]
  · have hget : (Array.to_slice e.kept)[i]? = none := by
      rw [Slice.getElem?_Usize_eq, hsl]
      exact List.getElem?_eq_none (by omega)
    simp only [hget, WP.spec_ok, hi, decide_false, ite_false, true_and]
    refine ⟨?_, SameBesidesKept.refl e⟩
    rw [Array.from_slice_val _ _ (by simp [Slice.set_opt, hsl, hlen])]
    simp [Slice.set_opt, hsl, set_opt_none]

/-- The state of the loop of `drop_oldest` after some rounds, against the
estimator `e` it started from: the places before `to` hold what was `count`
places further on, the places from `to` on are as they were, and nothing else
of the estimator has changed. -/
def DropInv {M : Std.Usize} (e : relation.Estimator M) (count : Std.Usize)
    (x : relation.Estimator M × Std.Usize × Std.Usize) : Prop :=
  x.2.2.val = x.2.1.val + count.val
  ∧ (x.2.2.val ≤ e.len.val ∨ x.2.1.val = 0)
  ∧ x.1.len = e.len ∧ SameBesidesKept x.1 e
  ∧ (∀ k, k < x.2.1.val → x.1.kept.val[k]? = e.kept.val[k + count.val]?)
  ∧ (∀ k, x.2.1.val ≤ k → x.1.kept.val[k]? = e.kept.val[k]?)

@[step]
theorem drop_oldest_loop_spec {M : Std.Usize} (e : relation.Estimator M) (count : Std.Usize)
    (hfit : e.len.val ≤ M.val) :
    relation.Estimator.drop_oldest_loop e 0#usize count ⦃ r =>
      (r.2.2.2.2.2.2.val = e.len.val - count.val)
      ∧ r.1.val.take r.2.2.2.2.2.2.val = (keptList e).drop count.val
      ∧ r.2.1 = e.span ∧ r.2.2.1 = e.limit ∧ r.2.2.2.1 = e.window
      ∧ r.2.2.2.2.1 = e.lowest ∧ r.2.2.2.2.2.1 = e.line ⦄ := by
  unfold relation.Estimator.drop_oldest_loop
  apply loop.spec_decr_nat
    (measure := fun x : relation.Estimator M × Std.Usize × Std.Usize => e.len.val - x.2.2.val)
    (inv := DropInv e count)
  · rintro ⟨self1, to1, from1⟩ ⟨hft, hle, hlen, hrest, hshift, hsame⟩
    simp only at hft hle hlen hrest hshift hsame
    unfold relation.Estimator.drop_oldest_loop.body
    simp only
    have hM : e.kept.val.length = M.val := by scalar_tac
    have hM1 : self1.kept.val.length = M.val := by scalar_tac
    split
    · have hfrom : from1.val < e.len.val := by rw [← hlen]; scalar_tac
      step as ⟨o, ho⟩
      obtain ⟨x, hx⟩ : ∃ x, e.kept.val[from1.val]? = some x :=
        ⟨e.kept.val[from1.val]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have ho' : o = some x := by
        rw [ho, keptList, hlen, List.getElem?_take, ite_eq_left hfrom, hsame _ (by omega), hx]
      subst ho'
      simp only
      rw [Aeneas.Std.bind_assoc]
      step as ⟨r, hr1, hr2, hr3, hr4⟩
      obtain ⟨b, self2⟩ := r
      simp only [uncurry, bind_ok] at hr1 hr2 hr3 hr4 ⊢
      step as ⟨to2, hto2⟩
      step as ⟨from2, hfrom2⟩
      have hto2v : to2.val = to1.val + 1 := by
        rw [hto2]; exact Usize.saturating_add_val _ _ (by scalar_tac)
      have hfrom2v : from2.val = from1.val + 1 := by
        rw [hfrom2]; exact Usize.saturating_add_val _ _ (by scalar_tac)
      have hto1M : to1.val < M.val := by omega
      rw [ite_eq_left hto1M] at hr2
      refine ⟨⟨?_, Or.inl ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · show from2.val = to2.val + count.val
        omega
      · show from2.val ≤ e.len.val
        omega
      · show self2.len = e.len
        rw [hr3, hlen]
      · exact hr4.trans hrest
      · intro k hk
        show self2.kept.val[k]? = e.kept.val[k + count.val]?
        have hk' : k < to2.val := hk
        rw [hr2, List.getElem?_set]
        by_cases hkt : to1.val = k
        · subst hkt
          rw [ite_eq_left rfl, ite_eq_left (by omega), ← hft, hx]
        · rw [ite_eq_right hkt]
          exact hshift k (by omega)
      · intro k hk
        show self2.kept.val[k]? = e.kept.val[k]?
        have hk' : to2.val ≤ k := hk
        rw [hr2, List.getElem?_set, ite_eq_right (by omega)]
        exact hsame k (by omega)
      · show e.len.val - from2.val < e.len.val - from1.val
        omega
    · have hge : e.len.val ≤ from1.val := by rw [← hlen]; scalar_tac
      simp only [WP.spec_ok]
      have hto : to1.val = e.len.val - count.val := by omega
      obtain ⟨g1, g2, g3, g4, g5⟩ := hrest
      refine ⟨hto, ?_, g1, g2, g3, g4, g5⟩
      apply List.ext_getElem?
      intro k
      simp only [keptList, List.getElem?_take, List.getElem?_drop]
      by_cases hk : k < to1.val
      · rw [ite_eq_left hk, ite_eq_left (by omega), hshift k hk, Nat.add_comm]
      · rw [ite_eq_right hk, ite_eq_right (by omega)]
  · simp [DropInv, SameBesidesKept.refl]

/-- `drop_oldest` removes the `count` oldest kept samples and changes nothing
else, for an estimator whose count of kept samples fits its room. -/
@[step]
theorem drop_oldest_spec {M : Std.Usize} (e : relation.Estimator M) (count : Std.Usize)
    (hfit : e.len.val ≤ M.val) :
    relation.Estimator.drop_oldest e count ⦃ e' =>
      keptList e' = (keptList e).drop count.val
      ∧ e'.len.val = e.len.val - count.val
      ∧ SameBesidesKept e' e ⦄ := by
  unfold relation.Estimator.drop_oldest
  split
  · have h0 : count.val = 0 := by scalar_tac
    simp [h0, SameBesidesKept.refl]
  · step as ⟨a, sp, lim, wi, lo, li, left, p1, p2, p3, p4, p5, p6, p7⟩
    exact ⟨p2, p1, p3, p4, p5, p6, p7⟩

end Unisono.Relation
