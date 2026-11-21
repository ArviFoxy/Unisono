/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed
public import Unisono.Lists

/-!
# The estimator of a clock relation

What the functions of `unisono_core::relation` compute.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Relation

open Unisono.Lists

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
@[step]
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

/-- Two estimators that differ at most in the samples they keep and in how
many. -/
def SameBesidesKept {M : Std.Usize} (e' e : relation.Estimator M) : Prop :=
  e'.span = e.span ∧ e'.limit = e.limit ∧ e'.latest = e.latest
  ∧ e'.window = e.window ∧ e'.lowest = e.lowest ∧ e'.line = e.line

theorem SameBesidesKept.refl {M : Std.Usize} (e : relation.Estimator M) :
    SameBesidesKept e e := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameBesidesKept.trans {M : Std.Usize} {a b c : relation.Estimator M}
    (h1 : SameBesidesKept a b) (h2 : SameBesidesKept b c) : SameBesidesKept a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6⟩

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
      (r.2.2.2.2.2.2.2.val = e.len.val - count.val)
      ∧ r.1.val.take r.2.2.2.2.2.2.2.val = (keptList e).drop count.val
      ∧ r.2.1 = e.span ∧ r.2.2.1 = e.limit ∧ r.2.2.2.1 = e.latest
      ∧ r.2.2.2.2.1 = e.window ∧ r.2.2.2.2.2.1 = e.lowest
      ∧ r.2.2.2.2.2.2.1 = e.line ⦄ := by
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
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hrest
      refine ⟨hto, ?_, g1, g2, g3, g4, g5, g6⟩
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
  · step as ⟨a, sp, lim, hw, wi, lo, li, left, p1, p2, p3, p4, p5, p6, p7, p8⟩
    exact ⟨p2, p1, p3, p4, p5, p6, p7, p8⟩

/-- Dropping the first `n` of a list is dropping while a test holds, when the
first `n` pass the test and the next one, if there is one, does not. -/
theorem drop_eq_dropWhile {α : Type} (p : α → Bool) (l : List α) (n : ℕ)
    (h1 : ∀ k, k < n → ∀ s, l[k]? = some s → p s = true)
    (h2 : ∀ s, l[n]? = some s → p s = false) (hn : n ≤ l.length) :
    l.drop n = l.dropWhile p := by
  induction l generalizing n with
  | nil => simp
  | cons hd tl ih =>
    cases n with
    | zero =>
      have := h2 hd (by simp)
      simp [List.dropWhile, this]
    | succ m =>
      have hhd := h1 0 (by omega) hd (by simp)
      rw [List.drop_succ_cons, List.dropWhile_cons, hhd]
      simp only [ite_true]
      apply ih m
      · intro k hk s hs
        exact h1 (k + 1) (by omega) s (by simpa using hs)
      · intro s hs
        exact h2 s (by simpa using hs)
      · simpa using hn

@[step]
theorem forget_before_loop_spec {M : Std.Usize} (e : relation.Estimator M) (time : Std.I64) :
    relation.Estimator.forget_before_loop e time 0#usize ⦃ r =>
      r.1 = e.kept ∧ r.2.1 = e.len ∧ r.2.2.1 = e.span ∧ r.2.2.2.1 = e.limit
      ∧ r.2.2.2.2.1 = e.latest ∧ r.2.2.2.2.2.1 = e.window
      ∧ r.2.2.2.2.2.2.1 = e.lowest ∧ r.2.2.2.2.2.2.2.1 = e.line
      ∧ r.2.2.2.2.2.2.2.2.val ≤ (keptList e).length
      ∧ (∀ k, k < r.2.2.2.2.2.2.2.2.val → ∀ s, (keptList e)[k]? = some s → s.time.val < time.val)
      ∧ (∀ s, (keptList e)[r.2.2.2.2.2.2.2.2.val]? = some s → ¬ s.time.val < time.val) ⦄ := by
  unfold relation.Estimator.forget_before_loop
  apply loop.spec_decr_nat (measure := fun old : Std.Usize => e.len.val - old.val)
    (inv := fun old : Std.Usize => old.val ≤ (keptList e).length
      ∧ ∀ k, k < old.val → ∀ s, (keptList e)[k]? = some s → s.time.val < time.val)
  · rintro old ⟨hold, hbefore⟩
    unfold relation.Estimator.forget_before_loop.body
    split
    · have hlt : old.val < e.len.val := by scalar_tac
      step as ⟨o, ho⟩
      split
      · -- no sample here: stop
        simp only [WP.spec_ok, true_and]
        refine ⟨hold, hbefore, ?_⟩
        intro s hs
        rw [← ho] at hs
        cases hs
      · rename_i _ sample
        split
        · -- an old sample: go on
          step as ⟨old1, hold1⟩
          have hv : old1.val = old.val + 1 := by
            rw [hold1]; exact Usize.saturating_add_val _ _ (by scalar_tac)
          have hlen : old.val < (keptList e).length := by
            by_contra hcon
            rw [List.getElem?_eq_none (by omega)] at ho
            cases ho
          refine ⟨by omega, ?_, by omega⟩
          intro k hk s hs
          by_cases hko : k < old.val
          · exact hbefore k hko s hs
          · have : k = old.val := by omega
            subst this
            rw [← ho] at hs
            cases hs
            scalar_tac
        · -- a sample that stays: stop
          simp only [WP.spec_ok, true_and]
          refine ⟨hold, hbefore, ?_⟩
          intro s hs
          rw [← ho] at hs
          cases hs
          scalar_tac
    · -- past the kept samples: stop
      have hge : e.len.val ≤ old.val := by scalar_tac
      simp only [WP.spec_ok, true_and]
      refine ⟨hold, hbefore, ?_⟩
      intro s hs
      rw [List.getElem?_eq_none (by simp only [keptList, List.length_take]; omega)] at hs
      cases hs
  · simp

/-- `forget_before` removes the kept samples at the old end whose time is
before `time`, and changes nothing else. -/
@[step]
theorem forget_before_spec {M : Std.Usize} (e : relation.Estimator M) (time : Std.I64)
    (hfit : e.len.val ≤ M.val) :
    relation.Estimator.forget_before e time ⦃ e' =>
      keptList e' = (keptList e).dropWhile (fun s => decide (s.time.val < time.val))
      ∧ e'.len.val = (keptList e').length
      ∧ SameBesidesKept e' e ⦄ := by
  unfold relation.Estimator.forget_before
  step as ⟨a, len, sp, lim, hw, wi, lo, li, old, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩
  subst p1 p2 p3 p4 p5 p6 p7 p8
  have he : (⟨e.kept, e.len, e.span, e.limit, e.latest, e.window, e.lowest, e.line⟩ :
      relation.Estimator M) = e := rfl
  rw [he]
  step as ⟨e', q1, q2, q3⟩
  refine ⟨?_, ?_, q3⟩
  · rw [q1]
    exact drop_eq_dropWhile _ _ _ (fun k hk s hs => by simpa using p10 k hk s hs)
      (fun s hs => by simpa using p11 s hs) p9
  · have hM : e'.kept.val.length = M.val := by scalar_tac
    simp only [keptList, List.length_take]
    omega

/-- Whatever `hull_sample` returns is one of the kept samples. -/
@[step]
theorem hull_sample_spec {M : Std.Usize} (e : relation.Estimator M)
    (hull : Std.Array Std.Usize M) (position : Std.Usize) :
    relation.Estimator.hull_sample e hull position
      ⦃ o => ∀ s, o = some s → s ∈ keptList e ⦄ := by
  unfold relation.Estimator.hull_sample
  simp only [lift, bind_ok, core.slice.Slice.get, core.slice.index.Usize.get]
  cases (Array.to_slice hull)[position]? with
  | none => simp
  | some index =>
    simp only
    step as ⟨o, ho⟩
    rename_i s hs
    rw [hs] at ho
    exact List.mem_of_getElem? ho.symm

/-- The search for the hull's edge around `middle` ends, and a pair it returns
are two kept samples, the first not after `middle`, the second not before it,
and the first earlier than the second. -/
@[step]
theorem bridge_loop1_spec {M : Std.Usize} (e : relation.Estimator M) (middle : Std.I64)
    (hull : Std.Array Std.Usize M) (size edge : Std.Usize) :
    relation.Estimator.bridge_loop1 e.kept e.len e.span e.limit e.latest e.window e.lowest
        e.line middle hull size edge
      ⦃ r => ∀ a b, r = some (a, b) →
        a ∈ keptList e ∧ b ∈ keptList e ∧ a.time.val ≤ middle.val
        ∧ middle.val ≤ b.time.val ∧ a.time.val < b.time.val ⦄ := by
  unfold relation.Estimator.bridge_loop1
  have he : (⟨e.kept, e.len, e.span, e.limit, e.latest, e.window, e.lowest, e.line⟩ :
      relation.Estimator M) = e := rfl
  apply loop.spec_decr_nat (measure := fun edge1 : Std.Usize => size.val - edge1.val)
    (inv := fun _ : Std.Usize => True)
  · intro edge1 _
    unfold relation.Estimator.bridge_loop1.body
    rw [he]
    step as ⟨i4, hi4⟩
    have hi4v : i4.val = min Usize.max (edge1.val + 1) := by
      rw [hi4, Usize.saturating_add_val_min]
      simp
    split
    · have hsz : size.val ≤ Usize.max := by scalar_tac
      have hi4lt : i4.val < size.val := by scalar_tac
      have hnext : edge1.val + 1 < size.val := by
        rcases Nat.le_total Usize.max (edge1.val + 1) with h | h
        · rw [min_eq_left h] at hi4v; omega
        · rw [min_eq_right h] at hi4v; omega
      have hstep : ∀ edge2 : Std.Usize, edge2 = core.num.Usize.saturating_add edge1 1#usize →
          size.val - edge2.val < size.val - edge1.val := by
        intro edge2 h2
        have : edge2.val = edge1.val + 1 := by
          rw [h2]; exact Usize.saturating_add_val _ _ (by scalar_tac)
        omega
      step as ⟨o2, ho2⟩
      split
      · step as ⟨edge2, h2⟩
        exact hstep edge2 h2
      · rename_i _ a
        step as ⟨i5, hi5⟩
        step as ⟨o3, ho3⟩
        split
        · step as ⟨edge2, h2⟩
          exact hstep edge2 h2
        · rename_i _ b
          split
          · split
            · split
              · simp only [WP.spec_ok]
                intro a' b' hab
                cases hab
                exact ⟨ho2 a rfl, ho3 b rfl, by scalar_tac, by scalar_tac, by scalar_tac⟩
              · step as ⟨edge2, h2⟩
                exact hstep edge2 h2
            · step as ⟨edge2, h2⟩
              exact hstep edge2 h2
          · step as ⟨edge2, h2⟩
            exact hstep edge2 h2
    · simp
  · trivial

/-- The loop that removes samples from the end of the hull ends. -/
@[step]
theorem bridge_loop0_loop0_spec {M : Std.Usize} (e : relation.Estimator M)
    (hull : Std.Array Std.Usize M) (size : Std.Usize) (candidate : relation.Sample) :
    relation.Estimator.bridge_loop0_loop0 e.kept e.len e.span e.limit e.latest e.window
        e.lowest e.line hull size candidate ⦃ _ => True ⦄ := by
  unfold relation.Estimator.bridge_loop0_loop0
  have he : (⟨e.kept, e.len, e.span, e.limit, e.latest, e.window, e.lowest, e.line⟩ :
      relation.Estimator M) = e := rfl
  apply loop.spec_decr_nat (measure := fun size1 : Std.Usize => size1.val)
    (inv := fun _ : Std.Usize => True)
  · intro size1 _
    unfold relation.Estimator.bridge_loop0_loop0.body
    rw [he]
    split
    · have h2 : 2 ≤ size1.val := by scalar_tac
      step as ⟨i4, hi4⟩
      step as ⟨before, hbefore⟩
      step as ⟨i5, hi5⟩
      step as ⟨last, hlast⟩
      split
      · simp
      · split
        · simp
        · step with side_total as ⟨i6⟩
          split
          · step as ⟨size2, hsize2⟩
            have : size2.val = size1.val - 1 := by
              rw [hsize2]; exact Usize.saturating_sub_val _ _
            scalar_tac
          · simp
    · simp
  · trivial

/-- The loop that builds the hull ends, and hands the estimator back as it was. -/
@[step]
theorem bridge_loop0_spec {M : Std.Usize} (e : relation.Estimator M)
    (hull : Std.Array Std.Usize M) (size next : Std.Usize) :
    relation.Estimator.bridge_loop0 e hull size next ⦃ r =>
      r.1 = e.kept ∧ r.2.1 = e.len ∧ r.2.2.1 = e.span ∧ r.2.2.2.1 = e.limit
      ∧ r.2.2.2.2.1 = e.latest ∧ r.2.2.2.2.2.1 = e.window
      ∧ r.2.2.2.2.2.2.1 = e.lowest ∧ r.2.2.2.2.2.2.2.1 = e.line ⦄ := by
  unfold relation.Estimator.bridge_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Std.Array Std.Usize M × Std.Usize × Std.Usize => e.len.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨hull1, size1, next1⟩ _
    unfold relation.Estimator.bridge_loop0.body
    simp only
    split
    · have hlt : next1.val < e.len.val := by scalar_tac
      step as ⟨o, ho⟩
      split
      · simp
      · rename_i _ candidate
        step as ⟨size2⟩
        simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
          core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
        have hnext : (core.num.Usize.saturating_add next1 1#usize).val = next1.val + 1 :=
          Usize.saturating_add_val _ _ (by scalar_tac)
        split
        · simp only [bind_ok, Std.uncurry, WP.spec_ok]
          omega
        · simp only [bind_ok, Std.uncurry, WP.spec_ok]
          omega
    · simp
  · trivial

/-- `bridge` ends, and a pair it returns are two kept samples, the first not
after `middle`, the second not before it, and the first earlier than the
second. -/
@[step]
theorem bridge_spec {M : Std.Usize} (e : relation.Estimator M) (middle : Std.I64) :
    relation.Estimator.bridge e middle
      ⦃ r => ∀ a b, r = some (a, b) →
        a ∈ keptList e ∧ b ∈ keptList e ∧ a.time.val ≤ middle.val
        ∧ middle.val ≤ b.time.val ∧ a.time.val < b.time.val ⦄ := by
  unfold relation.Estimator.bridge
  simp only
  step as ⟨a, len, sp, lim, hw, wi, lo, li, hull1, size, p1, p2, p3, p4, p5, p6, p7, p8⟩
  subst p1 p2 p3 p4 p5 p6 p7 p8
  exact bridge_loop1_spec e middle hull1 size 0#usize

theorem slope_within_total (rise run limit : Std.I64) :
    relation.slope_within rise run limit ⦃ _ => True ⦄ := by
  unfold relation.slope_within
  step*
  split <;> step*

/-- The search for the sample that lies lowest against a slope ends, and
returns the sample it started from or a kept sample. -/
@[step]
theorem lowest_against_spec {M : Std.Usize} (e : relation.Estimator M)
    (start : relation.Sample) (rise : Std.I64) :
    relation.Estimator.lowest_against e start rise
      ⦃ r => r = start ∨ r ∈ keptList e ⦄ := by
  unfold relation.Estimator.lowest_against relation.Estimator.lowest_against_loop
  apply loop.spec_decr_nat
    (measure := fun x : relation.Sample × Std.Usize => e.len.val - x.2.val)
    (inv := fun x : relation.Sample × Std.Usize => x.1 = start ∨ x.1 ∈ keptList e)
  · rintro ⟨lowest, index⟩ hinv
    simp only at hinv
    unfold relation.Estimator.lowest_against_loop.body
    simp only
    split
    · have hlt : index.val < e.len.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add index 1#usize).val = index.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      step as ⟨o, ho⟩
      cases o with
      | none =>
        simp only [bind_ok]
        step as ⟨index1, hindex1⟩
        refine ⟨hinv, ?_⟩
        show e.len.val - index1.val < e.len.val - index.val
        rw [hindex1]; omega
      | some sample =>
        have hmem : sample ∈ keptList e := List.mem_of_getElem? ho.symm
        simp only
        rw [Aeneas.Std.bind_assoc]
        step with side_total as ⟨i2⟩
        split
        · simp only [bind_ok]
          step as ⟨index1, hindex1⟩
          refine ⟨Or.inr hmem, ?_⟩
          show e.len.val - index1.val < e.len.val - index.val
          rw [hindex1]; omega
        · simp only [bind_ok]
          step as ⟨index1, hindex1⟩
          refine ⟨hinv, ?_⟩
          show e.len.val - index1.val < e.len.val - index.val
          rw [hindex1]; omega
    · simp only [WP.spec_ok]
      exact hinv
  · exact Or.inl rfl

/-- A sample whose numbers leave room for a second and for the limit of a
slope to be added: an eighth of the range of a 64-bit integer, 36 years in
nanoseconds on either side of zero. -/
def Tiny (s : relation.Sample) : Prop :=
  -2^60 ≤ s.time.val ∧ s.time.val ≤ 2^60 ∧ -2^60 ≤ s.value.val ∧ s.value.val ≤ 2^60

theorem Tiny.small {s : relation.Sample} (h : Tiny s) : Small s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A stored line is sound for a list of samples: its run is positive, it
passes through one of the samples, and every sample lies on or above it. The
last is stated without division: `run * (value - a.value) ≥ rise * (time - a.time)`. -/
def LineUnder (l : relation.Line) (kept : List relation.Sample) : Prop :=
  0 < l.run.val ∧ ∃ a ∈ kept, l.time = a.time ∧ l.value = a.value ∧
    ∀ s ∈ kept,
      0 ≤ l.run.val * (s.value.val - a.value.val) - l.rise.val * (s.time.val - a.time.val)

/-- The times of samples less `first`, added up. -/
def timesFrom (first : ℤ) (kept : List relation.Sample) : ℤ :=
  (kept.map fun s => s.time.val - first).sum

theorem timesFrom_append (first : ℤ) (l : List relation.Sample) (x : relation.Sample) :
    timesFrom first (l ++ [x]) = timesFrom first l + (x.time.val - first) := by
  simp [timesFrom]

/-- `mean_time` returns the mean of the times of the kept samples, rounded
down: `first` and the mean of the times less `first`. -/
theorem mean_time_spec {M : Std.Usize} (e : relation.Estimator M) (first : Std.I64)
    (htiny : ∀ s ∈ keptList e, Tiny s) (hfirst : -2^60 ≤ first.val ∧ first.val ≤ 2^60)
    (hlen : 0 < e.len.val ∧ e.len.val < 2^62) :
    relation.Estimator.mean_time e first
      ⦃ r => r.val = first.val + timesFrom first.val (keptList e) / e.len.val ⦄ := by
  unfold relation.Estimator.mean_time relation.Estimator.mean_time_loop
  apply WP.spec_bind
    (Pₘ := fun p : Std.Usize × Std.I128 => p.1 = e.len
      ∧ p.2.val = timesFrom first.val (keptList e)
      ∧ -((e.len.val : ℤ) * 2^61) ≤ p.2.val ∧ p.2.val ≤ (e.len.val : ℤ) * 2^61)
  · apply loop.spec_decr_nat
      (measure := fun p : Std.I128 × Std.Usize => e.len.val - p.2.val)
      (inv := fun p : Std.I128 × Std.Usize => p.2.val ≤ e.len.val
        ∧ p.1.val = timesFrom first.val ((keptList e).take p.2.val)
        ∧ -((p.2.val : ℤ) * 2^61) ≤ p.1.val ∧ p.1.val ≤ (p.2.val : ℤ) * 2^61)
    · rintro ⟨sum, index⟩ ⟨hle, hsum, hlow, hhigh⟩
      dsimp only at hle hsum hlow hhigh
      unfold relation.Estimator.mean_time_loop.body
      simp only
      split
      · have hlt : index.val < e.len.val := by scalar_tac
        have hnext : (core.num.Usize.saturating_add index 1#usize).val = index.val + 1 :=
          Usize.saturating_add_val _ _ (by scalar_tac)
        have hnextZ : ((core.num.Usize.saturating_add index 1#usize).val : ℤ) = index.val + 1 := by
          rw [hnext]; push_cast; rfl
        step as ⟨o, ho⟩
        split
        · -- no sample at this place: the kept samples end before it
          have hend : (keptList e).length ≤ index.val := List.getElem?_eq_none_iff.mp ho.symm
          simp only [bind_ok, lift, WP.spec_ok, hnext]
          refine ⟨by omega, ?_, by omega, by omega, by omega⟩
          rw [List.take_of_length_le (by omega), hsum, List.take_of_length_le hend]
        · rename_i _ sample
          have hget : (keptList e)[index.val]? = some sample := ho.symm
          obtain ⟨hin, hat⟩ := List.getElem?_eq_some_iff.mp hget
          obtain ⟨t1, t2, -, -⟩ := htiny sample (List.mem_of_getElem? hget)
          have hdiff : (core.num.I128.wrapping_sub (IScalar.cast .I128 sample.time)
              (IScalar.cast .I128 first)).val = sample.time.val - first.val := by
            rw [I128.wrapping_sub_val _ _
              (by rw [I64.cast_I128_val, I64.cast_I128_val]; constructor <;> linarith),
              I64.cast_I128_val, I64.cast_I128_val]
          have hbound : (index.val : ℤ) + 1 ≤ 2^62 := by omega
          have hadd : (core.num.I128.wrapping_add sum
              (core.num.I128.wrapping_sub (IScalar.cast .I128 sample.time)
                (IScalar.cast .I128 first))).val
              = sum.val + (sample.time.val - first.val) := by
            rw [I128.wrapping_add_val _ _ (by rw [hdiff]; constructor <;> linarith), hdiff]
          simp only [bind_ok, lift, WP.spec_ok, hnext, hadd]
          refine ⟨by omega, ?_, by omega, by omega, by omega⟩
          rw [List.take_succ_eq_append_getElem hin, timesFrom_append, hsum, hat]
      · have hend : index.val = e.len.val := by scalar_tac
        rw [WP.spec_ok]
        dsimp only
        refine ⟨rfl, ?_, by rw [← hend]; exact hlow, by rw [← hend]; exact hhigh⟩
        rw [hsum, hend, List.take_of_length_le]
        simp only [keptList, List.length_take]
        exact min_le_left _ _
    · have h0 : (0#usize).val = 0 := rfl
      have h1 : (0#i128).val = 0 := rfl
      dsimp only
      rw [h0, h1]
      exact ⟨Nat.zero_le _, by simp [timesFrom], by norm_num, by norm_num⟩
  · rintro ⟨i, sum⟩ ⟨hi, hsum, hlow, hhigh⟩
    dsimp only at hi hsum hlow hhigh
    simp only [uncurry]
    subst hi
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = first.val := by rw [hi1, I64.cast_I128_val]
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = e.len.val := by rw [hi2, Usize.hcast_I64_val _ (by omega)]
    step as ⟨i3, hi3, hzero⟩
    have hpos : (0 : ℤ) < e.len.val := by exact_mod_cast hlen.1
    have hi3v : i3.val = sum.val / e.len.val := by rw [hi3 (by rw [hi2v]; exact hpos), hi2v]
    have hq1 : sum.val / (e.len.val : ℤ) ≤ 2^61 := Int.ediv_le_of_le_mul hpos (by linarith)
    have hq0 : -2^61 ≤ sum.val / (e.len.val : ℤ) := Int.le_ediv_of_mul_le hpos (by linarith)
    step as ⟨i4, hi4⟩
    have hi4v : i4.val = first.val + sum.val / e.len.val := by
      rw [hi4, I128.wrapping_add_val _ _ (by rw [hi1v, hi3v]; omega), hi1v, hi3v]
    step with Unisono.Fixed.saturate_spec as ⟨i5, hi5⟩
    have hf1 := hfirst.1
    have hf2 := hfirst.2
    rw [hi5, hi4v]
    simp only [Unisono.Fixed.clamp64]
    rw [max_eq_right (by omega), min_eq_left (by omega), hsum]

/-- `slope_within` checks `|rise| * 10^9 ≤ limit * run` without wrapping. -/
theorem slope_within_spec (rise run limit : Std.I64) :
    relation.slope_within rise run limit ⦃ b =>
      b = true ↔ |rise.val| * 10 ^ 9 ≤ limit.val * run.val ⦄ := by
  unfold relation.slope_within
  have hsec : relation.SECOND.val = 10 ^ 9 := by simp [relation.SECOND]
  have hrise : -2 ^ 63 ≤ rise.val ∧ rise.val < 2 ^ 63 := by scalar_tac
  have hlim_run := I64.mul_val_bounds limit run
  step as ⟨wide, hwide⟩
  have hwidev : wide.val = rise.val := by rw [hwide, I64.cast_I128_val]
  have hsize :
      (if wide < 0#i128 then ok (core.num.I128.wrapping_sub 0#i128 wide) else ok wide)
        ⦃ sz => sz.val = |rise.val| ⦄ := by
    split
    · rename_i hlt
      have hneg : rise.val < 0 := by rw [← hwidev]; scalar_tac
      have h0 : (0#i128).val = 0 := rfl
      rw [WP.spec_ok, I128.wrapping_sub_val _ _ (by rw [h0, hwidev]; omega), h0, hwidev,
        abs_of_neg hneg]
      omega
    · rename_i hge
      have hnonneg : 0 ≤ rise.val := by rw [← hwidev]; scalar_tac
      rw [WP.spec_ok, hwidev, abs_of_nonneg hnonneg]
  apply WP.spec_bind hsize
  intro sz hsz
  step as ⟨i, hi⟩
  have hiv : i.val = 10 ^ 9 := by rw [hi, I64.cast_I128_val, hsec]
  step as ⟨i1, hi1⟩
  have habs : 0 ≤ |rise.val| ∧ |rise.val| ≤ 2 ^ 63 := ⟨abs_nonneg _, abs_le.mpr ⟨by omega, by omega⟩⟩
  have hi1v : i1.val = |rise.val| * 10 ^ 9 := by
    rw [hi1, I128.wrapping_mul_val _ _ (by rw [hsz, hiv]; constructor <;> nlinarith), hsz, hiv]
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hi2v : i2.val = limit.val := by rw [hi2, I64.cast_I128_val]
  have hi3v : i3.val = run.val := by rw [hi3, I64.cast_I128_val]
  step as ⟨i4, hi4⟩
  have hi4v : i4.val = limit.val * run.val := by
    rw [hi4, I128.wrapping_mul_val _ _ (by rw [hi2v, hi3v]; constructor <;> linarith), hi2v, hi3v]
  rw [← hi1v, ← hi4v]
  exact ⟨fun h => by scalar_tac, fun h => by scalar_tac⟩

/-- A line that `limited` returns is sound for the kept samples, with `rise`
over one second (`relation.SECOND`). -/
@[step]
theorem limited_spec {M : Std.Usize} (e : relation.Estimator M) (start : relation.Sample)
    (rise : Std.I64) (htiny : ∀ s ∈ keptList e, Tiny s) (hstart : start ∈ keptList e)
    (hrise : -2^60 ≤ rise.val ∧ rise.val ≤ 2^60) :
    relation.Estimator.limited e start rise
      ⦃ r => ∀ l, r = some l →
          LineUnder l (keptList e) ∧ l.rise = rise ∧ l.run = relation.SECOND ⦄ := by
  have hsmall : ∀ s ∈ keptList e, Small s := fun s hs => (htiny s hs).small
  unfold relation.Estimator.limited
  step as ⟨lowest, hlowest⟩
  have hlmem : lowest ∈ keptList e := by
    rcases hlowest with h | h
    · rw [h]; exact hstart
    · exact h
  obtain ⟨t1, t2, t3, t4⟩ := htiny lowest hlmem
  have hslow : Small lowest := hsmall lowest hlmem
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  have hsec : relation.SECOND.val = 1000000000 := by simp [relation.SECOND]
  have hiv : i.val = lowest.time.val + 1000000000 := by
    rw [hi, I64.saturating_add_val, hsec, max_eq_right, min_eq_right] <;> omega
  have hi1v : i1.val = lowest.value.val + rise.val := by
    rw [hi1, I64.saturating_add_val, max_eq_right, min_eq_right] <;> omega
  have hahead : Small ({ time := i, value := i1 } : relation.Sample) :=
    ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega⟩
  step as ⟨b, hb⟩
  split
  · rename_i hbt
    simp only [WP.spec_ok]
    intro l hl
    cases hl
    refine ⟨⟨by simp only; omega, lowest, hlmem, rfl, rfl, ?_⟩, rfl, rfl⟩
    intro s hs
    have := (hb.mp hbt) s hs
    simp only [sideZ, hiv, hi1v] at this
    simp only [hsec]
    linarith
  · simp

/-- A stored line passes through two of the samples, one not after the time
`c` and one not before it, and no sample lies below it. Of all lines under
the samples it is then the highest at `c`; see `Unisono.Estimate`. -/
def LineThrough (l : relation.Line) (kept : List relation.Sample) (c : ℤ) : Prop :=
  ∃ a ∈ kept, ∃ b ∈ kept, a.time.val ≤ c ∧ c ≤ b.time.val ∧ a.time.val < b.time.val
    ∧ l.time = a.time ∧ l.value = a.value
    ∧ l.rise.val = b.value.val - a.value.val ∧ l.run.val = b.time.val - a.time.val
    ∧ ∀ s ∈ kept, 0 ≤ sideZ a b s

/-- The time at which the fit makes the line highest: the mean of the times
of the kept samples, rounded down. -/
def anchor {M : Std.Usize} (e : relation.Estimator M) : ℤ :=
  match (keptList e)[0]? with
  | some first => first.time.val + timesFrom first.time.val (keptList e) / e.len.val
  | none => 0

/-- `fit` changes only the line, and a line it newly stores for two or more
kept samples is sound for them: it passes through a kept sample with no kept
sample below it, its slope stays within `e.limit`, and it is either the line
through two kept samples around the mean of their times or a line at the
slope limit (`±e.limit` over `relation.SECOND`). -/
theorem fit_spec {M : Std.Usize} (e : relation.Estimator M)
    (htiny : ∀ s ∈ keptList e, Tiny s) (hlimit : 0 ≤ e.limit.val ∧ e.limit.val ≤ 2^60)
    (hlen : e.len.val < 2^62) :
    relation.Estimator.fit e ⦃ e' =>
      e'.kept = e.kept ∧ e'.len = e.len ∧ e'.span = e.span ∧ e'.limit = e.limit
      ∧ e'.latest = e.latest ∧ e'.window = e.window ∧ e'.lowest = e.lowest
      ∧ (e.len.val ≠ 1 → e'.line = e.line ∨ e'.line = none
          ∨ ∃ l, e'.line = some l ∧ LineUnder l (keptList e)
              ∧ |l.rise.val| * 10 ^ 9 ≤ e.limit.val * l.run.val
              ∧ (LineThrough l (keptList e) (anchor e)
                  ∨ (l.run = relation.SECOND
                      ∧ (l.rise.val = e.limit.val ∨ l.rise.val = -e.limit.val)))) ⦄ := by
  have hsmall : ∀ s ∈ keptList e, Small s := fun s hs => (htiny s hs).small
  have hsec : relation.SECOND.val = 10 ^ 9 := by simp [relation.SECOND]
  unfold relation.Estimator.fit
  step as ⟨o, ho⟩
  split
  · simp
  · rename_i _ first
    have hget : (keptList e)[0]? = some first := ho.symm
    have hfirst : first ∈ keptList e := List.mem_of_getElem? hget
    have hanchor : anchor e
        = first.time.val + timesFrom first.time.val (keptList e) / e.len.val := by
      simp only [anchor, hget]
    split
    · have h1 : e.len.val = 1 := by scalar_tac
      split <;> simp [h1]
    · have hpos : 0 < e.len.val := by
        have h1 : 0 < (keptList e).length := List.length_pos_of_mem hfirst
        have h2 : (keptList e).length ≤ e.len.val := by
          simp only [keptList, List.length_take]
          exact min_le_left _ _
        omega
      obtain ⟨f1, f2, -, -⟩ := htiny first hfirst
      step with mean_time_spec e first.time htiny ⟨f1, f2⟩ ⟨hpos, hlen⟩ as ⟨mean, hmean⟩
      step as ⟨o2, ho2⟩
      split
      · simp
      · rename_i _ p
        obtain ⟨a, b⟩ := p
        simp only [uncurry]
        obtain ⟨ha, hb, ham, hmb, hab⟩ := ho2 a b rfl
        have hsa : Small a := hsmall a ha
        have hsb : Small b := hsmall b hb
        step as ⟨u, hu⟩
        split
        · rename_i hut
          step as ⟨rise, hrise⟩
          step as ⟨run, hrun⟩
          step with slope_within_spec rise run e.limit as ⟨b1, hb1⟩
          have hrisev : rise.val = b.value.val - a.value.val := by
            rw [hrise]; exact sub_small _ _ ⟨hsb.2.2.1, hsb.2.2.2⟩ ⟨hsa.2.2.1, hsa.2.2.2⟩
          have hrunv : run.val = b.time.val - a.time.val := by
            rw [hrun]; exact sub_small _ _ ⟨hsb.1, hsb.2.1⟩ ⟨hsa.1, hsa.2.1⟩
          split
          · rename_i hb1t
            have hbound : |rise.val| * 10 ^ 9 ≤ e.limit.val * run.val := hb1.mp hb1t
            simp only [WP.spec_ok, true_and]
            intro _
            right; right
            refine ⟨_, rfl, ⟨by simp only; omega, a, ha, rfl, rfl, ?_⟩, hbound, Or.inl ?_⟩
            · intro s hs
              have := (hu.mp hut) s hs
              simp only [sideZ] at this
              simp only [hrisev, hrunv]
              linarith
            · exact ⟨a, ha, b, hb, by rw [hanchor, ← hmean]; exact ham,
                by rw [hanchor, ← hmean]; exact hmb, hab, rfl, rfl, hrisev, hrunv, hu.mp hut⟩
          · have hneg : (core.num.I64.saturating_sub 0#i64 e.limit).val = -e.limit.val := by
              rw [I64.saturating_sub_val, max_eq_right, min_eq_right] <;> simp <;> omega
            have hr1 : -2^60 ≤ (core.num.I64.saturating_sub 0#i64 e.limit).val
                ∧ (core.num.I64.saturating_sub 0#i64 e.limit).val ≤ 2^60 := by
              rw [hneg]; omega
            have hr2 : -2^60 ≤ e.limit.val ∧ e.limit.val ≤ 2^60 := ⟨by omega, hlimit.2⟩
            split
            · simp only [bind_ok]
              step as ⟨o3, ho3⟩
              split
              · simp
              · rename_i _ l
                simp only [WP.spec_ok, true_and]
                intro _
                right; right
                obtain ⟨hunder, hlrise, hlrun⟩ := ho3 l rfl
                have hlv : l.rise.val = -e.limit.val := by rw [hlrise, hneg]
                have hbound : |l.rise.val| * 10 ^ 9 ≤ e.limit.val * l.run.val := by
                  rw [hlv, hlrun, hsec, abs_neg, abs_of_nonneg hlimit.1]
                exact ⟨l, rfl, hunder, hbound, Or.inr ⟨hlrun, Or.inr hlv⟩⟩
            · simp only [bind_ok]
              step as ⟨o3, ho3⟩
              split
              · simp
              · rename_i _ l
                simp only [WP.spec_ok, true_and]
                intro _
                right; right
                obtain ⟨hunder, hlrise, hlrun⟩ := ho3 l rfl
                have hlv : l.rise.val = e.limit.val := by rw [hlrise]
                have hbound : |l.rise.val| * 10 ^ 9 ≤ e.limit.val * l.run.val := by
                  rw [hlv, hlrun, hsec, abs_of_nonneg hlimit.1]
                exact ⟨l, rfl, hunder, hbound, Or.inr ⟨hlrun, Or.inl hlv⟩⟩
        · simp

/-! ## Nothing fails, whatever the state

The statements above say what the functions compute for an estimator in good
order. The ones below ask nothing of the state: each function returns, for
every estimator and every argument. -/

theorem is_under_total {M : Std.Usize} (e : relation.Estimator M) (a b : relation.Sample) :
    relation.Estimator.is_under e a b ⦃ _ => True ⦄ := by
  unfold relation.Estimator.is_under relation.Estimator.is_under_loop
  apply loop.spec_decr_nat (measure := fun i : Std.Usize => e.len.val - i.val)
    (inv := fun _ : Std.Usize => True)
  · intro i _
    unfold relation.Estimator.is_under_loop.body
    split
    · have hlt : i.val < e.len.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o, ho⟩
      split
      · step as ⟨i1, hi1⟩
        rw [hi1]; omega
      · step with side_total as ⟨r⟩
        split
        · simp
        · step as ⟨i1, hi1⟩
          rw [hi1]; omega
    · simp
  · trivial

theorem put_total {M : Std.Usize} (e : relation.Estimator M) (i : Std.Usize)
    (x : relation.Sample) : relation.Estimator.put e i x ⦃ _ => True ⦄ := by
  have h := put_spec e i x
  exact WP.spec_mono h (fun _ _ => trivial)

theorem drop_oldest_total {M : Std.Usize} (e : relation.Estimator M) (count : Std.Usize) :
    relation.Estimator.drop_oldest e count ⦃ _ => True ⦄ := by
  unfold relation.Estimator.drop_oldest
  split
  · simp
  · have hloop : relation.Estimator.drop_oldest_loop e 0#usize count ⦃ _ => True ⦄ := by
      unfold relation.Estimator.drop_oldest_loop
      apply loop.spec_decr_nat
        (measure := fun x : relation.Estimator M × Std.Usize × Std.Usize =>
          x.1.len.val - x.2.2.val)
        (inv := fun _ => True)
      · rintro ⟨self1, to1, from1⟩ _
        unfold relation.Estimator.drop_oldest_loop.body
        simp only
        split
        · have hlt : from1.val < self1.len.val := by scalar_tac
          have hnext : (core.num.Usize.saturating_add from1 1#usize).val = from1.val + 1 :=
            Usize.saturating_add_val _ _ (by scalar_tac)
          step as ⟨o, ho⟩
          cases o with
          | none =>
            simp only [bind_ok]
            step as ⟨to2, hto2⟩
            step as ⟨from2, hfrom2⟩
            show self1.len.val - from2.val < self1.len.val - from1.val
            rw [hfrom2]; omega
          | some x =>
            simp only
            rw [Aeneas.Std.bind_assoc]
            step as ⟨r, hr1, hr2, hr3, hr4⟩
            obtain ⟨b, self2⟩ := r
            simp only [uncurry, bind_ok] at hr3 ⊢
            step as ⟨to2, hto2⟩
            step as ⟨from2, hfrom2⟩
            show self2.len.val - from2.val < self1.len.val - from1.val
            rw [hfrom2, hr3]; omega
        · simp
      · trivial
    step with hloop as ⟨r⟩

theorem forget_before_total {M : Std.Usize} (e : relation.Estimator M) (time : Std.I64) :
    relation.Estimator.forget_before e time ⦃ _ => True ⦄ := by
  unfold relation.Estimator.forget_before
  step as ⟨a, len, sp, lim, hw, wi, lo, li, old⟩
  exact drop_oldest_total _ _

theorem limited_total {M : Std.Usize} (e : relation.Estimator M) (start : relation.Sample)
    (rise : Std.I64) : relation.Estimator.limited e start rise ⦃ _ => True ⦄ := by
  unfold relation.Estimator.limited
  step as ⟨lowest⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step with is_under_total as ⟨b⟩
  split <;> simp

theorem saturate_total (x : Std.I128) : fixed.saturate x ⦃ _ => True ⦄ :=
  WP.spec_mono (Unisono.Fixed.saturate_spec x) (fun _ _ => trivial)

theorem mean_time_total {M : Std.Usize} (e : relation.Estimator M) (first : Std.I64) :
    relation.Estimator.mean_time e first ⦃ _ => True ⦄ := by
  unfold relation.Estimator.mean_time relation.Estimator.mean_time_loop
  apply WP.spec_bind (Pₘ := fun _ => True)
  · apply loop.spec_decr_nat
      (measure := fun p : Std.I128 × Std.Usize => e.len.val - p.2.val)
      (inv := fun _ => True)
    · rintro ⟨sum, index⟩ -
      unfold relation.Estimator.mean_time_loop.body
      simp only
      split
      · have hlt : index.val < e.len.val := by scalar_tac
        have hnext : (core.num.Usize.saturating_add index 1#usize).val = index.val + 1 :=
          Usize.saturating_add_val _ _ (by scalar_tac)
        step as ⟨o, ho⟩
        split
        · simp only [bind_ok, lift, WP.spec_ok]
          rw [hnext]; omega
        · simp only [bind_ok, lift, WP.spec_ok]
          rw [hnext]; omega
      · simp
    · trivial
  · rintro ⟨i, sum⟩ -
    simp only [uncurry]
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨i3⟩
    step as ⟨i4, hi4⟩
    exact saturate_total _

theorem fit_total {M : Std.Usize} (e : relation.Estimator M) :
    relation.Estimator.fit e ⦃ _ => True ⦄ := by
  unfold relation.Estimator.fit
  step as ⟨o, ho⟩
  split
  · simp
  · split
    · split <;> simp
    · step with mean_time_total as ⟨mean⟩
      step as ⟨o2, ho2⟩
      split
      · simp
      · rename_i _ p
        obtain ⟨a, b⟩ := p
        simp only [uncurry]
        step with is_under_total as ⟨u⟩
        split
        · step as ⟨rise, hrise⟩
          step as ⟨run, hrun⟩
          step with slope_within_total as ⟨b1⟩
          split
          · simp
          · split
            · simp only [bind_ok]
              step with limited_total as ⟨o3⟩
              split <;> simp
            · simp only [bind_ok]
              step with limited_total as ⟨o3⟩
              split <;> simp
        · simp

/-- Appending a sample when `e.len ≤ M` keeps `e'.len ≤ M`. -/
theorem append_spec {M : Std.Usize} (e : relation.Estimator M) (x : relation.Sample)
    (hlen : e.len.val ≤ M.val) :
    relation.Estimator.append e x ⦃ e' => e'.len.val ≤ M.val ⦄ := by
  unfold relation.Estimator.append
  split
  · rename_i hge
    step with drop_oldest_spec e 1#usize as ⟨e1, hk1, hlen1, hs1⟩
    step with put_spec e1 e1.len x as ⟨ok, e2, hok, hkp2, hlen2, hs2⟩
    split
    · rename_i hokt
      have hlt : e1.len.val < M.val := by rw [hok] at hokt; exact of_decide_eq_true hokt
      step as ⟨i, hi⟩
      rw [hi, Usize.saturating_add_val _ _ (by scalar_tac), hlen2]
      have : (1#usize).val = 1 := rfl
      omega
    · simp only [WP.spec_ok]
      rw [hlen2, hlen1]
      omega
  · simp only [bind_ok]
    step with put_spec e e.len x as ⟨ok, e2, hok, hkp2, hlen2, hs2⟩
    split
    · rename_i hokt
      have hlt : e.len.val < M.val := by rw [hok] at hokt; exact of_decide_eq_true hokt
      step as ⟨i, hi⟩
      rw [hi, Usize.saturating_add_val _ _ (by scalar_tac), hlen2]
      have : (1#usize).val = 1 := rfl
      omega
    · simp only [WP.spec_ok]
      rw [hlen2]
      exact hlen

theorem append_total {M : Std.Usize} (e : relation.Estimator M) (x : relation.Sample) :
    relation.Estimator.append e x ⦃ _ => True ⦄ := by
  unfold relation.Estimator.append
  split
  · step with drop_oldest_total as ⟨e1⟩
    step with put_total as ⟨r⟩
    split
    · step as ⟨i, hi⟩
    · simp
  · simp only [bind_ok]
    step with put_total as ⟨r⟩
    split
    · step as ⟨i, hi⟩
    · simp

/-- Keeping a sample always leaves `e'.len ≤ M`, whatever `e.len` was before. -/
theorem keep_spec {M : Std.Usize} (e : relation.Estimator M) (x : relation.Sample) :
    relation.Estimator.keep e x ⦃ e' => e'.len.val ≤ M.val ⦄ := by
  unfold relation.Estimator.keep relation.Estimator.clear
  have h1 : (if e.len > M then ok { e with len := 0#usize, line := none } else ok e)
      ⦃ e1 => e1.len.val ≤ M.val ⦄ := by
    split
    · simp only [WP.spec_ok]; have : (0#usize).val = 0 := rfl; omega
    · simp only [WP.spec_ok]; scalar_tac
  apply WP.spec_bind h1
  intro e1 he1
  step as ⟨o, ho⟩
  cases o with
  | none =>
    simp only [bind_ok]
    exact append_spec e1 x he1
  | some index =>
    simp only
    step as ⟨last, hlast⟩
    split
    · exact append_spec e1 x he1
    · split
      · step as ⟨i, hi⟩
        step as ⟨i1, hi1⟩
        step as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        split
        · simp only [WP.spec_ok]; exact he1
        · exact append_spec _ x (by dsimp only; have : (0#usize).val = 0 := rfl; omega)
      · exact append_spec e1 x he1

theorem keep_total {M : Std.Usize} (e : relation.Estimator M) (x : relation.Sample) :
    relation.Estimator.keep e x ⦃ _ => True ⦄ :=
  WP.spec_mono (keep_spec e x) fun _ _ => trivial

/-- Ending a window preserves `e'.len ≤ M` whenever `e.len ≤ M` (and enforces it
whenever a sample was kept in the window). -/
theorem end_window_spec {M : Std.Usize} (e : relation.Estimator M) (hlen : e.len.val ≤ M.val) :
    relation.Estimator.end_window e ⦃ e' => e'.len.val ≤ M.val ⦄ := by
  unfold relation.Estimator.end_window
  simp only [core.option.Option.take]
  cases e.lowest with
  | none => simp [hlen]
  | some p =>
    obtain ⟨x, h⟩ := p
    simp only [uncurry]
    step with keep_spec as ⟨e1, he1⟩
    step as ⟨i, hi⟩
    step with forget_before_spec as ⟨e2, hk2, hlen2, hs2⟩
    have hfit : relation.Estimator.fit e2 ⦃ e3 => e3.len = e2.len ⦄ := by
      unfold relation.Estimator.fit
      step as ⟨o, ho⟩
      split
      · simp
      · split
        · split <;> simp
        · step with mean_time_total as ⟨mean⟩
          step as ⟨o2, ho2⟩
          split
          · simp
          · rename_i _ p1
            obtain ⟨a, b⟩ := p1
            simp only [uncurry]
            step with is_under_total as ⟨u⟩
            split
            · step as ⟨rise, hrise⟩
              step as ⟨run, hrun⟩
              step with slope_within_total as ⟨b1⟩
              split
              · simp
              · split
                · simp only [bind_ok]
                  step with limited_total as ⟨o3⟩
                  split <;> simp
                · simp only [bind_ok]
                  step with limited_total as ⟨o3⟩
                  split <;> simp
            · simp
    apply WP.spec_mono hfit
    intro e3 he3
    have hM : e2.kept.val.length = M.val := by scalar_tac
    rw [he3, hlen2]
    simp only [keptList, List.length_take]
    omega

theorem end_window_total {M : Std.Usize} (e : relation.Estimator M) :
    relation.Estimator.end_window e ⦃ _ => True ⦄ := by
  unfold relation.Estimator.end_window
  simp only [core.option.Option.take]
  cases e.lowest with
  | none => simp
  | some p =>
    obtain ⟨x, h⟩ := p
    simp only [uncurry]
    step with keep_total as ⟨e1⟩
    step as ⟨i, hi⟩
    step with forget_before_total as ⟨e2⟩
    exact fit_total _

/-- `Line.eval` computes `clamp64 (l.value + (l.rise * (time - l.time)) / l.run)`
for any line with positive `run`, and `l.value` when `run ≤ 0`. -/
theorem eval_spec (l : relation.Line) (time : Std.I64) :
    relation.Line.eval l time ⦃ r =>
      (0 < l.run.val →
        r.val = Unisono.Fixed.clamp64 (l.value.val + l.rise.val * (time.val - l.time.val) / l.run.val))
      ∧ (l.run.val ≤ 0 → r.val = l.value.val) ⦄ := by
  unfold relation.Line.eval
  have ht : -2 ^ 63 ≤ time.val ∧ time.val < 2 ^ 63 := by scalar_tac
  have hlt : -2 ^ 63 ≤ l.time.val ∧ l.time.val < 2 ^ 63 := by scalar_tac
  have hrise : -2 ^ 63 ≤ l.rise.val ∧ l.rise.val < 2 ^ 63 := by scalar_tac
  have hval : -2 ^ 63 ≤ l.value.val ∧ l.value.val < 2 ^ 63 := by scalar_tac
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨elapsed, hel⟩
  have helv : elapsed.val = time.val - l.time.val := by
    rw [hel, I128.wrapping_sub_val _ _ (by rw [hi, hi1, I64.cast_I128_val, I64.cast_I128_val]; omega),
      hi, hi1, I64.cast_I128_val, I64.cast_I128_val]
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = l.rise.val := by rw [hi2, I64.cast_I128_val]
  have hprod_b : -2 ^ 127 ≤ l.rise.val * (time.val - l.time.val)
      ∧ l.rise.val * (time.val - l.time.val) < 2 ^ 127 := by
    have he_b : -(2 ^ 64 - 1) ≤ time.val - l.time.val ∧ time.val - l.time.val ≤ 2 ^ 64 - 1 := by omega
    have h1 : |l.rise.val| ≤ 2 ^ 63 := abs_le.mpr ⟨by omega, by omega⟩
    have h2 : |time.val - l.time.val| ≤ 2 ^ 64 - 1 := abs_le.mpr he_b
    have hmul : |l.rise.val * (time.val - l.time.val)| ≤ 2 ^ 63 * (2 ^ 64 - 1) := by
      rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    obtain ⟨lo, hi'⟩ := abs_le.mp hmul
    omega
  step as ⟨product, hprod⟩
  have hprodv : product.val = l.rise.val * (time.val - l.time.val) := by
    rw [hprod, I128.wrapping_mul_val _ _ (by rw [hi2v, helv]; exact hprod_b), hi2v, helv]
  step as ⟨change, hch_pos, hch_nonpos⟩
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = l.value.val := by rw [hi3, I64.cast_I128_val]
  step as ⟨i4, hi4⟩
  step with Unisono.Fixed.saturate_spec as ⟨r, hr⟩
  rw [hr, hi4, I128.saturating_add_val, hi3v]
  constructor
  · intro hpos
    rw [hch_pos hpos, hprodv]
    simp only [Unisono.Fixed.clamp64]
    have hq_lo : -2 ^ 127 ≤ l.rise.val * (time.val - l.time.val) / l.run.val :=
      Int.le_ediv_of_mul_le hpos (by nlinarith)
    have hq_hi : l.rise.val * (time.val - l.time.val) / l.run.val ≤ 2 ^ 127 - 1 :=
      Int.ediv_le_of_le_mul hpos (by nlinarith)
    omega
  · intro hnonpos
    rw [hch_nonpos hnonpos]
    simp only [Unisono.Fixed.clamp64]
    omega

theorem eval_total (l : relation.Line) (time : Std.I64) :
    relation.Line.eval l time ⦃ _ => True ⦄ :=
  WP.spec_mono (eval_spec l time) fun _ _ => trivial

@[step]
theorem non_negative_spec (v : Std.I64) :
    relation.non_negative v ⦃ r => 0 ≤ r.val ∧ r.val = max 0 v.val ⦄ := by
  unfold relation.non_negative
  split
  · rw [WP.spec_ok]
    have hlt : v.val < 0 := by scalar_tac
    have h0 : (0#i64).val = 0 := by rfl
    rw [h0]
    exact ⟨le_refl 0, (max_eq_left (by omega)).symm⟩
  · rw [WP.spec_ok]
    have hge : 0 ≤ v.val := by scalar_tac
    exact ⟨hge, (max_eq_right hge).symm⟩

/-- A new estimator holds a `span` and a `limit` that are not negative, and
nothing else: no sample, no line, and no sample taken in. -/
@[step]
theorem new_spec (M : Std.Usize) (span limit : Std.I64) :
    relation.Estimator.new M span limit ⦃ e =>
      0 ≤ e.span.val ∧ e.span.val = max 0 span.val
      ∧ 0 ≤ e.limit.val ∧ e.limit.val = max 0 limit.val
      ∧ e.len.val = 0 ∧ e.latest = core.num.I64.MIN ∧ e.lowest = none ∧ e.line = none ⦄ := by
  unfold relation.Estimator.new
  step as ⟨sp, hsp0, hsp⟩
  step as ⟨lm, hlm0, hlm⟩
  exact ⟨hsp0, hsp, hlm0, hlm, rfl⟩

/-- `remember` clamps negative `span` to zero and leaves everything else untouched. -/
@[step]
theorem remember_spec {M : Std.Usize} (e : relation.Estimator M) (span : Std.I64) :
    relation.Estimator.remember e span ⦃ e' =>
      0 ≤ e'.span.val ∧ e'.span.val = max 0 span.val
      ∧ e'.kept = e.kept ∧ e'.len = e.len ∧ e'.limit = e.limit
      ∧ e'.latest = e.latest ∧ e'.window = e.window
      ∧ e'.lowest = e.lowest ∧ e'.line = e.line ⦄ := by
  unfold relation.Estimator.remember
  step as ⟨sp, hsp0, hsp⟩
  exact ⟨hsp0, hsp⟩

/-- `reset_window` ends the current window and lets the numbering start again
from any number. When the window held no sample, the kept samples and the
line stay as they are. -/
@[step]
theorem reset_window_spec {M : Std.Usize} (e : relation.Estimator M) :
    relation.Estimator.reset_window e ⦃ e' =>
      e'.latest = core.num.I64.MIN ∧ e'.window = 0#u64
      ∧ (e.lowest = none → e'.kept = e.kept ∧ e'.len = e.len ∧ e'.line = e.line) ⦄ := by
  unfold relation.Estimator.reset_window
  cases hlo : e.lowest with
  | none =>
    have hend : relation.Estimator.end_window e ⦃ e1 => e1 = e ⦄ := by
      unfold relation.Estimator.end_window
      simp only [core.option.Option.take, hlo]
      cases e; simp only at hlo; subst hlo; simp
    step with hend as ⟨e1, he1⟩
    rw [he1]
    exact ⟨rfl, rfl, rfl⟩
  | some p =>
    step with end_window_total as ⟨e1⟩
    intro hc; cases hc

/-- `consider` leaves the window and the latest time as they are, and the
window then has a lowest sample. -/
theorem consider_spec {M : Std.Usize} (e : relation.Estimator M) (x : relation.Sample) :
    relation.Estimator.consider e x ⦃ e' =>
      e'.window = e.window ∧ e'.latest = e.latest ∧ e'.lowest ≠ none ⦄ := by
  unfold relation.Estimator.consider
  cases hline : e.line with
  | none =>
    simp only [lift, bind_ok]
    cases hlow : e.lowest with
    | none => simp
    | some p =>
      simp only [bind_ok, uncurry]
      split <;> simp
  | some line =>
    rw [Aeneas.Std.bind_assoc]
    step as ⟨i⟩
    step with eval_total as ⟨i4⟩
    step as ⟨i2⟩
    step as ⟨h1⟩
    cases hlow : e.lowest with
    | none => simp
    | some p =>
      simp only [bind_ok, uncurry]
      split <;> simp

/-- A sample of a window before the one the estimator holds that can come
from a packet which later packets overtook: it is not later than the latest
sample taken in, and not earlier by more than samples are remembered. -/
def Overtaken {M : Std.Usize} (e : relation.Estimator M) (window : Std.U64)
    (x : relation.Sample) : Prop :=
  window.val < e.window.val ∧ x.time.val ≤ e.latest.val
    ∧ e.latest.val - x.time.val ≤ e.span.val

@[step]
theorem overtaken_spec {M : Std.Usize} (e : relation.Estimator M) (time : Std.I64) :
    relation.Estimator.overtaken e time ⦃ b =>
      (b = true ↔ time.val ≤ e.latest.val ∧ e.latest.val - time.val ≤ e.span.val) ⦄ := by
  unfold relation.Estimator.overtaken
  split
  · rename_i hle
    have hle' : time.val ≤ e.latest.val := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    have hiv : i.val = e.latest.val := by rw [hi, I64.cast_I128_val]
    have hi1v : i1.val = time.val := by rw [hi1, I64.cast_I128_val]
    have hi3v : i3.val = e.span.val := by rw [hi3, I64.cast_I128_val]
    have hi2v : i2.val = e.latest.val - time.val := by
      rw [hi2, I128.wrapping_sub_val _ _ (by rw [hiv, hi1v]; scalar_tac), hiv, hi1v]
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨hle', by rw [← hi2v, ← hi3v]; scalar_tac⟩
    · rintro ⟨-, h⟩
      have : i2.val ≤ i3.val := by rw [hi2v, hi3v]; exact h
      scalar_tac
  · rename_i hgt
    simp only [WP.spec_ok]
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩
      exact absurd (by scalar_tac : time ≤ e.latest) hgt

/-- What taking in a sample does, for every state of the estimator.

A sample that can come from an overtaken packet is left out, and the
estimator stays exactly as it is. Every other sample is taken in: the
estimator then holds the sample's window, a lowest sample for it, and a
latest time that is not before the sample's.

A sample that is left out is at most `span` earlier than `latest`, and
`latest` does not change while samples are left out. So from any state, a
stream whose time goes on is taken in from its first sample later than
`latest` on, which comes within `span` of stream time; see `observe_later`
and `observe_in_order`. -/
theorem observe_spec {M : Std.Usize} (e : relation.Estimator M) (window : Std.U64)
    (x : relation.Sample) :
    relation.Estimator.observe e window x ⦃ e' =>
      (Overtaken e window x → e' = e)
      ∧ (¬ Overtaken e window x →
          e'.window = window ∧ x.time.val ≤ e'.latest.val ∧ e'.lowest ≠ none) ⦄ := by
  unfold relation.Estimator.observe
  split
  · rename_i hlt
    have hlt' : window.val < e.window.val := by scalar_tac
    step as ⟨b, hb⟩
    split
    · rename_i hbt
      have hov : Overtaken e window x := ⟨hlt', hb.mp hbt⟩
      simp only [WP.spec_ok]
      exact ⟨fun _ => trivial, fun h => absurd hov h⟩
    · rename_i hbf
      have hnov : ¬ Overtaken e window x := fun h => hbf (hb.mpr h.2)
      step with end_window_total as ⟨e1⟩
      apply WP.spec_mono (consider_spec _ x)
      rintro e' ⟨hw, hl, hlow⟩
      refine ⟨fun h => absurd h hnov, fun _ => ⟨?_, ?_, hlow⟩⟩
      · rw [hw]
      · rw [hl]
  · rename_i hge
    have hnov : ¬ Overtaken e window x := fun h => hge (by have := h.1; scalar_tac)
    have hge' : e.window.val ≤ window.val := by scalar_tac
    split
    · step with end_window_total as ⟨e1⟩
      split
      · simp only [bind_ok]
        apply WP.spec_mono (consider_spec _ x)
        rintro e' ⟨hw, hl, hlow⟩
        refine ⟨fun h => absurd h hnov, fun _ => ⟨hw, ?_, hlow⟩⟩
        rw [hl]
      · rename_i hnl
        simp only [bind_ok]
        apply WP.spec_mono (consider_spec _ x)
        rintro e' ⟨hw, hl, hlow⟩
        refine ⟨fun h => absurd h hnov, fun _ => ⟨hw, ?_, hlow⟩⟩
        rw [hl]
        scalar_tac
    · rename_i hng
      have heq : e.window = window := by scalar_tac
      simp only [uncurry, bind_ok]
      split
      · simp only [bind_ok]
        apply WP.spec_mono (consider_spec _ x)
        rintro e' ⟨hw, hl, hlow⟩
        refine ⟨fun h => absurd h hnov, fun _ => ⟨by rw [hw]; exact heq, ?_, hlow⟩⟩
        rw [hl]
      · rename_i hnl
        simp only [bind_ok]
        apply WP.spec_mono (consider_spec _ x)
        rintro e' ⟨hw, hl, hlow⟩
        refine ⟨fun h => absurd h hnov, fun _ => ⟨by rw [hw]; exact heq, ?_, hlow⟩⟩
        rw [hl]
        scalar_tac

/-- From any state, a sample later than every sample taken in is taken in. -/
theorem observe_later {M : Std.Usize} (e : relation.Estimator M) (window : Std.U64)
    (x : relation.Sample) (h : e.latest.val < x.time.val) :
    relation.Estimator.observe e window x ⦃ e' =>
      e'.window = window ∧ x.time.val ≤ e'.latest.val ∧ e'.lowest ≠ none ⦄ := by
  apply WP.spec_mono (observe_spec e window x)
  rintro e' ⟨-, htaken⟩
  exact htaken (fun hov => by have := hov.2.1; omega)

/-- An estimator takes in every sample of the window it holds or of a later
one. With `observe_spec`: once a sample has been taken in, the samples that
follow it in order are taken in as well. -/
theorem observe_in_order {M : Std.Usize} (e : relation.Estimator M) (window : Std.U64)
    (x : relation.Sample) (h : e.window.val ≤ window.val) :
    relation.Estimator.observe e window x ⦃ e' =>
      e'.window = window ∧ x.time.val ≤ e'.latest.val ∧ e'.lowest ≠ none ⦄ := by
  apply WP.spec_mono (observe_spec e window x)
  rintro e' ⟨-, htaken⟩
  exact htaken (fun hov => by have := hov.1; omega)

/-- Taking in a packet returns, for every state of the estimator and every
packet. With `end_window_total`, no call into the estimator can fail. -/
theorem observe_total {M : Std.Usize} (e : relation.Estimator M) (window : Std.U64)
    (x : relation.Sample) : relation.Estimator.observe e window x ⦃ _ => True ⦄ :=
  WP.spec_mono (observe_spec e window x) (fun _ _ => trivial)

end Unisono.Relation
