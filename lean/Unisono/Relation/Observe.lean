/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Relation.Fit

/-!
# Clock-relation estimator: totality, observation, and evaluation

Unconditional totality proofs, window-closing (`end_window`), line evaluation
(`eval`), and top-level packet observation (`consider`, `overtaken`, `observe`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Relation

open Unisono.Lists

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
