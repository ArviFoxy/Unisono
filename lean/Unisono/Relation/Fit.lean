/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Relation.Hull

/-!
# Clock-relation estimator: line fitting

Slope clamping, mean-time anchor computation, and the lower support-line fit
(`lowest_against`, `mean_time`, `slope_within`, `limited`, `fit`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Relation

open Unisono.Lists

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


end Unisono.Relation
