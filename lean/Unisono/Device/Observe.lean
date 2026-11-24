/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Tactic.FieldSimp
public import Unisono.Device.Query
public import Unisono.Model.LineFit

/-!
# Device clock model: report ingestion and `LineFit` equivalence

`shift`, `step`, `observe`, and proofs connecting `beyondZ` / `beyondSlopeQ16Z`
to the real-valued unweighted least-squares line of `Unisono.Model.LineFit`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Device

variable {W : Std.Usize}

/-- Runs a function to its end: step by step, taking conditionals apart. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

/-! ## Taking in a report -/

/-- Moving the times of the kept reports shifts every kept report's timestamp
(saturating to `i64` whenever `b` is in `[-2^126, 2^126]`), leaves positions
and unkept slots untouched, and changes no metadata. -/
theorem shift_spec (d : device.Device W) (b : Std.I128) :
    device.Device.shift d b ⦃ d' =>
      d'.rate = d.rate ∧ d'.aside = d.aside ∧ d'.len = d.len ∧ d'.next = d.next
      ∧ (∀ k, k < min d.len.val (min W.val 4096) → ∀ r, d.readings.val[k]? = some r →
          ∃ r', d'.readings.val[k]? = some r' ∧ r'.position = r.position
            ∧ r'.time.val = Fixed.clamp64 (core.num.I128.wrapping_add (IScalar.cast .I128 r.time) b).val
            ∧ (-2 ^ 126 ≤ b.val → b.val ≤ 2 ^ 126 → r'.time.val = Fixed.clamp64 (r.time.val + b.val)))
      ∧ (∀ k, min d.len.val (min W.val 4096) ≤ k →
          d'.readings.val[k]? = d.readings.val[k]?) ⦄ := by
  unfold device.Device.shift
  step as ⟨kept, hkept, hkeptW, hkeptM⟩
  unfold device.Device.shift_loop
  apply loop.spec_decr_nat
    (measure := fun x : device.Device W × Std.Usize => kept.val - x.2.val)
    (inv := fun x : device.Device W × Std.Usize =>
      x.2.val ≤ kept.val
      ∧ x.1.rate = d.rate ∧ x.1.aside = d.aside ∧ x.1.len = d.len ∧ x.1.next = d.next
      ∧ (∀ k, k < x.2.val → ∀ r, d.readings.val[k]? = some r →
          ∃ r', x.1.readings.val[k]? = some r' ∧ r'.position = r.position
            ∧ r'.time.val = Fixed.clamp64 (core.num.I128.wrapping_add (IScalar.cast .I128 r.time) b).val
            ∧ (-2 ^ 126 ≤ b.val → b.val ≤ 2 ^ 126 → r'.time.val = Fixed.clamp64 (r.time.val + b.val)))
      ∧ (∀ k, x.2.val ≤ k → x.1.readings.val[k]? = d.readings.val[k]?))
  · rintro ⟨s, place⟩ ⟨hple, h1, h2, h3, h4, hdone, hrest⟩
    dsimp only at hple h1 h2 h3 h4 hdone hrest
    unfold device.Device.shift_loop.body
    simp only
    split
    · rename_i hlt
      have hlt' : place.val < kept.val := by scalar_tac
      have hlenW : s.readings.val.length = W.val := s.readings.property
      have hplaceW : place.val < s.readings.val.length := by omega
      have hsucc : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 := by
        rw [Usize.saturating_add_val _ _ (by scalar_tac)]; rfl
      step as ⟨o, ho⟩
      have hsget : s.readings.val[place.val]? = some (s.readings.val[place.val]'hplaceW) :=
        List.getElem?_eq_getElem hplaceW
      have hdget : d.readings.val[place.val]? = some (s.readings.val[place.val]'hplaceW) := by
        rw [← hrest place.val (le_refl _), hsget]
      rw [hsget] at ho
      rw [ho]
      simp only
      set reading := s.readings.val[place.val]'hplaceW
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      step with Fixed.saturate_spec as ⟨i2, hi2⟩
      simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
        core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
      have hslice_get : s.readings.to_slice[place]? = some reading := by
        rw [Slice.getElem?_Usize_eq]
        simpa [Array.to_slice] using hsget
      rw [hslice_get]
      simp only [bind_ok, WP.spec_ok]
      set a := s.readings.from_slice
        (s.readings.to_slice.set_opt place (some { reading with time := i2 }))
      have haval : a.val = s.readings.val.set place.val { reading with time := i2 } := by
        dsimp only [a]
        rw [Array.from_slice_val _ _ (by simp [Slice.set_opt, Array.to_slice, hlenW])]
        simp [Slice.set_opt, Array.to_slice, Unisono.Lists.set_opt_some]
      refine ⟨by omega, h1, h2, h3, h4, ?_, ?_, by omega⟩
      · intro k hk r hr
        by_cases hkp : k = place.val
        · subst hkp
          rw [hdget] at hr
          injection hr with hreq
          subst hreq
          refine ⟨{ reading with time := i2 }, ?_, rfl, ?_, ?_⟩
          · rw [haval, List.getElem?_set_self hplaceW]
          · simp only [hi2, hi1, hi]
          · intro hb1 hb2
            simp only [hi2, hi1, hi]
            have hrt : -2 ^ 63 ≤ reading.time.val ∧ reading.time.val < 2 ^ 63 := by scalar_tac
            rw [I128.wrapping_add_val _ _ (by rw [I64.cast_I128_val]; omega), I64.cast_I128_val]
        · have hklt : k < place.val := by omega
          obtain ⟨r', hr', hpos, htm, htm2⟩ := hdone k hklt r hr
          refine ⟨r', ?_, hpos, htm, htm2⟩
          rw [haval, List.getElem?_set_ne (by omega)]
          exact hr'
      · intro k hk
        rw [haval, List.getElem?_set_ne (by omega)]
        exact hrest k (by omega)
    · rename_i hge
      have heq : place.val = kept.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [← hkept, ← heq]
      exact ⟨h1, h2, h3, h4, hdone, hrest⟩
  · dsimp only
    have h0 : (0#usize).val = 0 := rfl
    refine ⟨by omega, rfl, rfl, rfl, rfl, fun k hk => by omega, fun k _ => rfl⟩

theorem off_total (d : device.Device W) (reading : device.Reading) (otherwise : Std.I128) :
    device.Device.off d reading otherwise ⦃ _ => True ⦄ := by
  unfold device.Device.off
  step with when_total as ⟨o⟩
  cases o <;> simp [lift]

/-- A report is kept: it is the newest of the kept reports, nothing is set
aside, and the counts are within what the device can keep. -/
def Kept (d : device.Device W) (r : device.Reading) : Prop :=
  d.aside = none ∧ Fits d ∧ (0 < W.val → newestReading d = some r)

/-- Taking in a step keeps the second of its two reports. -/
theorem step_spec (d : device.Device W) (earlier report : device.Reading) :
    device.Device.step d earlier report ⦃ d' => d'.rate = d.rate ∧ Kept d' report ⦄ := by
  unfold device.Device.step
  step with off_total as ⟨second⟩
  step with off_total as ⟨first⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step with shift_spec as ⟨d1, hr1, ha1, hl1, hn1, _, _⟩
  step with push_spec as ⟨d2, hr2, ha2, hf2, _, hnew2⟩
  apply WP.spec_mono (push_spec d2 report)
  rintro d' ⟨hr, ha, hf, _, hnew⟩
  exact ⟨hr.trans (hr2.trans hr1), ha.trans ha2, hf, hnew⟩

/-- What taking in a report does, for every state of the device and every
report. The rate stays. The report is either kept, or it is set aside while
everything else stays as it is, and that only when nothing was set aside
before. So of any two reports in a row the second is kept: whatever a device
holds, its line follows the reports again from the second one on. -/
theorem observe_spec (d : device.Device W) (position : Std.U64) (time : Std.I64) :
    device.Device.observe d position time ⦃ d' =>
      d'.rate = d.rate
      ∧ (Kept d' ⟨position, time⟩
        ∨ (d.aside = none ∧ d'.aside = some ⟨position, time⟩ ∧ d'.readings = d.readings
            ∧ d'.len = d.len ∧ d'.next = d.next)) ⦄ := by
  have hstart : device.Device.start d ⟨position, time⟩ ⦃ d' =>
      d'.rate = d.rate ∧ Kept d' ⟨position, time⟩ ⦄ := by
    apply WP.spec_mono (start_spec d ⟨position, time⟩)
    rintro d' ⟨hr, ha, hf, hnew⟩
    exact ⟨hr, ha, hf, fun hW => (hnew hW).2⟩
  have hpush_clear : device.Device.push { d with aside := none } ⟨position, time⟩ ⦃ d' =>
      d'.rate = d.rate ∧ Kept d' ⟨position, time⟩ ⦄ := by
    apply WP.spec_mono (push_spec { d with aside := none } ⟨position, time⟩)
    rintro d' ⟨hr, ha, hf, _, hnew⟩
    exact ⟨hr, ha, hf, hnew⟩
  unfold device.Device.observe
  step as ⟨o, ho⟩
  cases o with
  | none => exact WP.spec_mono hstart fun _ h => ⟨h.1, Or.inl h.2⟩
  | some newest =>
    simp only
    cases haside : d.aside with
    | none =>
      simp only
      step with restarted_total as ⟨b⟩
      split
      · exact WP.spec_mono hstart fun _ h => ⟨h.1, Or.inl h.2⟩
      · step with follows_total as ⟨b1⟩
        split
        · apply WP.spec_mono (push_spec d ⟨position, time⟩)
          rintro d' ⟨hr, ha, hf, _, hnew⟩
          exact ⟨hr, Or.inl ⟨ha.trans haside, hf, hnew⟩⟩
        · rw [WP.spec_ok]
          exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
    | some earlier =>
      simp only
      step with restarted_total as ⟨b⟩
      split
      · step with restarted_total as ⟨b1⟩
        split
        · exact WP.spec_mono hstart fun _ h => ⟨h.1, Or.inl h.2⟩
        · step with follows_total as ⟨b2⟩
          split
          · exact WP.spec_mono hpush_clear fun _ h => ⟨h.1, Or.inl h.2⟩
          · exact WP.spec_mono hstart fun _ h => ⟨h.1, Or.inl h.2⟩
      · step with follows_total as ⟨b1⟩
        split
        · apply WP.spec_mono (step_spec d earlier ⟨position, time⟩)
          rintro d' ⟨hr, hk⟩
          exact ⟨hr, Or.inl hk⟩
        · step with restarted_total as ⟨b2⟩
          split
          · exact WP.spec_mono hstart fun _ h => ⟨h.1, Or.inl h.2⟩
          · step with follows_total as ⟨b3⟩
            split
            · exact WP.spec_mono hpush_clear fun _ h => ⟨h.1, Or.inl h.2⟩
            · exact WP.spec_mono hstart fun _ h => ⟨h.1, Or.inl h.2⟩

/-- A report that follows one that was set aside is kept. -/
theorem observe_after_aside (d : device.Device W) (position : Std.U64) (time : Std.I64)
    (h : d.aside ≠ none) :
    device.Device.observe d position time ⦃ d' => Kept d' ⟨position, time⟩ ⦄ := by
  apply WP.spec_mono (observe_spec d position time)
  rintro d' ⟨-, hk | ⟨hnone, -⟩⟩
  · exact hk
  · exact absurd hnone h

/-- Taking in a report returns for every state of the device and every report. -/
theorem observe_total (d : device.Device W) (position : Std.U64) (time : Std.I64) :
    device.Device.observe d position time ⦃ _ => True ⦄ :=
  WP.spec_mono (observe_spec d position time) fun _ _ => trivial

/-! ## Connection to `Unisono.Model.LineFit`

When the kept reports span at least two distinct positions (`0 < spread`),
`beyondZ` is the integer floor of the unweighted least-squares line of
`Unisono.Model.LineFit` evaluated at `ahead`. -/

noncomputable section

private theorem int_ediv_eq_floor_real (a b : ℤ) (hb : 0 < b) :
    a / b = ⌊(a : ℝ) / (b : ℝ)⌋ := by
  symm
  rw [Int.floor_eq_iff]
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (a / b) * b ≤ a := (Int.le_ediv_iff_mul_le hb).mp le_rfl
  have h2 : a < (a / b + 1) * b := (Int.ediv_lt_iff_lt_mul hb).mp (by omega)
  constructor
  · rw [le_div_iff₀ hbr]; exact_mod_cast h1
  · rw [div_lt_iff₀ hbr]; exact_mod_cast h2

private theorem finset_range_sum_eq_list_sum (rs : List device.Reading) (f : device.Reading → ℤ) :
    (∑ i ∈ Finset.range rs.length, (f (rs.getD i ⟨0#u64, 0#i64⟩) : ℝ))
      = ((rs.map f).sum : ℤ) := by
  induction rs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
    rw [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, Int.cast_add]
    have hcongr :
        ∑ i ∈ Finset.range xs.length, (f ((xs ++ [x]).getD i ⟨0#u64, 0#i64⟩) : ℝ)
          = ∑ i ∈ Finset.range xs.length, (f (xs.getD i ⟨0#u64, 0#i64⟩) : ℝ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hlt : i < xs.length := Finset.mem_range.mp hi
      simp [List.getD, List.getElem?_append_left hlt]
    have hlast : (xs ++ [x]).getD xs.length ⟨0#u64, 0#i64⟩ = x := by
      simp [List.getD]
    rw [hcongr, hlast, ih]

/-- For any non-empty list of kept reports with positive spread, `beyondZ` is
the exact integer floor of the least-squares residual line from
`Unisono.Model.LineFit` evaluated at `ahead`. -/
theorem beyondZ_eq_floor_lineFit (rate : Std.U32) (newest : device.Reading)
    (rs : List device.Reading) (ahead : ℤ)
    (hn : 0 < rs.length)
    (hspread : 0 < (rs.length : ℤ) * sumXX newest rs - sumX newest rs * sumX newest rs) :
    let s := Finset.range rs.length
    let w : ℕ → ℝ := fun _ => 1
    let t : ℕ → ℝ := fun i => (relX newest (rs.getD i ⟨0#u64, 0#i64⟩) : ℝ)
    let z : ℕ → ℝ := fun i => (relY rate newest (rs.getD i ⟨0#u64, 0#i64⟩) : ℝ)
    beyondZ rate newest rs ahead
      = ⌊Unisono.Model.LineFit.value s w t z 0
          + Unisono.Model.LineFit.slope s w t z 0 * (ahead : ℝ)⌋ := by
  intro s w t z
  have hm0 : Unisono.Model.LineFit.moment s w t 0 0 = (rs.length : ℝ) := by
    simp [Unisono.Model.LineFit.moment, s, w]
  have hm1 : Unisono.Model.LineFit.moment s w t 0 1 = (sumX newest rs : ℝ) := by
    simp only [Unisono.Model.LineFit.moment, s, w, t, one_mul, sub_zero, pow_one]
    exact finset_range_sum_eq_list_sum rs (relX newest)
  have hm2 : Unisono.Model.LineFit.moment s w t 0 2 = (sumXX newest rs : ℝ) := by
    simp only [Unisono.Model.LineFit.moment, s, w, t, one_mul, sub_zero, sq]
    have h := finset_range_sum_eq_list_sum rs (fun r => relX newest r * relX newest r)
    simpa [sumXX] using h
  have hsz : Unisono.Model.LineFit.sumZ s w z = (sumY rate newest rs : ℝ) := by
    simp only [Unisono.Model.LineFit.sumZ, s, w, z, one_mul]
    exact finset_range_sum_eq_list_sum rs (relY rate newest)
  have hstz : Unisono.Model.LineFit.sumTZ s w t z 0 = (sumXY rate newest rs : ℝ) := by
    simp only [Unisono.Model.LineFit.sumTZ, s, w, t, z, one_mul, sub_zero]
    have h := finset_range_sum_eq_list_sum rs (fun r => relX newest r * relY rate newest r)
    simpa [sumXY] using h
  have hdet : Unisono.Model.LineFit.det s w t 0
      = (((rs.length : ℤ) * sumXX newest rs - sumX newest rs * sumX newest rs : ℤ) : ℝ) := by
    unfold Unisono.Model.LineFit.det
    rw [hm0, hm1, hm2]
    push_cast
    ring
  have hsp_pos_r : (0 : ℝ) < (((rs.length : ℤ) * sumXX newest rs
      - sumX newest rs * sumX newest rs : ℤ) : ℝ) := by exact_mod_cast hspread
  have hdet_ne : Unisono.Model.LineFit.det s w t 0 ≠ 0 := by rw [hdet]; linarith
  have hn_pos_r : (0 : ℝ) < (rs.length : ℝ) := by exact_mod_cast hn
  have hden_pos : (0 : ℤ) < (rs.length : ℤ)
      * ((rs.length : ℤ) * sumXX newest rs - sumX newest rs * sumX newest rs) := by
    nlinarith
  unfold beyondZ
  simp only [hspread, ↓reduceIte]
  rw [int_ediv_eq_floor_real _ _ hden_pos]
  congr 1
  unfold Unisono.Model.LineFit.value Unisono.Model.LineFit.slope
  rw [hm0, hm1, hm2, hsz, hstz, hdet]
  push_cast
  have hnr : (rs.length : ℝ) ≠ 0 := ne_of_gt hn_pos_r
  have hspr : (rs.length : ℝ) * (sumXX newest rs : ℝ)
      - (sumX newest rs : ℝ) * (sumX newest rs : ℝ) ≠ 0 := by
    have : (((rs.length : ℤ) * sumXX newest rs - sumX newest rs * sumX newest rs : ℤ) : ℝ) ≠ 0 :=
      ne_of_gt hsp_pos_r
    push_cast at this
    exact this
  field_simp [hnr, hspr]
  ring

/-- For any kept report list with positive spread, `beyondSlopeQ16Z` is the
exact integer floor of `2^16 * span` times the least-squares residual
slope from `Unisono.Model.LineFit`. -/
theorem beyondSlopeQ16Z_eq_floor_lineFit (rate : Std.U32) (newest : device.Reading)
    (rs : List device.Reading) (span : ℤ)
    (hspread : 0 < (rs.length : ℤ) * sumXX newest rs - sumX newest rs * sumX newest rs) :
    let s := Finset.range rs.length
    let w : ℕ → ℝ := fun _ => 1
    let t : ℕ → ℝ := fun i => (relX newest (rs.getD i ⟨0#u64, 0#i64⟩) : ℝ)
    let z : ℕ → ℝ := fun i => (relY rate newest (rs.getD i ⟨0#u64, 0#i64⟩) : ℝ)
    beyondSlopeQ16Z rate newest rs span
      = ⌊((span * 2 ^ 16 : ℤ) : ℝ) * Unisono.Model.LineFit.slope s w t z 0⌋ := by
  intro s w t z
  have hm0 : Unisono.Model.LineFit.moment s w t 0 0 = (rs.length : ℝ) := by
    simp [Unisono.Model.LineFit.moment, s, w]
  have hm1 : Unisono.Model.LineFit.moment s w t 0 1 = (sumX newest rs : ℝ) := by
    simp only [Unisono.Model.LineFit.moment, s, w, t, one_mul, sub_zero, pow_one]
    exact finset_range_sum_eq_list_sum rs (relX newest)
  have hm2 : Unisono.Model.LineFit.moment s w t 0 2 = (sumXX newest rs : ℝ) := by
    simp only [Unisono.Model.LineFit.moment, s, w, t, one_mul, sub_zero, sq]
    have h := finset_range_sum_eq_list_sum rs (fun r => relX newest r * relX newest r)
    simpa [sumXX] using h
  have hsz : Unisono.Model.LineFit.sumZ s w z = (sumY rate newest rs : ℝ) := by
    simp only [Unisono.Model.LineFit.sumZ, s, w, z, one_mul]
    exact finset_range_sum_eq_list_sum rs (relY rate newest)
  have hstz : Unisono.Model.LineFit.sumTZ s w t z 0 = (sumXY rate newest rs : ℝ) := by
    simp only [Unisono.Model.LineFit.sumTZ, s, w, t, z, one_mul, sub_zero]
    have h := finset_range_sum_eq_list_sum rs (fun r => relX newest r * relY rate newest r)
    simpa [sumXY] using h
  have hdet : Unisono.Model.LineFit.det s w t 0
      = (((rs.length : ℤ) * sumXX newest rs - sumX newest rs * sumX newest rs : ℤ) : ℝ) := by
    unfold Unisono.Model.LineFit.det
    rw [hm0, hm1, hm2]
    push_cast
    ring
  have hsp_pos_r : (0 : ℝ) < (((rs.length : ℤ) * sumXX newest rs
      - sumX newest rs * sumX newest rs : ℤ) : ℝ) := by exact_mod_cast hspread
  unfold beyondSlopeQ16Z
  simp only [hspread, ↓reduceIte]
  rw [int_ediv_eq_floor_real _ _ hspread]
  congr 1
  unfold Unisono.Model.LineFit.slope
  rw [hm0, hm1, hsz, hstz, hdet]
  push_cast
  have hspr : (rs.length : ℝ) * (sumXX newest rs : ℝ)
      - (sumX newest rs : ℝ) * (sumX newest rs : ℝ) ≠ 0 := by
    have : (((rs.length : ℤ) * sumXX newest rs - sumX newest rs * sumX newest rs : ℤ) : ℝ) ≠ 0 :=
      ne_of_gt hsp_pos_r
    push_cast at this
    exact this
  field_simp [hspr]

end

end Unisono.Device
