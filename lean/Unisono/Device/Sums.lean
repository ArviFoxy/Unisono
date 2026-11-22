/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import UnisonoCore
public import Unisono.Fixed
public import Unisono.Lists
public import Unisono.Scalar

/-!
# Device clock model: window storage and regression sums

Clamping bounds, ring-buffer storage (`push`, `start`), and non-wrapping
128-bit accumulation of least-squares sums (`add`, `sums`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Device

variable {W : Std.Usize}

/-- Runs a function to its end: step by step, taking conditionals apart. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

/-- The clamping bound on relative frame distances and nominal-rate residuals: `2^28`. -/
def reachZ : ℤ := 2 ^ 28

/-- Clamps an integer to `[-reachZ, reachZ]`. -/
def clampReach (x : ℤ) : ℤ := max (-reachZ) (min x reachZ)

theorem clampReach_bounds (x : ℤ) : -reachZ ≤ clampReach x ∧ clampReach x ≤ reachZ := by
  unfold clampReach reachZ
  omega

/-- Nominal nanoseconds for `frames` at `rate` frames per second, or zero when `rate = 0`. -/
def nominalZ (rate : Std.U32) (frames : ℤ) : ℤ :=
  if rate.val = 0 then 0 else (frames * 10 ^ 9) / rate.val

theorem nominalZ_bounds (rate : Std.U32) (frames : ℤ)
    (hf : -reachZ ≤ frames ∧ frames ≤ reachZ) :
    -reachZ * 10 ^ 9 ≤ nominalZ rate frames ∧ nominalZ rate frames ≤ reachZ * 10 ^ 9 := by
  unfold nominalZ reachZ at *
  split
  · omega
  · rename_i hr
    have hpos : (1 : ℤ) ≤ rate.val := by omega
    have hmul : -(2 ^ 28 : ℤ) * 10 ^ 9 ≤ frames * 10 ^ 9
        ∧ frames * 10 ^ 9 ≤ 2 ^ 28 * 10 ^ 9 := by omega
    constructor
    · have h1 : (-(2 ^ 28 : ℤ) * 10 ^ 9) * rate.val ≤ frames * 10 ^ 9 := by nlinarith
      exact (Int.le_ediv_iff_mul_le (by omega)).mpr h1
    · have h2 : frames * 10 ^ 9 < (2 ^ 28 * 10 ^ 9 + 1) * rate.val := by nlinarith
      have h3 : frames * 10 ^ 9 / (rate.val : ℤ) < 2 ^ 28 * 10 ^ 9 + 1 :=
        (Int.ediv_lt_iff_lt_mul (by omega)).mpr h2
      omega

/-- The kept reports of a device, in array order, capped at `min W 4096`. -/
def keptList (d : device.Device W) : List device.Reading :=
  d.readings.val.take (min d.len.val (min W.val 4096))

theorem keptList_length (d : device.Device W) :
    (keptList d).length = min d.len.val (min W.val 4096) := by
  unfold keptList
  have hlen : d.readings.val.length = W.val := d.readings.property
  rw [List.length_take, hlen]
  omega

/-- The newest reading of a device, matching `Device::newest`. -/
def newestReading (d : device.Device W) : Option device.Reading :=
  let cap := min W.val 4096
  if d.len.val = 0 ∨ cap = 0 then none
  else
    let place := if d.next.val = 0 ∨ cap < d.next.val then cap - 1 else d.next.val - 1
    d.readings.val[place]?

/-- Relative position of report `r` from `newest`, clamped to `[-reachZ, reachZ]`. -/
def relX (newest r : device.Reading) : ℤ :=
  clampReach ((r.position.val : ℤ) - (newest.position.val : ℤ))

/-- Residual time of report `r` from `newest` beyond the nominal rate, clamped to `[-reachZ, reachZ]`. -/
def relY (rate : Std.U32) (newest r : device.Reading) : ℤ :=
  clampReach (((r.time.val : ℤ) - (newest.time.val : ℤ)) - nominalZ rate (relX newest r))

/-- Exact integer sums over a list of reports relative to `newest`. -/
def sumX (newest : device.Reading) (rs : List device.Reading) : ℤ :=
  (rs.map (relX newest)).sum

def sumY (rate : Std.U32) (newest : device.Reading) (rs : List device.Reading) : ℤ :=
  (rs.map (relY rate newest)).sum

def sumXX (newest : device.Reading) (rs : List device.Reading) : ℤ :=
  (rs.map fun r => relX newest r * relX newest r).sum

def sumXY (rate : Std.U32) (newest : device.Reading) (rs : List device.Reading) : ℤ :=
  (rs.map fun r => relX newest r * relY rate newest r).sum

theorem prod_bounds {a b M N : ℤ}
    (ha : -M ≤ a ∧ a ≤ M) (hb : -N ≤ b ∧ b ≤ N) :
    -(M * N) ≤ a * b ∧ a * b ≤ M * N := by
  constructor <;> nlinarith

theorem ediv_abs_bound {a b B : ℤ} (hb : 1 ≤ b) (hB : 0 ≤ B)
    (ha : -B ≤ a ∧ a ≤ B) :
    -B ≤ a / b ∧ a / b ≤ B := by
  constructor
  · have h1 : (-B) * b ≤ a := by nlinarith
    exact (Int.le_ediv_iff_mul_le (by omega)).mpr h1
  · have h2 : a < (B + 1) * b := by nlinarith
    have h3 : a / b < B + 1 := (Int.ediv_lt_iff_lt_mul (by omega)).mpr h2
    omega

theorem sums_bounds (rate : Std.U32) (newest : device.Reading) (rs : List device.Reading) :
    -(rs.length : ℤ) * reachZ ≤ sumX newest rs
    ∧ sumX newest rs ≤ (rs.length : ℤ) * reachZ
    ∧ -(rs.length : ℤ) * reachZ ≤ sumY rate newest rs
    ∧ sumY rate newest rs ≤ (rs.length : ℤ) * reachZ
    ∧ 0 ≤ sumXX newest rs
    ∧ sumXX newest rs ≤ (rs.length : ℤ) * reachZ ^ 2
    ∧ -(rs.length : ℤ) * reachZ ^ 2 ≤ sumXY rate newest rs
    ∧ sumXY rate newest rs ≤ (rs.length : ℤ) * reachZ ^ 2 := by
  induction rs with
  | nil => simp [sumX, sumY, sumXX, sumXY]
  | cons r tl ih =>
    obtain ⟨hx1, hx2, hy1, hy2, hxx1, hxx2, hxy1, hxy2⟩ := ih
    have hrx : -reachZ ≤ relX newest r ∧ relX newest r ≤ reachZ :=
      clampReach_bounds _
    have hry : -reachZ ≤ relY rate newest r ∧ relY rate newest r ≤ reachZ :=
      clampReach_bounds _
    have hrxx1 : 0 ≤ relX newest r * relX newest r := mul_self_nonneg _
    have hrxx2 : relX newest r * relX newest r ≤ reachZ ^ 2 := by
      have := (prod_bounds hrx hrx).2
      linarith [sq reachZ]
    have hrxy : -reachZ ^ 2 ≤ relX newest r * relY rate newest r
        ∧ relX newest r * relY rate newest r ≤ reachZ ^ 2 := by
      have := prod_bounds hrx hry
      constructor <;> linarith [sq reachZ]
    simp only [sumX, sumY, sumXX, sumXY, List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one] at *
    refine ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩

theorem sums_bounds_cap (rate : Std.U32) (newest : device.Reading) (rs : List device.Reading)
    (hlen : rs.length ≤ 4096) :
    -(4096 * reachZ) ≤ sumX newest rs
    ∧ sumX newest rs ≤ 4096 * reachZ
    ∧ -(4096 * reachZ) ≤ sumY rate newest rs
    ∧ sumY rate newest rs ≤ 4096 * reachZ
    ∧ -(4096 * reachZ ^ 2) ≤ sumXX newest rs
    ∧ sumXX newest rs ≤ 4096 * reachZ ^ 2
    ∧ -(4096 * reachZ ^ 2) ≤ sumXY rate newest rs
    ∧ sumXY rate newest rs ≤ 4096 * reachZ ^ 2 := by
  obtain ⟨hx1, hx2, hy1, hy2, hxx1, hxx2, hxy1, hxy2⟩ := sums_bounds rate newest rs
  have hlenZ : (rs.length : ℤ) ≤ 4096 := by omega
  have hR0 : 0 ≤ reachZ := by unfold reachZ; norm_num
  have hR2 : 0 ≤ reachZ ^ 2 := sq_nonneg reachZ
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

@[step]
theorem within_spec (value : Std.I128) :
    device.within value ⦃ r =>
      r.val = clampReach value.val ∧ -reachZ ≤ r.val ∧ r.val ≤ reachZ ⦄ := by
  unfold device.within
  have hr : device.REACH.val = reachZ := by simp [device.REACH, reachZ]
  have h0 : (0#i128).val = 0 := by rfl
  have hneg : (core.num.I128.wrapping_sub 0#i128 device.REACH).val = -reachZ := by
    rw [I128.wrapping_sub_val _ _ (by rw [h0, hr]; unfold reachZ; norm_num), h0, hr]
    omega
  split
  · simp only [WP.spec_ok, hr]
    have hgt : reachZ < value.val := by rw [← hr]; scalar_tac
    unfold clampReach reachZ at *
    omega
  · step as ⟨i, hi⟩
    have hiv : i.val = -reachZ := by rw [hi, hneg]
    have hle : value.val ≤ reachZ := by rw [← hr]; scalar_tac
    split
    · simp only [WP.spec_ok, hneg]
      have hlt : value.val < -reachZ := by rw [← hiv]; scalar_tac
      unfold clampReach reachZ at *
      omega
    · simp only [WP.spec_ok]
      have hge : -reachZ ≤ value.val := by rw [← hiv]; scalar_tac
      unfold clampReach reachZ at *
      omega

@[step]
theorem capacity_spec (W : Std.Usize) :
    device.Device.capacity W ⦃ r => r.val = min W.val 4096 ∧ r.val ≤ W.val ∧ r.val ≤ 4096 ⦄ := by
  unfold device.Device.capacity
  have hm : device.MAX_KEPT.val = 4096 := by simp [device.MAX_KEPT]
  split
  · simp only [WP.spec_ok, hm]
    have : 4096 < W.val := by rw [← hm]; scalar_tac
    omega
  · simp only [WP.spec_ok]
    have : W.val ≤ 4096 := by rw [← hm]; scalar_tac
    omega

@[step]
theorem kept_spec (d : device.Device W) :
    device.Device.kept d ⦃ r =>
      r.val = min d.len.val (min W.val 4096) ∧ r.val ≤ W.val ∧ r.val ≤ 4096 ⦄ := by
  unfold device.Device.kept
  step as ⟨cap, hcap, hcapW, hcapM⟩
  split
  · simp only [WP.spec_ok]
    have : cap.val < d.len.val := by scalar_tac
    omega
  · simp only [WP.spec_ok]
    have : d.len.val ≤ cap.val := by scalar_tac
    omega

@[step]
theorem at_spec (d : device.Device W) (place : Std.Usize) :
    device.Device.at d place ⦃ o => o = d.readings.val[place.val]? ⦄ := by
  unfold device.Device.at
  simp only [lift, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  cases h : d.readings.val[place.val]? <;> simp [h]

@[step]
theorem newest_spec (d : device.Device W) :
    device.Device.newest d ⦃ o =>
      o = newestReading d ∧ (o = none ↔ d.len.val = 0 ∨ W.val = 0) ⦄ := by
  unfold device.Device.newest newestReading
  step as ⟨cap, hcap, hcapW, hcapM⟩
  have hlen : d.readings.val.length = W.val := d.readings.property
  split
  · rename_i h0
    have hl0 : d.len.val = 0 := by scalar_tac
    simp [hl0]
  · rename_i hne0
    have hpos : 0 < d.len.val := by scalar_tac
    split
    · rename_i hc0
      have hc0v : cap.val = 0 := by scalar_tac
      have hW0 : W.val = 0 := by omega
      simp [hW0]
    · rename_i hcne0
      have hcpos : 0 < cap.val := by scalar_tac
      have hWpos : 0 < W.val := by omega
      split
      · rename_i hn0
        have hn0v : d.next.val = 0 := by scalar_tac
        simp only [bind_ok]
        step as ⟨o, ho⟩
        have hsub : (core.num.Usize.saturating_sub cap 1#usize).val = min W.val 4096 - 1 := by
          rw [Usize.saturating_sub_val]; simp; omega
        have hlt : min W.val 4096 - 1 < d.readings.val.length := by omega
        simp only [hn0v, true_or, ↓reduceIte]
        rw [ho, hsub, List.getElem?_eq_getElem hlt]
        simp; omega
      · rename_i hnne0
        have hnpos : 0 < d.next.val := by scalar_tac
        split
        · rename_i hngt
          have hngtv : min W.val 4096 < d.next.val := by rw [← hcap]; scalar_tac
          simp only [bind_ok]
          step as ⟨o, ho⟩
          have hsub : (core.num.Usize.saturating_sub cap 1#usize).val = min W.val 4096 - 1 := by
            rw [Usize.saturating_sub_val]; simp; omega
          have hlt : min W.val 4096 - 1 < d.readings.val.length := by omega
          simp only [hngtv, or_true, ↓reduceIte]
          rw [ho, hsub, List.getElem?_eq_getElem hlt]
          simp; omega
        · rename_i hnle
          have hnlev : d.next.val ≤ min W.val 4096 := by rw [← hcap]; scalar_tac
          have hcond : ¬ (d.next.val = 0 ∨ min W.val 4096 < d.next.val) := by omega
          simp only [bind_ok]
          step as ⟨o, ho⟩
          have hsub : (core.num.Usize.saturating_sub d.next 1#usize).val = d.next.val - 1 := by
            rw [Usize.saturating_sub_val]; simp
          have hlt : d.next.val - 1 < d.readings.val.length := by omega
          simp only [hcond, ↓reduceIte]
          rw [ho, hsub, List.getElem?_eq_getElem hlt]
          simp; omega

theorem nominal_spec (d : device.Device W) (frames : Std.I128)
    (hf : -reachZ ≤ frames.val ∧ frames.val ≤ reachZ) :
    device.Device.nominal d frames ⦃ r =>
      r.val = nominalZ d.rate frames.val
      ∧ -reachZ * 10 ^ 9 ≤ r.val ∧ r.val ≤ reachZ * 10 ^ 9 ⦄ := by
  unfold device.Device.nominal
  have hb : device.BILLION.val = 10 ^ 9 := by simp [device.BILLION]
  step as ⟨i, hi⟩
  have hiv : i.val = frames.val * 10 ^ 9 := by
    rw [hi, I128.wrapping_mul_val _ _ (by rw [hb]; unfold reachZ at hf; omega), hb]
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = d.rate.val := by rw [hi1, U32.hcast_I64_val]
  step with Fixed.div_floor_spec as ⟨r, hrpos, hrnonpos⟩
  have hnb := nominalZ_bounds d.rate frames.val hf
  have hval : r.val = nominalZ d.rate frames.val := by
    unfold nominalZ
    split
    · rename_i hz
      exact hrnonpos (by rw [hi1v, hz]; norm_num)
    · rename_i hnz
      rw [hrpos (by rw [hi1v]; omega), hiv, hi1v]
  rw [hval]
  exact ⟨rfl, hnb.1, hnb.2⟩

@[step]
theorem nominal_total (d : device.Device W) (frames : Std.I128) :
    device.Device.nominal d frames ⦃ _ => True ⦄ := by
  unfold device.Device.nominal
  run

theorem restarted_total (last : device.Reading) (position : Std.U64) :
    device.Device.restarted W last position ⦃ _ => True ⦄ := by
  unfold device.Device.restarted
  run

/-- The counts of a device are within what it can keep. -/
def Fits (d : device.Device W) : Prop :=
  d.len.val ≤ min W.val 4096 ∧ (0 < W.val → d.next.val < min W.val 4096)

/-- Writing a report: it is then the newest of the kept ones, the counts are
within what the device can keep, the kept count grows by one up to capacity,
and the rate and what is set aside stay. -/
theorem push_spec (d1 : device.Device W) (reading : device.Reading) :
    device.Device.push d1 reading ⦃ d' =>
      d'.rate = d1.rate ∧ d'.aside = d1.aside ∧ Fits d'
      ∧ d'.len.val = min (min d1.len.val (min W.val 4096) + 1) (min W.val 4096)
      ∧ (0 < W.val → newestReading d' = some reading) ⦄ := by
  unfold device.Device.push
  step as ⟨cap, hcap, hcapW, hcapM⟩
  have hi_spec : (if d1.len > cap then ok cap else ok d1.len)
      ⦃ i => i.val = min d1.len.val cap.val ⦄ := by
    split <;> simp only [WP.spec_ok] <;> scalar_tac
  apply WP.spec_bind hi_spec
  intro i hi
  split
  · rename_i hc0
    have hc0v : cap.val = 0 := by scalar_tac
    rw [WP.spec_ok]
    dsimp only
    exact ⟨rfl, rfl, (by unfold Fits; dsimp only; exact ⟨by omega, fun hW => by omega⟩),
      by omega, fun hW => by omega⟩
  · rename_i hcne0
    have hcpos : 0 < cap.val := by scalar_tac
    have hi1_spec : (if d1.next >= cap then ok 0#usize else ok d1.next)
        ⦃ i1 => i1.val < cap.val ⦄ := by
      split <;> simp only [WP.spec_ok] <;> scalar_tac
    apply WP.spec_bind hi1_spec
    intro i1 hi1
    simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
      core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
    have hlenW : d1.readings.val.length = W.val := d1.readings.property
    have ha_spec : ∀ a : Array device.Reading W, a.val[i1.val]? = some reading →
        (do
          let next1 ←
            if core.num.Usize.saturating_add i1 1#usize >= cap then ok 0#usize
            else ok (core.num.Usize.saturating_add i1 1#usize)
          if i < cap then
            ok { d1 with readings := a, len := core.num.Usize.saturating_add i 1#usize, next := next1 }
          else ok { d1 with readings := a, len := i, next := next1 })
        ⦃ d' =>
          d'.rate = d1.rate ∧ d'.aside = d1.aside ∧ Fits d'
          ∧ d'.len.val = min (min d1.len.val (min W.val 4096) + 1) (min W.val 4096)
          ∧ (0 < W.val → newestReading d' = some reading) ⦄ := by
      intro a ha
      have hsucc : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 := by
        rw [Usize.saturating_add_val _ _ (by scalar_tac)]; rfl
      have hn1_spec :
          (if core.num.Usize.saturating_add i1 1#usize >= cap then ok 0#usize
           else ok (core.num.Usize.saturating_add i1 1#usize))
          ⦃ next1 => next1.val < cap.val
            ∧ (if next1.val = 0 ∨ cap.val < next1.val then cap.val - 1 else next1.val - 1)
                = i1.val ⦄ := by
        split
        · rename_i hge
          have : cap.val ≤ i1.val + 1 := by rw [← hsucc]; scalar_tac
          simp only [WP.spec_ok]
          have h0 : (0#usize).val = 0 := by rfl
          rw [h0]
          simp only [true_or, ↓reduceIte]
          omega
        · rename_i hlt
          have : i1.val + 1 < cap.val := by rw [← hsucc]; scalar_tac
          simp only [WP.spec_ok, hsucc]
          refine ⟨this, ?_⟩
          have hne : ¬ (i1.val + 1 = 0 ∨ cap.val < i1.val + 1) := by omega
          simp only [hne, ↓reduceIte]
          omega
      apply WP.spec_bind hn1_spec
      rintro next1 ⟨hnext1, hplace⟩
      split
      · rename_i hilt
        have hil : i.val < cap.val := by scalar_tac
        have hi2v : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 := by
          rw [Usize.saturating_add_val _ _ (by scalar_tac)]; rfl
        rw [WP.spec_ok]
        dsimp only
        refine ⟨rfl, rfl, (by unfold Fits; dsimp only; exact ⟨by omega, fun _ => by omega⟩),
          by omega, fun hW => ?_⟩
        unfold newestReading
        dsimp only
        have hne : ¬ ((core.num.Usize.saturating_add i 1#usize).val = 0 ∨ min W.val 4096 = 0) := by
          omega
        simp only [hne, ↓reduceIte]
        rw [← hcap, hplace]
        exact ha
      · rename_i hige
        have hie : i.val = cap.val := by scalar_tac
        rw [WP.spec_ok]
        dsimp only
        refine ⟨rfl, rfl, (by unfold Fits; dsimp only; exact ⟨by omega, fun _ => by omega⟩),
          by omega, fun hW => ?_⟩
        unfold newestReading
        dsimp only
        have hne : ¬ (i.val = 0 ∨ min W.val 4096 = 0) := by omega
        simp only [hne, ↓reduceIte]
        rw [← hcap, hplace]
        exact ha
    have hi1W : i1.val < d1.readings.val.length := by omega
    have ha_match :
        (match d1.readings.to_slice[i1]? with
          | none => ok (d1.readings.from_slice (d1.readings.to_slice.set_opt i1 none))
          | some _ =>
            ok (d1.readings.from_slice
              (d1.readings.to_slice.set_opt i1 (some reading))))
        ⦃ a => a.val[i1.val]? = some reading ⦄ := by
      cases h : d1.readings.to_slice[i1]? with
      | none =>
        simp at h
        omega
      | some x =>
        simp
        rw [Unisono.Lists.set_opt_some, List.getElem?_set_self hi1W]
    apply WP.spec_bind ha_match
    intro a ha
    exact ha_spec a ha

/-- Starting anew at a report: it alone is kept (so `len = 1` when `0 < W`),
and nothing is set aside. -/
theorem start_spec (d : device.Device W) (reading : device.Reading) :
    device.Device.start d reading ⦃ d' =>
      d'.rate = d.rate ∧ d'.aside = none ∧ Fits d'
      ∧ (0 < W.val → d'.len.val = 1 ∧ newestReading d' = some reading) ⦄ := by
  unfold device.Device.start
  apply WP.spec_mono (push_spec _ reading)
  rintro d' ⟨h1, h2, h3, hlen, h4⟩
  have h0 : (0#usize).val = 0 := rfl
  exact ⟨h1, h2, h3, fun hW => ⟨by dsimp only at hlen; rw [h0] at hlen; omega, h4 hW⟩⟩

theorem follows_total (d : device.Device W) (earlier later : device.Reading) :
    device.Device.follows d earlier later ⦃ _ => True ⦄ := by
  unfold device.Device.follows
  run

theorem add_spec (d : device.Device W) (sums : device.Sums)
    (newest reading : device.Reading) (rs : List device.Reading)
    (hlen : rs.length < 4096)
    (hc : sums.count.val = rs.length)
    (hx : sums.x.val = sumX newest rs)
    (hy : sums.y.val = sumY d.rate newest rs)
    (hxx : sums.xx.val = sumXX newest rs)
    (hxy : sums.xy.val = sumXY d.rate newest rs) :
    device.Device.add d sums newest reading ⦃ s =>
      s.count.val = (rs ++ [reading]).length
      ∧ s.x.val = sumX newest (rs ++ [reading])
      ∧ s.y.val = sumY d.rate newest (rs ++ [reading])
      ∧ s.xx.val = sumXX newest (rs ++ [reading])
      ∧ s.xy.val = sumXY d.rate newest (rs ++ [reading]) ⦄ := by
  unfold device.Device.add
  obtain ⟨hx1, hx2, hy1, hy2, hxx1, hxx2, hxy1, hxy2⟩ := sums_bounds d.rate newest rs
  have hR : reachZ = 2 ^ 28 := rfl
  have hlenZ : (rs.length : ℤ) ≤ 4096 := by omega
  have hlen0 : (0 : ℤ) ≤ rs.length := by omega
  have hsx_b : -(4096 * reachZ) ≤ sums.x.val ∧ sums.x.val ≤ 4096 * reachZ := by
    rw [hx]; constructor <;> nlinarith
  have hsy_b : -(4096 * reachZ) ≤ sums.y.val ∧ sums.y.val ≤ 4096 * reachZ := by
    rw [hy]; constructor <;> nlinarith
  have hsxx_b : 0 ≤ sums.xx.val ∧ sums.xx.val ≤ 4096 * reachZ ^ 2 := by
    rw [hxx]; constructor <;> nlinarith [sq_nonneg reachZ]
  have hsxy_b : -(4096 * reachZ ^ 2) ≤ sums.xy.val ∧ sums.xy.val ≤ 4096 * reachZ ^ 2 := by
    rw [hxy]; constructor <;> nlinarith [sq_nonneg reachZ]
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  have hiv : i.val = reading.position.val := by rw [hi, U64.hcast_I128_val]
  have hi1v : i1.val = newest.position.val := by rw [hi1, U64.hcast_I128_val]
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = (reading.position.val : ℤ) - (newest.position.val : ℤ) := by
    rw [hi2, I128.wrapping_sub_val _ _ (by rw [hiv, hi1v]; scalar_tac), hiv, hi1v]
  step as ⟨x, hxv, hxlo, hxhi⟩
  have hxeq : x.val = relX newest reading := by rw [hxv, hi2v]; rfl
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  have hi3v : i3.val = reading.time.val := by rw [hi3, I64.cast_I128_val]
  have hi4v : i4.val = newest.time.val := by rw [hi4, I64.cast_I128_val]
  step as ⟨elapsed, helapsed⟩
  have helv : elapsed.val = reading.time.val - newest.time.val := by
    rw [helapsed, I128.wrapping_sub_val _ _ (by rw [hi3v, hi4v]; scalar_tac), hi3v, hi4v]
  step with nominal_spec d x ⟨hxlo, hxhi⟩ as ⟨i5, hi5v, hi5lo, hi5hi⟩
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = elapsed.val - i5.val := by
    rw [hi6, I128.wrapping_sub_val _ _ (by rw [helv, hR] at *; scalar_tac)]
  step as ⟨y, hyv, hylo, hyhi⟩
  have hyeq : y.val = relY d.rate newest reading := by
    rw [hyv, hi6v, helv, hi5v, hxeq]; rfl
  have h1 : (1#i128).val = 1 := by rfl
  step as ⟨i7, hi7⟩
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  step as ⟨i10, hi10⟩
  step as ⟨i11, hi11⟩
  step as ⟨i12, hi12⟩
  step as ⟨i13, hi13⟩
  have hxx_prod := prod_bounds ⟨hxlo, hxhi⟩ ⟨hxlo, hxhi⟩
  have hxy_prod := prod_bounds ⟨hxlo, hxhi⟩ ⟨hylo, hyhi⟩
  rw [hR] at hsx_b hsy_b hsxx_b hsxy_b hxlo hxhi hylo hyhi hxx_prod hxy_prod
  have hi7v : i7.val = sums.count.val + 1 := by
    rw [hi7, I128.wrapping_add_val _ _ (by rw [hc, h1]; omega), h1]
  have hi8v : i8.val = sums.x.val + x.val := by
    rw [hi8, I128.wrapping_add_val _ _ (by omega)]
  have hi9v : i9.val = sums.y.val + y.val := by
    rw [hi9, I128.wrapping_add_val _ _ (by omega)]
  have hi10v : i10.val = x.val * x.val := by
    rw [hi10, I128.wrapping_mul_val _ _ (by omega)]
  have hi11v : i11.val = sums.xx.val + x.val * x.val := by
    rw [hi11, I128.wrapping_add_val _ _ (by rw [hi10v]; omega), hi10v]
  have hi12v : i12.val = x.val * y.val := by
    rw [hi12, I128.wrapping_mul_val _ _ (by omega)]
  have hi13v : i13.val = sums.xy.val + x.val * y.val := by
    rw [hi13, I128.wrapping_add_val _ _ (by rw [hi12v]; omega), hi12v]
  simp only [List.length_append, List.length_singleton,
    sumX, sumY, sumXX, sumXY, List.map_append, List.map_singleton,
    List.sum_append, List.sum_singleton]
  refine ⟨by rw [hi7v, hc]; omega, by rw [hi8v, hx, hxeq]; rfl,
    by rw [hi9v, hy, hyeq]; rfl, by rw [hi11v, hxx, hxeq]; rfl,
    by rw [hi13v, hxy, hxeq, hyeq]; rfl⟩

@[step]
theorem add_total (d : device.Device W) (sums : device.Sums) (newest reading : device.Reading) :
    device.Device.add d sums newest reading ⦃ _ => True ⦄ := by
  unfold device.Device.add
  run

private theorem take_add_one {α : Type} (l : List α) (n : ℕ) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]] := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ k =>
      simp only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ]
      congr 1
      exact ih k (by simp at h; omega)

/-- `sums` computes the exact integer sums over `keptList d` with zero wrapping
for every `W` and every state `d`. -/
@[step]
theorem sums_spec (d : device.Device W) (newest : device.Reading) :
    device.Device.sums d newest ⦃ s =>
      s.count.val = (keptList d).length
      ∧ s.x.val = sumX newest (keptList d)
      ∧ s.y.val = sumY d.rate newest (keptList d)
      ∧ s.xx.val = sumXX newest (keptList d)
      ∧ s.xy.val = sumXY d.rate newest (keptList d)
      ∧ (keptList d).length ≤ 4096 ⦄ := by
  unfold device.Device.sums
  step as ⟨kept, hkept, hkeptW, hkeptM⟩
  unfold device.Device.sums_loop
  have hlen : d.readings.val.length = W.val := d.readings.property
  apply loop.spec_decr_nat
    (measure := fun p : device.Sums × Std.Usize => kept.val - p.2.val)
    (inv := fun p : device.Sums × Std.Usize =>
      p.2.val ≤ kept.val
      ∧ p.1.count.val = (d.readings.val.take p.2.val).length
      ∧ p.1.x.val = sumX newest (d.readings.val.take p.2.val)
      ∧ p.1.y.val = sumY d.rate newest (d.readings.val.take p.2.val)
      ∧ p.1.xx.val = sumXX newest (d.readings.val.take p.2.val)
      ∧ p.1.xy.val = sumXY d.rate newest (d.readings.val.take p.2.val))
  · rintro ⟨s, place⟩ ⟨hple, hc, hx, hy, hxx, hxy⟩
    dsimp only at hple hc hx hy hxx hxy
    unfold device.Device.sums_loop.body
    simp only
    split
    · have hlt : place.val < kept.val := by scalar_tac
      have hltLen : place.val < d.readings.val.length := by omega
      have htake_len : (d.readings.val.take place.val).length = place.val := by
        rw [List.length_take]; omega
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o, ho⟩
      have hget : o = some (d.readings.val[place.val]'hltLen) := by
        rw [ho, List.getElem?_eq_getElem hltLen]
      rw [hget]
      simp only
      step with add_spec d s newest (d.readings.val[place.val]'hltLen)
        (d.readings.val.take place.val) (by omega) hc hx hy hxx hxy
        as ⟨s1, hc1, hx1, hy1, hxx1, hxy1⟩
      step as ⟨place1, hplace1⟩
      have hp1 : place1.val = place.val + 1 := by rw [hplace1]; exact hnext
      have htake_succ := take_add_one d.readings.val place.val hltLen
      rw [hp1, htake_succ]
      exact ⟨by omega, hc1, hx1, hy1, hxx1, hxy1, by omega⟩
    · have heq : place.val = kept.val := by scalar_tac
      have hkl : keptList d = d.readings.val.take place.val := by
        unfold keptList; rw [heq, hkept]
      rw [WP.spec_ok, hkl]
      have : (d.readings.val.take place.val).length ≤ 4096 := by
        rw [List.length_take]; omega
      exact ⟨hc, hx, hy, hxx, hxy, this⟩
  · have h0 : (0#usize).val = 0 := by rfl
    have hc0 : (0#i128).val = 0 := by rfl
    simp [h0, hc0, sumX, sumY, sumXX, sumXY]


end Unisono.Device
