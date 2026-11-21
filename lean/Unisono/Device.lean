/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import UnisonoCore
public import Unisono.Fixed
public import Unisono.Lists
public import Unisono.Model.LineFit
public import Unisono.Scalar

/-!
# The line of a device

Every function of `unisono_core::device` returns for every state and every
report, and `Device::when` never wraps its 128-bit arithmetic for any window
size `W`. When the kept reports span at least two distinct positions, the value
`Device::when` adds to the nominal prediction is the integer floor of the
unique unweighted least-squares line from `Unisono.Model.LineFit`.
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

private theorem prod_bounds {a b M N : ℤ}
    (ha : -M ≤ a ∧ a ≤ M) (hb : -N ≤ b ∧ b ≤ N) :
    -(M * N) ≤ a * b ∧ a * b ≤ M * N := by
  constructor <;> nlinarith

private theorem ediv_abs_bound {a b B : ℤ} (hb : 1 ≤ b) (hB : 0 ≤ B)
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

/-- Exact integer residual computed by `Device::when` for a list of kept
reports `rs` relative to `newest` at clamped offset `ahead`. -/
def beyondZ (rate : Std.U32) (newest : device.Reading) (rs : List device.Reading)
    (ahead : ℤ) : ℤ :=
  let n : ℤ := rs.length
  let sx := sumX newest rs
  let sy := sumY rate newest rs
  let sxx := sumXX newest rs
  let sxy := sumXY rate newest rs
  let spread := n * sxx - sx * sx
  if 0 < spread then
    let tilt := n * sxy - sx * sy
    let lever := n * ahead - sx
    (sy * spread + tilt * lever) / (n * spread)
  else
    sy / n

/-- Nominal cycle duration in units of `2^-16` nanosecond for `span` frames,
or zero when `rate = 0`. -/
def nominalQ16Z (rate : Std.U32) (span : ℤ) : ℤ :=
  if rate.val = 0 then 0 else (span * 2 ^ 16 * 10 ^ 9) / rate.val

/-- Residual cycle duration in units of `2^-16` nanosecond from the fitted
slope over `rs`, or zero when all reports share one position. -/
def beyondSlopeQ16Z (rate : Std.U32) (newest : device.Reading) (rs : List device.Reading)
    (span : ℤ) : ℤ :=
  let n : ℤ := rs.length
  let sx := sumX newest rs
  let sy := sumY rate newest rs
  let sxx := sumXX newest rs
  let sxy := sumXY rate newest rs
  let spread := n * sxx - sx * sx
  if 0 < spread then
    let tilt := n * sxy - sx * sy
    (span * 2 ^ 16 * tilt) / spread
  else
    0

/-- Exact integer specification of `Device::eval_at` from precomputed sums,
spread, and tilt. -/
theorem eval_at_spec (d : device.Device W) (newest : device.Reading)
    (s : device.Sums) (spread tilt : Std.I128) (position : Std.U64)
    (hc : s.count.val = ((keptList d).length : ℤ))
    (hcnt_pos : (0 : ℤ) < s.count.val)
    (hle : (keptList d).length ≤ 4096)
    (hx : s.x.val = sumX newest (keptList d))
    (hy : s.y.val = sumY d.rate newest (keptList d))
    (hxx : s.xx.val = sumXX newest (keptList d))
    (hxy : s.xy.val = sumXY d.rate newest (keptList d))
    (hspv : spread.val = s.count.val * s.xx.val - s.x.val * s.x.val)
    (htiltv : 0 < spread.val → tilt.val = s.count.val * s.xy.val - s.x.val * s.y.val) :
    device.Device.eval_at d newest s spread tilt position ⦃ t =>
      let ahead := clampReach ((position.val : ℤ) - (newest.position.val : ℤ))
      t.val = Fixed.clamp64
        (newest.time.val + nominalZ d.rate ahead + beyondZ d.rate newest (keptList d) ahead) ⦄ := by
  unfold device.Device.eval_at
  obtain ⟨hx1, hx2, hy1, hy2, hxx1, hxx2, hxy1, hxy2⟩ :=
    sums_bounds_cap d.rate newest (keptList d) hle
  have hR : reachZ = 2 ^ 28 := rfl
  have hN : (s.count.val : ℤ) = ((keptList d).length : ℤ) := hc
  have hcnt_b : -(4096 : ℤ) ≤ s.count.val ∧ s.count.val ≤ 4096 := by omega
  have hsx_b : -(4096 * reachZ) ≤ s.x.val ∧ s.x.val ≤ 4096 * reachZ := by
    rw [hx]; exact ⟨hx1, hx2⟩
  have hsy_b : -(4096 * reachZ) ≤ s.y.val ∧ s.y.val ≤ 4096 * reachZ := by
    rw [hy]; exact ⟨hy1, hy2⟩
  have hsxx_b : -(4096 * reachZ ^ 2) ≤ s.xx.val ∧ s.xx.val ≤ 4096 * reachZ ^ 2 := by
    rw [hxx]; exact ⟨hxx1, hxx2⟩
  have hsxy_b : -(4096 * reachZ ^ 2) ≤ s.xy.val ∧ s.xy.val ≤ 4096 * reachZ ^ 2 := by
    rw [hxy]; exact ⟨hxy1, hxy2⟩
  have hcx_b := prod_bounds hcnt_b hsxx_b
  have hsx2_b := prod_bounds hsx_b hsx_b
  have hsp_b : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ s.count.val * s.xx.val - s.x.val * s.x.val
      ∧ s.count.val * s.xx.val - s.x.val * s.x.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
    rw [hR] at hcx_b hsx2_b ⊢; omega
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  have hiv : i.val = position.val := by rw [hi, U64.hcast_I128_val]
  have hi1v : i1.val = newest.position.val := by rw [hi1, U64.hcast_I128_val]
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = (position.val : ℤ) - (newest.position.val : ℤ) := by
    rw [hi2, I128.wrapping_sub_val _ _ (by rw [hiv, hi1v]; scalar_tac), hiv, hi1v]
  step as ⟨ahead, haheadv, halo, hahi⟩
  have haeq : ahead.val = clampReach ((position.val : ℤ) - (newest.position.val : ℤ)) := by
    rw [haheadv, hi2v]
  have hbeyond_spec :
      (if spread > 0#i128 then do
          let i3 ← lift (core.num.I128.wrapping_mul s.count ahead)
          let lever ← lift (core.num.I128.wrapping_sub i3 s.x)
          let i4 ← lift (core.num.I128.wrapping_mul s.y spread)
          let i5 ← lift (core.num.I128.wrapping_mul tilt lever)
          let i6 ← lift (core.num.I128.wrapping_add i4 i5)
          let i7 ← lift (core.num.I128.wrapping_mul s.count spread)
          fixed.div_floor_wide i6 i7
        else fixed.div_floor_wide s.y s.count)
      ⦃ beyond =>
        beyond.val = beyondZ d.rate newest (keptList d) ahead.val
        ∧ -2 ^ 124 ≤ beyond.val ∧ beyond.val ≤ 2 ^ 124 ⦄ := by
    split
    · rename_i hsp_gt
      have hsp_pos : 0 < spread.val := by scalar_tac
      have htilt_eq : tilt.val = s.count.val * s.xy.val - s.x.val * s.y.val := htiltv hsp_pos
      step as ⟨i3, hi3⟩
      step as ⟨lever, hlever⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      have hcxy_b := prod_bounds hcnt_b hsxy_b
      have hsxsy_b := prod_bounds hsx_b hsy_b
      have htilt_b : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ s.count.val * s.xy.val - s.x.val * s.y.val
          ∧ s.count.val * s.xy.val - s.x.val * s.y.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
        rw [hR] at hcxy_b hsxsy_b ⊢; omega
      have hca_b := prod_bounds hcnt_b ⟨halo, hahi⟩
      have hi3v : i3.val = s.count.val * ahead.val := by
        rw [hi3, I128.wrapping_mul_val _ _ (by rw [hR] at hca_b; omega)]
      have hlever_b : -(2 * 4096 * reachZ) ≤ s.count.val * ahead.val - s.x.val
          ∧ s.count.val * ahead.val - s.x.val ≤ 2 * 4096 * reachZ := by
        rw [hR] at hca_b hsx_b ⊢; omega
      have hleverv : lever.val = s.count.val * ahead.val - s.x.val := by
        rw [hlever, I128.wrapping_sub_val _ _ (by rw [hi3v]; rw [hR] at hlever_b; omega), hi3v]
      have hsp_abs : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ spread.val
          ∧ spread.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
        rw [hspv]; exact hsp_b
      have hi4_b := prod_bounds hsy_b hsp_abs
      have hi4v : i4.val = s.y.val * spread.val := by
        rw [hi4, I128.wrapping_mul_val _ _ (by rw [hR] at hi4_b; omega)]
      have htilt_b' : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ tilt.val
          ∧ tilt.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by rw [htilt_eq]; exact htilt_b
      have hlever_b' : -(2 * 4096 * reachZ) ≤ lever.val
          ∧ lever.val ≤ 2 * 4096 * reachZ := by rw [hleverv]; exact hlever_b
      have hi5_b := prod_bounds htilt_b' hlever_b'
      have hi5v : i5.val = tilt.val * lever.val := by
        rw [hi5, I128.wrapping_mul_val _ _ (by rw [hR] at hi5_b; omega)]
      have hi6_b : -(6 * 4096 ^ 3 * reachZ ^ 3) ≤ i4.val + i5.val
          ∧ i4.val + i5.val ≤ 6 * 4096 ^ 3 * reachZ ^ 3 := by
        rw [hi4v, hi5v]; rw [hR] at hi4_b hi5_b ⊢; omega
      have hi6v : i6.val = i4.val + i5.val := by
        rw [hi6, I128.wrapping_add_val _ _ (by rw [hR] at hi6_b; omega)]
      have hi7_b := prod_bounds hcnt_b hsp_abs
      have hi7_pos : 0 < s.count.val * spread.val := mul_pos hcnt_pos hsp_pos
      have hi7v : i7.val = s.count.val * spread.val := by
        rw [hi7, I128.wrapping_mul_val _ _ (by rw [hR] at hi7_b; omega)]
      step with Fixed.div_floor_wide_spec as ⟨beyond, hbd_pos, _⟩
      have hbd_eq : beyond.val = i6.val / i7.val := hbd_pos (by rw [hi7v]; exact hi7_pos)
      have hbd_bounds : -2 ^ 124 ≤ beyond.val ∧ beyond.val ≤ 2 ^ 124 := by
        rw [hbd_eq]
        exact ediv_abs_bound (by rw [hi7v]; omega) (by norm_num)
          (by rw [hi6v]; rw [hR] at hi6_b; omega)
      have hbz : beyond.val = beyondZ d.rate newest (keptList d) ahead.val := by
        unfold beyondZ
        dsimp only
        have hsp_eq' : ((keptList d).length : ℤ) * sumXX newest (keptList d)
            - sumX newest (keptList d) * sumX newest (keptList d) = spread.val := by
          rw [hspv, hN, hxx, hx]
        rw [hsp_eq']
        simp only [hsp_pos, ↓reduceIte]
        rw [hbd_eq, hi6v, hi4v, hi5v, hi7v, htilt_eq, hleverv, hN, hx, hy, hxy]
      exact ⟨hbz, hbd_bounds.1, hbd_bounds.2⟩
    · rename_i hsp_le
      have hsp_nonpos : spread.val ≤ 0 := by scalar_tac
      step with Fixed.div_floor_wide_spec as ⟨beyond, hbd_pos, _⟩
      have hbd_eq : beyond.val = s.y.val / s.count.val := hbd_pos hcnt_pos
      have hbd_bounds : -2 ^ 124 ≤ beyond.val ∧ beyond.val ≤ 2 ^ 124 := by
        rw [hbd_eq]
        exact ediv_abs_bound (by omega) (by norm_num) (by rw [hR] at hsy_b; omega)
      have hbz : beyond.val = beyondZ d.rate newest (keptList d) ahead.val := by
        unfold beyondZ
        dsimp only
        have hsp_eq' : ((keptList d).length : ℤ) * sumXX newest (keptList d)
            - sumX newest (keptList d) * sumX newest (keptList d) = spread.val := by
          rw [hspv, hN, hxx, hx]
        rw [hsp_eq']
        have hnot : ¬ (0 < spread.val) := by omega
        simp only [hnot, ↓reduceIte]
        rw [hbd_eq, hN, hy]
      exact ⟨hbz, hbd_bounds.1, hbd_bounds.2⟩
  apply WP.spec_bind hbeyond_spec
  intro beyond ⟨hbz, hbdlo, hbdhi⟩
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = newest.time.val := by rw [hi3, I64.cast_I128_val]
  step with nominal_spec d ahead ⟨halo, hahi⟩ as ⟨i4, hi4v, hi4lo, hi4hi⟩
  step as ⟨i5, hi5⟩
  have hi5v : i5.val = newest.time.val + nominalZ d.rate ahead.val := by
    rw [hi5, I128.wrapping_add_val _ _ (by rw [hi3v, hR] at *; scalar_tac), hi3v, hi4v]
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = newest.time.val + nominalZ d.rate ahead.val + beyond.val := by
    rw [hi6, I128.wrapping_add_val _ _ (by
      rw [hi5v]
      have hnt := newest.time.hBounds
      simp at hnt
      have hnb := nominalZ_bounds d.rate ahead.val ⟨halo, hahi⟩
      rw [hR] at hnb
      omega), hi5v]
  step with Fixed.saturate_spec as ⟨t, ht⟩
  rw [ht, hi6v, hbz, haeq]

/-- Exact integer specification of `Device::fit`: computes the exact sums,
spread, and tilt over `keptList d` with zero wrapping. -/
theorem fit_spec (d : device.Device W) :
    device.Device.fit d ⦃ out =>
      match newestReading d with
      | none => out = none
      | some newest =>
          ∃ s spread tilt, out = some (newest, s, spread, tilt)
            ∧ s.count.val = ((keptList d).length : ℤ)
            ∧ (0 : ℤ) < s.count.val
            ∧ (keptList d).length ≤ 4096
            ∧ s.x.val = sumX newest (keptList d)
            ∧ s.y.val = sumY d.rate newest (keptList d)
            ∧ s.xx.val = sumXX newest (keptList d)
            ∧ s.xy.val = sumXY d.rate newest (keptList d)
            ∧ spread.val = s.count.val * s.xx.val - s.x.val * s.x.val
            ∧ (0 < spread.val → tilt.val = s.count.val * s.xy.val - s.x.val * s.y.val) ⦄ := by
  unfold device.Device.fit
  step with newest_spec d as ⟨o, ho, hnone⟩
  cases o with
  | none =>
    simp [ho.symm]
  | some newest =>
    simp only
    have hne : ¬ (d.len.val = 0 ∨ W.val = 0) := by
      intro hc
      have := hnone.mpr hc
      cases this
    have hlen_pos : 0 < d.len.val := by omega
    have hW_pos : 0 < W.val := by omega
    step with sums_spec d newest as ⟨s, hc, hx, hy, hxx, hxy, hle⟩
    have hkl_pos : 0 < (keptList d).length := by
      rw [keptList_length]; omega
    have hcnt_pos : (0 : ℤ) < s.count.val := by omega
    split
    · rename_i hle0
      have : s.count.val ≤ 0 := by scalar_tac
      omega
    · obtain ⟨hx1, hx2, hy1, hy2, hxx1, hxx2, hxy1, hxy2⟩ :=
        sums_bounds_cap d.rate newest (keptList d) hle
      have hR : reachZ = 2 ^ 28 := rfl
      have hcnt_b : -(4096 : ℤ) ≤ s.count.val ∧ s.count.val ≤ 4096 := by omega
      have hsx_b : -(4096 * reachZ) ≤ s.x.val ∧ s.x.val ≤ 4096 * reachZ := by
        rw [hx]; exact ⟨hx1, hx2⟩
      have hsy_b : -(4096 * reachZ) ≤ s.y.val ∧ s.y.val ≤ 4096 * reachZ := by
        rw [hy]; exact ⟨hy1, hy2⟩
      have hsxx_b : -(4096 * reachZ ^ 2) ≤ s.xx.val ∧ s.xx.val ≤ 4096 * reachZ ^ 2 := by
        rw [hxx]; exact ⟨hxx1, hxx2⟩
      have hsxy_b : -(4096 * reachZ ^ 2) ≤ s.xy.val ∧ s.xy.val ≤ 4096 * reachZ ^ 2 := by
        rw [hxy]; exact ⟨hxy1, hxy2⟩
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      step as ⟨spread, hspread⟩
      have hcx_b := prod_bounds hcnt_b hsxx_b
      have hsx2_b := prod_bounds hsx_b hsx_b
      have hi_v : i.val = s.count.val * s.xx.val := by
        rw [hi, I128.wrapping_mul_val _ _ (by rw [hR] at hcx_b; omega)]
      have hi1_v : i1.val = s.x.val * s.x.val := by
        rw [hi1, I128.wrapping_mul_val _ _ (by rw [hR] at hsx2_b; omega)]
      have hsp_b : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ s.count.val * s.xx.val - s.x.val * s.x.val
          ∧ s.count.val * s.xx.val - s.x.val * s.x.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
        rw [hR] at hcx_b hsx2_b ⊢; omega
      have hspv : spread.val = s.count.val * s.xx.val - s.x.val * s.x.val := by
        rw [hspread, I128.wrapping_sub_val _ _ (by rw [hi_v, hi1_v]; rw [hR] at hsp_b; omega),
          hi_v, hi1_v]
      split
      · rename_i hsp_gt
        step as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        step as ⟨tilt, htilt⟩
        have hcxy_b := prod_bounds hcnt_b hsxy_b
        have hsxsy_b := prod_bounds hsx_b hsy_b
        have hi2_v : i2.val = s.count.val * s.xy.val := by
          rw [hi2, I128.wrapping_mul_val _ _ (by rw [hR] at hcxy_b; omega)]
        have hi3_v : i3.val = s.x.val * s.y.val := by
          rw [hi3, I128.wrapping_mul_val _ _ (by rw [hR] at hsxsy_b; omega)]
        have htilt_b : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ s.count.val * s.xy.val - s.x.val * s.y.val
            ∧ s.count.val * s.xy.val - s.x.val * s.y.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
          rw [hR] at hcxy_b hsxsy_b ⊢; omega
        have htilt_v : tilt.val = s.count.val * s.xy.val - s.x.val * s.y.val := by
          rw [htilt, I128.wrapping_sub_val _ _ (by rw [hi2_v, hi3_v]; rw [hR] at htilt_b; omega),
            hi2_v, hi3_v]
        simp only [← ho]
        exact ⟨s, spread, tilt, rfl, hc, hcnt_pos, hle, hx, hy, hxx, hxy, hspv, fun _ => htilt_v⟩
      · rename_i hsp_le
        have hsp_nonpos : spread.val ≤ 0 := by scalar_tac
        rw [WP.spec_ok]
        simp only [← ho]
        exact ⟨s, spread, 0#i128, rfl, hc, hcnt_pos, hle, hx, hy, hxx, hxy, hspv,
          fun hpos => by omega⟩

/-- Exact integer specification of `Device::when`: for any window size `W`,
any device state, and any queried position, no intermediate 128-bit arithmetic
wraps, and when reports are held the returned timestamp equals
`clamp64 (newest.time + nominal(ahead) + beyondZ)`. -/
theorem when_spec (d : device.Device W) (position : Std.U64) :
    device.Device.when d position ⦃ out =>
      match newestReading d with
      | none => out = none
      | some newest =>
          ∃ t, out = some t
            ∧ let ahead := clampReach ((position.val : ℤ) - (newest.position.val : ℤ))
              t.val = Fixed.clamp64
                (newest.time.val + nominalZ d.rate ahead + beyondZ d.rate newest (keptList d) ahead) ⦄ := by
  unfold device.Device.when
  step with fit_spec d as ⟨o, ho⟩
  cases hnew : newestReading d with
  | none =>
    rw [hnew] at ho
    rw [ho]
    simp
  | some newest =>
    rw [hnew] at ho
    obtain ⟨s, spread, tilt, ho_eq, hc, hcnt_pos, hle, hx, hy, hxx, hxy, hspv, htiltv⟩ := ho
    rw [ho_eq]
    simp only
    step with eval_at_spec d newest s spread tilt position hc hcnt_pos hle hx hy hxx hxy hspv htiltv
      as ⟨t, ht⟩
    exact ⟨t, rfl, ht⟩

/-- Exact integer specification of `Device::when_cycle`: for any window size
`W`, any device state, any queried position, and any cycle frame count, no
intermediate 128-bit arithmetic wraps, the returned start time matches
`Device::when`, and the returned sub-nanosecond cycle duration equals
`clamp64 (nominalQ16Z + beyondSlopeQ16Z)`. -/
theorem when_cycle_spec (d : device.Device W) (position : Std.U64) (frames : Std.U32) :
    device.Device.when_cycle d position frames ⦃ out =>
      match newestReading d with
      | none => out = none
      | some newest =>
          ∃ start dur, out = some (start, dur)
            ∧ let ahead := clampReach ((position.val : ℤ) - (newest.position.val : ℤ))
              let span := clampReach (frames.val : ℤ)
              start.val = Fixed.clamp64
                (newest.time.val + nominalZ d.rate ahead
                  + beyondZ d.rate newest (keptList d) ahead)
              ∧ dur.val = Fixed.clamp64
                (nominalQ16Z d.rate span + beyondSlopeQ16Z d.rate newest (keptList d) span) ⦄ := by
  unfold device.Device.when_cycle
  step with fit_spec d as ⟨o, ho⟩
  cases hnew : newestReading d with
  | none =>
    rw [hnew] at ho
    rw [ho]
    simp
  | some newest =>
    rw [hnew] at ho
    obtain ⟨s, spread, tilt, ho_eq, hc, hcnt_pos, hle, hx, hy, hxx, hxy, hspv, htiltv⟩ := ho
    rw [ho_eq]
    simp only
    obtain ⟨hx1, hx2, hy1, hy2, hxx1, hxx2, hxy1, hxy2⟩ :=
      sums_bounds_cap d.rate newest (keptList d) hle
    have hR : reachZ = 2 ^ 28 := rfl
    have hN : (s.count.val : ℤ) = ((keptList d).length : ℤ) := hc
    have hcnt_b : -(4096 : ℤ) ≤ s.count.val ∧ s.count.val ≤ 4096 := by omega
    have hsx_b : -(4096 * reachZ) ≤ s.x.val ∧ s.x.val ≤ 4096 * reachZ := by
      rw [hx]; exact ⟨hx1, hx2⟩
    have hsy_b : -(4096 * reachZ) ≤ s.y.val ∧ s.y.val ≤ 4096 * reachZ := by
      rw [hy]; exact ⟨hy1, hy2⟩
    have hsxy_b : -(4096 * reachZ ^ 2) ≤ s.xy.val ∧ s.xy.val ≤ 4096 * reachZ ^ 2 := by
      rw [hxy]; exact ⟨hxy1, hxy2⟩
    step with eval_at_spec d newest s spread tilt position hc hcnt_pos hle hx hy hxx hxy hspv htiltv
      as ⟨start, hstart⟩
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = (frames.val : ℤ) := by rw [hi2, U32.hcast_I128_val]
    step as ⟨span, hspan_eq, hspan_lo, hspan_hi⟩
    have hspanv : span.val = clampReach (frames.val : ℤ) := by rw [hspan_eq, hi2v]
    step as ⟨span_q16, hsq⟩
    have hsq_v : span_q16.val = span.val * 2 ^ 16 := by
      have h16 : (16#u32).val = 16 := rfl
      rw [hsq, I128.wrapping_shl_val span 16#u32 (by rw [h16]; omega)
        (by rw [h16]; rw [hR] at hspan_lo hspan_hi; omega), h16]
    have hsq_b : -(reachZ * 2 ^ 16) ≤ span_q16.val ∧ span_q16.val ≤ reachZ * 2 ^ 16 := by
      rw [hsq_v, hR] at *; omega
    have hb : device.BILLION.val = 10 ^ 9 := by simp [device.BILLION]
    step as ⟨i3, hi3⟩
    have hi3v : i3.val = span.val * 2 ^ 16 * 10 ^ 9 := by
      rw [hi3, I128.wrapping_mul_val _ _ (by rw [hsq_v, hb, hR] at *; omega), hsq_v, hb]
    step as ⟨i4, hi4⟩
    have hi4v : i4.val = (d.rate.val : ℤ) := by rw [hi4, U32.hcast_I64_val]
    step with Fixed.div_floor_spec i3 i4 as ⟨nominal_q16, hnq_pos, hnq_zero⟩
    have hnq_eq : nominal_q16.val = nominalQ16Z d.rate span.val := by
      unfold nominalQ16Z
      by_cases hr0 : d.rate.val = 0
      · simp only [hr0, ↓reduceIte]
        exact hnq_zero (by omega)
      · simp only [hr0, ↓reduceIte]
        rw [hnq_pos (by omega), hi3v, hi4v]
    have hnq_b : -(2 ^ 75 : ℤ) ≤ nominal_q16.val ∧ nominal_q16.val ≤ 2 ^ 75 := by
      rw [hnq_eq]
      unfold nominalQ16Z
      by_cases hr0 : d.rate.val = 0
      · simp [hr0]
      · simp only [hr0, ↓reduceIte]
        exact ediv_abs_bound (by omega) (by norm_num) (by rw [hR] at hspan_lo hspan_hi; omega)
    have hbeyond_q16_spec :
        (if spread > 0#i128 then do
            let i5 ← lift (core.num.I128.wrapping_mul span_q16 tilt)
            fixed.div_floor_wide i5 spread
          else ok 0#i128)
        ⦃ bq =>
          bq.val = beyondSlopeQ16Z d.rate newest (keptList d) span.val
          ∧ -(2 ^ 126 : ℤ) ≤ bq.val ∧ bq.val ≤ 2 ^ 126 ⦄ := by
      split
      · rename_i hsp_gt
        have hsp_pos : 0 < spread.val := by scalar_tac
        have htilt_eq : tilt.val = s.count.val * s.xy.val - s.x.val * s.y.val := htiltv hsp_pos
        step as ⟨i5, hi5⟩
        have hcxy_b := prod_bounds hcnt_b hsxy_b
        have hsxsy_b := prod_bounds hsx_b hsy_b
        have htilt_b : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ s.count.val * s.xy.val - s.x.val * s.y.val
            ∧ s.count.val * s.xy.val - s.x.val * s.y.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
          rw [hR] at hcxy_b hsxsy_b ⊢; omega
        have htilt_b' : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ tilt.val
            ∧ tilt.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by rw [htilt_eq]; exact htilt_b
        have hi5_b := prod_bounds hsq_b htilt_b'
        have hi5v : i5.val = span_q16.val * tilt.val := by
          rw [hi5, I128.wrapping_mul_val _ _ (by rw [hR] at hi5_b; omega)]
        step with Fixed.div_floor_wide_spec i5 spread as ⟨bq, hbq_pos, _⟩
        have hbq_eq : bq.val = i5.val / spread.val := hbq_pos hsp_pos
        have hbq_b : -(2 ^ 126 : ℤ) ≤ bq.val ∧ bq.val ≤ 2 ^ 126 := by
          rw [hbq_eq]
          exact ediv_abs_bound (by omega) (by norm_num) (by rw [hi5v]; rw [hR] at hi5_b; omega)
        have hbq_z : bq.val = beyondSlopeQ16Z d.rate newest (keptList d) span.val := by
          unfold beyondSlopeQ16Z
          dsimp only
          have hsp_eq' : ((keptList d).length : ℤ) * sumXX newest (keptList d)
              - sumX newest (keptList d) * sumX newest (keptList d) = spread.val := by
            rw [hspv, hN, hxx, hx]
          rw [hsp_eq']
          simp only [hsp_pos, ↓reduceIte]
          rw [hbq_eq, hi5v, hsq_v, htilt_eq, hN, hx, hy, hxy]
        exact ⟨hbq_z, hbq_b.1, hbq_b.2⟩
      · rename_i hsp_le
        have hsp_nonpos : spread.val ≤ 0 := by scalar_tac
        rw [WP.spec_ok]
        have h0 : (0#i128).val = 0 := by rfl
        have hsp_eq' : ((keptList d).length : ℤ) * sumXX newest (keptList d)
            - sumX newest (keptList d) * sumX newest (keptList d) = spread.val := by
          rw [hspv, hN, hxx, hx]
        have hnot : ¬ (0 < spread.val) := by omega
        refine ⟨?_, by rw [h0]; norm_num, by rw [h0]; norm_num⟩
        unfold beyondSlopeQ16Z
        dsimp only
        rw [hsp_eq']
        simp only [hnot, ↓reduceIte, h0]
    apply WP.spec_bind hbeyond_q16_spec
    intro beyond_q16 ⟨hbqz, hbq_lo, hbq_hi⟩
    step as ⟨i5, hi5⟩
    have hi5v : i5.val = nominal_q16.val + beyond_q16.val := by
      rw [hi5, I128.wrapping_add_val _ _ (by omega)]
    step with Fixed.saturate_spec as ⟨dur, hdur⟩
    exact ⟨start, dur, rfl, hstart, by rw [hdur, hi5v, hnq_eq, hbqz, hspanv]⟩

/-- Asking when a position's frame leaves the device returns for every state
and every position. -/
theorem when_total (d : device.Device W) (position : Std.U64) :
    device.Device.when d position ⦃ _ => True ⦄ :=
  WP.spec_mono (when_spec d position) fun _ _ => trivial

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
the exact integer floor of the least-squares optimal residual line from
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
exact integer floor of `2^16 * span` times the least-squares optimal residual
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
