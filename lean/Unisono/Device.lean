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
public import Unisono.Player
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

@[step]
theorem restarted_total (d : device.Device W) (position : Std.U64) (time : Std.I64) :
    device.Device.restarted d position time ⦃ _ => True ⦄ := by
  unfold device.Device.restarted
  step as ⟨o, _, _⟩
  cases o with
  | none => simp
  | some newest =>
    simp only
    run

private theorem observe_write_spec (d1 : device.Device W) (cap : Std.Usize)
    (position : Std.U64) (time : Std.I64)
    (hcap : cap.val = min W.val 4096) :
    (do
      let i ← if d1.len > cap then ok cap else ok d1.len
      if cap = 0#usize then ok { d1 with len := i }
      else
        let i1 ← if d1.next >= cap then ok 0#usize else ok d1.next
        let (s, to_slice_mut_back) ← lift (Array.to_slice_mut d1.readings)
        let (o, get_mut_back) ←
          core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice device.Reading) s i1
        let a ←
          match o with
          | none =>
            let s1 := get_mut_back none
            ok (to_slice_mut_back s1)
          | some _ =>
            let s1 := get_mut_back (some { position, time })
            ok (to_slice_mut_back s1)
        let next ← lift (core.num.Usize.saturating_add i1 1#usize)
        let next1 ← if next >= cap then ok 0#usize else ok next
        if i < cap then
          let i2 ← lift (core.num.Usize.saturating_add i 1#usize)
          ok { d1 with readings := a, len := i2, next := next1 }
        else ok { d1 with readings := a, len := i, next := next1 })
    ⦃ d' =>
      d'.rate = d1.rate
      ∧ d'.len.val ≤ min W.val 4096
      ∧ (0 < W.val → d'.next.val < min W.val 4096) ⦄ := by
  have hi_spec : (if d1.len > cap then ok cap else ok d1.len) ⦃ i => i.val ≤ cap.val ⦄ := by
    split <;> simp only [WP.spec_ok] <;> scalar_tac
  apply WP.spec_bind hi_spec
  intro i hi
  split
  · rename_i hc0
    have hc0v : cap.val = 0 := by scalar_tac
    rw [WP.spec_ok]
    dsimp only
    exact ⟨rfl, by omega, fun hW => by omega⟩
  · rename_i hcne0
    have hcpos : 0 < cap.val := by scalar_tac
    have hi1_spec : (if d1.next >= cap then ok 0#usize else ok d1.next)
        ⦃ i1 => i1.val < cap.val ⦄ := by
      split <;> simp only [WP.spec_ok] <;> scalar_tac
    apply WP.spec_bind hi1_spec
    intro i1 hi1
    simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
      core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
    have ha_spec : ∀ a : Array device.Reading W,
        (do
          let next1 ←
            if core.num.Usize.saturating_add i1 1#usize >= cap then ok 0#usize
            else ok (core.num.Usize.saturating_add i1 1#usize)
          if i < cap then
            ok { d1 with readings := a, len := core.num.Usize.saturating_add i 1#usize, next := next1 }
          else ok { d1 with readings := a, len := i, next := next1 })
        ⦃ d' =>
          d'.rate = d1.rate
          ∧ d'.len.val ≤ min W.val 4096
          ∧ (0 < W.val → d'.next.val < min W.val 4096) ⦄ := by
      intro a
      have hn1_spec :
          (if core.num.Usize.saturating_add i1 1#usize >= cap then ok 0#usize
           else ok (core.num.Usize.saturating_add i1 1#usize))
          ⦃ next1 => next1.val < cap.val ⦄ := by
        split <;> simp only [WP.spec_ok] <;> scalar_tac
      apply WP.spec_bind hn1_spec
      intro next1 hnext1
      split
      · rename_i hilt
        have hil : i.val < cap.val := by scalar_tac
        have hi2v : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 := by
          rw [Usize.saturating_add_val _ _ (by scalar_tac)]; rfl
        rw [WP.spec_ok]
        dsimp only
        exact ⟨rfl, by omega, fun _ => by omega⟩
      · rw [WP.spec_ok]
        dsimp only
        exact ⟨rfl, by omega, fun _ => by omega⟩
    have ha_match :
        (match d1.readings.to_slice[i1]? with
          | none => ok (d1.readings.from_slice (d1.readings.to_slice.set_opt i1 none))
          | some _ =>
            ok (d1.readings.from_slice
              (d1.readings.to_slice.set_opt i1 (some { position, time }))))
        ⦃ _ => True ⦄ := by
      cases d1.readings.to_slice[i1]? <;> simp
    apply WP.spec_bind ha_match
    intro a _
    exact ha_spec a

/-- Taking in a report returns for every state and every report, keeps `rate`
unchanged, and leaves `len` and `next` within the device's capacity. -/
theorem observe_spec (d : device.Device W) (position : Std.U64) (time : Std.I64) :
    device.Device.observe d position time ⦃ d' =>
      d'.rate = d.rate
      ∧ d'.len.val ≤ min W.val 4096
      ∧ (0 < W.val → d'.next.val < min W.val 4096) ⦄ := by
  unfold device.Device.observe
  step as ⟨cap, hcap, hcapW, hcapM⟩
  step as ⟨b⟩
  split
  · simp only [bind_ok]
    exact observe_write_spec { d with len := 0#usize, next := 0#usize } cap position time hcap
  · simp only [bind_ok]
    exact observe_write_spec d cap position time hcap

/-- Taking in a report returns for every state of the device and every report. -/
theorem observe_total (d : device.Device W) (position : Std.U64) (time : Std.I64) :
    device.Device.observe d position time ⦃ _ => True ⦄ :=
  WP.spec_mono (observe_spec d position time) fun _ _ => trivial

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
    have hcnt_le : s.count.val ≤ 4096 := by omega
    split
    · rename_i hle0
      have : s.count.val ≤ 0 := by scalar_tac
      omega
    · obtain ⟨hx1, hx2, hy1, hy2, hxx1, hxx2, hxy1, hxy2⟩ :=
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
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨spread, hspread⟩
      have hcx_b := prod_bounds hcnt_b hsxx_b
      have hsx2_b := prod_bounds hsx_b hsx_b
      have hi3v : i3.val = s.count.val * s.xx.val := by
        rw [hi3, I128.wrapping_mul_val _ _ (by rw [hR] at hcx_b; omega)]
      have hi4v : i4.val = s.x.val * s.x.val := by
        rw [hi4, I128.wrapping_mul_val _ _ (by rw [hR] at hsx2_b; omega)]
      have hsp_b : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ s.count.val * s.xx.val - s.x.val * s.x.val
          ∧ s.count.val * s.xx.val - s.x.val * s.x.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
        rw [hR] at hcx_b hsx2_b ⊢; omega
      have hspv : spread.val = s.count.val * s.xx.val - s.x.val * s.x.val := by
        rw [hspread, I128.wrapping_sub_val _ _ (by rw [hi3v, hi4v]; rw [hR] at hsp_b; omega),
          hi3v, hi4v]
      have hbeyond_spec :
          (if spread > 0#i128 then do
              let i5 ← lift (core.num.I128.wrapping_mul s.count s.xy)
              let i6 ← lift (core.num.I128.wrapping_mul s.x s.y)
              let tilt ← lift (core.num.I128.wrapping_sub i5 i6)
              let i7 ← lift (core.num.I128.wrapping_mul s.count ahead)
              let lever ← lift (core.num.I128.wrapping_sub i7 s.x)
              let i8 ← lift (core.num.I128.wrapping_mul s.y spread)
              let i9 ← lift (core.num.I128.wrapping_mul tilt lever)
              let i10 ← lift (core.num.I128.wrapping_add i8 i9)
              let i11 ← lift (core.num.I128.wrapping_mul s.count spread)
              fixed.div_floor_wide i10 i11
            else fixed.div_floor_wide s.y s.count)
          ⦃ beyond =>
            beyond.val = beyondZ d.rate newest (keptList d) ahead.val
            ∧ -2 ^ 124 ≤ beyond.val ∧ beyond.val ≤ 2 ^ 124 ⦄ := by
        split
        · rename_i hsp_gt
          have hsp_pos : 0 < spread.val := by scalar_tac
          step as ⟨i5, hi5⟩
          step as ⟨i6, hi6⟩
          step as ⟨tilt, htilt⟩
          step as ⟨i7, hi7⟩
          step as ⟨lever, hlever⟩
          step as ⟨i8, hi8⟩
          step as ⟨i9, hi9⟩
          step as ⟨i10, hi10⟩
          step as ⟨i11, hi11⟩
          have hcxy_b := prod_bounds hcnt_b hsxy_b
          have hsxsy_b := prod_bounds hsx_b hsy_b
          have hi5v : i5.val = s.count.val * s.xy.val := by
            rw [hi5, I128.wrapping_mul_val _ _ (by rw [hR] at hcxy_b; omega)]
          have hi6v : i6.val = s.x.val * s.y.val := by
            rw [hi6, I128.wrapping_mul_val _ _ (by rw [hR] at hsxsy_b; omega)]
          have htilt_b : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ s.count.val * s.xy.val - s.x.val * s.y.val
              ∧ s.count.val * s.xy.val - s.x.val * s.y.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
            rw [hR] at hcxy_b hsxsy_b ⊢; omega
          have htiltv : tilt.val = s.count.val * s.xy.val - s.x.val * s.y.val := by
            rw [htilt, I128.wrapping_sub_val _ _ (by rw [hi5v, hi6v]; rw [hR] at htilt_b; omega),
              hi5v, hi6v]
          have hca_b := prod_bounds hcnt_b ⟨halo, hahi⟩
          have hi7v : i7.val = s.count.val * ahead.val := by
            rw [hi7, I128.wrapping_mul_val _ _ (by rw [hR] at hca_b; omega)]
          have hlever_b : -(2 * 4096 * reachZ) ≤ s.count.val * ahead.val - s.x.val
              ∧ s.count.val * ahead.val - s.x.val ≤ 2 * 4096 * reachZ := by
            rw [hR] at hca_b hsx_b ⊢; omega
          have hleverv : lever.val = s.count.val * ahead.val - s.x.val := by
            rw [hlever, I128.wrapping_sub_val _ _ (by rw [hi7v]; rw [hR] at hlever_b; omega), hi7v]
          have hsp_abs : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ spread.val
              ∧ spread.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by
            rw [hspv]; exact hsp_b
          have hi8_b := prod_bounds hsy_b hsp_abs
          have hi8v : i8.val = s.y.val * spread.val := by
            rw [hi8, I128.wrapping_mul_val _ _ (by rw [hR] at hi8_b; omega)]
          have htilt_b' : -(2 * 4096 * 4096 * reachZ ^ 2) ≤ tilt.val
              ∧ tilt.val ≤ 2 * 4096 * 4096 * reachZ ^ 2 := by rw [htiltv]; exact htilt_b
          have hlever_b' : -(2 * 4096 * reachZ) ≤ lever.val
              ∧ lever.val ≤ 2 * 4096 * reachZ := by rw [hleverv]; exact hlever_b
          have hi9_b := prod_bounds htilt_b' hlever_b'
          have hi9v : i9.val = tilt.val * lever.val := by
            rw [hi9, I128.wrapping_mul_val _ _ (by rw [hR] at hi9_b; omega)]
          have hi10_b : -(6 * 4096 ^ 3 * reachZ ^ 3) ≤ i8.val + i9.val
              ∧ i8.val + i9.val ≤ 6 * 4096 ^ 3 * reachZ ^ 3 := by
            rw [hi8v, hi9v]; rw [hR] at hi8_b hi9_b ⊢; omega
          have hi10v : i10.val = i8.val + i9.val := by
            rw [hi10, I128.wrapping_add_val _ _ (by rw [hR] at hi10_b; omega)]
          have hi11_b := prod_bounds hcnt_b hsp_abs
          have hi11_pos : 0 < s.count.val * spread.val := mul_pos hcnt_pos hsp_pos
          have hi11v : i11.val = s.count.val * spread.val := by
            rw [hi11, I128.wrapping_mul_val _ _ (by rw [hR] at hi11_b; omega)]
          step with Fixed.div_floor_wide_spec as ⟨beyond, hbd_pos, _⟩
          have hbd_eq : beyond.val = i10.val / i11.val := hbd_pos (by rw [hi11v]; exact hi11_pos)
          have hbd_bounds : -2 ^ 124 ≤ beyond.val ∧ beyond.val ≤ 2 ^ 124 := by
            rw [hbd_eq]
            exact ediv_abs_bound (by rw [hi11v]; omega) (by norm_num)
              (by rw [hi10v]; rw [hR] at hi10_b; omega)
          have hbz : beyond.val = beyondZ d.rate newest (keptList d) ahead.val := by
            unfold beyondZ
            dsimp only
            have hsp_eq' : ((keptList d).length : ℤ) * sumXX newest (keptList d)
                - sumX newest (keptList d) * sumX newest (keptList d) = spread.val := by
              rw [hspv, hN, hxx, hx]
            rw [hsp_eq']
            simp only [hsp_pos, ↓reduceIte]
            rw [hbd_eq, hi10v, hi8v, hi9v, hi11v, htiltv, hleverv, hN, hx, hy, hxy]
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
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = newest.time.val := by rw [hi5, I64.cast_I128_val]
      step with nominal_spec d ahead ⟨halo, hahi⟩ as ⟨i6, hi6v, hi6lo, hi6hi⟩
      step as ⟨i7, hi7⟩
      have hi7v : i7.val = newest.time.val + nominalZ d.rate ahead.val := by
        rw [hi7, I128.wrapping_add_val _ _ (by rw [hi5v, hR] at *; scalar_tac), hi5v, hi6v]
      step as ⟨i8, hi8⟩
      have hi8v : i8.val = newest.time.val + nominalZ d.rate ahead.val + beyond.val := by
        rw [hi8, I128.wrapping_add_val _ _ (by
          rw [hi7v]
          have hnt := newest.time.hBounds
          simp at hnt
          have hnb := nominalZ_bounds d.rate ahead.val ⟨halo, hahi⟩
          rw [hR] at hnb
          omega), hi7v]
      step with Fixed.saturate_spec as ⟨i9, hi9⟩
      simp only [← ho]
      exact ⟨i9, rfl, by rw [hi9, hi8v, hbz, haeq]⟩

/-- Asking when a position's frame leaves the device returns for every state
and every position. -/
theorem when_total (d : device.Device W) (position : Std.U64) :
    device.Device.when d position ⦃ _ => True ⦄ :=
  WP.spec_mono (when_spec d position) fun _ _ => trivial

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

end

end Unisono.Device
