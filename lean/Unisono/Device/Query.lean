/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Device.Sums

/-!
# Device clock model: line evaluation and cycle queries

Exact integer residual and Q16 slope specifications (`beyondZ`, `beyondSlopeQ16Z`),
`eval_at`, `fit`, `when`, and `when_cycle`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Device

variable {W : Std.Usize}

/-- Runs a function to its end: step by step, taking conditionals apart. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

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


end Unisono.Device
