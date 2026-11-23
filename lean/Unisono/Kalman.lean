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
# Two-state fixed-point Kalman filter

Totality, positive semi-definiteness (`p00 ≥ 0 ∧ p11 ≥ 0 ∧ p01² ≤ p00 * p11`),
bumpless offset-shift invariance, and valid `Line` export (`run = LINE_RUN > 0`)
for `unisono_core::kalman`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Kalman

/-- Positive semi-definiteness of a 2×2 fixed-point covariance `(p00, p01, p11)`:
both variances are non-negative and the off-diagonal obeys `p01² ≤ p00 * p11`. -/
def IsPsd (p00 p01 p11 : Std.I128) : Prop :=
  0 ≤ p00.val ∧ 0 ≤ p11.val ∧ p01.val * p01.val ≤ p00.val * p11.val

/-- `clamp_nonneg` bounds its output to `[0, hi]` when `hi ≥ 0`. -/
@[step]
theorem clamp_nonneg_spec (x hi : Std.I128) (hhi : 0 ≤ hi.val) :
    kalman.clamp_nonneg x hi ⦃ r => 0 ≤ r.val ∧ r.val ≤ hi.val ⦄ := by
  unfold kalman.clamp_nonneg
  split
  · simp; exact hhi
  · split
    · simp; exact hhi
    · simp; scalar_tac

/-- `clamp_sym` bounds its output to `[-hi, hi]` when `hi ≥ 0`. -/
@[step]
theorem clamp_sym_spec (x hi : Std.I128) (hhi : 0 ≤ hi.val) :
    kalman.clamp_sym x hi ⦃ r => -hi.val ≤ r.val ∧ r.val ≤ hi.val ⦄ := by
  unfold kalman.clamp_sym
  have hhi_max : hi.val < 2 ^ 127 := by scalar_tac
  have h0 : (0#i128).val = 0 := rfl
  have hlo : (core.num.I128.wrapping_sub 0#i128 hi).val = -hi.val := by
    rw [I128.wrapping_sub_val 0#i128 hi (by rw [h0]; omega), h0]; omega
  step as ⟨lo, hlo_eq⟩
  have hlov : lo.val = -hi.val := by rw [hlo_eq, hlo]
  split
  · simp; omega
  · split
    · simp; omega
    · simp; scalar_tac

@[step]
theorem clamp_sym_total (x hi : Std.I128) :
    kalman.clamp_sym x hi ⦃ _ => True ⦄ := by
  unfold kalman.clamp_sym
  step*

@[step]
theorem clamp_sym_i64_total (x hi : Std.I64) :
    kalman.clamp_sym_i64 x hi ⦃ _ => True ⦄ := by
  unfold kalman.clamp_sym_i64
  step*

@[step]
theorem abs_i128_total (x : Std.I128) :
    kalman.abs_i128 x ⦃ _ => True ⦄ := by
  unfold kalman.abs_i128
  step*

@[step]
theorem mul_shr_safe_total (a b : Std.I128) (shift : Std.U32) :
    kalman.mul_shr_safe a b shift ⦃ _ => True ⦄ := by
  unfold kalman.mul_shr_safe
  have hs : (if shift > 64#u32 then ok 64#u32 else ok shift) ⦃ _ => True ⦄ := by
    split <;> simp
  apply WP.spec_bind hs
  intro s _
  cases h1 : I128.checked_mul a b with
  | some prod => simp [lift]
  | none =>
    simp only [lift, bind_ok]
    have hmask :
        (if s = 64#u32 then ok 18446744073709551615#i128
         else ok (core.num.I128.wrapping_sub (core.num.I128.wrapping_shl 1#i128 s) 1#i128))
          ⦃ _ => True ⦄ := by
      split <;> simp
    apply WP.spec_bind hmask
    intro mask _
    step as ⟨t1⟩
    cases h2 : I128.checked_mul (a &&& mask) b with
    | some p => simp
    | none => step*

/-- **Covariance PSD enforcement:** `enforce_psd` always returns a positive
semi-definite 2×2 matrix (`p00 ≥ 0`, `p11 ≥ 0`, `p01² ≤ p00 * p11`) within
`[0, MAX_P00] × [0, MAX_P11]`. -/
@[step]
theorem enforce_psd_spec (p00_in p01_in p11_in : Std.I128) :
    kalman.enforce_psd p00_in p01_in p11_in ⦃ r =>
      IsPsd r.1 r.2.1 r.2.2
      ∧ r.1.val ≤ kalman.MAX_P00.val ∧ r.2.2.val ≤ kalman.MAX_P11.val ⦄ := by
  have hmax0 : 0 ≤ kalman.MAX_P00.val := by unfold kalman.MAX_P00; decide
  have hmax1 : 0 ≤ kalman.MAX_P11.val := by unfold kalman.MAX_P11; decide
  have hmax01 : 0 ≤ kalman.MAX_P01.val := by unfold kalman.MAX_P01; decide
  unfold kalman.enforce_psd
  step with clamp_nonneg_spec p00_in kalman.MAX_P00 hmax0 as ⟨p00, hp00_0, hp00_hi⟩
  step with clamp_nonneg_spec p11_in kalman.MAX_P11 hmax1 as ⟨p11, hp11_0, hp11_hi⟩
  step with clamp_sym_spec p01_in kalman.MAX_P01 hmax01 as ⟨p01, _, _⟩
  split
  · simp [IsPsd, hp00_0, hp11_0, hp00_hi, hp11_hi]; exact mul_nonneg hp00_0 hp11_0
  · split
    · simp [IsPsd, hp00_0, hp11_0, hp00_hi, hp11_hi]; exact mul_nonneg hp00_0 hp11_0
    · step as ⟨s0, hs0⟩
      step as ⟨s1, hs1⟩
      have hs0v : s0.val = p00.val / 2^16 := by
        rw [hs0, I128.wrapping_shr_val _ _ (by decide)]; rfl
      have hs1v : s1.val = p11.val / 2^16 := by
        rw [hs1, I128.wrapping_shr_val _ _ (by decide)]; rfl
      have hbound :
          (if s0 > 0#i128 then
            if s1 > 0#i128 then do
              let prod ← fixed.saturating_mul_i128 s0 s1
              let i ← fixed.root prod
              fixed.saturating_mul_i128 i 65536#i128
            else do
              let i ← fixed.saturating_mul_i128 p00 p11
              fixed.root i
          else do
            let i ← fixed.saturating_mul_i128 p00 p11
            fixed.root i)
          ⦃ b => 0 ≤ b.val ∧ b.val * b.val ≤ p00.val * p11.val ⦄ := by
        have hdirect :
            (do
              let i ← fixed.saturating_mul_i128 p00 p11
              fixed.root i) ⦃ b => 0 ≤ b.val ∧ b.val * b.val ≤ p00.val * p11.val ⦄ := by
          step with Fixed.saturating_mul_i128_spec p00 p11 as ⟨prod, hprod⟩
          step with Fixed.root_spec prod as ⟨b, hb0, hble0, hbpos⟩
          refine ⟨hb0, ?_⟩
          by_cases hpos : 0 < prod.val
          · have hsq := (hbpos hpos).1
            have hle_mul : prod.val ≤ p00.val * p11.val := by
              rw [hprod]
              have hnn : 0 ≤ p00.val * p11.val := mul_nonneg hp00_0 hp11_0
              simp only [Fixed.clamp128]
              omega
            linarith
          · have hb_zero : b.val = 0 := hble0 (by omega)
            rw [hb_zero]; nlinarith
        split
        · split
          · rename_i hs0p hs1p
            have hs0_pos : 0 < s0.val := by scalar_tac
            have hs1_pos : 0 < s1.val := by scalar_tac
            step with Fixed.saturating_mul_i128_spec s0 s1 as ⟨prod, hprod⟩
            step with Fixed.root_spec prod as ⟨rt, hrt0, hrtle0, hrtpos⟩
            step with Fixed.saturating_mul_i128_spec rt 65536#i128 as ⟨b, hb⟩
            have hrt_mul_nn : 0 ≤ rt.val * 2^16 := by nlinarith
            have hb0 : 0 ≤ b.val := by
              rw [hb]; simp only [Fixed.clamp128]; omega
            have hble : b.val ≤ rt.val * 2^16 := by
              rw [hb]; simp only [Fixed.clamp128]; omega
            have hrt_sq : rt.val * rt.val ≤ s0.val * s1.val := by
              by_cases hpos : 0 < prod.val
              · have hsq := (hrtpos hpos).1
                have hle_mul : prod.val ≤ s0.val * s1.val := by
                  rw [hprod]
                  have hnn : 0 ≤ s0.val * s1.val := mul_nonneg hs0_pos.le hs1_pos.le
                  simp only [Fixed.clamp128]; omega
                linarith
              · rw [hrtle0 (by omega)]; nlinarith
            have hs0_le : s0.val * 2^16 ≤ p00.val := by omega
            have hs1_le : s1.val * 2^16 ≤ p11.val := by omega
            refine ⟨hb0, ?_⟩
            have h1 : b.val * b.val ≤ (rt.val * 2^16) * (rt.val * 2^16) :=
              mul_le_mul hble hble hb0 hrt_mul_nn
            have h2 : (rt.val * 2^16) * (rt.val * 2^16) = (rt.val * rt.val) * (2^16 * 2^16) := by
              ring
            have h3 : (rt.val * rt.val) * (2^16 * 2^16) ≤ (s0.val * s1.val) * (2^16 * 2^16) :=
              mul_le_mul_of_nonneg_right hrt_sq (by norm_num)
            have h4 : (s0.val * s1.val) * (2^16 * 2^16) = (s0.val * 2^16) * (s1.val * 2^16) := by
              ring
            have h5 : (s0.val * 2^16) * (s1.val * 2^16) ≤ p00.val * p11.val :=
              mul_le_mul hs0_le hs1_le (by nlinarith) hp00_0
            linarith
          · exact hdirect
        · exact hdirect
      apply WP.spec_bind hbound
      rintro bound ⟨hb0, hble⟩
      step with clamp_sym_spec p01 bound hb0 as ⟨p01', hlo, hhi⟩
      refine ⟨⟨hp00_0, hp11_0, ?_⟩, hp00_hi, hp11_hi⟩
      have hsq : p01'.val * p01'.val ≤ bound.val * bound.val := by nlinarith
      linarith

/-! ## NoisePrior -/

@[step]
theorem noise_prior_combine_total (a b : kalman.NoisePrior) :
    kalman.NoisePrior.combine a b ⦃ _ => True ⦄ := by
  unfold kalman.NoisePrior.combine
  step*

@[step]
theorem noise_prior_scale_total (p : kalman.NoisePrior) (num den : Std.I64) :
    kalman.NoisePrior.scale p num den ⦃ _ => True ⦄ := by
  have hmax0 : 0 ≤ kalman.MAX_P00.val := by unfold kalman.MAX_P00; decide
  have hmax1 : 0 ≤ kalman.MAX_P11.val := by unfold kalman.MAX_P11; decide
  unfold kalman.NoisePrior.scale
  split
  · simp
  · split
    · simp
    · step with clamp_nonneg_spec p.q0_q16_ns2_per_s kalman.MAX_P00 hmax0 as ⟨q0⟩
      step with clamp_nonneg_spec p.q2_q80_per_s kalman.MAX_P11 hmax1 as ⟨q2⟩
      step*

/-! ## KalmanFilter lifecycle, PSD preservation, and `Line` export -/

private theorem init_psd : IsPsd kalman.INIT_P00 0#i128 kalman.INIT_P11 := by
  have h0 : 0 ≤ kalman.INIT_P00.val := by unfold kalman.INIT_P00; decide
  have h1 : 0 ≤ kalman.INIT_P11.val := by unfold kalman.INIT_P11; decide
  have hz : (0#i128).val = 0 := rfl
  refine ⟨h0, h1, ?_⟩
  rw [hz]; nlinarith

@[step]
theorem new_spec (prior : kalman.NoisePrior) (jump_ns : Std.I64) :
    kalman.KalmanFilter.new prior jump_ns ⦃ k =>
      k.anchored = false ∧ IsPsd k.p00 k.p01 k.p11 ⦄ := by
  unfold kalman.KalmanFilter.new
  split <;> (rw [WP.spec_ok]; exact ⟨rfl, init_psd⟩)

@[step]
theorem reset_spec (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.reset k ⦃ k' =>
      k'.anchored = false ∧ IsPsd k'.p00 k'.p01 k'.p11 ⦄ := by
  unfold kalman.KalmanFilter.reset
  rw [WP.spec_ok]
  exact ⟨rfl, init_psd⟩

@[step]
theorem set_prior_total (k : kalman.KalmanFilter) (prior : kalman.NoisePrior) :
    kalman.KalmanFilter.set_prior k prior ⦃ _ => True ⦄ := by
  unfold kalman.KalmanFilter.set_prior; simp

@[step]
theorem is_anchored_total (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.is_anchored k ⦃ b => b = k.anchored ⦄ := by
  unfold kalman.KalmanFilter.is_anchored; simp

@[step]
theorem last_time_ns_total (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.impl.last_time_ns k ⦃ t => t = k.last_time_ns ⦄ := by
  unfold kalman.KalmanFilter.impl.last_time_ns; simp

@[step]
theorem freq_q48_total (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.impl.freq_q48 k ⦃ f => f = k.freq_q48 ⦄ := by
  unfold kalman.KalmanFilter.impl.freq_q48; simp

@[step]
theorem offset_variance_ns2_total (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.offset_variance_ns2 k ⦃ _ => True ⦄ := by
  have hmax0 : 0 ≤ kalman.MAX_P00.val := by unfold kalman.MAX_P00; decide
  unfold kalman.KalmanFilter.offset_variance_ns2
  step with clamp_nonneg_spec k.p00 kalman.MAX_P00 hmax0 as ⟨i⟩
  step*

@[step]
theorem covariance_raw_total (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.covariance_raw k ⦃ r => r = (k.p00, k.p01, k.p11) ⦄ := by
  unfold kalman.KalmanFilter.covariance_raw; simp

/-- Shifting the offset anchor changes only `base_offset_ns` (via saturating
addition) and leaves `theta_q16`, `freq_q48`, covariance, and anchor state
untouched. -/
@[step]
theorem shift_offset_ns_spec (k : kalman.KalmanFilter) (delta_ns : Std.I64) :
    kalman.KalmanFilter.shift_offset_ns k delta_ns ⦃ k' =>
      k'.anchored = k.anchored ∧ k'.last_time_ns = k.last_time_ns
      ∧ k'.theta_q16 = k.theta_q16 ∧ k'.freq_q48 = k.freq_q48
      ∧ k'.p00 = k.p00 ∧ k'.p01 = k.p01 ∧ k'.p11 = k.p11
      ∧ (k.anchored = true → k'.base_offset_ns = core.num.I64.saturating_add k.base_offset_ns delta_ns)
      ∧ (k.anchored = false → k' = k) ⦄ := by
  unfold kalman.KalmanFilter.shift_offset_ns
  cases h : k.anchored <;> simp [lift, h]

@[step]
theorem recenter_spec (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.recenter k ⦃ k' =>
      k'.anchored = k.anchored ∧ k'.last_time_ns = k.last_time_ns
      ∧ k'.freq_q48 = k.freq_q48 ∧ k'.p00 = k.p00 ∧ k'.p01 = k.p01 ∧ k'.p11 = k.p11 ⦄ := by
  unfold kalman.KalmanFilter.recenter
  step as ⟨whole_ns⟩
  have hmag :
      (if whole_ns = core.num.I64.MIN then ok core.num.I64.MAX
       else if whole_ns < 0#i64 then ok (core.num.I64.wrapping_sub 0#i64 whole_ns)
       else ok whole_ns) ⦃ _ => True ⦄ := by
    split
    · simp
    · split <;> simp
  apply WP.spec_bind hmag
  intro mag _
  split
  · step*
  · simp

@[step]
theorem anchor_spec (k : kalman.KalmanFilter) (time_ns offset_ns : Std.I64)
    (variance_ns2 : Std.U64) :
    kalman.KalmanFilter.anchor k time_ns offset_ns variance_ns2 ⦃ k' =>
      k'.anchored = true ∧ IsPsd k'.p00 k'.p01 k'.p11 ⦄ := by
  have hmax0 : 0 ≤ kalman.MAX_P00.val := by unfold kalman.MAX_P00; decide
  have hinit1 : 0 ≤ kalman.INIT_P11.val := by unfold kalman.INIT_P11; decide
  unfold kalman.KalmanFilter.anchor
  step as ⟨i⟩
  step as ⟨i1⟩
  step with clamp_nonneg_spec i1 kalman.MAX_P00 hmax0 as ⟨meas_q16, hm0, _⟩
  split
  · rw [WP.spec_ok]
    refine ⟨rfl, hm0, hinit1, ?_⟩
    have hz : (0#i128).val = 0 := rfl
    rw [hz]; nlinarith
  · rw [WP.spec_ok]
    exact ⟨rfl, init_psd⟩

/-- **Time-update PSD preservation:** `predict` always terminates, preserves
`anchored`, and maintains `IsPsd` whenever `k` already satisfies `IsPsd`. -/
@[step]
theorem predict_psd (k : kalman.KalmanFilter) (dt_ns : Std.I64) :
    kalman.KalmanFilter.predict k dt_ns ⦃ k' =>
      k'.anchored = k.anchored ∧ (IsPsd k.p00 k.p01 k.p11 → IsPsd k'.p00 k'.p01 k'.p11) ⦄ := by
  have hmax0 : 0 ≤ kalman.MAX_P00.val := by unfold kalman.MAX_P00; decide
  have hmax1 : 0 ≤ kalman.MAX_P11.val := by unfold kalman.MAX_P11; decide
  unfold kalman.KalmanFilter.predict
  cases hanch : k.anchored with
  | false => simp [hanch]
  | true =>
    simp only [↓reduceIte]
    split
    · simp [hanch]
    · have hdt : (if dt_ns > kalman.MAX_DT_NS then ok kalman.MAX_DT_NS else ok dt_ns)
          ⦃ _ => True ⦄ := by
        split <;> simp
      apply WP.spec_bind hdt
      intro dt _
      step as ⟨dt128⟩
      step as ⟨i⟩
      step as ⟨i1⟩
      step as ⟨d_theta⟩
      step as ⟨i2⟩
      step as ⟨i3⟩
      step as ⟨i4⟩
      step as ⟨i5⟩
      step with enforce_psd_spec k.p00 k.p01 k.p11 as ⟨p00, p01, p11, _, _, _⟩
      step with clamp_nonneg_spec k.prior.q0_q16_ns2_per_s kalman.MAX_P00 hmax0 as ⟨q0_rate⟩
      step with clamp_nonneg_spec k.prior.q2_q80_per_s kalman.MAX_P11 hmax1 as ⟨q2_rate⟩
      step as ⟨i6⟩
      step as ⟨q11⟩
      step as ⟨q2_dt2⟩
      step as ⟨q01⟩
      step as ⟨i7⟩
      step as ⟨q00_walk⟩
      step as ⟨i8⟩
      step as ⟨q00_white⟩
      step as ⟨p11_dt⟩
      step as ⟨p11_dt2⟩
      step as ⟨p01_dt⟩
      step as ⟨i9⟩
      step as ⟨i10⟩
      step as ⟨i11⟩
      step as ⟨i12⟩
      step as ⟨next_p00⟩
      step as ⟨i13⟩
      step as ⟨next_p01⟩
      step as ⟨next_p11⟩
      step with enforce_psd_spec next_p00 next_p01 next_p11 as ⟨fp00, fp01, fp11, hpsd, _, _⟩
      step with recenter_spec as ⟨k', ha, _, _, hp0, hp01, hp1⟩
      refine ⟨ha, fun _ => ?_⟩
      rw [hp0, hp01, hp1]
      exact hpsd

/-- **Measurement-update PSD preservation:** `update` always terminates, anchors
the filter, and preserves `IsPsd` on every branch (anchor, jump-reanchor,
out-of-order ignore, and Joseph-form covariance update). -/
@[step]
theorem update_psd (k : kalman.KalmanFilter) (meas_time_ns offset_ns : Std.I64)
    (variance_ns2 : Std.U64) :
    kalman.KalmanFilter.update k meas_time_ns offset_ns variance_ns2 ⦃ out =>
      out.2.anchored = true ∧ (IsPsd k.p00 k.p01 k.p11 → IsPsd out.2.p00 out.2.p01 out.2.p11) ⦄ := by
  have hmax0 : 0 ≤ kalman.MAX_P00.val := by unfold kalman.MAX_P00; decide
  have hq32 : 0 ≤ kalman.Q32_ONE.val := by unfold kalman.Q32_ONE; decide
  have hmaxk1 : 0 ≤ kalman.MAX_K1.val := by unfold kalman.MAX_K1; decide
  unfold kalman.KalmanFilter.update
  have hvar : (if variance_ns2 = 0#u64 then ok 1#u64 else ok variance_ns2) ⦃ _ => True ⦄ := by
    split <;> simp
  apply WP.spec_bind hvar
  intro var_ns2 _
  cases hanch : k.anchored with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with anchor_spec k meas_time_ns offset_ns var_ns2 as ⟨k', ha, hpsd⟩
    exact ⟨ha, fun _ => hpsd⟩
  | true =>
    simp only [↓reduceIte]
    split
    · simp [hanch]
    · step as ⟨dt⟩
      step with predict_psd k dt as ⟨k1, ha1, hpsd1⟩
      step as ⟨i⟩
      step as ⟨i1⟩
      step as ⟨rel_ns⟩
      step as ⟨i2⟩
      step as ⟨pred_ns⟩
      step as ⟨innov_whole⟩
      split
      · step as ⟨i3⟩
        step as ⟨i4⟩
        split
        · step with anchor_spec k1 meas_time_ns offset_ns var_ns2 as ⟨k2, ha2, hpsd2⟩
          exact ⟨ha2, fun _ => hpsd2⟩
        · step as ⟨i5⟩
          step as ⟨i6⟩
          step as ⟨innov_q16⟩
          step with enforce_psd_spec k1.p00 k1.p01 k1.p11 as ⟨p00, p01, p11, _, _, _⟩
          step as ⟨i7⟩
          step as ⟨i8⟩
          step with clamp_nonneg_spec i8 kalman.MAX_P00 hmax0 as ⟨meas_q16⟩
          have hmpos : (if meas_q16 <= 0#i128 then ok 1#i128 else ok meas_q16) ⦃ _ => True ⦄ := by
            split <;> simp
          apply WP.spec_bind hmpos
          intro meas_pos _
          step as ⟨innov_var⟩
          step as ⟨i9⟩
          step with clamp_nonneg_spec i9 kalman.Q32_ONE hq32 as ⟨k0⟩
          step as ⟨i10⟩
          step with clamp_sym_spec i10 kalman.MAX_K1 hmaxk1 as ⟨k1_g⟩
          step*
          simp_all
      · step as ⟨i5⟩
        step as ⟨i6⟩
        step as ⟨innov_q16⟩
        step with enforce_psd_spec k1.p00 k1.p01 k1.p11 as ⟨p00, p01, p11, _, _, _⟩
        step as ⟨i7⟩
        step as ⟨i8⟩
        step with clamp_nonneg_spec i8 kalman.MAX_P00 hmax0 as ⟨meas_q16⟩
        have hmpos : (if meas_q16 <= 0#i128 then ok 1#i128 else ok meas_q16) ⦃ _ => True ⦄ := by
          split <;> simp
        apply WP.spec_bind hmpos
        intro meas_pos _
        step as ⟨innov_var⟩
        step as ⟨i9⟩
        step with clamp_nonneg_spec i9 kalman.Q32_ONE hq32 as ⟨k0⟩
        step as ⟨i10⟩
        step with clamp_sym_spec i10 kalman.MAX_K1 hmaxk1 as ⟨k1_g⟩
        step*
        simp_all

@[step]
theorem predict_offset_ns_total (k : kalman.KalmanFilter) (time_ns : Std.I64) :
    kalman.KalmanFilter.predict_offset_ns k time_ns ⦃ _ => True ⦄ := by
  unfold kalman.KalmanFilter.predict_offset_ns
  split
  · step*
  · simp

/-- `to_line` returns `none` when unanchored, and `some line` with
`line.run = LINE_RUN = 2^48 > 0`, `line.time = k.last_time_ns`, and
`line.rise = k.freq_q48` when anchored. -/
@[step]
theorem to_line_spec (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.to_line k ⦃ o =>
      (k.anchored = false → o = none)
      ∧ (k.anchored = true → ∃ l, o = some l
          ∧ l.run = kalman.LINE_RUN ∧ 0 < l.run.val
          ∧ l.time = k.last_time_ns ∧ l.rise = k.freq_q48) ⦄ := by
  have hrun_pos : 0 < kalman.LINE_RUN.val := by unfold kalman.LINE_RUN; decide
  unfold kalman.KalmanFilter.to_line
  cases h : k.anchored with
  | false => simp
  | true =>
    simp only [↓reduceIte]
    step as ⟨i⟩
    step as ⟨whole_ns⟩
    step as ⟨i1⟩
    step as ⟨i2⟩
    step as ⟨val⟩
    exact ⟨fun hc => (by cases hc), _, rfl, rfl, hrun_pos, rfl, rfl⟩

/-! ## Zero-innovation fixed point (used for exact zero-cost playback under `IdealConstantWorld`) -/

private theorem i128_wrapping_shr_zero (s : Std.U32) :
    core.num.I128.wrapping_shr 0#i128 s = 0#i128 := by
  apply IScalar.eq_of_val_eq
  simp only [IScalar.val, core.num.I128.wrapping_shr_bv_eq]
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  have h0 : (0#i128 : Std.I128).bv.toInt = 0 := rfl
  rw [h0, Int.zero_ediv]

private theorem ite_t {α : Type _} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp only [h, ↓reduceIte]

private theorem ite_f {α : Type _} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp only [h, ↓reduceIte]

private theorem mul_shr_safe_zero_right (a : Std.I128) (shift : Std.U32) :
    kalman.mul_shr_safe a 0#i128 shift ⦃ r => r = 0#i128 ⦄ := by
  unfold kalman.mul_shr_safe
  have hs : (if shift > 64#u32 then ok 64#u32 else ok shift) ⦃ _ => True ⦄ := by
    split <;> simp
  apply WP.spec_bind hs
  intro s _
  have hcm := I128.checked_mul_bv_spec a 0#i128
  have h0 : (0#i128 : Std.I128).val = 0 := rfl
  have hcm_eq : I128.checked_mul a 0#i128 = some 0#i128 := by
    rw [I128.checked_mul_eq]
    cases h : core.num.checked_mul_IScalar a 0#i128 with
    | none =>
      rw [h] at hcm
      exfalso; apply hcm
      rw [h0, mul_zero]
      simp only [I128.min, I128.max, I128.numBits]
      exact ⟨by decide, by decide⟩
    | some z =>
      rw [h] at hcm
      congr 1; apply IScalar.eq_of_val_eq
      rw [hcm.2.2.1, h0, mul_zero]
  rw [show lift (I128.checked_mul a 0#i128) = ok (some 0#i128) from congrArg ok hcm_eq, bind_ok]
  rw [WP.spec_ok]
  exact i128_wrapping_shr_zero s

private theorem abs_i128_zero : kalman.abs_i128 0#i128 ⦃ r => r = 0#i128 ⦄ := by
  unfold kalman.abs_i128
  have hnotlt : ¬ (0#i128 < 0#i128) := by decide
  have hnotmin : ¬ (0#i128 = core.num.I128.MIN) := by decide
  rw [ite_f hnotlt, ite_f hnotmin, WP.spec_ok]

private theorem clamp_sym_i64_zero (hi : Std.I64) (hhi : 0 ≤ hi.val) (hhi_lt : hi.val < 2^63) :
    kalman.clamp_sym_i64 0#i64 hi ⦃ r => r = 0#i64 ⦄ := by
  unfold kalman.clamp_sym_i64
  have h0 : (0#i64 : Std.I64).val = 0 := rfl
  have hlo : (core.num.I64.wrapping_sub 0#i64 hi).val = -hi.val := by
    rw [I64.wrapping_sub_val 0#i64 hi ⟨by rw [h0]; omega, by rw [h0]; omega⟩, h0]; omega
  step as ⟨lo, hlo_eq⟩
  have hlov : lo.val = -hi.val := by rw [hlo_eq, hlo]
  split
  · rename_i hgt; exfalso; have : hi.val < (0#i64 : Std.I64).val := hgt; omega
  · split
    · rename_i hlt; exfalso; have : (0#i64 : Std.I64).val < lo.val := hlt; omega
    · simp

private theorem recenter_zero (k : kalman.KalmanFilter) (ht : k.theta_q16 = 0#i64) :
    kalman.KalmanFilter.recenter k ⦃ k' => k' = k ⦄ := by
  unfold kalman.KalmanFilter.recenter
  rw [ht]
  have hshr0 : core.num.I64.wrapping_shr 0#i64 16#u32 = 0#i64 := by
    apply IScalar.eq_of_val_eq
    simp only [IScalar.val, core.num.I64.wrapping_shr_bv_eq]
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    have h0 : (0#i64 : Std.I64).bv.toInt = 0 := rfl
    rw [h0, Int.zero_ediv]
  simp only [lift, bind_ok, hshr0]
  have h1 : ¬ (0#i64 = core.num.I64.MIN) := by decide
  have h2 : ¬ (0#i64 < 0#i64) := by decide
  have h3 : ¬ (0#i64 > 1000000000#i64) := by decide
  simp only [h1, h2, h3, ↓reduceIte, bind_ok, WP.spec_ok]

/-- **Prediction fixed point at zero frequency and zero residual:** if `k` is
anchored with `theta_q16 = 0` and `freq_q48 = 0`, `predict k dt_ns` preserves
`base_offset_ns`, `theta_q16 = 0`, `freq_q48 = 0`, `anchored = true`, and `IsPsd`. -/
theorem predict_zero_fixed_point (k : kalman.KalmanFilter) (dt_ns : Std.I64)
    (hanch : k.anchored = true) (ht : k.theta_q16 = 0#i64) (hf : k.freq_q48 = 0#i64)
    (hpsd : IsPsd k.p00 k.p01 k.p11) :
    kalman.KalmanFilter.predict k dt_ns ⦃ k' =>
      k'.anchored = true ∧ k'.base_offset_ns = k.base_offset_ns
      ∧ k'.theta_q16 = 0#i64 ∧ k'.freq_q48 = 0#i64
      ∧ IsPsd k'.p00 k'.p01 k'.p11 ⦄ := by
  have hmax0 : 0 ≤ kalman.MAX_P00.val := by unfold kalman.MAX_P00; decide
  have hmax1 : 0 ≤ kalman.MAX_P11.val := by unfold kalman.MAX_P11; decide
  unfold kalman.KalmanFilter.predict
  simp only [hanch, ↓reduceIte]
  split
  · rw [WP.spec_ok]; exact ⟨hanch, rfl, ht, hf, hpsd⟩
  · have hdt : (if dt_ns > kalman.MAX_DT_NS then ok kalman.MAX_DT_NS else ok dt_ns) ⦃ _ => True ⦄ := by
      split <;> simp
    apply WP.spec_bind hdt; intro dt _
    step as ⟨dt128⟩
    step as ⟨i, hi⟩
    have hi0 : i = 0#i128 := by
      rw [hi, hf]; apply IScalar.eq_of_val_eq; exact I64.cast_I128_val 0#i64
    subst hi0
    step as ⟨i1, hi1⟩
    have hi10 : i1 = 0#i128 := by
      rw [hi1]; apply IScalar.eq_of_val_eq
      rw [I128.wrapping_mul_val 0#i128 dt128 ⟨by simp, by simp⟩]; simp
    subst hi10
    step as ⟨d_theta, hd_theta⟩
    have hd_theta0 : d_theta = 0#i128 := by rw [hd_theta]; exact i128_wrapping_shr_zero 32#u32
    subst hd_theta0
    step as ⟨i2, hi2⟩
    have hi20 : i2 = 0#i128 := by
      rw [hi2, ht]; apply IScalar.eq_of_val_eq; exact I64.cast_I128_val 0#i64
    subst hi20
    step as ⟨i3, hi3⟩
    have hi30 : i3 = 0#i128 := by
      rw [hi3]; apply IScalar.eq_of_val_eq
      rw [I128.wrapping_add_val 0#i128 0#i128 ⟨by simp, by simp⟩]; simp
    subst hi30
    step with Fixed.saturate_spec 0#i128 as ⟨i4, hi4⟩
    have hi40 : i4 = 0#i64 := by apply IScalar.eq_of_val_eq; rw [hi4, Fixed.clamp64]; simp
    subst hi40
    step as ⟨i5⟩
    step with enforce_psd_spec k.p00 k.p01 k.p11 as ⟨p00, p01, p11, _, _, _⟩
    step with clamp_nonneg_spec k.prior.q0_q16_ns2_per_s kalman.MAX_P00 hmax0 as ⟨q0_rate⟩
    step with clamp_nonneg_spec k.prior.q2_q80_per_s kalman.MAX_P11 hmax1 as ⟨q2_rate⟩
    step as ⟨i6⟩; step as ⟨q11⟩; step as ⟨q2_dt2⟩; step as ⟨q01⟩
    step as ⟨i7⟩; step as ⟨q00_walk⟩; step as ⟨i8⟩; step as ⟨q00_white⟩
    step as ⟨p11_dt⟩; step as ⟨p11_dt2⟩; step as ⟨p01_dt⟩
    step as ⟨i9⟩; step as ⟨i10⟩; step as ⟨i11⟩; step as ⟨i12⟩; step as ⟨next_p00⟩
    step as ⟨i13⟩; step as ⟨next_p01⟩; step as ⟨next_p11⟩
    step with enforce_psd_spec next_p00 next_p01 next_p11 as ⟨fp00, fp01, fp11, hpsd', _, _⟩
    step with recenter_zero
      { k with anchored := true, last_time_ns := i5, theta_q16 := 0#i64, p00 := fp00, p01 := fp01, p11 := fp11 } rfl
      as ⟨k', hk'⟩
    rw [hk']
    exact ⟨rfl, rfl, rfl, hf, hpsd'⟩

/-- **Zero-innovation fixed point of `KalmanFilter.update`:** if `k` is anchored
at `base_offset_ns = offset` with `theta_q16 = 0` and `freq_q48 = 0`, then
feeding the exact same `offset` at any `meas_time_ns` and any `variance_ns2`
keeps `base_offset_ns = offset`, `theta_q16 = 0`, `freq_q48 = 0`, `anchored = true`,
and `IsPsd`. -/
theorem update_zero_innovation_fixed_point (k : kalman.KalmanFilter)
    (meas_time_ns : Std.I64) (variance_ns2 : Std.U64)
    (hanch : k.anchored = true) (ht : k.theta_q16 = 0#i64) (hf : k.freq_q48 = 0#i64)
    (hpsd : IsPsd k.p00 k.p01 k.p11) :
    kalman.KalmanFilter.update k meas_time_ns k.base_offset_ns variance_ns2 ⦃ out =>
      out.2.anchored = true ∧ out.2.base_offset_ns = k.base_offset_ns
      ∧ out.2.theta_q16 = 0#i64 ∧ out.2.freq_q48 = 0#i64
      ∧ IsPsd out.2.p00 out.2.p01 out.2.p11 ⦄ := by
  have hmax0 : 0 ≤ kalman.MAX_P00.val := by unfold kalman.MAX_P00; decide
  have hq32 : 0 ≤ kalman.Q32_ONE.val := by unfold kalman.Q32_ONE; decide
  have hmaxk1 : 0 ≤ kalman.MAX_K1.val := by unfold kalman.MAX_K1; decide
  have hmaxf_nn : 0 ≤ kalman.MAX_FREQ_Q48.val := by unfold kalman.MAX_FREQ_Q48; decide
  have hmaxf_lt : kalman.MAX_FREQ_Q48.val < 2^63 := by unfold kalman.MAX_FREQ_Q48; decide
  unfold kalman.KalmanFilter.update
  have hvar : (if variance_ns2 = 0#u64 then ok 1#u64 else ok variance_ns2) ⦃ _ => True ⦄ := by
    split <;> simp
  apply WP.spec_bind hvar; intro var_ns2 _
  simp only [hanch, ↓reduceIte]
  split
  · rw [WP.spec_ok]; exact ⟨hanch, rfl, ht, hf, hpsd⟩
  · step as ⟨dt⟩
    step with predict_zero_fixed_point k dt hanch ht hf hpsd
      as ⟨k1, ha1, hbase1, ht1, hf1, hpsd1⟩
    step as ⟨i, hi⟩; step as ⟨i1, hi1⟩
    step as ⟨rel_ns, hrel⟩
    have hrel0 : rel_ns = 0#i128 := by
      rw [hrel, hi, hi1, hbase1]
      apply IScalar.eq_of_val_eq
      have h0 : (0#i128 : Std.I128).val = 0 := rfl
      rw [I128.wrapping_sub_val _ _ ⟨by omega, by omega⟩, h0]; omega
    subst hrel0
    step as ⟨i2, hi2⟩
    have hi20 : i2 = 0#i128 := by
      rw [hi2, ht1]; apply IScalar.eq_of_val_eq; exact I64.cast_I128_val 0#i64
    subst hi20
    step with Fixed.div_floor_wide_spec 0#i128 65536#i128 as ⟨pred_ns, hpred_pos, _⟩
    have hpred0 : pred_ns = 0#i128 := by
      apply IScalar.eq_of_val_eq; rw [hpred_pos (by decide)]; rfl
    subst hpred0
    step as ⟨innov_whole, hinnov_w⟩
    have hinnov_w0 : innov_whole = 0#i128 := by
      rw [hinnov_w]; apply IScalar.eq_of_val_eq
      rw [I128.wrapping_sub_val 0#i128 0#i128 ⟨by simp, by simp⟩]; simp
    subst hinnov_w0
    -- Common update tail when `rel_ns = 0`, `k1.theta_q16 = 0`, `k1.freq_q48 = 0`.
    have htail :
        (do
          let i5 ← fixed.saturating_mul_i128 0#i128 65536#i128
          let i6 ← lift (IScalar.cast .I128 k1.theta_q16)
          let innov_q16 ← lift (core.num.I128.saturating_sub i5 i6)
          let (p00, p01, p11) ← kalman.enforce_psd k1.p00 k1.p01 k1.p11
          let i7 ← lift (UScalar.hcast .I128 var_ns2)
          let i8 ← lift (core.num.I128.wrapping_shl i7 16#u32)
          let meas_q16 ← kalman.clamp_nonneg i8 kalman.MAX_P00
          let meas_pos ← if meas_q16 <= 0#i128 then ok 1#i128 else ok meas_q16
          let innov_var ← lift (core.num.I128.saturating_add p00 meas_pos)
          let i9 ← fixed.scale_div_pow2 p00 32#u32 innov_var
          let k0 ← kalman.clamp_nonneg i9 kalman.Q32_ONE
          let i10 ← fixed.scale_div_pow2 p01 32#u32 innov_var
          let k1_g ← kalman.clamp_sym i10 kalman.MAX_K1
          let d_theta ← kalman.mul_shr_safe k0 innov_q16 32#u32
          let d_freq ← kalman.mul_shr_safe k1_g innov_q16 32#u32
          let i11 ← lift (IScalar.cast .I128 k1.theta_q16)
          let i12 ← lift (core.num.I128.saturating_add i11 d_theta)
          let i13 ← fixed.saturate i12
          let i14 ← lift (IScalar.cast .I128 k1.freq_q48)
          let i15 ← lift (core.num.I128.saturating_add i14 d_freq)
          let i16 ← fixed.saturate i15
          let i17 ← kalman.clamp_sym_i64 i16 kalman.MAX_FREQ_Q48
          let one_m_k0 ← lift (core.num.I128.wrapping_sub kalman.Q32_ONE k0)
          let a2 ← kalman.mul_shr_safe one_m_k0 one_m_k0 32#u32
          let k02 ← kalman.mul_shr_safe k0 k0 32#u32
          let i18 ← kalman.mul_shr_safe a2 p00 32#u32
          let i19 ← kalman.mul_shr_safe k02 meas_pos 32#u32
          let next_p00 ← lift (core.num.I128.saturating_add i18 i19)
          let k1_p00 ← kalman.mul_shr_safe k1_g p00 32#u32
          let k1_meas ← kalman.mul_shr_safe k1_g meas_pos 32#u32
          let i20 ← lift (core.num.I128.saturating_sub p01 k1_p00)
          let i21 ← kalman.mul_shr_safe one_m_k0 i20 32#u32
          let i22 ← kalman.mul_shr_safe k0 k1_meas 32#u32
          let next_p01 ← lift (core.num.I128.saturating_add i21 i22)
          let k1_p01 ← kalman.mul_shr_safe k1_g p01 32#u32
          let k1sq_p00 ← kalman.mul_shr_safe k1_g k1_p00 32#u32
          let k1sq_meas ← kalman.mul_shr_safe k1_g k1_meas 32#u32
          let i23 ← fixed.saturating_mul_i128 k1_p01 2#i128
          let i24 ← lift (core.num.I128.saturating_sub p11 i23)
          let i25 ← lift (core.num.I128.saturating_add i24 k1sq_p00)
          let next_p11 ← lift (core.num.I128.saturating_add i25 k1sq_meas)
          let (fp00, fp01, fp11) ← kalman.enforce_psd next_p00 next_p01 next_p11
          let self2 ← kalman.KalmanFilter.recenter
            { k1 with theta_q16 := i13, freq_q48 := i17, p00 := fp00, p01 := fp01, p11 := fp11 }
          ok (true, self2))
        ⦃ out =>
          out.2.anchored = true ∧ out.2.base_offset_ns = k.base_offset_ns
          ∧ out.2.theta_q16 = 0#i64 ∧ out.2.freq_q48 = 0#i64
          ∧ IsPsd out.2.p00 out.2.p01 out.2.p11 ⦄ := by
      step with Fixed.saturating_mul_i128_spec 0#i128 65536#i128 as ⟨i5, hi5⟩
      have hi50 : i5 = 0#i128 := by apply IScalar.eq_of_val_eq; rw [hi5]; simp [Fixed.clamp128]
      subst hi50
      step as ⟨i6, hi6⟩
      have hi60 : i6 = 0#i128 := by
        rw [hi6, ht1]; apply IScalar.eq_of_val_eq; exact I64.cast_I128_val 0#i64
      subst hi60
      step as ⟨iq, hiq⟩
      have hiq0 : iq = 0#i128 := by
        rw [hiq]; apply IScalar.eq_of_val_eq
        rw [I128.saturating_sub_val]; change max (-2^127) (min (2^127 - 1) ((0 : ℤ) - 0)) = 0; omega
      subst hiq0
      step with enforce_psd_spec k1.p00 k1.p01 k1.p11 as ⟨p00, p01, p11, _, _, _⟩
      step as ⟨i7⟩; step as ⟨i8⟩
      step with clamp_nonneg_spec i8 kalman.MAX_P00 hmax0 as ⟨meas_q16⟩
      have hmpos : (if meas_q16 <= 0#i128 then ok 1#i128 else ok meas_q16) ⦃ _ => True ⦄ := by
        split <;> simp
      apply WP.spec_bind hmpos; intro meas_pos _
      step as ⟨innov_var⟩; step as ⟨i9⟩
      step with clamp_nonneg_spec i9 kalman.Q32_ONE hq32 as ⟨k0⟩
      step as ⟨i10⟩
      step with clamp_sym_spec i10 kalman.MAX_K1 hmaxk1 as ⟨k1_g⟩
      step with mul_shr_safe_zero_right k0 32#u32 as ⟨dt_u, hdt_u⟩; subst hdt_u
      step with mul_shr_safe_zero_right k1_g 32#u32 as ⟨df_u, hdf_u⟩; subst hdf_u
      step as ⟨i11, hi11⟩
      have hi110 : i11 = 0#i128 := by
        rw [hi11, ht1]; apply IScalar.eq_of_val_eq; exact I64.cast_I128_val 0#i64
      subst hi110
      step as ⟨i12, hi12⟩
      have hi120 : i12 = 0#i128 := by
        rw [hi12]; apply IScalar.eq_of_val_eq
        rw [I128.saturating_add_val]; change max (-2^127) (min (2^127 - 1) ((0 : ℤ) + 0)) = 0; omega
      subst hi120
      step with Fixed.saturate_spec 0#i128 as ⟨i13, hi13⟩
      have hi130 : i13 = 0#i64 := by apply IScalar.eq_of_val_eq; rw [hi13, Fixed.clamp64]; simp
      subst hi130
      step as ⟨i14, hi14⟩
      have hi140 : i14 = 0#i128 := by
        rw [hi14, hf1]; apply IScalar.eq_of_val_eq; exact I64.cast_I128_val 0#i64
      subst hi140
      step as ⟨i15, hi15⟩
      have hi150 : i15 = 0#i128 := by
        rw [hi15]; apply IScalar.eq_of_val_eq
        rw [I128.saturating_add_val]; change max (-2^127) (min (2^127 - 1) ((0 : ℤ) + 0)) = 0; omega
      subst hi150
      step with Fixed.saturate_spec 0#i128 as ⟨i16, hi16⟩
      have hi160 : i16 = 0#i64 := by apply IScalar.eq_of_val_eq; rw [hi16, Fixed.clamp64]; simp
      subst hi160
      step with clamp_sym_i64_zero kalman.MAX_FREQ_Q48 hmaxf_nn hmaxf_lt as ⟨i17, hi17⟩
      subst hi17
      step as ⟨one_m_k0⟩; step as ⟨a2⟩; step as ⟨k02⟩; step as ⟨i18⟩; step as ⟨i19⟩; step as ⟨next_p00⟩
      step as ⟨k1_p00⟩; step as ⟨k1_meas⟩; step as ⟨i20⟩; step as ⟨i21⟩; step as ⟨i22⟩; step as ⟨next_p01⟩
      step as ⟨k1_p01⟩; step as ⟨k1sq_p00⟩; step as ⟨k1sq_meas⟩; step as ⟨i23⟩; step as ⟨i24⟩
      step as ⟨i25⟩; step as ⟨next_p11⟩
      step with enforce_psd_spec next_p00 next_p01 next_p11 as ⟨fp00, fp01, fp11, hpsd', _, _⟩
      step with recenter_zero
        { k1 with theta_q16 := 0#i64, freq_q48 := 0#i64, p00 := fp00, p01 := fp01, p11 := fp11 } rfl
        as ⟨self2, hself2⟩
      rw [hself2]
      exact ⟨ha1, hbase1, rfl, rfl, hpsd'⟩
    split
    · rename_i hjp
      step with abs_i128_zero as ⟨i3, hi3⟩; subst hi3
      step as ⟨i4, hi4⟩
      have hnotgt : ¬ (0#i128 > i4) := by
        have h1 : (0#i64 : Std.I64).val < k1.jump_ns.val := hjp
        have h0_64 : (0#i64 : Std.I64).val = 0 := rfl
        have h2 : i4.val = k1.jump_ns.val := by rw [hi4, I64.cast_I128_val]
        have h0 : (0#i128 : Std.I128).val = 0 := rfl
        intro hgt; have : i4.val < (0#i128 : Std.I128).val := hgt; omega
      rw [ite_f hnotgt]
      exact htail
    · exact htail

/-- On a zero-residual, zero-frequency anchored filter, `to_line` exports the
exact constant line `value = base_offset_ns`, `rise = 0`, `run = LINE_RUN`. -/
theorem to_line_zero_fixed_point (k : kalman.KalmanFilter)
    (hanch : k.anchored = true) (ht : k.theta_q16 = 0#i64) (hf : k.freq_q48 = 0#i64) :
    kalman.KalmanFilter.to_line k ⦃ o =>
      o = some { time := k.last_time_ns, value := k.base_offset_ns,
                 rise := 0#i64, run := kalman.LINE_RUN } ⦄ := by
  unfold kalman.KalmanFilter.to_line
  simp only [hanch, ↓reduceIte]
  step as ⟨i, hi⟩
  have hi0 : i = 0#i128 := by rw [hi, ht]; apply IScalar.eq_of_val_eq; exact I64.cast_I128_val 0#i64
  subst hi0
  step with Fixed.div_floor_wide_spec 0#i128 65536#i128 as ⟨w, hw, _⟩
  have hw0 : w = 0#i128 := by apply IScalar.eq_of_val_eq; rw [hw (by decide)]; rfl
  subst hw0
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hbounds : -2^63 ≤ k.base_offset_ns.val ∧ k.base_offset_ns.val ≤ 2^63 - 1 := by
    have hb := k.base_offset_ns.hBounds
    change -2^63 ≤ k.base_offset_ns.val ∧ k.base_offset_ns.val < 2^63 at hb
    omega
  have hi2_eq : i2 = IScalar.cast .I128 k.base_offset_ns := by
    rw [hi2, hi1]; apply IScalar.eq_of_val_eq
    have hc : (IScalar.cast .I128 k.base_offset_ns).val = k.base_offset_ns.val := I64.cast_I128_val _
    rw [I128.saturating_add_val, hc]
    change max (-2^127) (min (2^127 - 1) (k.base_offset_ns.val + 0)) = k.base_offset_ns.val; omega
  clear hi2; subst hi2_eq
  step with Fixed.saturate_spec (IScalar.cast .I128 k.base_offset_ns) as ⟨val, hval⟩
  have hval_eq : val = k.base_offset_ns := by
    apply IScalar.eq_of_val_eq
    have hc : (IScalar.cast .I128 k.base_offset_ns).val = k.base_offset_ns.val := I64.cast_I128_val _
    rw [hval, hc, Fixed.clamp64]; omega
  rw [hval_eq, hf]

end Unisono.Kalman
