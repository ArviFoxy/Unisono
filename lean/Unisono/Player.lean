/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed
public import Unisono.Relation

/-!
# Timing and the regulator

The functions of `unisono_core::timing` and `unisono_core::player` return for
every argument and every state: no reading of a clock, no schedule and no
state of the regulator makes the planning of a cycle fail.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Player

attribute [step] Unisono.Relation.saturate_total Unisono.Relation.eval_total

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

@[step]
theorem sender_time_total (line : relation.Line) (path time : Std.I64) :
    timing.sender_time line path time ⦃ _ => True ⦄ := by
  unfold timing.sender_time
  run

@[step]
theorem due_total (schedule : timing.Schedule) (time : Std.I64) :
    timing.due schedule time ⦃ _ => True ⦄ := by
  unfold timing.due
  run

@[step]
theorem continues_total (a b : timing.Schedule) :
    timing.Schedule.continues a b ⦃ _ => True ⦄ := by
  unfold timing.Schedule.continues
  run

@[step]
theorem distance_total (a b : timing.Position) : timing.distance a b ⦃ _ => True ⦄ := by
  unfold timing.distance
  run

@[step]
theorem advance_total (start : timing.Position) (frames : Std.U32) (step : Std.I64) :
    timing.advance start frames step ⦃ _ => True ⦄ := by
  unfold timing.advance
  run

/-- The gain of a cycle of `duration` nanoseconds, in units of `2⁻³²`: the
gain per second, which the settings give in units of `2⁻¹⁶`, times the length
of the cycle, which counts as at most `2⁴⁰` nanoseconds and as zero when it is
negative; rounded down, and at most one. -/
def cycleGain (p : player.Player) (duration : ℤ) : ℤ :=
  min (2 ^ 32) (p.regulation.gain.val * max 0 (min duration (2 ^ 40)) * 2 ^ 16 / 10 ^ 9)

theorem cycleGain_bounds (p : player.Player) (duration : ℤ) :
    0 ≤ cycleGain p duration ∧ cycleGain p duration ≤ 2 ^ 32 := by
  unfold cycleGain
  have hgain : (0 : ℤ) ≤ p.regulation.gain.val := by positivity
  have hspan : (0 : ℤ) ≤ max 0 (min duration (2 ^ 40)) := le_max_left _ _
  have hquot : (0 : ℤ) ≤ p.regulation.gain.val * max 0 (min duration (2 ^ 40)) * 2 ^ 16 / 10 ^ 9 :=
    Int.ediv_nonneg (by positivity) (by norm_num)
  exact ⟨le_min (by norm_num) hquot, min_le_left _ _⟩

/-- The gain that the code computes for a cycle. -/
@[step]
theorem gain_spec (p : player.Player) (duration : Std.I64) :
    player.Player.gain p duration ⦃ r => r.val = cycleGain p duration.val ⦄ := by
  unfold player.Player.gain
  have hbillion : player.BILLION.val = 10 ^ 9 := by simp [player.BILLION]
  have hlongest : player.LONGEST_CYCLE.val = 2 ^ 40 := by simp [player.LONGEST_CYCLE]
  have hlargest : player.LARGEST_GAIN.val = 2 ^ 32 := by simp [player.LARGEST_GAIN]
  apply WP.spec_bind
    (Pₘ := fun span : Std.I64 => span.val = max 0 (min duration.val (2 ^ 40)))
  · split
    · rename_i hneg
      have : duration.val < 0 := by scalar_tac
      rw [WP.spec_ok]
      have h0 : (0#i64).val = 0 := rfl
      rw [h0]
      omega
    · rename_i hneg
      have hd0 : 0 ≤ duration.val := by scalar_tac
      split
      · rename_i hlong
        have : 2 ^ 40 < duration.val := by rw [← hlongest]; scalar_tac
        rw [WP.spec_ok, hlongest]
        omega
      · rename_i hlong
        have : duration.val ≤ 2 ^ 40 := by rw [← hlongest]; scalar_tac
        rw [WP.spec_ok]
        omega
  · intro span hspan
    have hspan0 : 0 ≤ span.val := by rw [hspan]; exact le_max_left _ _
    have hspan1 : span.val ≤ 2 ^ 40 := by rw [hspan]; omega
    have hgain0 : (0 : ℤ) ≤ p.regulation.gain.val := by positivity
    have hgain1 : (p.regulation.gain.val : ℤ) ≤ 2 ^ 32 := by scalar_tac
    have hprod0 : 0 ≤ (p.regulation.gain.val : ℤ) * span.val := mul_nonneg hgain0 hspan0
    have hprod1 : (p.regulation.gain.val : ℤ) * span.val ≤ 2 ^ 32 * 2 ^ 40 :=
      mul_le_mul hgain1 hspan1 hspan0 (by norm_num)
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨scaled, hscaled⟩
    have hiv : i.val = p.regulation.gain.val := by rw [hi, U32.hcast_I128_val]
    have hi1v : i1.val = span.val := by rw [hi1, I64.cast_I128_val]
    have hi2v : i2.val = p.regulation.gain.val * span.val := by
      rw [hi2, I128.wrapping_mul_val _ _ (by rw [hiv, hi1v]; constructor <;> linarith), hiv, hi1v]
    have hsixteen : (16#u32).val = 16 := rfl
    have hscaledv : scaled.val = p.regulation.gain.val * span.val * 2 ^ 16 := by
      rw [hscaled, I128.wrapping_shl_val _ _ (by rw [hsixteen]; norm_num)
        (by rw [hsixteen, hi2v]; constructor <;> linarith), hsixteen, hi2v]
    step as ⟨gain, hgain, hzero⟩
    have hgainv : gain.val = p.regulation.gain.val * span.val * 2 ^ 16 / 10 ^ 9 := by
      rw [hgain (by rw [hbillion]; norm_num), hscaledv, hbillion]
    unfold cycleGain
    rw [← hspan, ← hgainv]
    split
    · rename_i hgt
      have : 2 ^ 32 < gain.val := by rw [← hlargest]; scalar_tac
      rw [WP.spec_ok, hlargest]
      omega
    · rename_i hgt
      have : gain.val ≤ 2 ^ 32 := by rw [← hlargest]; scalar_tac
      rw [WP.spec_ok]
      omega

@[step]
theorem gains_total (p : player.Player) (duration : Std.I64) :
    player.Player.gains p duration ⦃ _ => True ⦄ := by
  unfold player.Player.gains
  run

@[step]
theorem ahead_total (p : player.Player) (frames : Std.U32) (scheduled : Std.I64)
    (slope : Std.I32) : player.Player.ahead p frames scheduled slope ⦃ _ => True ⦄ := by
  unfold player.Player.ahead
  run

@[step]
theorem regulate_total (p : player.Player) (behind ahead duration : Std.I64) :
    player.Player.regulate p behind ahead duration ⦃ _ => True ⦄ := by
  unfold player.Player.regulate
  run

/-- The largest step that a regulator takes either way, in units of 2^-64
frame for each output frame: its limit of the pace, which counts as three in a
thousand when it is set higher. -/
def reach (p : player.Player) : ℤ := (min p.regulation.limit.val 3000000 : ℕ) * 2^64 / 10^9

theorem reach_bounds (p : player.Player) : 0 ≤ reach p ∧ reach p ≤ 55340232221128654 := by
  unfold reach
  have h : (min p.regulation.limit.val 3000000 : ℕ) ≤ 3000000 := Nat.min_le_right _ _
  constructor
  · positivity
  · omega

@[step]
theorem reach_spec (p : player.Player) :
    player.Player.reach p ⦃ r => r.val = reach p ⦄ := by
  unfold player.Player.reach
  have hbillion : player.BILLION.val = 10^9 := by simp [player.BILLION]
  have hframe : player.FRAME.val = 2^64 := by simp [player.FRAME]
  have hlargest : player.LARGEST_LIMIT.val = 3000000 := by simp [player.LARGEST_LIMIT]
  split
  · rename_i hgt
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    have hiv : i.val = 3000000 := by rw [hi, U32.hcast_I128_val, hlargest]; rfl
    have hi1v : i1.val = 3000000 * 2^64 := by
      rw [hi1, I128.wrapping_mul_val _ _ (by rw [hiv, hframe]; norm_num), hiv, hframe]
    step as ⟨r, hr, hzero⟩
    rw [hr (by rw [hbillion]; norm_num), hi1v, hbillion]
    unfold reach
    have : min p.regulation.limit.val 3000000 = 3000000 := by scalar_tac
    rw [this]
    norm_num
  · rename_i hle
    simp only [bind_ok]
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    have hlim : p.regulation.limit.val ≤ 3000000 := by scalar_tac
    have hiv : i.val = p.regulation.limit.val := by rw [hi, U32.hcast_I128_val]
    have hi1v : i1.val = p.regulation.limit.val * 2^64 := by
      rw [hi1, I128.wrapping_mul_val _ _ (by rw [hiv, hframe]; omega), hiv, hframe]
    step as ⟨r, hr, hzero⟩
    rw [hr (by rw [hbillion]; norm_num), hi1v, hbillion]
    unfold reach
    have : min p.regulation.limit.val 3000000 = p.regulation.limit.val := by omega
    rw [this]

/-- Clamping a step offset brings it within `±2^56` units of `2^-64` frame. -/
@[step]
theorem step_clamped_spec (offset : Std.I64) :
    timing.Step.clamped offset ⦃ s =>
      s.offset.val = max (-2^56) (min offset.val (2^56))
      ∧ -2^56 ≤ s.offset.val ∧ s.offset.val ≤ 2^56 ⦄ := by
  unfold timing.Step.clamped
  have hl : timing.Step.LARGEST_OFFSET.val = 2^56 := by simp [timing.Step.LARGEST_OFFSET]
  have h0 : (0#i64).val = 0 := by rfl
  step as ⟨low, hlow⟩
  have hlowv : low.val = -(2^56) := by
    rw [hlow, I64.wrapping_sub_val _ _ (by rw [h0, hl]; norm_num), h0, hl]
    norm_num
  split
  · have hgt : 2^56 < offset.val := by rw [← hl]; scalar_tac
    simp only [WP.spec_ok, hl]
    omega
  · have hle : offset.val ≤ 2^56 := by rw [← hl]; scalar_tac
    split
    · have hlt : offset.val < -(2^56) := by rw [← hlowv]; scalar_tac
      simp only [WP.spec_ok, hlowv]
      omega
    · have hge : -(2^56) ≤ offset.val := by rw [← hlowv]; scalar_tac
      simp only [WP.spec_ok]
      omega

@[step]
theorem step_offset_spec (s : timing.Step) :
    timing.Step.impl.offset s ⦃ r => r = s.offset ⦄ := by
  unfold timing.Step.impl.offset
  simp

/-- The step of a cycle is within the limit of the pace, whatever the state
of the regulator, the schedule and the correction that was wanted. -/
@[step]
theorem step_spec (p : player.Player) (wanted : Std.I64) (frames : Std.U32)
    (scheduled : Std.I64) :
    player.Player.step p wanted frames scheduled
      ⦃ r => -reach p ≤ r.offset.val ∧ r.offset.val ≤ reach p ⦄ := by
  unfold player.Player.step
  have hb := reach_bounds p
  step as ⟨reach1, hreach⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  step as ⟨beyond, hbeyond⟩
  step as ⟨i6, hi6⟩
  step as ⟨i7, hi7⟩
  step as ⟨even, heven, hzero⟩
  have h0 : (0#i128).val = 0 := by rfl
  have hneg : (core.num.I128.wrapping_sub 0#i128 reach1).val = -reach p := by
    rw [I128.wrapping_sub_val _ _ (by rw [h0, hreach]; omega), h0, hreach]
    omega
  have hlim :
      (if even > reach1 then fixed.saturate reach1
       else do
         let i8 ← lift (core.num.I128.wrapping_sub 0#i128 reach1)
         if even < i8 then
           let i9 ← lift (core.num.I128.wrapping_sub 0#i128 reach1)
           fixed.saturate i9
         else fixed.saturate even)
      ⦃ lim => -reach p ≤ lim.val ∧ lim.val ≤ reach p ⦄ := by
    split
    · step with Fixed.saturate_spec as ⟨r, hr⟩
      simp only [Fixed.clamp64, hreach] at hr
      omega
    · rename_i hle
      have hle' : even.val ≤ reach p := by rw [← hreach]; scalar_tac
      step as ⟨i8, hi8⟩
      split
      · step as ⟨i9, hi9⟩
        step with Fixed.saturate_spec as ⟨r, hr⟩
        rw [hi9, hneg] at hr
        simp only [Fixed.clamp64] at hr
        omega
      · rename_i hge
        have hge' : -reach p ≤ even.val := by rw [← hneg, ← hi8]; scalar_tac
        step with Fixed.saturate_spec as ⟨r, hr⟩
        simp only [Fixed.clamp64] at hr
        omega
  apply WP.spec_bind hlim
  intro lim ⟨hlo, hhi⟩
  step with step_clamped_spec lim as ⟨s, hseq, _, _⟩
  omega

@[step]
theorem position_units_total (p : timing.Position) :
    timing.Position.units p ⦃ _ => True ⦄ := by
  unfold timing.Position.units
  run

@[step]
theorem position_from_units_total (units : Std.U128) :
    timing.Position.from_units units ⦃ _ => True ⦄ := by
  unfold timing.Position.from_units
  run

@[step]
theorem step_units_total (s : timing.Step) : timing.Step.units s ⦃ _ => True ⦄ := by
  unfold timing.Step.units
  run

@[step]
theorem position_advance_total (p : timing.Position) (s : timing.Step) (frames : Std.U64) :
    timing.Position.advance p s frames ⦃ _ => True ⦄ := by
  unfold timing.Position.advance
  run

/-- Playing a cycle takes a step within the limit of the pace and leaves the
settings of the regulator as they are. -/
@[step]
theorem play_spec (p : player.Player) (frames : Std.U32)
    (scheduled behind ahead duration : Std.I64) :
    player.Player.play p frames scheduled behind ahead duration
      ⦃ r => -reach p ≤ r.1.2.offset.val ∧ r.1.2.offset.val ≤ reach p
        ∧ r.2.regulation = p.regulation ⦄ := by
  unfold player.Player.play
  step as ⟨wanted⟩
  step as ⟨st, hlo, hhi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨o⟩
  cases o <;> simp [hlo, hhi]

@[step]
theorem jumps_total (p : player.Player) (now : timing.Position) :
    player.Player.jumps p now ⦃ _ => True ⦄ := by
  unfold player.Player.jumps
  run

/-- Planning a cycle returns, for every state of the regulator and every
schedule, and the step of the plan is within the limit of the pace: a cycle
reads at most `reach` units of 2^-64 frame more or less than one frame of the
stream for each output frame, whatever the schedule does over it. -/
@[step]
theorem cycle_spec (p : player.Player) (now later : timing.Position) (frames : Std.U32)
    (duration : Std.I64) (slope : Std.I32) :
    player.Player.cycle p now later frames duration slope
      ⦃ r => -reach p ≤ r.1.step.offset.val ∧ r.1.step.offset.val ≤ reach p ∧
        r.2.regulation = p.regulation ⦄ := by
  unfold player.Player.cycle
  have hb := reach_bounds p
  step as ⟨scheduled⟩
  have hu : timing.Step.UNITY.offset.val = 0 := by simp [timing.Step.UNITY]
  split
  · simp only [WP.spec_ok]
    refine ⟨?_, ?_, trivial⟩ <;> (rw [hu]; omega)
  · split
    · simp only [WP.spec_ok]
      refine ⟨?_, ?_, trivial⟩ <;> (rw [hu]; omega)
    · step as ⟨jumped⟩
      cases jumped
      · simp only [Bool.false_eq_true, ↓reduceIte]
        step as ⟨behind⟩
        step as ⟨ahead⟩
        step as ⟨start, st, q, hlo, hhi, hreg⟩
        exact ⟨hlo, hhi, hreg⟩
      · simp only [↓reduceIte, bind_ok]
        step as ⟨start, st, q, hlo, hhi, hreg⟩
        exact ⟨hlo, hhi, hreg⟩

/-- The step of every plan is one that the resampler takes: below 2^56 units
either way, which is a pace within four in a thousand of one frame for each
output frame. -/
theorem cycle_step_small (p : player.Player) (now later : timing.Position) (frames : Std.U32)
    (duration : Std.I64) (slope : Std.I32) :
    player.Player.cycle p now later frames duration slope
      ⦃ r => -2^56 < r.1.step.offset.val ∧ r.1.step.offset.val < 2^56 ⦄ := by
  have hb := reach_bounds p
  apply WP.spec_mono (cycle_spec p now later frames duration slope)
  intro r hr
  omega

@[step]
theorem stop_total (p : player.Player) : player.Player.stop p ⦃ _ => True ⦄ := by
  unfold player.Player.stop
  simp

/-! ## Positions and steps as counts of units

The functions that the code outside the core uses to count positions and
steps in units of 2^-64 frame return for every argument. -/

theorem position_new_total (frame fraction : Std.U64) :
    timing.Position.new frame fraction ⦃ _ => True ⦄ := by
  unfold timing.Position.new
  simp

theorem position_at_frame_total (frame : Std.U64) :
    timing.Position.at_frame frame ⦃ _ => True ⦄ := by
  unfold timing.Position.at_frame
  simp

theorem position_frame_total (p : timing.Position) :
    timing.Position.impl.frame p ⦃ _ => True ⦄ := by
  unfold timing.Position.impl.frame
  simp

theorem position_fraction_total (p : timing.Position) :
    timing.Position.impl.fraction p ⦃ _ => True ⦄ := by
  unfold timing.Position.impl.fraction
  simp

theorem step_new_total (offset : Std.I64) : timing.Step.new offset ⦃ _ => True ⦄ := by
  unfold timing.Step.new
  run

theorem step_from_parts_per_billion_total (parts : Std.I64) :
    timing.Step.from_parts_per_billion parts ⦃ _ => True ⦄ := by
  unfold timing.Step.from_parts_per_billion
  run

/-! ## Parallel two-mode modal regulator (`ModalPlayer`) -/

/-- The largest pace offset for a `limit` in parts per billion, capped at
three in a thousand, in units of `2^-64` frame per output frame. -/
def reachOf (limit : Std.U32) : ℤ := (min limit.val 3000000 : ℕ) * 2^64 / 10^9

theorem reachOf_bounds (limit : Std.U32) : 0 ≤ reachOf limit ∧ reachOf limit ≤ 55340232221128654 := by
  unfold reachOf
  have h : (min limit.val 3000000 : ℕ) ≤ 3000000 := Nat.min_le_right _ _
  constructor
  · positivity
  · omega

@[step]
theorem modal_regulation_from_single_total (reg : player.Regulation) :
    player.ModalRegulation.from_single reg ⦃ _ => True ⦄ := by
  unfold player.ModalRegulation.from_single
  simp

@[step]
theorem modal_new_total (reg : player.ModalRegulation) :
    player.ModalPlayer.new reg ⦃ _ => True ⦄ := by
  unfold player.ModalPlayer.new
  simp

@[step]
theorem modal_stop_total (p : player.ModalPlayer) :
    player.ModalPlayer.stop p ⦃ _ => True ⦄ := by
  unfold player.ModalPlayer.stop
  simp

@[step]
theorem ns_to_frames_q32_total (schedule : timing.Schedule) (delta : Std.I64) :
    player.ns_to_frames_q32 schedule delta ⦃ _ => True ⦄ := by
  unfold player.ns_to_frames_q32
  run

@[step]
theorem gains_for_total (gain : Std.U32) (duration : Std.I64) :
    player.gains_for gain duration ⦃ _ => True ⦄ := by
  unfold player.gains_for
  run

@[step]
theorem regulate_for_total (gain : Std.U32) (behind ahead duration : Std.I64) :
    player.regulate_for gain behind ahead duration ⦃ _ => True ⦄ := by
  unfold player.regulate_for
  run

@[step]
theorem carry_slope_total (read : Std.I128) (prev slope : Std.I32) :
    player.carry_slope read prev slope ⦃ _ => True ⦄ := by
  unfold player.carry_slope
  run

@[step]
theorem reach_for_spec (limit : Std.U32) :
    player.reach_for limit ⦃ r => r.val = reachOf limit ⦄ := by
  unfold player.reach_for
  have hbillion : player.BILLION.val = 10^9 := by simp [player.BILLION]
  have hframe : player.FRAME.val = 2^64 := by simp [player.FRAME]
  have hlargest : player.LARGEST_LIMIT.val = 3000000 := by simp [player.LARGEST_LIMIT]
  split
  · rename_i hgt
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    have hiv : i.val = 3000000 := by rw [hi, U32.hcast_I128_val, hlargest]; rfl
    have hi1v : i1.val = 3000000 * 2^64 := by
      rw [hi1, I128.wrapping_mul_val _ _ (by rw [hiv, hframe]; norm_num), hiv, hframe]
    step as ⟨r, hr, _⟩
    rw [hr (by rw [hbillion]; norm_num), hi1v, hbillion]
    unfold reachOf
    have : min limit.val 3000000 = 3000000 := by scalar_tac
    rw [this]
    norm_num
  · rename_i hle
    simp only [bind_ok]
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    have hlim : limit.val ≤ 3000000 := by scalar_tac
    have hiv : i.val = limit.val := by rw [hi, U32.hcast_I128_val]
    have hi1v : i1.val = limit.val * 2^64 := by
      rw [hi1, I128.wrapping_mul_val _ _ (by rw [hiv, hframe]; omega), hiv, hframe]
    step as ⟨r, hr, _⟩
    rw [hr (by rw [hbillion]; norm_num), hi1v, hbillion]
    unfold reachOf
    have : min limit.val 3000000 = limit.val := by omega
    rw [this]

theorem clamp_sym_i128_spec (x hi : Std.I128) (hhi : 0 ≤ hi.val) (hfit : hi.val < 2^127) :
    player.clamp_sym_i128 x hi ⦃ r => -hi.val ≤ r.val ∧ r.val ≤ hi.val ⦄ := by
  unfold player.clamp_sym_i128
  have h0 : (0#i128).val = 0 := rfl
  step as ⟨lo, hlo⟩
  have hlov : lo.val = -hi.val := by
    rw [hlo, I128.wrapping_sub_val _ _ (by rw [h0]; omega), h0]; omega
  split
  · rw [WP.spec_ok]; omega
  · rename_i hle
    have hle' : x.val ≤ hi.val := by scalar_tac
    split
    · rw [WP.spec_ok, hlov]; omega
    · rename_i hge
      have hge' : -hi.val ≤ x.val := by rw [← hlov]; scalar_tac
      rw [WP.spec_ok]; omega

@[step]
theorem clamp_sym_i128_total (x hi : Std.I128) :
    player.clamp_sym_i128 x hi ⦃ _ => True ⦄ := by
  unfold player.clamp_sym_i128
  run

@[step]
theorem step_for_limit_spec (limit : Std.U32) (wanted : Std.I64) (frames : Std.U32)
    (scheduled : Std.I64) :
    player.step_for_limit limit wanted frames scheduled
      ⦃ s => -reachOf limit ≤ s.offset.val ∧ s.offset.val ≤ reachOf limit ⦄ := by
  unfold player.step_for_limit
  have hb := reachOf_bounds limit
  step as ⟨reach1, hreach⟩
  step as ⟨i, _⟩
  step as ⟨i1, _⟩
  step as ⟨i2, _⟩
  step as ⟨i3, _⟩
  step as ⟨i4, _⟩
  step as ⟨i5, _⟩
  step as ⟨beyond, _⟩
  step as ⟨i6, _⟩
  step as ⟨i7, _⟩
  step as ⟨st, _, _⟩
  step with clamp_sym_i128_spec st reach1 (by omega) (by omega) as ⟨cl, hcl_lo, hcl_hi⟩
  step with Fixed.saturate_spec cl as ⟨sat, hsat⟩
  step with step_clamped_spec sat as ⟨s, hs, _, _⟩
  rw [hreach] at hcl_lo hcl_hi
  simp only [Fixed.clamp64] at hsat
  omega

@[step]
theorem modal_jumps_total (p : player.ModalPlayer) (now : timing.Position) :
    player.ModalPlayer.jumps p now ⦃ _ => True ⦄ := by
  unfold player.ModalPlayer.jumps
  run

/-- Planning a cycle with `ModalPlayer` always returns, preserves its
regulation settings, and takes a step strictly within `reachOf` (and therefore
within `±2^56`, the resampler's safe step band). -/
@[step]
theorem modal_cycle_spec (p : player.ModalPlayer) (now later : timing.Position) (frames : Std.U32)
    (duration : Std.I64) (schedule : timing.Schedule) (peer_active : Bool) (epoch : Std.U32)
    (com_now com_then : Std.I64) :
    player.ModalPlayer.cycle p now later frames duration schedule peer_active epoch com_now com_then
      ⦃ r => -reachOf p.regulation.limit ≤ r.1.step.offset.val
        ∧ r.1.step.offset.val ≤ reachOf p.regulation.limit
        ∧ r.2.regulation = p.regulation ⦄ := by
  unfold player.ModalPlayer.cycle
  have hb := reachOf_bounds p.regulation.limit
  have hu : timing.Step.UNITY.offset.val = 0 := by simp [timing.Step.UNITY]
  step as ⟨scheduled⟩
  split
  · simp only [WP.spec_ok]; refine ⟨?_, ?_, trivial⟩ <;> (rw [hu]; omega)
  · split
    · simp only [WP.spec_ok]; refine ⟨?_, ?_, trivial⟩ <;> (rw [hu]; omega)
    · step as ⟨jumped⟩
      cases jumped
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases peer_active
        · simp only [Bool.false_eq_true, ↓reduceIte]
          apply WP.spec_bind (Pₘ := fun _ => True)
          · cases p.was_peer <;> simp [lift]
          · intro ⟨_, _, _, _, _⟩ _
            step*
        · simp only [↓reduceIte]
          apply WP.spec_bind (Pₘ := fun t => t.1 = p.regulation)
          · repeat' (first | split | step*)
          · intro ⟨mr, _, _, _, _, _, _⟩ hmr
            subst hmr
            step*
      · simp only [↓reduceIte]
        step as ⟨st, hlo, hhi⟩
        cases peer_active
        · simp only [Bool.false_eq_true, ↓reduceIte]
          step*
        · simp only [↓reduceIte]
          step*

/-- The step of every `ModalPlayer` plan stays strictly within `±2^56`, the
resampler's permitted band. -/
theorem modal_cycle_step_small (p : player.ModalPlayer) (now later : timing.Position)
    (frames : Std.U32) (duration : Std.I64) (schedule : timing.Schedule)
    (peer_active : Bool) (epoch : Std.U32) (com_now com_then : Std.I64) :
    player.ModalPlayer.cycle p now later frames duration schedule peer_active epoch com_now com_then
      ⦃ r => -2^56 < r.1.step.offset.val ∧ r.1.step.offset.val < 2^56 ⦄ := by
  have hb := reachOf_bounds p.regulation.limit
  apply WP.spec_mono
    (modal_cycle_spec p now later frames duration schedule peer_active epoch com_now com_then)
  intro r hr
  omega

/-- Helper: `player.gains_for` equals `Player.gains` for the same gain. -/
theorem gains_for_eq_player_gains (p : player.Player) (duration : Std.I64) :
    player.gains_for p.regulation.gain duration = player.Player.gains p duration := by
  unfold player.gains_for player.Player.gains player.Player.gain
  simp only [lift, bind_ok, Std.bind_assoc]

/-- Helper: `player.regulate_for` equals `Player.regulate` for the same gain. -/
theorem regulate_for_eq_player_regulate (p : player.Player) (behind ahead duration : Std.I64) :
    player.regulate_for p.regulation.gain behind ahead duration =
      player.Player.regulate p behind ahead duration := by
  unfold player.regulate_for player.Player.regulate
  rw [gains_for_eq_player_gains]

/-- Helper: `player.reach_for` equals `Player.reach` for the same limit. -/
theorem reach_for_eq_player_reach (p : player.Player) :
    player.reach_for p.regulation.limit = player.Player.reach p := by
  unfold player.reach_for player.Player.reach
  rfl

/-- Helper: `player.step_for_limit` equals `Player.step` for the same limit. -/
theorem step_for_limit_eq_player_step (p : player.Player) (wanted : Std.I64)
    (frames : Std.U32) (scheduled : Std.I64) :
    player.step_for_limit p.regulation.limit wanted frames scheduled =
      player.Player.step p wanted frames scheduled := by
  unfold player.step_for_limit player.Player.step player.clamp_sym_i128
  rw [← reach_for_eq_player_reach p]
  simp only [lift, bind_ok]
  congr 1; funext reach1
  congr 1; funext step
  split
  · simp only [bind_ok]
  · split <;> simp only [bind_ok]

private theorem exists_ok_of_spec {α : Type} {r : Result α} {P : α → Prop}
    (h : r ⦃ P ⦄) : ∃ x, r = ok x ∧ P x := by
  cases r with
  | ret x => exact ⟨x, rfl, by simpa [WP.spec_ok] using h⟩
  | vis _ _ => simp [WP.spec_vis] at h
  | div => simp [WP.spec_div] at h

private theorem regulate_for_zero (gain : Std.U32) (duration : Std.I64) :
    player.regulate_for gain 0#i64 0#i64 duration = ok 0#i64 := by
  have h : player.regulate_for gain 0#i64 0#i64 duration ⦃ r => r = 0#i64 ⦄ := by
    unfold player.regulate_for
    step as ⟨g⟩
    have hz : (IScalar.cast .I128 0#i64).val = 0 := by
      rw [I64.cast_I128_val]; rfl
    have hm1 : (core.num.I128.wrapping_mul g.ahead (IScalar.cast .I128 0#i64)).val = 0 := by
      rw [I128.wrapping_mul_val _ _ (by rw [hz]; norm_num), hz, mul_zero]
    have hm2 : (core.num.I128.wrapping_mul g.behind (IScalar.cast .I128 0#i64)).val = 0 := by
      rw [I128.wrapping_mul_val _ _ (by rw [hz]; norm_num), hz, mul_zero]
    have hs1 : (core.num.I128.wrapping_shr
        (core.num.I128.wrapping_mul g.ahead (IScalar.cast .I128 0#i64)) 32#u32).val = 0 := by
      rw [I128.wrapping_shr_val _ _ (by decide), hm1]; norm_num
    have hs2 : (core.num.I128.wrapping_shr
        (core.num.I128.wrapping_mul g.behind (IScalar.cast .I128 0#i64)) 32#u32).val = 0 := by
      rw [I128.wrapping_shr_val _ _ (by decide), hm2]; norm_num
    have ha : (core.num.I128.wrapping_add
        (core.num.I128.wrapping_shr
          (core.num.I128.wrapping_mul g.ahead (IScalar.cast .I128 0#i64)) 32#u32)
        (core.num.I128.wrapping_shr
          (core.num.I128.wrapping_mul g.behind (IScalar.cast .I128 0#i64)) 32#u32)).val = 0 := by
      rw [I128.wrapping_add_val _ _ (by rw [hs1, hs2]; norm_num), hs1, hs2]
      norm_num
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨kept, hkept⟩
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨added, hadded⟩
    step as ⟨i4, hi4⟩
    step with Fixed.saturate_spec i4 as ⟨r, hr⟩
    apply IScalar.eq_of_val_eq
    have hi4v : i4.val = 0 := by rw [hi4, hkept, hadded, hi1, hi3, hi, hi2]; exact ha
    rw [hr, hi4v]
    simp [Fixed.clamp64]
  obtain ⟨r, hr, h0⟩ := exists_ok_of_spec h
  rw [hr, h0]

/-- **Exact Star degeneration of `ModalPlayer`:** when `peer_active = false`
(and `was_peer = false`), `ModalPlayer.cycle` produces the exact same `Plan`
and next playback `(running, position, pace, slope)` as single-mode
`Player.cycle` at `star_gain`. -/
theorem modal_star_matches_player (m : player.ModalPlayer) (p : player.Player)
    (now later : timing.Position) (frames : Std.U32) (duration : Std.I64)
    (schedule : timing.Schedule) (epoch : Std.U32) (com_now com_then : Std.I64)
    (hgain : m.regulation.star_gain = p.regulation.gain)
    (hlim : m.regulation.limit = p.regulation.limit)
    (hjump : m.regulation.jump = p.regulation.jump)
    (hrun : m.running = p.running)
    (hpos : m.position = p.position)
    (hpace : m.diff_pace = p.pace)
    (hslope : m.slope = p.slope)
    (hwp : m.was_peer = false) :
    (do
      let rm ← player.ModalPlayer.cycle m now later frames duration schedule false epoch com_now com_then
      let rp ← player.Player.cycle p now later frames duration schedule.level_slope
      ok (rm, rp))
      ⦃ pair =>
        pair.1.1 = pair.2.1
        ∧ pair.1.2.running = pair.2.2.running
        ∧ pair.1.2.position = pair.2.2.position
        ∧ pair.1.2.diff_pace = pair.2.2.pace
        ∧ pair.1.2.slope = pair.2.2.slope
        ∧ pair.1.2.was_peer = false ⦄ := by
  have hjumps_eq : player.ModalPlayer.jumps m now = player.Player.jumps p now := by
    unfold player.ModalPlayer.jumps player.Player.jumps
    rw [hrun, hpos, hjump]
  obtain ⟨scheduled, hsched, -⟩ := exists_ok_of_spec (distance_total now later)
  unfold player.ModalPlayer.cycle player.Player.cycle
  simp only [hgain, hlim, hrun, hpos, hpace, hslope, hwp, Bool.false_eq_true, ↓reduceIte,
    hsched, bind_ok, hjumps_eq]
  split
  · simp [hrun, hpos, hpace, hslope, hwp]
  · split
    · simp [hrun, hpos, hpace, hslope, hwp]
    · obtain ⟨jumped, hjumped, -⟩ := exists_ok_of_spec (jumps_total p now)
      simp only [hjumped, bind_ok]
      cases jumped
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨behind, hbeh, -⟩ := exists_ok_of_spec (distance_total p.position now)
        set read :=
          core.num.I128.wrapping_add
            (core.num.I128.wrapping_mul (UScalar.hcast .I128 frames) player.FRAME_IN_CORRECTIONS)
            (core.num.I128.wrapping_shr
              (core.num.I128.wrapping_mul (UScalar.hcast .I128 frames) (IScalar.cast .I128 p.pace))
              16#u32)
        obtain ⟨carried, hcarried, -⟩ :=
          exists_ok_of_spec (carry_slope_total read p.slope schedule.level_slope)
        obtain ⟨ahead, hahead_sat, -⟩ :=
          exists_ok_of_spec (Fixed.saturate_spec
            (core.num.I128.wrapping_sub carried
              (core.num.I128.wrapping_mul (IScalar.cast .I128 scheduled) player.SIXTEEN_BITS)))
        have hahead : player.Player.ahead p frames scheduled schedule.level_slope = ok ahead := by
          unfold player.Player.ahead
          simp only [lift, bind_ok]
          have hcarried' := hcarried
          unfold player.carry_slope at hcarried'
          simp only [lift, bind_ok] at hcarried'
          rw [show (if (p.slope != schedule.level_slope) = true then
              if core.num.I128.wrapping_add (IScalar.cast .I128 player.BILLION) (IScalar.cast .I128 p.slope) > 0#i128 then
                if core.num.I128.wrapping_add (IScalar.cast .I128 player.BILLION) (IScalar.cast .I128 schedule.level_slope) > 0#i128 then
                  fixed.div_floor_wide
                    (core.num.I128.wrapping_mul read
                      (core.num.I128.wrapping_add (IScalar.cast .I128 player.BILLION) (IScalar.cast .I128 p.slope)))
                    (core.num.I128.wrapping_add (IScalar.cast .I128 player.BILLION) (IScalar.cast .I128 schedule.level_slope))
                else ok read
              else ok read
            else ok read) = ok carried from hcarried']
          simpa [bind_ok] using hahead_sat
        obtain ⟨wanted, hwanted, -⟩ :=
          exists_ok_of_spec (regulate_for_total p.regulation.gain behind ahead duration)
        obtain ⟨st, hst, -⟩ :=
          exists_ok_of_spec (step_for_limit_spec p.regulation.limit wanted frames scheduled)
        obtain ⟨adv, hadv, -⟩ :=
          exists_ok_of_spec (position_advance_total p.position st (UScalar.cast .U64 frames))
        unfold player.Player.play
        simp only [hbeh, bind_ok, lift, hahead, timing.Step.impl.offset, Std.uncurry]
        rw [hcarried]
        simp only [bind_ok, hahead_sat, ← regulate_for_eq_player_regulate,
          ← step_for_limit_eq_player_step]
        simp only [hwanted, bind_ok, hst, hadv]
        cases adv <;> simp
      · simp only [↓reduceIte, bind_ok]
        have hreg0 := regulate_for_zero p.regulation.gain duration
        obtain ⟨st, hst, -⟩ :=
          exists_ok_of_spec (step_for_limit_spec p.regulation.limit 0#i64 frames scheduled)
        obtain ⟨adv, hadv, -⟩ :=
          exists_ok_of_spec (position_advance_total now st (UScalar.cast .U64 frames))
        unfold player.Player.play
        simp only [lift, bind_ok, ← regulate_for_eq_player_regulate,
          ← step_for_limit_eq_player_step, timing.Step.impl.offset, Std.uncurry]
        rw [hreg0]
        simp only [bind_ok, hst, hadv]
        cases adv <;> simp

end Unisono.Player
