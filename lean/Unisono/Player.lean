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
theorem distance_total (a b : timing.Position) : timing.distance a b ⦃ _ => True ⦄ := by
  unfold timing.distance
  run

@[step]
theorem advance_total (start : timing.Position) (frames : Std.U32) (step : Std.I64) :
    timing.advance start frames step ⦃ _ => True ⦄ := by
  unfold timing.advance
  run

@[step]
theorem gain_total (p : player.Player) (duration : Std.I64) :
    player.Player.gain p duration ⦃ _ => True ⦄ := by
  unfold player.Player.gain
  run

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
  step*

@[step]
theorem jumps_total (p : player.Player) (behind : Std.I64) :
    player.Player.jumps p behind ⦃ _ => True ⦄ := by
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
    · step as ⟨behind⟩
      step as ⟨jumped⟩
      cases jumped
      · simp only [Bool.false_eq_true, ↓reduceIte]
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

theorem step_new_total (offset : Std.I64) : timing.Step.new offset ⦃ _ => True ⦄ := by
  unfold timing.Step.new
  run

theorem position_advance_total (p : timing.Position) (s : timing.Step) (frames : Std.U64) :
    timing.Position.advance p s frames ⦃ _ => True ⦄ := by
  unfold timing.Position.advance
  run

theorem step_from_parts_per_billion_total (parts : Std.I64) :
    timing.Step.from_parts_per_billion parts ⦃ _ => True ⦄ := by
  unfold timing.Step.from_parts_per_billion
  run

end Unisono.Player
