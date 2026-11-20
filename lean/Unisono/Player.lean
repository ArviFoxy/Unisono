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
theorem regulate_total (p : player.Player) (behind duration : Std.I64) :
    player.Player.regulate p behind duration ⦃ _ => True ⦄ := by
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

/-- The step of a cycle is within the limit of the pace, whatever the state
of the regulator, the schedule and the correction that was wanted. -/
@[step]
theorem step_spec (p : player.Player) (wanted : Std.I64) (frames : Std.U32)
    (scheduled : Std.I64) :
    player.Player.step p wanted frames scheduled
      ⦃ r => -reach p ≤ r.val ∧ r.val ≤ reach p ⦄ := by
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

/-- Playing a cycle takes a step within the limit of the pace and leaves the
settings of the regulator as they are. -/
@[step]
theorem play_spec (p : player.Player) (frames : Std.U32) (scheduled behind duration : Std.I64) :
    player.Player.play p frames scheduled behind duration
      ⦃ r => -reach p ≤ r.1.2.val ∧ r.1.2.val ≤ reach p ∧ r.2.regulation = p.regulation ⦄ := by
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
    (duration : Std.I64) :
    player.Player.cycle p now later frames duration
      ⦃ r => -reach p ≤ r.1.step.val ∧ r.1.step.val ≤ reach p ∧
        r.2.regulation = p.regulation ⦄ := by
  unfold player.Player.cycle
  have hb := reach_bounds p
  step as ⟨scheduled⟩
  have h0 : (0#i64).val = 0 := by rfl
  split
  · simp only [WP.spec_ok]
    refine ⟨?_, ?_, trivial⟩ <;> (rw [h0]; omega)
  · split
    · simp only [WP.spec_ok]
      refine ⟨?_, ?_, trivial⟩ <;> (rw [h0]; omega)
    · step as ⟨behind⟩
      step as ⟨jumped⟩
      cases jumped
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
        step as ⟨start, st, q, hlo, hhi, hreg⟩
        exact ⟨hlo, hhi, hreg⟩
      · simp only [↓reduceIte, bind_ok]
        step as ⟨start, st, q, hlo, hhi, hreg⟩
        exact ⟨hlo, hhi, hreg⟩

/-- The step of every plan is one that the resampler takes: below 2^56 units
either way, which is a pace within four in a thousand of one frame for each
output frame. -/
theorem cycle_step_small (p : player.Player) (now later : timing.Position) (frames : Std.U32)
    (duration : Std.I64) :
    player.Player.cycle p now later frames duration
      ⦃ r => -2^56 < r.1.step.val ∧ r.1.step.val < 2^56 ⦄ := by
  have hb := reach_bounds p
  apply WP.spec_mono (cycle_spec p now later frames duration)
  intro r hr
  omega

@[step]
theorem stop_total (p : player.Player) : player.Player.stop p ⦃ _ => True ⦄ := by
  unfold player.Player.stop
  simp

end Unisono.Player
