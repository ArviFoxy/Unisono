/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Lists
public import Unisono.Player

/-!
# The line of a device

The functions of `unisono_core::device` return for every state and every
report: also when the count of kept reports or the place of the next one is
not what the functions themselves would have left.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Device

variable {W : Std.Usize}

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

@[step]
theorem div_floor_wide_total (a b : Std.I128) : fixed.div_floor_wide a b ⦃ _ => True ⦄ := by
  unfold fixed.div_floor_wide
  run

@[step]
theorem within_total (value : Std.I128) : device.within value ⦃ _ => True ⦄ := by
  unfold device.within
  run

@[step]
theorem kept_total (d : device.Device W) : device.Device.kept d ⦃ _ => True ⦄ := by
  unfold device.Device.kept
  run

@[step]
theorem at_total (d : device.Device W) (place : Std.Usize) :
    device.Device.at d place ⦃ _ => True ⦄ := by
  unfold device.Device.at
  simp only [lift, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  split <;> simp

@[step]
theorem newest_total (d : device.Device W) : device.Device.newest d ⦃ _ => True ⦄ := by
  unfold device.Device.newest
  run

@[step]
theorem nominal_total (d : device.Device W) (frames : Std.I128) :
    device.Device.nominal d frames ⦃ _ => True ⦄ := by
  unfold device.Device.nominal
  run

@[step]
theorem restarted_total (d : device.Device W) (position : Std.U64) (time : Std.I64) :
    device.Device.restarted d position time ⦃ _ => True ⦄ := by
  unfold device.Device.restarted
  step as ⟨o⟩
  cases o with
  | none => simp
  | some newest =>
    simp only
    split <;> simp

@[step]
theorem add_total (d : device.Device W) (sums : device.Sums) (newest reading : device.Reading) :
    device.Device.add d sums newest reading ⦃ _ => True ⦄ := by
  unfold device.Device.add
  run

@[step]
theorem sums_total (d : device.Device W) (newest : device.Reading) :
    device.Device.sums d newest ⦃ _ => True ⦄ := by
  unfold device.Device.sums
  step as ⟨kept⟩
  unfold device.Device.sums_loop
  apply loop.spec_decr_nat
    (measure := fun x : device.Sums × Std.Usize => kept.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨sums, place⟩ _
    unfold device.Device.sums_loop.body
    simp only
    split
    · have hlt : place.val < kept.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o⟩
      cases o with
      | none =>
        simp only [bind_ok]
        step as ⟨place1, hplace1⟩
        rw [hplace1]
        omega
      | some reading =>
        simp only
        step as ⟨sums1⟩
        step as ⟨place1, hplace1⟩
        rw [hplace1]
        omega
    · simp
  · trivial

/-- Taking in a report returns for every state of the device and every
report. -/
theorem observe_total (d : device.Device W) (position : Std.U64) (time : Std.I64) :
    device.Device.observe d position time ⦃ _ => True ⦄ := by
  unfold device.Device.observe
  step as ⟨restarted⟩
  simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
    core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
  run

/-- Asking when a position's frame leaves the device returns for every state
and every position. -/
theorem when_total (d : device.Device W) (position : Std.U64) :
    device.Device.when d position ⦃ _ => True ⦄ := by
  unfold device.Device.when
  step as ⟨o⟩
  cases o with
  | none => simp
  | some newest =>
    simp only
    step as ⟨sums⟩
    run

end Unisono.Device
