/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar

/-!
# When recent packets arrived

The functions of `unisono_core::arrivals` return for every state of the table
and every argument.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Arrivals

variable {K : Std.Usize}

@[step]
theorem at_total (a : arrivals.Arrivals K) (place : Std.Usize) :
    arrivals.Arrivals.at a place ⦃ _ => True ⦄ := by
  unfold arrivals.Arrivals.at
  simp only [lift, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  split <;> simp

/-- Looking for an arrival returns, whatever the table holds. -/
@[step]
theorem find_total (a : arrivals.Arrivals K) (index : Std.U64) :
    arrivals.Arrivals.find a index ⦃ _ => True ⦄ := by
  unfold arrivals.Arrivals.find arrivals.Arrivals.find_loop
  apply loop.spec_decr_nat
    (measure := fun place : Std.Usize => K.val - place.val)
    (inv := fun _ => True)
  · rintro place -
    unfold arrivals.Arrivals.find_loop.body
    split
    · have hlt : place.val < K.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨arrival⟩
      split
      · split
        · simp
        · step as ⟨place1, hplace1⟩
          rw [hplace1]
          omega
      · step as ⟨place1, hplace1⟩
        rw [hplace1]
        omega
    · simp
  · trivial

/-- Keeping an arrival returns, whatever the table holds: also when the place
it would write to does not exist. -/
@[step]
theorem record_total (a : arrivals.Arrivals K) (index : Std.U64) (time : Std.I64) :
    arrivals.Arrivals.record a index time ⦃ _ => True ⦄ := by
  unfold arrivals.Arrivals.record
  step as ⟨o⟩
  cases o with
  | some v => simp
  | none =>
    simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, Array.to_slice_mut,
      lift, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
      bind_ok, Std.uncurry]
    split <;> step*

end Unisono.Arrivals
