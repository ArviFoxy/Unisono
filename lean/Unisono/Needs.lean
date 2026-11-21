/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Packet

/-!
# The needs of the frames of a stream

Every function of `unisono_core::needs` returns, for every state and every
argument, and so do the functions of `unisono_core::packet` that write the
needs into a report and read them back.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Needs

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

variable {S : Std.Usize}

@[step]
theorem new_total (S : Std.Usize) : needs.Needs.new S ⦃ _ => True ⦄ := by
  unfold needs.Needs.new
  run

@[step]
theorem clear_total (n : needs.Needs S) : needs.Needs.clear n ⦃ _ => True ⦄ := by
  unfold needs.Needs.clear needs.Needs.clear_loop
  apply loop.spec_decr_nat
    (measure := fun x : needs.Needs S × Std.Usize => S.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨s, place⟩ -
    unfold needs.Needs.clear_loop.body
    simp only
    split
    · have hlt : place.val < S.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
        core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
      cases s.places.to_slice[place]? <;>
        (simp only [bind_ok, WP.spec_ok]; exact ⟨trivial, by rw [hnext]; omega⟩)
    · simp
  · trivial

@[step]
theorem held_any_total (n : needs.Needs S) : needs.Needs.held_any n ⦃ _ => True ⦄ := by
  unfold needs.Needs.held_any needs.Needs.held_any_loop
  apply loop.spec_decr_nat
    (measure := fun place : Std.Usize => S.val - place.val)
    (inv := fun _ => True)
  · rintro place -
    unfold needs.Needs.held_any_loop.body
    split
    · have hlt : place.val < S.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [lift, bind_ok, core.slice.Slice.get, core.slice.index.Usize.get]
      repeat' split
      all_goals first
        | (simp only [WP.spec_ok]; exact ⟨trivial, by rw [hnext]; omega⟩)
        | simp
    · simp
  · trivial

@[step]
theorem kept_total (n : needs.Needs S) (stretch : Std.U64) :
    needs.Needs.kept n stretch ⦃ _ => True ⦄ := by
  unfold needs.Needs.kept
  run

@[step]
theorem put_total (n : needs.Needs S) (stretch : Std.U64) (need : Std.I64) :
    needs.Needs.put n stretch need ⦃ _ => True ⦄ := by
  unfold needs.Needs.put
  simp only [lift, bind_ok, Array.to_slice_mut, core.slice.Slice.get_mut,
    core.slice.index.Usize.get_mut, Std.uncurry]
  repeat' split
  all_goals run

/-- Taking in a need returns, for every state, stretch and need. -/
theorem observe_total (n : needs.Needs S) (stretch : Std.U64) (need : Std.I64) :
    needs.Needs.observe n stretch need ⦃ _ => True ⦄ := by
  unfold needs.Needs.observe
  run

theorem newest_total (n : needs.Needs S) : needs.Needs.impl.newest n ⦃ _ => True ⦄ := by
  unfold needs.Needs.impl.newest
  run

@[step]
theorem get_total (n : needs.Needs S) (stretch : Std.U64) :
    needs.Needs.get n stretch ⦃ _ => True ⦄ := by
  unfold needs.Needs.get
  simp only [lift, bind_ok, Array.to_slice, core.slice.Slice.get,
    core.slice.index.Usize.get]
  run

@[step]
theorem microseconds_total (need : Std.I64) : needs.microseconds need ⦃ _ => True ⦄ := by
  unfold needs.microseconds
  run

@[step]
theorem recent_loop_total (a : Array needs.Place S) (newest : Std.U64) (count : Std.U8)
    (slots : Array Std.I32 11#usize) (back : Std.Usize) :
    needs.Needs.recent_loop a newest count slots back ⦃ _ => True ⦄ := by
  unfold needs.Needs.recent_loop
  apply loop.spec_decr_nat
    (measure := fun x : Std.U8 × Array Std.I32 11#usize × Std.Usize => 11 - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨count1, slots1, back1⟩ -
    unfold needs.Needs.recent_loop.body
    simp only
    split
    · have hlt : back1.val < 11 := by
        simp only [packet.RECENT] at *
        scalar_tac
      have hnext : (core.num.Usize.saturating_add back1 1#usize).val = back1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [lift, bind_ok, Array.to_slice_mut, core.slice.Slice.get_mut,
        core.slice.index.Usize.get_mut, Std.uncurry]
      split
      · split
        · split
          · simp only [bind_ok, WP.spec_ok]
            exact ⟨trivial, by rw [hnext]; omega⟩
          · rw [Aeneas.Std.bind_assoc]
            step as ⟨o1⟩
            split
            · simp only [bind_ok, WP.spec_ok]
              rw [hnext]
              omega
            · rw [Aeneas.Std.bind_assoc]
              step as ⟨slot⟩
              rw [hnext]
              omega
        · simp
      · simp
    · simp
  · trivial

/-- Making the needs that a report carries returns, for every state. -/
theorem recent_total (n : needs.Needs S) : needs.Needs.recent n ⦃ _ => True ⦄ := by
  unfold needs.Needs.recent
  run

end Unisono.Needs

namespace Unisono.Packet

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

@[step]
theorem write_needs_loop_total (a : Array Std.I32 11#usize) (bytes : Slice Std.U8)
    (count : Std.Usize) (written : Bool) (i : Std.Usize) :
    packet.write_needs_loop a bytes count written i ⦃ _ => True ⦄ := by
  unfold packet.write_needs_loop
  apply loop.spec_decr_nat
    (measure := fun x : Slice Std.U8 × Bool × Std.Usize => count.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨bytes1, written1, i1⟩ _
    unfold packet.write_needs_loop.body
    simp only
    split
    · have hlt : i1.val < count.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [lift, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok,
        Array.to_slice]
      split
      all_goals
        step as ⟨out⟩
        rw [hnext]
        omega
    · simp
  · trivial

@[step]
theorem parse_needs_loop_total (bytes : Slice Std.U8) (count : Std.U8)
    (slots : Array Std.I32 11#usize) (said : Std.Usize) (i : Std.Usize) :
    packet.parse_needs_loop bytes count slots said i ⦃ _ => True ⦄ := by
  unfold packet.parse_needs_loop
  apply loop.spec_decr_nat
    (measure := fun x : Std.U8 × Array Std.I32 11#usize × Std.Usize => said.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨count1, slots1, i1⟩ _
    unfold packet.parse_needs_loop.body
    simp only
    split
    · have hlt : i1.val < said.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [lift, bind_ok, Array.to_slice_mut, core.slice.Slice.get_mut,
        core.slice.index.Usize.get_mut, Std.uncurry]
      step as ⟨o⟩
      split
      · simp
      · split
        all_goals
          simp only [bind_ok, WP.spec_ok]
          rw [hnext]
          omega
    · simp
  · trivial

/-- Reading the needs from a report returns, for every bytes. -/
theorem parse_needs_total (bytes : Slice Std.U8) :
    packet.parse_needs bytes ⦃ _ => True ⦄ := by
  unfold packet.parse_needs
  run

/-- Writing the needs into a report returns, for every needs and bytes. -/
theorem write_needs_total (recent : packet.Recent) (bytes : Slice Std.U8) :
    packet.write_needs recent bytes ⦃ _ => True ⦄ := by
  unfold packet.write_needs
  run

end Unisono.Packet
