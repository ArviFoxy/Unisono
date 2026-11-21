/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed
public import Unisono.Lists
public import Unisono.Player

/-!
# The answers that went fastest there and back

Every function of `unisono_core::answers` returns, for every state and every
argument.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Answers

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

variable {R : Std.Usize}

@[step]
theorem round_trip_total (forward : relation.Line) (answer : answers.Answer) :
    answers.round_trip forward answer ⦃ _ => True ⦄ := by
  unfold answers.round_trip
  run

@[step]
theorem new_total (R : Std.Usize) (length : Std.I64) :
    answers.Answers.new R length ⦃ _ => True ⦄ := by
  unfold answers.Answers.new
  run

@[step]
theorem clear_spec (a : answers.Answers R) :
    answers.Answers.clear a ⦃ a' =>
      ∀ k, k < R.val → ∀ p, a'.places.val[k]? = some p → p.held = false ⦄ := by
  unfold answers.Answers.clear answers.Answers.clear_loop
  apply loop.spec_decr_nat
    (measure := fun x : answers.Answers R × Std.Usize => R.val - x.2.val)
    (inv := fun x : answers.Answers R × Std.Usize =>
      x.2.val ≤ R.val ∧ ∀ k, k < x.2.val → ∀ p, x.1.places.val[k]? = some p → p.held = false)
  · rintro ⟨s, place⟩ ⟨hple, hdone⟩
    dsimp only at hple hdone
    unfold answers.Answers.clear_loop.body
    simp only
    split
    · have hlt : place.val < R.val := by scalar_tac
      have hlenR : s.places.val.length = R.val := s.places.property
      have hplaceR : place.val < s.places.val.length := by omega
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
        core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
      have hsget : s.places.val[place.val]? = some (s.places.val[place.val]'hplaceR) :=
        List.getElem?_eq_getElem hplaceR
      have hslice_get : s.places.to_slice[place]? = some (s.places.val[place.val]'hplaceR) := by
        rw [Slice.getElem?_Usize_eq]
        simp [Array.to_slice]
      rw [hslice_get]
      simp only [bind_ok, WP.spec_ok]
      set slot := s.places.val[place.val]'hplaceR
      set arr := s.places.from_slice
        (s.places.to_slice.set_opt place (some { slot with held := false }))
      have haval : arr.val = s.places.val.set place.val { slot with held := false } := by
        dsimp only [arr]
        rw [Array.from_slice_val _ _ (by simp [Slice.set_opt, Array.to_slice, hlenR])]
        simp [Slice.set_opt, Array.to_slice, Unisono.Lists.set_opt_some]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro k hk p hp
      rw [haval] at hp
      by_cases hkp : k = place.val
      · subst hkp
        rw [List.getElem?_set_self hplaceR] at hp
        injection hp with hp'
        rw [← hp']
      · rw [List.getElem?_set_ne (by omega)] at hp
        exact hdone k (by omega) p hp
    · have heq : place.val = R.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [← heq]
      exact hdone
  · dsimp only
    have h0 : (0#usize).val = 0 := rfl
    exact ⟨by omega, fun k hk => by omega⟩

theorem clear_total (a : answers.Answers R) : answers.Answers.clear a ⦃ _ => True ⦄ :=
  WP.spec_mono (clear_spec a) fun _ _ => trivial

@[step]
theorem held_any_total (a : answers.Answers R) : answers.Answers.held_any a ⦃ _ => True ⦄ := by
  unfold answers.Answers.held_any answers.Answers.held_any_loop
  apply loop.spec_decr_nat
    (measure := fun place : Std.Usize => R.val - place.val)
    (inv := fun _ => True)
  · rintro place -
    unfold answers.Answers.held_any_loop.body
    split
    · have hlt : place.val < R.val := by scalar_tac
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
theorem oldest_total (a : answers.Answers R) : answers.Answers.oldest a ⦃ _ => True ⦄ := by
  unfold answers.Answers.oldest
  run

@[step]
theorem restarts_total (a : answers.Answers R) (window : Std.I64) :
    answers.Answers.restarts a window ⦃ _ => True ⦄ := by
  unfold answers.Answers.restarts
  run

@[step]
theorem passed_total (a : answers.Answers R) (window : Std.I64) :
    answers.Answers.passed a window ⦃ _ => True ⦄ := by
  unfold answers.Answers.passed
  run

@[step]
theorem put_total (a : answers.Answers R) (window : Std.I64) (answer : answers.Answer)
    (forward : relation.Line) : answers.Answers.put a window answer forward ⦃ _ => True ⦄ := by
  unfold answers.Answers.put
  simp only [lift, bind_ok, Array.to_slice_mut, core.slice.Slice.get_mut,
    core.slice.index.Usize.get_mut, Std.uncurry]
  run

/-- Taking in an answer returns, for every state, answer and estimate. -/
theorem observe_total (a : answers.Answers R) (answer : answers.Answer)
    (forward : relation.Line) : answers.Answers.observe a answer forward ⦃ _ => True ⦄ := by
  unfold answers.Answers.observe
  run

/-- Asking for the shortest time there and back returns, for every state and
estimate. -/
theorem shortest_total (a : answers.Answers R) (forward : relation.Line) :
    answers.Answers.shortest a forward ⦃ _ => True ⦄ := by
  unfold answers.Answers.shortest answers.Answers.shortest_loop
  step as ⟨oldest⟩
  apply loop.spec_decr_nat
    (measure := fun x : Option Std.I64 × Std.Usize => R.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨small, place⟩ -
    unfold answers.Answers.shortest_loop.body
    simp only
    split
    · have hlt : place.val < R.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [lift, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok,
        Array.to_slice]
      repeat' split
      all_goals try (simp only [bind_ok, WP.spec_ok]; exact ⟨trivial, by rw [hnext]; omega⟩)
      all_goals
        rw [Aeneas.Std.bind_assoc]
        step with round_trip_total as ⟨time⟩
        try split
        all_goals first
          | (simp only [bind_ok, WP.spec_ok]; rw [hnext]; omega)
          | (rw [hnext]; omega)
    · simp
  · trivial

end Unisono.Answers
