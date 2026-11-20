/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Lists
public import Unisono.Scalar

/-!
# When recent packets arrived

Functional specifications for `unisono_core::arrivals`: lookup finds the first
used slot matching the packet index, and recording an arrival preserves an
already-recorded entry (keeping the earliest arrival) or stores the new entry
at `next` and advances `next` modulo `K`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Arrivals

variable {K : Std.Usize}

/-- Whether a slot holds an arrival for `index`. -/
def matchesIndex (index : Std.U64) (s : arrivals.Arrival) : Bool :=
  s.used && s.index == index

/-- The arrival time stored for `index`, if any slot holds it. -/
def lookup (a : arrivals.Arrivals K) (index : Std.U64) : Option Std.I64 :=
  (a.places.val.find? (matchesIndex index)).map (·.time)

/-- The entry at `place`, or an unused placeholder if out of bounds. -/
@[step]
theorem at_spec (a : arrivals.Arrivals K) (place : Std.Usize) :
    arrivals.Arrivals.at a place ⦃ r =>
      (place.val < K.val → ∃ h : place.val < a.places.val.length, r = a.places.val[place.val]'h)
      ∧ (K.val ≤ place.val → r = { used := false, index := 0#u64, time := 0#i64 }) ⦄ := by
  unfold arrivals.Arrivals.at
  simp only [lift, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  have hlen : a.places.val.length = K.val := a.places.property
  have hval : a.places.to_slice.val = a.places.val := by simp [Array.to_slice]
  have hidx : a.places.to_slice[place]? = a.places.val[place.val]? := by
    change a.places.to_slice.val[place.val]? = a.places.val[place.val]?
    rw [hval]
  rw [hidx]
  by_cases hlt : place.val < K.val
  · have hlt' : place.val < a.places.val.length := by omega
    rw [List.getElem?_eq_getElem hlt']
    rw [WP.spec_ok]
    exact ⟨fun _ => ⟨hlt', rfl⟩, fun h => by omega⟩
  · rw [List.getElem?_eq_none (by omega)]
    rw [WP.spec_ok]
    exact ⟨fun h => by omega, fun _ => rfl⟩

@[step]
theorem at_total (a : arrivals.Arrivals K) (place : Std.Usize) :
    arrivals.Arrivals.at a place ⦃ _ => True ⦄ :=
  WP.spec_mono (at_spec a place) (fun _ _ => trivial)

/-- Looking up an arrival searches slots `0 .. K` in order and returns the time
of the first matching used slot, or `none`. -/
@[step]
theorem find_spec (a : arrivals.Arrivals K) (index : Std.U64) :
    arrivals.Arrivals.find a index ⦃ r => r = lookup a index ⦄ := by
  unfold arrivals.Arrivals.find arrivals.Arrivals.find_loop
  have hlen : a.places.val.length = K.val := a.places.property
  have hloop : ∀ place : Std.Usize,
      loop (fun place1 => arrivals.Arrivals.find_loop.body a index place1) place
        ⦃ r => r = ((a.places.val.drop place.val).find? (matchesIndex index)).map (·.time) ⦄ := by
    intro place0
    apply loop.spec_decr_nat
      (measure := fun place : Std.Usize => K.val - place.val)
      (inv := fun place : Std.Usize =>
        ((a.places.val.drop place.val).find? (matchesIndex index)).map (·.time) =
          ((a.places.val.drop place0.val).find? (matchesIndex index)).map (·.time))
    · rintro place hinv
      unfold arrivals.Arrivals.find_loop.body
      split
      · have hlt : place.val < K.val := by scalar_tac
        have hlt_len : place.val < a.places.val.length := by omega
        have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
          Usize.saturating_add_val _ _ (by scalar_tac)
        have hdrop : a.places.val.drop place.val =
            a.places.val[place.val]'hlt_len :: a.places.val.drop (place.val + 1) :=
          List.drop_eq_getElem_cons hlt_len
        step with at_spec a place as ⟨arrival, hat_lt, _⟩
        obtain ⟨_, harr⟩ := hat_lt hlt
        split
        · rename_i hused
          split
          · rename_i hidx
            rw [WP.spec_ok]
            rw [← hinv, hdrop, List.find?_cons]
            have hm : matchesIndex index (a.places.val[place.val]'hlt_len) = true := by
              rw [← harr]
              simp [matchesIndex, hused, hidx]
            simp [hm, harr]
          · rename_i hidx
            step as ⟨place1, hplace1⟩
            refine ⟨?_, by rw [hplace1, hnext]; omega⟩
            rw [← hinv, hdrop, List.find?_cons, hplace1, hnext]
            have hm : matchesIndex index (a.places.val[place.val]'hlt_len) = false := by
              rw [← harr]
              simp [matchesIndex, hidx]
            simp [hm]
        · rename_i hused
          have hused' : arrival.used = false := by simpa using hused
          step as ⟨place1, hplace1⟩
          refine ⟨?_, by rw [hplace1, hnext]; omega⟩
          rw [← hinv, hdrop, List.find?_cons, hplace1, hnext]
          have hm : matchesIndex index (a.places.val[place.val]'hlt_len) = false := by
            rw [← harr]
            simp [matchesIndex, hused']
          simp [hm]
      · rename_i hge
        have hge' : a.places.val.length ≤ place.val := by scalar_tac
        rw [WP.spec_ok]
        rw [← hinv, List.drop_eq_nil_of_le hge']
        rfl
    · rfl
  simpa [lookup] using hloop 0#usize

theorem find_total (a : arrivals.Arrivals K) (index : Std.U64) :
    arrivals.Arrivals.find a index ⦃ _ => True ⦄ :=
  WP.spec_mono (find_spec a index) (fun _ _ => trivial)

private theorem find?_set_of_none {α : Type} (l : List α) (p : α → Bool) (i : ℕ) (x : α)
    (hnone : l.find? p = none) (hi : i < l.length) (hpx : p x = true) :
    (l.set i x).find? p = some x := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    rw [List.find?_cons] at hnone
    have hphd : p hd = false := by
      cases h : p hd
      · rfl
      · simp [h] at hnone
    rw [hphd] at hnone
    cases i with
    | zero =>
      simp [List.set, hpx]
    | succ n =>
      simp only [List.set, List.find?_cons, hphd]
      exact ih n hnone (by simpa using hi)

/-- Recording an arrival:
- If `index` is already recorded, the table is unchanged (preserving the first
  arrival).
- Otherwise, when `a.next < K`, the entry is written to slot `a.next`, `next`
  advances modulo `K` (staying `< K`), and `lookup` immediately finds `time`. -/
theorem record_spec (a : arrivals.Arrivals K) (index : Std.U64) (time : Std.I64) :
    arrivals.Arrivals.record a index time ⦃ a' =>
      (lookup a index ≠ none → a' = a)
      ∧ (lookup a index = none → a.next.val < K.val →
          a'.places.val = a.places.val.set a.next.val { used := true, index, time }
          ∧ a'.next.val = (a.next.val + 1) % K.val
          ∧ a'.next.val < K.val
          ∧ lookup a' index = some time)
      ∧ (K.val > 0 → a'.next.val < K.val ∨ lookup a index ≠ none) ⦄ := by
  unfold arrivals.Arrivals.record
  step with find_spec a index as ⟨o, ho⟩
  cases hlk : lookup a index with
  | some t =>
    rw [hlk] at ho
    rw [ho]
    simp only [Option.isSome, ↓reduceIte]
    rw [WP.spec_ok]
    refine ⟨fun _ => rfl, (fun h => by cases h), (fun _ => Or.inr (by simp))⟩
  | none =>
    rw [hlk] at ho
    rw [ho]
    simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte,
      Array.to_slice_mut, lift, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
      bind_ok, Std.uncurry]
    have hlen : a.places.val.length = K.val := a.places.property
    have hval : a.places.to_slice.val = a.places.val := by simp [Array.to_slice]
    have hidx : a.places.to_slice[a.next]? = a.places.val[a.next.val]? := by
      change a.places.to_slice.val[a.next.val]? = a.places.val[a.next.val]?
      rw [hval]
    rw [hidx]
    have hrem_lt : ∀ (i : Std.Usize), K.val > 0 →
        (core.option.Option.unwrap_or (Usize.checked_rem i K) 0#usize).val = i.val % K.val := by
      intro i hK
      have hspec := Usize.checked_rem_bv_spec i K
      cases hr : Usize.checked_rem i K with
      | none =>
        rw [hr] at hspec
        omega
      | some r =>
        rw [hr] at hspec
        simpa [core.option.Option.unwrap_or] using hspec.2.1
    by_cases hlt : a.next.val < K.val
    · have hlt' : a.next.val < a.places.val.length := by omega
      rw [List.getElem?_eq_getElem hlt']
      simp only [bind_ok]
      have hinc : (core.num.Usize.saturating_add a.next 1#usize).val = a.next.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      have hKpos : 0 < K.val := by omega
      have hrem := hrem_lt (core.num.Usize.saturating_add a.next 1#usize) hKpos
      rw [hinc] at hrem
      have hplaces :
          (a.places.from_slice
            (a.places.to_slice.set_opt a.next (some { used := true, index, time }))).val =
          a.places.val.set a.next.val { used := true, index, time } := by
        simp [Array.from_slice, Array.to_slice, Slice.set_opt, Unisono.Lists.set_opt_some]
      have hfind_none : a.places.val.find? (matchesIndex index) = none := by
        unfold lookup at hlk
        cases hf : a.places.val.find? (matchesIndex index) with
        | none => rfl
        | some v => simp [hf] at hlk
      have hnew_lookup :
          ((a.places.val.set a.next.val { used := true, index, time }).find?
              (matchesIndex index)).map (·.time) = some time := by
        rw [find?_set_of_none a.places.val (matchesIndex index) a.next.val
            { used := true, index, time } hfind_none hlt' (by simp [matchesIndex])]
        rfl
      rw [WP.spec_ok]
      dsimp only
      refine ⟨fun h => absurd rfl h, fun _ _ => ⟨hplaces, hrem, ?_, ?_⟩, fun _ => Or.inl ?_⟩
      · rw [hrem]; exact Nat.mod_lt _ hKpos
      · unfold lookup
        rw [hplaces]
        exact hnew_lookup
      · rw [hrem]; exact Nat.mod_lt _ hKpos
    · rw [List.getElem?_eq_none (by omega)]
      simp only [bind_ok]
      rw [WP.spec_ok]
      dsimp only
      refine ⟨fun h => absurd rfl h, fun _ h => absurd h hlt, fun hKpos => Or.inl ?_⟩
      have hrem := hrem_lt (core.num.Usize.saturating_add a.next 1#usize) hKpos
      rw [hrem]
      exact Nat.mod_lt _ hKpos

@[step]
theorem record_total (a : arrivals.Arrivals K) (index : Std.U64) (time : Std.I64) :
    arrivals.Arrivals.record a index time ⦃ _ => True ⦄ :=
  WP.spec_mono (record_spec a index time) (fun _ _ => trivial)

end Unisono.Arrivals
