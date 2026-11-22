/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Presence.Mark

/-!
# Presence bitmap: advancing the stretch and querying runs

Clearing and advancing the active stretch (`clear`, `advance`), contiguous
held/missing run queries (`run`, `gap`), and initialization (`new`, `restart`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Presence

variable {N : Std.Usize}

/-! ## Moving the stretch forward -/

theorem clear_loop_spec (p : presence.Presence N) :
    presence.Presence.clear_loop p 0#usize ⦃ r =>
      r.base = p.base ∧ ∀ j, bitOf r j = false ⦄ := by
  unfold presence.Presence.clear_loop
  apply loop.spec_decr_nat
    (measure := fun x : presence.Presence N × Std.Usize => N.val - x.2.val)
    (inv := fun x : presence.Presence N × Std.Usize =>
      x.2.val ≤ N.val ∧ x.1.base = p.base
      ∧ ∀ k, k < x.2.val → x.1.words.val.getD k 0#u64 = 0#u64)
  · rintro ⟨s, w⟩ ⟨hw, hbase, hzero⟩
    dsimp only at hw hbase hzero
    unfold presence.Presence.clear_loop.body
    simp only
    have hlen : s.words.val.length = N.val := by scalar_tac
    split
    · have hlt : w.val < N.val := by scalar_tac
      step as ⟨s1, hb1, hw1⟩
      step as ⟨w1, hw1v⟩
      have hv : w1.val = w.val + 1 := by
        rw [hw1v]; exact Usize.saturating_add_val _ _ (by scalar_tac)
      refine ⟨by omega, hb1.trans hbase, ?_, by omega⟩
      intro k hk
      rw [hw1]
      by_cases hkw : k = w.val
      · subst hkw
        simp [List.getD, hlen, hlt]
      · have hkw' : ¬ w.val = k := fun h => hkw h.symm
        have := hzero k (by omega)
        simpa [List.getD, hkw'] using this
    · have hwN : w.val = N.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨hbase, fun j => ?_⟩
      unfold bitOf
      by_cases hN : N.val = 0
      · have hnil : s.words.val = [] := List.eq_nil_of_length_eq_zero (by omega)
        simp [hnil]
      · rw [hzero _ (by rw [hwN]; exact Nat.mod_lt _ (by omega))]
        simp
  · dsimp only
    refine ⟨by scalar_tac, rfl, ?_⟩
    intro k hk
    have h0 : (0#usize).val = 0 := by rfl
    omega

/-- `clear` leaves no bit set. -/
@[step]
theorem clear_spec (p : presence.Presence N) :
    presence.Presence.clear p ⦃ r => r.base = p.base ∧ ∀ j, bitOf r j = false ⦄ := by
  unfold presence.Presence.clear
  exact clear_loop_spec p

theorem advance_loop_spec (p : presence.Presence N) (target : Std.U64) (hN : 0 < N.val)
    (hle : p.base.val ≤ target.val) :
    presence.Presence.advance_loop p target p.base ⦃ r =>
      r.base = p.base
      ∧ ∀ j, bitOf r j = true ↔
          bitOf p j = true
          ∧ ∀ k, p.base.val ≤ k → k < target.val → ¬ SamePlace N.val k j ⦄ := by
  unfold presence.Presence.advance_loop
  apply loop.spec_decr_nat
    (measure := fun x : presence.Presence N × Std.U64 => target.val - x.2.val)
    (inv := fun x : presence.Presence N × Std.U64 =>
      p.base.val ≤ x.2.val ∧ x.2.val ≤ target.val ∧ x.1.base = p.base
      ∧ ∀ j, bitOf x.1 j = true ↔
          bitOf p j = true ∧ ∀ k, p.base.val ≤ k → k < x.2.val → ¬ SamePlace N.val k j)
  · rintro ⟨s, index⟩ ⟨hlo, hhi, hbase, hbits⟩
    dsimp only at hlo hhi hbase hbits
    unfold presence.Presence.advance_loop.body
    simp only
    split
    · have hlt : index.val < target.val := by scalar_tac
      have ht : target.val ≤ U64.max := by scalar_tac
      step as ⟨was, s1, hb1, h0, h1⟩
      obtain ⟨-, hput⟩ := h1 hN
      step as ⟨index1, hindex1⟩
      have hv : index1.val = index.val + 1 := by
        rw [hindex1]; exact U64.saturating_add_one_val index target.val hlt ht
      refine ⟨by omega, by omega, hb1.trans hbase, ?_, by omega⟩
      intro j
      rw [hput j]
      by_cases hs : SamePlace N.val index.val j
      · simp only [hs, ↓reduceIte, Bool.false_eq_true, false_iff, not_and]
        intro _ hall
        exact hall index.val hlo (by omega) hs
      · simp only [hs, ↓reduceIte]
        rw [hbits j]
        constructor
        · rintro ⟨hb, hall⟩
          refine ⟨hb, fun k hk1 hk2 => ?_⟩
          by_cases hki : k = index.val
          · subst hki; exact hs
          · exact hall k hk1 (by omega)
        · rintro ⟨hb, hall⟩
          exact ⟨hb, fun k hk1 hk2 => hall k hk1 (by omega)⟩
    · have hit : index.val = target.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [← hit]
      exact ⟨hbase, hbits⟩
  · dsimp only
    refine ⟨le_refl _, hle, rfl, fun j => ?_⟩
    constructor
    · intro hb
      exact ⟨hb, fun k hk1 hk2 => by omega⟩
    · exact fun h => h.1

/-- Moving the start of the stretch forward to `target`. The start is the
later of the old start and `target`, and a frame is held afterwards exactly
when it was held before and is not before `target`: nothing behind the new
start is held, nothing ahead of it is lost, and the indices that the stretch
newly covers hold nothing. -/
@[step]
theorem advance_spec (p : presence.Presence N) (target : Std.U64) :
    presence.Presence.advance p target ⦃ r =>
      r.base.val = max p.base.val target.val
      ∧ ∀ j, Held r j ↔ target.val ≤ j ∧ Held p j ⦄ := by
  unfold presence.Presence.advance
  split
  · rename_i hle
    have hle' : target.val ≤ p.base.val := by scalar_tac
    simp only [WP.spec_ok]
    refine ⟨by omega, fun j => ?_⟩
    constructor
    · intro h
      exact ⟨by have := h.1.1; omega, h⟩
    · exact fun h => h.2
  · rename_i hgt
    have hgt' : p.base.val < target.val := by scalar_tac
    have ht : target.val ≤ U64.max := by scalar_tac
    step as ⟨i, hi⟩
    have hiv : i.val = target.val - p.base.val := by
      rw [hi]; exact U64.wrapping_sub_val _ _ (by omega)
    step as ⟨w, hw⟩
    split
    · rename_i hfar
      have hfar' : p.base.val + widthOf N.val ≤ target.val := by scalar_tac
      step as ⟨s1, hb1, hclear⟩
      refine ⟨by simp; omega, fun j => ?_⟩
      constructor
      · rintro ⟨-, hb⟩
        have : bitOf s1 j = true := hb
        rw [hclear j] at this
        cases this
      · rintro ⟨hj, ⟨-, hc2, -⟩, -⟩
        omega
    · rename_i hnear
      have hnear' : target.val < p.base.val + widthOf N.val := by scalar_tac
      have hwle := widthOf_le N.val
      have hN : 0 < N.val := by omega
      have hwidth : widthOf N.val = 64 * N.val := by
        unfold widthOf at hnear' ⊢
        split at hnear'
        · rename_i hfit; simp [hfit]
        · omega
      step with advance_loop_spec p target hN (by omega) as ⟨s1, hb1, hbits⟩
      refine ⟨by simp; omega, fun j => ?_⟩
      have hbit : bitOf { s1 with base := target } j = bitOf s1 j := rfl
      unfold Held
      rw [hbit, hbits j]
      unfold Covered
      simp only
      constructor
      · rintro ⟨⟨hc1, hc2, hc3⟩, hb, hall⟩
        refine ⟨hc1, ⟨by omega, ?_, hc3⟩, hb⟩
        by_contra hout
        have hk : SamePlace N.val (j - 64 * N.val) j := by
          have := SamePlace.add_width N.val (j - 64 * N.val)
          rwa [Nat.sub_add_cancel (by omega)] at this
        exact hall (j - 64 * N.val) (by omega) (by omega) hk
      · rintro ⟨hj, ⟨hc1, hc2, hc3⟩, hb⟩
        refine ⟨⟨hj, by omega, hc3⟩, hb, fun k hk1 hk2 hs => ?_⟩
        have := hs.eq (by omega) (by omega)
        omega

/-! ## Frames held without a break -/

theorem run_loop_spec (p : presence.Presence N) (start : Std.U64) (limit : Std.U32) :
    presence.Presence.run_loop p start limit 0#u32 ⦃ r =>
      r.val ≤ limit.val
      ∧ (∀ k, k < r.val → Held p (start.val + k))
      ∧ (r.val < limit.val → ¬ Held p (start.val + r.val)) ⦄ := by
  unfold presence.Presence.run_loop
  apply loop.spec_decr_nat
    (measure := fun count : Std.U32 => limit.val - count.val)
    (inv := fun count : Std.U32 =>
      count.val ≤ limit.val ∧ ∀ k, k < count.val → Held p (start.val + k))
  · rintro count ⟨hle, hall⟩
    unfold presence.Presence.run_loop.body
    have hl : limit.val ≤ U32.max := by scalar_tac
    split
    · have hlt : count.val < limit.val := by scalar_tac
      step as ⟨b, hb⟩
      split
      · rename_i hheld
        step as ⟨count1, hcount1⟩
        have hv : count1.val = count.val + 1 := by
          rw [hcount1]; exact U32.saturating_add_one_val count limit.val hlt hl
        refine ⟨by omega, ?_, by omega⟩
        intro k hk
        by_cases hkc : k = count.val
        · subst hkc
          exact hb.mp hheld
        · exact hall k (by omega)
      · rename_i hnot
        simp only [WP.spec_ok]
        exact ⟨hle, hall, fun _ h => hnot (hb.mpr h)⟩
    · have : ¬ count.val < limit.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨hle, hall, fun h => absurd h this⟩
  · refine ⟨by scalar_tac, fun k hk => ?_⟩
    have h0 : (0#u32).val = 0 := by rfl
    omega

/-- `run` counts the frames held without a break from an index on: every one
of that many frames is held, and the next one is not, unless the count has
reached the limit. -/
@[step]
theorem run_spec (p : presence.Presence N) (start : Std.U64) (limit : Std.U32) :
    presence.Presence.run p start limit ⦃ r =>
      r.val ≤ limit.val
      ∧ (∀ k, k < r.val → Held p (start.val + k))
      ∧ (r.val < limit.val → ¬ Held p (start.val + r.val)) ⦄ := by
  unfold presence.Presence.run
  exact run_loop_spec p start limit

theorem gap_loop_spec (p : presence.Presence N) (start : Std.U64) (limit : Std.U32) :
    presence.Presence.gap_loop p start limit 0#u32 ⦃ r =>
      r.val ≤ limit.val
      ∧ (∀ k, k < r.val → ¬ Held p (start.val + k))
      ∧ (r.val < limit.val → Held p (start.val + r.val)) ⦄ := by
  unfold presence.Presence.gap_loop
  apply loop.spec_decr_nat
    (measure := fun count : Std.U32 => limit.val - count.val)
    (inv := fun count : Std.U32 =>
      count.val ≤ limit.val ∧ ∀ k, k < count.val → ¬ Held p (start.val + k))
  · rintro count ⟨hle, hall⟩
    unfold presence.Presence.gap_loop.body
    have hl : limit.val ≤ U32.max := by scalar_tac
    split
    · have hlt : count.val < limit.val := by scalar_tac
      step as ⟨b, hb⟩
      split
      · rename_i hheld
        simp only [WP.spec_ok]
        exact ⟨hle, hall, fun _ => hb.mp hheld⟩
      · rename_i hnot
        step as ⟨count1, hcount1⟩
        have hv : count1.val = count.val + 1 := by
          rw [hcount1]; exact U32.saturating_add_one_val count limit.val hlt hl
        refine ⟨by omega, ?_, by omega⟩
        intro k hk
        by_cases hkc : k = count.val
        · subst hkc
          exact fun h => hnot (hb.mpr h)
        · exact hall k (by omega)
    · have : ¬ count.val < limit.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨hle, hall, fun h => absurd h this⟩
  · refine ⟨by scalar_tac, fun k hk => ?_⟩
    have h0 : (0#u32).val = 0 := by rfl
    omega

/-- `gap` counts the frames that are not held without a break from an index
on: none of that many frames is held, and the next one is, unless the count
has reached the limit. -/
@[step]
theorem gap_spec (p : presence.Presence N) (start : Std.U64) (limit : Std.U32) :
    presence.Presence.gap p start limit ⦃ r =>
      r.val ≤ limit.val
      ∧ (∀ k, k < r.val → ¬ Held p (start.val + k))
      ∧ (r.val < limit.val → Held p (start.val + r.val)) ⦄ := by
  unfold presence.Presence.gap
  exact gap_loop_spec p start limit

/-- A stretch that is started anew holds nothing. -/
@[step]
theorem restart_spec (p : presence.Presence N) (base : Std.U64) :
    presence.Presence.restart p base ⦃ r => r.base = base ∧ ∀ j, ¬ Held r j ⦄ := by
  unfold presence.Presence.restart
  step as ⟨s1, hb1, hclear⟩
  intro j h
  have hb : bitOf s1 j = true := h.2
  rw [hclear j] at hb
  cases hb

/-- A new stretch holds nothing. -/
theorem new_spec (N : Std.Usize) :
    presence.Presence.new N ⦃ r => r.base.val = 0 ∧ ∀ j, ¬ Held r j ⦄ := by
  unfold presence.Presence.new
  simp only [WP.spec_ok]
  refine ⟨rfl, fun j h => ?_⟩
  have hb : bitOf ({ words := Array.repeat N 0#u64, base := 0#u64 } : presence.Presence N) j
      = true := h.2
  unfold bitOf at hb
  simp [Array.repeat, List.getD] at hb

end Unisono.Presence
