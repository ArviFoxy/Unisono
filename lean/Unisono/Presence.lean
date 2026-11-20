/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Lists

/-!
# Which frames a receiver holds

What the functions of `unisono_core::presence` compute, stated for the set of
held indices: an index is held when it lies in the stretch and its bit is set.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Presence

/-! ## One bit of a word -/

/-- The word with only bit `k` set has bit `j` set exactly when `j` is `k`. -/
theorem getLsbD_one_shiftLeft (k j : ℕ) (hk : k < 64) :
    (1#64 <<< k).getLsbD j = decide (j = k) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

/-- A word has something in common with the word of bit `k` exactly when its
bit `k` is set. -/
theorem and_one_shiftLeft_ne_zero (w : BitVec 64) (k : ℕ) (hk : k < 64) :
    (w &&& (1#64 <<< k) ≠ 0#64) ↔ w.getLsbD k = true := by
  constructor
  · intro h
    by_contra hw
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [BitVec.getLsbD_and, getLsbD_one_shiftLeft _ _ hk]
    by_cases hik : i = k
    · subst hik
      simp [hw]
    · simp [hik]
  · intro hw h
    have h' := congrArg (fun v => v.getLsbD k) h
    simp [BitVec.getLsbD_and, getLsbD_one_shiftLeft _ _ hk, hw] at h'

/-- Setting bit `k` of a word sets it and leaves the other bits. -/
theorem getLsbD_or_one_shiftLeft (w : BitVec 64) (k j : ℕ) (hk : k < 64) :
    (w ||| (1#64 <<< k)).getLsbD j = (w.getLsbD j || decide (j = k)) := by
  rw [BitVec.getLsbD_or, getLsbD_one_shiftLeft _ _ hk]

/-- Clearing bit `k` of a word clears it and leaves the other bits. -/
theorem getLsbD_and_not_one_shiftLeft (w : BitVec 64) (k j : ℕ) (hk : k < 64) :
    (w &&& ~~~(1#64 <<< k)).getLsbD j = (w.getLsbD j && !decide (j = k)) := by
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, getLsbD_one_shiftLeft _ _ hk]
  by_cases hj : j < 64
  · simp [hj]
  · have : w.getLsbD j = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [this]

/-! ## The stretch and its bits -/

variable {N : Std.Usize}

/-- The number of indices in a stretch of `n` words: 64 for each word, and
none when that number does not fit in 64 bits. -/
def widthOf (n : ℕ) : ℕ := if 64 * n ≤ U64.max then 64 * n else 0

/-- Index `i` lies in the stretch. -/
def Covered (p : presence.Presence N) (i : ℕ) : Prop :=
  p.base.val ≤ i ∧ i < p.base.val + widthOf N.val ∧ i ≤ U64.max

instance (p : presence.Presence N) (i : ℕ) : Decidable (Covered p i) := by
  unfold Covered; infer_instance

/-- The bit of index `i`, wherever the stretch is. -/
def bitOf (p : presence.Presence N) (i : ℕ) : Bool :=
  (p.words.val.getD (i / 64 % N.val) 0#u64).bv.getLsbD (i % 64)

/-- Index `i` is held: it lies in the stretch and its bit is set. -/
def Held (p : presence.Presence N) (i : ℕ) : Prop := Covered p i ∧ bitOf p i = true

/-- The bits of two indices are at the same place. -/
def SamePlace (n i j : ℕ) : Prop := i / 64 % n = j / 64 % n ∧ i % 64 = j % 64

instance (n i j : ℕ) : Decidable (SamePlace n i j) := by unfold SamePlace; infer_instance

@[step]
theorem width_spec (p : presence.Presence N) :
    presence.Presence.width p ⦃ r => r.val = widthOf N.val ⦄ := by
  unfold presence.Presence.width
  step as ⟨i, hi⟩
  step as ⟨o, ho⟩
  have hiv : i.val = N.val := by rw [hi]; exact Usize.cast_U64_val N
  cases o with
  | none =>
    simp only at ho
    have : ¬ 64 * N.val ≤ U64.max := by omega
    simp [widthOf, this, core.option.Option.unwrap_or]
  | some z =>
    simp only at ho
    obtain ⟨h1, h2, -⟩ := ho
    have : 64 * N.val ≤ U64.max := by omega
    simp [widthOf, this, core.option.Option.unwrap_or]
    omega

@[step]
theorem covers_spec (p : presence.Presence N) (index : Std.U64) :
    presence.Presence.covers p index ⦃ r => r = decide (Covered p index.val) ⦄ := by
  unfold presence.Presence.covers
  have hb : index.val ≤ U64.max := by scalar_tac
  split
  · rename_i hge
    have hge' : p.base.val ≤ index.val := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨w, hw⟩
    have hsub : i.val = index.val - p.base.val := by
      rw [hi]; exact U64.wrapping_sub_val _ _ hge'
    have hiff : i < w ↔ Covered p index.val := by
      unfold Covered
      constructor
      · intro h
        have : i.val < w.val := by scalar_tac
        omega
      · rintro ⟨-, h2, -⟩
        have : i.val < w.val := by omega
        scalar_tac
    simp [hiff]
  · rename_i hlt
    have hlt' : index.val < p.base.val := by scalar_tac
    have : ¬ Covered p index.val := by
      unfold Covered; omega
    simp [this]

@[step]
theorem place_spec (N : Std.Usize) (index : Std.U64) :
    presence.Presence.place N index ⦃ r =>
      (N.val = 0 → r = none)
      ∧ (0 < N.val → ∃ k mask, r = some (k, mask) ∧ k.val = index.val / 64 % N.val
          ∧ mask.bv = 1#64 <<< (index.val % 64)) ⦄ := by
  unfold presence.Presence.place
  step as ⟨i, hi⟩
  step as ⟨n, hn⟩
  step as ⟨o, ho⟩
  have hnv : n.val = N.val := by rw [hn]; exact Usize.cast_U64_val N
  cases o with
  | none =>
    simp only at ho
    simp only [WP.spec_ok, true_and, implies_true]
    omega
  | some word =>
    simp only at ho
    obtain ⟨h0, hword, -⟩ := ho
    have hwlt : word.val < N.val := by
      rw [hword, hnv]; exact Nat.mod_lt _ (by omega)
    simp only
    step as ⟨k, hk⟩
    step as ⟨r, hr⟩
    step as ⟨bit, hbit⟩
    step as ⟨m, hm⟩
    have hkv : k.val = word.val := by
      rw [hk]; exact U64.cast_Usize_val _ (by scalar_tac)
    have hbv : bit.val = index.val % 64 := by
      rw [hbit, U64.cast_U32_val _ (by scalar_tac)]; exact hr
    refine ⟨by omega, fun _ => ⟨k, m, rfl, ?_, ?_⟩⟩
    · rw [hkv, hword, hi, hnv]
    · have hmod : index.val % 64 % 64 = index.val % 64 := Nat.mod_mod _ _
      rw [hm, core.num.U64.wrapping_shl_bv_eq, hbv, hmod]
      rfl

/-- The word at a place, or zero where there is none. -/
@[step]
theorem word_spec (p : presence.Presence N) (k : Std.Usize) :
    presence.Presence.word p k ⦃ r => r = p.words.val.getD k.val 0#u64 ⦄ := by
  unfold presence.Presence.word
  have hsl : (Array.to_slice p.words).val = p.words.val := by simp [Array.to_slice]
  simp only [lift, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  rw [Slice.getElem?_Usize_eq, hsl]
  cases h : p.words.val[k.val]? <;> simp [List.getD, h]

/-- Replacing the word at a place changes that word, if there is one, and
nothing else. -/
@[step]
theorem set_word_spec (p : presence.Presence N) (k : Std.Usize) (bits : Std.U64) :
    presence.Presence.set_word p k bits ⦃ r =>
      r.base = p.base ∧ r.words.val = p.words.val.set k.val bits ⦄ := by
  unfold presence.Presence.set_word
  simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
    core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
  have hlen : p.words.val.length = N.val := by scalar_tac
  have hsl : (Array.to_slice p.words).val = p.words.val := by simp [Array.to_slice]
  by_cases hi : k.val < N.val
  · have hget : (Array.to_slice p.words)[k]? = some (p.words.val[k.val]'(by omega)) := by
      rw [Slice.getElem?_Usize_eq, hsl]
      exact List.getElem?_eq_getElem (by omega)
    simp only [hget, WP.spec_ok, true_and]
    rw [Array.from_slice_val _ _ (by simp [Slice.set_opt, hsl, hlen])]
    simp [Slice.set_opt, hsl, Unisono.Lists.set_opt_some]
  · have hget : (Array.to_slice p.words)[k]? = none := by
      rw [Slice.getElem?_Usize_eq, hsl]
      exact List.getElem?_eq_none (by omega)
    simp only [hget, WP.spec_ok, true_and]
    rw [Array.from_slice_val _ _ (by simp [Slice.set_opt, hsl, hlen])]
    simp [Slice.set_opt, hsl, Unisono.Lists.set_opt_none]
    rw [List.set_eq_of_length_le (by omega)]

/-- A word is not zero exactly when its bits are not all clear. -/
theorem bne_zero_iff (a : Std.U64) : (a != 0#u64) = true ↔ UScalar.bv a ≠ 0#64 := by
  rw [bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq]
  rfl

/-- What the function reads is the bit of the index. -/
@[step]
theorem bit_spec (p : presence.Presence N) (index : Std.U64) :
    presence.Presence.bit p index ⦃ r => r = bitOf p index.val ⦄ := by
  unfold presence.Presence.bit
  step as ⟨o, ho0, ho1⟩
  by_cases hN : N.val = 0
  · have := ho0 hN
    subst this
    have hlen : p.words.val.length = N.val := by scalar_tac
    have hnil : p.words.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [bitOf, hnil]
  · obtain ⟨k, mask, rfl, hk, hmask⟩ := ho1 (by omega)
    simp only [Std.uncurry]
    step as ⟨w, hw⟩
    step as ⟨a, ha, habv⟩
    have hlt : index.val % 64 < 64 := Nat.mod_lt _ (by omega)
    simp only [U64.bv] at habv hmask
    rw [Bool.eq_iff_iff, bne_zero_iff, habv, hmask, and_one_shiftLeft_ne_zero _ _ hlt, hw, hk]
    rfl

/-- After one word is replaced, the bit of an index is read from the new
word if that is the index's word, and is unchanged otherwise. -/
theorem bitOf_set (p p' : presence.Presence N) (k : ℕ) (w : Std.U64) (hk : k < N.val)
    (hw : p'.words.val = p.words.val.set k w) (j : ℕ) :
    bitOf p' j = if j / 64 % N.val = k then (UScalar.bv w).getLsbD (j % 64) else bitOf p j := by
  have hlen : p.words.val.length = N.val := by scalar_tac
  unfold bitOf
  rw [hw]
  by_cases hj : j / 64 % N.val = k
  · simp [hj, List.getD, hlen, hk]
  · have hj' : ¬ k = j / 64 % N.val := fun h => hj h.symm
    simp [hj, hj', List.getD]

/-- Setting the bit of index `i` within its word, read at index `j`. -/
theorem ite_or_samePlace (n i j : ℕ) (old : Bool) :
    (if j / 64 % n = i / 64 % n then (old || decide (j % 64 = i % 64)) else old)
      = if SamePlace n i j then true else old := by
  unfold SamePlace
  by_cases h1 : j / 64 % n = i / 64 % n
  · by_cases h2 : j % 64 = i % 64
    · simp [h1, h2]
    · have h2' : ¬ i % 64 = j % 64 := fun h => h2 h.symm
      simp [h1, h2, h2']
  · have h1' : ¬ i / 64 % n = j / 64 % n := fun h => h1 h.symm
    simp [h1, h1']

/-- Clearing the bit of index `i` within its word, read at index `j`. -/
theorem ite_and_not_samePlace (n i j : ℕ) (old : Bool) :
    (if j / 64 % n = i / 64 % n then (old && !decide (j % 64 = i % 64)) else old)
      = if SamePlace n i j then false else old := by
  unfold SamePlace
  by_cases h1 : j / 64 % n = i / 64 % n
  · by_cases h2 : j % 64 = i % 64
    · simp [h1, h2]
    · have h2' : ¬ i % 64 = j % 64 := fun h => h2 h.symm
      simp [h1, h2, h2']
  · have h1' : ¬ i / 64 % n = j / 64 % n := fun h => h1 h.symm
    simp [h1, h1']

/-- `put` sets or clears the bit of an index, says what the bit was, and
leaves the bit at every other place. Without words it does nothing. -/
@[step]
theorem put_spec (p : presence.Presence N) (index : Std.U64) (h : Bool) :
    presence.Presence.put p index h ⦃ r =>
      r.2.base = p.base
      ∧ (N.val = 0 → r = (false, p))
      ∧ (0 < N.val → r.1 = bitOf p index.val
          ∧ ∀ j, bitOf r.2 j = if SamePlace N.val index.val j then h else bitOf p j) ⦄ := by
  unfold presence.Presence.put
  step as ⟨o, ho0, ho1⟩
  by_cases hN : N.val = 0
  · have := ho0 hN
    subst this
    simp [hN]
  · obtain ⟨k, mask, rfl, hk, hmask⟩ := ho1 (by omega)
    clear ho0
    have hlt : index.val % 64 < 64 := Nat.mod_lt _ (by omega)
    have hkN : k.val < N.val := by rw [hk]; exact Nat.mod_lt _ (by omega)
    simp only [U64.bv] at hmask
    simp only [Std.uncurry]
    step as ⟨bits, hbits⟩
    have hwas : ∀ a : Std.U64, UScalar.bv a = UScalar.bv bits &&& UScalar.bv mask →
        (a != 0#u64) = bitOf p index.val := by
      intro a habv
      rw [Bool.eq_iff_iff, bne_zero_iff, habv, hmask, and_one_shiftLeft_ne_zero _ _ hlt, hbits,
        hk]
      rfl
    have hbit : ∀ j, j / 64 % N.val = index.val / 64 % N.val →
        (UScalar.bv bits).getLsbD (j % 64) = bitOf p j := by
      intro j hj
      rw [hbits, hk, ← hj]
      rfl
    split
    · rename_i hh
      step as ⟨i, hi, hibv⟩
      step as ⟨p1, hp1b, hp1w⟩
      step as ⟨a, ha, habv⟩
      refine ⟨hp1b, fun h0 => absurd h0 hN, fun _ => ⟨hwas a habv, fun j => ?_⟩⟩
      rw [bitOf_set p p1 k.val i hkN hp1w j, hh, ← ite_or_samePlace, hk]
      by_cases hj : j / 64 % N.val = index.val / 64 % N.val
      · simp only [hj, ↓reduceIte]
        rw [hibv, hmask, getLsbD_or_one_shiftLeft _ _ _ hlt, hbit j hj]
      · simp only [hj, ↓reduceIte]
    · rename_i hh
      have hh' : h = false := by simpa using hh
      step as ⟨nm, hnm⟩
      step as ⟨i, hi, hibv⟩
      step as ⟨p1, hp1b, hp1w⟩
      step as ⟨a, ha, habv⟩
      have hnmbv : UScalar.bv nm = ~~~ UScalar.bv mask := by rw [hnm]; rfl
      refine ⟨hp1b, fun h0 => absurd h0 hN, fun _ => ⟨hwas a habv, fun j => ?_⟩⟩
      rw [bitOf_set p p1 k.val i hkN hp1w j, hh', ← ite_and_not_samePlace, hk]
      by_cases hj : j / 64 % N.val = index.val / 64 % N.val
      · simp only [hj, ↓reduceIte]
        rw [hibv, hnmbv, hmask, getLsbD_and_not_one_shiftLeft _ _ _ hlt, hbit j hj]
      · simp only [hj, ↓reduceIte]

/-- `held` says whether an index is held. -/
@[step]
theorem held_spec (p : presence.Presence N) (index : Std.U64) :
    presence.Presence.held p index ⦃ r => r = true ↔ Held p index.val ⦄ := by
  unfold presence.Presence.held
  step as ⟨b, hb⟩
  split
  · rename_i hc
    have hcov : Covered p index.val := by simpa [hb] using hc
    step as ⟨r, hr⟩
    simp [Held, hcov, hr]
  · rename_i hc
    have hcov : ¬ Covered p index.val := by simpa [hb] using hc
    simp [Held, hcov]

/-! ## One place for each index of the stretch -/

theorem SamePlace.refl (n i : ℕ) : SamePlace n i i := ⟨rfl, rfl⟩

theorem SamePlace.symm {n i j : ℕ} (h : SamePlace n i j) : SamePlace n j i :=
  ⟨h.1.symm, h.2.symm⟩

/-- Two indices less than `64 * n` apart have different places. -/
theorem SamePlace.eq {n i j : ℕ} (h : SamePlace n i j) (hij : i ≤ j) (hlt : j < i + 64 * n) :
    i = j := by
  obtain ⟨h1, h2⟩ := h
  have hd : j / 64 - i / 64 < n := by omega
  have hmod : (j / 64 - i / 64) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq h1.symm
  rw [Nat.mod_eq_of_lt hd] at hmod
  omega

/-- The index `64 * n` further on has the same place. -/
theorem SamePlace.add_width (n i : ℕ) : SamePlace n i (i + 64 * n) := by
  refine ⟨?_, by omega⟩
  have : (i + 64 * n) / 64 = i / 64 + n := by omega
  rw [this, Nat.add_mod_right]

theorem widthOf_le (n : ℕ) : widthOf n ≤ 64 * n := by
  unfold widthOf
  split <;> omega

/-- Two indices of the stretch with the same place are the same index. -/
theorem Covered.eq_of_samePlace {p : presence.Presence N} {i j : ℕ} (hi : Covered p i)
    (hj : Covered p j) (h : SamePlace N.val i j) : i = j := by
  have hw := widthOf_le N.val
  obtain ⟨hi1, hi2, -⟩ := hi
  obtain ⟨hj1, hj2, -⟩ := hj
  rcases Nat.le_total i j with hij | hji
  · exact h.eq hij (by omega)
  · exact (h.symm.eq hji (by omega)).symm

/-- A stretch that covers an index has words. -/
theorem Covered.pos {p : presence.Presence N} {i : ℕ} (hi : Covered p i) : 0 < N.val := by
  have hw := widthOf_le N.val
  obtain ⟨hi1, hi2, -⟩ := hi
  omega

/-- Whether an index lies in the stretch depends on the start of the stretch
alone. -/
theorem covered_congr {p q : presence.Presence N} (h : q.base = p.base) (i : ℕ) :
    Covered q i ↔ Covered p i := by
  simp only [Covered, h]

/-! ## The arrival of frames -/

/-- What becomes of the frame at index `i` when it arrives. -/
def outcomeOf (p : presence.Presence N) (i : ℕ) : presence.Outcome :=
  if Covered p i then (if bitOf p i then presence.Outcome.Duplicate else presence.Outcome.Stored)
  else if i < p.base.val then presence.Outcome.Late
  else presence.Outcome.Early

/-- The arrival of one frame: its outcome is the one its index has, the
stretch stays where it is, and the frame is held afterwards if it lies in the
stretch. Nothing else changes in what is held. -/
@[step]
theorem mark_frame_spec (p : presence.Presence N) (index : Std.U64) :
    presence.Presence.mark_frame p index ⦃ r =>
      r.1 = outcomeOf p index.val ∧ r.2.base = p.base
      ∧ ∀ j, Held r.2 j ↔ Held p j ∨ (j = index.val ∧ Covered p j) ⦄ := by
  unfold presence.Presence.mark_frame
  step as ⟨b, hb⟩
  split
  · rename_i hc
    have hcov : Covered p index.val := by simpa [hb] using hc
    step as ⟨was, p1, hbase, h0, h1⟩
    obtain ⟨hwas, hbits⟩ := h1 hcov.pos
    have hheld : ∀ j, Held p1 j ↔ Held p j ∨ (j = index.val ∧ Covered p j) := by
      intro j
      unfold Held
      rw [covered_congr hbase, hbits]
      by_cases hs : SamePlace N.val index.val j
      · simp only [hs, ↓reduceIte, and_true]
        constructor
        · intro hcj
          exact Or.inr ⟨(hcov.eq_of_samePlace hcj hs).symm, hcj⟩
        · rintro (⟨hcj, -⟩ | ⟨-, hcj⟩) <;> exact hcj
      · simp only [hs, ↓reduceIte]
        constructor
        · exact Or.inl
        · rintro (h | ⟨rfl, -⟩)
          · exact h
          · exact absurd (SamePlace.refl _ _) hs
    split
    · rename_i hw
      simp only [WP.spec_ok]
      refine ⟨?_, hbase, hheld⟩
      have : bitOf p index.val = true := by rw [← hwas]; exact hw
      simp [outcomeOf, hcov, this]
    · rename_i hw
      simp only [WP.spec_ok]
      refine ⟨?_, hbase, hheld⟩
      have : bitOf p index.val = false := by rw [← hwas]; simpa using hw
      simp [outcomeOf, hcov, this]
  · rename_i hc
    have hcov : ¬ Covered p index.val := by simpa [hb] using hc
    have hheld : ∀ j, Held p j ↔ Held p j ∨ (j = index.val ∧ Covered p j) := by
      intro j
      constructor
      · exact Or.inl
      · rintro (h | ⟨rfl, hcj⟩)
        · exact h
        · exact absurd hcj hcov
    split
    · rename_i hlt
      have : index.val < p.base.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, trivial, hheld⟩
      simp [outcomeOf, hcov, this]
    · rename_i hlt
      have : ¬ index.val < p.base.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, trivial, hheld⟩
      simp [outcomeOf, hcov, this]

/-- The arrival of the frame at an offset from an index. Past the largest
index there is no frame, and its outcome is the one of an index beyond the
stretch. -/
@[step]
theorem mark_at_spec (p : presence.Presence N) (first : Std.U64) (offset : Std.U32) :
    presence.Presence.mark_at p first offset ⦃ r =>
      r.1 = outcomeOf p (first.val + offset.val) ∧ r.2.base = p.base
      ∧ ∀ j, Held r.2 j ↔ Held p j ∨ (j = first.val + offset.val ∧ Covered p j) ⦄ := by
  unfold presence.Presence.mark_at
  step as ⟨i, hi⟩
  have hiv : i.val = offset.val := by rw [hi]; exact U32.cast_U64_val offset
  step as ⟨o, ho⟩
  cases o with
  | none =>
    simp only at ho
    have hb : p.base.val ≤ U64.max := by scalar_tac
    have hcov : ¬ Covered p (first.val + offset.val) := by
      unfold Covered; omega
    have hlate : ¬ first.val + offset.val < p.base.val := by omega
    simp only [WP.spec_ok]
    refine ⟨?_, trivial, ?_⟩
    · simp [outcomeOf, hcov, hlate]
    · intro j
      constructor
      · exact Or.inl
      · rintro (h | ⟨rfl, hc⟩)
        · exact h
        · exact absurd hc hcov
  | some index =>
    simp only at ho
    obtain ⟨-, hidx, -⟩ := ho
    have hval : index.val = first.val + offset.val := by omega
    simp only
    step as ⟨out, h1, h2, h3⟩
    rw [hval] at h1 h3
    exact ⟨h1, h2, h3⟩

/-- Whether the frame at an offset from an index is held. -/
@[step]
theorem held_at_spec (p : presence.Presence N) (start : Std.U64) (offset : Std.U32) :
    presence.Presence.held_at p start offset ⦃ r =>
      r = true ↔ Held p (start.val + offset.val) ⦄ := by
  unfold presence.Presence.held_at
  step as ⟨i, hi⟩
  have hiv : i.val = offset.val := by rw [hi]; exact U32.cast_U64_val offset
  step as ⟨o, ho⟩
  cases o with
  | none =>
    simp only at ho
    have hcov : ¬ Covered p (start.val + offset.val) := by
      unfold Covered; omega
    simp [Held, hcov]
  | some index =>
    simp only at ho
    obtain ⟨-, hidx, -⟩ := ho
    have hval : index.val = start.val + offset.val := by omega
    simp only
    step as ⟨r, hr⟩
    rw [hval] at hr
    exact hr

deriving instance DecidableEq for presence.Outcome

/-- Counting a frame adds one to the count of its outcome. -/
@[step]
theorem count_spec (m : presence.Marked) (o : presence.Outcome) :
    presence.Marked.count m o ⦃ r =>
      r.stored = (if o = presence.Outcome.Stored
        then core.num.U32.saturating_add m.stored 1#u32 else m.stored)
      ∧ r.duplicate = (if o = presence.Outcome.Duplicate
        then core.num.U32.saturating_add m.duplicate 1#u32 else m.duplicate)
      ∧ r.late = (if o = presence.Outcome.Late
        then core.num.U32.saturating_add m.late 1#u32 else m.late)
      ∧ r.early = (if o = presence.Outcome.Early
        then core.num.U32.saturating_add m.early 1#u32 else m.early) ⦄ := by
  unfold presence.Marked.count
  cases o <;> simp only <;> step*

/-- How many of the frames at `first`, ..., `first + d - 1` have the outcome
`o` when they arrive at `p`. -/
def countOf (p : presence.Presence N) (first d : ℕ) (o : presence.Outcome) : ℕ :=
  (List.range d).countP (fun k => decide (outcomeOf p (first + k) = o))

theorem countOf_succ (p : presence.Presence N) (first d : ℕ) (o : presence.Outcome) :
    countOf p first (d + 1) o
      = countOf p first d o + if outcomeOf p (first + d) = o then 1 else 0 := by
  unfold countOf
  rw [List.range_succ, List.countP_append, List.countP_singleton]
  simp

theorem countOf_le (p : presence.Presence N) (first d : ℕ) (o : presence.Outcome) :
    countOf p first d o ≤ d := by
  unfold countOf
  have := List.countP_le_length (p := fun k => decide (outcomeOf p (first + k) = o))
    (l := List.range d)
  simpa using this

/-- Every frame of a packet has exactly one outcome. -/
theorem countOf_total (p : presence.Presence N) (first d : ℕ) :
    countOf p first d presence.Outcome.Stored + countOf p first d presence.Outcome.Duplicate
      + countOf p first d presence.Outcome.Late + countOf p first d presence.Outcome.Early
      = d := by
  induction d with
  | zero => simp [countOf]
  | succ d ih =>
    simp only [countOf_succ]
    cases h : outcomeOf p (first + d) <;> simp <;> omega

/-- A count that follows the number of frames with one outcome, after one
more frame. It does not reach the largest number, so nothing saturates. -/
theorem tally_step (x : Std.U32) (c d frames : ℕ) (hx : x.val = c) (hc : c ≤ d)
    (hd : d < frames) (hf : frames ≤ U32.max) (hit : Prop) [Decidable hit] :
    (if hit then core.num.U32.saturating_add x 1#u32 else x).val
      = c + if hit then 1 else 0 := by
  split
  · rw [U32.saturating_add_one_val x frames (by omega) hf, hx]
  · simp [hx]

/-- The receiver's state and counts after the first `d` frames of a packet
that starts at index `first` have arrived at `p`. -/
def Arrived (p : presence.Presence N) (first d : ℕ) (s : presence.Presence N)
    (m : presence.Marked) : Prop :=
  s.base = p.base
  ∧ (∀ j, Held s j ↔ Held p j ∨ (first ≤ j ∧ j < first + d ∧ Covered p j))
  ∧ m.stored.val = countOf p first d presence.Outcome.Stored
  ∧ m.duplicate.val = countOf p first d presence.Outcome.Duplicate
  ∧ m.late.val = countOf p first d presence.Outcome.Late
  ∧ m.early.val = countOf p first d presence.Outcome.Early

/-- Before a frame of the packet arrives, its outcome is the one it has at the
state the packet found: no earlier frame of the packet has its index. -/
theorem Arrived.outcomeOf_next {p s : presence.Presence N} {first d : ℕ}
    {m : presence.Marked} (h : Arrived p first d s m) :
    outcomeOf s (first + d) = outcomeOf p (first + d) := by
  obtain ⟨hbase, hheld, -⟩ := h
  have hh := hheld (first + d)
  unfold outcomeOf
  rw [hbase]
  by_cases hc : Covered p (first + d)
  · have hcs : Covered s (first + d) := (covered_congr hbase _).mpr hc
    have hbit : bitOf s (first + d) = bitOf p (first + d) := by
      rw [Bool.eq_iff_iff]
      unfold Held at hh
      constructor
      · intro hb
        rcases hh.mp ⟨hcs, hb⟩ with h1 | h1
        · exact h1.2
        · omega
      · intro hb
        exact (hh.mpr (Or.inl ⟨hc, hb⟩)).2
    simp [hc, hcs, hbit]
  · have hcs : ¬ Covered s (first + d) := fun h => hc ((covered_congr hbase _).mp h)
    simp [hc, hcs]

theorem mark_loop_spec (p : presence.Presence N) (first : Std.U64) (frames : Std.U32) :
    presence.Presence.mark_loop p first frames
      { stored := 0#u32, duplicate := 0#u32, late := 0#u32, early := 0#u32 } 0#u32 ⦃ r =>
      Arrived p first.val frames.val r.2 r.1 ⦄ := by
  unfold presence.Presence.mark_loop
  apply loop.spec_decr_nat
    (measure := fun x : presence.Presence N × presence.Marked × Std.U32 =>
      frames.val - x.2.2.val)
    (inv := fun x : presence.Presence N × presence.Marked × Std.U32 =>
      x.2.2.val ≤ frames.val ∧ Arrived p first.val x.2.2.val x.1 x.2.1)
  · rintro ⟨s, m, d⟩ ⟨hd, harr⟩
    dsimp only at hd harr
    unfold presence.Presence.mark_loop.body
    simp only
    split
    · have hlt : d.val < frames.val := by scalar_tac
      have hf : frames.val ≤ U32.max := by scalar_tac
      have hnext := harr.outcomeOf_next
      obtain ⟨hbase, hheld, hst, hdu, hla, hea⟩ := harr
      step as ⟨outcome, s1, hout, hb1, hh1⟩
      step as ⟨m1, hm1s, hm1d, hm1l, hm1e⟩
      step as ⟨d1, hd1⟩
      have hd1v : d1.val = d.val + 1 := by
        rw [hd1]; exact U32.saturating_add_one_val d frames.val hlt hf
      rw [hnext] at hout
      refine ⟨by omega, ⟨hb1.trans hbase, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
      · intro j
        rw [hh1, hheld, covered_congr hbase, hd1v]
        constructor
        · rintro ((h | ⟨a, b, c⟩) | ⟨rfl, c⟩)
          · exact Or.inl h
          · exact Or.inr ⟨a, by omega, c⟩
          · exact Or.inr ⟨by omega, by omega, c⟩
        · rintro (h | ⟨a, b, c⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hj : j = first.val + d.val
            · exact Or.inr ⟨hj, c⟩
            · exact Or.inl (Or.inr ⟨a, by omega, c⟩)
      · rw [hm1s, hd1v, countOf_succ, hout]
        exact tally_step _ _ d.val frames.val hst (countOf_le _ _ _ _) hlt hf _
      · rw [hm1d, hd1v, countOf_succ, hout]
        exact tally_step _ _ d.val frames.val hdu (countOf_le _ _ _ _) hlt hf _
      · rw [hm1l, hd1v, countOf_succ, hout]
        exact tally_step _ _ d.val frames.val hla (countOf_le _ _ _ _) hlt hf _
      · rw [hm1e, hd1v, countOf_succ, hout]
        exact tally_step _ _ d.val frames.val hea (countOf_le _ _ _ _) hlt hf _
    · have hdf : d.val = frames.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [← hdf]
      exact harr
  · dsimp only
    have h0 : (0#u32).val = 0 := by rfl
    rw [h0]
    refine ⟨by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      constructor
      · exact Or.inl
      · rintro (h | ⟨a, b, -⟩)
        · exact h
        · omega
    all_goals simp [countOf]

/-- The arrival of a packet of `frames` frames from index `first` on. The
stretch stays where it is. A frame is held afterwards exactly when it was held
before or it is a frame of the packet that lies in the stretch. Each count is
the number of the packet's frames whose index has that outcome. -/
@[step]
theorem mark_spec (p : presence.Presence N) (first : Std.U64) (frames : Std.U32) :
    presence.Presence.mark p first frames ⦃ r =>
      Arrived p first.val frames.val r.2 r.1 ⦄ := by
  unfold presence.Presence.mark
  exact mark_loop_spec p first frames

/-- Two packets leave the same frames held in whichever order they arrive. -/
theorem Arrived.comm {p q r q' r' : presence.Presence N} {a b da db : ℕ}
    {m1 m2 m3 m4 : presence.Marked}
    (h1 : Arrived p a da q m1) (h2 : Arrived q b db r m2)
    (h3 : Arrived p b db q' m3) (h4 : Arrived q' a da r' m4) :
    r.base = r'.base ∧ ∀ j, Held r j ↔ Held r' j := by
  obtain ⟨hb1, hh1, -⟩ := h1
  obtain ⟨hb2, hh2, -⟩ := h2
  obtain ⟨hb3, hh3, -⟩ := h3
  obtain ⟨hb4, hh4, -⟩ := h4
  refine ⟨by rw [hb2, hb1, hb4, hb3], fun j => ?_⟩
  rw [hh2, hh1, hh4, hh3, covered_congr hb1, covered_congr hb3]
  tauto

/-- A packet that arrives a second time changes nothing in what is held, and
none of its frames counts as stored. -/
theorem Arrived.again {p q r : presence.Presence N} {a d : ℕ} {m1 m2 : presence.Marked}
    (h1 : Arrived p a d q m1) (h2 : Arrived q a d r m2) :
    (∀ j, Held r j ↔ Held q j) ∧ m2.stored.val = 0 := by
  obtain ⟨hb1, hh1, -⟩ := h1
  obtain ⟨hb2, hh2, hst, -⟩ := h2
  constructor
  · intro j
    rw [hh2, hh1, covered_congr hb1]
    tauto
  · rw [hst]
    unfold countOf
    rw [List.countP_eq_zero]
    intro k hk
    have hk' : k < d := by simpa using hk
    simp only [decide_eq_true_eq]
    unfold outcomeOf
    by_cases hc : Covered q (a + k)
    · have hheld : Held q (a + k) :=
        (hh1 (a + k)).mpr (Or.inr ⟨by omega, by omega, (covered_congr hb1 _).mp hc⟩)
      simp [hc, hheld.2]
    · simp only [hc, ↓reduceIte]
      split <;> simp

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
