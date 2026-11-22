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
# Presence bitmap: bit operations and stretch indexing

Bit-level helpers, stretch coverage (`Covered`, `Held`, `SamePlace`), and
single-bit accessors (`width`, `covers`, `place`, `word`, `set_word`, `bit`,
`put`, `held`).
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


end Unisono.Presence
