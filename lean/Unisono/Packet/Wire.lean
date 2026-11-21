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
# Packet wire primitives

Little-endian byte encoding/decoding (`readLE`, `HasLE`, `read_spec`, `write_spec`),
format and payload sizing helpers, `kind` decoding, and scalar cast round-trip lemmas.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Packet

/-! ## Little-endian byte encoding and decoding -/

/-- Decodes `count` little-endian bytes starting at `atPos` in `bs`. -/
def readLE (bs : List Std.U8) (atPos : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => readLE bs atPos k + (bs.getD (atPos + k) 0#u8).val * 2 ^ (8 * k)

theorem readLE_lt (bs : List Std.U8) (atPos : ℕ) : ∀ k, readLE bs atPos k < 2 ^ (8 * k)
  | 0 => by simp [readLE]
  | k + 1 => by
    unfold readLE
    have ih := readLE_lt bs atPos k
    have hb : (bs.getD (atPos + k) 0#u8).val < 256 := by scalar_tac
    have hpow : 2 ^ (8 * (k + 1)) = 256 * 2 ^ (8 * k) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    have hmul : (bs.getD (atPos + k) 0#u8).val * 2 ^ (8 * k) + 2 ^ (8 * k) ≤ 256 * 2 ^ (8 * k) := by
      have : (bs.getD (atPos + k) 0#u8).val + 1 ≤ 256 := hb
      calc (bs.getD (atPos + k) 0#u8).val * 2 ^ (8 * k) + 2 ^ (8 * k)
          = ((bs.getD (atPos + k) 0#u8).val + 1) * 2 ^ (8 * k) := by ring
        _ ≤ 256 * 2 ^ (8 * k) := Nat.mul_le_mul_right _ this
    omega

/-- `bs` stores the low `count` bytes of `v` in little-endian order starting at `atPos`. -/
def HasLE (bs : List Std.U8) (atPos count v : ℕ) : Prop :=
  atPos + count ≤ bs.length ∧
  ∀ k < count, (bs.getD (atPos + k) 0#u8).val = (v / 2 ^ (8 * k)) % 256

theorem readLE_of_hasLE {bs : List Std.U8} {atPos count v : ℕ}
    (h : HasLE bs atPos count v) :
    readLE bs atPos count = v % 2 ^ (8 * count) := by
  obtain ⟨hlen, hbytes⟩ := h
  induction count with
  | zero => simp [readLE]; omega
  | succ k ih =>
    unfold readLE
    rw [ih (by omega) (fun j hj => hbytes j (by omega)), hbytes k (by omega)]
    have hpow : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    rw [hpow, Nat.mod_mul, Nat.mul_comm (2 ^ (8 * k))]

theorem readLE_of_hasLE_eq {bs : List Std.U8} {atPos count v : ℕ}
    (h : HasLE bs atPos count v) (hv : v < 2 ^ (8 * count)) :
    readLE bs atPos count = v := by
  rw [readLE_of_hasLE h, Nat.mod_eq_of_lt hv]

private theorem nat_lor_mul_pow2 (x y s : ℕ) (hx : x < 2 ^ s) :
    x ||| (y * 2 ^ s) = x + y * 2 ^ s := by
  have hshift : y * 2 ^ s = y <<< s := by
    rw [Nat.shiftLeft_eq]
  rw [hshift, Nat.lor_comm, Nat.add_comm]
  exact (Nat.shiftLeft_add_eq_or_of_lt hx y).symm

private theorem u64_wrapping_shl_val (x : Std.U64) (s : Std.U32)
    (hs : s.val < 64) (hfit : x.val * 2 ^ s.val < 2 ^ 64) :
    (core.num.U64.wrapping_shl x s).val = x.val * 2 ^ s.val := by
  have hbv : (core.num.U64.wrapping_shl x s).bv = x.bv <<< (s.val % 64) :=
    core.num.U64.wrapping_shl_bv_eq x s
  have hmod : s.val % 64 = s.val := Nat.mod_eq_of_lt hs
  rw [hmod] at hbv
  change (core.num.U64.wrapping_shl x s).bv.toNat = x.bv.toNat * 2 ^ s.val
  rw [hbv, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt hfit

private theorem u64_wrapping_shr_val (x : Std.U64) (s : Std.U32) (hs : s.val < 64) :
    (core.num.U64.wrapping_shr x s).val = x.val / 2 ^ s.val := by
  have hbv : (core.num.U64.wrapping_shr x s).bv = x.bv >>> (s.val % 64) :=
    core.num.U64.wrapping_shr_bv_eq x s
  have hmod : s.val % 64 = s.val := Nat.mod_eq_of_lt hs
  rw [hmod] at hbv
  change (core.num.U64.wrapping_shr x s).bv.toNat = x.bv.toNat / 2 ^ s.val
  rw [hbv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Little-endian reading from an in-bounds range of at most 8 bytes returns
`some v` with `v.val = readLE bytes.val pos.val count.val`. -/
theorem read_spec (bytes : Slice Std.U8) (pos count : Std.Usize)
    (hfit : pos.val + count.val ≤ bytes.val.length) (hcount : count.val ≤ 8) :
    packet.read bytes pos count ⦃ o =>
      ∃ v, o = some v ∧ v.val = readLE bytes.val pos.val count.val ⦄ := by
  unfold packet.read packet.read_loop
  have hlen_max : bytes.val.length ≤ Usize.max := bytes.property
  apply loop.spec_decr_nat
    (measure := fun x : Std.U64 × Std.Usize => count.val - x.2.val)
    (inv := fun x : Std.U64 × Std.Usize =>
      x.2.val ≤ count.val ∧ x.1.val = readLE bytes.val pos.val x.2.val)
  · rintro ⟨value, i⟩ ⟨hi_le, hval⟩
    dsimp only at hi_le hval
    unfold packet.read_loop.body
    simp only
    split
    · have hlt : i.val < count.val := by scalar_tac
      have hplace_lt : pos.val + i.val < bytes.val.length := by omega
      have hadd_spec := Usize.checked_add_bv_spec pos i
      cases hadd : Usize.checked_add pos i with
      | none =>
        rw [hadd] at hadd_spec
        omega
      | some place =>
        rw [hadd] at hadd_spec
        obtain ⟨-, hplace_val, -⟩ := hadd_spec
        simp only [lift, bind_ok, core.slice.Slice.get, core.slice.index.Usize.get]
        have hget : bytes[place]? = some (bytes.val[pos.val + i.val]'hplace_lt) := by
          change bytes.val[place.val]? = some (bytes.val[pos.val + i.val]'hplace_lt)
          rw [hplace_val, List.getElem?_eq_getElem hplace_lt]
        rw [hget]
        have hi1 : (UScalar.cast .U32 i).val = i.val := by
          rw [UScalar.cast_val_mod_pow_of_inBounds_eq]; scalar_tac
        have hshift : (core.num.U32.wrapping_mul (UScalar.cast .U32 i) 8#u32).val = 8 * i.val := by
          simp only [core.num.U32.wrapping_mul_val_eq, hi1]
          have h8 : (8#u32).val = 8 := by rfl
          rw [h8, Nat.mod_eq_of_lt (by scalar_tac)]
          omega
        have hbyte : (UScalar.cast .U64 (bytes.val[pos.val + i.val]'hplace_lt)).val =
            (bytes.val[pos.val + i.val]'hplace_lt).val := by
          rw [UScalar.cast_val_mod_pow_of_inBounds_eq]; scalar_tac
        have hbyte_lt : (bytes.val[pos.val + i.val]'hplace_lt).val < 256 := by scalar_tac
        have hshl_lt : (bytes.val[pos.val + i.val]'hplace_lt).val * 2 ^ (8 * i.val) < 2 ^ 64 := by
          have hpow : 2 ^ (8 * i.val) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have : (bytes.val[pos.val + i.val]'hplace_lt).val * 2 ^ (8 * i.val) ≤ 255 * 2 ^ 56 :=
            Nat.mul_le_mul (by omega) hpow
          omega
        have hshl :
            (core.num.U64.wrapping_shl
              (UScalar.cast .U64 (bytes.val[pos.val + i.val]'hplace_lt))
              (core.num.U32.wrapping_mul (UScalar.cast .U32 i) 8#u32)).val =
            (bytes.val[pos.val + i.val]'hplace_lt).val * 2 ^ (8 * i.val) := by
          rw [u64_wrapping_shl_val _ _ (by omega) (by rw [hbyte, hshift]; exact hshl_lt),
            hbyte, hshift]
        have hval_lt : value.val < 2 ^ (8 * i.val) := by
          rw [hval]; exact readLE_lt bytes.val pos.val i.val
        have hlor :
            (value ||| core.num.U64.wrapping_shl
              (UScalar.cast .U64 (bytes.val[pos.val + i.val]'hplace_lt))
              (core.num.U32.wrapping_mul (UScalar.cast .U32 i) 8#u32)).val =
            value.val + (bytes.val[pos.val + i.val]'hplace_lt).val * 2 ^ (8 * i.val) := by
          set rhs := core.num.U64.wrapping_shl
            (UScalar.cast .U64 (bytes.val[pos.val + i.val]'hplace_lt))
            (core.num.U32.wrapping_mul (UScalar.cast .U32 i) 8#u32)
          have hbv_or : (value ||| rhs).val = value.val ||| rhs.val := by
            change (value.bv ||| rhs.bv).toNat = value.bv.toNat ||| rhs.bv.toNat
            exact BitVec.toNat_or value.bv rhs.bv
          rw [hbv_or, hshl]
          exact nat_lor_mul_pow2 value.val _ (8 * i.val) hval_lt
        have hnext : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 :=
          Usize.saturating_add_val _ _ (by scalar_tac)
        have hgetD : bytes.val.getD (pos.val + i.val) 0#u8 = bytes.val[pos.val + i.val]'hplace_lt := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hplace_lt]
        rw [WP.spec_ok]
        dsimp only
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hnext, hlor, hval, readLE, hgetD]
    · rename_i hge
      have heq : i.val = count.val := by scalar_tac
      rw [WP.spec_ok]
      exact ⟨value, rfl, by rw [hval, heq]⟩
  · refine ⟨by scalar_tac, ?_⟩
    rfl

/-- Reading from bytes that satisfy `HasLE` for a value fitting `count` bytes
recovers that exact value. -/
theorem read_of_hasLE (bytes : Slice Std.U8) (pos count : Std.Usize) (v : ℕ)
    (h : HasLE bytes.val pos.val count.val v) (hcount : count.val ≤ 8)
    (hv : v < 2 ^ (8 * count.val)) :
    packet.read bytes pos count ⦃ o => ∃ r, o = some r ∧ r.val = v ⦄ := by
  apply WP.spec_mono (read_spec bytes pos count h.1 hcount)
  rintro o ⟨r, ho, hr⟩
  exact ⟨r, ho, by rw [hr, readLE_of_hasLE_eq h hv]⟩

/-- Little-endian writing into an in-bounds range of at most 8 bytes succeeds,
preserves length, stores the low `count` bytes of `value`, and leaves all bytes
outside `[pos, pos + count)` untouched. -/
theorem write_spec (bytes : Slice Std.U8) (pos count : Std.Usize) (value : Std.U64)
    (hfit : pos.val + count.val ≤ bytes.val.length) (hcount : count.val ≤ 8) :
    packet.write bytes pos count value ⦃ out =>
      out.1 = true
      ∧ out.2.val.length = bytes.val.length
      ∧ HasLE out.2.val pos.val count.val value.val
      ∧ ∀ j, j < pos.val ∨ pos.val + count.val ≤ j →
          out.2.val.getD j 0#u8 = bytes.val.getD j 0#u8 ⦄ := by
  unfold packet.write packet.write_loop
  have hlen_max : bytes.val.length ≤ Usize.max := bytes.property
  apply loop.spec_decr_nat
    (measure := fun x : Slice Std.U8 × Std.Usize => count.val - x.2.val)
    (inv := fun x : Slice Std.U8 × Std.Usize =>
      x.2.val ≤ count.val
      ∧ x.1.val.length = bytes.val.length
      ∧ HasLE x.1.val pos.val x.2.val value.val
      ∧ ∀ j, j < pos.val ∨ pos.val + x.2.val ≤ j →
          x.1.val.getD j 0#u8 = bytes.val.getD j 0#u8)
  · rintro ⟨bs, i⟩ ⟨hi_le, hlen, hhas, hout⟩
    dsimp only at hi_le hlen hhas hout
    unfold packet.write_loop.body
    simp only
    split
    · have hlt : i.val < count.val := by scalar_tac
      have hplace_lt : pos.val + i.val < bs.val.length := by omega
      have hadd_spec := Usize.checked_add_bv_spec pos i
      cases hadd : Usize.checked_add pos i with
      | none =>
        rw [hadd] at hadd_spec
        omega
      | some place =>
        rw [hadd] at hadd_spec
        obtain ⟨-, hplace_val, -⟩ := hadd_spec
        simp only [lift, bind_ok, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut]
        have hget : bs[place]? = some (bs.val[pos.val + i.val]'hplace_lt) := by
          change bs.val[place.val]? = some (bs.val[pos.val + i.val]'hplace_lt)
          rw [hplace_val, List.getElem?_eq_getElem hplace_lt]
        rw [hget]
        simp only [Std.uncurry]
        have hi1 : (UScalar.cast .U32 i).val = i.val := by
          rw [UScalar.cast_val_mod_pow_of_inBounds_eq]; scalar_tac
        have hshift : (core.num.U32.wrapping_mul (UScalar.cast .U32 i) 8#u32).val = 8 * i.val := by
          simp only [core.num.U32.wrapping_mul_val_eq, hi1]
          have h8 : (8#u32).val = 8 := by rfl
          rw [h8, Nat.mod_eq_of_lt (by scalar_tac)]
          omega
        have hshr :
            (core.num.U64.wrapping_shr value
              (core.num.U32.wrapping_mul (UScalar.cast .U32 i) 8#u32)).val =
            value.val / 2 ^ (8 * i.val) := by
          rw [u64_wrapping_shr_val _ _ (by omega), hshift]
        set b : Std.U8 := UScalar.cast .U8
          (core.num.U64.wrapping_shr value
            (core.num.U32.wrapping_mul (UScalar.cast .U32 i) 8#u32))
        have hb_val : b.val = (value.val / 2 ^ (8 * i.val)) % 256 := by
          dsimp only [b]
          rw [UScalar.cast_val_eq, hshr]
          rfl
        have hnext : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 :=
          Usize.saturating_add_val _ _ (by scalar_tac)
        have hset_val : (bs.set_opt place (some b)).val = bs.val.set (pos.val + i.val) b := by
          rw [Slice.set_opt_val_eq, Unisono.Lists.set_opt_some, hplace_val]
        rw [WP.spec_ok]
        dsimp only
        refine ⟨⟨by omega, by rw [hset_val, List.length_set, hlen], ?_, ?_⟩, by omega⟩
        · refine ⟨by rw [hset_val, List.length_set]; omega, fun k hk => ?_⟩
          rw [hset_val]
          by_cases hki : k = i.val
          · subst hki
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by rw [List.length_set]; exact hplace_lt),
              List.getElem_set_self]
            exact hb_val
          · have hklt : k < i.val := by omega
            have hne : pos.val + i.val ≠ pos.val + k := by omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
            exact hhas.2 k hklt
        · intro j hj
          rw [hset_val]
          have hne : pos.val + i.val ≠ j := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
          exact hout j (by omega)
    · rename_i hge
      have heq : i.val = count.val := by scalar_tac
      rw [WP.spec_ok]
      rw [heq] at hhas hout
      exact ⟨rfl, hlen, hhas, hout⟩
  · dsimp only
    refine ⟨by scalar_tac, rfl, ⟨by scalar_tac, fun k hk => by scalar_tac⟩, fun j _ => rfl⟩

/-- Writing to `[at2, at2 + c2)` preserves `HasLE` on any disjoint range. -/
theorem HasLE.preserve {bs1 bs2 : List Std.U8} {a1 c1 v1 a2 c2 : ℕ}
    (hlen : bs2.length = bs1.length)
    (hout : ∀ j, j < a2 ∨ a2 + c2 ≤ j → bs2.getD j 0#u8 = bs1.getD j 0#u8)
    (hdisj : a1 + c1 ≤ a2 ∨ a2 + c2 ≤ a1)
    (h : HasLE bs1 a1 c1 v1) :
    HasLE bs2 a1 c1 v1 := by
  have h1 := h.1
  refine ⟨by omega, fun k hk => ?_⟩
  rw [hout (a1 + k) (by omega)]
  exact h.2 k hk

/-! ## Totality of low-level helpers -/

@[step]
theorem read_total (bytes : Slice Std.U8) (pos count : Std.Usize) :
    packet.read bytes pos count ⦃ _ => True ⦄ := by
  unfold packet.read packet.read_loop
  apply loop.spec_decr_nat
    (measure := fun x : Std.U64 × Std.Usize => count.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨value, i⟩ _
    unfold packet.read_loop.body
    simp only
    split
    · have hlt : i.val < count.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o, ho⟩
      split
      · simp
      · simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
        split
        · simp
        · step*
    · simp
  · trivial

@[step]
theorem write_total (bytes : Slice Std.U8) (pos count : Std.Usize) (value : Std.U64) :
    packet.write bytes pos count value ⦃ _ => True ⦄ := by
  unfold packet.write packet.write_loop
  apply loop.spec_decr_nat
    (measure := fun x : Slice Std.U8 × Std.Usize => count.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨bytes1, i⟩ _
    unfold packet.write_loop.body
    simp only
    split
    · have hlt : i.val < count.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o, ho⟩
      split
      · simp
      · simp only [core.slice.Slice.get_mut, core.slice.index.Usize.get_mut, bind_ok,
          uncurry]
        split
        · simp
        · step*
    · simp
  · trivial

/-- Bytes per sample for a format. -/
def formatBytes : packet.Format → ℕ
  | .Signed16 => 2
  | .Signed24 => 3

/-- Wire code for a format. -/
def formatCode : packet.Format → ℕ
  | .Signed16 => 1
  | .Signed24 => 2

/-- Payload length in bytes announced by an audio header. -/
def payloadLen (h : packet.Audio) : ℕ :=
  h.frames.val * h.channels.val * formatBytes h.format

@[step]
theorem format_bytes_spec (f : packet.Format) :
    packet.Format.bytes f ⦃ r => r.val = formatBytes f ⦄ := by
  unfold packet.Format.bytes
  cases f <;> simp [formatBytes]

@[step]
theorem format_code_spec (f : packet.Format) :
    packet.Format.code f ⦃ r => r.val = formatCode f ⦄ := by
  unfold packet.Format.code
  cases f <;> simp [formatCode]

@[step]
theorem format_from_code_spec (c : Std.U8) :
    packet.Format.from_code c ⦃ o =>
      (c.val = 1 → o = some .Signed16)
      ∧ (c.val = 2 → o = some .Signed24)
      ∧ (c.val ≠ 1 → c.val ≠ 2 → o = none) ⦄ := by
  unfold packet.Format.from_code
  split
  · rw [WP.spec_ok]
    refine ⟨fun _ => rfl, fun h => by change 1 = 2 at h; omega, fun h _ => absurd rfl h⟩
  · rw [WP.spec_ok]
    refine ⟨fun h => by change 2 = 1 at h; omega, fun _ => rfl, fun _ h => absurd rfl h⟩
  · rename_i h1 h2
    have hc1 : c.val ≠ 1 := fun hv => h1 (UScalar.eq_of_val_eq hv)
    have hc2 : c.val ≠ 2 := fun hv => h2 (UScalar.eq_of_val_eq hv)
    simp [hc1, hc2]

theorem payloadLen_le (h : packet.Audio) : payloadLen h ≤ 50134275 := by
  unfold payloadLen
  have hf : h.frames.val ≤ 65535 := by scalar_tac
  have hc : h.channels.val ≤ 255 := by scalar_tac
  have hb : formatBytes h.format ≤ 3 := by cases h.format <;> simp [formatBytes]
  have h1 : h.frames.val * h.channels.val ≤ 65535 * 255 := Nat.mul_le_mul hf hc
  have h2 : h.frames.val * h.channels.val * formatBytes h.format ≤ 65535 * 255 * 3 :=
    Nat.mul_le_mul h1 hb
  omega

theorem usize_max_ge : 2 ^ 32 - 1 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> (rw [h]; scalar_tac)

theorem usize_size_ge : 2 ^ 32 ≤ Usize.size := by
  have h1 := usize_max_succ
  rw [usize_max_eq] at h1
  have h2 := usize_max_ge
  have h3 : Usize.size = 2 ^ UScalarTy.Usize.numBits := by
    rw [Usize.size_def, Usize.numBits_def]
  omega

@[step]
theorem payload_spec (h : packet.Audio) :
    packet.payload h ⦃ r => r.val = payloadLen h ⦄ := by
  unfold packet.payload
  have hsize : 2 ^ 32 ≤ UScalar.size UScalarTy.Usize := by
    rw [UScalar.size_UScalarTyUsize]; exact usize_size_ge
  have hpow : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    rw [← Usize.numBits_def, ← Usize.size_def]; exact usize_size_ge
  have hf : h.frames.val ≤ 65535 := by scalar_tac
  have hc : h.channels.val ≤ 255 := by scalar_tac
  have h1 : (UScalar.cast .Usize h.frames).val = h.frames.val := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq]; omega
  have h2 : (UScalar.cast .Usize h.channels).val = h.channels.val := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq]; omega
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hi2_val : i2.val = h.frames.val * h.channels.val := by
    rw [hi2, core.num.Usize.wrapping_mul_val_eq, hi, hi1, h1, h2]
    have hle : h.frames.val * h.channels.val ≤ 65535 * 255 := Nat.mul_le_mul hf hc
    exact Nat.mod_eq_of_lt (by omega)
  step with format_bytes_spec h.format as ⟨i3, hi3⟩
  rw [core.num.Usize.wrapping_mul_val_eq, hi2_val, hi3]
  have hle := payloadLen_le h
  unfold payloadLen at hle ⊢
  exact Nat.mod_eq_of_lt (by omega)


/-! ## Kind and parsing validity -/

@[step]
theorem kind_total (bytes : Slice Std.U8) : packet.kind bytes ⦃ _ => True ⦄ := by
  unfold packet.kind
  step*

/-- `kind` returns `Ok k` when bytes 0..6 carry the magic, version, and kind `k`. -/
theorem kind_of_hasLE (bytes : Slice Std.U8) (k : Std.U8)
    (hm : HasLE bytes.val 0 4 packet.MAGIC.val)
    (hv : HasLE bytes.val 4 1 packet.VERSION.val)
    (hk : HasLE bytes.val 5 1 k.val) :
    packet.kind bytes ⦃ r => r = .Ok k ⦄ := by
  unfold packet.kind
  have hmagic_lt : packet.MAGIC.val < 2 ^ (8 * 4) := by
    simp [packet.MAGIC]
  have hver_lt : packet.VERSION.val < 2 ^ (8 * 1) := by
    simp [packet.VERSION]
  have hk_lt : k.val < 2 ^ (8 * 1) := by scalar_tac
  step with read_of_hasLE bytes 0#usize 4#usize packet.MAGIC.val hm (by decide) hmagic_lt
    as ⟨o, magic, ho, hmagic⟩
  step with read_of_hasLE bytes 4#usize 1#usize packet.VERSION.val hv (by decide) hver_lt
    as ⟨o1, ver, ho1, hver⟩
  step with read_of_hasLE bytes 5#usize 1#usize k.val hk (by decide) hk_lt
    as ⟨o2, kf, ho2, hkf⟩
  rw [ho, ho1, ho2]
  have hmeq : magic = packet.MAGIC := UScalar.eq_of_val_eq hmagic
  simp only [hmeq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step as ⟨i, hi⟩
  have hiveq : ver = i := by
    apply UScalar.eq_of_val_eq
    rw [hver, hi, UScalar.cast_val_mod_pow_of_inBounds_eq]
    scalar_tac
  simp only [hiveq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step as ⟨i1, hi1⟩
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hi1, UScalar.cast_val_mod_pow_of_inBounds_eq, hkf]
  scalar_tac

/-! ## Cast round-trip helpers -/

theorem cast_u8_u64_val (x : Std.U8) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]; scalar_tac

theorem cast_u16_u64_val (x : Std.U16) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]; scalar_tac

theorem cast_u32_u64_val (x : Std.U32) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]; scalar_tac

theorem hcast_i64_u64_i64 (x : Std.I64) (u : Std.U64)
    (hu : u.val = (IScalar.hcast .U64 x).val) :
    UScalar.hcast .I64 u = x := by
  have hueq : u = IScalar.hcast .U64 x := UScalar.eq_of_val_eq hu
  subst hueq
  cases x with
  | mk bv =>
    congr 1
    simp [IScalar.hcast]


end Unisono.Packet
