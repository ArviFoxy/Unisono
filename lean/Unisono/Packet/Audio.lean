/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Packet.Wire

/-!
# Audio packets

Semantic header validity (`ValidAudio`, `validate_audio_spec`), `parse_audio`
validity, and `write_audio` / `parse_audio` wire layout and round-trip proofs.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Packet

/-! ## Semantic validity of audio headers -/

/-- Semantic invariants guaranteed for every header accepted by `parse_audio`. -/
def ValidAudio (h : packet.Audio) : Prop :=
  0 < h.rate.val
  ∧ 0 < h.channels.val
  ∧ (h.flags &&& packet.KNOWN_FLAGS) = h.flags
  ∧ h.protection.val ≤ 1
  ∧ -1000000000 < h.drift.val
  ∧ -1000000000 < h.level_slope.val

@[step]
theorem validate_audio_spec (h : packet.Audio) :
    packet.validate_audio h ⦃ r => (r = .Ok () ↔ ValidAudio h) ⦄ := by
  unfold packet.validate_audio
  have hmin : packet.MIN_SLOPE.val = -999999999 := by simp [packet.MIN_SLOPE]
  have hprot : packet.PROTECTION_ON_REQUEST.val = 1 := by simp [packet.PROTECTION_ON_REQUEST]
  split
  · rename_i hr
    have hr0 : h.rate.val = 0 := by scalar_tac
    simp [ValidAudio, hr0]
  · rename_i hr
    have hrpos : 0 < h.rate.val := by scalar_tac
    split
    · rename_i hc
      have hc0 : h.channels.val = 0 := by scalar_tac
      simp [ValidAudio, hc0]
    · rename_i hc
      have hcpos : 0 < h.channels.val := by scalar_tac
      step as ⟨i, hi, _⟩
      have hi_eq : i = h.flags &&& packet.KNOWN_FLAGS := UScalar.eq_of_val_eq hi
      split
      · rename_i hf
        have hfne : (h.flags &&& packet.KNOWN_FLAGS) ≠ h.flags := by
          rw [← hi_eq]; simpa using hf
        simp [ValidAudio, hfne]
      · rename_i hf
        have hfeq : (h.flags &&& packet.KNOWN_FLAGS) = h.flags := by
          rw [← hi_eq]
          exact UScalar.eq_of_val_eq (by simpa using hf)
        split
        · rename_i hp
          have hpne : ¬ h.protection.val ≤ 1 := by scalar_tac
          simp [ValidAudio, hpne]
        · rename_i hp
          have hp0 : h.protection.val ≤ 1 := by scalar_tac
          split
          · rename_i hd
            have hdlt : h.drift.val ≤ -1000000000 := by scalar_tac
            simp [ValidAudio]; omega
          · rename_i hd
            have hdgt : -1000000000 < h.drift.val := by scalar_tac
            split
            · rename_i hs
              have hslt : h.level_slope.val ≤ -1000000000 := by scalar_tac
              simp [ValidAudio]; omega
            · rename_i hs
              have hsgt : -1000000000 < h.level_slope.val := by scalar_tac
              simp [ValidAudio, hrpos, hcpos, hfeq, hp0, hdgt, hsgt]

/-- Every audio header accepted by `parse_audio` satisfies `ValidAudio` and has
exact payload length `bytes.len - HEADER`. -/
theorem parse_audio_valid (bytes : Slice Std.U8) :
    packet.parse_audio bytes ⦃ r =>
      ∀ h, r = .Ok h → ValidAudio h ∧ bytes.val.length = packet.HEADER.val + payloadLen h ⦄ := by
  unfold packet.parse_audio
  dsimp only
  have hhdr : packet.HEADER.val = 88 := by simp [packet.HEADER]
  split
  · simp
  · rename_i hge
    have hge' : packet.HEADER.val ≤ bytes.val.length := by
      have : bytes.len.val = bytes.val.length := rfl
      scalar_tac
    step with kind_total bytes as ⟨rk⟩
    cases rk with
    | Err _ => simp
    | Ok found =>
      dsimp only
      cases hne : (found != packet.KIND_AUDIO) with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        step with read_total bytes 6#usize 2#usize as ⟨o⟩
        step with read_total bytes 8#usize 8#usize as ⟨o1⟩
        step with read_total bytes 16#usize 8#usize as ⟨o2⟩
        step with read_total bytes 24#usize 8#usize as ⟨o3⟩
        step with read_total bytes 32#usize 4#usize as ⟨o4⟩
        step with read_total bytes 36#usize 2#usize as ⟨o5⟩
        cases o with | none => simp | some stream =>
        cases o1 with | none => simp | some timeline =>
        cases o2 with | none => simp | some index =>
        cases o3 with | none => simp | some capture =>
        cases o4 with | none => simp | some rate =>
        cases o5 with | none => simp | some frames =>
        step with read_total bytes 38#usize 1#usize as ⟨o6⟩
        step with read_total bytes 39#usize 1#usize as ⟨o7⟩
        step with read_total bytes 40#usize 8#usize as ⟨o8⟩
        step with read_total bytes 48#usize 4#usize as ⟨o9⟩
        step with read_total bytes 52#usize 4#usize as ⟨o10⟩
        step with read_total bytes 56#usize 4#usize as ⟨o11⟩
        step with read_total bytes 60#usize 2#usize as ⟨o12⟩
        cases o6 with | none => simp | some channels =>
        cases o7 with | none => simp | some fmt =>
        cases o8 with | none => simp | some level =>
        cases o9 with | none => simp | some level_slope =>
        cases o10 with | none => simp | some span =>
        cases o11 with | none => simp | some window =>
        cases o12 with | none => simp | some flags =>
        step with read_total bytes 62#usize 2#usize as ⟨o13⟩
        step with read_total bytes 64#usize 8#usize as ⟨o14⟩
        step with read_total bytes 72#usize 8#usize as ⟨o15⟩
        step with read_total bytes 80#usize 4#usize as ⟨o16⟩
        step with read_total bytes 84#usize 4#usize as ⟨o17⟩
        cases o13 with | none => simp | some protection =>
        cases o14 with | none => simp | some stamped_index =>
        cases o15 with | none => simp | some stamped_departure =>
        cases o16 with | none => simp | some drift =>
        cases o17 with | none => simp | some clock =>
        step as ⟨fc⟩
        step with format_from_code_spec fc as ⟨ofmt, _, _, _⟩
        cases ofmt with
        | none => step; simp
        | some format =>
          step as ⟨s1⟩; step as ⟨s2⟩; step as ⟨s3⟩; step as ⟨s4⟩
          step as ⟨s5⟩; step as ⟨s6⟩; step as ⟨s7⟩; step as ⟨s8⟩
          step as ⟨s9⟩; step as ⟨s10⟩; step as ⟨s11⟩; step as ⟨s12⟩
          step as ⟨s13⟩; step as ⟨s14⟩; step as ⟨s15⟩; step as ⟨s16⟩
          step with validate_audio_spec as ⟨rval, hrval⟩
          cases rval with
          | Err _ => simp
          | Ok _ =>
            have hvalid := hrval.mp rfl
            step as ⟨sub, hsub⟩
            step with payload_spec as ⟨pl, hpl⟩
            split
            · simp
            · rename_i heq
              rw [WP.spec_ok]
              intro h hh
              injection hh with hh'
              subst hh'
              have hsub_eq : sub.val = pl.val := by scalar_tac
              have hsub_val : sub.val = bytes.val.length - packet.HEADER.val := by
                rw [hsub, core.num.Usize.wrapping_sub_val_eq, UScalar.size_UScalarTyUsize]
                have hblen : bytes.len.val = bytes.val.length := rfl
                have hmax : bytes.val.length ≤ Usize.max := bytes.property
                have hlt : Usize.max < Usize.size := by
                  have h1 := usize_max_succ; rw [usize_max_eq] at h1
                  rw [Usize.size_def, Usize.numBits_def]; omega
                rw [hblen,
                  show bytes.val.length + (Usize.size - packet.HEADER.val) =
                    (bytes.val.length - packet.HEADER.val) + Usize.size by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              exact ⟨hvalid, by omega⟩

theorem parse_audio_total (bytes : Slice Std.U8) :
    packet.parse_audio bytes ⦃ _ => True ⦄ :=
  WP.spec_mono (parse_audio_valid bytes) (fun _ _ => trivial)

theorem write_audio_total (h : packet.Audio) (bytes : Slice Std.U8) :
    packet.write_audio h bytes ⦃ _ => True ⦄ := by
  unfold packet.write_audio
  simp only
  step*


/-! ## Audio header wire layout and round-trip -/

/-- Exact 88-byte wire layout and total packet length produced by `write_audio`. -/
theorem write_audio_spec (h : packet.Audio) (bytes : Slice Std.U8)
    (hlen : packet.HEADER.val ≤ bytes.val.length) :
    packet.write_audio h bytes ⦃ out =>
      (∃ n, out.1 = some n ∧ n.val = packet.HEADER.val + payloadLen h)
      ∧ out.2.val.length = bytes.val.length
      ∧ HasLE out.2.val 0 4 packet.MAGIC.val
      ∧ HasLE out.2.val 4 1 packet.VERSION.val
      ∧ HasLE out.2.val 5 1 packet.KIND_AUDIO.val
      ∧ HasLE out.2.val 6 2 h.stream.val
      ∧ HasLE out.2.val 8 8 h.timeline.val
      ∧ HasLE out.2.val 16 8 h.index.val
      ∧ HasLE out.2.val 24 8 (IScalar.hcast .U64 h.capture).val
      ∧ HasLE out.2.val 32 4 h.rate.val
      ∧ HasLE out.2.val 36 2 h.frames.val
      ∧ HasLE out.2.val 38 1 h.channels.val
      ∧ HasLE out.2.val 39 1 (formatCode h.format)
      ∧ HasLE out.2.val 40 8 (IScalar.hcast .U64 h.level).val
      ∧ HasLE out.2.val 48 4 (IScalar.hcast .U32 h.level_slope).val
      ∧ HasLE out.2.val 52 4 h.span.val
      ∧ HasLE out.2.val 56 4 h.window.val
      ∧ HasLE out.2.val 60 2 h.flags.val
      ∧ HasLE out.2.val 62 2 h.protection.val
      ∧ HasLE out.2.val 64 8 h.stamped_index.val
      ∧ HasLE out.2.val 72 8 (IScalar.hcast .U64 h.stamped_departure).val
      ∧ HasLE out.2.val 80 4 (IScalar.hcast .U32 h.drift).val
      ∧ HasLE out.2.val 84 4 h.clock.val ⦄ := by
  have hhdr : packet.HEADER.val = 88 := by simp [packet.HEADER]
  have hge88 : 88 ≤ bytes.val.length := by omega
  unfold packet.write_audio
  have hnotlt : ¬ bytes.len < packet.HEADER := by
    have : bytes.len.val = bytes.val.length := rfl
    scalar_tac
  simp only [hnotlt, ↓reduceIte]
  have hfit : ∀ (s : Slice Std.U8) (p c : Std.Usize),
      s.val.length = bytes.val.length → p.val + c.val ≤ 88 → p.val + c.val ≤ s.val.length :=
    fun _ _ _ h1 h2 => by omega
  step with write_spec bytes 0#usize 4#usize packet.MAGIC (hfit _ _ _ rfl (by decide)) (by decide)
    as ⟨b0, bs1, hb0, hl1, hf0, _⟩
  step as ⟨v1, hv1⟩
  step with write_spec bs1 4#usize 1#usize v1 (hfit _ _ _ hl1 (by decide)) (by decide)
    as ⟨b1, bs2, hb1, hl2, hf1, ho1⟩
  have hl2' : bs2.val.length = bytes.val.length := hl2.trans hl1
  step as ⟨v2, hv2⟩
  step with write_spec bs2 5#usize 1#usize v2 (hfit _ _ _ hl2' (by decide)) (by decide)
    as ⟨b2, bs3, hb2, hl3, hf2, ho2⟩
  have hl3' : bs3.val.length = bytes.val.length := hl3.trans hl2'
  step as ⟨v3, hv3⟩
  step with write_spec bs3 6#usize 2#usize v3 (hfit _ _ _ hl3' (by decide)) (by decide)
    as ⟨b3, bs4, hb3, hl4, hf3, ho3⟩
  have hl4' : bs4.val.length = bytes.val.length := hl4.trans hl3'
  step with write_spec bs4 8#usize 8#usize h.timeline (hfit _ _ _ hl4' (by decide)) (by decide)
    as ⟨b4, bs5, hb4, hl5, hf4, ho4⟩
  have hl5' : bs5.val.length = bytes.val.length := hl5.trans hl4'
  step with write_spec bs5 16#usize 8#usize h.index (hfit _ _ _ hl5' (by decide)) (by decide)
    as ⟨b5, bs6, hb5, hl6, hf5, ho5⟩
  have hl6' : bs6.val.length = bytes.val.length := hl6.trans hl5'
  step as ⟨v6, hv6⟩
  step with write_spec bs6 24#usize 8#usize v6 (hfit _ _ _ hl6' (by decide)) (by decide)
    as ⟨b6, bs7, hb6, hl7, hf6, ho6⟩
  have hl7' : bs7.val.length = bytes.val.length := hl7.trans hl6'
  step as ⟨v7, hv7⟩
  step with write_spec bs7 32#usize 4#usize v7 (hfit _ _ _ hl7' (by decide)) (by decide)
    as ⟨b7, bs8, hb7, hl8, hf7, ho7⟩
  have hl8' : bs8.val.length = bytes.val.length := hl8.trans hl7'
  step as ⟨v8, hv8⟩
  step with write_spec bs8 36#usize 2#usize v8 (hfit _ _ _ hl8' (by decide)) (by decide)
    as ⟨b8, bs9, hb8, hl9, hf8, ho8⟩
  have hl9' : bs9.val.length = bytes.val.length := hl9.trans hl8'
  step as ⟨v9, hv9⟩
  step with write_spec bs9 38#usize 1#usize v9 (hfit _ _ _ hl9' (by decide)) (by decide)
    as ⟨b9, bs10, hb9, hl10, hf9, ho9⟩
  have hl10' : bs10.val.length = bytes.val.length := hl10.trans hl9'
  step with format_code_spec h.format as ⟨fc, hfc⟩
  step as ⟨v10, hv10⟩
  step with write_spec bs10 39#usize 1#usize v10 (hfit _ _ _ hl10' (by decide)) (by decide)
    as ⟨b10, bs11, hb10, hl11, hf10, ho10⟩
  have hl11' : bs11.val.length = bytes.val.length := hl11.trans hl10'
  step as ⟨v11, hv11⟩
  step with write_spec bs11 40#usize 8#usize v11 (hfit _ _ _ hl11' (by decide)) (by decide)
    as ⟨b11, bs12, hb11, hl12, hf11, ho11⟩
  have hl12' : bs12.val.length = bytes.val.length := hl12.trans hl11'
  step as ⟨v12a, hv12a⟩
  step as ⟨v12, hv12⟩
  step with write_spec bs12 48#usize 4#usize v12 (hfit _ _ _ hl12' (by decide)) (by decide)
    as ⟨b12, bs13, hb12, hl13, hf12, ho12⟩
  have hl13' : bs13.val.length = bytes.val.length := hl13.trans hl12'
  step as ⟨v13, hv13⟩
  step with write_spec bs13 52#usize 4#usize v13 (hfit _ _ _ hl13' (by decide)) (by decide)
    as ⟨b13, bs14, hb13, hl14, hf13, ho13⟩
  have hl14' : bs14.val.length = bytes.val.length := hl14.trans hl13'
  step as ⟨v14, hv14⟩
  step with write_spec bs14 56#usize 4#usize v14 (hfit _ _ _ hl14' (by decide)) (by decide)
    as ⟨b14, bs15, hb14, hl15, hf14, ho14⟩
  have hl15' : bs15.val.length = bytes.val.length := hl15.trans hl14'
  step as ⟨v15, hv15⟩
  step with write_spec bs15 60#usize 2#usize v15 (hfit _ _ _ hl15' (by decide)) (by decide)
    as ⟨b15, bs16, hb15, hl16, hf15, ho15⟩
  have hl16' : bs16.val.length = bytes.val.length := hl16.trans hl15'
  step as ⟨v16, hv16⟩
  step with write_spec bs16 62#usize 2#usize v16 (hfit _ _ _ hl16' (by decide)) (by decide)
    as ⟨b16, bs17, hb16, hl17, hf16, ho16⟩
  have hl17' : bs17.val.length = bytes.val.length := hl17.trans hl16'
  step with write_spec bs17 64#usize 8#usize h.stamped_index (hfit _ _ _ hl17' (by decide)) (by decide)
    as ⟨b17, bs18, hb17, hl18, hf17, ho17⟩
  have hl18' : bs18.val.length = bytes.val.length := hl18.trans hl17'
  step as ⟨v18, hv18⟩
  step with write_spec bs18 72#usize 8#usize v18 (hfit _ _ _ hl18' (by decide)) (by decide)
    as ⟨b18, bs19, hb18, hl19, hf18, ho18⟩
  have hl19' : bs19.val.length = bytes.val.length := hl19.trans hl18'
  step as ⟨v19a, hv19a⟩
  step as ⟨v19, hv19⟩
  step with write_spec bs19 80#usize 4#usize v19 (hfit _ _ _ hl19' (by decide)) (by decide)
    as ⟨b19, bs20, hb19, hl20, hf19, ho19⟩
  have hl20' : bs20.val.length = bytes.val.length := hl20.trans hl19'
  step as ⟨v20, hv20⟩
  step with write_spec bs20 84#usize 4#usize v20 (hfit _ _ _ hl20' (by decide)) (by decide)
    as ⟨b20, bs21, hb20, hl21, hf20, ho20⟩
  have hl21' : bs21.val.length = bytes.val.length := hl21.trans hl20'
  simp only [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13,
    hb14, hb15, hb16, hb17, hb18, hb19, hb20, Bool.and_self, ↓reduceIte]
  step with payload_spec h as ⟨pl_w, hpl_w⟩
  step as ⟨tot_w, htot_w⟩
  have htot_val : tot_w.val = packet.HEADER.val + payloadLen h := by
    have hsize := usize_size_ge
    have hple := payloadLen_le h
    rw [htot_w, core.num.Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize, hpl_w]
    exact Nat.mod_eq_of_lt (by omega)
  have p20 : ∀ a c v, a + c ≤ 84 → HasLE bs20.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => hh.preserve hl21 ho20 (Or.inl hle)
  have p19 : ∀ a c v, a + c ≤ 80 → HasLE bs19.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p20 _ _ _ (by omega) (hh.preserve hl20 ho19 (Or.inl hle))
  have p18 : ∀ a c v, a + c ≤ 72 → HasLE bs18.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p19 _ _ _ (by omega) (hh.preserve hl19 ho18 (Or.inl hle))
  have p17 : ∀ a c v, a + c ≤ 64 → HasLE bs17.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p18 _ _ _ (by omega) (hh.preserve hl18 ho17 (Or.inl hle))
  have p16 : ∀ a c v, a + c ≤ 62 → HasLE bs16.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p17 _ _ _ (by omega) (hh.preserve hl17 ho16 (Or.inl hle))
  have p15 : ∀ a c v, a + c ≤ 60 → HasLE bs15.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p16 _ _ _ (by omega) (hh.preserve hl16 ho15 (Or.inl hle))
  have p14 : ∀ a c v, a + c ≤ 56 → HasLE bs14.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p15 _ _ _ (by omega) (hh.preserve hl15 ho14 (Or.inl hle))
  have p13 : ∀ a c v, a + c ≤ 52 → HasLE bs13.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p14 _ _ _ (by omega) (hh.preserve hl14 ho13 (Or.inl hle))
  have p12 : ∀ a c v, a + c ≤ 48 → HasLE bs12.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p13 _ _ _ (by omega) (hh.preserve hl13 ho12 (Or.inl hle))
  have p11 : ∀ a c v, a + c ≤ 40 → HasLE bs11.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p12 _ _ _ (by omega) (hh.preserve hl12 ho11 (Or.inl hle))
  have p10 : ∀ a c v, a + c ≤ 39 → HasLE bs10.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p11 _ _ _ (by omega) (hh.preserve hl11 ho10 (Or.inl hle))
  have p9 : ∀ a c v, a + c ≤ 38 → HasLE bs9.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p10 _ _ _ (by omega) (hh.preserve hl10 ho9 (Or.inl hle))
  have p8 : ∀ a c v, a + c ≤ 36 → HasLE bs8.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p9 _ _ _ (by omega) (hh.preserve hl9 ho8 (Or.inl hle))
  have p7 : ∀ a c v, a + c ≤ 32 → HasLE bs7.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p8 _ _ _ (by omega) (hh.preserve hl8 ho7 (Or.inl hle))
  have p6 : ∀ a c v, a + c ≤ 24 → HasLE bs6.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p7 _ _ _ (by omega) (hh.preserve hl7 ho6 (Or.inl hle))
  have p5 : ∀ a c v, a + c ≤ 16 → HasLE bs5.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p6 _ _ _ (by omega) (hh.preserve hl6 ho5 (Or.inl hle))
  have p4 : ∀ a c v, a + c ≤ 8 → HasLE bs4.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p5 _ _ _ (by omega) (hh.preserve hl5 ho4 (Or.inl hle))
  have p3 : ∀ a c v, a + c ≤ 6 → HasLE bs3.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p4 _ _ _ (by omega) (hh.preserve hl4 ho3 (Or.inl hle))
  have p2 : ∀ a c v, a + c ≤ 5 → HasLE bs2.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p3 _ _ _ (by omega) (hh.preserve hl3 ho2 (Or.inl hle))
  have p1 : ∀ a c v, a + c ≤ 4 → HasLE bs1.val a c v → HasLE bs21.val a c v :=
    fun _ _ _ hle hh => p2 _ _ _ (by omega) (hh.preserve hl2 ho1 (Or.inl hle))
  have hv1_eq : v1.val = packet.VERSION.val := by rw [hv1]; exact cast_u8_u64_val _
  have hv2_eq : v2.val = packet.KIND_AUDIO.val := by rw [hv2]; exact cast_u8_u64_val _
  have hv3_eq : v3.val = h.stream.val := by rw [hv3]; exact cast_u16_u64_val _
  have hv7_eq : v7.val = h.rate.val := by rw [hv7]; exact cast_u32_u64_val _
  have hv8_eq : v8.val = h.frames.val := by rw [hv8]; exact cast_u16_u64_val _
  have hv9_eq : v9.val = h.channels.val := by rw [hv9]; exact cast_u8_u64_val _
  have hv10_eq : v10.val = formatCode h.format := by rw [hv10, cast_u8_u64_val, hfc]
  have hv12_eq : v12.val = (IScalar.hcast .U32 h.level_slope).val := by
    rw [hv12, hv12a]; exact cast_u32_u64_val _
  have hv13_eq : v13.val = h.span.val := by rw [hv13]; exact cast_u32_u64_val _
  have hv14_eq : v14.val = h.window.val := by rw [hv14]; exact cast_u32_u64_val _
  have hv15_eq : v15.val = h.flags.val := by rw [hv15]; exact cast_u16_u64_val _
  have hv16_eq : v16.val = h.protection.val := by rw [hv16]; exact cast_u16_u64_val _
  have hv19_eq : v19.val = (IScalar.hcast .U32 h.drift).val := by
    rw [hv19, hv19a]; exact cast_u32_u64_val _
  have hv20_eq : v20.val = h.clock.val := by rw [hv20]; exact cast_u32_u64_val _
  refine ⟨⟨tot_w, rfl, htot_val⟩, hl21', p1 _ _ _ (by decide) hf0, ?_, ?_, ?_,
    p5 _ _ _ (by decide) hf4, p6 _ _ _ (by decide) hf5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    p18 _ _ _ (by decide) hf17, ?_, ?_, ?_⟩
  · rw [← hv1_eq]; exact p2 _ _ _ (by decide) hf1
  · rw [← hv2_eq]; exact p3 _ _ _ (by decide) hf2
  · rw [← hv3_eq]; exact p4 _ _ _ (by decide) hf3
  · rw [← hv6]; exact p7 _ _ _ (by decide) hf6
  · rw [← hv7_eq]; exact p8 _ _ _ (by decide) hf7
  · rw [← hv8_eq]; exact p9 _ _ _ (by decide) hf8
  · rw [← hv9_eq]; exact p10 _ _ _ (by decide) hf9
  · rw [← hv10_eq]; exact p11 _ _ _ (by decide) hf10
  · rw [← hv11]; exact p12 _ _ _ (by decide) hf11
  · rw [← hv12_eq]; exact p13 _ _ _ (by decide) hf12
  · rw [← hv13_eq]; exact p14 _ _ _ (by decide) hf13
  · rw [← hv14_eq]; exact p15 _ _ _ (by decide) hf14
  · rw [← hv15_eq]; exact p16 _ _ _ (by decide) hf15
  · rw [← hv16_eq]; exact p17 _ _ _ (by decide) hf16
  · rw [← hv18]; exact p19 _ _ _ (by decide) hf18
  · rw [← hv19_eq]; exact p20 _ _ _ (by decide) hf19
  · rw [← hv20_eq]; exact hf20

/-- Writing a valid `Audio` header into a buffer of exact packet length
`HEADER + payloadLen h` and parsing it back recovers the exact `Audio` header. -/
theorem audio_roundtrip (h : packet.Audio) (bytes : Slice Std.U8)
    (hvalid : ValidAudio h)
    (hlen : bytes.val.length = packet.HEADER.val + payloadLen h) :
    (do
      let out ← packet.write_audio h bytes
      match out.1 with
      | some _ => packet.parse_audio out.2
      | none => ok (.Err .TooShort))
    ⦃ r => r = .Ok h ⦄ := by
  have hhdr : packet.HEADER.val = 88 := by simp [packet.HEADER]
  step with write_audio_spec h bytes (by omega)
    as ⟨out, n, hsome, _, hlen21, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11,
      hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20⟩
  rw [hsome]
  have hv3_lt : h.stream.val < 2 ^ (8 * 2) := by scalar_tac
  have hv4_lt : h.timeline.val < 2 ^ (8 * 8) := by scalar_tac
  have hv5_lt : h.index.val < 2 ^ (8 * 8) := by scalar_tac
  have hv6_lt : (IScalar.hcast .U64 h.capture).val < 2 ^ (8 * 8) := by scalar_tac
  have hv7_lt : h.rate.val < 2 ^ (8 * 4) := by scalar_tac
  have hv8_lt : h.frames.val < 2 ^ (8 * 2) := by scalar_tac
  have hv9_lt : h.channels.val < 2 ^ (8 * 1) := by scalar_tac
  have hv10_lt : formatCode h.format < 2 ^ (8 * 1) := by cases h.format <;> decide
  have hv11_lt : (IScalar.hcast .U64 h.level).val < 2 ^ (8 * 8) := by scalar_tac
  have hv12_lt : (IScalar.hcast .U32 h.level_slope).val < 2 ^ (8 * 4) := by scalar_tac
  have hv13_lt : h.span.val < 2 ^ (8 * 4) := by scalar_tac
  have hv14_lt : h.window.val < 2 ^ (8 * 4) := by scalar_tac
  have hv15_lt : h.flags.val < 2 ^ (8 * 2) := by scalar_tac
  have hv16_lt : h.protection.val < 2 ^ (8 * 2) := by scalar_tac
  have hv17_lt : h.stamped_index.val < 2 ^ (8 * 8) := by scalar_tac
  have hv18_lt : (IScalar.hcast .U64 h.stamped_departure).val < 2 ^ (8 * 8) := by scalar_tac
  have hv19_lt : (IScalar.hcast .U32 h.drift).val < 2 ^ (8 * 4) := by scalar_tac
  have hv20_lt : h.clock.val < 2 ^ (8 * 4) := by scalar_tac
  unfold packet.parse_audio
  have hnotlt21 : ¬ out.2.len < packet.HEADER := by
    have : out.2.len.val = out.2.val.length := rfl
    scalar_tac
  simp only [hnotlt21, ↓reduceIte]
  step with kind_of_hasLE out.2 packet.KIND_AUDIO hg0 hg1 hg2 as ⟨rk, hrk⟩
  rw [hrk]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step with read_of_hasLE out.2 6#usize 2#usize h.stream.val hg3 (by decide) hv3_lt as ⟨o3, r3, ho3', hr3⟩
  step with read_of_hasLE out.2 8#usize 8#usize h.timeline.val hg4 (by decide) hv4_lt as ⟨o4, r4, ho4', hr4⟩
  step with read_of_hasLE out.2 16#usize 8#usize h.index.val hg5 (by decide) hv5_lt as ⟨o5, r5, ho5', hr5⟩
  step with read_of_hasLE out.2 24#usize 8#usize (IScalar.hcast .U64 h.capture).val hg6 (by decide) hv6_lt
    as ⟨o6, r6, ho6', hr6⟩
  step with read_of_hasLE out.2 32#usize 4#usize h.rate.val hg7 (by decide) hv7_lt as ⟨o7, r7, ho7', hr7⟩
  step with read_of_hasLE out.2 36#usize 2#usize h.frames.val hg8 (by decide) hv8_lt as ⟨o8, r8, ho8', hr8⟩
  rw [ho3', ho4', ho5', ho6', ho7', ho8']
  step with read_of_hasLE out.2 38#usize 1#usize h.channels.val hg9 (by decide) hv9_lt as ⟨o9, r9, ho9', hr9⟩
  step with read_of_hasLE out.2 39#usize 1#usize (formatCode h.format) hg10 (by decide) hv10_lt
    as ⟨o10, r10, ho10', hr10⟩
  step with read_of_hasLE out.2 40#usize 8#usize (IScalar.hcast .U64 h.level).val hg11 (by decide) hv11_lt
    as ⟨o11, r11, ho11', hr11⟩
  step with read_of_hasLE out.2 48#usize 4#usize (IScalar.hcast .U32 h.level_slope).val hg12 (by decide) hv12_lt
    as ⟨o12, r12, ho12', hr12⟩
  step with read_of_hasLE out.2 52#usize 4#usize h.span.val hg13 (by decide) hv13_lt as ⟨o13, r13, ho13', hr13⟩
  step with read_of_hasLE out.2 56#usize 4#usize h.window.val hg14 (by decide) hv14_lt as ⟨o14, r14, ho14', hr14⟩
  step with read_of_hasLE out.2 60#usize 2#usize h.flags.val hg15 (by decide) hv15_lt as ⟨o15, r15, ho15', hr15⟩
  rw [ho9', ho10', ho11', ho12', ho13', ho14', ho15']
  step with read_of_hasLE out.2 62#usize 2#usize h.protection.val hg16 (by decide) hv16_lt as ⟨o16, r16, ho16', hr16⟩
  step with read_of_hasLE out.2 64#usize 8#usize h.stamped_index.val hg17 (by decide) hv17_lt as ⟨o17, r17, ho17', hr17⟩
  step with read_of_hasLE out.2 72#usize 8#usize (IScalar.hcast .U64 h.stamped_departure).val hg18 (by decide) hv18_lt
    as ⟨o18, r18, ho18', hr18⟩
  step with read_of_hasLE out.2 80#usize 4#usize (IScalar.hcast .U32 h.drift).val hg19 (by decide) hv19_lt
    as ⟨o19, r19, ho19', hr19⟩
  step with read_of_hasLE out.2 84#usize 4#usize h.clock.val hg20 (by decide) hv20_lt as ⟨o20, r20, ho20', hr20⟩
  rw [ho16', ho17', ho18', ho19', ho20']
  step as ⟨fc_r, hfc_r⟩
  have hfc_val : fc_r.val = formatCode h.format := by
    rw [hfc_r, UScalar.cast_val_mod_pow_of_inBounds_eq, hr10]
    rw [hr10]; cases h.format <;> decide
  step with format_from_code_spec fc_r as ⟨ofmt, hf16, hf24, _⟩
  have hofmt : ofmt = some h.format := by
    cases hfmt : h.format <;> simp [hfmt, formatCode] at hfc_val
    · exact hf16 hfc_val
    · exact hf24 hfc_val
  rw [hofmt]
  step as ⟨p_stream, hp_stream⟩
  step as ⟨p_cap, hp_cap⟩
  step as ⟨p_drift_u, hp_drift_u⟩
  step as ⟨p_drift, hp_drift⟩
  step as ⟨p_rate, hp_rate⟩
  step as ⟨p_frames, hp_frames⟩
  step as ⟨p_ch, hp_ch⟩
  step as ⟨p_lvl, hp_lvl⟩
  step as ⟨p_sl_u, hp_sl_u⟩
  step as ⟨p_sl, hp_sl⟩
  step as ⟨p_span, hp_span⟩
  step as ⟨p_win, hp_win⟩
  step as ⟨p_flags, hp_flags⟩
  step as ⟨p_prot, hp_prot⟩
  step as ⟨p_sdep, hp_sdep⟩
  step as ⟨p_clk, hp_clk⟩
  have hhdr_eq :
      ({ stream := p_stream, timeline := r4, index := r5, capture := p_cap, drift := p_drift,
         rate := p_rate, frames := p_frames, channels := p_ch, format := h.format,
         level := p_lvl, level_slope := p_sl, span := p_span, window := p_win,
         flags := p_flags, protection := p_prot, stamped_index := r17,
         stamped_departure := p_sdep, clock := p_clk } : packet.Audio) = h := by
    have to_u8 : ∀ (x : Std.U8) (u : Std.U64), u.val = x.val → UScalar.cast .U8 u = x := by
      intro x u hu; apply UScalar.eq_of_val_eq
      rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hu]; scalar_tac
    have to_u16 : ∀ (x : Std.U16) (u : Std.U64), u.val = x.val → UScalar.cast .U16 u = x := by
      intro x u hu; apply UScalar.eq_of_val_eq
      rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hu]; scalar_tac
    have to_u32 : ∀ (x : Std.U32) (u : Std.U64), u.val = x.val → UScalar.cast .U32 u = x := by
      intro x u hu; apply UScalar.eq_of_val_eq
      rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hu]; scalar_tac
    have to_i32 : ∀ (x : Std.I32) (u : Std.U64), u.val = (IScalar.hcast .U32 x).val →
        UScalar.hcast .I32 (UScalar.cast .U32 u) = x := by
      intro x u hu
      have hu32 : UScalar.cast .U32 u = IScalar.hcast .U32 x := to_u32 _ u hu
      rw [hu32]; cases x with | mk bv => congr 1; simp [IScalar.hcast]
    cases h
    congr 1
    · rw [hp_stream]; exact to_u16 _ r3 hr3
    · exact UScalar.eq_of_val_eq hr4
    · exact UScalar.eq_of_val_eq hr5
    · rw [hp_cap]; exact hcast_i64_u64_i64 _ r6 hr6
    · rw [hp_drift, hp_drift_u]; exact to_i32 _ r19 hr19
    · rw [hp_rate]; exact to_u32 _ r7 hr7
    · rw [hp_frames]; exact to_u16 _ r8 hr8
    · rw [hp_ch]; exact to_u8 _ r9 hr9
    · rw [hp_lvl]; exact hcast_i64_u64_i64 _ r11 hr11
    · rw [hp_sl, hp_sl_u]; exact to_i32 _ r12 hr12
    · rw [hp_span]; exact to_u32 _ r13 hr13
    · rw [hp_win]; exact to_u32 _ r14 hr14
    · rw [hp_flags]; exact to_u16 _ r15 hr15
    · rw [hp_prot]; exact to_u16 _ r16 hr16
    · exact UScalar.eq_of_val_eq hr17
    · rw [hp_sdep]; exact hcast_i64_u64_i64 _ r18 hr18
    · rw [hp_clk]; exact to_u32 _ r20 hr20
  rw [hhdr_eq]
  step with validate_audio_spec h as ⟨rval, hrval⟩
  rw [hrval.mpr hvalid]
  step as ⟨sub, hsub⟩
  step with payload_spec h as ⟨pl, hpl⟩
  have hsub_eq : sub = pl := by
    apply UScalar.eq_of_val_eq
    rw [hsub, hpl, core.num.Usize.wrapping_sub_val_eq, UScalar.size_UScalarTyUsize]
    have hblen : out.2.len.val = out.2.val.length := rfl
    have hmax : out.2.val.length ≤ Usize.max := out.2.property
    have hlt : Usize.max < Usize.size := by
      have h1 := usize_max_succ; rw [usize_max_eq] at h1
      rw [Usize.size_def, Usize.numBits_def]; omega
    rw [hblen, hlen21, hlen,
      show packet.HEADER.val + payloadLen h + (Usize.size - packet.HEADER.val) =
        payloadLen h + Usize.size by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp [hsub_eq]


end Unisono.Packet
