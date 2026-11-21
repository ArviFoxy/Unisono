/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Packet.Wire
public import Unisono.Packet.Audio

/-!
# Packet parser/writer totality and kind consistency

Totality proofs for `Report`, `Echo`, `Request`, and `Needs` parsers/writers,
and consistency between `kind` and each packet parser.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Packet

/-! ## Reports and the answers to them (totality & kind consistency) -/

theorem parse_report_total (bytes : Slice Std.U8) :
    packet.parse_report bytes ⦃ _ => True ⦄ := by
  unfold packet.parse_report
  step*

theorem parse_echo_total (bytes : Slice Std.U8) :
    packet.parse_echo bytes ⦃ _ => True ⦄ := by
  unfold packet.parse_echo
  step*

theorem write_echo_total (e : packet.Echo) (bytes : Slice Std.U8) :
    packet.write_echo e bytes ⦃ _ => True ⦄ := by
  unfold packet.write_echo
  simp only
  step*

theorem parse_request_total (bytes : Slice Std.U8) :
    packet.parse_request bytes ⦃ _ => True ⦄ := by
  unfold packet.parse_request
  step*

theorem write_request_total (e : packet.Request) (bytes : Slice Std.U8) :
    packet.write_request e bytes ⦃ _ => True ⦄ := by
  unfold packet.write_request
  simp only
  step*

@[step]
theorem write_report_loop_total (bytes : Slice Std.U8) (length : Std.Usize)
    (written : Bool) (place : Std.Usize) :
    packet.write_report_loop bytes length written place ⦃ _ => True ⦄ := by
  unfold packet.write_report_loop
  apply loop.spec_decr_nat
    (measure := fun x : Slice Std.U8 × Bool × Std.Usize => length.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨bytes1, written1, place1⟩ _
    unfold packet.write_report_loop.body
    simp only
    split
    · have hlt : place1.val < length.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place1 1#usize).val = place1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨out⟩
      step as ⟨place2, hplace2⟩
      rw [hplace2]
      omega
    · simp
  · trivial

theorem write_report_total (r : packet.Report) (bytes : Slice Std.U8) (length : Std.Usize) :
    packet.write_report r bytes length ⦃ _ => True ⦄ := by
  unfold packet.write_report
  split <;> simp only <;> step*

/-- Pure specification of `packet.kind`: checks length ≥ 6, magic `unis`, and
version 1, returning byte 5 on success. -/
def kindOf (bytes : Slice Std.U8) : core.result.Result Std.U8 packet.Rejected :=
  if bytes.val.length < 6 then .Err .TooShort
  else if readLE bytes.val 0 4 ≠ packet.MAGIC.val then .Err .NotUnisono
  else if readLE bytes.val 4 1 ≠ packet.VERSION.val then
    .Err (.Version (bytes.val.getD 4 0#u8))
  else .Ok (bytes.val.getD 5 0#u8)

theorem kind_spec (bytes : Slice Std.U8) :
    packet.kind bytes ⦃ r => r = kindOf bytes ⦄ := by
  unfold packet.kind
  by_cases hlen : bytes.val.length < 6
  · have hnone5 : packet.read bytes 5#usize 1#usize ⦃ o => o = none ⦄ := by
      unfold packet.read packet.read_loop
      apply loop.spec_decr_nat
        (measure := fun x : Std.U64 × Std.Usize => 1 - x.2.val)
        (inv := fun x : Std.U64 × Std.Usize => x.2.val = 0)
      · rintro ⟨value, i⟩ hi0
        dsimp only at hi0
        unfold packet.read_loop.body
        simp only
        have hlt : i < 1#usize := by scalar_tac
        simp only [hlt, ↓reduceIte]
        have hadd := Usize.checked_add_bv_spec 5#usize i
        cases h : Usize.checked_add 5#usize i with
        | none => simp [lift]
        | some place =>
          rw [h] at hadd
          obtain ⟨-, hplace_val, -⟩ := hadd
          simp only [lift, bind_ok, core.slice.Slice.get, core.slice.index.Usize.get]
          have hget : bytes[place]? = none := by
            change bytes.val[place.val]? = none
            exact List.getElem?_eq_none (by scalar_tac)
          rw [hget]
          simp
      · rfl
    step with read_total bytes 0#usize 4#usize as ⟨o⟩
    step with read_total bytes 4#usize 1#usize as ⟨o1⟩
    step with hnone5 as ⟨o2, ho2⟩
    rw [ho2]
    cases o <;> cases o1 <;> simp [kindOf, hlen]
  · have hge6 : 6 ≤ bytes.val.length := by omega
    step with read_spec bytes 0#usize 4#usize (by scalar_tac) (by decide) as ⟨o, magic, ho, hmagic⟩
    step with read_spec bytes 4#usize 1#usize (by scalar_tac) (by decide) as ⟨o1, ver, ho1, hver⟩
    step with read_spec bytes 5#usize 1#usize (by scalar_tac) (by decide) as ⟨o2, kf, ho2, hkf⟩
    rw [ho, ho1, ho2]
    have hnotlt : ¬ bytes.val.length < 6 := by omega
    have hver1 : readLE bytes.val 4 1 = (bytes.val.getD 4 0#u8).val := by simp [readLE]
    have hkf1 : readLE bytes.val 5 1 = (bytes.val.getD 5 0#u8).val := by simp [readLE]
    unfold kindOf
    simp only [hnotlt, ↓reduceIte]
    cases hmb : (magic != packet.MAGIC) with
    | true =>
      have hmne : magic.val ≠ packet.MAGIC.val := by
        intro heq; have h1 : magic = packet.MAGIC := UScalar.eq_of_val_eq heq
        simp [h1] at hmb
      have hne : readLE bytes.val 0 4 ≠ packet.MAGIC.val := by omega
      simp [hne]
    | false =>
      have hmeq : magic.val = packet.MAGIC.val := by
        have h1 : magic = packet.MAGIC := by simpa using hmb
        rw [h1]
      have hm : readLE bytes.val 0 4 = packet.MAGIC.val := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, hm, ne_eq, not_true_eq_false]
      step as ⟨iv, hiv⟩
      have hiv_val : iv.val = packet.VERSION.val := by
        rw [hiv, UScalar.cast_val_mod_pow_of_inBounds_eq]; scalar_tac
      cases hvb : (ver != iv) with
      | true =>
        have hvne : ver.val ≠ iv.val := by
          intro heq; have h1 : ver = iv := UScalar.eq_of_val_eq heq
          simp [h1] at hvb
        have hv : readLE bytes.val 4 1 ≠ packet.VERSION.val := by omega
        simp only [hv, not_false_eq_true, ↓reduceIte]
        step as ⟨v8, hv8⟩
        congr 2
        apply UScalar.eq_of_val_eq
        rw [hv8, UScalar.cast_val_mod_pow_of_inBounds_eq, hver, hver1]
        scalar_tac
      | false =>
        have hveq : ver.val = iv.val := by
          have h1 : ver = iv := by simpa using hvb
          rw [h1]
        have hv : readLE bytes.val 4 1 = packet.VERSION.val := by omega
        simp only [Bool.false_eq_true, ↓reduceIte, hv, not_true_eq_false]
        step as ⟨k8, hk8⟩
        congr 1
        apply UScalar.eq_of_val_eq
        rw [hk8, UScalar.cast_val_mod_pow_of_inBounds_eq, hkf, hkf1]
        scalar_tac

/-- `parse_audio` succeeds only when `kind` returns `Ok KIND_AUDIO`. -/
theorem parse_audio_kind (bytes : Slice Std.U8) :
    packet.parse_audio bytes ⦃ r =>
      (∃ h, r = .Ok h) → kindOf bytes = .Ok packet.KIND_AUDIO ⦄ := by
  unfold packet.parse_audio
  dsimp only
  split
  · simp
  · step with kind_spec bytes as ⟨rk, hrk⟩
    cases rk with
    | Err _ => simp
    | Ok found =>
      dsimp only
      cases hne : (found != packet.KIND_AUDIO) with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hf : found = packet.KIND_AUDIO := by simpa using hne
        have hgoal : kindOf bytes = .Ok packet.KIND_AUDIO := by rw [← hrk, hf]
        step*

/-- `parse_report` succeeds only when `kind` returns `Ok KIND_REPORT`. -/
theorem parse_report_kind (bytes : Slice Std.U8) :
    packet.parse_report bytes ⦃ r =>
      (∃ rep, r = .Ok rep) → kindOf bytes = .Ok packet.KIND_REPORT ⦄ := by
  unfold packet.parse_report
  step with kind_spec bytes as ⟨rk, hrk⟩
  cases rk with
  | Err _ => simp
  | Ok found =>
    dsimp only
    cases hne : (found != packet.KIND_REPORT) with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : found = packet.KIND_REPORT := by simpa using hne
      have hgoal : kindOf bytes = .Ok packet.KIND_REPORT := by rw [← hrk, hf]
      step*

/-- `parse_echo` succeeds only when `kind` returns `Ok KIND_ECHO`. -/
theorem parse_echo_kind (bytes : Slice Std.U8) :
    packet.parse_echo bytes ⦃ r =>
      (∃ e, r = .Ok e) → kindOf bytes = .Ok packet.KIND_ECHO ⦄ := by
  unfold packet.parse_echo
  step with kind_spec bytes as ⟨rk, hrk⟩
  cases rk with
  | Err _ => simp
  | Ok found =>
    dsimp only
    cases hne : (found != packet.KIND_ECHO) with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : found = packet.KIND_ECHO := by simpa using hne
      have hgoal : kindOf bytes = .Ok packet.KIND_ECHO := by rw [← hrk, hf]
      step*

/-- `parse_request` succeeds only when `kind` returns `Ok KIND_REQUEST`. -/
theorem parse_request_kind (bytes : Slice Std.U8) :
    packet.parse_request bytes ⦃ r =>
      (∃ e, r = .Ok e) → kindOf bytes = .Ok packet.KIND_REQUEST ⦄ := by
  unfold packet.parse_request
  step with kind_spec bytes as ⟨rk, hrk⟩
  cases rk with
  | Err _ => simp
  | Ok found =>
    dsimp only
    cases hne : (found != packet.KIND_REQUEST) with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : found = packet.KIND_REQUEST := by simpa using hne
      have hgoal : kindOf bytes = .Ok packet.KIND_REQUEST := by rw [← hrk, hf]
      step*

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
theorem parse_needs_loop_total (bytes : Slice Std.U8) (newest : Std.U64) (count : Std.U8)
    (slots : Array Std.I32 11#usize) (said : Std.Usize) (i : Std.Usize) :
    packet.parse_needs_loop bytes newest count slots said i ⦃ _ => True ⦄ := by
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
      split
      · step as ⟨o⟩
        split
        · simp
        · split
          all_goals
            simp only [bind_ok, WP.spec_ok]
            rw [hnext]
            omega
      · simp
    · simp
  · trivial

/-- Reading the needs from a report returns, for every bytes. -/
theorem parse_needs_total (bytes : Slice Std.U8) :
    packet.parse_needs bytes ⦃ _ => True ⦄ := by
  unfold packet.parse_needs
  repeat' (first | split | step*)

/-- Writing the needs into a report returns, for every needs and bytes. -/
theorem write_needs_total (recent : packet.Recent) (bytes : Slice Std.U8) :
    packet.write_needs recent bytes ⦃ _ => True ⦄ := by
  unfold packet.write_needs
  repeat' (first | split | step*)

end Unisono.Packet
