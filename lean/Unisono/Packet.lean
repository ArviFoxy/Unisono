/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar

/-!
# The audio packet

What the functions of `unisono_core::packet` compute.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Packet

/-- Reading a number from bytes returns, for every slice and every place. -/
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

/-- Writing a number into bytes returns, for every slice and every place. -/
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

@[step]
theorem format_bytes_total (f : packet.Format) : packet.Format.bytes f ⦃ _ => True ⦄ := by
  unfold packet.Format.bytes
  split <;> simp

@[step]
theorem format_code_total (f : packet.Format) : packet.Format.code f ⦃ _ => True ⦄ := by
  unfold packet.Format.code
  split <;> simp

@[step]
theorem format_from_code_total (c : Std.U8) : packet.Format.from_code c ⦃ _ => True ⦄ := by
  unfold packet.Format.from_code
  split <;> simp

@[step]
theorem payload_total (h : packet.Audio) : packet.payload h ⦃ _ => True ⦄ := by
  unfold packet.payload
  step*

/-- Reading a header returns, with a header or with a reason for rejection,
for every string of bytes. -/
theorem parse_audio_total (bytes : Slice Std.U8) :
    packet.parse_audio bytes ⦃ _ => True ⦄ := by
  unfold packet.parse_audio
  simp only
  step*

/-- Writing a header returns, for every header and every buffer. -/
theorem write_audio_total (h : packet.Audio) (bytes : Slice Std.U8) :
    packet.write_audio h bytes ⦃ _ => True ⦄ := by
  unfold packet.write_audio
  simp only
  step*

/-! ## Reports and the answers to them -/

/-- Telling the kind of a packet returns for every string of bytes. -/
@[step]
theorem kind_total (bytes : Slice Std.U8) : packet.kind bytes ⦃ _ => True ⦄ := by
  unfold packet.kind
  step*

/-- Reading a report returns, with a report or with a reason for rejection,
for every string of bytes. -/
theorem parse_report_total (bytes : Slice Std.U8) :
    packet.parse_report bytes ⦃ _ => True ⦄ := by
  unfold packet.parse_report
  step*

/-- Reading an answer to a report returns for every string of bytes. -/
theorem parse_echo_total (bytes : Slice Std.U8) :
    packet.parse_echo bytes ⦃ _ => True ⦄ := by
  unfold packet.parse_echo
  step*

/-- Writing an answer to a report returns for every answer and every
buffer. -/
theorem write_echo_total (e : packet.Echo) (bytes : Slice Std.U8) :
    packet.write_echo e bytes ⦃ _ => True ⦄ := by
  unfold packet.write_echo
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

/-- Writing a report, padded to a length, returns for every report, buffer
and length. -/
theorem write_report_total (r : packet.Report) (bytes : Slice Std.U8) (length : Std.Usize) :
    packet.write_report r bytes length ⦃ _ => True ⦄ := by
  unfold packet.write_report
  split <;> simp only <;> step*

end Unisono.Packet
