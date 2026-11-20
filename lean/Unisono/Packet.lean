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

end Unisono.Packet
