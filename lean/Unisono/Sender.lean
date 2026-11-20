/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar

/-!
# The sender of a stream

What the functions of `unisono_core::sender` do to the numbering of frames
and to the departure that packets carry.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Sender

/-- The departure that a sender knows is of a packet that it sent in this
timeline: the first frame of that packet is before the next frame. -/
def Stamped (s : sender.Sender) : Prop :=
  s.stamped = true → s.stamped_index.val < s.next.val

/-- The header of the next packet. Its first frame is the next frame of the
timeline, and the frame after its last is the next frame afterwards, so the
packets of a timeline follow each other without a break. The numbering stops
at the largest index. A header that says it carries a departure carries that
of a packet whose first frame is before its own. -/
theorem packet_spec (s : sender.Sender) (frames : Std.U16) (capture : Std.I64)
    (drift : Std.I32) :
    sender.Sender.packet s frames capture drift ⦃ out =>
      out.1.timeline = s.timeline ∧ out.1.index = s.next ∧ out.1.frames = frames
      ∧ out.1.capture = capture ∧ out.1.drift = drift
      ∧ out.2.timeline = s.timeline
      ∧ out.2.next.val = min U64.max (s.next.val + frames.val)
      ∧ (Stamped s → Stamped out.2)
      ∧ (out.1.flags = packet.FLAG_STAMPED ↔ s.stamped = true)
      ∧ (Stamped s → s.stamped = true → out.1.stamped_index.val < out.1.index.val) ⦄ := by
  unfold sender.Sender.packet
  step as ⟨i, hi⟩
  have hiv : i.val = frames.val := by
    rw [hi, UScalar.cast_val_mod_pow_of_inBounds_eq]
    scalar_tac
  step as ⟨next, hnext⟩
  have hnv : next.val = min U64.max (s.next.val + frames.val) := by
    rw [hnext, U64.saturating_add_val, hiv]
  have hmax : s.next.val ≤ U64.max := by scalar_tac
  have hflag : (0#u16 : Std.U16) ≠ packet.FLAG_STAMPED := by
    simp [packet.FLAG_STAMPED]
  split
  · rename_i hst
    simp only [WP.spec_ok, true_and]
    refine ⟨hnv, fun hS hst' => ?_, by simp [hst], fun hS _ => hS hst⟩
    have := hS hst'
    simp only at this ⊢
    omega
  · rename_i hst
    have hst' : s.stamped = false := by simpa using hst
    simp only [WP.spec_ok, true_and]
    refine ⟨hnv, fun _ hc => ?_, ?_, fun _ hc => ?_⟩
    · simp only at hc
      rw [hst'] at hc
      cases hc
    · simp [hst', hflag]
    · rw [hst'] at hc
      cases hc

/-- Taking in a departure keeps the known departure one of a packet that was
sent in this timeline, and changes neither the timeline nor the numbering. -/
theorem departed_spec (s : sender.Sender) (timeline index : Std.U64) (departure : Std.I64) :
    sender.Sender.departed s timeline index departure ⦃ s' =>
      s'.timeline = s.timeline ∧ s'.next = s.next ∧ (Stamped s → Stamped s') ⦄ := by
  unfold sender.Sender.departed
  split
  · simp
  · split
    · simp
    · rename_i hlt
      have hlt' : index.val < s.next.val := by scalar_tac
      split
      · split
        · simp
        · simp only [WP.spec_ok, true_and]
          exact fun _ _ => hlt'
      · simp only [WP.spec_ok, true_and]
        exact fun _ _ => hlt'

/-- A restart starts a timeline with a larger number, unless the number was
the largest there is, and numbers its frames from zero. No departure of the
new timeline is known. -/
theorem restart_spec (s : sender.Sender) (timeline : Std.U64) :
    sender.Sender.restart s timeline ⦃ s' =>
      s'.next.val = 0 ∧ s'.stamped = false
      ∧ s.timeline.val ≤ s'.timeline.val ∧ timeline.val ≤ s'.timeline.val
      ∧ (s.timeline.val < U64.max → s.timeline.val < s'.timeline.val) ⦄ := by
  unfold sender.Sender.restart
  step as ⟨after, hafter⟩
  have hav : after.val = min U64.max (s.timeline.val + 1) := by
    rw [hafter, U64.saturating_add_val]
    rfl
  have hmax : s.timeline.val ≤ U64.max := by scalar_tac
  split
  · rename_i hgt
    have : after.val < timeline.val := by scalar_tac
    simp only [WP.spec_ok]
    refine ⟨rfl, trivial, ?_, le_refl _, fun _ => ?_⟩ <;> omega
  · rename_i hle
    have : timeline.val ≤ after.val := by scalar_tac
    simp only [WP.spec_ok]
    refine ⟨rfl, trivial, ?_, ?_, fun _ => ?_⟩ <;> omega

end Unisono.Sender
