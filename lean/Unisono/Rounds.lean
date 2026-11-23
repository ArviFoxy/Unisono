/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Arrivals
public import Unisono.Device
public import Unisono.Packet
public import Unisono.Presence

/-!
# How many rounds the loops of a cycle run

The functions that run in a cycle of a device, or when a packet arrives, hold
no recursion, so their work is the work of their loops. This file bounds the
loops over the frames a receiver holds, over the arrivals it keeps and over
the reports of a device: each is done after at most a number of rounds that
the sizes involved give, whatever the state and whatever arrives. The loops of
the estimator and of reading and writing a packet are shown to end where
those functions are proved total; their bounds are not stated here.

A translated loop is `loop body x`: `body` runs on a state and either ends
the loop or gives the state for the next round.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Rounds

/-- The loop of `body` from `x` is done within `n` rounds: each round returns,
and at most `n` of them run. -/
def EndsWithin {α β : Type} (body : α → Result (ControlFlow α β)) : ℕ → α → Prop
  | 0, _ => False
  | n + 1, x => body x ⦃ r =>
      match r with
      | .done _ => True
      | .cont x' => EndsWithin body n x' ⦄

/-- A loop whose every round lowers a number that cannot go below zero is done
within that number of rounds, and one more for the round that ends it. -/
theorem endsWithin_of_measure {α β : Type} (measure : α → ℕ) (inv : α → Prop)
    (body : α → Result (ControlFlow α β))
    (hBody : ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done _ => True
      | .cont x' => inv x' ∧ measure x' < measure x ⦄) :
    ∀ n x, inv x → measure x < n → EndsWithin body n x := by
  intro n
  induction n with
  | zero => intro x _ h; omega
  | succ n ih =>
    intro x hinv hlt
    simp only [EndsWithin]
    apply WP.spec_mono (hBody x hinv)
    intro r hr
    cases r with
    | done y => trivial
    | cont x' =>
      simp only at hr ⊢
      exact ih x' hr.1 (by omega)

variable {N : Std.Usize}

/-! ## The frames a receiver holds -/

/-- Marking the frames of a packet takes one round for each frame. -/
theorem mark_rounds (p : presence.Presence N) (first : Std.U64) (frames : Std.U32)
    (m : presence.Marked) :
    EndsWithin
      (fun x : presence.Presence N × presence.Marked × Std.U32 =>
        presence.Presence.mark_loop.body first frames x.1 x.2.1 x.2.2)
      (frames.val + 1) (p, m, 0#u32) := by
  apply endsWithin_of_measure
    (measure := fun x : presence.Presence N × presence.Marked × Std.U32 =>
      frames.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨s, m1, d⟩ -
    unfold presence.Presence.mark_loop.body
    simp only
    split
    · have hlt : d.val < frames.val := by scalar_tac
      have hf : frames.val ≤ U32.max := by scalar_tac
      step as ⟨outcome, s1, hout, hb1, hh1⟩
      step as ⟨m2, c1, c2, c3, c4⟩
      step as ⟨d1, hd1⟩
      have hv : d1.val = d.val + 1 := by
        rw [hd1]; exact U32.saturating_add_one_val d frames.val hlt hf
      omega
    · simp
  · trivial
  · have h0 : (0#u32).val = 0 := by rfl
    simp only [h0]
    omega

/-- Counting the frames held without a break takes at most one round for each
frame up to the limit. -/
theorem run_rounds (p : presence.Presence N) (start : Std.U64) (limit : Std.U32) :
    EndsWithin (fun count : Std.U32 => presence.Presence.run_loop.body p start limit count)
      (limit.val + 1) 0#u32 := by
  apply endsWithin_of_measure
    (measure := fun count : Std.U32 => limit.val - count.val) (inv := fun _ => True)
  · rintro count -
    unfold presence.Presence.run_loop.body
    have hl : limit.val ≤ U32.max := by scalar_tac
    split
    · have hlt : count.val < limit.val := by scalar_tac
      step as ⟨b, hb⟩
      split
      · step as ⟨count1, hcount1⟩
        have hv : count1.val = count.val + 1 := by
          rw [hcount1]; exact U32.saturating_add_one_val count limit.val hlt hl
        omega
      · simp
    · simp
  · trivial
  · have h0 : (0#u32).val = 0 := by rfl
    simp only [h0]
    omega

/-- Counting the frames not held without a break takes at most one round for
each frame up to the limit. -/
theorem gap_rounds (p : presence.Presence N) (start : Std.U64) (limit : Std.U32) :
    EndsWithin (fun count : Std.U32 => presence.Presence.gap_loop.body p start limit count)
      (limit.val + 1) 0#u32 := by
  apply endsWithin_of_measure
    (measure := fun count : Std.U32 => limit.val - count.val) (inv := fun _ => True)
  · rintro count -
    unfold presence.Presence.gap_loop.body
    have hl : limit.val ≤ U32.max := by scalar_tac
    split
    · have hlt : count.val < limit.val := by scalar_tac
      step as ⟨b, hb⟩
      split
      · simp
      · step as ⟨count1, hcount1⟩
        have hv : count1.val = count.val + 1 := by
          rw [hcount1]; exact U32.saturating_add_one_val count limit.val hlt hl
        omega
    · simp
  · trivial
  · have h0 : (0#u32).val = 0 := by rfl
    simp only [h0]
    omega

/-- Moving the playhead forward within the stretch takes one round for each
frame it passes. -/
theorem advance_rounds (p : presence.Presence N) (target index : Std.U64) :
    EndsWithin
      (fun x : presence.Presence N × Std.U64 =>
        presence.Presence.advance_loop.body target x.1 x.2)
      (target.val - index.val + 1) (p, index) := by
  apply endsWithin_of_measure
    (measure := fun x : presence.Presence N × Std.U64 => target.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨s, i⟩ -
    unfold presence.Presence.advance_loop.body
    simp only
    split
    · have hlt : i.val < target.val := by scalar_tac
      have ht : target.val ≤ U64.max := by scalar_tac
      step as ⟨was, s1, hb1, h0, h1⟩
      step as ⟨i1, hi1⟩
      have hv : i1.val = i.val + 1 := by
        rw [hi1]; exact U64.saturating_add_one_val i target.val hlt ht
      omega
    · simp
  · trivial
  · simp only
    omega

/-- Dropping everything a receiver holds takes one round for each word of its
stretch. -/
theorem clear_rounds (p : presence.Presence N) :
    EndsWithin
      (fun x : presence.Presence N × Std.Usize =>
        presence.Presence.clear_loop.body x.1 x.2)
      (N.val + 1) (p, 0#usize) := by
  apply endsWithin_of_measure
    (measure := fun x : presence.Presence N × Std.Usize => N.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨s, w⟩ -
    unfold presence.Presence.clear_loop.body
    simp only
    split
    · have hlt : w.val < N.val := by scalar_tac
      step as ⟨s1, hb1, hw1⟩
      step as ⟨w1, hw1v⟩
      have hv : w1.val = w.val + 1 := by
        rw [hw1v]; exact Usize.saturating_add_val _ _ (by scalar_tac)
      omega
    · simp
  · trivial
  · have h0 : (0#usize).val = 0 := by rfl
    simp only [h0]
    omega

/-! ## Arrivals, the line of a device, and packets -/

/-- Looking for the arrival of a packet takes at most one round for each
arrival that is kept. -/
theorem find_rounds {K : Std.Usize} (a : arrivals.Arrivals K) (index : Std.U64) :
    EndsWithin (fun place : Std.Usize => arrivals.Arrivals.find_loop.body a index place)
      (K.val + 1) 0#usize := by
  apply endsWithin_of_measure
    (measure := fun place : Std.Usize => K.val - place.val) (inv := fun _ => True)
  · rintro place -
    unfold arrivals.Arrivals.find_loop.body
    split
    · have hlt : place.val < K.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨arrival⟩
      split
      · split
        · simp
        · step as ⟨place1, hplace1⟩
          rw [hplace1]
          omega
      · step as ⟨place1, hplace1⟩
        rw [hplace1]
        omega
    · simp
  · trivial
  · have h0 : (0#usize).val = 0 := by rfl
    simp only [h0]
    omega

/-- Fitting the line of a device takes one round for each report it keeps. -/
theorem sums_rounds {W : Std.Usize} (d : device.Device W) (newest : device.Reading)
    (kept : Std.Usize) (sums : device.Sums) :
    EndsWithin
      (fun x : device.Sums × Std.Usize =>
        device.Device.sums_loop.body d newest kept x.1 x.2)
      (kept.val + 1) (sums, 0#usize) := by
  apply endsWithin_of_measure
    (measure := fun x : device.Sums × Std.Usize => kept.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨s, place⟩ -
    unfold device.Device.sums_loop.body
    simp only
    split
    · have hlt : place.val < kept.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o⟩
      cases o with
      | none =>
        simp only [bind_ok]
        step as ⟨place1, hplace1⟩
        rw [hplace1]
        omega
      | some reading =>
        simp only
        step as ⟨sums1⟩
        step as ⟨place1, hplace1⟩
        rw [hplace1]
        omega
    · simp
  · trivial
  · have h0 : (0#usize).val = 0 := by rfl
    simp only [h0]
    omega

/-- Shifting the timestamps of a device takes one round for each report it keeps. -/
theorem shift_rounds {W : Std.Usize} (d : device.Device W) (b : Std.I128) (kept : Std.Usize) :
    EndsWithin
      (fun x : device.Device W × Std.Usize =>
        device.Device.shift_loop.body b kept x.1 x.2)
      (kept.val + 1) (d, 0#usize) := by
  apply endsWithin_of_measure
    (measure := fun x : device.Device W × Std.Usize => kept.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨s, place⟩ -
    unfold device.Device.shift_loop.body
    simp only
    split
    · have hlt : place.val < kept.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add place 1#usize).val = place.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o⟩
      cases o with
      | none =>
        simp only [bind_ok]
        step as ⟨place1, hplace1⟩
        rw [hplace1]
        omega
      | some reading =>
        simp only
        step as ⟨i, hi⟩
        step as ⟨i1, hi1⟩
        step with Unisono.Fixed.saturate_spec as ⟨i2, hi2⟩
        simp only [Array.to_slice_mut, lift, core.slice.Slice.get_mut,
          core.slice.index.Usize.get_mut, bind_ok, Std.uncurry]
        cases s.readings.to_slice[place]? <;>
          (simp only [bind_ok, WP.spec_ok]; rw [hnext]; omega)
    · simp
  · trivial
  · have h0 : (0#usize).val = 0 := by rfl
    simp only [h0]
    omega

/-! ## Fixed-point scaling, sliding minimum-RTT, and peer lookup -/

/-- The binary long-division loop of `fixed.scale_div_pow2` takes at most
`shift + 1` rounds. -/
theorem scale_div_pow2_rounds (den : Std.I128) (shift : Std.U32) (rem frac : Std.I128) :
    EndsWithin
      (fun x : Std.I128 × Std.I128 × Std.U32 =>
        fixed.scale_div_pow2_loop.body den shift x.1 x.2.1 x.2.2)
      (shift.val + 1) (rem, frac, 0#u32) := by
  apply endsWithin_of_measure
    (measure := fun x : Std.I128 × Std.I128 × Std.U32 => shift.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨r, f, bit⟩ -
    unfold fixed.scale_div_pow2_loop.body
    simp only
    split
    · have hlt : bit.val < shift.val := by scalar_tac
      have hs : shift.val ≤ U32.max := by scalar_tac
      step as ⟨f1⟩; step as ⟨hu⟩
      have hbr : (if r >= hu then do
          let rem2 ← lift (core.num.I128.wrapping_sub r hu)
          let frac3 ← lift (core.num.I128.wrapping_add f1 1#i128)
          ok (rem2, frac3)
        else do
          let rem2 ← lift (core.num.I128.wrapping_add r r)
          ok (rem2, f1)) ⦃ _ => True ⦄ := by split <;> step*
      step with hbr as ⟨r1, f2⟩
      step as ⟨bit1, hbit1⟩
      have hv : bit1.val = bit.val + 1 := by
        rw [hbit1]; exact U32.saturating_add_one_val bit shift.val hlt hs
      omega
    · simp
  · trivial
  · have h0 : (0#u32).val = 0 := by rfl
    simp only [h0]; omega

/-- Scanning the sliding minimum-RTT window takes one round per slot up to `limit`. -/
theorem best_in_window_rounds {W : Std.Usize} (a : Array min_rtt.Slot W) (limit : Std.Usize) :
    EndsWithin
      (fun x : Option min_rtt.Sampled × Std.Usize =>
        min_rtt.SlidingMinRtt.best_in_window_loop.body a limit x.1 x.2)
      (limit.val + 1) (none, 0#usize) := by
  apply endsWithin_of_measure
    (measure := fun x : Option min_rtt.Sampled × Std.Usize => limit.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨best, i⟩ -
    unfold min_rtt.SlidingMinRtt.best_in_window_loop.body
    simp only
    split
    · have hlt : i.val < limit.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s⟩
      have hget : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice min_rtt.Slot) s i
          ⦃ _ => True ⦄ := by simp [core.slice.Slice.get, core.slice.index.Usize.get]
      step with hget as ⟨o⟩
      apply WP.spec_bind (Pₘ := fun _ => True)
      · cases o with
        | none => simp
        | some slot =>
          dsimp only
          split
          · apply WP.spec_bind (Pₘ := fun _ => True)
            · cases best with
              | none => simp
              | some cur =>
                dsimp only
                apply WP.spec_bind (Pₘ := fun _ => True)
                · split <;> (try split) <;> simp
                · intro _ _; simp
            · rintro ⟨_, pick⟩ -; cases pick <;> simp
          · simp
      · intro _ _
        step as ⟨i1, hi1⟩
        rw [hi1, hnext]; omega
    · simp
  · trivial
  · have h0 : (0#usize).val = 0 := by rfl
    simp only [h0]; omega

/-- Scanning the minimum-RTT history windows takes at most `MIN_RTT_WINDOWS + 1` rounds. -/
theorem min_rtt_ns_rounds (a : Array min_rtt.RttWindow 8#usize) (newest : Std.I64)
    (oldest : Std.I128) :
    EndsWithin
      (fun x : Option Std.I64 × Std.Usize =>
        min_rtt.SlidingMinRtt.min_rtt_ns_loop.body a newest oldest x.1 x.2)
      (min_rtt.MIN_RTT_WINDOWS.val + 1) (none, 0#usize) := by
  apply endsWithin_of_measure
    (measure := fun x : Option Std.I64 × Std.Usize => min_rtt.MIN_RTT_WINDOWS.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨best, i⟩ -
    unfold min_rtt.SlidingMinRtt.min_rtt_ns_loop.body
    simp only
    split
    · have hlt : i.val < min_rtt.MIN_RTT_WINDOWS.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s⟩
      have hget : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice min_rtt.RttWindow) s i
          ⦃ _ => True ⦄ := by simp [core.slice.Slice.get, core.slice.index.Usize.get]
      step with hget as ⟨o⟩
      apply WP.spec_bind (Pₘ := fun _ => True)
      · cases o with
        | none => simp
        | some slot =>
          dsimp only
          split
          · step as ⟨_⟩
            split
            · split
              · apply WP.spec_bind (Pₘ := fun _ => True)
                · cases best with
                  | none => simp
                  | some prev => dsimp only; split <;> simp
                · intro _ _; simp
              · simp
            · simp
          · simp
      · intro _ _
        step as ⟨i1, hi1⟩
        rw [hi1, hnext]; omega
    · simp
  · trivial
  · have h0 : (0#usize).val = 0 := by rfl
    simp only [h0]; omega

/-- Looking up a peer in the static peer table takes at most `peer_count + 1` rounds. -/
theorem find_peer_rounds (s : sync.Sync) (identity : Std.U64) :
    EndsWithin (fun i : Std.Usize => sync.Sync.find_peer_loop.body s identity i)
      (s.peer_count.val + 1) 0#usize := by
  apply endsWithin_of_measure
    (measure := fun i : Std.Usize => s.peer_count.val - i.val) (inv := fun _ => True)
  · rintro i -
    unfold sync.Sync.find_peer_loop.body
    split
    · have hlt : i.val < s.peer_count.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i 1#usize).val = i.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨sl⟩
      have hget : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice sync.PeerSlot) sl i
          ⦃ _ => True ⦄ := by simp [core.slice.Slice.get, core.slice.index.Usize.get]
      step with hget as ⟨o⟩
      cases o with
      | none => dsimp only; step as ⟨i1, hi1⟩; rw [hi1, hnext]; omega
      | some p =>
        dsimp only
        split
        · split
          · simp
          · step as ⟨i1, hi1⟩; rw [hi1, hnext]; omega
        · step as ⟨i1, hi1⟩; rw [hi1, hnext]; omega
    · simp
  · trivial
  · have h0 : (0#usize).val = 0 := by rfl
    simp only [h0]; omega

end Unisono.Rounds
