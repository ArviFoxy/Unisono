/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed

/-!
# Four-timestamp NTP exchanges and sliding minimum-RTT selection

Exact arithmetic specification of `ntp_exchange`, totality and structural
invariants of `SlidingMinRtt<W>` (`len ≤ W`, variance floor, non-negative
`path_ns`), and strict monotonic deduplication of emitted measurement IDs.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.MinRtt

@[step]
private theorem slice_get_total {T : Type} (s : Slice T) (i : Std.Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T) s i ⦃ _ => True ⦄ := by
  simp [core.slice.Slice.get, core.slice.index.Usize.get]

@[step]
private theorem slice_get_mut_total {T : Type} (s : Slice T) (i : Std.Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice T) s i ⦃ _ => True ⦄ := by
  simp [core.slice.Slice.get_mut, core.slice.index.Usize.get_mut]

/-! ## Four-timestamp NTP exchange -/

/-- Exact integer specification of `ntp_exchange`: rejects negative peer
processing time or negative round-trip delay, and otherwise returns the
four-timestamp offset, non-negative RTT, and local midpoint. -/
@[step]
theorem ntp_exchange_spec (ex : min_rtt.Exchange) :
    min_rtt.ntp_exchange ex ⦃ o =>
      let leg := ex.t4.val - ex.t1.val
      let proc := ex.t3.val - ex.t2.val
      let rtt := leg - proc
      ((proc < 0 ∨ rtt < 0) → o = none)
      ∧ (0 ≤ proc → 0 ≤ rtt →
          ∃ s, o = some s
            ∧ s.id = ex.id
            ∧ s.rtt_ns.val = Fixed.clamp64 rtt
            ∧ 0 ≤ s.rtt_ns.val
            ∧ s.offset_ns.val = Fixed.clamp64 (((ex.t2.val - ex.t1.val) + (ex.t3.val - ex.t4.val)) / 2)
            ∧ s.midpoint_ns.val = Fixed.clamp64 (ex.t1.val + leg / 2)) ⦄ := by
  have ht1 : -2^63 ≤ ex.t1.val ∧ ex.t1.val ≤ 2^63 - 1 := by scalar_tac
  have ht2 : -2^63 ≤ ex.t2.val ∧ ex.t2.val ≤ 2^63 - 1 := by scalar_tac
  have ht3 : -2^63 ≤ ex.t3.val ∧ ex.t3.val ≤ 2^63 - 1 := by scalar_tac
  have ht4 : -2^63 ≤ ex.t4.val ∧ ex.t4.val ≤ 2^63 - 1 := by scalar_tac
  unfold min_rtt.ntp_exchange
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨leg, hleg⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨proc_t, hproc⟩
  have hlegv : leg.val = ex.t4.val - ex.t1.val := by
    rw [hleg, I128.wrapping_sub_val _ _ (by rw [hi, hi1, I64.cast_I128_val, I64.cast_I128_val]; omega),
      hi, hi1, I64.cast_I128_val, I64.cast_I128_val]
  have hprocv : proc_t.val = ex.t3.val - ex.t2.val := by
    rw [hproc, I128.wrapping_sub_val _ _ (by rw [hi2, hi3, I64.cast_I128_val, I64.cast_I128_val]; omega),
      hi2, hi3, I64.cast_I128_val, I64.cast_I128_val]
  split
  · rename_i hneg
    have hpn : ex.t3.val - ex.t2.val < 0 := by rw [← hprocv]; scalar_tac
    rw [WP.spec_ok]
    exact ⟨fun _ => rfl, fun hp _ => by omega⟩
  · rename_i hnn
    have hpp : 0 ≤ ex.t3.val - ex.t2.val := by rw [← hprocv]; scalar_tac
    step as ⟨rtt, hrtt⟩
    have hrttv : rtt.val = (ex.t4.val - ex.t1.val) - (ex.t3.val - ex.t2.val) := by
      rw [hrtt, I128.wrapping_sub_val _ _ (by rw [hlegv, hprocv]; omega), hlegv, hprocv]
    split
    · rename_i hrneg
      have hrn : (ex.t4.val - ex.t1.val) - (ex.t3.val - ex.t2.val) < 0 := by
        rw [← hrttv]; scalar_tac
      rw [WP.spec_ok]
      exact ⟨fun _ => rfl, fun _ hr => by omega⟩
    · rename_i hrnn
      have hrp : 0 ≤ (ex.t4.val - ex.t1.val) - (ex.t3.val - ex.t2.val) := by
        rw [← hrttv]; scalar_tac
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step as ⟨d1, hd1⟩
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      step as ⟨d2, hd2⟩
      step as ⟨i8, hi8⟩
      step with Fixed.div_floor_wide_spec i8 2#i128 as ⟨off, hoff_pos, _⟩
      step as ⟨i9, hi9⟩
      step with Fixed.div_floor_wide_spec leg 2#i128 as ⟨i10, hi10_pos, _⟩
      step as ⟨mid, hmid⟩
      step with Fixed.saturate_spec mid as ⟨s_mid, hsmid⟩
      step with Fixed.saturate_spec off as ⟨s_off, hsoff⟩
      step with Fixed.saturate_spec rtt as ⟨s_rtt, hsrtt⟩
      have hd1v : d1.val = ex.t2.val - ex.t1.val := by
        rw [hd1, I128.wrapping_sub_val _ _ (by rw [hi4, hi5, I64.cast_I128_val, I64.cast_I128_val]; omega),
          hi4, hi5, I64.cast_I128_val, I64.cast_I128_val]
      have hd2v : d2.val = ex.t3.val - ex.t4.val := by
        rw [hd2, I128.wrapping_sub_val _ _ (by rw [hi6, hi7, I64.cast_I128_val, I64.cast_I128_val]; omega),
          hi6, hi7, I64.cast_I128_val, I64.cast_I128_val]
      have hi8v : i8.val = (ex.t2.val - ex.t1.val) + (ex.t3.val - ex.t4.val) := by
        rw [hi8, I128.wrapping_add_val _ _ (by rw [hd1v, hd2v]; omega), hd1v, hd2v]
      have hoffv : off.val = ((ex.t2.val - ex.t1.val) + (ex.t3.val - ex.t4.val)) / 2 := by
        rw [hoff_pos (by decide), hi8v]
      have hi10v : i10.val = (ex.t4.val - ex.t1.val) / 2 := by
        rw [hi10_pos (by decide), hlegv]
      have hmidv : mid.val = ex.t1.val + (ex.t4.val - ex.t1.val) / 2 := by
        rw [hmid, I128.wrapping_add_val _ _ (by rw [hi9, I64.cast_I128_val, hi10v]; omega),
          hi9, I64.cast_I128_val, hi10v]
      refine ⟨fun h => by omega, fun _ _ => ⟨_, rfl, rfl, by rw [hsrtt, hrttv], ?_,
        by rw [hsoff, hoffv], by rw [hsmid, hmidv]⟩⟩
      rw [hsrtt, hrttv]
      simp only [Fixed.clamp64]
      omega

/-! ## Helper accessors and variance clamp -/

@[step]
theorem get_i64_total (buf : Slice Std.I64) (idx : Std.Usize) :
    min_rtt.get_i64 buf idx ⦃ _ => True ⦄ := by
  unfold min_rtt.get_i64
  simp only [core.slice.Slice.get, core.slice.index.Usize.get]
  cases buf[idx]? <;> simp

@[step]
theorem set_i64_total (buf : Slice Std.I64) (idx : Std.Usize) (val : Std.I64) :
    min_rtt.set_i64 buf idx val ⦃ _ => True ⦄ := by
  unfold min_rtt.set_i64
  simp only [core.slice.Slice.get_mut, core.slice.index.Usize.get_mut]
  cases buf[idx]? <;> simp

@[step]
theorem clamp_var_spec (val : Std.I128) (floor : Std.U64) :
    min_rtt.clamp_var val floor ⦃ v =>
      min floor.val min_rtt.MAX_VAR_NS2.val ≤ v.val
      ∧ v.val ≤ min_rtt.MAX_VAR_NS2.val ⦄ := by
  have hmax : min_rtt.MAX_VAR_NS2.val = 1000000000000000000 := by
    unfold min_rtt.MAX_VAR_NS2; rfl
  unfold min_rtt.clamp_var
  step as ⟨i, hi⟩
  have hiv : i.val = floor.val := by rw [hi, U64.hcast_I128_val]
  have hlow :
      (if val < i then ok (UScalar.hcast .I128 floor) else ok val)
        ⦃ cl => (floor.val : ℤ) ≤ cl.val ⦄ := by
    split
    · rw [WP.spec_ok, U64.hcast_I128_val]
    · rw [WP.spec_ok]; scalar_tac
  apply WP.spec_bind hlow
  intro cl hcl
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = min_rtt.MAX_VAR_NS2.val := by rw [hi1, U64.hcast_I128_val]
  have hbound :
      (if cl > i1 then ok (UScalar.hcast .I128 min_rtt.MAX_VAR_NS2) else ok cl)
        ⦃ b => (min floor.val min_rtt.MAX_VAR_NS2.val : ℤ) ≤ b.val
          ∧ b.val ≤ (min_rtt.MAX_VAR_NS2.val : ℤ) ⦄ := by
    split
    · rw [WP.spec_ok, U64.hcast_I128_val]; omega
    · rw [WP.spec_ok]; have : cl.val ≤ i1.val := by scalar_tac
      omega
  apply WP.spec_bind hbound
  rintro b ⟨hblo, hbhi⟩
  rw [WP.spec_ok]
  have hb_nonneg : 0 ≤ b.val := by omega
  have hb_lt : b.val < (2 ^ UScalarTy.U64.numBits : ℕ) := by
    have : UScalarTy.U64.numBits = 64 := rfl
    rw [this]; omega
  have hcast : ((IScalar.hcast .U64 b).val : ℤ) = b.val := by
    rw [IScalar.hcast_val_eq, Int.emod_eq_of_lt hb_nonneg (by exact_mod_cast hb_lt)]
    exact Int.toNat_of_nonneg hb_nonneg
  omega

/-! ## SlidingMinRtt lifecycle, bounds, and deduplication -/

variable {W : Std.Usize}

@[step]
theorem new_spec (W stride : Std.Usize) (initial_var_ns2 floor_var_ns2 : Std.U64) :
    min_rtt.SlidingMinRtt.new W stride initial_var_ns2 floor_var_ns2 ⦃ s =>
      s.len.val = 0 ∧ s.len.val ≤ W.val ∧ s.has_emitted = false
      ∧ 1 ≤ s.floor_var_ns2.val ∧ s.floor_var_ns2.val ≤ min_rtt.MAX_VAR_NS2.val
      ∧ s.floor_var_ns2.val ≤ s.ewma_var_ns2.val
      ∧ s.ewma_var_ns2.val ≤ min_rtt.MAX_VAR_NS2.val ⦄ := by
  have hmax : min_rtt.MAX_VAR_NS2.val = 1000000000000000000 := by
    unfold min_rtt.MAX_VAR_NS2; rfl
  unfold min_rtt.SlidingMinRtt.new
  have hfloor :
      (if floor_var_ns2 = 0#u64 then ok 1#u64
       else if floor_var_ns2 > min_rtt.MAX_VAR_NS2 then ok min_rtt.MAX_VAR_NS2
       else ok floor_var_ns2)
        ⦃ fl => 1 ≤ fl.val ∧ fl.val ≤ min_rtt.MAX_VAR_NS2.val ⦄ := by
    split
    · rw [WP.spec_ok]; scalar_tac
    · split
      · rw [WP.spec_ok]; omega
      · rw [WP.spec_ok]; scalar_tac
  apply WP.spec_bind hfloor
  rintro fl ⟨hfl1, hflhi⟩
  have hinit :
      (if initial_var_ns2 < fl then ok fl
       else if initial_var_ns2 > min_rtt.MAX_VAR_NS2 then ok min_rtt.MAX_VAR_NS2
       else ok initial_var_ns2)
        ⦃ ini => fl.val ≤ ini.val ∧ ini.val ≤ min_rtt.MAX_VAR_NS2.val ⦄ := by
    split
    · rw [WP.spec_ok]; omega
    · split
      · rw [WP.spec_ok]; omega
      · rw [WP.spec_ok]; scalar_tac
  apply WP.spec_bind hinit
  rintro ini ⟨hini_lo, hini_hi⟩
  have hstr : (if stride = 0#usize then ok 1#usize else ok stride) ⦃ _ => True ⦄ := by
    split <;> simp
  apply WP.spec_bind hstr
  intro _ _
  rw [WP.spec_ok]
  exact ⟨rfl, Nat.zero_le _, rfl, hfl1, hflhi, hini_lo, hini_hi⟩

@[step]
theorem clear_min_windows_loop_spec (s : min_rtt.SlidingMinRtt W) (i : Std.Usize) :
    min_rtt.SlidingMinRtt.clear_min_windows_loop s i ⦃ s' =>
      s'.len = s.len ∧ s'.seen = s.seen ∧ s'.stride = s.stride
      ∧ s'.has_emitted = s.has_emitted ∧ s'.last_emitted_id = s.last_emitted_id
      ∧ s'.floor_var_ns2 = s.floor_var_ns2 ∧ s'.ewma_var_ns2 = s.ewma_var_ns2
      ∧ s'.initial_var_ns2 = s.initial_var_ns2 ⦄ := by
  unfold min_rtt.SlidingMinRtt.clear_min_windows_loop
  apply loop.spec_decr_nat
    (measure := fun x : min_rtt.SlidingMinRtt W × Std.Usize => min_rtt.MIN_RTT_WINDOWS.val - x.2.val)
    (inv := fun x : min_rtt.SlidingMinRtt W × Std.Usize =>
      x.1.len = s.len ∧ x.1.seen = s.seen ∧ x.1.stride = s.stride
      ∧ x.1.has_emitted = s.has_emitted ∧ x.1.last_emitted_id = s.last_emitted_id
      ∧ x.1.floor_var_ns2 = s.floor_var_ns2 ∧ x.1.ewma_var_ns2 = s.ewma_var_ns2
      ∧ x.1.initial_var_ns2 = s.initial_var_ns2)
  · rintro ⟨s1, i1⟩ ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    dsimp only at h1 h2 h3 h4 h5 h6 h7 h8
    unfold min_rtt.SlidingMinRtt.clear_min_windows_loop.body
    simp only
    split
    · have hlt : i1.val < min_rtt.MIN_RTT_WINDOWS.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [lift, bind_ok, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
        Std.uncurry]
      cases (Array.to_slice_mut s1.min_windows).1[i1]? <;>
        (simp only [bind_ok, WP.spec_ok]; exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, by omega⟩)
    · simp [h1, h2, h3, h4, h5, h6, h7, h8]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[step]
theorem clear_min_windows_spec (s : min_rtt.SlidingMinRtt W) :
    min_rtt.SlidingMinRtt.clear_min_windows s ⦃ s' =>
      s'.len = s.len ∧ s'.seen = s.seen ∧ s'.stride = s.stride
      ∧ s'.has_emitted = s.has_emitted ∧ s'.last_emitted_id = s.last_emitted_id
      ∧ s'.floor_var_ns2 = s.floor_var_ns2 ∧ s'.ewma_var_ns2 = s.ewma_var_ns2
      ∧ s'.initial_var_ns2 = s.initial_var_ns2 ⦄ := by
  unfold min_rtt.SlidingMinRtt.clear_min_windows
  step as ⟨s1, h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

@[step]
theorem reset_loop_spec (s : min_rtt.SlidingMinRtt W) (i : Std.Usize) :
    min_rtt.SlidingMinRtt.reset_loop s i ⦃ s' =>
      s'.floor_var_ns2 = s.floor_var_ns2 ∧ s'.initial_var_ns2 = s.initial_var_ns2 ⦄ := by
  unfold min_rtt.SlidingMinRtt.reset_loop
  apply loop.spec_decr_nat
    (measure := fun x : min_rtt.SlidingMinRtt W × Std.Usize => W.val - x.2.val)
    (inv := fun x : min_rtt.SlidingMinRtt W × Std.Usize =>
      x.1.floor_var_ns2 = s.floor_var_ns2 ∧ x.1.initial_var_ns2 = s.initial_var_ns2)
  · rintro ⟨s1, i1⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    unfold min_rtt.SlidingMinRtt.reset_loop.body
    simp only
    split
    · have hlt : i1.val < W.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      simp only [lift, bind_ok, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
        Std.uncurry]
      cases (Array.to_slice_mut s1.slots).1[i1]? <;>
        (simp only [bind_ok, WP.spec_ok]; exact ⟨⟨h1, h2⟩, by omega⟩)
    · simp [h1, h2]
  · exact ⟨rfl, rfl⟩

@[step]
theorem reset_spec (s : min_rtt.SlidingMinRtt W) :
    min_rtt.SlidingMinRtt.reset s ⦃ s' =>
      s'.len.val = 0 ∧ s'.has_emitted = false
      ∧ s'.floor_var_ns2 = s.floor_var_ns2
      ∧ s'.ewma_var_ns2 = s.initial_var_ns2 ⦄ := by
  unfold min_rtt.SlidingMinRtt.reset
  step as ⟨s1, hf, hi⟩
  step as ⟨s2, hl, _, _, he, _, hfl, hew, _⟩
  exact ⟨by rw [hl]; rfl, he, hfl.trans hf, hew.trans hi⟩

@[step]
theorem record_min_rtt_spec (s : min_rtt.SlidingMinRtt W) (midpoint_ns rtt_ns : Std.I64) :
    min_rtt.SlidingMinRtt.record_min_rtt s midpoint_ns rtt_ns ⦃ s' =>
      s'.len = s.len ∧ s'.seen = s.seen ∧ s'.stride = s.stride
      ∧ s'.has_emitted = s.has_emitted ∧ s'.last_emitted_id = s.last_emitted_id
      ∧ s'.floor_var_ns2 = s.floor_var_ns2 ∧ s'.ewma_var_ns2 = s.ewma_var_ns2 ⦄ := by
  unfold min_rtt.SlidingMinRtt.record_min_rtt
  step as ⟨i⟩
  step as ⟨i1⟩
  step as ⟨win⟩
  step as ⟨i2⟩
  step as ⟨i3⟩
  step as ⟨i4⟩
  step as ⟨oldest⟩
  step as ⟨i5⟩
  step as ⟨i6⟩
  step as ⟨i7⟩
  step as ⟨far⟩
  have hrestart :
      (if s.has_min_window = true then do
         let i8 ← lift (IScalar.cast .I128 win)
         ok (decide (i8 ≤ far))
       else ok true) ⦃ _ => True ⦄ := by
    split <;> simp [lift]
  apply WP.spec_bind hrestart
  intro restart _
  have hfin :
      ∀ (a : Array min_rtt.Slot W) (i8 i9 i10 : Std.Usize) (i11 : Std.U64) (b : Bool)
        (i12 : Std.U64) (b1 : Bool) (i13 i14 i15 : Std.U64)
        (a1 : Array min_rtt.RttWindow 8#usize) (i16 : Std.I64) (b2 : Bool),
        i8 = s.len → i11 = s.seen → i10 = s.stride → b = s.has_emitted →
        i12 = s.last_emitted_id → i15 = s.floor_var_ns2 → i13 = s.ewma_var_ns2 →
        (do
          let i17 ← lift (IScalar.cast .I128 win)
          let o ← fixed.rem_euclid_wide i17 min_rtt.MIN_RTT_WINDOWS
          match o with
          | none =>
            ok ({ slots := a, len := i8, next := i9, stride := i10, seen := i11,
                  has_emitted := b, last_emitted_id := i12, has_ewma := b1,
                  ewma_var_ns2 := i13, initial_var_ns2 := i14, floor_var_ns2 := i15,
                  min_windows := a1, newest_window := i16, has_min_window := b2 } :
                  min_rtt.SlidingMinRtt W)
          | some place => do
            let (sl, back) ← lift (Array.to_slice_mut a1)
            let (o1, get_back) ←
              core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice min_rtt.RttWindow)
                sl place
            match o1 with
            | none =>
              ok { slots := a, len := i8, next := i9, stride := i10, seen := i11,
                   has_emitted := b, last_emitted_id := i12, has_ewma := b1,
                   ewma_var_ns2 := i13, initial_var_ns2 := i14, floor_var_ns2 := i15,
                   min_windows := back (get_back none), newest_window := i16, has_min_window := b2 }
            | some slot => do
              let faster ←
                if slot.held = true then
                  if (slot.window != win) = true then ok true
                  else ok (decide (rtt_ns < slot.rtt_ns))
                else ok true
              if faster = true then
                ok { slots := a, len := i8, next := i9, stride := i10, seen := i11,
                     has_emitted := b, last_emitted_id := i12, has_ewma := b1,
                     ewma_var_ns2 := i13, initial_var_ns2 := i14, floor_var_ns2 := i15,
                     min_windows := back (get_back (some { held := true, window := win, rtt_ns := rtt_ns })),
                     newest_window := i16, has_min_window := b2 }
              else
                ok { slots := a, len := i8, next := i9, stride := i10, seen := i11,
                     has_emitted := b, last_emitted_id := i12, has_ewma := b1,
                     ewma_var_ns2 := i13, initial_var_ns2 := i14, floor_var_ns2 := i15,
                     min_windows := back (get_back o1), newest_window := i16, has_min_window := b2 })
          ⦃ s' =>
            s'.len = s.len ∧ s'.seen = s.seen ∧ s'.stride = s.stride
            ∧ s'.has_emitted = s.has_emitted ∧ s'.last_emitted_id = s.last_emitted_id
            ∧ s'.floor_var_ns2 = s.floor_var_ns2 ∧ s'.ewma_var_ns2 = s.ewma_var_ns2 ⦄ := by
    intro a i8 i9 i10 i11 b i12 b1 i13 i14 i15 a1 i16 b2 h1 h2 h3 h4 h5 h6 h7
    step as ⟨i17⟩
    step as ⟨o⟩
    cases o with
    | none => simp [h1, h2, h3, h4, h5, h6, h7]
    | some place =>
      step as ⟨s_sl, back⟩
      step as ⟨o1, get_back⟩
      cases o1 with
      | none => simp [h1, h2, h3, h4, h5, h6, h7]
      | some slot =>
        have hf :
            (if slot.held = true then
               if (slot.window != win) = true then ok true
               else ok (decide (rtt_ns < slot.rtt_ns))
             else ok true) ⦃ _ => True ⦄ := by
          split
          · split <;> simp
          · simp
        apply WP.spec_bind hf
        intro faster _
        split <;> simp [h1, h2, h3, h4, h5, h6, h7]
  split
  · step with clear_min_windows_spec s as ⟨s1, h1, h2, h3, h4, h5, h6, h7, _⟩
    exact hfin _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7
  · step as ⟨i8⟩
    split
    · simp
    · have hnw : (if win > s.newest_window then ok win else ok s.newest_window) ⦃ _ => True ⦄ := by
        split <;> simp
      apply WP.spec_bind hnw
      intro i17 _
      exact hfin _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl

@[step]
theorem min_rtt_ns_loop_total (a : Array min_rtt.RttWindow 8#usize) (newest : Std.I64)
    (oldest : Std.I128) (best : Option Std.I64) (i : Std.Usize) :
    min_rtt.SlidingMinRtt.min_rtt_ns_loop a newest oldest best i ⦃ _ => True ⦄ := by
  unfold min_rtt.SlidingMinRtt.min_rtt_ns_loop
  apply loop.spec_decr_nat
    (measure := fun x : Option Std.I64 × Std.Usize => min_rtt.MIN_RTT_WINDOWS.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨best1, i1⟩ _
    unfold min_rtt.SlidingMinRtt.min_rtt_ns_loop.body
    simp only
    split
    · have hlt : i1.val < min_rtt.MIN_RTT_WINDOWS.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s_sl⟩
      step as ⟨o⟩
      have hstep :
          (match o with
            | none => ok best1
            | some slot =>
              if slot.held = true then do
                let i2 ← lift (IScalar.cast .I128 slot.window)
                if i2 ≥ oldest then
                  if slot.window ≤ newest then do
                    let i3 ←
                      match best1 with
                      | none => ok slot.rtt_ns
                      | some prev => if prev ≤ slot.rtt_ns then ok prev else ok slot.rtt_ns
                    ok (some i3)
                  else ok best1
                else ok best1
              else ok best1) ⦃ _ => True ⦄ := by
        cases o with
        | none => simp
        | some slot =>
          dsimp only
          split
          · step as ⟨i2⟩
            split
            · split
              · cases best1 with
                | none => simp
                | some prev => dsimp only; split <;> simp
              · simp
            · simp
          · simp
      apply WP.spec_bind hstep
      intro best2 _
      step as ⟨i2, hi2⟩
      rw [hi2, hnext]; omega
    · simp
  · trivial

@[step]
theorem min_rtt_ns_total (s : min_rtt.SlidingMinRtt W) :
    min_rtt.SlidingMinRtt.min_rtt_ns s ⦃ _ => True ⦄ := by
  unfold min_rtt.SlidingMinRtt.min_rtt_ns
  split
  · step*
  · simp

/-- `path_ns` is total and always returns a non-negative one-way delay. -/
@[step]
theorem path_ns_spec (s : min_rtt.SlidingMinRtt W) :
    min_rtt.SlidingMinRtt.path_ns s ⦃ p => 0 ≤ p.val ⦄ := by
  unfold min_rtt.SlidingMinRtt.path_ns
  step as ⟨o⟩
  cases o with
  | none => simp
  | some rtt =>
    simp only
    split
    · rename_i hpos
      have hr : 0 < rtt.val := by scalar_tac
      rw [WP.spec_ok]
      simp only [IScalar.val, core.num.I64.wrapping_shr_bv_eq]
      have h1 : (1#u32).val % 64 = 1 := by decide
      rw [h1, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
      change 0 ≤ rtt.val / 2^1
      omega
    · simp

/-- `variance_ns2` is total and never drops below `floor_var_ns2`. -/
@[step]
theorem variance_ns2_spec (s : min_rtt.SlidingMinRtt W) :
    min_rtt.SlidingMinRtt.variance_ns2 s ⦃ v => s.floor_var_ns2.val ≤ v.val ⦄ := by
  unfold min_rtt.SlidingMinRtt.variance_ns2
  split
  · simp
  · rw [WP.spec_ok]; scalar_tac

@[step]
theorem best_in_window_loop_total (a : Array min_rtt.Slot W) (limit : Std.Usize)
    (best : Option min_rtt.Sampled) (i : Std.Usize) :
    min_rtt.SlidingMinRtt.best_in_window_loop a limit best i ⦃ _ => True ⦄ := by
  unfold min_rtt.SlidingMinRtt.best_in_window_loop
  apply loop.spec_decr_nat
    (measure := fun x : Option min_rtt.Sampled × Std.Usize => limit.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨best1, i1⟩ _
    unfold min_rtt.SlidingMinRtt.best_in_window_loop.body
    simp only
    split
    · have hlt : i1.val < limit.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s_sl⟩
      step as ⟨o⟩
      have hstep :
          (match o with
            | none => ok best1
            | some slot =>
              if slot.used = true then do
                let (s1, pick) ←
                  match best1 with
                  | none => ok (slot.sample, true)
                  | some cur => do
                    let b ←
                      if slot.sample.rtt_ns < cur.rtt_ns then ok true
                      else if slot.sample.rtt_ns = cur.rtt_ns then
                        ok (decide (slot.sample.id > cur.id))
                      else ok false
                    ok (slot.sample, b)
                if pick = true then ok (some s1) else ok best1
              else ok best1) ⦃ _ => True ⦄ := by
        cases o with
        | none => simp
        | some slot =>
          dsimp only
          split
          · cases best1 with
            | none => simp
            | some cur =>
              dsimp only
              split
              · simp
              · split
                · simp only [bind_ok, Std.uncurry]; split <;> simp
                · simp
          · simp
      apply WP.spec_bind hstep
      intro best2 _
      step as ⟨i2, hi2⟩
      rw [hi2, hnext]; omega
    · simp
  · trivial

@[step]
theorem best_in_window_total (s : min_rtt.SlidingMinRtt W) :
    min_rtt.SlidingMinRtt.best_in_window s ⦃ _ => True ⦄ := by
  unfold min_rtt.SlidingMinRtt.best_in_window
  have hlim : (if s.len < W then ok s.len else ok W) ⦃ _ => True ⦄ := by split <;> simp
  apply WP.spec_bind hlim
  intro lim _
  step*

@[step]
theorem update_variance_loop0_total (a : Array min_rtt.Slot W) (best_rtt_ns : Std.I64)
    (limit : Std.Usize) (excesses : Array Std.I64 W) (count i : Std.Usize) :
    min_rtt.SlidingMinRtt.update_variance_loop0 a best_rtt_ns limit excesses count i
      ⦃ _ => True ⦄ := by
  unfold min_rtt.SlidingMinRtt.update_variance_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I64 W × Std.Usize × Std.Usize => limit.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨ex1, c1, i1⟩ _
    unfold min_rtt.SlidingMinRtt.update_variance_loop0.body
    simp only
    split
    · have hlt : i1.val < limit.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s_sl⟩
      step as ⟨o⟩
      have hpair :
          (match o with
            | none => ok (ex1, c1)
            | some slot =>
              if slot.used = true then do
                let diff ← lift (core.num.I64.saturating_sub slot.sample.rtt_ns best_rtt_ns)
                let clamped ←
                  if diff < 0#i64 then ok 0#i64
                  else if diff > min_rtt.MAX_EXCESS_NS then ok min_rtt.MAX_EXCESS_NS
                  else ok diff
                let (s1, back) ← lift (Array.to_slice_mut ex1)
                let (o1, get_back) ←
                  core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.I64) s1 c1
                match o1 with
                | none => ok (back (get_back none), c1)
                | some _ => do
                  let c2 ← lift (core.num.Usize.saturating_add c1 1#usize)
                  ok (back (get_back (some clamped)), c2)
              else ok (ex1, c1)) ⦃ _ => True ⦄ := by
        cases o with
        | none => simp
        | some slot =>
          dsimp only
          split
          · step as ⟨diff⟩
            have hcl :
                (if diff < 0#i64 then ok 0#i64
                 else if diff > min_rtt.MAX_EXCESS_NS then ok min_rtt.MAX_EXCESS_NS
                 else ok diff) ⦃ _ => True ⦄ := by
              split
              · simp
              · split <;> simp
            apply WP.spec_bind hcl
            intro clamped _
            step as ⟨s1, back⟩
            step as ⟨o1, get_back⟩
            cases o1 <;> step*
          · simp
      apply WP.spec_bind hpair
      rintro ⟨ex2, c2⟩ _
      step as ⟨i2, hi2⟩
      rw [hi2, hnext]; omega
    · simp
  · trivial

@[step]
theorem update_variance_loop1_loop0_total (excesses : Array Std.I64 W) (key : Std.I64)
    (b : Std.Usize) :
    min_rtt.SlidingMinRtt.update_variance_loop1_loop0 excesses key b ⦃ _ => True ⦄ := by
  unfold min_rtt.SlidingMinRtt.update_variance_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I64 W × Std.Usize => x.2.val)
    (inv := fun _ => True)
  · rintro ⟨ex1, b1⟩ _
    unfold min_rtt.SlidingMinRtt.update_variance_loop1_loop0.body
    simp only
    split
    · have hpos : 0 < b1.val := by scalar_tac
      have hprev : (core.num.Usize.wrapping_sub b1 1#usize).val = b1.val - 1 := by
        simp only [core.num.Usize.wrapping_sub_val_eq, UScalar.size]
        have hb : b1.val < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
        have h1 : (1#usize).val = 1 := rfl
        rw [h1]
        have hadd : b1.val + (2 ^ UScalarTy.Usize.numBits - 1) =
            (b1.val - 1) + 1 * 2 ^ UScalarTy.Usize.numBits := by omega
        rw [hadd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      step as ⟨prev_idx, hprev_eq⟩
      step as ⟨s_sl⟩
      step as ⟨prev⟩
      split
      · step as ⟨s1, back⟩
        step as ⟨s2⟩
        rw [hprev_eq, hprev]; omega
      · simp
    · simp
  · trivial

@[step]
theorem update_variance_loop1_total (excesses : Array Std.I64 W) (count a : Std.Usize) :
    min_rtt.SlidingMinRtt.update_variance_loop1 excesses count a ⦃ _ => True ⦄ := by
  unfold min_rtt.SlidingMinRtt.update_variance_loop1
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I64 W × Std.Usize => count.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨ex1, a1⟩ _
    unfold min_rtt.SlidingMinRtt.update_variance_loop1.body
    simp only
    split
    · have hlt : a1.val < count.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add a1 1#usize).val = a1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s_sl⟩
      step as ⟨key⟩
      step as ⟨ex2, b⟩
      step as ⟨s1, back⟩
      step as ⟨s2⟩
      step as ⟨a2, ha2⟩
      rw [ha2, hnext]; omega
    · simp
  · trivial

@[step]
theorem update_variance_spec (s : min_rtt.SlidingMinRtt W) (best_rtt_ns : Std.I64) :
    min_rtt.SlidingMinRtt.update_variance s best_rtt_ns ⦃ out =>
      min s.floor_var_ns2.val min_rtt.MAX_VAR_NS2.val ≤ out.1.val
      ∧ out.2.len = s.len ∧ out.2.has_emitted = s.has_emitted
      ∧ out.2.last_emitted_id = s.last_emitted_id
      ∧ out.2.floor_var_ns2 = s.floor_var_ns2 ⦄ := by
  unfold min_rtt.SlidingMinRtt.update_variance
  have hlim : (if s.len < W then ok s.len else ok W) ⦃ _ => True ⦄ := by split <;> simp
  apply WP.spec_bind hlim
  intro lim _
  split
  · step with variance_ns2_spec s as ⟨v, hv⟩
    exact le_trans (Nat.min_le_left _ _) hv
  · step as ⟨ex1, count⟩
    split
    · step with variance_ns2_spec s as ⟨v, hv⟩
      exact le_trans (Nat.min_le_left _ _) hv
    · step as ⟨ex2⟩
      step as ⟨mid⟩
      step as ⟨s_sl⟩
      step as ⟨med⟩
      step as ⟨i⟩
      step as ⟨i1⟩
      step as ⟨med_sq⟩
      step as ⟨i2⟩
      step as ⟨denom⟩
      step as ⟨raw_var⟩
      have hsm :
          (if s.has_ewma = true then do
            let i3 ← lift (UScalar.hcast .I128 s.ewma_var_ns2)
            let i4 ← lift (core.num.I128.wrapping_mul i3 17#i128)
            let i5 ← lift (core.num.I128.wrapping_mul raw_var 3#i128)
            let blended ← lift (core.num.I128.wrapping_add i4 i5)
            fixed.div_floor_wide blended 20#i128
          else ok raw_var) ⦃ _ => True ⦄ := by
        split <;> step*
      apply WP.spec_bind hsm
      intro sm _
      step with clamp_var_spec sm s.floor_var_ns2 as ⟨v, hv_lo, _⟩
      exact hv_lo

/-- **Observation totality, bounded ring length, variance floor, and strict
monotonic deduplication:** `SlidingMinRtt.observe` always terminates, preserves
`len ≤ W` and `floor_var_ns2`, respects the variance floor on every emitted
measurement, and guarantees that any emitted measurement has an `id` strictly
greater than `last_emitted_id` whenever a measurement was previously emitted. -/
@[step]
theorem observe_spec (s : min_rtt.SlidingMinRtt W) (ex : min_rtt.Exchange) :
    min_rtt.SlidingMinRtt.observe s ex ⦃ out =>
      (s.len.val ≤ W.val → out.2.len.val ≤ W.val)
      ∧ out.2.floor_var_ns2 = s.floor_var_ns2
      ∧ (∀ m, out.1 = some m →
          min s.floor_var_ns2.val min_rtt.MAX_VAR_NS2.val ≤ m.variance_ns2.val
          ∧ out.2.has_emitted = true
          ∧ out.2.last_emitted_id = m.id
          ∧ (s.has_emitted = true → s.last_emitted_id.val < m.id.val))
      ∧ (out.1 = none →
          out.2.has_emitted = s.has_emitted ∧ out.2.last_emitted_id = s.last_emitted_id) ⦄ := by
  unfold min_rtt.SlidingMinRtt.observe
  split
  · simp
  · step as ⟨o⟩
    cases o with
    | none => simp
    | some sampled =>
      simp only
      have hplace : (if s.next < W then ok s.next else ok 0#usize) ⦃ _ => True ⦄ := by
        split <;> simp
      apply WP.spec_bind hplace
      intro place _
      step as ⟨s_sl, back⟩
      step as ⟨o1, get_back⟩
      have ha :
          (match o1 with
            | none => ok (back (get_back none))
            | some _ => ok (back (get_back (some { used := true, sample := sampled }))))
            ⦃ _ => True ⦄ := by
        cases o1 <;> simp
      apply WP.spec_bind ha
      intro a _
      step as ⟨i⟩
      step as ⟨o2⟩
      step as ⟨i1⟩
      have hlen2 :
          (if s.len < W then ok (core.num.Usize.saturating_add s.len 1#usize) else ok s.len)
            ⦃ l2 => s.len.val ≤ W.val → l2.val ≤ W.val ⦄ := by
        split
        · rename_i hlt
          have hlt' : s.len.val < W.val := by scalar_tac
          have hadd : (core.num.Usize.saturating_add s.len 1#usize).val = s.len.val + 1 :=
            Usize.saturating_add_val _ _ (by scalar_tac)
          rw [WP.spec_ok]; intro _; omega
        · rw [WP.spec_ok]; exact id
      apply WP.spec_bind hlen2
      intro i2 hi2
      step with record_min_rtt_spec as ⟨s1, hs1_len, _, _, hs1_he, hs1_id, hs1_fl, _⟩
      step as ⟨i3⟩
      have hstride : (if s1.stride = 0#usize then ok 1#usize else ok s1.stride) ⦃ _ => True ⦄ := by
        split <;> simp
      apply WP.spec_bind hstride
      intro stride _
      step as ⟨i4⟩
      have hon :
          (if i3 >= i4 then do
            let i5 ← lift (UScalar.cast .U64 stride)
            let o3 ← lift (U64.checked_rem i3 i5)
            let i6 ← lift (core.option.Option.unwrap_or o3 1#u64)
            ok (decide (i6 = 0#u64))
          else ok false) ⦃ _ => True ⦄ := by
        split <;> step*
      apply WP.spec_bind hon
      intro on_stride _
      have hemit :
          ((do
            let o3 ← min_rtt.SlidingMinRtt.best_in_window { s1 with seen := i3 }
            match o3 with
            | none => ok (none, { s1 with seen := i3 })
            | some best =>
              let (variance_ns2, s2) ←
                min_rtt.SlidingMinRtt.update_variance { s1 with seen := i3 } best.rtt_ns
              if s2.has_emitted then
                if best.id <= s2.last_emitted_id then ok (none, s2)
                else
                  ok (some ({ id := best.id, midpoint_ns := best.midpoint_ns,
                              offset_ns := best.offset_ns, rtt_ns := best.rtt_ns,
                              variance_ns2 } : min_rtt.Measurement),
                      { s2 with last_emitted_id := best.id })
              else
                ok (some ({ id := best.id, midpoint_ns := best.midpoint_ns,
                            offset_ns := best.offset_ns, rtt_ns := best.rtt_ns,
                            variance_ns2 } : min_rtt.Measurement),
                    { s2 with has_emitted := true, last_emitted_id := best.id })) :
            Result (Option min_rtt.Measurement × min_rtt.SlidingMinRtt W))
          ⦃ out =>
            (s.len.val ≤ W.val → out.2.len.val ≤ W.val)
            ∧ out.2.floor_var_ns2 = s.floor_var_ns2
            ∧ (∀ m, out.1 = some m →
                min s.floor_var_ns2.val min_rtt.MAX_VAR_NS2.val ≤ m.variance_ns2.val
                ∧ out.2.has_emitted = true
                ∧ out.2.last_emitted_id = m.id
                ∧ (s.has_emitted = true → s.last_emitted_id.val < m.id.val))
            ∧ (out.1 = none →
                out.2.has_emitted = s.has_emitted ∧ out.2.last_emitted_id = s.last_emitted_id) ⦄ := by
        step as ⟨o3⟩
        cases o3 with
        | none =>
          simp only [WP.spec_ok]
          exact ⟨fun h => by rw [hs1_len]; exact hi2 h, hs1_fl,
            fun _ hc => (by cases hc), fun _ => ⟨hs1_he, hs1_id⟩⟩
        | some best =>
          simp only
          step with update_variance_spec as ⟨v, s2, hv, hs2_len, hs2_he, hs2_id, hs2_fl⟩
          have hlen_f : s.len.val ≤ W.val → s2.len.val ≤ W.val := fun h => by
            rw [hs2_len, hs1_len]; exact hi2 h
          have hfl_f : s2.floor_var_ns2 = s.floor_var_ns2 := hs2_fl.trans hs1_fl
          have hhe_f : s2.has_emitted = s.has_emitted := hs2_he.trans hs1_he
          have hid_f : s2.last_emitted_id = s.last_emitted_id := hs2_id.trans hs1_id
          have hv_f : min s.floor_var_ns2.val min_rtt.MAX_VAR_NS2.val ≤ v.val := by
            rw [← hs1_fl]; exact hv
          split
          · rename_i hhe2
            split
            · simp only [WP.spec_ok]
              exact ⟨hlen_f, hfl_f, fun _ hc => (by cases hc), fun _ => ⟨hhe_f, hid_f⟩⟩
            · rename_i hgt
              have hgt' : s2.last_emitted_id.val < best.id.val := by scalar_tac
              simp only [WP.spec_ok]
              refine ⟨hlen_f, hfl_f, fun m hm => ?_, fun hc => (by cases hc)⟩
              cases hm
              exact ⟨hv_f, hhe2, rfl, fun _ => by rw [← hid_f]; exact hgt'⟩
          · rename_i hne2
            have hne' : s.has_emitted = false := by
              rw [← hhe_f]; simpa using hne2
            simp only [WP.spec_ok]
            refine ⟨hlen_f, hfl_f, fun m hm => ?_, fun hc => (by cases hc)⟩
            cases hm
            exact ⟨hv_f, trivial, rfl, fun hc => by rw [hne'] at hc; cases hc⟩
      split
      · split
        · exact hemit
        · simp only [WP.spec_ok]
          exact ⟨fun h => by rw [hs1_len]; exact hi2 h, hs1_fl,
            fun _ hc => (by cases hc), fun _ => ⟨hs1_he, hs1_id⟩⟩
      · exact hemit

end Unisono.MinRtt
