/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed
public import Unisono.Sender
public import Unisono.Player
public import Unisono.Due
public import Unisono.MinRtt
public import Unisono.Kalman
public import Unisono.Blue
public import Unisono.Sync
public import Unisono.Receiver
public import Unisono.Spec.Solution
public import Unisono.Spec.Run
public import Unisono.Spec.Objectives
public import Unisono.Spec.Topologies
public import Unisono.Spec.Limits
public import Unisono.Spec.Models.Bounded
public import Unisono.Spec.Models.Ideal
public import Unisono.Spec.AtLatency

/-!
# `Unisono.Spec.Solution` harness wrapping the translated `unisono-core`

This module composes the Aeneas-translated Rust core functions (`UnisonoCore`:
`sender.Sender`, `sync.Sync`, `receiver.Receiver`, `player.ModalPlayer`, and
the v2 wire headers in `packet`) into an event-driven
`Unisono.Spec.Solution H R CoreMsg`.

## Scope and differences from `unisono-runtime`

Because `unisono-runtime` is not translated to Lean, `stepHost` is a Lean
composition of the translated core functions rather than a proof about the
shipped runtime threads. In particular, `stepHost` differs from
`crates/unisono-runtime` in four ways:
- it does not fit an audio-device clock line (`Device`);
- it sends reports and peer probes only at playback-block requests rather than
  on independent timers;
- it constructs echo replies directly with `departure = arrival` (`T3 = T2`);
- it does not schedule `Timer` events.

All properties proved on `Core.solution` below refer to this Lean composition.

## Theorems proved in this module

1. **Causality:** `Core.solution` has type `Unisono.Spec.Solution H R CoreMsg`,
   depending strictly on each host's local event view and local clock readings.
2. **Topology membership (`usesGraph_of_peers`, `isStar_of_no_peers`):**
   Every message sent respects the configured star + peer allowlist graph. When
   every host's peer list is empty, `Core.solution` satisfies
   `Solution.IsStar p.sender` and never emits `peerProbe`, `peerEcho`, or
   `peerRelay` (`star_no_peer_messages`).
3. **Exact Star degeneration (`star_sync_snapshot_eq_sender_kalman`,
   `star_modal_player_eq_single_mode`):** With an empty peer list, `Sync`
   always publishes `peer_active = false`, `active_peers = 0`,
   `diff_var_ns2 = 0`, and `common_line = sender_filter.to_line`; and
   `ModalPlayer.cycle` produces the exact same `Plan` and playback state as
   single-mode `Player.cycle` at `star_gain`.
4. **Non-Zeno progress & request liveness (`progress`, `request_step`):**
   In every world satisfying `World.WithinBounds B`, the run advances past
   every true time `T` and handles every playback request `(r, b)`.
5. **Within-block speed and conditional boundary-step bounds
   (`withinBlock_speed_bound`, `boundary_step_safe`):**
   Every block planned by `Core.solution` has pace offset within
   `±reachOf limit / 2^64 ≤ 3/1000`, yielding the exact `World.speed` bound
   between consecutive samples inside every block unconditionally in every
   world satisfying `World.WithinBounds B`, and a per-sample advance bound
   across adjacent non-empty block boundaries whenever `regulation.jump ≥ 3`,
   `Position.advance` does not saturate `U64.MAX`, and no silence restart
   occurred. Full `Solution.WithinSpeed` across all boundaries is open.
6. **Component-level ideal-world exactness and trajectory check
   (`ideal_ntp_exchange_exact`, `ideal_kalman_and_sender_time_exact`,
   `ideal_modal_cycle_unity`, `ideal_zero_cost_objectives`):**
   Within the 64-bit nanosecond/frame range, `ntp_exchange` recovers exact host
   clock offset `Δc`, `KalmanFilter` preserves the zero-innovation fixed point
   `(Δc, 0)` and `SyncSnapshot.sender_time` maps local time to exact sender
   time `t + Δc`, and `ModalPlayer.cycle` plans `timing.Step.UNITY`.
   `ideal_zero_cost_objectives` proves that any playback trajectory already
   on the ideal unity-step schedule has zero objective costs; connecting a full
   run of `Core.solution` to any of the six `Unisono.Spec.Objectives` remains
   open in every model.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Core

open Aeneas Aeneas.Std Result
open unisono_core
open Unisono.Spec
open scoped ENNReal

/-! ## 1. Total evaluation of translated Aeneas functions and fixed-point conversions -/

theorem exists_ok_of_spec {α : Type} {r : Result α} {P : α → Prop}
    (h : r ⦃ P ⦄) : ∃ x, r = ok x ∧ P x := by
  cases r with
  | ret x => exact ⟨x, rfl, by simpa [WP.spec_ok] using h⟩
  | vis _ _ => simp [WP.spec_vis] at h
  | div => simp [WP.spec_div] at h

theorem ok_inj {α : Type} {x y : α} (h : (ok x : Result α) = ok y) : x = y := by
  have hx : (ok x : Result α) ⦃ z => z = x ⦄ := by simp
  rw [h, WP.spec_ok] at hx
  exact hx.symm

/-- Extract the return value of an Aeneas `Result α`, falling back to `default`
only on non-`ok` branches (which are unreachable whenever a `WP` spec holds). -/
def evalResult {α : Type} (r : Result α) (default : α) : α := by
  classical
  exact if h : ∃ x, r = ok x then Classical.choose h else default

theorem evalResult_eq_of_ok {α : Type} {x d : α} :
    evalResult (ok x) d = x := by
  classical
  unfold evalResult
  have hex : ∃ y, (ok x : Result α) = ok y := ⟨x, rfl⟩
  simp only [hex, ↓reduceDIte]
  exact (ok_inj (Classical.choose_spec hex)).symm

theorem evalResult_spec_eq {α : Type} {r : Result α} {P : α → Prop} {d : α}
    (h : r ⦃ P ⦄) : r = ok (evalResult r d) ∧ P (evalResult r d) := by
  obtain ⟨x, hx, hPx⟩ := exists_ok_of_spec h
  rw [hx, evalResult_eq_of_ok]
  exact ⟨rfl, hPx⟩

theorem evalResult_of_spec {α : Type} {r : Result α} {P : α → Prop} {d : α}
    (h : r ⦃ P ⦄) : P (evalResult r d) :=
  (evalResult_spec_eq (d := d) h).2

/-- Quantize a real clock reading (in seconds) to clamped signed 64-bit nanoseconds. -/
def toNs (t : ℝ) : Std.I64 :=
  ⟨BitVec.ofInt 64 (max (-2 ^ 63) (min ⌊t * (10 ^ 9 : ℝ)⌋ (2 ^ 63 - 1)))⟩

theorem toNs_val (t : ℝ) :
    (toNs t).val = max (-2 ^ 63) (min ⌊t * (10 ^ 9 : ℝ)⌋ (2 ^ 63 - 1)) := by
  unfold toNs
  change (BitVec.ofInt 64 (max (-2 ^ 63) (min ⌊t * (10 ^ 9 : ℝ)⌋ (2 ^ 63 - 1)))).toInt = _
  rw [BitVec.toInt_ofInt]
  have h := Unisono.clamp_bmod 64 (by norm_num) ⌊t * (10 ^ 9 : ℝ)⌋
  have hmin : min ⌊t * (10 ^ 9 : ℝ)⌋ (2 ^ 63 - 1 : ℤ) = min (2 ^ 63 - 1 : ℤ) ⌊t * (10 ^ 9 : ℝ)⌋ :=
    min_comm _ _
  rw [hmin]
  simpa using h

theorem toNs_of_int {z : ℤ} (hlo : -2 ^ 63 ≤ z) (hhi : z ≤ 2 ^ 63 - 1) :
    (toNs ((z : ℝ) / (10 ^ 9 : ℝ))).val = z := by
  rw [toNs_val]
  have hmul : (z : ℝ) / (10 ^ 9 : ℝ) * (10 ^ 9 : ℝ) = (z : ℝ) := by norm_num
  rw [hmul, Int.floor_intCast]
  omega

/-- Clamped conversion from `ℕ` to `Std.U16`. -/
def natToU16 (n : ℕ) : Std.U16 :=
  ⟨BitVec.ofNat 16 (min n 65535)⟩

/-- Clamped conversion from `ℕ` to `Std.U32`. -/
def natToU32 (n : ℕ) : Std.U32 :=
  ⟨BitVec.ofNat 32 (min n (2 ^ 32 - 1))⟩

theorem natToU32_val (n : ℕ) : (natToU32 n).val = min n (2 ^ 32 - 1) := by
  unfold natToU32
  change (BitVec.ofNat 32 (min n (2 ^ 32 - 1))).toNat = _
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- Clamped conversion from `ℕ` to `Std.I64`. -/
def natToI64 (n : ℕ) : Std.I64 :=
  ⟨BitVec.ofInt 64 (min (n : ℤ) (2 ^ 63 - 1))⟩

/-- Real frame position represented by `timing.Position` (`frame + fraction / 2^64`). -/
def posToReal (pos : timing.Position) : ℝ :=
  (pos.frame.val : ℝ) + (pos.fraction.val : ℝ) / (2 : ℝ) ^ 64

/-- Real frame step per output sample represented by `timing.Step` (`1 + offset / 2^64`). -/
def stepToReal (st : timing.Step) : ℝ :=
  1 + (st.offset.val : ℝ) / (2 : ℝ) ^ 64

/-- Exact `2^-64`-frame integer units of a `timing.Position`. -/
def posUnitsNat (pos : timing.Position) : ℕ :=
  pos.frame.val * 2 ^ 64 + pos.fraction.val

theorem posToReal_eq_units (pos : timing.Position) :
    posToReal pos = (posUnitsNat pos : ℝ) / (2 : ℝ) ^ 64 := by
  unfold posToReal posUnitsNat
  push_cast
  have h2 : ((2 : ℝ) ^ 64) ≠ 0 := by positivity
  field_simp
  norm_num

private theorem u64_cast_u128_val (x : Std.U64) : (UScalar.cast .U128 x).val = x.val := by
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
  have hx : x.val < 2 ^ 64 := by scalar_tac
  change x.val < 2 ^ 128
  exact lt_trans hx (by norm_num)

private theorem u32_cast_u128_val (x : Std.U32) : (UScalar.cast .U128 x).val = x.val := by
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
  have hx : x.val < 2 ^ 32 := by scalar_tac
  change x.val < 2 ^ 128
  exact lt_trans hx (by norm_num)

private theorem u128_wrapping_add_val (a b : Std.U128) (h : a.val + b.val < 2 ^ 128) :
    (core.num.U128.wrapping_add a b).val = a.val + b.val := by
  simp only [core.num.U128.wrapping_add_val_eq, UScalar.size]
  exact Nat.mod_eq_of_lt h

private theorem u128_wrapping_sub_val (a b : Std.U128) (h : b.val ≤ a.val) :
    (core.num.U128.wrapping_sub a b).val = a.val - b.val := by
  simp only [core.num.U128.wrapping_sub_val_eq, UScalar.size]
  have ha : a.val < 2 ^ 128 := by scalar_tac
  have hb : b.val < 2 ^ 128 := by scalar_tac
  change (a.val + (2 ^ 128 - b.val)) % 2 ^ 128 = a.val - b.val
  have hadd : a.val + (2 ^ 128 - b.val) = (a.val - b.val) + 1 * 2 ^ 128 := by omega
  rw [hadd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

private theorem position_units_val (pos : timing.Position) :
    timing.Position.units pos ⦃ u => u.val = posUnitsNat pos ⦄ := by
  unfold timing.Position.units
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hiv : i.val = pos.frame.val := by rw [hi]; exact u64_cast_u128_val pos.frame
  have hfr : pos.frame.val < 2 ^ 64 := by scalar_tac
  have hi1v : i1.val = pos.frame.val * 2 ^ 64 := by
    rw [hi1]
    simp only [UScalar.val, core.num.U128.wrapping_shl_bv_eq]
    change (i.bv <<< 64).toNat = pos.frame.val * 2 ^ 64
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have : i.bv.toNat = pos.frame.val := hiv
    rw [this]
    have hlt : pos.frame.val * 2 ^ 64 < 2 ^ 128 := by
      have : pos.frame.val ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt hfr
      calc pos.frame.val * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := Nat.mul_le_mul_right _ this
        _ < 2 ^ 128 := by norm_num
    exact Nat.mod_eq_of_lt hlt
  have hi2v : i2.val = pos.fraction.val := by rw [hi2]; exact u64_cast_u128_val pos.fraction
  have hfrac : pos.fraction.val < 2 ^ 64 := by scalar_tac
  have hlt_sum : i1.val + i2.val < 2 ^ 128 := by
    rw [hi1v, hi2v]
    have h1 : pos.frame.val ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt hfr
    have h2 : pos.fraction.val ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt hfrac
    calc pos.frame.val * 2 ^ 64 + pos.fraction.val
        ≤ (2 ^ 64 - 1) * 2 ^ 64 + (2 ^ 64 - 1) := Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2
      _ < 2 ^ 128 := by norm_num
  rw [u128_wrapping_add_val i1 i2 hlt_sum, hi1v, hi2v]
  rfl

private theorem position_from_units_val (u : Std.U128) :
    timing.Position.from_units u ⦃ pos => posUnitsNat pos = u.val ⦄ := by
  unfold timing.Position.from_units
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hu : u.val < 2 ^ 128 := by scalar_tac
  have hiv : i.val = u.val / 2 ^ 64 := by
    rw [hi]
    simp only [UScalar.val, core.num.U128.wrapping_shr_bv_eq]
    change (u.bv >>> 64).toNat = u.val / 2 ^ 64
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  have hi1v : i1.val = u.val / 2 ^ 64 := by
    rw [hi1, UScalar.cast_val_mod_pow_of_inBounds_eq]
    · exact hiv
    · rw [hiv]; change u.val / 2 ^ 64 < 2 ^ 64
      have hmul : (2 ^ 128 : ℕ) = 2 ^ 64 * 2 ^ 64 := by norm_num
      exact Nat.div_lt_of_lt_mul (hmul ▸ hu)
  have hi2v : i2.val = u.val % 2 ^ 64 := by
    rw [hi2, UScalar.cast_val_eq]
    rfl
  unfold posUnitsNat
  rw [hi1v, hi2v, Nat.mul_comm, Nat.div_add_mod]

private theorem step_units_val (st : timing.Step) :
    timing.Step.units st ⦃ u => (u.val : ℤ) = 2 ^ 64 + st.offset.val ⦄ := by
  unfold timing.Step.units
  have hoff : -2 ^ 63 ≤ st.offset.val ∧ st.offset.val < 2 ^ 63 := by scalar_tac
  have hframe : timing.FRAME.val = 2 ^ 64 := by unfold timing.FRAME; decide
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  have hiv : i.val = st.offset.val := by rw [hi]; exact I64.cast_I128_val st.offset
  have hi1v : i1.val = 2 ^ 64 + st.offset.val := by
    rw [hi1, I128.wrapping_add_val _ _ (by rw [hframe, hiv]; omega), hframe, hiv]
  rw [IScalar.hcast_val_eq]
  have hmod : i1.val % 2 ^ UScalarTy.U128.numBits = i1.val :=
    Int.emod_eq_of_lt (by omega) (by change i1.val < 2 ^ 128; omega)
  rw [hmod, Int.toNat_of_nonneg (by omega), hi1v]

/-- Exact real-number semantics of `timing.Position.advance`: whenever `advance`
does not overflow `U128` (`= ok (some next)`), `next` advances `start` by
exactly `frames * stepToReal st` with zero rounding error. -/
theorem posToReal_advance (start : timing.Position) (st : timing.Step) (frames : Std.U64)
    (next : timing.Position)
    (hadv : timing.Position.advance start st frames = ok (some next)) :
    posToReal next = posToReal start + (frames.val : ℝ) * stepToReal st := by
  have hspec : timing.Position.advance start st frames ⦃ o =>
      ∀ n, o = some n → posToReal n = posToReal start + (frames.val : ℝ) * stepToReal st ⦄ := by
    unfold timing.Position.advance
    step with step_units_val st as ⟨u_step, hu_step⟩
    step as ⟨u_fr, hu_fr⟩
    have hfrv : u_fr.val = frames.val := by rw [hu_fr]; exact u64_cast_u128_val frames
    step as ⟨o1, ho1⟩
    cases o1 with
    | none => simp
    | some dist =>
      dsimp only
      have hdist_val : dist.val = u_step.val * u_fr.val := ho1.2.1
      step with position_units_val start as ⟨u_start, hu_start⟩
      step as ⟨o2, ho2⟩
      cases o2 with
      | none => simp
      | some total =>
        dsimp only
        have htot_val : total.val = u_start.val + dist.val := ho2.2.1
        step with position_from_units_val total as ⟨p, hp⟩
        intro n hn
        injection hn with hn; subst hn
        rw [posToReal_eq_units p, posToReal_eq_units start, hp, htot_val, hu_start, hdist_val,
          hfrv]
        have hu_step_r : (u_step.val : ℝ) = (2 : ℝ) ^ 64 + (st.offset.val : ℝ) := by
          have h1 : ((u_step.val : ℤ) : ℝ) = ((2 ^ 64 + st.offset.val : ℤ) : ℝ) := by
            exact_mod_cast hu_step
          push_cast at h1
          linarith [h1]
        unfold stepToReal
        push_cast
        rw [hu_step_r]
        have h2 : ((2 : ℝ) ^ 64) ≠ 0 := by positivity
        field_simp
  have hret := evalResult_of_spec (d := none) hspec
  rw [hadv, evalResult_eq_of_ok] at hret
  exact hret next rfl

private theorem u128_shl64_val (x : Std.U128) (hx : x.val < 2 ^ 64) :
    (core.num.U128.wrapping_shl x 64#u32).val = x.val * 2 ^ 64 := by
  simp only [UScalar.val, core.num.U128.wrapping_shl_bv_eq]
  change (x.bv <<< 64).toNat = x.val * 2 ^ 64
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hlt : x.bv.toNat * 2 ^ 64 < 2 ^ 128 := by
    have hx' : x.bv.toNat ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt hx
    calc x.bv.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := Nat.mul_le_mul_right _ hx'
      _ < 2 ^ 128 := by norm_num
  exact Nat.mod_eq_of_lt hlt

/-- When a running `ModalPlayer` decides `jumps = true`, `now` lies strictly
further than `regulation.jump` frames away from `m.position`. -/
theorem posToReal_sub_of_jumps_true (m : player.ModalPlayer) (now : timing.Position)
    (hrun : m.running = true)
    (hjump : player.ModalPlayer.jumps m now = ok true) :
    (m.regulation.jump.val : ℝ) < |posToReal now - posToReal m.position| := by
  have hspec : player.ModalPlayer.jumps m now ⦃ b =>
      b = true → (m.regulation.jump.val : ℝ) < |posToReal now - posToReal m.position| ⦄ := by
    unfold player.ModalPlayer.jumps
    simp only [hrun, ↓reduceIte]
    step with position_units_val m.position as ⟨cur, hcur⟩
    step with position_units_val now as ⟨tgt, htgt⟩
    have hgap :
        (if tgt >= cur then ok (core.num.U128.wrapping_sub tgt cur)
         else ok (core.num.U128.wrapping_sub cur tgt))
        ⦃ g => (g.val : ℤ) = |(posUnitsNat now : ℤ) - (posUnitsNat m.position : ℤ)| ⦄ := by
      split
      · rename_i hge
        have hge' : cur.val ≤ tgt.val := hge
        have hge_z : (cur.val : ℤ) ≤ (tgt.val : ℤ) := by exact_mod_cast hge'
        rw [WP.spec_ok, u128_wrapping_sub_val tgt cur hge', Nat.cast_sub hge', ← hcur, ← htgt,
          abs_of_nonneg (sub_nonneg.mpr hge_z)]
      · rename_i hlt
        have hlt' : tgt.val < cur.val := Nat.lt_of_not_le hlt
        have hlt_z : (tgt.val : ℤ) < (cur.val : ℤ) := by exact_mod_cast hlt'
        rw [WP.spec_ok, u128_wrapping_sub_val cur tgt hlt'.le, Nat.cast_sub hlt'.le, ← hcur, ← htgt,
          abs_of_neg (sub_neg.mpr hlt_z)]
        ring
    apply WP.spec_bind hgap
    intro gap hgapv
    step as ⟨i, hi⟩
    step as ⟨lim, hlim⟩
    have hiv : i.val = m.regulation.jump.val := by rw [hi]; exact u32_cast_u128_val m.regulation.jump
    have hj_lt : i.val < 2 ^ 64 := by
      have : m.regulation.jump.val < 2 ^ 32 := m.regulation.jump.hBounds
      rw [hiv]; omega
    have hlimv : lim.val = m.regulation.jump.val * 2 ^ 64 := by
      rw [hlim, u128_shl64_val i hj_lt, hiv]
    intro hb
    have hgt_us : gap > lim := of_decide_eq_true hb
    have hgt : lim.val < gap.val := hgt_us
    have hgt_z : (m.regulation.jump.val : ℤ) * (2 : ℤ) ^ 64 <
        |(posUnitsNat now : ℤ) - (posUnitsNat m.position : ℤ)| := by
      have h1 : (lim.val : ℤ) < (gap.val : ℤ) := Int.ofNat_lt.mpr hgt
      rw [hlimv, hgapv] at h1
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h1
    have hgt_r : (m.regulation.jump.val : ℝ) * (2 : ℝ) ^ 64 <
        |(posUnitsNat now : ℝ) - (posUnitsNat m.position : ℝ)| := by
      have hcast : (((m.regulation.jump.val : ℤ) * (2 : ℤ) ^ 64 : ℤ) : ℝ) <
          ((|(posUnitsNat now : ℤ) - (posUnitsNat m.position : ℤ)| : ℤ) : ℝ) :=
        Int.cast_lt.mpr hgt_z
      simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat,
        Int.cast_abs, Int.cast_sub] using hcast
    have hpow : (0 : ℝ) < (2 : ℝ) ^ 64 := pow_pos (by norm_num) 64
    rw [posToReal_eq_units now, posToReal_eq_units m.position, ← sub_div, abs_div,
      abs_of_pos hpow]
    exact (lt_div_iff₀ hpow).mpr hgt_r
  have hret := evalResult_of_spec (d := false) hspec
  rw [hjump, evalResult_eq_of_ok] at hret
  exact hret rfl

/-! ## 2. Wire message type, parameters, and state of `Core.solution` -/

/-- Wire messages carried by `Core.solution`, mirroring `unisono_core::packet`. -/
inductive CoreMsg where
  | audio (header : packet.Audio)
  | report (r : packet.Report)
  | echo (e : packet.Echo)
  | peerProbe (p : packet.PeerProbe)
  | peerEcho (e : packet.PeerEcho)
  | peerRelay (r : packet.PeerRelay)

/-- Parameters of the production core solution. -/
structure Params (H : Type) where
  /-- The sender host. -/
  sender : H
  /-- Speaker hosts to which the sender transmits audio packets. -/
  speakers : List H
  /-- Per-host static peer allowlist: `(peerHost, peerIdentity, weightQ16)`. -/
  peers : H → List (H × Std.U64 × Std.U32)
  /-- Numeric host identity (`u64`). -/
  hostId : H → Std.U64
  /-- Stream identifier (`u16`). -/
  stream : Std.U16
  /-- Sender clock identity (`u32`). -/
  clockId : Std.U32
  /-- Timeline identifier (`u64`). -/
  timeline : Std.U64
  /-- Nominal sample rate in frames per second (`u32`). -/
  rate : Std.U32
  /-- Channel count (`u8`). -/
  channels : Std.U8
  /-- Window span / packet span settings for `sender.Settings`. -/
  span : Std.U32
  window : Std.U32
  /-- Initial sender latency level in nanoseconds. -/
  targetLatencyNs : Std.I64
  /-- Receiver silence restart timeout in nanoseconds. -/
  silenceNs : Std.I64
  /-- Receiver legacy estimator slope limit (ppb). -/
  estLimit : Std.I64
  /-- Modal playback regulation (`star_gain`, `common_gain`, `diff_gain`, `limit`, `jump`). -/
  regulation : player.ModalRegulation
  /-- Minimum interval between sender clock reports from a receiving host (ns). -/
  reportPeriodNs : Std.I64
  /-- Per-host `sync.SyncSettings`. -/
  syncSettings : H → sync.SyncSettings

/-- Construct `sender.Settings` from `Params`. -/
def Params.senderSettings {H : Type} (p : Params H) : sender.Settings where
  stream := p.stream
  rate := p.rate
  channels := p.channels
  format := packet.Format.Signed24
  span := p.span
  window := p.window
  clock := p.clockId

/-- Construct `receiver.Settings` from `Params` for host `h`. -/
def Params.receiverSettings {H : Type} (p : Params H) (h : H) : receiver.Settings where
  stream := p.stream
  identity := p.hostId h
  silence := p.silenceNs
  limit := p.estLimit
  regulation := { gain := p.regulation.star_gain, limit := p.regulation.limit, jump := p.regulation.jump }

/-- Initial `sender.Sender` produced by `unisono_core::sender::Sender::new`. -/
def initSender {H : Type} (p : Params H) : sender.Sender :=
  evalResult (sender.Sender.new p.senderSettings p.timeline p.targetLatencyNs)
    { settings := p.senderSettings
      timeline := p.timeline
      next := 0#u64
      level_index := 0#u64
      level_base := p.targetLatencyNs
      level_slope := 0#i32
      stamped := false
      stamped_index := 0#u64
      stamped_departure := 0#i64 }

/-- Register a list of peers into `sync.Sync` via `sync.Sync.add_peer`. -/
def registerPeers {H : Type} (s : sync.Sync) : List (H × Std.U64 × Std.U32) → sync.Sync
  | [] => s
  | (_, id, w) :: rest =>
      let (_, s') := evalResult (sync.Sync.add_peer s id w) (none, s)
      registerPeers s' rest

/-- Initial `sync.Sync` for host `h`, created by `sync.Sync.new` and populated
with `p.peers h` via `sync.Sync.add_peer`. -/
def initSync {H : Type} (p : Params H) (h : H) : sync.Sync :=
  let base := Classical.choose (exists_ok_of_spec (Unisono.Sync.new_total (p.syncSettings h)))
  registerPeers base (p.peers h)

/-- Initial `receiver.Receiver N M K` for host `h`, created by `Receiver.new`
with `enable_sync` active for `p.regulation`. -/
def initReceiver {H : Type} (p : Params H) (N M K : Std.Usize) (h : H) :
    receiver.Receiver N M K :=
  let r0 : receiver.Receiver N M K :=
    Classical.choose (exists_ok_of_spec (Unisono.Receiver.new_spec N M K (p.receiverSettings h)))
  evalResult (receiver.Receiver.enable_sync r0 p.regulation) r0

/-- Look up the peer host corresponding to `Sync` peer table index `idx`. -/
def peerHostOf {H : Type} (p : Params H) (h : H) (idx : Std.Usize) : Option H :=
  ((p.peers h)[idx.val]?).map Prod.fst

theorem peerHostOf_mem {H : Type} (p : Params H) (h : H) (idx : Std.Usize) {dst : H}
    (hd : peerHostOf p h idx = some dst) :
    dst ∈ (p.peers h).map Prod.fst := by
  unfold peerHostOf at hd
  cases hget : (p.peers h)[idx.val]? with
  | none => simp [hget] at hd
  | some entry =>
    simp only [hget, Option.map_some, Option.some.injEq] at hd
    rw [← hd]
    exact List.mem_map.mpr ⟨entry, List.mem_of_getElem? hget, rfl⟩

/-- Per-host state maintained across events by `Core.solution`. -/
structure Memory (H : Type) (R : ℕ) (N M K : Std.Usize) where
  snd : sender.Sender
  syn : sync.Sync
  rcv : Fin R → receiver.Receiver N M K
  lastReport : Option Std.I64
  reportSeq : Std.U64

/-- Initial host memory before any event. -/
def Memory.init {H : Type} {R : ℕ} (p : Params H) (N M K : Std.Usize) (h : H) :
    Memory H R N M K where
  snd := initSender p
  syn := initSync p h
  rcv := fun _ => initReceiver p N M K h
  lastReport := none
  reportSeq := 0#u64

/-- Whether a receiving host sends a sender clock report at clock reading `nowNs`. -/
def shouldSendReport (lastReport : Option Std.I64) (nowNs periodNs : Std.I64) : Bool :=
  match lastReport with
  | none => true
  | some prev => decide (periodNs.val ≤ (core.num.I64.saturating_sub nowNs prev).val)

/-- Block duration in nanoseconds for `count` samples at rate `rate` Hz. -/
def blockDurationNs (count : ℕ) (rate : Std.U32) : Std.I64 :=
  if rate.val = 0 then 0#i64
  else natToI64 (count * 10 ^ 9 / rate.val)

/-- Convert a `player.Plan` for block `outputs` into per-sample positions in `ℝ`. -/
def planPlays (outputs : List ℕ) (plan : player.Plan) : ℕ → Option ℝ :=
  if plan.frames.val = 0 then fun _ => none
  else
    match outputs.head? with
    | none => fun _ => none
    | some first => fun k =>
        if first ≤ k ∧ k < first + min outputs.length plan.frames.val then
          some (posToReal plan.start + ((k - first : ℕ) : ℝ) * stepToReal plan.step)
        else none

/-- Outgoing sender-report step during an `.asked` event on a non-sender host. -/
def askedReport {H : Type} (p : Params H) (h : H) (syn : sync.Sync)
    (lastRep : Option Std.I64) (seq : Std.U64) (nowNs : Std.I64) :
    List (H × CoreMsg × Finset ℕ) × sync.Sync × Option Std.I64 × Std.U64 :=
  if shouldSendReport lastRep nowNs p.reportPeriodNs then
    let rep : packet.Report :=
      { stream := p.stream, timeline := p.timeline, receiver := p.hostId h, sequence := seq }
    let s' := evalResult (sync.Sync.report_departed syn seq nowNs) syn
    ([(p.sender, CoreMsg.report rep, ∅)], s', some nowNs, core.num.U64.wrapping_add seq 1#u64)
  else ([], syn, lastRep, seq)

/-- Outgoing peer-probe step during an `.asked` event on a non-sender host. -/
def askedProbe {H : Type} (p : Params H) (h : H) (syn : sync.Sync) (nowNs : Std.I64) :
    List (H × CoreMsg × Finset ℕ) × sync.Sync :=
  let (op, s') := evalResult (sync.Sync.next_peer_probe syn nowNs) (none, syn)
  match op with
  | some (pidx, probe) =>
      match peerHostOf p h pidx with
      | some dst =>
          let s'' := evalResult (sync.Sync.peer_probe_departed s' pidx probe.sequence nowNs) s'
          ([(dst, CoreMsg.peerProbe probe, ∅)], s'')
      | none => ([], s')
  | none => ([], s')

/-- Outgoing peer-relay step during an `.asked` event on a non-sender host. -/
def askedRelay {H : Type} (p : Params H) (h : H) (syn : sync.Sync) (nowNs : Std.I64) :
    List (H × CoreMsg × Finset ℕ) × sync.Sync :=
  if evalResult (sync.Sync.should_relay syn nowNs) false then
    let (or_, s') := evalResult (sync.Sync.build_relay syn nowNs) (none, syn)
    match or_ with
    | some rel =>
        (((p.peers h).map Prod.fst).map fun dst => (dst, CoreMsg.peerRelay rel, ∅), s')
    | none => ([], s')
  else ([], syn)

/-- Default empty `player.Plan`. -/
def emptyPlan : player.Plan where
  frames := 0#u32
  start := { frame := 0#u64, fraction := 0#u64 }
  step := timing.Step.UNITY
  jumped := false

/-- One host step processing event `e` from memory `m`, calling the translated
`UnisonoCore` functions directly. -/
def stepHost {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (m : Memory H R N M K) (e : Event H R CoreMsg) :
    Memory H R N M K × Action H CoreMsg :=
  let nowNs := toNs e.reading
  match e.observation with
  | .handed frames reported =>
      if h = p.sender then
        match frames with
        | [] => (m, ⟨[], [], fun _ => none⟩)
        | _ :: _ =>
            let (hdr, snd1) :=
              evalResult (sender.Sender.packet m.snd (natToU16 frames.length) (toNs reported) 0#i32)
                ({ stream := p.stream, timeline := p.timeline, index := m.snd.next,
                   capture := toNs reported, drift := 0#i32, rate := p.rate,
                   frames := natToU16 frames.length, channels := p.channels,
                   format := packet.Format.Signed24, level := p.targetLatencyNs,
                   level_slope := 0#i32, span := p.span, window := p.window,
                   flags := 0#u16, protection := 0#u16, stamped_index := 0#u64,
                   stamped_departure := 0#i64, clock := p.clockId }, m.snd)
            let snd2 := evalResult (sender.Sender.departed snd1 hdr.timeline hdr.index nowNs) snd1
            let frameSet := (frames.map Prod.fst).toFinset
            let sends := (p.speakers.filter (· ≠ p.sender)).map fun dst =>
              (dst, CoreMsg.audio hdr, frameSet)
            ({ m with snd := snd2 }, ⟨sends, [], fun _ => none⟩)
      else (m, ⟨[], [], fun _ => none⟩)
  | .received _ (.audio hdr) _ =>
      if h = p.sender then (m, ⟨[], [], fun _ => none⟩)
      else
        let rcv' := fun r =>
          (evalResult (receiver.Receiver.packet (m.rcv r) hdr nowNs)
            ({ ignored := false, adopted := false, restarted := false,
               marked := { stored := 0#u32, duplicate := 0#u32, late := 0#u32, early := 0#u32 } },
             m.rcv r)).2
        ({ m with rcv := rcv' }, ⟨[], [], fun _ => none⟩)
  | .received i (.report rep) _ =>
      if h = p.sender ∧ rep.stream = p.stream then
        let ec : packet.Echo :=
          { stream := rep.stream
            receiver := rep.receiver
            sequence := rep.sequence
            arrival := nowNs
            departure := nowNs }
        (m, ⟨[(i, CoreMsg.echo ec, ∅)], [], fun _ => none⟩)
      else (m, ⟨[], [], fun _ => none⟩)
  | .received _ (.echo ec) _ =>
      if h = p.sender then (m, ⟨[], [], fun _ => none⟩)
      else
        let syn1 := (evalResult (sync.Sync.on_sender_echo m.syn ec nowNs) (false, m.syn)).2
        let (snap, syn2) := evalResult (sync.Sync.step syn1 nowNs) (sync.SyncSnapshot.EMPTY, syn1)
        let rcv' := fun r => evalResult (receiver.Receiver.apply_sync (m.rcv r) snap) (m.rcv r)
        ({ m with syn := syn2, rcv := rcv' }, ⟨[], [], fun _ => none⟩)
  | .received i (.peerProbe probe) _ =>
      if h = p.sender then (m, ⟨[], [], fun _ => none⟩)
      else
        match evalResult (sync.Sync.on_peer_probe m.syn probe nowNs nowNs) none with
        | some pe =>
            if i ∈ (p.peers h).map Prod.fst then
              (m, ⟨[(i, CoreMsg.peerEcho pe, ∅)], [], fun _ => none⟩)
            else (m, ⟨[], [], fun _ => none⟩)
        | none => (m, ⟨[], [], fun _ => none⟩)
  | .received _ (.peerEcho pe) _ =>
      if h = p.sender then (m, ⟨[], [], fun _ => none⟩)
      else
        let syn1 := (evalResult (sync.Sync.on_peer_echo m.syn pe nowNs) (false, m.syn)).2
        let (snap, syn2) := evalResult (sync.Sync.step syn1 nowNs) (sync.SyncSnapshot.EMPTY, syn1)
        let rcv' := fun r => evalResult (receiver.Receiver.apply_sync (m.rcv r) snap) (m.rcv r)
        ({ m with syn := syn2, rcv := rcv' }, ⟨[], [], fun _ => none⟩)
  | .received _ (.peerRelay rel) _ =>
      if h = p.sender then (m, ⟨[], [], fun _ => none⟩)
      else
        let syn1 := (evalResult (sync.Sync.on_peer_relay m.syn rel nowNs) (0#usize, m.syn)).2
        let (snap, syn2) := evalResult (sync.Sync.step syn1 nowNs) (sync.SyncSnapshot.EMPTY, syn1)
        let rcv' := fun r => evalResult (receiver.Receiver.apply_sync (m.rcv r) snap) (m.rcv r)
        ({ m with syn := syn2, rcv := rcv' }, ⟨[], [], fun _ => none⟩)
  | .asked r outputs reported =>
      let (snap, syn1) := evalResult (sync.Sync.step m.syn nowNs) (sync.SyncSnapshot.EMPTY, m.syn)
      let r1 := evalResult (receiver.Receiver.apply_sync (m.rcv r) snap) (m.rcv r)
      let dur := blockDurationNs outputs.length p.rate
      let (plan, r2) := evalResult
        (receiver.Receiver.cycle r1 (toNs reported) dur (natToU32 outputs.length))
        (emptyPlan, r1)
      let rcv' := Function.update m.rcv r r2
      if h = p.sender then
        ({ m with syn := syn1, rcv := rcv' }, ⟨[], [], planPlays outputs plan⟩)
      else
        let repRes := askedReport p h syn1 m.lastReport m.reportSeq nowNs
        let probeRes := askedProbe p h repRes.2.1 nowNs
        let relayRes := askedRelay p h probeRes.2 nowNs
        ({ m with syn := relayRes.2, rcv := rcv',
                  lastReport := repRes.2.2.1, reportSeq := repRes.2.2.2 },
         ⟨repRes.1 ++ probeRes.1 ++ relayRes.1, [], planPlays outputs plan⟩)
  | .timer => (m, ⟨[], [], fun _ => none⟩)

/-- Memory transition of `Core.solution` on one event. -/
def remember {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (m : Memory H R N M K) (e : Event H R CoreMsg) : Memory H R N M K :=
  (stepHost p N M K h m e).1

/-- Action emitted by `Core.solution` on one event from memory `m`. -/
def act {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (m : Memory H R N M K) (e : Event H R CoreMsg) : Action H CoreMsg :=
  (stepHost p N M K h m e).2

/-- Memory reconstructed from a host's view. -/
def memoryOf {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (view : List (Event H R CoreMsg)) : Memory H R N M K :=
  view.foldl (remember p N M K h) (Memory.init p N M K h)

/-- **The production core wrapped directly as a `Unisono.Spec.Solution`.** -/
def solution {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize) :
    Solution H R CoreMsg := fun h view =>
  match view.getLast? with
  | some e => act p N M K h (memoryOf p N M K h view.dropLast) e
  | none => ⟨[], [], fun _ => none⟩

theorem solution_append {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (view : List (Event H R CoreMsg)) (e : Event H R CoreMsg) :
    solution p N M K h (view ++ [e]) = act p N M K h (memoryOf p N M K h view) e := by
  simp [solution]

theorem memoryOf_append {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (view : List (Event H R CoreMsg)) (e : Event H R CoreMsg) :
    memoryOf p N M K h (view ++ [e]) = remember p N M K h (memoryOf p N M K h view) e := by
  simp [memoryOf]

/-! ## 3. Topology membership (`UsesGraph`, `IsStar`) -/

private theorem mem_askedReport {H : Type} (p : Params H) (h : H) (syn : sync.Sync)
    (lastRep : Option Std.I64) (seq' : Std.U64) (nowNs : Std.I64)
    {dst : H} {msg : CoreMsg} {frames : Finset ℕ}
    (hmem : (dst, msg, frames) ∈ (askedReport p h syn lastRep seq' nowNs).1) :
    dst = p.sender ∧ ∃ rep, msg = .report rep := by
  unfold askedReport at hmem
  dsimp only at hmem
  split_ifs at hmem
  · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    exact ⟨hmem.1, _, hmem.2.1⟩
  · simp at hmem

private theorem mem_askedProbe {H : Type} (p : Params H) (h : H) (syn : sync.Sync) (nowNs : Std.I64)
    {dst : H} {msg : CoreMsg} {frames : Finset ℕ}
    (hmem : (dst, msg, frames) ∈ (askedProbe p h syn nowNs).1) :
    dst ∈ (p.peers h).map Prod.fst := by
  unfold askedProbe at hmem
  dsimp only at hmem
  cases h1 : (evalResult (sync.Sync.next_peer_probe syn nowNs) (none, syn)).1 with
  | none => simp [h1] at hmem
  | some pair =>
    simp only [h1] at hmem
    cases hph : peerHostOf p h pair.1 with
    | none => simp [hph] at hmem
    | some dst' =>
      simp only [hph, List.mem_singleton, Prod.mk.injEq] at hmem
      exact hmem.1 ▸ peerHostOf_mem p h pair.1 hph

private theorem mem_askedRelay {H : Type} (p : Params H) (h : H) (syn : sync.Sync) (nowNs : Std.I64)
    {dst : H} {msg : CoreMsg} {frames : Finset ℕ}
    (hmem : (dst, msg, frames) ∈ (askedRelay p h syn nowNs).1) :
    dst ∈ (p.peers h).map Prod.fst := by
  unfold askedRelay at hmem
  dsimp only at hmem
  split_ifs at hmem
  · cases h1 : (evalResult (sync.Sync.build_relay syn nowNs) (none, syn)).1 with
    | none => simp [h1] at hmem
    | some rel =>
      simp only [h1] at hmem
      rw [List.mem_map] at hmem
      obtain ⟨dst', hdst', hEq⟩ := hmem
      injection hEq with hEq _
      exact hEq ▸ hdst'
  · simp at hmem

/-- Every message sent by `Core.solution` travels either on a star link incident
to `p.sender` or to a host explicitly listed in `p.peers h`. -/
theorem usesGraph_of_peers {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize) :
    (solution p N M K : Solution H R CoreMsg).UsesGraph
      (fun h dst => h = p.sender ∨ dst = p.sender ∨ dst ∈ (p.peers h).map Prod.fst) := by
  intro h view dst msg frames hmem
  unfold solution at hmem
  cases hlast : view.getLast? with
  | none => simp [hlast] at hmem
  | some e =>
    simp only [hlast] at hmem
    unfold act stepHost at hmem
    dsimp only at hmem
    cases hobs : e.observation with
    | handed fs rep =>
      simp only [hobs] at hmem
      split_ifs at hmem with hs
      · cases fs with
        | nil => simp at hmem
        | cons _ _ => exact Or.inl hs
      · simp at hmem
    | received origin contents fs =>
      simp only [hobs] at hmem
      cases contents with
      | audio hdr => split_ifs at hmem <;> simp at hmem
      | report rep =>
        by_cases hs : h = p.sender
        · exact Or.inl hs
        · simp [hs] at hmem
      | echo ec => split_ifs at hmem <;> simp at hmem
      | peerProbe pr =>
        split_ifs at hmem with hs
        · simp at hmem
        · cases hres : evalResult (sync.Sync.on_peer_probe (memoryOf p N M K h view.dropLast).syn pr
              (toNs e.reading) (toNs e.reading)) none with
          | none => simp [hres] at hmem
          | some pe =>
            simp only [hres] at hmem
            split_ifs at hmem with hin
            · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
              exact Or.inr (Or.inr (hmem.1 ▸ hin))
            · simp at hmem
      | peerEcho pe => split_ifs at hmem <;> simp at hmem
      | peerRelay rel => split_ifs at hmem <;> simp at hmem
    | asked r outs rep =>
      simp only [hobs] at hmem
      split_ifs at hmem with hs
      · simp at hmem
      · simp only [List.mem_append] at hmem
        rcases hmem with (hrep | hpr) | hrel
        · exact Or.inr (Or.inl (mem_askedReport p h _ _ _ (toNs e.reading) hrep).1)
        · exact Or.inr (Or.inr (mem_askedProbe p h _ _ hpr))
        · exact Or.inr (Or.inr (mem_askedRelay p h _ _ hrel))
    | timer => simp [hobs] at hmem

/-- **Star topology theorem:** when every host has an empty peer list,
`Core.solution` is a star solution (`Solution.IsStar p.sender`). -/
theorem isStar_of_no_peers {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (hno : ∀ h, p.peers h = []) :
    (solution p N M K : Solution H R CoreMsg).IsStar p.sender := by
  intro h view dst msg frames hmem
  have h := usesGraph_of_peers p N M K h view dst msg frames hmem
  rcases h with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2
  · simp [hno h] at h3

/-! ## 4. Non-Zeno progress & request liveness under `World.WithinBounds` -/

/-- Message weight for non-Zeno progress: reports and peer probes have weight 2
(each triggers at most one weight-1 echo); all other messages have weight 1
(triggering no replies). -/
def msgWeight : CoreMsg → ℕ
  | .audio _ => 1
  | .report _ => 2
  | .echo _ => 1
  | .peerProbe _ => 2
  | .peerEcho _ => 1
  | .peerRelay _ => 1

private theorem sum_map_weight_const {H : Type} (l : List H) (m : CoreMsg) (F : Finset ℕ) :
    ((l.map fun dst => (dst, m, F)).map fun s => msgWeight s.2.1).sum =
      msgWeight m * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    ring

private theorem weight_askedReport {H : Type} (p : Params H) (h : H) (syn : sync.Sync)
    (lastRep : Option Std.I64) (seq : Std.U64) (nowNs : Std.I64) :
    ((askedReport p h syn lastRep seq nowNs).1.map fun s => msgWeight s.2.1).sum ≤ 2 := by
  unfold askedReport; dsimp only
  split_ifs <;> simp [msgWeight]

private theorem weight_askedProbe {H : Type} (p : Params H) (h : H) (syn : sync.Sync)
    (nowNs : Std.I64) :
    ((askedProbe p h syn nowNs).1.map fun s => msgWeight s.2.1).sum ≤ 2 := by
  unfold askedProbe; dsimp only
  cases (evalResult (sync.Sync.next_peer_probe syn nowNs) (none, syn)).1 with
  | none => simp
  | some pair => cases hph : peerHostOf p h pair.1 <;> simp [hph, msgWeight]

private theorem weight_askedRelay {H : Type} (p : Params H) (h : H) (syn : sync.Sync)
    (nowNs : Std.I64) :
    ((askedRelay p h syn nowNs).1.map fun s => msgWeight s.2.1).sum ≤ (p.peers h).length := by
  unfold askedRelay; dsimp only
  split_ifs
  · cases (evalResult (sync.Sync.build_relay syn nowNs) (none, syn)).1 with
    | none => simp
    | some rel =>
      rw [sum_map_weight_const ((p.peers h).map Prod.fst) (CoreMsg.peerRelay rel) ∅]
      simp [msgWeight]
  · simp

private theorem core_no_timers {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (view : List (Event H R CoreMsg)) :
    (solution p N M K h view).timers = [] := by
  unfold solution
  cases view.getLast? with
  | none => rfl
  | some e =>
    unfold act stepHost
    dsimp only
    cases e.observation with
    | handed fs rep =>
      dsimp only; split_ifs
      · cases fs <;> rfl
      · rfl
    | received i c fs =>
      cases c with
      | audio _ => dsimp only; split_ifs <;> rfl
      | report _ => dsimp only; split_ifs <;> rfl
      | echo _ => dsimp only; split_ifs <;> rfl
      | peerProbe _ =>
        dsimp only
        by_cases hs : h = p.sender
        · simp [hs]
        · simp only [hs, ↓reduceIte]
          cases evalResult _ none with
          | none => rfl
          | some _ => dsimp only; split_ifs <;> rfl
      | peerEcho _ => dsimp only; split_ifs <;> rfl
      | peerRelay _ => dsimp only; split_ifs <;> rfl
    | asked r outs rep =>
      dsimp only; split_ifs <;> rfl
    | timer => rfl

/-- **Non-Zeno progress of `Core.solution` under `World.WithinBounds`:**
the run advances past every true time `T`. -/
theorem progress {H : Type} {R : ℕ} [DecidableEq H] [Fintype H]
    (p : Params H) (N M K : Std.Usize)
    (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+) (T : Time) :
    ∃ n, T < (solution p N M K : Solution H R CoreMsg).eventTime w lookahead n := by
  obtain ⟨-, hsrc, hspk, -, -, -, hlead, -, -, -, -⟩ := hw
  let maxPeers : ℕ := Finset.univ.sup fun h : H => (p.peers h).length
  refine Solution.progress w (solution p N M K) lookahead msgWeight
    ((p.speakers.filter (· ≠ p.sender)).length + 1) (4 + maxPeers + 1)
    (core_no_timers p N M K) ?_ ?_ ?_
    (CaptureDevice.handed_unbounded w.rate_pos hsrc B.deviceRate_lt_one)
    (fun r => PlaybackDevice.asked_unbounded w.rate_pos (hspk r) B.deviceRate_lt_one (hlead r)) T
  · intro h view frames rep reading
    rw [solution_append]
    unfold act stepHost
    dsimp only
    split_ifs
    · cases frames with
      | nil => simp
      | cons a tl =>
        dsimp only
        rw [sum_map_weight_const (p.speakers.filter (· ≠ p.sender)) _ _]
        simp [msgWeight]
    · simp
  · intro h view r outs rep reading
    rw [solution_append]
    unfold act stepHost
    dsimp only
    split_ifs
    · simp
    · simp only [List.map_append, List.sum_append]
      have hle : (p.peers h).length ≤ maxPeers :=
        Finset.le_sup (f := fun h : H => (p.peers h).length) (Finset.mem_univ h)
      refine Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add
        (Nat.add_le_add (weight_askedReport p h _ _ _ _) (weight_askedProbe p h _ _))
        (weight_askedRelay p h _ _)) 1) ?_
      omega
  · intro h view i c F reading
    rw [solution_append]
    unfold act stepHost
    dsimp only
    cases c with
    | audio hdr => dsimp only; split_ifs <;> simp [msgWeight]
    | report rep => dsimp only; split_ifs <;> simp [msgWeight]
    | echo ec => dsimp only; split_ifs <;> simp [msgWeight]
    | peerProbe pr =>
      dsimp only
      by_cases hs : h = p.sender
      · simp [hs, msgWeight]
      · simp only [hs, ↓reduceIte]
        cases evalResult _ none with
        | none => simp [msgWeight]
        | some pe => dsimp only; split_ifs <;> simp [msgWeight]
    | peerEcho pe => dsimp only; split_ifs <;> simp [msgWeight]
    | peerRelay rel => dsimp only; split_ifs <;> simp [msgWeight]

/-- **Request liveness of `Core.solution` under `World.WithinBounds`:**
every playback request `(r, b)` of every speaker is handled at some step. -/
theorem request_step {H : Type} {R : ℕ} [DecidableEq H] [Fintype H]
    (p : Params H) (N M K : Std.Usize)
    (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (r : Fin R) (b : ℕ) :
    ∃ n, ((solution p N M K : Solution H R CoreMsg).states w lookahead n).askedNext r = b ∧
      earliest (((solution p N M K : Solution H R CoreMsg).states w lookahead n).key w)
        ((solution p N M K : Solution H R CoreMsg).states w lookahead n).due = some (.asked r b) := by
  obtain ⟨m, hm⟩ := progress p N M K w B hw lookahead ((w.speaker r).asked b)
  obtain ⟨n, -, h1, h2⟩ := Solution.exists_asked_step w (solution p N M K) lookahead
    (Solution.lt_askedNext (solution p N M K) w lookahead hm)
  exact ⟨n, h1, h2⟩

/-! ## 5. Exact Star degeneration directly on `Core.solution` -/

/-- `Sync.new` initializes `peer_count = 0`. -/
private theorem sync_new_peer_count (ss : sync.SyncSettings) :
    sync.Sync.new ss ⦃ s => s.peer_count = 0#usize ⦄ := by
  unfold sync.Sync.new
  step as ⟨sf⟩
  step as ⟨mr⟩
  step as ⟨dep⟩
  step as ⟨ps⟩
  step as ⟨arr1⟩
  step as ⟨arr2⟩
  step as ⟨kf1⟩

/-- `Sync.note_started` preserves `peer_count`. -/
private theorem note_started_peer_count (s : sync.Sync) (t : Std.I64) :
    sync.Sync.note_started s t ⦃ s' => s'.peer_count = s.peer_count ⦄ := by
  unfold sync.Sync.note_started
  split <;> simp

/-- `Sync.report_departed` preserves `peer_count`. -/
private theorem report_departed_peer_count (s : sync.Sync) (seq : Std.U64) (t : Std.I64) :
    sync.Sync.report_departed s seq t ⦃ s' => s'.peer_count = s.peer_count ⦄ := by
  unfold sync.Sync.report_departed
  step*

/-- `Sync.on_sender_echo` preserves `peer_count`. -/
private theorem on_sender_echo_peer_count (s : sync.Sync) (ec : packet.Echo) (t : Std.I64) :
    sync.Sync.on_sender_echo s ec t ⦃ out => out.2.peer_count = s.peer_count ⦄ := by
  unfold sync.Sync.on_sender_echo
  split
  · simp
  · split
    · simp
    · step with note_started_peer_count s t as ⟨s1, hs1⟩
      step as ⟨o⟩
      cases o with
      | none => simp [hs1]
      | some t1 =>
        dsimp only
        step as ⟨o2, mr⟩
        cases o2 with
        | none => simp [hs1]
        | some samp =>
          dsimp only
          step as ⟨_, kf⟩
          exact hs1

/-- `Sync.on_peer_echo` preserves `peer_count = 0`. -/
private theorem on_peer_echo_zero_peers (s : sync.Sync) (pe : packet.PeerEcho) (t : Std.I64)
    (h0 : s.peer_count = 0#usize) :
    sync.Sync.on_peer_echo s pe t ⦃ out => out.2.peer_count = 0#usize ⦄ := by
  unfold sync.Sync.on_peer_echo
  split
  · rw [WP.spec_ok]; exact h0
  · split
    · rw [WP.spec_ok]; exact h0
    · step with note_started_peer_count s t as ⟨s1, hs1⟩
      have h1 : s1.peer_count = 0#usize := hs1.trans h0
      step with Unisono.Sync.find_peer_zero_peers s1 pe.responder h1 as ⟨o, ho⟩
      rw [ho, WP.spec_ok]; exact h1

/-- `Sync.on_peer_relay` preserves `peer_count = 0`. -/
private theorem on_peer_relay_zero_peers (s : sync.Sync) (rel : packet.PeerRelay) (t : Std.I64)
    (h0 : s.peer_count = 0#usize) :
    sync.Sync.on_peer_relay s rel t ⦃ out => out.2.peer_count = 0#usize ⦄ := by
  unfold sync.Sync.on_peer_relay
  split
  · rw [WP.spec_ok]; exact h0
  · step with Unisono.Sync.find_peer_zero_peers s rel.sender h0 as ⟨o, ho⟩
    rw [ho, WP.spec_ok]; exact h0

private theorem peer_count_askedReport {H : Type} (p : Params H) (h : H) (syn : sync.Sync)
    (lastRep : Option Std.I64) (seq : Std.U64) (nowNs : Std.I64) (h0 : syn.peer_count = 0#usize) :
    (askedReport p h syn lastRep seq nowNs).2.1.peer_count = 0#usize := by
  unfold askedReport; dsimp only
  split_ifs
  · have := evalResult_of_spec (d := syn) (report_departed_peer_count syn seq nowNs)
    rw [this, h0]
  · exact h0

private theorem peer_count_askedProbe {H : Type} (p : Params H) (h : H) (syn : sync.Sync)
    (nowNs : Std.I64) (h0 : syn.peer_count = 0#usize) :
    (askedProbe p h syn nowNs).2.peer_count = 0#usize := by
  unfold askedProbe; dsimp only
  have hnp : sync.Sync.next_peer_probe syn nowNs = ok (none, syn) := by
    unfold sync.Sync.next_peer_probe; simp [h0]
  rw [hnp, evalResult_eq_of_ok]
  exact h0

private theorem peer_count_askedRelay {H : Type} (p : Params H) (h : H) (syn : sync.Sync)
    (nowNs : Std.I64) (h0 : syn.peer_count = 0#usize) :
    (askedRelay p h syn nowNs).2.peer_count = 0#usize := by
  unfold askedRelay; dsimp only
  have hsr : sync.Sync.should_relay syn nowNs = ok false := by
    unfold sync.Sync.should_relay; simp [h0]
  rw [hsr, evalResult_eq_of_ok]
  simp [h0]

/-- When `p.peers h = []`, `initSync p h` has `peer_count = 0#usize`. -/
theorem initSync_zero_peers {H : Type} (p : Params H) (h : H) (hno : p.peers h = []) :
    (initSync p h).peer_count = 0#usize := by
  unfold initSync
  rw [hno]
  dsimp only [registerPeers]
  have hspec := Classical.choose_spec (exists_ok_of_spec (Unisono.Sync.new_total (p.syncSettings h)))
  have hpc := sync_new_peer_count (p.syncSettings h)
  rw [hspec.1, WP.spec_ok] at hpc
  exact hpc

/-- When `p.peers h = []`, `Sync.peer_count` remains `0#usize` across every
event in host `h`'s view. -/
theorem sync_zero_peers_inv {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (hno : p.peers h = []) (view : List (Event H R CoreMsg)) :
    (memoryOf p N M K h view).syn.peer_count = 0#usize := by
  induction view using List.reverseRecOn with
  | nil => exact initSync_zero_peers p h hno
  | append_singleton view e ih =>
    rw [memoryOf_append]
    unfold remember stepHost
    dsimp only
    cases hobs : e.observation with
    | handed fs rep =>
      dsimp only; split_ifs
      · cases fs <;> exact ih
      · exact ih
    | received i c fs =>
      cases c with
      | audio hdr => dsimp only; split_ifs <;> exact ih
      | report rep => dsimp only; split_ifs <;> exact ih
      | echo ec =>
        dsimp only; split_ifs
        · exact ih
        · have h1 : (evalResult (sync.Sync.on_sender_echo (memoryOf p N M K h view).syn ec
              (toNs e.reading)) (false, (memoryOf p N M K h view).syn)).2.peer_count = 0#usize := by
            have := evalResult_of_spec (d := (false, (memoryOf p N M K h view).syn))
              (on_sender_echo_peer_count (memoryOf p N M K h view).syn ec (toNs e.reading))
            rw [this, ih]
          have h2 := evalResult_of_spec
            (d := (sync.SyncSnapshot.EMPTY, (evalResult (sync.Sync.on_sender_echo
              (memoryOf p N M K h view).syn ec (toNs e.reading)) (false, (memoryOf p N M K h view).syn)).2))
            (Unisono.Sync.step_zero_peers_star _ (toNs e.reading) h1)
          exact h2.2.2.2.2.1
      | peerProbe pr =>
        dsimp only
        split
        · exact ih
        · cases evalResult _ none with
          | none => exact ih
          | some _ => dsimp only; split <;> exact ih
      | peerEcho pe =>
        dsimp only; split_ifs
        · exact ih
        · have h1c : (evalResult (sync.Sync.on_peer_echo (memoryOf p N M K h view).syn pe
              (toNs e.reading)) (false, (memoryOf p N M K h view).syn)).2.peer_count = 0#usize :=
            evalResult_of_spec (on_peer_echo_zero_peers _ pe (toNs e.reading) ih)
          have h2 := evalResult_of_spec
            (d := (sync.SyncSnapshot.EMPTY, (evalResult (sync.Sync.on_peer_echo
              (memoryOf p N M K h view).syn pe (toNs e.reading)) (false, (memoryOf p N M K h view).syn)).2))
            (Unisono.Sync.step_zero_peers_star _ (toNs e.reading) h1c)
          exact h2.2.2.2.2.1
      | peerRelay rel =>
        dsimp only; split_ifs
        · exact ih
        · have h1c : (evalResult (sync.Sync.on_peer_relay (memoryOf p N M K h view).syn rel
              (toNs e.reading)) (0#usize, (memoryOf p N M K h view).syn)).2.peer_count = 0#usize :=
            evalResult_of_spec (on_peer_relay_zero_peers _ rel (toNs e.reading) ih)
          have h2 := evalResult_of_spec
            (d := (sync.SyncSnapshot.EMPTY, (evalResult (sync.Sync.on_peer_relay
              (memoryOf p N M K h view).syn rel (toNs e.reading)) (0#usize, (memoryOf p N M K h view).syn)).2))
            (Unisono.Sync.step_zero_peers_star _ (toNs e.reading) h1c)
          exact h2.2.2.2.2.1
    | asked r outs rep =>
      dsimp only
      have hstep := evalResult_of_spec
        (d := (sync.SyncSnapshot.EMPTY, (memoryOf p N M K h view).syn))
        (Unisono.Sync.step_zero_peers_star (memoryOf p N M K h view).syn (toNs e.reading) ih)
      have hsyn1 : (evalResult (sync.Sync.step (memoryOf p N M K h view).syn (toNs e.reading))
        (sync.SyncSnapshot.EMPTY, (memoryOf p N M K h view).syn)).2.peer_count = 0#usize :=
        hstep.2.2.2.2.1
      split_ifs
      · exact hsyn1
      · exact peer_count_askedRelay p h _ (toNs e.reading)
          (peer_count_askedProbe p h _ (toNs e.reading)
            (peer_count_askedReport p h _ _ _ (toNs e.reading) hsyn1))
    | timer => exact ih

/-- **Exact Star zero-peer traffic theorem:** when `p.peers h = []`, host `h`
never sends any `peerProbe`, `peerEcho`, or `peerRelay` message. -/
theorem star_no_peer_messages {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (hno : p.peers h = []) (view : List (Event H R CoreMsg))
    (dst : H) (msg : CoreMsg) (frames : Finset ℕ)
    (hmem : (dst, msg, frames) ∈ (solution p N M K h view).sends) :
    (∀ pr, msg ≠ .peerProbe pr) ∧ (∀ pe, msg ≠ .peerEcho pe) ∧ (∀ rel, msg ≠ .peerRelay rel) := by
  unfold solution at hmem
  cases hlast : view.getLast? with
  | none => simp [hlast] at hmem
  | some e =>
    simp only [hlast] at hmem
    unfold act stepHost at hmem
    dsimp only at hmem
    cases hobs : e.observation with
    | handed fs rep =>
      simp only [hobs] at hmem
      split_ifs at hmem
      · cases fs with
        | nil => simp at hmem
        | cons _ _ =>
          simp only [List.mem_map, Prod.mk.injEq] at hmem
          obtain ⟨_, _, _, rfl, _⟩ := hmem
          exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
      · simp at hmem
    | received i c fs =>
      simp only [hobs] at hmem
      cases c with
      | audio _ => split_ifs at hmem <;> simp at hmem
      | report rep =>
        by_cases hcond : h = p.sender ∧ rep.stream = p.stream
        · simp only [hcond, and_self, ↓reduceIte, List.mem_singleton, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl, _⟩
          exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
        · simp [hcond] at hmem
      | echo _ => split_ifs at hmem <;> simp at hmem
      | peerProbe pr =>
        by_cases hs : h = p.sender
        · simp [hs] at hmem
        · simp only [hs, ↓reduceIte] at hmem
          cases hres : evalResult ((memoryOf p N M K h view.dropLast).syn.on_peer_probe pr
              (toNs e.reading) (toNs e.reading)) none with
          | none => simp [hres] at hmem
          | some _ => simp [hres, hno] at hmem
      | peerEcho _ => split_ifs at hmem <;> simp at hmem
      | peerRelay _ => split_ifs at hmem <;> simp at hmem
    | asked r outs rep =>
      simp only [hobs] at hmem
      split_ifs at hmem
      · simp at hmem
      · simp only [List.mem_append] at hmem
        rcases hmem with (hrep | hpr) | hrel
        · obtain ⟨_, rep, rfl⟩ := mem_askedReport p h _ _ _ (toNs e.reading) hrep
          exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
        · have := mem_askedProbe p h _ _ hpr; simp [hno] at this
        · have := mem_askedRelay p h _ _ hrel; simp [hno] at this
    | timer => simp [hobs] at hmem

/-- **Exact Star snapshot degeneration:** when `p.peers h = []`, every
`Sync.step` executed by `Core.solution` publishes `peer_active = false`,
`active_peers = 0`, `diff_var_ns2 = 0`, and `common_line` equal to
`sender_filter.to_line`. -/
theorem star_sync_snapshot_eq_sender_kalman {H : Type} {R : ℕ} [DecidableEq H]
    (p : Params H) (N M K : Std.Usize) (h : H) (hno : p.peers h = [])
    (view : List (Event H R CoreMsg)) (t : Std.I64) :
    let m := memoryOf p N M K h view
    let (snap, _) := evalResult (sync.Sync.step m.syn t) (sync.SyncSnapshot.EMPTY, m.syn)
    snap.peer_active = false ∧ snap.active_peers = 0#u8 ∧ snap.diff_var_ns2 = 0#u64 := by
  have h0 := sync_zero_peers_inv p N M K h hno view
  have hspec := evalResult_of_spec
    (d := (sync.SyncSnapshot.EMPTY, (memoryOf p N M K h view).syn))
    (Unisono.Sync.step_zero_peers_star (memoryOf p N M K h view).syn t h0)
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩

/-- **Exact Star regulator degeneration:** when `peer_active = false` and
`was_peer = false`, `ModalPlayer.cycle` inside `Core.solution` produces the
exact same `Plan` and playback state as single-mode `Player.cycle` at
`p.regulation.star_gain`. -/
theorem star_modal_player_eq_single_mode (m : player.ModalPlayer) (pl : player.Player)
    (now later : timing.Position) (frames : Std.U32) (duration : Std.I64)
    (schedule : timing.Schedule) (epoch : Std.U32) (com_now com_then : Std.I64)
    (hgain : m.regulation.star_gain = pl.regulation.gain)
    (hlim : m.regulation.limit = pl.regulation.limit)
    (hjump : m.regulation.jump = pl.regulation.jump)
    (hrun : m.running = pl.running) (hpos : m.position = pl.position)
    (hpace : m.diff_pace = pl.pace) (hslope : m.slope = pl.slope)
    (hwp : m.was_peer = false) :
    let rm := evalResult
      (player.ModalPlayer.cycle m now later frames duration schedule false epoch com_now com_then)
      (emptyPlan, m)
    let rp := evalResult
      (player.Player.cycle pl now later frames duration schedule.level_slope)
      (emptyPlan, pl)
    rm.1 = rp.1 ∧ rm.2.running = rp.2.running ∧ rm.2.position = rp.2.position
      ∧ rm.2.diff_pace = rp.2.pace ∧ rm.2.slope = rp.2.slope ∧ rm.2.was_peer = false := by
  have hspec := Unisono.Player.modal_star_matches_player m pl now later frames duration schedule
    epoch com_now com_then hgain hlim hjump hrun hpos hpace hslope hwp
  obtain ⟨hrm, -⟩ := evalResult_spec_eq (d := (emptyPlan, m))
    (Unisono.Player.modal_cycle_spec m now later frames duration schedule false epoch com_now com_then)
  obtain ⟨hrp, -⟩ := evalResult_spec_eq (d := (emptyPlan, pl))
    (Unisono.Player.cycle_spec pl now later frames duration schedule.level_slope)
  rw [hrm, hrp] at hspec
  simp only [bind_ok, WP.spec_ok] at hspec
  exact hspec

/-! ## 6. Within-block speed and conditional boundary-step bounds under `World.WithinBounds` -/

private theorem receiver_turn_preserves_modal {N M K : Std.Usize} (r : receiver.Receiver N M K) :
    receiver.Receiver.turn r ⦃ r' =>
      r'.use_sync = r.use_sync ∧ r'.modal_player = r.modal_player
      ∧ r'.sync_snapshot = r.sync_snapshot ⦄ := by
  unfold receiver.Receiver.turn
  cases r.next <;> simp

private theorem receiver_reached_preserves_modal {N M K : Std.Usize} (r : receiver.Receiver N M K)
    (schedule : timing.Schedule) (now : timing.Position) (first : Std.I64) :
    receiver.Receiver.reached r schedule now first ⦃ out =>
      out.2.use_sync = r.use_sync ∧ out.2.modal_player = r.modal_player
      ∧ out.2.sync_snapshot = r.sync_snapshot ⦄ := by
  unfold receiver.Receiver.reached
  cases r.next with
  | none => simp
  | some next =>
    dsimp only
    split
    · step with receiver_turn_preserves_modal r as ⟨r1, hu1, hm1, hs1⟩
      step as ⟨o⟩
      cases o with
      | none => simp [hu1, hm1, hs1]
      | some turned =>
        dsimp only
        cases r1.next with
        | none => simp [hu1, hm1, hs1]
        | some next1 =>
          dsimp only
          split
          · step with receiver_turn_preserves_modal r1 as ⟨r2, hu2, hm2, hs2⟩
            step as ⟨o1⟩
            cases o1 <;> simp [hu2.trans hu1, hm2.trans hm1, hs2.trans hs1]
          · simp [hu1, hm1, hs1]
    · simp

@[local step]
private theorem position_advance_eq_spec (p : timing.Position) (s : timing.Step) (n : Std.U64) :
    timing.Position.advance p s n ⦃ o => timing.Position.advance p s n = ok o ⦄ := by
  obtain ⟨o, ho, _⟩ := exists_ok_of_spec (Unisono.Player.position_advance_total p s n)
  rw [ho, WP.spec_ok]

set_option maxHeartbeats 800000 in
/-- `ModalPlayer.cycle` detailed specification covering step bounds,
jump-distance lower bound, non-jump continuity, and `Position.advance`
post-state. -/
theorem modal_cycle_full_spec (m : player.ModalPlayer) (now later : timing.Position)
    (frames : Std.U32) (duration : Std.I64) (schedule : timing.Schedule)
    (peer_active : Bool) (epoch : Std.U32) (com_now com_then : Std.I64) :
    player.ModalPlayer.cycle m now later frames duration schedule peer_active epoch com_now com_then
      ⦃ out =>
        -Unisono.Player.reachOf m.regulation.limit ≤ out.1.step.offset.val
        ∧ out.1.step.offset.val ≤ Unisono.Player.reachOf m.regulation.limit
        ∧ out.2.regulation = m.regulation
        ∧ (out.1.frames.val = 0 ∨
            (out.1.frames = frames
             ∧ out.2.running = true
             ∧ (out.1.jumped = false → out.1.start = m.position)
             ∧ (out.1.jumped = true →
                  m.running = false ∨
                  (m.regulation.jump.val : ℝ) < |posToReal out.1.start - posToReal m.position|)
             ∧ (∀ next, timing.Position.advance out.1.start out.1.step
                  (UScalar.cast .U64 out.1.frames) = ok (some next) →
                  out.2.position = next))) ⦄ := by
  have hb := Unisono.Player.reachOf_bounds m.regulation.limit
  have hu : timing.Step.UNITY.offset.val = 0 := by simp [timing.Step.UNITY]
  unfold player.ModalPlayer.cycle
  step as ⟨scheduled⟩
  split
  · rw [WP.spec_ok]; refine ⟨by rw [hu]; omega, by rw [hu]; omega, rfl, Or.inl rfl⟩
  · split
    · rw [WP.spec_ok]; refine ⟨by rw [hu]; omega, by rw [hu]; omega, rfl, Or.inl rfl⟩
    · obtain ⟨jumped, hjump_eq, -⟩ := exists_ok_of_spec
        (Unisono.Player.modal_jumps_total m now)
      rw [hjump_eq, bind_ok]
      cases jumped with
      | true =>
        simp only [↓reduceIte]
        step as ⟨st, hlo, hhi⟩
        have htuple :
            (if peer_active = true then do
              let i4 ← lift (core.num.I64.saturating_sub com_then com_now)
              let com_sched ← player.ns_to_frames_q32 schedule i4
              let reach ← player.reach_for m.regulation.limit
              let i5 ← lift (IScalar.cast .I128 com_sched)
              let i6 ← lift (core.num.I128.wrapping_shl i5 32#u32)
              let i7 ← lift (UScalar.hcast .I64 frames)
              let raw_com_pace ← fixed.div_floor i6 i7
              let i8 ← player.clamp_sym_i128 raw_com_pace reach
              let com_pace ← fixed.saturate i8
              let i9 ← timing.Step.impl.offset st
              let i10 ← lift (core.num.I64.wrapping_sub i9 com_pace)
              let i11 ← lift (UScalar.hcast .I128 frames)
              let i12 ← lift (IScalar.cast .I128 com_pace)
              let i13 ← lift (core.num.I128.wrapping_mul i11 i12)
              let i14 ← lift (core.num.I128.wrapping_shr i13 32#u32)
              let i15 ← fixed.saturate i14
              let i16 ← lift (core.num.I64.saturating_sub com_sched i15)
              ok (i10, com_pace, i15, i16)
            else do
              let i4 ← timing.Step.impl.offset st
              ok (i4, 0#i64, 0#i64, 0#i64)) ⦃ _ => True ⦄ := by
          cases peer_active <;> simp <;> step*
        apply WP.spec_bind htuple
        intro ⟨i, i1, i2, i3⟩ _
        step as ⟨u_fr, hu_fr⟩
        step with position_advance_eq_spec now st u_fr as ⟨o, ho_eq⟩
        have hjd : m.running = false ∨
            (m.regulation.jump.val : ℝ) < |posToReal now - posToReal m.position| := by
          cases hrun : m.running with
          | false => exact Or.inl rfl
          | true => exact Or.inr (posToReal_sub_of_jumps_true m now hrun hjump_eq)
        cases o with
        | none =>
          rw [WP.spec_ok]
          refine ⟨hlo, hhi, rfl, Or.inr ⟨rfl, rfl, (fun hc => nomatch hc), (fun _ => hjd),
            fun next hnext => by
              rw [← hu_fr, ho_eq] at hnext
              exact nomatch (ok_inj hnext)⟩⟩
        | some next0 =>
          rw [WP.spec_ok]
          refine ⟨hlo, hhi, rfl, Or.inr ⟨rfl, rfl, (fun hc => nomatch hc), (fun _ => hjd),
            fun next hnext => by
              rw [← hu_fr, ho_eq] at hnext
              exact Option.some.inj (ok_inj hnext)⟩⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hrun : m.running = true := by
          cases hr : m.running with
          | true => rfl
          | false =>
            unfold player.ModalPlayer.jumps at hjump_eq
            simp [hr] at hjump_eq
        cases peer_active with
        | true =>
          simp only [↓reduceIte]
          apply WP.spec_bind (Pₘ := fun t => t.1 = m.regulation)
          · repeat' (first | split | step*)
          · intro ⟨mr, i, i1, i2, i3, b, i4⟩ hmr
            subst hmr
            step; step; step; step; step; step; step; step; step; step
            step; step; step; step; step; step; step; step; step; step
            step; step; step; step; step; step; step; step; step; step
            step; step; step; step; step; step
            step as ⟨st, hlo, hhi⟩
            step; step; step; step; step; step; step; step; step; step
            step; step; step; step; step; step; step; step; step; step
            step as ⟨u_fr, hu_fr⟩
            step with position_advance_eq_spec m.position st u_fr as ⟨o, ho_eq⟩
            cases o with
            | none =>
              rw [WP.spec_ok]
              refine ⟨hlo, hhi, rfl, Or.inr ⟨rfl, hrun, (fun _ => rfl), (fun hc => nomatch hc),
                fun next hnext => by
                  rw [← hu_fr, ho_eq] at hnext
                  exact nomatch (ok_inj hnext)⟩⟩
            | some next0 =>
              rw [WP.spec_ok]
              refine ⟨hlo, hhi, rfl, Or.inr ⟨rfl, hrun, (fun _ => rfl), (fun hc => nomatch hc),
                fun next hnext => by
                  rw [← hu_fr, ho_eq] at hnext
                  exact Option.some.inj (ok_inj hnext)⟩⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply WP.spec_bind (Pₘ := fun _ => True)
          · cases m.was_peer <;> simp [lift]
          · intro ⟨i, i1, b, i2, total_pace⟩ _
            step; step; step; step; step; step; step; step; step; step
            step; step; step; step
            step as ⟨st, hlo, hhi⟩
            step
            step as ⟨u_fr, hu_fr⟩
            step with position_advance_eq_spec m.position st u_fr as ⟨o, ho_eq⟩
            cases o with
            | none =>
              rw [WP.spec_ok]
              refine ⟨hlo, hhi, rfl, Or.inr ⟨rfl, hrun, (fun _ => rfl), (fun hc => nomatch hc),
                fun next hnext => by
                  rw [← hu_fr, ho_eq] at hnext
                  exact nomatch (ok_inj hnext)⟩⟩
            | some next0 =>
              rw [WP.spec_ok]
              refine ⟨hlo, hhi, rfl, Or.inr ⟨rfl, hrun, (fun _ => rfl), (fun hc => nomatch hc),
                fun next hnext => by
                  rw [← hu_fr, ho_eq] at hnext
                  exact Option.some.inj (ok_inj hnext)⟩⟩

/-- `Receiver.cycle` preserves `use_sync = true` and `modal_player.regulation`,
and inherits the full `modal_cycle_full_spec` postcondition on the returned
`Plan` and next `ModalPlayer`. -/
theorem receiver_cycle_plan_spec {N M K : Std.Usize} (r : receiver.Receiver N M K)
    (time duration : Std.I64) (frames : Std.U32) (huse : r.use_sync = true) :
    receiver.Receiver.cycle r time duration frames ⦃ out =>
      -Unisono.Player.reachOf r.modal_player.regulation.limit ≤ out.1.step.offset.val
      ∧ out.1.step.offset.val ≤ Unisono.Player.reachOf r.modal_player.regulation.limit
      ∧ out.2.use_sync = true
      ∧ out.2.modal_player.regulation = r.modal_player.regulation
      ∧ (out.1.frames.val = 0 ∨
          (out.1.frames = frames
           ∧ out.2.modal_player.running = true
           ∧ (out.1.jumped = false → out.1.start = r.modal_player.position)
           ∧ (out.1.jumped = true →
                r.modal_player.running = false ∨
                (r.modal_player.regulation.jump.val : ℝ) <
                  |posToReal out.1.start - posToReal r.modal_player.position|)
           ∧ (∀ next, timing.Position.advance out.1.start out.1.step
                (UScalar.cast .U64 out.1.frames) = ok (some next) →
                out.2.modal_player.position = next))) ⦄ := by
  have hb := Unisono.Player.reachOf_bounds r.modal_player.regulation.limit
  have hu : timing.Step.UNITY.offset.val = 0 := by simp [timing.Step.UNITY]
  unfold receiver.Receiver.cycle
  split
  · cases r.schedule with
    | none =>
      rw [WP.spec_ok]; refine ⟨by rw [hu]; omega, by rw [hu]; omega, huse, rfl, Or.inl rfl⟩
    | some schedule =>
      dsimp only
      step as ⟨end_time⟩
      split
      · step with Unisono.Sync.snapshot_sender_time_total r.sync_snapshot time as ⟨first⟩
        step with Unisono.Sync.snapshot_sender_time_total r.sync_snapshot end_time as ⟨last⟩
        step as ⟨o1⟩
        cases o1 with
        | none =>
          rw [WP.spec_ok]; refine ⟨by rw [hu]; omega, by rw [hu]; omega, huse, rfl, Or.inl rfl⟩
        | some now =>
          dsimp only
          step with receiver_reached_preserves_modal r schedule now first as ⟨o2, r1, hu1, hm1, hs1⟩
          cases o2 with
          | none =>
            rw [WP.spec_ok]
            refine ⟨by rw [hu]; omega, by rw [hu]; omega, hu1.trans huse, by rw [hm1], Or.inl rfl⟩
          | some turned =>
            obtain ⟨schedule1, now1⟩ := turned
            dsimp only
            step as ⟨o3⟩
            cases o3 with
            | none =>
              rw [WP.spec_ok]
              refine ⟨by rw [hu]; omega, by rw [hu]; omega, hu1.trans huse, by rw [hm1], Or.inl rfl⟩
            | some later =>
              dsimp only
              have hu1' : r1.use_sync = true := hu1.trans huse
              simp only [hu1', ↓reduceIte]
              step with Unisono.Sync.snapshot_common_offset_ns_total r1.sync_snapshot time as ⟨com_now⟩
              step with Unisono.Sync.snapshot_common_offset_ns_total r1.sync_snapshot end_time as ⟨com_then⟩
              step with modal_cycle_full_spec r1.modal_player now1 later frames duration schedule1
                r1.sync_snapshot.peer_active r1.sync_snapshot.epoch com_now com_then as ⟨out, m', hlo, hhi, hreg, hbody⟩
              rw [hm1] at hlo hhi hreg hbody
              exact ⟨hlo, hhi, hreg, hbody⟩
      · rw [WP.spec_ok]; refine ⟨by rw [hu]; omega, by rw [hu]; omega, huse, rfl, Or.inl rfl⟩
  · rw [WP.spec_ok]; refine ⟨by rw [hu]; omega, by rw [hu]; omega, huse, rfl, Or.inl rfl⟩

/-- `Receiver.packet` preserves `use_sync = true` and `modal_player.regulation`. -/
private theorem receiver_packet_preserves_modal_reg {N M K : Std.Usize}
    (r : receiver.Receiver N M K) (hdr : packet.Audio) (t : Std.I64)
    (huse : r.use_sync = true) :
    receiver.Receiver.packet r hdr t ⦃ out =>
      out.2.use_sync = true
      ∧ out.2.modal_player.regulation = r.modal_player.regulation ⦄ := by
  have hadopt : ∀ r0 : receiver.Receiver N M K, r0.use_sync = true →
      receiver.Receiver.adopt r0 hdr ⦃ r' =>
        r'.use_sync = true ∧ r'.modal_player.regulation = r0.modal_player.regulation ⦄ := by
    intro r0 hu0
    unfold receiver.Receiver.adopt player.Player.stop player.ModalPlayer.stop
    have hsc : (if r0.following = true then ok (hdr, decide (hdr.clock = r0.clock_id))
      else ok (hdr, false)) ⦃ _ => True ⦄ := by split <;> simp
    apply WP.spec_bind hsc
    intro ⟨h1, sc⟩ _
    step as ⟨p⟩; step as ⟨a⟩
    split <;> step*
  have hkeep : ∀ r0 : receiver.Receiver N M K, r0.use_sync = true →
      receiver.Receiver.keep_newest r0 hdr ⦃ r' =>
        r'.use_sync = true ∧ r'.modal_player.regulation = r0.modal_player.regulation ⦄ := by
    intro r0 hu0
    unfold receiver.Receiver.keep_newest
    rw [hu0]; simp only [↓reduceIte]
    split
    · simp [hu0]
    · step with Unisono.Presence.width_spec r0.presence as ⟨w, _⟩
      split
      · simp [hu0]
      · unfold presence.Presence.impl.base
        simp only [bind_ok]
        step as ⟨i⟩; step as ⟨e⟩; step as ⟨se⟩; step as ⟨lim⟩
        split
        · split
          · split
            · step as ⟨tgt⟩
              have hnb : (if tgt < hdr.index then ok tgt else ok hdr.index) ⦃ _ => True ⦄ := by
                split <;> simp
              apply WP.spec_bind hnb
              intro nb _
              step as ⟨p⟩
            · simp [hu0]
          · simp [hu0]
        · simp [hu0]
  have hstale : ∀ (r0 : receiver.Receiver N M K) (m : presence.Marked), r0.use_sync = true →
      receiver.Receiver.stale r0 m t ⦃ out =>
        out.2.use_sync = true ∧ out.2.modal_player.regulation = r0.modal_player.regulation ⦄ := by
    intro r0 m hu0
    unfold receiver.Receiver.stale
    have hf : (if r0.fresh > t then ok t else ok r0.fresh) ⦃ _ => True ⦄ := by
      split <;> simp
    apply WP.spec_bind hf
    intro i _
    split
    · simp [hu0]
    · split
      · simp [hu0]
      · split
        · simp [hu0]
        · split
          · simp [hu0]
          · step as ⟨_⟩; simp [hu0]
  have hrenew : ∀ r0 : receiver.Receiver N M K, r0.use_sync = true →
      receiver.Receiver.renew r0 hdr ⦃ out =>
        out.2.use_sync = true ∧ out.2.modal_player.regulation = r0.modal_player.regulation ⦄ := by
    intro r0 hu0
    unfold receiver.Receiver.renew player.Player.stop player.ModalPlayer.stop
    step*
  have hnote : ∀ r0 : receiver.Receiver N M K, r0.use_sync = true →
      receiver.Receiver.note r0 hdr ⦃ r' =>
        r'.use_sync = true ∧ r'.modal_player.regulation = r0.modal_player.regulation ⦄ := by
    intro r0 hu0
    unfold receiver.Receiver.note
    cases r0.schedule with
    | none => simp [hu0]
    | some _ =>
      dsimp only
      cases r0.next with
      | none =>
        dsimp only; repeat' (first | split | step*)
      | some _ =>
        dsimp only
        cases r0.after with
        | none =>
          dsimp only; repeat' (first | split | step*)
        | some _ =>
          dsimp only
          split
          · simp [hu0]
          · step as ⟨b⟩
            split
            · simp [hu0]
            · step with receiver_turn_preserves_modal r0 as ⟨r1, hu1, hm1, _⟩
              simp [hu1.trans hu0, hm1]
  have hrefresh : ∀ (r0 : receiver.Receiver N M K) (m : presence.Marked), r0.use_sync = true →
      receiver.Receiver.refresh r0 hdr m t ⦃ r' =>
        r'.use_sync = true ∧ r'.modal_player.regulation = r0.modal_player.regulation ⦄ := by
    intro r0 m hu0
    unfold receiver.Receiver.refresh
    split
    · exact hnote _ hu0
    · split
      · exact hnote _ hu0
      · split
        · step as ⟨b⟩
          split
          · exact hnote _ hu0
          · split <;> simp [hu0]
        · split <;> simp [hu0]
  have haccept : ∀ (r0 : receiver.Receiver N M K) (ad : Bool), r0.use_sync = true →
      receiver.Receiver.accept r0 hdr t ad ⦃ out =>
        out.2.use_sync = true ∧ out.2.modal_player.regulation = r0.modal_player.regulation ⦄ := by
    intro r0 ad hu0
    unfold receiver.Receiver.accept
    step with hkeep { r0 with heard := t } hu0 as ⟨r1, hu1, hm1⟩
    have hmeas : (if r1.use_sync = true then ok r1
        else receiver.Receiver.measure r1 hdr t) = ok r1 := by rw [hu1]; rfl
    rw [hmeas, bind_ok]
    step as ⟨i⟩
    step as ⟨first, p⟩
    step with hstale { r1 with presence := p } first hu1 as ⟨restarted, r3, hu3, hm3⟩
    have h4 :
        (if restarted = true then do
          let (marked1, self5) ← receiver.Receiver.renew r3 hdr
          ok (self5, marked1)
        else ok (r3, first)) ⦃ p4 =>
          p4.1.use_sync = true ∧ p4.1.modal_player.regulation = r0.modal_player.regulation ⦄ := by
      split
      · step with hrenew r3 hu3 as ⟨m1, r5, hu5, hm5⟩
        simp [hu5, hm5.trans (hm3.trans hm1)]
      · simp [hu3, hm3.trans hm1]
    apply WP.spec_bind h4
    intro ⟨r4, m4⟩ ⟨hu4, hm4⟩
    step with hrefresh r4 m4 hu4 as ⟨r5, hu5, hm5⟩
    simp [hu5, hm5.trans hm4]
  unfold receiver.Receiver.packet
  split
  · simp [huse]
  · have hi : (if r.heard > t then ok t else ok r.heard) ⦃ _ => True ⦄ := by
      split <;> simp
    apply WP.spec_bind hi
    intro i _
    step as ⟨adopted⟩
    split
    · step with hadopt { r with heard := i } huse as ⟨r1, hu1, hm1⟩
      step with haccept r1 adopted hu1 as ⟨out, hu2, hm2⟩
      exact ⟨hu2, hm2.trans hm1⟩
    · split
      · simp [huse]
      · exact haccept { r with has_candidate := false, heard := i } adopted huse

/-- Across every event in host `h`'s view, every speaker's `Receiver` in
`Core.solution` keeps `use_sync = true` and `modal_player.regulation = p.regulation`. -/
theorem rcv_modal_inv {H : Type} {R : ℕ} [DecidableEq H] (p : Params H) (N M K : Std.Usize)
    (h : H) (view : List (Event H R CoreMsg)) (r : Fin R) :
    ((memoryOf p N M K h view).rcv r).use_sync = true
    ∧ ((memoryOf p N M K h view).rcv r).modal_player.regulation = p.regulation := by
  induction view using List.reverseRecOn with
  | nil =>
    unfold memoryOf Memory.init initReceiver
    dsimp only
    unfold receiver.Receiver.enable_sync player.ModalPlayer.set_regulation
    simp [evalResult_eq_of_ok]
  | append_singleton view e ih =>
    rw [memoryOf_append]
    unfold remember stepHost
    cases hobs : e.observation with
    | handed fs rep =>
      dsimp only; split_ifs
      · cases fs <;> exact ih
      · exact ih
    | received i c fs =>
      cases c with
      | audio hdr =>
        dsimp only; split_ifs
        · exact ih
        · let d0 : receiver.Heard :=
            { ignored := false, adopted := false, restarted := false,
              marked := { stored := 0#u32, duplicate := 0#u32, late := 0#u32, early := 0#u32 } }
          have hp := evalResult_of_spec
            (d := (d0, (memoryOf p N M K h view).rcv r))
            (receiver_packet_preserves_modal_reg ((memoryOf p N M K h view).rcv r) hdr (toNs e.reading) ih.1)
          exact ⟨hp.1, hp.2.trans ih.2⟩
      | report _ => dsimp only; split_ifs <;> exact ih
      | echo ec =>
        dsimp only; split_ifs
        · exact ih
        · unfold receiver.Receiver.apply_sync
          cases (evalResult (sync.Sync.step _ (toNs e.reading)) _).1.valid <;>
            simp [evalResult_eq_of_ok, ih.2]
      | peerProbe _ =>
        dsimp only
        split
        · exact ih
        · cases evalResult _ none with
          | none => exact ih
          | some _ => dsimp only; split <;> exact ih
      | peerEcho _ =>
        dsimp only; split_ifs
        · exact ih
        · unfold receiver.Receiver.apply_sync
          cases (evalResult (sync.Sync.step _ (toNs e.reading)) _).1.valid <;>
            simp [evalResult_eq_of_ok, ih.2]
      | peerRelay _ =>
        dsimp only; split_ifs
        · exact ih
        · unfold receiver.Receiver.apply_sync
          cases (evalResult (sync.Sync.step _ (toNs e.reading)) _).1.valid <;>
            simp [evalResult_eq_of_ok, ih.2]
    | asked r' outs rep =>
      dsimp only
      have happly : ∀ (snap : sync.SyncSnapshot) (rv : receiver.Receiver N M K),
          rv.modal_player.regulation = p.regulation →
          (evalResult (receiver.Receiver.apply_sync rv snap) rv).use_sync = true
          ∧ (evalResult (receiver.Receiver.apply_sync rv snap) rv).modal_player.regulation = p.regulation := by
        intro snap rv hreg
        unfold receiver.Receiver.apply_sync
        cases snap.valid <;> simp [evalResult_eq_of_ok, hreg]
      let snap := (evalResult (sync.Sync.step (memoryOf p N M K h view).syn (toNs e.reading))
        (sync.SyncSnapshot.EMPTY, (memoryOf p N M K h view).syn)).1
      split_ifs
      · by_cases hr : r = r'
        · subst hr
          simp only [Function.update_self]
          have ha := happly snap ((memoryOf p N M K h view).rcv r) ih.2
          have hc := evalResult_of_spec
            (d := (emptyPlan, evalResult (receiver.Receiver.apply_sync
              ((memoryOf p N M K h view).rcv r) snap) ((memoryOf p N M K h view).rcv r)))
            (receiver_cycle_plan_spec _ (toNs rep) (blockDurationNs outs.length p.rate)
              (natToU32 outs.length) ha.1)
          exact ⟨hc.2.2.1, hc.2.2.2.1.trans ha.2⟩
        · simp only [Function.update_of_ne hr]; exact ih
      · by_cases hr : r = r'
        · subst hr
          simp only [Function.update_self]
          have ha := happly snap ((memoryOf p N M K h view).rcv r) ih.2
          have hc := evalResult_of_spec
            (d := (emptyPlan, evalResult (receiver.Receiver.apply_sync
              ((memoryOf p N M K h view).rcv r) snap) ((memoryOf p N M K h view).rcv r)))
            (receiver_cycle_plan_spec _ (toNs rep) (blockDurationNs outs.length p.rate)
              (natToU32 outs.length) ha.1)
          exact ⟨hc.2.2.1, hc.2.2.2.1.trans ha.2⟩
        · simp only [Function.update_of_ne hr]; exact ih
    | timer => exact ih

/-- The normalized real pace bound `reachOf limit / 2^64` (at most `3 / 1000 < 1`). -/
def paceBound (limit : Std.U32) : ℝ :=
  (Unisono.Player.reachOf limit : ℝ) / (2 : ℝ) ^ 64

theorem paceBound_nonneg (limit : Std.U32) : 0 ≤ paceBound limit := by
  have hb := Unisono.Player.reachOf_bounds limit
  unfold paceBound
  exact div_nonneg (by exact_mod_cast hb.1) (by positivity)

theorem paceBound_le_three_thousandths (limit : Std.U32) : paceBound limit ≤ 3 / 1000 := by
  have hb := Unisono.Player.reachOf_bounds limit
  unfold paceBound
  rw [div_le_iff₀ (by positivity)]
  have h1 : (Unisono.Player.reachOf limit : ℝ) ≤ (55340232221128654 : ℝ) := by
    exact_mod_cast hb.2
  linarith [show (55340232221128654 : ℝ) ≤ 3 / 1000 * (2 : ℝ) ^ 64 by norm_num]

theorem paceBound_lt_one (limit : Std.U32) : paceBound limit < 1 :=
  lt_of_le_of_lt (paceBound_le_three_thousandths limit) (by norm_num)

/-- Local speed-bound lemma: if a continuous step `(k, k + 1)` with
`plays r k = some x`, `plays r (k + 1) = some y`, `x < y < x + 2` satisfies
`|y - x - 1| ≤ u` (with `0 ≤ u < 1`), then in any world satisfying
`World.WithinBounds B` its `World.speed` is within
`(2 ε + (1 + ε) u) / (1 - ε)` of `1`. -/
theorem speed_bound_of_step {H : Type} {R : ℕ} (w : World H R) (B : Bounds H)
    (hw : w.WithinBounds B) {plays : Fin R → ℕ → Option ℝ} {r : Fin R} {k : ℕ}
    {x y u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hx : plays r k = some x) (hy : plays r (k + 1) = some y)
    (hstep : |y - x - 1| ≤ u)
    (hv : w.speed plays r k = some v) :
    |v - 1| ≤ (2 * B.deviceRate + (1 + B.deviceRate) * u) / (1 - B.deviceRate) := by
  obtain ⟨-, hsrc, hspk, -, -, -, -, -, -, -, -⟩ := hw
  set ε := B.deviceRate
  have hε0 : 0 ≤ ε := B.deviceRate_nonneg
  have hε1 : ε < 1 := B.deviceRate_lt_one
  have h1m : 0 < 1 - ε := by linarith
  have h1p : 0 < 1 + ε := by linarith
  have hrate : 0 < w.rate := w.rate_pos
  unfold World.speed at hv
  rw [hx, hy] at hv
  dsimp only at hv
  split_ifs at hv with hcont
  injection hv with hv
  subst hv
  have hstep_xy := abs_le.mp hstep
  have hcap := w.captured_sub_mem hsrc hcont.1.le
  have hout_abs := abs_le.mp ((hspk r) k)
  have hout : (1 - ε) / w.rate ≤ (w.speaker r).out (k + 1) - (w.speaker r).out k
      ∧ (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ (1 + ε) / w.rate := by
    constructor
    · rw [sub_div]; linarith [hout_abs.1]
    · rw [add_div]; linarith [hout_abs.2]
  set Δc := w.captured y - w.captured x
  set Δo := (w.speaker r).out (k + 1) - (w.speaker r).out k
  have hΔo_pos : 0 < Δo := by
    have : 0 < (1 - ε) / w.rate := div_pos h1m hrate
    linarith [hout.1]
  have hcap_lo : (1 - ε) / w.rate * (1 - u) ≤ Δc := by
    have h1 : 0 ≤ (1 - ε) / w.rate := div_nonneg h1m.le hrate.le
    nlinarith [hcap.1]
  have hcap_hi : Δc ≤ (1 + ε) / w.rate * (1 + u) := by
    have h1 : 0 ≤ (1 + ε) / w.rate := div_nonneg h1p.le hrate.le
    nlinarith [hcap.2]
  have hhi : Δc / Δo - 1 ≤ (2 * ε + (1 + ε) * u) / (1 - ε) := by
    have hfrac : Δc / Δo ≤ ((1 + ε) / w.rate * (1 + u)) / ((1 - ε) / w.rate) := by
      rw [div_le_div_iff₀ hΔo_pos (div_pos h1m hrate)]
      have h0 : 0 ≤ (1 - ε) / w.rate := div_nonneg h1m.le hrate.le
      have h1 : 0 ≤ (1 + ε) / w.rate * (1 + u) := by positivity
      nlinarith [hout.1, hcap_hi, h0, h1]
    have hsimp : ((1 + ε) / w.rate * (1 + u)) / ((1 - ε) / w.rate)
        = (1 + ε) * (1 + u) / (1 - ε) := by
      have hr : w.rate ≠ 0 := hrate.ne'; field_simp
    rw [hsimp] at hfrac
    have hdiff : (1 + ε) * (1 + u) / (1 - ε) - 1 = (2 * ε + (1 + ε) * u) / (1 - ε) := by
      have hne : 1 - ε ≠ 0 := h1m.ne'; field_simp; ring
    linarith
  have hlo : -((2 * ε + (1 + ε) * u) / (1 - ε)) ≤ Δc / Δo - 1 := by
    have hfrac : ((1 - ε) / w.rate * (1 - u)) / ((1 + ε) / w.rate) ≤ Δc / Δo := by
      rw [div_le_div_iff₀ (div_pos h1p hrate) hΔo_pos]
      have h1 : 0 ≤ (1 - ε) / w.rate * (1 - u) := by
        have : 0 ≤ 1 - u := by linarith
        positivity
      nlinarith [hout.2, hcap_lo]
    have hsimp : ((1 - ε) / w.rate * (1 - u)) / ((1 + ε) / w.rate)
        = (1 - ε) * (1 - u) / (1 + ε) := by
      have hr : w.rate ≠ 0 := hrate.ne'; field_simp
    rw [hsimp] at hfrac
    have hdiff : 1 - (1 - ε) * (1 - u) / (1 + ε) = (2 * ε + (1 - ε) * u) / (1 + ε) := by
      have hne : 1 + ε ≠ 0 := h1p.ne'; field_simp; ring
    have hcmp : (2 * ε + (1 - ε) * u) / (1 + ε) ≤ (2 * ε + (1 + ε) * u) / (1 - ε) := by
      rw [div_le_div_iff₀ h1p h1m]; nlinarith
    linarith
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Within any single block planned by `planPlays`, consecutive played samples
`(k, k + 1)` advance by `stepToReal plan.step`. -/
theorem planPlays_succ_sub (outputs : List ℕ) (plan : player.Plan) {k : ℕ} {x y : ℝ}
    (hx : planPlays outputs plan k = some x)
    (hy : planPlays outputs plan (k + 1) = some y) :
    y - x = stepToReal plan.step := by
  unfold planPlays at hx hy
  split_ifs at hx hy with h0
  cases hhd : outputs.head? with
  | none => simp [hhd] at hx
  | some first =>
    simp only [hhd] at hx hy
    split_ifs at hx with hkx
    split_ifs at hy with hky
    injection hx with hx; injection hy with hy
    rw [← hx, ← hy]
    have hk : k + 1 - first = (k - first) + 1 := by omega
    rw [hk]
    push_cast
    ring

/-- **Within-block speed bound of `Core.solution` (unconditional, all `k : ℕ`):**
in every world satisfying `World.WithinBounds B`, for every speaker `r` and
every consecutive pair `(k, k + 1)` belonging to the same playback block `b`,
`Core.solution`'s speed lies within
`(2 ε_D + (1 + ε_D) * paceBound limit) / (1 - ε_D)` of `1`. -/
theorem withinBlock_speed_bound {H : Type} {R : ℕ} [DecidableEq H]
    (p : Params H) (N M K : Std.Usize) (w : World H R) (B : Bounds H)
    (hw : w.WithinBounds B) (lookahead : ℕ+) {r : Fin R} {b k : ℕ} {v : ℝ}
    (hk1 : k ∈ (w.speaker r).block b) (hk2 : k + 1 ∈ (w.speaker r).block b)
    (hv : w.speed ((solution p N M K : Solution H R CoreMsg).plays w lookahead) r k = some v) :
    |v - 1| ≤
      (2 * B.deviceRate + (1 + B.deviceRate) * paceBound p.regulation.limit) /
        (1 - B.deviceRate) := by
  set σ : Solution H R CoreMsg := solution p N M K
  cases hpk : σ.plays w lookahead r k with
  | none => simp [World.speed, hpk] at hv
  | some x =>
    cases hpk1 : σ.plays w lookahead r (k + 1) with
    | none => simp [World.speed, hpk, hpk1] at hv
    | some y =>
      obtain ⟨b₁, n₁, hmem₁, hnext₁, hear₁, hact₁⟩ :=
        exists_asked_of_plays_some σ w lookahead hpk
      obtain ⟨b₂, n₂, hmem₂, hnext₂, hear₂, hact₂⟩ :=
        exists_asked_of_plays_some σ w lookahead hpk1
      have huniq : ∀ b' k', k' ∈ (w.speaker r).block b → k' ∈ (w.speaker r).block b' → b' = b := by
        intro b' k' h1 h2
        unfold PlaybackDevice.block at h1 h2
        simp only [List.mem_range'] at h1 h2
        have hlt1 : k' < (w.speaker r).first (b + 1) := by
          have := (w.speaker r).first_strictMono (Nat.lt_succ_self b); omega
        have hlt2 : k' < (w.speaker r).first (b' + 1) := by
          have := (w.speaker r).first_strictMono (Nat.lt_succ_self b'); omega
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := (w.speaker r).first_strictMono.monotone (show b' + 1 ≤ b by omega)
          omega
        · have := (w.speaker r).first_strictMono.monotone (show b + 1 ≤ b' by omega)
          omega
      have hb1 : b₁ = b := huniq b₁ k hk1 hmem₁
      have hb2 : b₂ = b := huniq b₂ (k + 1) hk2 hmem₂
      rw [hb1] at hmem₁ hnext₁ hear₁ hact₁
      rw [hb2] at hmem₂ hnext₂ hear₂ hact₂
      have hn : n₁ = n₂ := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hsucc := σ.askedNext_succ w lookahead (hnext₁ ▸ hear₁)
          have hmono := σ.askedNext_mono w lookahead r (show n₁ + 1 ≤ n₂ by omega)
          dsimp only at hmono
          rw [hnext₁] at hsucc; rw [hsucc, hnext₂] at hmono; omega
        · have hsucc := σ.askedNext_succ w lookahead (hnext₂ ▸ hear₂)
          have hmono := σ.askedNext_mono w lookahead r (show n₂ + 1 ≤ n₁ by omega)
          dsimp only at hmono
          rw [hnext₂] at hsucc; rw [hsucc, hnext₁] at hmono; omega
      subst hn
      dsimp only [σ] at hact₁ hact₂
      rw [solution_append] at hact₁ hact₂
      set m := memoryOf p N M K (w.host r) ((σ.states w lookahead n₁).views (w.host r))
      set outs := (w.speaker r).block b
      set rep := (w.speaker r).reported b
      set rd := (w.clock (w.host r)).read ((w.speaker r).asked b)
      set snap := (evalResult (sync.Sync.step m.syn (toNs rd)) (sync.SyncSnapshot.EMPTY, m.syn)).1
      set r1 := evalResult (receiver.Receiver.apply_sync (m.rcv r) snap) (m.rcv r)
      set plan := (evalResult (receiver.Receiver.cycle r1 (toNs rep)
        (blockDurationNs outs.length p.rate) (natToU32 outs.length)) (emptyPlan, r1)).1
      have hplay_eq : (act p N M K (w.host r) m ⟨rd, .asked r outs rep⟩).plays = planPlays outs plan := by
        unfold act stepHost
        dsimp only
        split_ifs <;> rfl
      rw [hplay_eq] at hact₁ hact₂
      have hsub : y - x = stepToReal plan.step := planPlays_succ_sub outs plan hact₁ hact₂
      have hinv := rcv_modal_inv p N M K (w.host r) ((σ.states w lookahead n₁).views (w.host r)) r
      have hr1_use : r1.use_sync = true ∧ r1.modal_player.regulation = p.regulation := by
        dsimp only [r1]
        unfold receiver.Receiver.apply_sync
        cases snap.valid <;> simp only [↓reduceIte, Bool.false_eq_true, evalResult_eq_of_ok]
        · exact ⟨trivial, hinv.2⟩
        · exact ⟨trivial, hinv.2⟩
      have hcyc := evalResult_of_spec (d := (emptyPlan, r1))
        (receiver_cycle_plan_spec r1 (toNs rep) (blockDurationNs outs.length p.rate)
          (natToU32 outs.length) hr1_use.1)
      have hstep_b : |y - x - 1| ≤ paceBound p.regulation.limit := by
        rw [hsub]
        unfold stepToReal paceBound
        rw [add_sub_cancel_left, abs_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ) ^ 64 by positivity)]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [hr1_use.2] at hcyc
        have hlo : -(Unisono.Player.reachOf p.regulation.limit : ℝ) ≤ (plan.step.offset.val : ℝ) := by
          exact_mod_cast hcyc.1
        have hhi : (plan.step.offset.val : ℝ) ≤ (Unisono.Player.reachOf p.regulation.limit : ℝ) := by
          exact_mod_cast hcyc.2.1
        exact abs_le.mpr ⟨hlo, hhi⟩
      exact speed_bound_of_step w B hw (paceBound_nonneg _) (paceBound_lt_one _) hpk hpk1 hstep_b hv

/-- **Block-boundary speed safety of `Core.solution`:**
across two adjacent non-empty plans `plan_b` (for block `b`, `n_b = outputs_b.length ≤ 2^32 - 1`,
`Position.advance` did not overflow `U64.MAX`) and `plan_next` (planned from
`m_next` continuing with `running = true` and `position = next`, i.e., no
intervening `stop()`):
* if `plan_next.jumped = false`, the boundary step satisfies
  `|y - x - 1| ≤ paceBound limit` (exact continuation from `plan_b.step`);
* if `plan_next.jumped = true` and `jump ≥ 3`, then `¬ (x < y ∧ y < x + 2)`
  so `World.speed` treats the boundary as a discontinuity (`none`), not a
  speed violation. -/
theorem boundary_step_safe
    (plan_b plan_next : player.Plan) (m_next : player.ModalPlayer) (next : timing.Position)
    (n_b : ℕ) (hnb_pos : 0 < n_b) (hnb_eq : plan_b.frames.val = n_b)
    (hstep_b : -Unisono.Player.reachOf m_next.regulation.limit ≤ plan_b.step.offset.val
      ∧ plan_b.step.offset.val ≤ Unisono.Player.reachOf m_next.regulation.limit)
    (hadv : timing.Position.advance plan_b.start plan_b.step
      (UScalar.cast .U64 plan_b.frames) = ok (some next))
    (hpos_eq : m_next.position = next)
    (hno_jump : plan_next.jumped = false → plan_next.start = m_next.position)
    (hjump : plan_next.jumped = true →
      (m_next.regulation.jump.val : ℝ) < |posToReal plan_next.start - posToReal m_next.position|)
    (hjump3 : 3 ≤ m_next.regulation.jump.val) :
    let x := posToReal plan_b.start + ((n_b - 1 : ℕ) : ℝ) * stepToReal plan_b.step
    let y := posToReal plan_next.start
    (x < y ∧ y < x + 2) → |y - x - 1| ≤ paceBound m_next.regulation.limit := by
  intro x y hcont
  have hnext_r := posToReal_advance plan_b.start plan_b.step (UScalar.cast .U64 plan_b.frames) next hadv
  have hcast_val : (UScalar.cast .U64 plan_b.frames).val = n_b := by
    rw [U32.cast_U64_val, hnb_eq]
  rw [hcast_val] at hnext_r
  have hx_next : posToReal next = x + stepToReal plan_b.step := by
    dsimp only [x]
    rw [hnext_r]
    have h1 : (n_b : ℝ) = ((n_b - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (Nat.sub_add_cancel hnb_pos).symm
    rw [h1]; ring
  have hstep_bound : |stepToReal plan_b.step - 1| ≤ paceBound m_next.regulation.limit := by
    unfold stepToReal paceBound
    rw [add_sub_cancel_left, abs_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ) ^ 64 by positivity)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hlo : -(Unisono.Player.reachOf m_next.regulation.limit : ℝ) ≤ (plan_b.step.offset.val : ℝ) := by
      exact_mod_cast hstep_b.1
    have hhi : (plan_b.step.offset.val : ℝ) ≤ (Unisono.Player.reachOf m_next.regulation.limit : ℝ) := by
      exact_mod_cast hstep_b.2
    exact abs_le.mpr ⟨hlo, hhi⟩
  cases hj : plan_next.jumped with
  | false =>
    have hy_eq : y = posToReal next := by
      dsimp only [y]; rw [hno_jump hj, hpos_eq]
    rw [hy_eq, hx_next]
    simpa [add_sub_cancel_left] using hstep_bound
  | true =>
    exfalso
    have hgt := hjump hj
    rw [hpos_eq, hx_next] at hgt
    have h3 : (3 : ℝ) ≤ (m_next.regulation.jump.val : ℝ) := by exact_mod_cast hjump3
    have hp3 := paceBound_le_three_thousandths m_next.regulation.limit
    have hst := abs_le.mp (hstep_bound.trans hp3)
    have hdist : |y - (x + stepToReal plan_b.step)| > 3 := lt_of_le_of_lt h3 hgt
    rcases lt_or_ge (y - (x + stepToReal plan_b.step)) 0 with hneg | hnn
    · rw [abs_of_neg hneg] at hdist; linarith [hcont.1, hst.2]
    · rw [abs_of_nonneg hnn] at hdist; linarith [hcont.2, hst.1]

/-! ## 7. Exact recovery and zero-cost playback on `IdealConstantWorld.Symmetric` -/

/-- **Exact 4-timestamp NTP recovery on `IdealConstantWorld.Symmetric`:**
within the 64-bit nanosecond horizon (`|t1_ns|, |d_ns|, |Δc_ns| ≤ 2^59`),
`min_rtt.ntp_exchange` recovers the exact clock offset `Δc_ns` and exact RTT
`2 * d_ns`. -/
theorem ideal_ntp_exchange_exact {H : Type} {R : ℕ}
    {m : IdealConstantWorld H R} {w : World H R}
    (hw : m.Holds w) (hsym : m.Symmetric)
    (h : H) (t_send : Time)
    (t1_ns d_ns Δc_ns : ℤ)
    (hd_pos : 0 < d_ns)
    (ht1_b : |t1_ns| ≤ 2 ^ 59) (hd_b : |d_ns| ≤ 2 ^ 59) (hΔ_b : |Δc_ns| ≤ 2 ^ 59)
    (ht1_eq : (w.clock h).read t_send = (t1_ns : ℝ) / (10 ^ 9 : ℝ))
    (hd_eq : m.delay h w.sender = (d_ns : ℝ) / (10 ^ 9 : ℝ))
    (hΔ_eq : (w.clock w.sender).read t_send - (w.clock h).read t_send = (Δc_ns : ℝ) / (10 ^ 9 : ℝ))
    (seq : Std.U64) :
    let t1 := toNs ((w.clock h).read t_send)
    let t2 := toNs ((w.clock w.sender).read (t_send + m.delay h w.sender))
    let t4 := toNs ((w.clock h).read (t_send + m.delay h w.sender + m.delay w.sender h))
    let ex : min_rtt.Exchange := { id := seq, t1 := t1, t2 := t2, t3 := t2, t4 := t4 }
    ∃ s, min_rtt.ntp_exchange ex = ok (some s)
      ∧ s.offset_ns.val = Δc_ns
      ∧ s.rtt_ns.val = 2 * d_ns := by
  obtain ⟨c₀_h, hc_h⟩ := hw.clocks h
  obtain ⟨c₀_s, hc_s⟩ := hw.clocks w.sender
  have hΔ_c : c₀_s - c₀_h = (Δc_ns : ℝ) / (10 ^ 9 : ℝ) := by
    have := hΔ_eq
    rw [hc_s t_send, hc_h t_send] at this
    linarith
  have ht1_b' := abs_le.mp ht1_b
  have hd_b' := abs_le.mp hd_b
  have hΔ_b' := abs_le.mp hΔ_b
  have ht1_val : (toNs ((w.clock h).read t_send)).val = t1_ns := by
    rw [ht1_eq]; exact toNs_of_int (by omega) (by omega)
  have ht2_real : (w.clock w.sender).read (t_send + m.delay h w.sender) =
      ((t1_ns + d_ns + Δc_ns : ℤ) : ℝ) / (10 ^ 9 : ℝ) := by
    rw [hc_s]
    have h1 : t_send + c₀_h = (t1_ns : ℝ) / (10 ^ 9 : ℝ) := by rw [← hc_h t_send, ht1_eq]
    push_cast
    linarith [h1, hd_eq, hΔ_c]
  have ht2_val : (toNs ((w.clock w.sender).read (t_send + m.delay h w.sender))).val =
      t1_ns + d_ns + Δc_ns := by
    rw [ht2_real]; exact toNs_of_int (by omega) (by omega)
  have ht4_real : (w.clock h).read (t_send + m.delay h w.sender + m.delay w.sender h) =
      ((t1_ns + 2 * d_ns : ℤ) : ℝ) / (10 ^ 9 : ℝ) := by
    rw [hc_h, hsym w.sender h]
    have h1 : t_send + c₀_h = (t1_ns : ℝ) / (10 ^ 9 : ℝ) := by rw [← hc_h t_send, ht1_eq]
    push_cast
    linarith [h1, hd_eq]
  have ht4_val : (toNs ((w.clock h).read (t_send + m.delay h w.sender + m.delay w.sender h))).val =
      t1_ns + 2 * d_ns := by
    rw [ht4_real]; exact toNs_of_int (by omega) (by omega)
  let t1 := toNs ((w.clock h).read t_send)
  let t2 := toNs ((w.clock w.sender).read (t_send + m.delay h w.sender))
  let t4 := toNs ((w.clock h).read (t_send + m.delay h w.sender + m.delay w.sender h))
  let ex : min_rtt.Exchange := { id := seq, t1 := t1, t2 := t2, t3 := t2, t4 := t4 }
  obtain ⟨o, ho_eq, hspec⟩ := exists_ok_of_spec (Unisono.MinRtt.ntp_exchange_spec ex)
  obtain ⟨-, hpos⟩ := hspec
  have hproc : 0 ≤ ex.t3.val - ex.t2.val := by simp [ex]
  have hrtt : 0 ≤ (ex.t4.val - ex.t1.val) - (ex.t3.val - ex.t2.val) := by
    change 0 ≤ (t4.val - t1.val) - (t2.val - t2.val)
    rw [ht4_val, ht1_val]; omega
  obtain ⟨s, hs_eq, _, hsrtt, _, hsoff, _⟩ := hpos hproc hrtt
  refine ⟨s, by rw [ho_eq, hs_eq], ?_, ?_⟩
  · change s.offset_ns.val = Unisono.Fixed.clamp64 (((t2.val - t1.val) + (t2.val - t4.val)) / 2) at hsoff
    rw [hsoff, ht1_val, ht2_val, ht4_val]
    have hsum : (t1_ns + d_ns + Δc_ns - t1_ns) + (t1_ns + d_ns + Δc_ns - (t1_ns + 2 * d_ns)) =
        2 * Δc_ns := by ring
    rw [hsum, Int.mul_ediv_cancel_left Δc_ns (by decide)]
    unfold Unisono.Fixed.clamp64; omega
  · change s.rtt_ns.val = Unisono.Fixed.clamp64 ((t4.val - t1.val) - (t2.val - t2.val)) at hsrtt
    rw [hsrtt, ht1_val, ht4_val]
    unfold Unisono.Fixed.clamp64; omega

/-- **Exact Kalman + `SyncSnapshot.sender_time` mapping on constant-offset clocks:**
given a zero-residual, zero-frequency anchored `KalmanFilter` at `base_offset_ns = Δc`,
any non-decreasing update at `Δc` preserves the exact fixed point `(Δc, 0)`,
`to_line` exports the exact constant offset line, and `SyncSnapshot.sender_time`
maps every local timestamp `t` (within `|t| + |Δc| ≤ 2^62`) to exact `t + Δc`. -/
theorem ideal_kalman_and_sender_time_exact (k : kalman.KalmanFilter)
    (hanch : k.anchored = true) (ht : k.theta_q16 = 0#i64) (hf : k.freq_q48 = 0#i64)
    (hpsd : Unisono.Kalman.IsPsd k.p00 k.p01 k.p11)
    (t_meas : Std.I64) (var_ns2 : Std.U64)
    (t_local : Std.I64) (hfit : |t_local.val| + |k.base_offset_ns.val| ≤ 2 ^ 62) :
    let (_, k') := evalResult (kalman.KalmanFilter.update k t_meas k.base_offset_ns var_ns2) (false, k)
    ∃ l, kalman.KalmanFilter.to_line k' = ok (some l)
      ∧ let snap : sync.SyncSnapshot :=
          { sync.SyncSnapshot.EMPTY with valid := true, peer_active := false, common_line := l }
        ∃ ts, sync.SyncSnapshot.sender_time snap t_local = ok ts
          ∧ ts.val = t_local.val + k.base_offset_ns.val := by
  obtain ⟨upd, hupd_eq, hupd_spec⟩ := exists_ok_of_spec
    (Unisono.Kalman.update_zero_innovation_fixed_point k t_meas var_ns2 hanch ht hf hpsd)
  change ∃ l, kalman.KalmanFilter.to_line (evalResult _ (false, k)).2 = ok (some l) ∧ _
  rw [hupd_eq, evalResult_eq_of_ok]
  obtain ⟨ha', hbase', ht', hf', _⟩ := hupd_spec
  obtain ⟨ol, hol_eq, hol_spec⟩ := exists_ok_of_spec
    (Unisono.Kalman.to_line_zero_fixed_point upd.2 ha' ht' hf')
  rw [hol_spec] at hol_eq
  refine ⟨{ time := upd.2.last_time_ns, value := upd.2.base_offset_ns,
            rise := 0#i64, run := kalman.LINE_RUN }, hol_eq, ?_⟩
  dsimp only
  set l : relation.Line := { time := upd.2.last_time_ns, value := upd.2.base_offset_ns,
                             rise := 0#i64, run := kalman.LINE_RUN }
  set snap : sync.SyncSnapshot :=
    { sync.SyncSnapshot.EMPTY with valid := true, peer_active := false, common_line := l }
  have heval : relation.Line.eval l t_local ⦃ v => v = k.base_offset_ns ⦄ := by
    have hrun_pos : 0 < l.run.val := by
      change (0 : ℤ) < kalman.LINE_RUN.val
      unfold kalman.LINE_RUN; decide
    have hsp := Unisono.Relation.eval_spec l t_local
    apply WP.spec_mono hsp
    intro v hv
    apply IScalar.eq_of_val_eq
    have hrise0 : l.rise.val = 0 := rfl
    rw [hv.1 hrun_pos, hrise0, zero_mul, Int.zero_ediv, add_zero]
    dsimp only [l]
    rw [hbase']
    have hb := k.base_offset_ns.hBounds
    change -2 ^ 63 ≤ k.base_offset_ns.val ∧ k.base_offset_ns.val < 2 ^ 63 at hb
    unfold Unisono.Fixed.clamp64; omega
  have hst : sync.SyncSnapshot.sender_time snap t_local ⦃ ts =>
      ts.val = t_local.val + k.base_offset_ns.val ⦄ := by
    unfold sync.SyncSnapshot.sender_time
    simp only [snap, ↓reduceIte, Bool.false_eq_true, bind_ok]
    step with heval as ⟨i, hi⟩; subst hi
    step as ⟨com, hcom⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step with Unisono.Fixed.saturate_spec i3 as ⟨ts, hts⟩
    have hcomv : com.val = k.base_offset_ns.val := by rw [hcom, I64.cast_I128_val]
    have hi1v : i1.val = t_local.val := by rw [hi1, I64.cast_I128_val]
    have hfit' : -2 ^ 62 ≤ t_local.val ∧ t_local.val ≤ 2 ^ 62
        ∧ -2 ^ 62 ≤ k.base_offset_ns.val ∧ k.base_offset_ns.val ≤ 2 ^ 62 := by
      have h1 := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg _)) hfit)
      have h2 := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg _)) hfit)
      exact ⟨h1.1, h1.2, h2.1, h2.2⟩
    have hi2v : i2.val = t_local.val := by
      rw [hi2, I128.saturating_add_val, hi1v]
      change max (-2 ^ 127) (min (2 ^ 127 - 1) (t_local.val + 0)) = t_local.val
      omega
    have hi3v : i3.val = t_local.val + k.base_offset_ns.val := by
      rw [hi3, I128.saturating_add_val, hi2v, hcomv]
      omega
    rw [hts, hi3v]
    unfold Unisono.Fixed.clamp64
    have habs : |t_local.val + k.base_offset_ns.val| ≤ 2 ^ 62 :=
      le_trans (abs_add_le _ _) hfit
    have habs' := abs_le.mp habs
    omega
  obtain ⟨ts, hts_eq, hts_val⟩ := exists_ok_of_spec hst
  exact ⟨ts, hts_eq, hts_val⟩

/-- Helper: `step_for_limit` returns exact `timing.Step.UNITY` whenever
`wanted = 0` and `scheduled = frames * 2^32` (with `0 < frames < 2^31`). -/
private theorem step_for_limit_unity (limit : Std.U32) (frames : Std.U32) (scheduled : Std.I64)
    (hfr_pos : 0 < frames.val) (hfr_lt : frames.val < 2 ^ 31)
    (hsched : scheduled.val = (frames.val : ℤ) * 2 ^ 32) :
    player.step_for_limit limit 0#i64 frames scheduled = ok timing.Step.UNITY := by
  have hspec : player.step_for_limit limit 0#i64 frames scheduled ⦃ s => s = timing.Step.UNITY ⦄ := by
    have hb := Unisono.Player.reachOf_bounds limit
    have h16 : player.SIXTEEN_BITS.val = 2 ^ 16 := by unfold player.SIXTEEN_BITS; decide
    have h48 : player.FRAME_IN_CORRECTIONS.val = 2 ^ 48 := by
      unfold player.FRAME_IN_CORRECTIONS; decide
    unfold player.step_for_limit
    step as ⟨reach1, hreach⟩
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    step as ⟨beyond, hbey⟩
    have hiv : i.val = (frames.val : ℤ) * 2 ^ 32 := by rw [hi, I64.cast_I128_val, hsched]
    have hi1v : i1.val = (frames.val : ℤ) * 2 ^ 48 := by
      rw [hi1, I128.wrapping_mul_val _ _ (by rw [hiv, h16]; omega), hiv, h16]; ring
    have hi2v : i2.val = 0 := by rw [hi2]; exact I64.cast_I128_val 0#i64
    have hi3v : i3.val = (frames.val : ℤ) * 2 ^ 48 := by
      rw [hi3, I128.wrapping_add_val _ _ (by rw [hi1v, hi2v]; omega), hi1v, hi2v, add_zero]
    have hi4v : i4.val = (frames.val : ℤ) := by rw [hi4, U32.hcast_I128_val]
    have hi5v : i5.val = (frames.val : ℤ) * 2 ^ 48 := by
      rw [hi5, I128.wrapping_mul_val _ _ (by rw [hi4v, h48]; omega), hi4v, h48]
    have hbeyv : beyond.val = 0 := by
      rw [hbey, I128.wrapping_sub_val _ _ (by rw [hi3v, hi5v]; omega), hi3v, hi5v, sub_self]
    step as ⟨i6, hi6⟩
    have hi6v : i6.val = 0 := by
      rw [hi6, I128.wrapping_mul_val _ _ (by rw [hbeyv, h16]; omega), hbeyv, zero_mul]
    step as ⟨i7, hi7⟩
    have hi7v : i7.val = (frames.val : ℤ) := by rw [hi7, U32.hcast_I64_val]
    step with Unisono.Fixed.div_floor_spec i6 i7 as ⟨st, hst_pos, _⟩
    have hstv : st.val = 0 := by rw [hst_pos (by omega), hi6v, Int.zero_ediv]
    have hcl0 : player.clamp_sym_i128 st reach1 ⦃ r => r.val = 0 ⦄ := by
      unfold player.clamp_sym_i128
      have h0 : (0#i128).val = 0 := rfl
      step as ⟨lo, hlo⟩
      have hlov : lo.val = -reach1.val := by
        rw [hlo, I128.wrapping_sub_val _ _ (by rw [h0, hreach]; omega), h0]
        omega
      split
      · rename_i hgt
        have : reach1.val < st.val := by scalar_tac
        omega
      · split
        · rename_i hlt
          have : st.val < lo.val := by scalar_tac
          omega
        · rw [WP.spec_ok]; exact hstv
    step with hcl0 as ⟨i8, hi8⟩
    step with Unisono.Fixed.saturate_spec i8 as ⟨i9, hi9⟩
    have hi9v : i9.val = 0 := by rw [hi9, hi8]; unfold Unisono.Fixed.clamp64; simp
    step with Unisono.Player.step_clamped_spec i9 as ⟨s, hs, _, _⟩
    have hso : s.offset = 0#i64 := by
      apply IScalar.eq_of_val_eq
      rw [hs, hi9v]; norm_num
    cases s
    simp only at hso
    subst hso
    unfold timing.Step.UNITY
    rfl
  obtain ⟨s, hs_eq, hs_val⟩ := exists_ok_of_spec hspec
  rw [hs_eq, hs_val]

/-- **Exact unity step of `ModalPlayer.cycle` in Star mode on an ideal nominal
schedule:** when `timing.distance now later = ok (frames * 2^32)` (`0 < frames < 2^31`)
and the player is either starting (`running = false`) or already on-target
(`position = now`, `diff_pace = 0`, `slope = schedule.level_slope`, `was_peer = false`),
`ModalPlayer.cycle` produces **`plan.step = timing.Step.UNITY`** (`offset = 0`)
and keeps `diff_pace = 0`. -/
theorem ideal_modal_cycle_unity (m : player.ModalPlayer) (now later : timing.Position)
    (frames : Std.U32) (duration : Std.I64) (schedule : timing.Schedule) (epoch : Std.U32)
    (com_now com_then : Std.I64)
    (hfr_pos : 0 < frames.val) (hfr_lt : frames.val < 2 ^ 31)
    (hdist : ∃ sc : Std.I64, timing.distance now later = ok sc ∧ sc.val = (frames.val : ℤ) * 2 ^ 32)
    (hstate : m.running = false ∨
      (m.running = true ∧ m.position = now ∧ m.diff_pace = 0#i64
       ∧ m.slope = schedule.level_slope ∧ m.was_peer = false)) :
    player.ModalPlayer.cycle m now later frames duration schedule false epoch com_now com_then
      ⦃ out => out.1.frames = frames ∧ out.1.start = now
        ∧ out.1.step = timing.Step.UNITY ∧ out.2.running = true
        ∧ out.2.diff_pace = 0#i64 ∧ out.2.slope = schedule.level_slope
        ∧ out.2.was_peer = false ⦄ := by
  obtain ⟨sc, hsc_eq, hsc_val⟩ := hdist
  have hfr_ne0 : ¬ (frames = 0#u32) := by
    intro h0; subst h0; simp at hfr_pos
  have hsc_not_le0 : ¬ (sc <= 0#i64) := by
    intro hle
    have : sc.val ≤ 0 := by scalar_tac
    omega
  have hstep_u := step_for_limit_unity m.regulation.limit frames sc hfr_pos hfr_lt hsc_val
  unfold player.ModalPlayer.cycle
  rw [hsc_eq, bind_ok]
  simp only [hfr_ne0, hsc_not_le0, ↓reduceIte]
  rcases hstate with hnotrun | ⟨hrun, hpos, hpace, hslope, hwp⟩
  · have hj : player.ModalPlayer.jumps m now = ok true := by
      unfold player.ModalPlayer.jumps; simp [hnotrun]
    rw [hj, bind_ok]
    simp only [↓reduceIte]
    rw [hstep_u, bind_ok]
    simp only [Bool.false_eq_true, ↓reduceIte, timing.Step.impl.offset, timing.Step.UNITY,
      lift, bind_ok]
    step as ⟨o⟩
    cases o <;> simp
  · have hj : player.ModalPlayer.jumps m now = ok false := by
      unfold player.ModalPlayer.jumps
      simp only [hrun, hpos, ↓reduceIte]
      have hspec : (do
          let current ← timing.Position.units now
          let target ← timing.Position.units now
          let gap ← if target >= current
            then ok (core.num.U128.wrapping_sub target current)
            else ok (core.num.U128.wrapping_sub current target)
          let i ← lift (UScalar.cast .U128 m.regulation.jump)
          let limit ← lift (core.num.U128.wrapping_shl i 64#u32)
          ok (decide (gap > limit))) ⦃ b => b = false ⦄ := by
        step with position_units_val now as ⟨u1, hu1⟩
        step with position_units_val now as ⟨u2, hu2⟩
        have hueq : u2 = u1 := UScalar.eq_of_val_eq (hu2.trans hu1.symm)
        rw [hueq]
        have hge : u1 >= u1 := Nat.le_refl _
        simp only [hge, ↓reduceIte, bind_ok]
        have hsub0 : (core.num.U128.wrapping_sub u1 u1).val = 0 := by
          rw [u128_wrapping_sub_val u1 u1 (Nat.le_refl _), Nat.sub_self]
        step as ⟨i, _⟩
        step as ⟨lim, _⟩
        have hng : ¬ (lim.val < (core.num.U128.wrapping_sub u1 u1).val) := by omega
        exact decide_eq_false hng
      obtain ⟨b, hb_eq, hb_val⟩ := exists_ok_of_spec hspec
      rw [hb_eq, hb_val]
    rw [hj, bind_ok]
    simp only [Bool.false_eq_true, ↓reduceIte, hwp, hpos, hpace, hslope, bind_ok]
    have hbeh0 : timing.distance now now = ok 0#i64 := by
      have hsp : timing.distance now now ⦃ d => d = 0#i64 ⦄ := by
        unfold timing.distance
        step as ⟨i, hi⟩
        step as ⟨i1, hi1⟩
        step as ⟨fr, hfr⟩
        step as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        step as ⟨i4, hi4⟩
        step as ⟨i5, hi5⟩
        step as ⟨frac, hfrac⟩
        step as ⟨i6, hi6⟩
        step as ⟨i7, hi7⟩
        step with Unisono.Fixed.saturate_spec i7 as ⟨d, hd⟩
        have hfrv : fr.val = 0 := by
          rw [hfr, I128.wrapping_sub_val _ _ ⟨by rw [hi, hi1]; omega, by rw [hi, hi1]; omega⟩,
            hi, hi1, sub_self]
        have hfracv : frac.val = 0 := by
          rw [hfrac, I128.wrapping_sub_val _ _ ⟨by rw [hi3, hi5, hi2, hi4]; omega,
            by rw [hi3, hi5, hi2, hi4]; omega⟩, hi3, hi5, hi2, hi4, sub_self]
        have hi6v : i6.val = 0 := by
          rw [hi6, I128.wrapping_shl_val _ _ (by decide) ⟨by rw [hfrv]; norm_num, by rw [hfrv]; norm_num⟩, hfrv]
          norm_num
        have hi7v : i7.val = 0 := by
          rw [hi7, I128.wrapping_add_val _ _ ⟨by rw [hi6v, hfracv]; omega,
            by rw [hi6v, hfracv]; omega⟩, hi6v, hfracv, add_zero]
        apply IScalar.eq_of_val_eq
        rw [hd, hi7v]; unfold Unisono.Fixed.clamp64; simp
      obtain ⟨d, hd_eq, hd_val⟩ := exists_ok_of_spec hsp
      rw [hd_eq, hd_val]
    rw [hbeh0]
    simp only [bind_ok]
    have h48 : player.FRAME_IN_CORRECTIONS.val = 2 ^ 48 := by
      unfold player.FRAME_IN_CORRECTIONS; decide
    have h16 : player.SIXTEEN_BITS.val = 2 ^ 16 := by unfold player.SIXTEEN_BITS; decide
    step as ⟨i3, hi3⟩; step as ⟨i4, hi4⟩; step as ⟨i5, hi5⟩; step as ⟨i6, hi6⟩
    step as ⟨i7, hi7⟩; step as ⟨i8, hi8⟩; step as ⟨read, hread⟩
    have hi3v : i3.val = (frames.val : ℤ) := by rw [hi3, U32.hcast_I128_val]
    have hi4v : i4.val = (frames.val : ℤ) * 2 ^ 48 := by
      rw [hi4, I128.wrapping_mul_val _ _ (by rw [hi3v, h48]; omega), hi3v, h48]
    have hi5v : i5.val = (frames.val : ℤ) := by rw [hi5, U32.hcast_I128_val]
    have hi6v : i6.val = 0 := by rw [hi6]; exact I64.cast_I128_val 0#i64
    have hi7v : i7.val = 0 := by
      rw [hi7, I128.wrapping_mul_val _ _ (by rw [hi5v, hi6v]; omega), hi6v, mul_zero]
    have hi8v : i8.val = 0 := by
      rw [hi8, I128.wrapping_shr_val _ _ (by decide), hi7v]; norm_num
    have hreadv : read.val = (frames.val : ℤ) * 2 ^ 48 := by
      rw [hread, I128.wrapping_add_val _ _ (by rw [hi4v, hi8v]; omega), hi4v, hi8v, add_zero]
    have hcar : player.carry_slope read schedule.level_slope schedule.level_slope = ok read := by
      unfold player.carry_slope; simp [lift]
    rw [hcar, bind_ok]
    step as ⟨i9, hi9⟩; step as ⟨i10, hi10⟩; step as ⟨i11, hi11⟩
    have hi9v : i9.val = (frames.val : ℤ) * 2 ^ 32 := by rw [hi9, I64.cast_I128_val, hsc_val]
    have hi10v : i10.val = (frames.val : ℤ) * 2 ^ 48 := by
      rw [hi10, I128.wrapping_mul_val _ _ (by rw [hi9v, h16]; omega), hi9v, h16]; ring
    have hi11v : i11.val = 0 := by
      rw [hi11, I128.wrapping_sub_val _ _ (by rw [hreadv, hi10v]; omega), hreadv, hi10v, sub_self]
    step with Unisono.Fixed.saturate_spec i11 as ⟨ah, hah⟩
    have hah0 : ah = 0#i64 := by
      apply IScalar.eq_of_val_eq; rw [hah, hi11v]; unfold Unisono.Fixed.clamp64; simp
    subst hah0
    have hreg0 : player.regulate_for m.regulation.star_gain 0#i64 0#i64 duration = ok 0#i64 := by
      have hsp : player.regulate_for m.regulation.star_gain 0#i64 0#i64 duration ⦃ r => r = 0#i64 ⦄ := by
        unfold player.regulate_for
        step as ⟨g⟩
        have hz : (IScalar.cast .I128 0#i64).val = 0 := I64.cast_I128_val 0#i64
        have hm1 : (core.num.I128.wrapping_mul g.ahead (IScalar.cast .I128 0#i64)).val = 0 := by
          rw [I128.wrapping_mul_val _ _ (by rw [hz]; norm_num), hz, mul_zero]
        have hm2 : (core.num.I128.wrapping_mul g.behind (IScalar.cast .I128 0#i64)).val = 0 := by
          rw [I128.wrapping_mul_val _ _ (by rw [hz]; norm_num), hz, mul_zero]
        have hs1 : (core.num.I128.wrapping_shr
            (core.num.I128.wrapping_mul g.ahead (IScalar.cast .I128 0#i64)) 32#u32).val = 0 := by
          rw [I128.wrapping_shr_val _ _ (by decide), hm1]; norm_num
        have hs2 : (core.num.I128.wrapping_shr
            (core.num.I128.wrapping_mul g.behind (IScalar.cast .I128 0#i64)) 32#u32).val = 0 := by
          rw [I128.wrapping_shr_val _ _ (by decide), hm2]; norm_num
        step as ⟨a1, ha1⟩; step as ⟨a2, ha2⟩; step as ⟨kept, hkept⟩
        step as ⟨a3, ha3⟩; step as ⟨a4, ha4⟩; step as ⟨added, hadded⟩
        step as ⟨a5, ha5⟩
        step with Unisono.Fixed.saturate_spec a5 as ⟨r, hr⟩
        apply IScalar.eq_of_val_eq
        have ha5v : a5.val = 0 := by
          rw [ha5, I128.wrapping_add_val _ _ (by
            rw [hkept, hadded, ha2, ha4, ha1, ha3, hs1, hs2]; norm_num),
            hkept, hadded, ha2, ha4, ha1, ha3, hs1, hs2]
          norm_num
        rw [hr, ha5v]; unfold Unisono.Fixed.clamp64; simp
      obtain ⟨r, hr_eq, hr_val⟩ := exists_ok_of_spec hsp
      rw [hr_eq, hr_val]
    rw [hreg0, bind_ok, hstep_u, bind_ok]
    simp only [timing.Step.impl.offset, timing.Step.UNITY, lift, bind_ok]
    step as ⟨o⟩
    cases o <;> simp [hrun]

set_option maxHeartbeats 800000 in
/-- **Exact zero-cost objectives on `IdealConstantWorld`:**
when every speaker `r` plays from output sample `K` onward on the exact
unity-step trajectory `plays r k = some (t_r0 * m.rate + k)` matching
`w.captured (plays r k) = (w.speaker r).out k - m.targetLatency` (the exact
trajectory produced by `ideal_ntp_exchange_exact` +
`ideal_kalman_and_sender_time_exact` + `ideal_modal_cycle_unity`), then all six
`Unisono.Spec.Objectives` attain their ideal values:
`sync = 0`, `tracking = 0`, `roughness = 0`, `missed = 0`,
`discontinuities = 0`, and `meanLatency ≤ ENNReal.ofReal m.targetLatency`. -/
theorem ideal_zero_cost_objectives {H : Type} {R : ℕ}
    {m : IdealConstantWorld H R} {w : World H R} (hw : m.Holds w)
    (plays : Fin R → ℕ → Option ℝ) (K : ℕ)
    (htraj : ∀ r k, K ≤ k →
      ∃ x, plays r k = some x
        ∧ plays r (k + 1) = some (x + 1)
        ∧ w.captured x = (w.speaker r).out k - m.targetLatency) :
    w.sync plays = 0
    ∧ w.tracking plays = 0
    ∧ w.roughness plays = 0
    ∧ w.missed plays = 0
    ∧ w.discontinuities plays = 0
    ∧ w.meanLatency plays ≤ ENNReal.ofReal m.targetLatency := by
  have hpal : w.PlaysAtLatency plays m.targetLatency 0 K := by
    intro r k hk
    obtain ⟨x, hx, hx1, hcap⟩ := htraj r k hk
    exact ⟨⟨x, x + 1, hx, hx1, by linarith, by linarith⟩, x, hx, by simp [hcap]⟩
  have hmissed : w.missed plays = 0 := missed_eq_zero w plays hpal
  have hdisc : w.discontinuities plays = 0 := discontinuities_eq_zero w plays hpal
  have hspeed1 : ∀ r k, K ≤ k → w.speed plays r k = some 1 := by
    intro r k hk
    obtain ⟨x, hx, hx1, hcap⟩ := htraj r k hk
    obtain ⟨x', hx', _, hcap1⟩ := htraj r (k + 1) (Nat.le_succ_of_le hk)
    rw [hx1, Option.some.injEq] at hx'
    subst hx'
    unfold World.speed
    rw [hx, hx1]
    simp only [lt_add_iff_pos_right, zero_lt_one, add_lt_add_iff_left, Nat.one_lt_ofNat,
      and_self, ↓reduceIte, Option.some.injEq]
    rw [hcap, hcap1]
    have hpos : 0 < (w.speaker r).out (k + 1) - (w.speaker r).out k :=
      sub_pos.mpr ((w.speaker r).out_strictMono (Nat.lt_succ_self k))
    have hnum : ((w.speaker r).out (k + 1) - m.targetLatency) -
        ((w.speaker r).out k - m.targetLatency) =
        (w.speaker r).out (k + 1) - (w.speaker r).out k := by ring
    rw [hnum, div_self hpos.ne']
  have hrough : w.roughness plays = 0 := by
    classical
    have hz : ∀ r k, K < k → w.roughnessCost plays r k = 0 := by
      intro r k hk
      unfold World.roughnessCost
      rw [hspeed1 r k hk.le]
      cases hnc : nextContinuous (plays r) k with
      | none => rfl
      | some j =>
        have hkj : k < j := by
          unfold nextContinuous at hnc
          split_ifs at hnc with hex
          injection hnc with hj; rw [← hj]; exact (Nat.find_spec hex).1
        dsimp only
        rw [hspeed1 r j (by omega)]
        simp
    refine le_antisymm ?_ zero_le
    refine longRun_le ?_ 0 fun T _ => by simpa using w.accruedOutputs_le _ K hz T
    rcases Nat.eq_zero_or_pos R with hR | hR
    · subst hR; simp
    · apply ENNReal.mul_ne_top (by simpa using hR.ne')
      exact ENNReal.sum_ne_top.mpr fun r _ => ENNReal.sum_ne_top.mpr fun k _ => by
        unfold World.roughnessCost
        cases w.speed plays r k <;> simp
        cases nextContinuous (plays r) k <;> simp
        cases w.speed plays r _ <;> simp
  -- Exact playTime for every frame not covered before K: playTime = capture n + targetLatency.
  obtain ⟨N, hN⟩ := exists_frame_beyond plays K
  have hplay_exact : ∀ r n, N ≤ n → ∀ t, w.playTime plays r n = some t →
      t = w.source.capture n + m.targetLatency := by
    classical
    intro r n hn t ht
    unfold World.playTime Spec.playTime at ht
    split_ifs at ht with hex
    set k := Nat.find hex
    have hcov : Covers (plays r) k n := Nat.find_spec hex
    have hkK : K ≤ k := by
      by_contra hlt; exact hN r k n (not_le.mp hlt) hn hcov
    obtain ⟨x, y, hx, hy, hxy, hyx, hxn, hny⟩ := hcov
    change (match plays r k, plays r (k + 1) with
      | some x, some y => some ((w.speaker r).out k + ((n : ℝ) - x) / (y - x) *
          ((w.speaker r).out (k + 1) - (w.speaker r).out k))
      | _, _ => none) = some t at ht
    rw [hx, hy] at ht
    injection ht with ht
    obtain ⟨x0, hx0, hx01, hcap0⟩ := htraj r k hkK
    rw [hx, Option.some.injEq] at hx0; subst hx0
    rw [hy, Option.some.injEq] at hx01; subst hx01
    obtain ⟨tc0, htc⟩ := hw.capture
    obtain ⟨to0, hto⟩ := hw.speaker_out r
    have hrate : 0 < m.rate := m.rate_pos
    have hcap_all : w.captured x = tc0 + x / m.rate := by
      unfold World.captured
      rw [htc ⌊x⌋₊, htc (⌊x⌋₊ + 1)]
      push_cast
      have hne : m.rate ≠ 0 := hrate.ne'
      field_simp; ring
    rw [← ht, hto k, hto (k + 1), htc n]
    rw [hcap_all, hto k] at hcap0
    push_cast
    have hne : m.rate ≠ 0 := hrate.ne'
    have h1 : (x + 1 - x) = 1 := by ring
    rw [h1, div_one]
    have h2 : (to0 + ((k : ℝ) + 1) / m.rate) - (to0 + (k : ℝ) / m.rate) = 1 / m.rate := by
      field_simp; ring
    rw [h2]
    linarith [hcap0, show ((n : ℝ) - x) * (1 / m.rate) = (n : ℝ) / m.rate - x / m.rate by ring]
  -- Wait: clean proof of `hcap_all` works without `hx_nn`!
  have hsync : w.sync plays = 0 := by
    have hz : ∀ n, N ≤ n → w.syncCost plays n = 0 := by
      intro n hn
      unfold World.syncCost
      suffices hsum : ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
          w.pairCost plays p.1 p.2 n = 0 by rw [hsum, mul_zero]
      refine Finset.sum_eq_zero fun p _ => ?_
      unfold World.pairCost
      cases h1 : w.playTime plays p.1 n with
      | none => rfl
      | some t1 =>
        cases h2 : w.playTime plays p.2 n with
        | none => rfl
        | some t2 =>
          rw [hplay_exact p.1 n hn t1 h1, hplay_exact p.2 n hn t2 h2]
          simp
    refine le_antisymm ?_ zero_le
    refine longRun_le (C := ∑ n ∈ Finset.range N,
        w.syncCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n))
      ?_ 0 fun T _ => ?_
    · exact ENNReal.sum_ne_top.mpr fun n _ => ENNReal.mul_ne_top
        (by
          unfold World.syncCost
          rcases Nat.eq_zero_or_pos R with hR | hR
          · subst hR; simp
          · apply ENNReal.mul_ne_top (by simpa [pow_two] using hR.ne')
            exact ENNReal.sum_ne_top.mpr fun p _ => by
              unfold World.pairCost
              cases w.playTime plays p.1 n <;> simp
              cases w.playTime plays p.2 n <;> simp)
        ENNReal.ofReal_ne_top
    · simp only [zero_mul, zero_add]
      unfold World.accruedFrames
      rw [tsum_eq_sum (s := Finset.range N)]
      · exact Finset.sum_le_sum fun n _ => by split_ifs <;> simp
      · intro n hn
        simp only [Finset.mem_range, not_lt] at hn
        simp [hz n hn]
  have htrack : w.tracking plays = 0 := by
    have hz : ∀ n, N ≤ n → w.trackingCost plays n = 0 := by
      intro n hn
      unfold World.trackingCost
      suffices hsum : ∑ r : Fin R, w.trackingAt plays r n = 0 by rw [hsum, mul_zero]
      refine Finset.sum_eq_zero fun r _ => ?_
      unfold World.trackingAt World.latency
      cases h1 : w.playTime plays r n with
      | none => rfl
      | some t1 =>
        rw [hplay_exact r n hn t1 h1, hw.target_eq n]
        simp
    refine le_antisymm ?_ zero_le
    refine longRun_le (C := ∑ n ∈ Finset.range N,
        w.trackingCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n))
      ?_ 0 fun T _ => ?_
    · exact ENNReal.sum_ne_top.mpr fun n _ => ENNReal.mul_ne_top
        (average_ne_top fun r => by
          unfold World.trackingAt World.latency
          cases w.playTime plays r n <;> simp)
        ENNReal.ofReal_ne_top
    · simp only [zero_mul, zero_add]
      unfold World.accruedFrames
      rw [tsum_eq_sum (s := Finset.range N)]
      · exact Finset.sum_le_sum fun n _ => by split_ifs <;> simp
      · intro n hn
        simp only [Finset.mem_range, not_lt] at hn
        simp [hz n hn]
  have hlat : w.meanLatency plays ≤ ENNReal.ofReal m.targetLatency := by
    have hbound : ∀ n, N ≤ n → w.latencyCost plays n ≤ ENNReal.ofReal m.targetLatency := by
      intro n hn
      unfold World.latencyCost
      refine average_le fun r => ?_
      unfold World.latencyAt World.latency
      cases h1 : w.playTime plays r n with
      | none => simp
      | some t1 =>
        rw [hplay_exact r n hn t1 h1]
        simp
    refine longRun_le (C := (∑ n ∈ Finset.range N,
        w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n))
        + ENNReal.ofReal m.targetLatency * ENNReal.ofReal (max (-w.source.capture N) 0 + 1 / m.rate))
      ?_ 0 fun T hT => ?_
    · apply ENNReal.add_ne_top.mpr
      constructor
      · exact ENNReal.sum_ne_top.mpr fun n _ => ENNReal.mul_ne_top
          (average_ne_top fun r => by
            unfold World.latencyAt World.latency
            cases w.playTime plays r n <;> simp)
          ENNReal.ofReal_ne_top
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · obtain ⟨tc0, htc⟩ := hw.capture
      have hstep : ∀ n, w.source.capture (n + 1) - w.source.capture n = 1 / m.rate := by
        intro n; rw [htc n, htc (n + 1)]; push_cast; have := m.rate_pos.ne'; field_simp; ring
      have hsplit : w.accruedFrames (w.latencyCost plays) T =
          (∑ n ∈ Finset.range N, if w.source.capture n < T then
            w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
          + ∑' n, if N ≤ n ∧ w.source.capture n < T then
            w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0 := by
        unfold World.accruedFrames
        let g : ℕ → ℝ≥0∞ := fun n => if w.source.capture n < T then
          w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0
        have hsum := ((CompleteLattice.summable (f := fun n => g (n + N))).hasSum.sum_range_add).tsum_eq
        change ∑' n, g n = (∑ n ∈ Finset.range N, g n) + _
        rw [hsum]
        congr 1
        rw [← tsum_eq_tsum_of_ne_zero_bij (i := fun k => (k : ℕ) + N)]
        · intro a b h; exact Subtype.ext (Nat.add_right_cancel h)
        · intro n hn
          have hge : N ≤ n := by
            by_contra hlt; simp only [Function.mem_support, ne_eq] at hn
            have : ¬ (N ≤ n ∧ w.source.capture n < T) := fun h => hlt h.1
            exact hn (by simp [this])
          exact ⟨⟨n - N, by
            simp only [Function.mem_support, ne_eq] at hn ⊢
            have hsub : n - N + N = n := Nat.sub_add_cancel hge
            simpa [g, hsub, hge] using hn⟩, Nat.sub_add_cancel hge⟩
        · intro k
          have hk : N ≤ (k : ℕ) + N := Nat.le_add_left N k
          simp [g, hk]
      rw [hsplit]
      have hhead : (∑ n ∈ Finset.range N, if w.source.capture n < T then
          w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
          ≤ ∑ n ∈ Finset.range N,
            w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) :=
        Finset.sum_le_sum fun n _ => by split_ifs <;> simp
      have htail : (∑' n, if N ≤ n ∧ w.source.capture n < T then
          w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
          ≤ ENNReal.ofReal m.targetLatency * ENNReal.ofReal T
            + ENNReal.ofReal m.targetLatency * ENNReal.ofReal (max (-w.source.capture N) 0 + 1 / m.rate) := by
        -- Count how many `n ≥ N` satisfy `w.source.capture n < T`.
        have hfin_cnt : ∃ M : ℕ, ∀ n, N + M ≤ n → ¬ (w.source.capture n < T) := by
          obtain ⟨M, hM⟩ := exists_nat_gt ((T - w.source.capture N) * m.rate)
          refine ⟨M, fun n hn hlt => ?_⟩
          have hdiff : w.source.capture n - w.source.capture N = ((n - N : ℕ) : ℝ) / m.rate := by
            rw [htc n, htc N]; have hge : N ≤ n := by omega
            rw [Nat.cast_sub hge]; ring
          have hnm : (M : ℝ) ≤ ((n - N : ℕ) : ℝ) := by exact_mod_cast (show M ≤ n - N by omega)
          have hrate := m.rate_pos
          have hlt_div : T - w.source.capture N < (M : ℝ) / m.rate := (lt_div_iff₀ hrate).mpr hM
          have hge_div : (M : ℝ) / m.rate ≤ ((n - N : ℕ) : ℝ) / m.rate :=
            div_le_div_of_nonneg_right hnm hrate.le
          linarith
        obtain ⟨M, hM⟩ := hfin_cnt
        have hle_sum : (∑' n, if N ≤ n ∧ w.source.capture n < T then
            w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
            ≤ ENNReal.ofReal m.targetLatency *
              ∑' n, if N ≤ n ∧ w.source.capture n < T then
                ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0 := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_le_tsum fun n => ?_
          split_ifs with hc
          · exact mul_le_mul_of_nonneg_right (hbound n hc.1) zero_le
          · simp
        refine hle_sum.trans ?_
        rw [← mul_add, ← ENNReal.ofReal_add hT (by
          have : 0 ≤ max (-w.source.capture N) 0 := le_max_right _ _
          have : 0 < 1 / m.rate := div_pos one_pos m.rate_pos
          linarith)]
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        by_cases h0 : w.source.capture N < T
        · -- Let `J` be the first `k` with `T ≤ w.source.capture (N + k)`.
          classical
          have hex_k : ∃ k, T ≤ w.source.capture (N + k) := ⟨M, not_lt.mp (hM (N + M) le_rfl)⟩
          set J := Nat.find hex_k
          have hJ_pos : 0 < J := by
            by_contra h0'; have hJ0 : J = 0 := by omega
            have hspecJ : T ≤ w.source.capture (N + J) := Nat.find_spec hex_k
            rw [hJ0, add_zero] at hspecJ; linarith
          have hJ_prev : w.source.capture (N + (J - 1)) < T := by
            have := Nat.find_min hex_k (show J - 1 < J by omega); linarith
          have hsum_eq : (∑' n, if N ≤ n ∧ w.source.capture n < T then
              ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0) =
              ∑ k ∈ Finset.range J, ENNReal.ofReal (1 / m.rate) := by
            rw [tsum_eq_sum (s := Finset.Ico N (N + J))]
            · rw [Finset.sum_Ico_eq_sum_range]
              refine Finset.sum_congr (by rw [Nat.add_sub_cancel_left]) fun k hk => ?_
              rw [Finset.mem_range] at hk
              have hlt : w.source.capture (N + k) < T := by
                have := Nat.find_min hex_k hk; linarith
              simp [hlt, hstep]
            · intro n hn
              simp only [Finset.mem_Ico, not_and, not_lt] at hn
              by_cases hge : N ≤ n
              · have hnj : N + J ≤ n := hn hge
                have hnotlt : ¬ w.source.capture n < T := by
                  have h1 := Nat.find_spec hex_k
                  have h2 := w.source.capture_strictMono.monotone hnj
                  linarith
                simp [hnotlt]
              · simp [hge]
          rw [hsum_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg J)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hJ_span : (J : ℝ) * (1 / m.rate) =
              (w.source.capture (N + (J - 1)) - w.source.capture N) + 1 / m.rate := by
            rw [htc (N + (J - 1)), htc N]
            have h1 : ((N + (J - 1) : ℕ) : ℝ) - (N : ℝ) = ((J - 1 : ℕ) : ℝ) := by push_cast; ring
            have h2 : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by exact_mod_cast Nat.sub_add_cancel hJ_pos
            have hne := m.rate_pos.ne'
            field_simp; linarith [h1, h2]
          have hmax : -w.source.capture N ≤ max (-w.source.capture N) 0 := le_max_left _ _
          linarith [hJ_span, hJ_prev, hmax]
        · have hzero : (∑' n, if N ≤ n ∧ w.source.capture n < T then
              ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0) = 0 := by
            refine tsum_eq_zero_iff.mpr fun n => ?_
            split_ifs with hc
            · exfalso
              have h1 := w.source.capture_strictMono.monotone hc.1
              linarith
            · rfl
          rw [hzero]; exact zero_le
      calc (∑ n ∈ Finset.range N, if w.source.capture n < T then
              w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
            + (∑' n, if N ≤ n ∧ w.source.capture n < T then
              w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
          ≤ (∑ n ∈ Finset.range N,
              w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n))
            + (ENNReal.ofReal m.targetLatency * ENNReal.ofReal T
               + ENNReal.ofReal m.targetLatency * ENNReal.ofReal (max (-w.source.capture N) 0 + 1 / m.rate)) :=
            add_le_add hhead htail
        _ = ENNReal.ofReal m.targetLatency * ENNReal.ofReal T
            + ((∑ n ∈ Finset.range N,
                w.latencyCost plays n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n))
               + ENNReal.ofReal m.targetLatency * ENNReal.ofReal (max (-w.source.capture N) 0 + 1 / m.rate)) := by
            ring
  exact ⟨hsync, htrack, hrough, hmissed, hdisc, hlat⟩

end Unisono.Solutions.Core
