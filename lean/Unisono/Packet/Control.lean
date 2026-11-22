/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Packet.Wire

/-!
# Control packets: Echo, Request, and Report

Wire layouts and round-trip proofs for `Echo`, `Request`, and `Report`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Packet

/-! ## Echo wire layout and round-trip -/

/-- Exact 32-byte wire layout produced by `write_echo`. -/
theorem write_echo_spec (e : packet.Echo) (bytes : Slice Std.U8)
    (hlen : bytes.val.length = packet.ECHO.val) :
    packet.write_echo e bytes ⦃ out =>
      out.1 = some packet.ECHO
      ∧ out.2.val.length = 32
      ∧ HasLE out.2.val 0 4 packet.MAGIC.val
      ∧ HasLE out.2.val 4 1 packet.VERSION.val
      ∧ HasLE out.2.val 5 1 packet.KIND_ECHO.val
      ∧ HasLE out.2.val 6 2 e.stream.val
      ∧ HasLE out.2.val 8 8 e.receiver.val
      ∧ HasLE out.2.val 16 8 e.sequence.val
      ∧ HasLE out.2.val 24 8 (IScalar.hcast .U64 e.arrival).val ⦄ := by
  have hecho : packet.ECHO.val = 32 := by simp [packet.ECHO]
  have hlen32 : bytes.val.length = 32 := by omega
  unfold packet.write_echo
  have hnotlt : ¬ bytes.len < packet.ECHO := by
    have : bytes.len.val = bytes.val.length := rfl
    scalar_tac
  simp only [hnotlt, ↓reduceIte]
  step with write_spec bytes 0#usize 4#usize packet.MAGIC (by scalar_tac) (by decide)
    as ⟨b0, bs1, hb0, hl1, hm1, _⟩
  step as ⟨iv, hiv⟩
  step with write_spec bs1 4#usize 1#usize iv (by scalar_tac) (by decide)
    as ⟨b1, bs2, hb1, hl2, hv2, ho2⟩
  step as ⟨ik, hik⟩
  step with write_spec bs2 5#usize 1#usize ik (by scalar_tac) (by decide)
    as ⟨b2, bs3, hb2, hl3, hk3, ho3⟩
  step as ⟨is, his⟩
  step with write_spec bs3 6#usize 2#usize is (by scalar_tac) (by decide)
    as ⟨b3, bs4, hb3, hl4, hs4, ho4⟩
  step with write_spec bs4 8#usize 8#usize e.receiver (by scalar_tac) (by decide)
    as ⟨b4, bs5, hb4, hl5, hr5, ho5⟩
  step with write_spec bs5 16#usize 8#usize e.sequence (by scalar_tac) (by decide)
    as ⟨b5, bs6, hb5, hl6, hq6, ho6⟩
  step as ⟨ia, hia⟩
  step with write_spec bs6 24#usize 8#usize ia (by scalar_tac) (by decide)
    as ⟨b6, bs7, hb6, hl7, ha7, ho7⟩
  simp only [hb0, hb1, hb2, hb3, hb4, hb5, hb6, Bool.and_self, ↓reduceIte]
  rw [WP.spec_ok]
  dsimp only
  have hv_eq : iv.val = packet.VERSION.val := by rw [hiv]; exact cast_u8_u64_val _
  have hk_eq : ik.val = packet.KIND_ECHO.val := by rw [hik]; exact cast_u8_u64_val _
  have hs_eq : is.val = e.stream.val := by rw [his]; exact cast_u16_u64_val _
  refine ⟨rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((hm1.preserve hl2 ho2 (Or.inl (by decide)))
      |>.preserve hl3 ho3 (Or.inl (by decide)))
      |>.preserve hl4 ho4 (Or.inl (by decide)))
      |>.preserve hl5 ho5 (Or.inl (by decide)))
      |>.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide))
  · rw [← hv_eq]
    exact (((((hv2.preserve hl3 ho3 (Or.inl (by decide)))
      |>.preserve hl4 ho4 (Or.inl (by decide)))
      |>.preserve hl5 ho5 (Or.inl (by decide)))
      |>.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide)))
  · rw [← hk_eq]
    exact ((((hk3.preserve hl4 ho4 (Or.inl (by decide)))
      |>.preserve hl5 ho5 (Or.inl (by decide)))
      |>.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide)))
  · rw [← hs_eq]
    exact (((hs4.preserve hl5 ho5 (Or.inl (by decide)))
      |>.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide)))
  · exact ((hr5.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide)))
  · exact hq6.preserve hl7 ho7 (Or.inl (by decide))
  · rw [← hia]; exact ha7

/-- Writing an `Echo` into a 32-byte buffer and parsing it back recovers the
exact `Echo`. -/
theorem echo_roundtrip (e : packet.Echo) (bytes : Slice Std.U8)
    (hlen : bytes.val.length = packet.ECHO.val) :
    (do
      let out ← packet.write_echo e bytes
      match out.1 with
      | some _ => packet.parse_echo out.2
      | none => ok (.Err .TooShort))
    ⦃ r => r = .Ok e ⦄ := by
  have hecho : packet.ECHO.val = 32 := by simp [packet.ECHO]
  step with write_echo_spec e bytes hlen
    as ⟨out, hsome, hlen7, hm7, hv7, hk7, hs7, hr7, hq7, ha7⟩
  rw [hsome]
  have hs_lt : e.stream.val < 2 ^ (8 * 2) := by scalar_tac
  have hrec_lt : e.receiver.val < 2 ^ (8 * 8) := by scalar_tac
  have hseq_lt : e.sequence.val < 2 ^ (8 * 8) := by scalar_tac
  have hia_lt : (IScalar.hcast .U64 e.arrival).val < 2 ^ (8 * 8) := by scalar_tac
  unfold packet.parse_echo
  step with kind_of_hasLE out.2 packet.KIND_ECHO hm7 hv7 hk7 as ⟨rk, hrk⟩
  rw [hrk]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step with read_of_hasLE out.2 6#usize 2#usize e.stream.val hs7 (by decide) hs_lt
    as ⟨o0, stream, ho0, hstream⟩
  step with read_of_hasLE out.2 8#usize 8#usize e.receiver.val hr7 (by decide) hrec_lt
    as ⟨o1, receiver, ho1, hreceiver⟩
  step with read_of_hasLE out.2 16#usize 8#usize e.sequence.val hq7 (by decide) hseq_lt
    as ⟨o2, sequence, ho2', hsequence⟩
  step with read_of_hasLE out.2 24#usize 8#usize (IScalar.hcast .U64 e.arrival).val ha7 (by decide)
      hia_lt
    as ⟨o3, arrival, ho3', harrival⟩
  rw [ho0, ho1, ho2', ho3']
  have hlen_eq : out.2.len = packet.ECHO := by
    apply UScalar.eq_of_val_eq
    have : out.2.len.val = out.2.val.length := rfl
    omega
  simp only [hlen_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step as ⟨st, hst⟩
  step as ⟨ar, har⟩
  congr 1
  cases e
  congr 1
  · rw [hst]
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hstream]
    scalar_tac
  · exact UScalar.eq_of_val_eq hreceiver
  · exact UScalar.eq_of_val_eq hsequence
  · rw [har]; exact hcast_i64_u64_i64 _ arrival harrival

/-! ## Request round-trip -/

/-- Exact 32-byte wire layout produced by `write_request`. -/
theorem write_request_spec (e : packet.Request) (bytes : Slice Std.U8)
    (hlen : bytes.val.length = packet.REQUEST.val) :
    packet.write_request e bytes ⦃ out =>
      out.1 = some packet.REQUEST
      ∧ out.2.val.length = 32
      ∧ HasLE out.2.val 0 4 packet.MAGIC.val
      ∧ HasLE out.2.val 4 1 packet.VERSION.val
      ∧ HasLE out.2.val 5 1 packet.KIND_REQUEST.val
      ∧ HasLE out.2.val 6 2 e.stream.val
      ∧ HasLE out.2.val 8 8 e.timeline.val
      ∧ HasLE out.2.val 16 8 e.first.val
      ∧ HasLE out.2.val 24 8 e.frames.val ⦄ := by
  have hrequest : packet.REQUEST.val = 32 := by simp [packet.REQUEST]
  have hlen32 : bytes.val.length = 32 := by omega
  unfold packet.write_request
  have hnotlt : ¬ bytes.len < packet.REQUEST := by
    have : bytes.len.val = bytes.val.length := rfl
    scalar_tac
  simp only [hnotlt, ↓reduceIte]
  step with write_spec bytes 0#usize 4#usize packet.MAGIC (by scalar_tac) (by decide)
    as ⟨b0, bs1, hb0, hl1, hm1, _⟩
  step as ⟨iv, hiv⟩
  step with write_spec bs1 4#usize 1#usize iv (by scalar_tac) (by decide)
    as ⟨b1, bs2, hb1, hl2, hv2, ho2⟩
  step as ⟨ik, hik⟩
  step with write_spec bs2 5#usize 1#usize ik (by scalar_tac) (by decide)
    as ⟨b2, bs3, hb2, hl3, hk3, ho3⟩
  step as ⟨is, his⟩
  step with write_spec bs3 6#usize 2#usize is (by scalar_tac) (by decide)
    as ⟨b3, bs4, hb3, hl4, hs4, ho4⟩
  step with write_spec bs4 8#usize 8#usize e.timeline (by scalar_tac) (by decide)
    as ⟨b4, bs5, hb4, hl5, hr5, ho5⟩
  step with write_spec bs5 16#usize 8#usize e.first (by scalar_tac) (by decide)
    as ⟨b5, bs6, hb5, hl6, hq6, ho6⟩
  step with write_spec bs6 24#usize 8#usize e.frames (by scalar_tac) (by decide)
    as ⟨b6, bs7, hb6, hl7, ha7, ho7⟩
  simp only [hb0, hb1, hb2, hb3, hb4, hb5, hb6, Bool.and_self, ↓reduceIte]
  rw [WP.spec_ok]
  dsimp only
  have hv_eq : iv.val = packet.VERSION.val := by rw [hiv]; exact cast_u8_u64_val _
  have hk_eq : ik.val = packet.KIND_REQUEST.val := by rw [hik]; exact cast_u8_u64_val _
  have hs_eq : is.val = e.stream.val := by rw [his]; exact cast_u16_u64_val _
  refine ⟨rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((hm1.preserve hl2 ho2 (Or.inl (by decide)))
      |>.preserve hl3 ho3 (Or.inl (by decide)))
      |>.preserve hl4 ho4 (Or.inl (by decide)))
      |>.preserve hl5 ho5 (Or.inl (by decide)))
      |>.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide))
  · rw [← hv_eq]
    exact (((((hv2.preserve hl3 ho3 (Or.inl (by decide)))
      |>.preserve hl4 ho4 (Or.inl (by decide)))
      |>.preserve hl5 ho5 (Or.inl (by decide)))
      |>.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide)))
  · rw [← hk_eq]
    exact ((((hk3.preserve hl4 ho4 (Or.inl (by decide)))
      |>.preserve hl5 ho5 (Or.inl (by decide)))
      |>.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide)))
  · rw [← hs_eq]
    exact (((hs4.preserve hl5 ho5 (Or.inl (by decide)))
      |>.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide)))
  · exact ((hr5.preserve hl6 ho6 (Or.inl (by decide)))
      |>.preserve hl7 ho7 (Or.inl (by decide)))
  · exact hq6.preserve hl7 ho7 (Or.inl (by decide))
  · exact ha7

/-- Writing a `Request` into a 32-byte buffer and parsing it back recovers the
exact `Request`. -/
theorem request_roundtrip (e : packet.Request) (bytes : Slice Std.U8)
    (hlen : bytes.val.length = packet.REQUEST.val) :
    (do
      let out ← packet.write_request e bytes
      match out.1 with
      | some _ => packet.parse_request out.2
      | none => ok (.Err .TooShort))
    ⦃ r => r = .Ok e ⦄ := by
  have hrequest : packet.REQUEST.val = 32 := by simp [packet.REQUEST]
  step with write_request_spec e bytes hlen
    as ⟨out, hsome, hlen7, hm7, hv7, hk7, hs7, hr7, hq7, ha7⟩
  rw [hsome]
  have hs_lt : e.stream.val < 2 ^ (8 * 2) := by scalar_tac
  have htl_lt : e.timeline.val < 2 ^ (8 * 8) := by scalar_tac
  have hfirst_lt : e.first.val < 2 ^ (8 * 8) := by scalar_tac
  have hframes_lt : e.frames.val < 2 ^ (8 * 8) := by scalar_tac
  unfold packet.parse_request
  step with kind_of_hasLE out.2 packet.KIND_REQUEST hm7 hv7 hk7 as ⟨rk, hrk⟩
  rw [hrk]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step with read_of_hasLE out.2 6#usize 2#usize e.stream.val hs7 (by decide) hs_lt
    as ⟨o0, stream, ho0, hstream⟩
  step with read_of_hasLE out.2 8#usize 8#usize e.timeline.val hr7 (by decide) htl_lt
    as ⟨o1, timeline, ho1, htimeline⟩
  step with read_of_hasLE out.2 16#usize 8#usize e.first.val hq7 (by decide) hfirst_lt
    as ⟨o2, first, ho2', hfirst⟩
  step with read_of_hasLE out.2 24#usize 8#usize e.frames.val ha7 (by decide) hframes_lt
    as ⟨o3, frames, ho3', hframes⟩
  rw [ho0, ho1, ho2', ho3']
  have hlen_eq : out.2.len = packet.REQUEST := by
    apply UScalar.eq_of_val_eq
    have : out.2.len.val = out.2.val.length := rfl
    omega
  simp only [hlen_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step as ⟨st, hst⟩
  congr 1
  cases e
  congr 1
  · rw [hst]
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hstream]
    scalar_tac
  · exact UScalar.eq_of_val_eq htimeline
  · exact UScalar.eq_of_val_eq hfirst
  · exact UScalar.eq_of_val_eq hframes

/-! ## Report round-trip -/

@[step]
theorem write_report_loop_spec (bytes : Slice Std.U8) (length : Std.Usize)
    (written : Bool) (place : Std.Usize)
    (hfit : length.val ≤ bytes.val.length) (hplace : packet.REPORT.val ≤ place.val)
    (hple : place.val ≤ length.val) :
    packet.write_report_loop bytes length written place ⦃ out =>
      out.1.val.length = bytes.val.length
      ∧ out.2 = written
      ∧ (∀ j < packet.REPORT.val, out.1.val.getD j 0#u8 = bytes.val.getD j 0#u8)
      ∧ ∀ j, place.val ≤ j → j < length.val → out.1.val.getD j 0#u8 = 0#u8 ⦄ := by
  unfold packet.write_report_loop
  apply loop.spec_decr_nat
    (measure := fun x : Slice Std.U8 × Bool × Std.Usize => length.val - x.2.2.val)
    (inv := fun x : Slice Std.U8 × Bool × Std.Usize =>
      x.1.val.length = bytes.val.length
      ∧ x.2.1 = written
      ∧ packet.REPORT.val ≤ x.2.2.val
      ∧ x.2.2.val ≤ length.val
      ∧ (∀ j < packet.REPORT.val, x.1.val.getD j 0#u8 = bytes.val.getD j 0#u8)
      ∧ ∀ j, place.val ≤ j → j < x.2.2.val → x.1.val.getD j 0#u8 = 0#u8)
  · rintro ⟨bs, w, p⟩ ⟨hlen, hw, hp, hpl, hpre, hzero⟩
    dsimp only at hlen hw hp hpl hpre hzero
    unfold packet.write_report_loop.body
    simp only
    split
    · have hlt : p.val < length.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add p 1#usize).val = p.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step with write_spec bs p 1#usize 0#u64 (by scalar_tac) (by decide)
        as ⟨b, bs1, hb, hlen1, hhas1, hout1⟩
      step as ⟨p1, hp1⟩
      refine ⟨by omega, by simp [hw, hb], by rw [hp1, hnext]; omega, by rw [hp1, hnext]; omega,
        fun j hj => ?_, fun j hj1 hj2 => ?_, by rw [hp1, hnext]; omega⟩
      · rw [hout1 j (Or.inl (by omega))]
        exact hpre j hj
      · rw [hp1, hnext] at hj2
        by_cases hjp : j = p.val
        · subst hjp
          have hb0 := hhas1.2 0 (by omega)
          rw [Nat.add_zero] at hb0
          apply UScalar.eq_of_val_eq
          simpa using hb0
        · rw [hout1 j (by omega)]
          exact hzero j hj1 (by omega)
    · have heq : p.val = length.val := by scalar_tac
      rw [WP.spec_ok]
      rw [heq] at hzero
      exact ⟨hlen, hw, hpre, hzero⟩
  · dsimp only
    exact ⟨rfl, rfl, hplace, hple, fun _ _ => rfl, fun _ h1 h2 => by omega⟩

/-- Exact 32-byte wire prefix, exact length, and zero padding produced by `write_report`. -/
theorem write_report_spec (rep : packet.Report) (bytes : Slice Std.U8) (length : Std.Usize)
    (hlen : max packet.REPORT.val length.val ≤ bytes.val.length) :
    packet.write_report rep bytes length ⦃ out =>
      (∃ n, out.1 = some n ∧ n.val = max packet.REPORT.val length.val)
      ∧ out.2.val.length = bytes.val.length
      ∧ HasLE out.2.val 0 4 packet.MAGIC.val
      ∧ HasLE out.2.val 4 1 packet.VERSION.val
      ∧ HasLE out.2.val 5 1 packet.KIND_REPORT.val
      ∧ HasLE out.2.val 6 2 rep.stream.val
      ∧ HasLE out.2.val 8 8 rep.timeline.val
      ∧ HasLE out.2.val 16 8 rep.receiver.val
      ∧ HasLE out.2.val 24 8 rep.sequence.val
      ∧ ∀ j, packet.REPORT.val ≤ j → j < max packet.REPORT.val length.val →
          out.2.val.getD j 0#u8 = 0#u8 ⦄ := by
  have hrep : packet.REPORT.val = 32 := by simp [packet.REPORT]
  unfold packet.write_report
  have hlen1_eq :
      (if length < packet.REPORT then ok packet.REPORT else ok length) =
        ok (if length < packet.REPORT then packet.REPORT else length) := by
    split <;> rfl
  rw [hlen1_eq]
  simp only [bind_ok]
  set length1 : Std.Usize := if length < packet.REPORT then packet.REPORT else length
  have hl1_val : length1.val = max packet.REPORT.val length.val := by
    dsimp only [length1]; split <;> scalar_tac
  have hl1_ge : 32 ≤ length1.val := by
    dsimp only [length1]; split <;> scalar_tac
  have hl1_le : length1.val ≤ bytes.val.length := by
    have h1 : packet.REPORT.val ≤ bytes.val.length := le_trans (le_max_left _ _) hlen
    have h2 : length.val ≤ bytes.val.length := le_trans (le_max_right _ _) hlen
    dsimp only [length1]
    split <;> assumption
  have hnotlt : ¬ bytes.len < length1 := by
    have : bytes.len.val = bytes.val.length := rfl
    scalar_tac
  simp only [hnotlt, ↓reduceIte]
  have hfit : ∀ (s : Slice Std.U8) (p c : Std.Usize),
      s.val.length = bytes.val.length → p.val + c.val ≤ 32 → p.val + c.val ≤ s.val.length :=
    fun _ _ _ h1 h2 => by omega
  step with write_spec bytes 0#usize 4#usize packet.MAGIC (hfit _ _ _ rfl (by decide)) (by decide)
    as ⟨b0, bs1, hb0, hl1, hm1, _⟩
  step as ⟨iv, hiv⟩
  step with write_spec bs1 4#usize 1#usize iv (hfit _ _ _ hl1 (by decide)) (by decide)
    as ⟨b1, bs2, hb1, hl2, hv2, ho2⟩
  step as ⟨ik, hik⟩
  step with write_spec bs2 5#usize 1#usize ik (hfit _ _ _ (hl2.trans hl1) (by decide)) (by decide)
    as ⟨b2, bs3, hb2, hl3, hk3, ho3⟩
  step as ⟨is, his⟩
  step with write_spec bs3 6#usize 2#usize is (hfit _ _ _ (hl3.trans (hl2.trans hl1)) (by decide)) (by decide)
    as ⟨b3, bs4, hb3, hl4, hs4, ho4⟩
  step with write_spec bs4 8#usize 8#usize rep.timeline (hfit _ _ _ (by omega) (by decide)) (by decide)
    as ⟨b4, bs5, hb4, hl5, ht5, ho5⟩
  step with write_spec bs5 16#usize 8#usize rep.receiver (hfit _ _ _ (by omega) (by decide)) (by decide)
    as ⟨b5, bs6, hb5, hl6, hr6, ho6⟩
  step with write_spec bs6 24#usize 8#usize rep.sequence (hfit _ _ _ (by omega) (by decide)) (by decide)
    as ⟨b6, bs7, hb6, hl7, hq7, ho7⟩
  step with write_report_loop_spec bs7 length1
      ((((((b0 && b1) && b2) && b3) && b4) && b5) && b6) packet.REPORT (by omega)
      (le_refl _) (by omega)
    as ⟨bs8, w8, hl8, hw8, hpre8, hzero8⟩
  have hw8_true : w8 = true := by simp [hw8, hb0, hb1, hb2, hb3, hb4, hb5, hb6]
  simp only [hw8_true, ↓reduceIte]
  rw [WP.spec_ok]
  dsimp only
  have hpre_hasLE : ∀ a c v, a + c ≤ 32 → HasLE bs7.val a c v → HasLE bs8.val a c v := by
    intro a c v hac h
    refine ⟨by omega, fun k hk => ?_⟩
    rw [hpre8 (a + k) (by omega)]
    exact h.2 k hk
  have hv_eq : iv.val = packet.VERSION.val := by rw [hiv]; exact cast_u8_u64_val _
  have hk_eq : ik.val = packet.KIND_REPORT.val := by rw [hik]; exact cast_u8_u64_val _
  have hs_eq : is.val = rep.stream.val := by rw [his]; exact cast_u16_u64_val _
  refine ⟨⟨length1, rfl, hl1_val⟩, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpre_hasLE 0 4 _ (by omega)
      ((((((hm1.preserve hl2 ho2 (Or.inl (by decide)))
        |>.preserve hl3 ho3 (Or.inl (by decide)))
        |>.preserve hl4 ho4 (Or.inl (by decide)))
        |>.preserve hl5 ho5 (Or.inl (by decide)))
        |>.preserve hl6 ho6 (Or.inl (by decide)))
        |>.preserve hl7 ho7 (Or.inl (by decide)))
  · rw [← hv_eq]
    exact hpre_hasLE 4 1 _ (by omega)
      (((((hv2.preserve hl3 ho3 (Or.inl (by decide)))
        |>.preserve hl4 ho4 (Or.inl (by decide)))
        |>.preserve hl5 ho5 (Or.inl (by decide)))
        |>.preserve hl6 ho6 (Or.inl (by decide)))
        |>.preserve hl7 ho7 (Or.inl (by decide)))
  · rw [← hk_eq]
    exact hpre_hasLE 5 1 _ (by omega)
      ((((hk3.preserve hl4 ho4 (Or.inl (by decide)))
        |>.preserve hl5 ho5 (Or.inl (by decide)))
        |>.preserve hl6 ho6 (Or.inl (by decide)))
        |>.preserve hl7 ho7 (Or.inl (by decide)))
  · rw [← hs_eq]
    exact hpre_hasLE 6 2 _ (by omega)
      (((hs4.preserve hl5 ho5 (Or.inl (by decide)))
        |>.preserve hl6 ho6 (Or.inl (by decide)))
        |>.preserve hl7 ho7 (Or.inl (by decide)))
  · exact hpre_hasLE 8 8 _ (by omega)
      ((ht5.preserve hl6 ho6 (Or.inl (by decide)))
        |>.preserve hl7 ho7 (Or.inl (by decide)))
  · exact hpre_hasLE 16 8 _ (by omega) (hr6.preserve hl7 ho7 (Or.inl (by decide)))
  · exact hpre_hasLE 24 8 _ (by omega) hq7
  · intro j hj1 hj2
    exact hzero8 j hj1 (by rw [hl1_val]; exact hj2)

/-- Writing a `Report` (with any padding length that fits `bytes`) and parsing
it back recovers the exact `Report`. -/
theorem report_roundtrip (rep : packet.Report) (bytes : Slice Std.U8) (length : Std.Usize)
    (hlen : max packet.REPORT.val length.val ≤ bytes.val.length) :
    (do
      let out ← packet.write_report rep bytes length
      match out.1 with
      | some _ => packet.parse_report out.2
      | none => ok (.Err .TooShort))
    ⦃ r => r = .Ok rep ⦄ := by
  step with write_report_spec rep bytes length hlen
    as ⟨out, n, hsome, _, _, hm8, hv8, hk8, hs8, ht8, hr8, hq8, _⟩
  rw [hsome]
  have hs_lt : rep.stream.val < 2 ^ (8 * 2) := by scalar_tac
  have htl_lt : rep.timeline.val < 2 ^ (8 * 8) := by scalar_tac
  have hrec_lt : rep.receiver.val < 2 ^ (8 * 8) := by scalar_tac
  have hseq_lt : rep.sequence.val < 2 ^ (8 * 8) := by scalar_tac
  unfold packet.parse_report
  step with kind_of_hasLE out.2 packet.KIND_REPORT hm8 hv8 hk8 as ⟨rk, hrk⟩
  rw [hrk]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  step with read_of_hasLE out.2 6#usize 2#usize rep.stream.val hs8 (by decide) hs_lt
    as ⟨o0, stream, ho0, hstream⟩
  step with read_of_hasLE out.2 8#usize 8#usize rep.timeline.val ht8 (by decide) htl_lt
    as ⟨o1, timeline, ho1, htimeline⟩
  step with read_of_hasLE out.2 16#usize 8#usize rep.receiver.val hr8 (by decide) hrec_lt
    as ⟨o2, receiver, ho2', hreceiver⟩
  step with read_of_hasLE out.2 24#usize 8#usize rep.sequence.val hq8 (by decide) hseq_lt
    as ⟨o3, sequence, ho3', hsequence⟩
  rw [ho0, ho1, ho2', ho3']
  step as ⟨st, hst⟩
  congr 1
  cases rep
  congr 1
  · rw [hst]
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hstream]
    scalar_tac
  · exact UScalar.eq_of_val_eq htimeline
  · exact UScalar.eq_of_val_eq hreceiver
  · exact UScalar.eq_of_val_eq hsequence


end Unisono.Packet
