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
# Graph Best Linear Unbiased Estimator (BLUE) over integer LDLᵀ

Totality, output variance invariants, zero-residual fixed-point preservation
of `solve_ldlt`, and exact Star degeneration of `solve_blue` on a single-edge
two-host graph.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Blue

@[step]
private theorem slice_get_total {T : Type} (s : Slice T) (i : Std.Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T) s i ⦃ _ => True ⦄ := by
  simp [core.slice.Slice.get, core.slice.index.Usize.get]

@[step]
private theorem slice_get_mut_total {T : Type} (s : Slice T) (i : Std.Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice T) s i ⦃ _ => True ⦄ := by
  simp [core.slice.Slice.get_mut, core.slice.index.Usize.get_mut]

private theorem usize_wrapping_sub_one_val (b : Std.Usize) (hpos : 0 < b.val) :
    (core.num.Usize.wrapping_sub b 1#usize).val = b.val - 1 := by
  simp only [core.num.Usize.wrapping_sub_val_eq, UScalar.size]
  have hb : b.val < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
  have h1 : (1#usize).val = 1 := rfl
  rw [h1]
  have hadd : b.val + (2 ^ UScalarTy.Usize.numBits - 1) =
      (b.val - 1) + 1 * 2 ^ UScalarTy.Usize.numBits := by omega
  rw [hadd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

private theorem loop_step {α β : Type} (body : α → Result (ControlFlow α β)) (x : α)
    (post : β → Prop)
    (h : body x ⦃ r => match r with | .done y => post y | .cont x' => loop body x' ⦃ post ⦄ ⦄) :
    loop body x ⦃ post ⦄ := by
  unfold loop
  apply WP.spec_bind h
  intro r hr
  cases r with
  | done z => simpa using hr
  | cont x' => exact hr

private theorem usize_sat_add_one (a : Std.Usize) (h : a.val < 1000) :
    (core.num.Usize.saturating_add a 1#usize).val = a.val + 1 := by
  have hm : 1000 ≤ Usize.max := by
    rcases Usize.bounds_eq with hb | hb <;> rw [hb] <;> scalar_tac
  exact Usize.saturating_add_val a 1#usize (by change a.val + 1 ≤ Usize.max; omega)

private theorem ite_t {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

private theorem ite_f {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

private theorem i128_wrapping_shr_zero (s : Std.U32) :
    core.num.I128.wrapping_shr 0#i128 s = 0#i128 := by
  apply IScalar.eq_of_val_eq
  simp only [IScalar.val, core.num.I128.wrapping_shr_bv_eq]
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  have h0 : (0#i128 : Std.I128).bv.toInt = 0 := rfl
  rw [h0, Int.zero_ediv]

private theorem i128_saturating_sub_zero :
    core.num.I128.saturating_sub 0#i128 0#i128 = 0#i128 := by
  apply IScalar.eq_of_val_eq
  rw [I128.saturating_sub_val]
  change max (-2^127) (min (2^127 - 1) ((0 : ℤ) - 0)) = 0
  omega

private theorem list_getElem?_set_opt {α : Type} (l : List α) (i k : Nat) (x : Option α) :
    (l.set_opt i x)[k]? =
      if k = i then match l[k]? with | none => none | some old => some (x.getD old)
      else l[k]? := by
  induction l generalizing i k with
  | nil => simp
  | cons hd tl ih =>
    cases i with
    | zero => cases k <;> simp
    | succ i' =>
      cases k with
      | zero => simp [List.set_opt_cons_nzero' _ _ _ _ (Nat.succ_pos i')]
      | succ k' =>
        simp only [List.set_opt_cons_nzero' _ _ _ _ (Nat.succ_pos i'), Nat.succ_sub_one,
          List.getElem?_cons_succ, ih i' k', Nat.succ.injEq]

private theorem array_slice_getElem? {T : Type} {n : Std.Usize} (a : Array T n) (k : Std.Usize) :
    (Array.to_slice a)[k]? = a.val[k.val]? := by
  rw [Slice.getElem?_Usize_eq]
  simp [Array.to_slice]

private theorem array_to_slice_mut_fst {T : Type} {n : Std.Usize} (a : Array T n) :
    (Array.to_slice_mut a).1 = Array.to_slice a := by
  simp [Array.to_slice_mut]

private theorem array_to_slice_mut_set_opt {T : Type} {n : Std.Usize} (a : Array T n)
    (i : Std.Usize) (x : Option T) :
    (Array.to_slice_mut a).2 ((Array.to_slice_mut a).1.set_opt i x) = a.set_opt i x := by
  cases a
  simp [Array.to_slice_mut, Array.from_slice, Array.to_slice, Array.set_opt, Slice.set_opt]

private theorem array_set_opt_val {T : Type} {n : Std.Usize} (a : Array T n) (i : Std.Usize)
    (x : Option T) :
    ((Array.to_slice_mut a).2 ((Array.to_slice_mut a).1.set_opt i x)).val =
      a.val.set_opt i.val x := by
  rw [array_to_slice_mut_set_opt, Array.set_opt_val_eq]

private theorem array_repeat_get? {T : Type} {n : Std.Usize} (x : T) (k : Std.Usize) :
    (Array.to_slice (Array.repeat n x))[k]? = if k.val < n.val then some x else none := by
  rw [array_slice_getElem?]
  have hrep : (Array.repeat n x).val = List.replicate n.val x := by simp [Array.repeat]
  rw [hrep, List.getElem?_replicate]

private theorem array_set_opt_get? {T : Type} {n : Std.Usize} (a : Array T n) (i k : Std.Usize)
    (x : Option T) :
    (Array.to_slice (a.set_opt i x))[k]? =
      if k.val = i.val then
        match (Array.to_slice a)[k]? with | none => none | some old => some (x.getD old)
      else (Array.to_slice a)[k]? := by
  rw [array_slice_getElem?, Array.set_opt_val_eq, list_getElem?_set_opt, array_slice_getElem?]

/-! ## Scalar and array helpers -/

@[step]
theorem clamp_sym_total (x hi : Std.I128) :
    blue.clamp_sym x hi ⦃ _ => True ⦄ := by
  unfold blue.clamp_sym
  step as ⟨lo⟩
  split
  · simp
  · split <;> simp

@[step]
theorem get_i128_spec (slice : Slice Std.I128) (idx : Std.Usize) :
    blue.get_i128 slice idx ⦃ r =>
      r = match slice[idx]? with | none => 0#i128 | some v => v ⦄ := by
  unfold blue.get_i128
  simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  cases slice[idx]? <;> simp

@[step]
theorem get_i64_spec (slice : Slice Std.I64) (idx : Std.Usize) :
    blue.get_i64 slice idx ⦃ r =>
      r = match slice[idx]? with | none => 0#i64 | some v => v ⦄ := by
  unfold blue.get_i64
  simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  cases slice[idx]? <;> simp

@[step]
theorem get_bool_spec (slice : Slice Bool) (idx : Std.Usize) :
    blue.get_bool slice idx ⦃ r =>
      r = match slice[idx]? with | none => false | some v => v ⦄ := by
  unfold blue.get_bool
  simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  cases slice[idx]? <;> simp

@[step]
theorem get_usize_spec (slice : Slice Std.Usize) (idx : Std.Usize) :
    blue.get_usize slice idx ⦃ r =>
      r = match slice[idx]? with | none => 0#usize | some v => v ⦄ := by
  unfold blue.get_usize
  simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  cases slice[idx]? <;> simp

@[step]
theorem mat_add_total (mat : Array Std.I128 256#usize) (dim row col : Std.Usize)
    (delta : Std.I128) :
    blue.mat_add mat dim row col delta ⦃ _ => True ⦄ := by
  unfold blue.mat_add
  step as ⟨i⟩
  step as ⟨idx⟩
  step as ⟨s, back⟩
  step as ⟨o, get_back⟩
  cases o <;> step*

@[step]
theorem mat_get_total (mat : Array Std.I128 256#usize) (dim row col : Std.Usize) :
    blue.mat_get mat dim row col ⦃ _ => True ⦄ := by
  unfold blue.mat_get
  step*

@[step]
theorem mul_shr32_total (a b : Std.I128) :
    blue.mul_shr32 a b ⦃ _ => True ⦄ := by
  unfold blue.mul_shr32
  step as ⟨o⟩
  cases o with
  | none =>
    step as ⟨hi⟩
    step as ⟨lo⟩
    step as ⟨t1⟩
    step as ⟨o1⟩
    have ht2 :
        (match o1 with
          | none => do
            let b_hi ← lift (core.num.I128.wrapping_shr b 32#u32)
            let b_lo ← lift (b &&& 4294967295#i128)
            let i ← fixed.saturating_mul_i128 lo b_hi
            let i1 ← fixed.saturating_mul_i128 lo b_lo
            let i2 ← lift (core.num.I128.wrapping_shr i1 32#u32)
            ok (core.num.I128.saturating_add i i2)
          | some p => ok (core.num.I128.wrapping_shr p 32#u32)) ⦃ _ => True ⦄ := by
      cases o1 with
      | none => step*
      | some p => simp
    apply WP.spec_bind ht2
    intro t2 _
    simp
  | some p => simp

/-- `clamp_out_var` always clamps its output into `[1, MAX_OUT_VAR_NS2]`. -/
@[step]
theorem clamp_out_var_spec (v : Std.I128) :
    blue.clamp_out_var v ⦃ r =>
      1 ≤ r.val ∧ r.val ≤ blue.MAX_OUT_VAR_NS2.val
      ∧ (1 ≤ v.val → v.val ≤ blue.MAX_OUT_VAR_NS2.val → (r.val : ℤ) = v.val)
      ∧ (blue.MAX_OUT_VAR_NS2.val < v.val → r = blue.MAX_OUT_VAR_NS2) ⦄ := by
  unfold blue.clamp_out_var
  have hmax_val : (blue.MAX_OUT_VAR_NS2 : Std.U64).val = 1000000000000000000 := by
    unfold blue.MAX_OUT_VAR_NS2; rfl
  split
  · rename_i hle
    rw [WP.spec_ok]
    refine ⟨by decide, by rw [hmax_val]; decide, fun h1 _ => ?_, fun hgt => ?_⟩
    · have : v.val ≤ 1 := by scalar_tac
      change (1 : ℤ) = v.val
      omega
    · have : v.val ≤ 1 := by scalar_tac
      rw [hmax_val] at hgt
      omega
  · step as ⟨hi, hhi⟩
    have hhi_val : hi.val = blue.MAX_OUT_VAR_NS2.val := by
      rw [hhi]; exact U64.hcast_I128_val _
    split
    · rename_i hgt
      rw [WP.spec_ok]
      refine ⟨by rw [hmax_val]; decide, le_refl _, fun _ hle => ?_, fun _ => rfl⟩
      have : hi.val < v.val := by scalar_tac
      omega
    · rename_i hnge hngt
      have hv_lo : 1 < v.val := by scalar_tac
      have hv_hi : v.val ≤ blue.MAX_OUT_VAR_NS2.val := by
        have : v.val ≤ hi.val := by scalar_tac
        omega
      rw [WP.spec_ok]
      have hcast : ((IScalar.hcast .U64 v).val : ℤ) = v.val := by
        rw [IScalar.hcast_val_eq]
        have hlt : v.val < (2 ^ UScalarTy.U64.numBits : ℕ) := by
          change v.val < (2 ^ 64 : ℕ)
          omega
        rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hlt)]
        exact Int.toNat_of_nonneg (by omega)
      refine ⟨by omega, by omega, fun _ _ => hcast, fun hgt => by omega⟩

/-! ## `solve_ldlt`: totality and zero-RHS fixed point -/

/-- Every entry of a 16-element `I128` array is zero. -/
def AllZero16 (a : Array Std.I128 16#usize) : Prop :=
  ∀ (k : Std.Usize) (v : Std.I128), (Array.to_slice a)[k]? = some v → v = 0#i128

private theorem allZero16_repeat : AllZero16 (Array.repeat 16#usize 0#i128) := by
  intro k v h
  rw [array_slice_getElem?] at h
  have hrep : (Array.repeat 16#usize 0#i128).val = List.replicate 16 0#i128 := by
    simp [Array.repeat]
  rw [hrep, List.getElem?_replicate] at h
  split_ifs at h
  exact (Option.some.inj h).symm

private theorem allZero16_set_zero (a : Array Std.I128 16#usize) (i : Std.Usize)
    (ha : AllZero16 a) :
    ∀ (opt : Option Std.I128), (∀ x, opt = some x → x = 0#i128) →
      AllZero16 ((Array.to_slice_mut a).2 ((Array.to_slice_mut a).1.set_opt i opt)) := by
  intro opt hopt k v h
  rw [array_slice_getElem?, array_set_opt_val, list_getElem?_set_opt] at h
  split_ifs at h with heq
  · cases hget : a.val[k.val]? with
    | none => rw [hget] at h; cases h
    | some old =>
      rw [hget] at h
      have hv := (Option.some.inj h).symm
      rw [hv]
      cases opt with
      | none => exact ha k old (by rw [array_slice_getElem?]; exact hget)
      | some val => exact hopt val rfl
  · exact ha k v (by rw [array_slice_getElem?]; exact h)

@[step]
theorem solve_ldlt_loop0_loop0_total (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (y : Array Std.I128 16#usize) (i : Std.Usize) (sum : Std.I128) (j : Std.Usize) :
    blue.solve_ldlt_loop0_loop0 dim l_q32 y i sum j ⦃ _ => True ⦄ := by
  unfold blue.solve_ldlt_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Std.I128 × Std.Usize => i.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨sum1, j1⟩ _
    unfold blue.solve_ldlt_loop0_loop0.body
    simp only
    split
    · have hlt : j1.val < i.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add j1 1#usize).val = j1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step*
    · simp
  · trivial

theorem solve_ldlt_loop0_loop0_zero (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (y : Array Std.I128 16#usize) (i : Std.Usize) (j : Std.Usize) (hy : AllZero16 y) :
    blue.solve_ldlt_loop0_loop0 dim l_q32 y i 0#i128 j ⦃ r => r = 0#i128 ⦄ := by
  unfold blue.solve_ldlt_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Std.I128 × Std.Usize => i.val - x.2.val)
    (inv := fun x => x.1 = 0#i128)
  · rintro ⟨sum1, j1⟩ hsum
    dsimp only at hsum
    subst hsum
    unfold blue.solve_ldlt_loop0_loop0.body
    simp only
    split
    · have hlt : j1.val < i.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add j1 1#usize).val = j1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s⟩
      step as ⟨i1⟩
      step as ⟨i2⟩
      step as ⟨i3⟩
      step as ⟨lij⟩
      step as ⟨s1, hs1⟩
      step as ⟨yj, hyj⟩
      have hyj0 : yj = 0#i128 := by
        rw [hyj, hs1]
        cases hget : (Array.to_slice y)[j1]? with
        | none => rfl
        | some v => exact hy j1 v hget
      subst hyj0
      step with Fixed.saturating_mul_i128_spec lij 0#i128 as ⟨prod, hprod⟩
      have hprod0 : prod = 0#i128 := by
        have hv : prod.val = 0 := by rw [hprod]; simp [Fixed.clamp128]
        exact IScalar.eq_of_val_eq hv
      subst hprod0
      step as ⟨term, hterm⟩
      have hterm0 : term = 0#i128 := by rw [hterm]; exact i128_wrapping_shr_zero 32#u32
      subst hterm0
      step as ⟨sum2, hsum2⟩
      have hsum20 : sum2 = 0#i128 := by rw [hsum2]; exact i128_saturating_sub_zero
      step as ⟨j2, hj2⟩
      exact ⟨hsum20, by rw [hj2, hnext]; omega⟩
    · simp
  · rfl

@[step]
theorem solve_ldlt_loop0_total (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (rhs y : Array Std.I128 16#usize) (i : Std.Usize) :
    blue.solve_ldlt_loop0 dim l_q32 rhs y i ⦃ _ => True ⦄ := by
  unfold blue.solve_ldlt_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I128 16#usize × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨y1, i1⟩ _
    unfold blue.solve_ldlt_loop0.body
    simp only
    split
    · have hlt : i1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s⟩
      step as ⟨sum⟩
      step as ⟨sum1⟩
      step as ⟨s1, back⟩
      step as ⟨o, get_back⟩
      have hy2 :
          (match o with
            | none => ok (back (get_back none))
            | some _ => ok (back (get_back (some sum1)))) ⦃ _ => True ⦄ := by
        cases o <;> simp
      apply WP.spec_bind hy2
      intro y2 _
      step as ⟨i2, hi2⟩
      rw [hi2, hnext]; omega
    · simp
  · trivial

theorem solve_ldlt_loop0_zero (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (rhs y : Array Std.I128 16#usize) (i : Std.Usize)
    (hrhs : AllZero16 rhs) (hy : AllZero16 y) :
    blue.solve_ldlt_loop0 dim l_q32 rhs y i ⦃ r => AllZero16 r ⦄ := by
  unfold blue.solve_ldlt_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I128 16#usize × Std.Usize => dim.val - x.2.val)
    (inv := fun x => AllZero16 x.1)
  · rintro ⟨y1, i1⟩ hy1
    dsimp only at hy1
    unfold blue.solve_ldlt_loop0.body
    simp only
    split
    · have hlt : i1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s, hs⟩
      step as ⟨sum, hsum⟩
      have hsum0 : sum = 0#i128 := by
        rw [hsum, hs]
        cases hget : (Array.to_slice rhs)[i1]? with
        | none => rfl
        | some v => exact hrhs i1 v hget
      subst hsum0
      step with solve_ldlt_loop0_loop0_zero dim l_q32 y1 i1 0#usize hy1 as ⟨sum1, hsum1⟩
      subst hsum1
      simp only [lift, bind_ok, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
        Std.uncurry]
      cases hget : (Array.to_slice_mut y1).1[i1]? with
      | none =>
        simp only [bind_ok, WP.spec_ok]
        exact ⟨allZero16_set_zero y1 i1 hy1 none (fun _ h => by cases h), by rw [hnext]; omega⟩
      | some old =>
        simp only [bind_ok, WP.spec_ok]
        exact ⟨allZero16_set_zero y1 i1 hy1 (some 0#i128) (fun _ h => (Option.some.inj h).symm),
          by rw [hnext]; omega⟩
    · simp [hy1]
  · exact hy

@[step]
theorem solve_ldlt_loop1_total (dim : Std.Usize) (d_q32 : Array Std.I128 16#usize)
    (scale_shift : Std.U32) (y z : Array Std.I128 16#usize) (k : Std.Usize) :
    blue.solve_ldlt_loop1 dim d_q32 scale_shift y z k ⦃ _ => True ⦄ := by
  unfold blue.solve_ldlt_loop1
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I128 16#usize × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨z1, k1⟩ _
    unfold blue.solve_ldlt_loop1.body
    simp only
    split
    · have hlt : k1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add k1 1#usize).val = k1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s⟩
      step as ⟨dk⟩
      step as ⟨s1⟩
      step as ⟨yk⟩
      step as ⟨zk⟩
      step as ⟨s2, back⟩
      step as ⟨o, get_back⟩
      have hz2 :
          (match o with
            | none => ok (back (get_back none))
            | some _ => ok (back (get_back (some zk)))) ⦃ _ => True ⦄ := by
        cases o <;> simp
      apply WP.spec_bind hz2
      intro z2 _
      step as ⟨k2, hk2⟩
      rw [hk2, hnext]; omega
    · simp
  · trivial

theorem solve_ldlt_loop1_zero (dim : Std.Usize) (d_q32 : Array Std.I128 16#usize)
    (scale_shift : Std.U32) (y z : Array Std.I128 16#usize) (k : Std.Usize)
    (hy : AllZero16 y) (hz : AllZero16 z) :
    blue.solve_ldlt_loop1 dim d_q32 scale_shift y z k ⦃ r => AllZero16 r ⦄ := by
  unfold blue.solve_ldlt_loop1
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I128 16#usize × Std.Usize => dim.val - x.2.val)
    (inv := fun x => AllZero16 x.1)
  · rintro ⟨z1, k1⟩ hz1
    dsimp only at hz1
    unfold blue.solve_ldlt_loop1.body
    simp only
    split
    · have hlt : k1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add k1 1#usize).val = k1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s⟩
      step as ⟨dk⟩
      step as ⟨s1, hs1⟩
      step as ⟨yk, hyk⟩
      have hyk0 : yk = 0#i128 := by
        rw [hyk, hs1]
        cases hget : (Array.to_slice y)[k1]? with
        | none => rfl
        | some v => exact hy k1 v hget
      subst hyk0
      step with Fixed.scale_div_pow2_spec 0#i128 scale_shift dk as ⟨zk, hzk_le, hzk_pos⟩
      have hzk0 : zk = 0#i128 := by
        by_cases hdk : dk.val ≤ 0
        · exact IScalar.eq_of_val_eq (hzk_le hdk)
        · have hpos : 0 < dk.val := by omega
          have hq := hzk_pos hpos
          simp only [Fixed.clamp128, Int.zero_mul, Int.zero_ediv] at hq
          exact IScalar.eq_of_val_eq (by change zk.val = 0; omega)
      subst hzk0
      simp only [lift, bind_ok, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
        Std.uncurry]
      cases hget : (Array.to_slice_mut z1).1[k1]? with
      | none =>
        simp only [bind_ok, WP.spec_ok]
        exact ⟨allZero16_set_zero z1 k1 hz1 none (fun _ h => by cases h), by rw [hnext]; omega⟩
      | some old =>
        simp only [bind_ok, WP.spec_ok]
        exact ⟨allZero16_set_zero z1 k1 hz1 (some 0#i128) (fun _ h => (Option.some.inj h).symm),
          by rw [hnext]; omega⟩
    · simp [hz1]
  · exact hz

@[step]
theorem solve_ldlt_loop2_loop0_total (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (x : Array Std.I128 16#usize) (rev : Std.Usize) (sum : Std.I128) (j : Std.Usize) :
    blue.solve_ldlt_loop2_loop0 dim l_q32 x rev sum j ⦃ _ => True ⦄ := by
  unfold blue.solve_ldlt_loop2_loop0
  apply loop.spec_decr_nat
    (measure := fun p : Std.I128 × Std.Usize => dim.val - p.2.val)
    (inv := fun _ => True)
  · rintro ⟨sum1, j1⟩ _
    unfold blue.solve_ldlt_loop2_loop0.body
    simp only
    split
    · have hlt : j1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add j1 1#usize).val = j1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step*
    · simp
  · trivial

theorem solve_ldlt_loop2_loop0_zero (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (x : Array Std.I128 16#usize) (rev j : Std.Usize) (hx : AllZero16 x) :
    blue.solve_ldlt_loop2_loop0 dim l_q32 x rev 0#i128 j ⦃ r => r = 0#i128 ⦄ := by
  unfold blue.solve_ldlt_loop2_loop0
  apply loop.spec_decr_nat
    (measure := fun p : Std.I128 × Std.Usize => dim.val - p.2.val)
    (inv := fun p => p.1 = 0#i128)
  · rintro ⟨sum1, j1⟩ hsum
    dsimp only at hsum
    subst hsum
    unfold blue.solve_ldlt_loop2_loop0.body
    simp only
    split
    · have hlt : j1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add j1 1#usize).val = j1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s⟩
      step as ⟨i⟩
      step as ⟨i1⟩
      step as ⟨i2⟩
      step as ⟨lji⟩
      step as ⟨s1, hs1⟩
      step as ⟨xj, hxj⟩
      have hxj0 : xj = 0#i128 := by
        rw [hxj, hs1]
        cases hget : (Array.to_slice x)[j1]? with
        | none => rfl
        | some v => exact hx j1 v hget
      subst hxj0
      step with Fixed.saturating_mul_i128_spec lji 0#i128 as ⟨prod, hprod⟩
      have hprod0 : prod = 0#i128 := by
        have hv : prod.val = 0 := by rw [hprod]; simp [Fixed.clamp128]
        exact IScalar.eq_of_val_eq hv
      subst hprod0
      step as ⟨term, hterm⟩
      have hterm0 : term = 0#i128 := by rw [hterm]; exact i128_wrapping_shr_zero 32#u32
      subst hterm0
      step as ⟨sum2, hsum2⟩
      have hsum20 : sum2 = 0#i128 := by rw [hsum2]; exact i128_saturating_sub_zero
      step as ⟨j2, hj2⟩
      exact ⟨hsum20, by rw [hj2, hnext]; omega⟩
    · simp
  · rfl

@[step]
theorem solve_ldlt_loop2_total (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (z x : Array Std.I128 16#usize) (rev : Std.Usize) :
    blue.solve_ldlt_loop2 dim l_q32 z x rev ⦃ _ => True ⦄ := by
  unfold blue.solve_ldlt_loop2
  apply loop.spec_decr_nat
    (measure := fun p : Array Std.I128 16#usize × Std.Usize => p.2.val)
    (inv := fun _ => True)
  · rintro ⟨x1, rev1⟩ _
    unfold blue.solve_ldlt_loop2.body
    simp only
    split
    · have hpos : 0 < rev1.val := by scalar_tac
      have hprev := usize_wrapping_sub_one_val rev1 hpos
      step as ⟨rev2, hrev2⟩
      step as ⟨s⟩
      step as ⟨sum⟩
      step as ⟨j⟩
      step as ⟨sum1⟩
      step as ⟨s1, back⟩
      step as ⟨o, get_back⟩
      cases o <;> (simp only [WP.spec_ok]; rw [hrev2, hprev]; omega)
    · simp
  · trivial

theorem solve_ldlt_loop2_zero (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (z x : Array Std.I128 16#usize) (rev : Std.Usize)
    (hz : AllZero16 z) (hx : AllZero16 x) :
    blue.solve_ldlt_loop2 dim l_q32 z x rev ⦃ r => AllZero16 r ⦄ := by
  unfold blue.solve_ldlt_loop2
  apply loop.spec_decr_nat
    (measure := fun p : Array Std.I128 16#usize × Std.Usize => p.2.val)
    (inv := fun p => AllZero16 p.1)
  · rintro ⟨x1, rev1⟩ hx1
    dsimp only at hx1
    unfold blue.solve_ldlt_loop2.body
    simp only
    split
    · have hpos : 0 < rev1.val := by scalar_tac
      have hprev := usize_wrapping_sub_one_val rev1 hpos
      step as ⟨rev2, hrev2⟩
      step as ⟨s, hs⟩
      step as ⟨sum, hsum⟩
      have hsum0 : sum = 0#i128 := by
        rw [hsum, hs]
        cases hget : (Array.to_slice z)[rev2]? with
        | none => rfl
        | some v => exact hz rev2 v hget
      subst hsum0
      step as ⟨j⟩
      step with solve_ldlt_loop2_loop0_zero dim l_q32 x1 rev2 j hx1 as ⟨sum1, hsum1⟩
      subst hsum1
      simp only [lift, bind_ok, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut,
        Std.uncurry]
      cases hget : (Array.to_slice_mut x1).1[rev2]? with
      | none =>
        simp only [WP.spec_ok]
        exact ⟨allZero16_set_zero x1 rev2 hx1 none (fun _ h => by cases h),
          by rw [hrev2, hprev]; omega⟩
      | some old =>
        simp only [WP.spec_ok]
        exact ⟨allZero16_set_zero x1 rev2 hx1 (some 0#i128) (fun _ h => (Option.some.inj h).symm),
          by rw [hrev2, hprev]; omega⟩
    · simp [hx1]
  · exact hx

@[step]
theorem solve_ldlt_total (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (d_q32 rhs : Array Std.I128 16#usize) (scale_shift : Std.U32) :
    blue.solve_ldlt dim l_q32 d_q32 rhs scale_shift ⦃ _ => True ⦄ := by
  unfold blue.solve_ldlt
  step*

/-- **Zero-RHS fixed-point preservation:** solving `(L D Lᵀ) x = 0` via
`solve_ldlt` always returns the all-zero vector, for any factors `L`, `D`,
dimension, and shift. In `solve_blue`, this guarantees that noiseless
spanning-tree measurements produce zero residual correction `delta_phi = 0`. -/
theorem solve_ldlt_zero_rhs (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (d_q32 rhs : Array Std.I128 16#usize) (scale_shift : Std.U32)
    (hrhs : AllZero16 rhs) :
    blue.solve_ldlt dim l_q32 d_q32 rhs scale_shift ⦃ x => AllZero16 x ⦄ := by
  unfold blue.solve_ldlt
  step with solve_ldlt_loop0_zero dim l_q32 rhs _ 0#usize hrhs allZero16_repeat as ⟨y1, hy1⟩
  step with solve_ldlt_loop1_zero dim d_q32 scale_shift y1 _ 0#usize hy1 allZero16_repeat as ⟨z1, hz1⟩
  exact solve_ldlt_loop2_zero dim l_q32 z1 _ dim hz1 allZero16_repeat

/-! ## `solve_blue` loops and global invariants -/

@[step]
theorem solve_blue_loop0_loop0_total (edges : Slice blue.EdgeObs)
    (hosts n_edges : Std.Usize) (reachable : Array Bool 17#usize)
    (tree_off : Array Std.I64 17#usize) (queue : Array Std.Usize 17#usize)
    (q_tail cur : Std.Usize) (cur_off : Std.I64) (e : Std.Usize) :
    blue.solve_blue_loop0_loop0 edges hosts n_edges reachable tree_off queue q_tail
      cur cur_off e ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Array Bool 17#usize × Array Std.I64 17#usize ×
        Array Std.Usize 17#usize × Std.Usize × Std.Usize => n_edges.val - x.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨r1, t1, q1, qt1, e1⟩ _
    unfold blue.solve_blue_loop0_loop0.body
    dsimp only
    by_cases hlt_c : e1 < n_edges
    · simp only [hlt_c, ↓reduceIte]
      have hlt : e1.val < n_edges.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add e1 1#usize).val = e1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o⟩
      have hupd :
          (match o with
            | none => ok (r1, t1, q1, qt1)
            | some edge =>
              if edge.variance_ns2 > 0#u64 then
                if edge.from < hosts then
                  if edge.to < hosts then
                    if edge.from != edge.to then
                      if edge.from = cur then do
                        let s ← lift (Array.to_slice r1)
                        let b ← blue.get_bool s edge.to
                        if b then
                          if edge.to = cur then do
                            let s1 ← lift (Array.to_slice r1)
                            let b1 ← blue.get_bool s1 edge.from
                            if b1 then ok (r1, t1, q1, qt1)
                            else do
                              let (s2, back) ← lift (Array.to_slice_mut r1)
                              let (o1, gb) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Bool) s2 edge.from
                              let r2 ← match o1 with | none => ok (back (gb none)) | some _ => ok (back (gb (some true)))
                              let (s3, back1) ← lift (Array.to_slice_mut t1)
                              let (o2, gb1) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.I64) s3 edge.from
                              let t2 ← match o2 with | none => ok (back1 (gb1 none)) | some _ => do let t ← lift (core.num.I64.saturating_sub cur_off edge.offset_ns); ok (back1 (gb1 (some t)))
                              let (s4, back2) ← lift (Array.to_slice_mut q1)
                              let (o3, gb2) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.Usize) s4 qt1
                              let (a, i) ← match o3 with | none => ok (back2 (gb2 none), qt1) | some _ => do let qt2 ← lift (core.num.Usize.saturating_add qt1 1#usize); ok (back2 (gb2 (some edge.from)), qt2)
                              ok (r2, t2, a, i)
                          else ok (r1, t1, q1, qt1)
                        else do
                          let (s1, back) ← lift (Array.to_slice_mut r1)
                          let (o1, gb) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Bool) s1 edge.to
                          let r2 ← match o1 with | none => ok (back (gb none)) | some _ => ok (back (gb (some true)))
                          let (s2, back1) ← lift (Array.to_slice_mut t1)
                          let (o2, gb1) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.I64) s2 edge.to
                          let t2 ← match o2 with | none => ok (back1 (gb1 none)) | some _ => do let t ← lift (core.num.I64.saturating_add cur_off edge.offset_ns); ok (back1 (gb1 (some t)))
                          let (s3, back2) ← lift (Array.to_slice_mut q1)
                          let (o3, gb2) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.Usize) s3 qt1
                          let (a, i) ← match o3 with | none => ok (back2 (gb2 none), qt1) | some _ => do let qt2 ← lift (core.num.Usize.saturating_add qt1 1#usize); ok (back2 (gb2 (some edge.to)), qt2)
                          ok (r2, t2, a, i)
                      else
                        if edge.to = cur then do
                          let s ← lift (Array.to_slice r1)
                          let b ← blue.get_bool s edge.from
                          if b then ok (r1, t1, q1, qt1)
                          else do
                            let (s1, back) ← lift (Array.to_slice_mut r1)
                            let (o1, gb) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Bool) s1 edge.from
                            let r2 ← match o1 with | none => ok (back (gb none)) | some _ => ok (back (gb (some true)))
                            let (s2, back1) ← lift (Array.to_slice_mut t1)
                            let (o2, gb1) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.I64) s2 edge.from
                            let t2 ← match o2 with | none => ok (back1 (gb1 none)) | some _ => do let t ← lift (core.num.I64.saturating_sub cur_off edge.offset_ns); ok (back1 (gb1 (some t)))
                            let (s3, back2) ← lift (Array.to_slice_mut q1)
                            let (o3, gb2) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.Usize) s3 qt1
                            let (a, i) ← match o3 with | none => ok (back2 (gb2 none), qt1) | some _ => do let qt2 ← lift (core.num.Usize.saturating_add qt1 1#usize); ok (back2 (gb2 (some edge.from)), qt2)
                            ok (r2, t2, a, i)
                        else ok (r1, t1, q1, qt1)
                    else ok (r1, t1, q1, qt1)
                  else ok (r1, t1, q1, qt1)
                else ok (r1, t1, q1, qt1)
              else ok (r1, t1, q1, qt1)) ⦃ _ => True ⦄ := by
        cases o with
        | none => simp
        | some edge =>
          dsimp only
          split
          · split
            · split
              · split
                · split
                  · step as ⟨s⟩
                    step as ⟨b⟩
                    split
                    · split
                      · step as ⟨s1⟩
                        step as ⟨b1⟩
                        split
                        · simp
                        · step as ⟨s2, back⟩; step as ⟨o1, gb⟩
                          have hr2 : (match o1 with | none => ok (back (gb none)) | some _ => ok (back (gb (some true)))) ⦃ _ => True ⦄ := by cases o1 <;> simp
                          apply WP.spec_bind hr2; intro r2 _
                          step as ⟨s3, back1⟩; step as ⟨o2, gb1⟩
                          have ht2 : (match o2 with | none => ok (back1 (gb1 none)) | some _ => do let t ← lift (core.num.I64.saturating_sub cur_off edge.offset_ns); ok (back1 (gb1 (some t)))) ⦃ _ => True ⦄ := by cases o2 <;> step*
                          apply WP.spec_bind ht2; intro t2 _
                          step as ⟨s4, back2⟩; step as ⟨o3, gb2⟩
                          have hq2 : (match o3 with | none => ok (back2 (gb2 none), qt1) | some _ => do let qt2 ← lift (core.num.Usize.saturating_add qt1 1#usize); ok (back2 (gb2 (some edge.from)), qt2)) ⦃ _ => True ⦄ := by cases o3 <;> step*
                          apply WP.spec_bind hq2; rintro ⟨a, i⟩ _; simp
                      · simp
                    · step as ⟨s1, back⟩; step as ⟨o1, gb⟩
                      have hr2 : (match o1 with | none => ok (back (gb none)) | some _ => ok (back (gb (some true)))) ⦃ _ => True ⦄ := by cases o1 <;> simp
                      apply WP.spec_bind hr2; intro r2 _
                      step as ⟨s2, back1⟩; step as ⟨o2, gb1⟩
                      have ht2 : (match o2 with | none => ok (back1 (gb1 none)) | some _ => do let t ← lift (core.num.I64.saturating_add cur_off edge.offset_ns); ok (back1 (gb1 (some t)))) ⦃ _ => True ⦄ := by cases o2 <;> step*
                      apply WP.spec_bind ht2; intro t2 _
                      step as ⟨s3, back2⟩; step as ⟨o3, gb2⟩
                      have hq2 : (match o3 with | none => ok (back2 (gb2 none), qt1) | some _ => do let qt2 ← lift (core.num.Usize.saturating_add qt1 1#usize); ok (back2 (gb2 (some edge.to)), qt2)) ⦃ _ => True ⦄ := by cases o3 <;> step*
                      apply WP.spec_bind hq2; rintro ⟨a, i⟩ _; simp
                  · split
                    · step as ⟨s⟩
                      step as ⟨b⟩
                      split
                      · simp
                      · step as ⟨s1, back⟩; step as ⟨o1, gb⟩
                        have hr2 : (match o1 with | none => ok (back (gb none)) | some _ => ok (back (gb (some true)))) ⦃ _ => True ⦄ := by cases o1 <;> simp
                        apply WP.spec_bind hr2; intro r2 _
                        step as ⟨s2, back1⟩; step as ⟨o2, gb1⟩
                        have ht2 : (match o2 with | none => ok (back1 (gb1 none)) | some _ => do let t ← lift (core.num.I64.saturating_sub cur_off edge.offset_ns); ok (back1 (gb1 (some t)))) ⦃ _ => True ⦄ := by cases o2 <;> step*
                        apply WP.spec_bind ht2; intro t2 _
                        step as ⟨s3, back2⟩; step as ⟨o3, gb2⟩
                        have hq2 : (match o3 with | none => ok (back2 (gb2 none), qt1) | some _ => do let qt2 ← lift (core.num.Usize.saturating_add qt1 1#usize); ok (back2 (gb2 (some edge.from)), qt2)) ⦃ _ => True ⦄ := by cases o3 <;> step*
                        apply WP.spec_bind hq2; rintro ⟨a, i⟩ _; simp
                    · simp
                · simp
              · simp
            · simp
          · simp
      apply WP.spec_bind hupd
      rintro ⟨r2, t2, q2, qt2⟩ _
      step as ⟨e2, he2⟩
      rw [he2, hnext]; omega
    · simp only [hlt_c, ↓reduceIte, WP.spec_ok]
  · trivial

@[step]
theorem solve_blue_loop0_total (edges : Slice blue.EdgeObs) (hosts n_edges : Std.Usize)
    (reachable : Array Bool 17#usize) (tree_off : Array Std.I64 17#usize)
    (queue : Array Std.Usize 17#usize) (q_head q_tail : Std.Usize) :
    blue.solve_blue_loop0 edges hosts n_edges reachable tree_off queue q_head q_tail
      ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Array Bool 17#usize × Array Std.I64 17#usize ×
        Array Std.Usize 17#usize × Std.Usize × Std.Usize => blue.MAX_HOSTS.val - x.2.2.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨r1, t1, q1, qh1, qt1⟩ _
    unfold blue.solve_blue_loop0.body
    simp only
    split
    · split
      · have hlt : qh1.val < blue.MAX_HOSTS.val := by scalar_tac
        have hnext : (core.num.Usize.saturating_add qh1 1#usize).val = qh1.val + 1 :=
          Usize.saturating_add_val _ _ (by scalar_tac)
        step*
      · simp
    · simp
  · trivial

@[step]
theorem solve_blue_loop1_spec (hosts : Std.Usize) (reachable : Array Bool 17#usize)
    (host_to_idx : Array Std.Usize 17#usize) (idx_to_host : Array Std.Usize 16#usize)
    (dim h : Std.Usize) (hdim : dim.val ≤ blue.MAX_PEERS.val) :
    blue.solve_blue_loop1 hosts reachable host_to_idx idx_to_host dim h
      ⦃ r => r.2.2.val ≤ blue.MAX_PEERS.val ⦄ := by
  unfold blue.solve_blue_loop1
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.Usize 17#usize × Array Std.Usize 16#usize ×
        Std.Usize × Std.Usize => hosts.val - x.2.2.2.val)
    (inv := fun x => x.2.2.1.val ≤ blue.MAX_PEERS.val)
  · rintro ⟨hti1, ith1, dim1, h1⟩ hdim1
    dsimp only at hdim1
    unfold blue.solve_blue_loop1.body
    simp only
    split
    · split
      · have hlt : h1.val < hosts.val := by scalar_tac
        have hdlt : dim1.val < blue.MAX_PEERS.val := by scalar_tac
        have hnext : (core.num.Usize.saturating_add h1 1#usize).val = h1.val + 1 :=
          Usize.saturating_add_val _ _ (by scalar_tac)
        step as ⟨s⟩
        step as ⟨b⟩
        have hstep :
            (if b = true then do
              let (s1, back) ← lift (Array.to_slice_mut hti1)
              let (o, gb) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.Usize) s1 h1
              let hti2 ← match o with | none => ok (back (gb none)) | some _ => ok (back (gb (some dim1)))
              let (s2, back1) ← lift (Array.to_slice_mut ith1)
              let (o1, gb1) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.Usize) s2 dim1
              let ith2 ← match o1 with | none => ok (back1 (gb1 none)) | some _ => ok (back1 (gb1 (some h1)))
              let dim2 ← lift (core.num.Usize.saturating_add dim1 1#usize)
              ok (hti2, ith2, dim2)
            else ok (hti1, ith1, dim1))
              ⦃ p => p.2.2.val ≤ blue.MAX_PEERS.val ⦄ := by
          split
          · step as ⟨s1, back⟩; step as ⟨o, gb⟩
            have h1' : (match o with | none => ok (back (gb none)) | some _ => ok (back (gb (some dim1)))) ⦃ _ => True ⦄ := by cases o <;> simp
            apply WP.spec_bind h1'; intro hti2 _
            step as ⟨s2, back1⟩; step as ⟨o1, gb1⟩
            have h2' : (match o1 with | none => ok (back1 (gb1 none)) | some _ => ok (back1 (gb1 (some h1)))) ⦃ _ => True ⦄ := by cases o1 <;> simp
            apply WP.spec_bind h2'; intro ith2 _
            step as ⟨dim2, hdim2⟩
            have hadd : (core.num.Usize.saturating_add dim1 1#usize).val = dim1.val + 1 :=
              Usize.saturating_add_val _ _ (by scalar_tac)
            rw [hdim2, hadd]; omega
          · simp [hdim1]
        apply WP.spec_bind hstep
        rintro ⟨hti2, ith2, dim2⟩ hdim2
        step as ⟨h2, hh2⟩
        exact ⟨hdim2, by rw [hh2, hnext]; omega⟩
      · simp [hdim1]
    · simp [hdim1]
  · exact hdim

@[step]
theorem solve_blue_loop2_total (edges : Slice blue.EdgeObs) (hosts n_edges : Std.Usize)
    (reachable : Array Bool 17#usize) (v_min : Std.U64) (e : Std.Usize) :
    blue.solve_blue_loop2 edges hosts n_edges reachable v_min e ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop2
  apply loop.spec_decr_nat
    (measure := fun x : Std.U64 × Std.Usize => n_edges.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨vm1, e1⟩ _
    unfold blue.solve_blue_loop2.body
    simp only
    split
    · have hlt : e1.val < n_edges.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add e1 1#usize).val = e1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o⟩
      have hvm :
          (match o with
            | none => ok vm1
            | some edge =>
              if edge.variance_ns2 > 0#u64 then
                if edge.from < hosts then
                  if edge.to < hosts then
                    if edge.from != edge.to then do
                      let s ← lift (Array.to_slice reachable)
                      let b ← blue.get_bool s edge.from
                      if b then do
                        let s1 ← lift (Array.to_slice reachable)
                        let b1 ← blue.get_bool s1 edge.to
                        if b1 then
                          if vm1 = 0#u64 then ok edge.variance_ns2
                          else if edge.variance_ns2 < vm1 then ok edge.variance_ns2
                          else ok vm1
                        else ok vm1
                      else ok vm1
                    else ok vm1
                  else ok vm1
                else ok vm1
              else ok vm1) ⦃ _ => True ⦄ := by
        cases o with
        | none => simp
        | some edge =>
          dsimp only
          split
          · split
            · split
              · split
                · step as ⟨s⟩; step as ⟨b⟩
                  split
                  · step as ⟨s1⟩; step as ⟨b1⟩
                    split
                    · split
                      · simp
                      · split <;> simp
                    · simp
                  · simp
                · simp
              · simp
            · simp
          · simp
      apply WP.spec_bind hvm
      intro vm2 _
      step as ⟨e2, he2⟩
      rw [he2, hnext]; omega
    · simp
  · trivial

@[step]
theorem solve_blue_loop3_total (edges : Slice blue.EdgeObs) (hosts n_edges : Std.Usize)
    (reachable : Array Bool 17#usize) (tree_off : Array Std.I64 17#usize)
    (host_to_idx : Array Std.Usize 17#usize) (dim : Std.Usize) (v_min : Std.U64)
    (mat : Array Std.I128 256#usize) (rhs : Array Std.I128 16#usize) (e : Std.Usize) :
    blue.solve_blue_loop3 edges hosts n_edges reachable tree_off host_to_idx dim v_min
      mat rhs e ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop3
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I128 256#usize × Array Std.I128 16#usize × Std.Usize =>
      n_edges.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨m1, r1, e1⟩ _
    unfold blue.solve_blue_loop3.body
    dsimp only
    by_cases hlt_c : e1 < n_edges
    · simp only [hlt_c, ↓reduceIte]
      have hlt : e1.val < n_edges.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add e1 1#usize).val = e1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨o⟩
      have hpair :
          (match o with
            | none => ok (m1, r1)
            | some edge =>
              if edge.variance_ns2 > 0#u64 then
                if edge.from < hosts then
                  if edge.to < hosts then
                    if edge.from != edge.to then do
                      let s ← lift (Array.to_slice reachable)
                      let b ← blue.get_bool s edge.from
                      if b then do
                        let s1 ← lift (Array.to_slice reachable)
                        let b1 ← blue.get_bool s1 edge.to
                        if b1 then do
                          let i ← lift (UScalar.hcast .I128 v_min)
                          let i1 ← lift (UScalar.hcast .I128 edge.variance_ns2)
                          let w_raw ← fixed.scale_div_pow2 i 32#u32 i1
                          let w ← if w_raw < 1#i128 then ok 1#i128
                            else if w_raw > blue.Q32_ONE then ok blue.Q32_ONE else ok w_raw
                          let s2 ← lift (Array.to_slice tree_off)
                          let i2 ← blue.get_i64 s2 edge.to
                          let i3 ← lift (IScalar.cast .I128 i2)
                          let s3 ← lift (Array.to_slice tree_off)
                          let i4 ← blue.get_i64 s3 edge.from
                          let i5 ← lift (IScalar.cast .I128 i4)
                          let tree_diff ← lift (core.num.I128.wrapping_sub i3 i5)
                          let i6 ← lift (IScalar.cast .I128 edge.offset_ns)
                          let i7 ← lift (core.num.I128.wrapping_sub i6 tree_diff)
                          let res ← blue.clamp_sym i7 blue.MAX_RESIDUAL_NS
                          let wr ← fixed.saturating_mul_i128 w res
                          let s4 ← lift (Array.to_slice host_to_idx)
                          let u ← blue.get_usize s4 edge.from
                          let s5 ← lift (Array.to_slice host_to_idx)
                          let v ← blue.get_usize s5 edge.to
                          let (mat2, rhs2) ←
                            if edge.from != 0#usize then
                              if u < dim then do
                                let mat3 ← blue.mat_add m1 dim u u w
                                let (s6, back) ← lift (Array.to_slice_mut r1)
                                let (o1, gb) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.I128) s6 u
                                let a ← match o1 with
                                  | none => ok (back (gb none))
                                  | some b2 => do let b3 ← lift (core.num.I128.saturating_sub b2 wr); ok (back (gb (some b3)))
                                ok (mat3, a)
                              else ok (m1, r1)
                            else ok (m1, r1)
                          let (mat3, rhs3) ←
                            if edge.to != 0#usize then
                              if v < dim then do
                                let mat4 ← blue.mat_add mat2 dim v v w
                                let (s6, back) ← lift (Array.to_slice_mut rhs2)
                                let (o1, gb) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.I128) s6 v
                                let a ← match o1 with
                                  | none => ok (back (gb none))
                                  | some b2 => do let b3 ← lift (core.num.I128.saturating_add b2 wr); ok (back (gb (some b3)))
                                ok (mat4, a)
                              else ok (mat2, rhs2)
                            else ok (mat2, rhs2)
                          let a ←
                            if edge.from != 0#usize then
                              if edge.to != 0#usize then
                                if u < dim then
                                  if v < dim then do
                                    let neg_w ← lift (core.num.I128.wrapping_sub 0#i128 w)
                                    let mat4 ← blue.mat_add mat3 dim u v neg_w
                                    blue.mat_add mat4 dim v u neg_w
                                  else ok mat3
                                else ok mat3
                              else ok mat3
                            else ok mat3
                          ok (a, rhs3)
                        else ok (m1, r1)
                      else ok (m1, r1)
                    else ok (m1, r1)
                  else ok (m1, r1)
                else ok (m1, r1)
              else ok (m1, r1)) ⦃ _ => True ⦄ := by
        cases o with
        | none => simp
        | some edge =>
          dsimp only
          by_cases hc1 : edge.variance_ns2 > 0#u64
          · simp only [hc1, ↓reduceIte]
            by_cases hc2 : edge.from < hosts
            · simp only [hc2, ↓reduceIte]
              by_cases hc3 : edge.to < hosts
              · simp only [hc3, ↓reduceIte]
                by_cases hc4 : edge.from != edge.to
                · simp only [hc4, ↓reduceIte]
                  step as ⟨s⟩; step as ⟨b⟩
                  by_cases hc5 : b = true
                  · simp only [hc5, ↓reduceIte]
                    step as ⟨s1⟩; step as ⟨b1⟩
                    by_cases hc6 : b1 = true
                    · simp only [hc6, ↓reduceIte]
                      step as ⟨i⟩; step as ⟨i1⟩; step as ⟨w_raw⟩
                      have hw : (if w_raw < 1#i128 then ok 1#i128 else if w_raw > blue.Q32_ONE then ok blue.Q32_ONE else ok w_raw) ⦃ _ => True ⦄ := by
                        split
                        · simp
                        · split <;> simp
                      apply WP.spec_bind hw; intro w _
                      step as ⟨s2⟩; step as ⟨i2⟩; step as ⟨i3⟩; step as ⟨s3⟩; step as ⟨i4⟩; step as ⟨i5⟩
                      step as ⟨td⟩; step as ⟨i6⟩; step as ⟨i7⟩; step as ⟨res⟩; step as ⟨wr⟩
                      step as ⟨s4⟩; step as ⟨u⟩; step as ⟨s5⟩; step as ⟨v⟩
                      have hmr2 :
                          (if edge.from != 0#usize then
                             if u < dim then do
                               let mat3 ← blue.mat_add m1 dim u u w
                               let (s6, back) ← lift (Array.to_slice_mut r1)
                               let (o1, gb) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.I128) s6 u
                               let a ← match o1 with | none => ok (back (gb none)) | some b2 => do let b3 ← lift (core.num.I128.saturating_sub b2 wr); ok (back (gb (some b3)))
                               ok (mat3, a)
                             else ok (m1, r1)
                           else ok (m1, r1)) ⦃ _ => True ⦄ := by
                        split
                        · split
                          · step as ⟨mat3⟩; step as ⟨s6, back⟩; step as ⟨o1, gb⟩
                            have ha : (match o1 with | none => ok (back (gb none)) | some b2 => do let b3 ← lift (core.num.I128.saturating_sub b2 wr); ok (back (gb (some b3)))) ⦃ _ => True ⦄ := by cases o1 <;> step*
                            apply WP.spec_bind ha; intro a _; simp
                          · simp
                        · simp
                      apply WP.spec_bind hmr2; rintro ⟨mat2, rhs2⟩ _
                      have hmr3 :
                          (if edge.to != 0#usize then
                             if v < dim then do
                               let mat4 ← blue.mat_add mat2 dim v v w
                               let (s6, back) ← lift (Array.to_slice_mut rhs2)
                               let (o1, gb) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Std.I128) s6 v
                               let a ← match o1 with | none => ok (back (gb none)) | some b2 => do let b3 ← lift (core.num.I128.saturating_add b2 wr); ok (back (gb (some b3)))
                               ok (mat4, a)
                             else ok (mat2, rhs2)
                           else ok (mat2, rhs2)) ⦃ _ => True ⦄ := by
                        split
                        · split
                          · step as ⟨mat4⟩; step as ⟨s6, back⟩; step as ⟨o1, gb⟩
                            have ha : (match o1 with | none => ok (back (gb none)) | some b2 => do let b3 ← lift (core.num.I128.saturating_add b2 wr); ok (back (gb (some b3)))) ⦃ _ => True ⦄ := by cases o1 <;> step*
                            apply WP.spec_bind ha; intro a _; simp
                          · simp
                        · simp
                      apply WP.spec_bind hmr3; rintro ⟨mat3, rhs3⟩ _
                      have ha3 :
                          (if edge.from != 0#usize then
                             if edge.to != 0#usize then
                               if u < dim then
                                 if v < dim then do
                                   let neg_w ← lift (core.num.I128.wrapping_sub 0#i128 w)
                                   let mat4 ← blue.mat_add mat3 dim u v neg_w
                                   blue.mat_add mat4 dim v u neg_w
                                 else ok mat3
                               else ok mat3
                             else ok mat3
                           else ok mat3) ⦃ _ => True ⦄ := by
                        split
                        · split
                          · split
                            · split
                              · step*
                              · simp
                            · simp
                          · simp
                        · simp
                      apply WP.spec_bind ha3; intro a _; simp
                    · rw [ite_f hc6, WP.spec_ok]; trivial
                  · rw [ite_f hc5, WP.spec_ok]; trivial
                · rw [ite_f hc4, WP.spec_ok]; trivial
              · rw [ite_f hc3, WP.spec_ok]; trivial
            · rw [ite_f hc2, WP.spec_ok]; trivial
          · rw [ite_f hc1, WP.spec_ok]; trivial
      apply WP.spec_bind hpair
      rintro ⟨m2, r2⟩ _
      step as ⟨e2, he2⟩
      rw [he2, hnext]; omega
    · simp only [hlt_c, ↓reduceIte, WP.spec_ok]
  · trivial

@[step]
theorem solve_blue_loop4_loop0_total (dim : Std.Usize) (l_q32 : Array Std.I64 256#usize)
    (d_q32 : Array Std.I128 16#usize) (j : Std.Usize) (dj : Std.I128) (k : Std.Usize) :
    blue.solve_blue_loop4_loop0 dim l_q32 d_q32 j dj k ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Std.I128 × Std.Usize => j.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨dj1, k1⟩ _
    unfold blue.solve_blue_loop4_loop0.body
    simp only
    split
    · have hlt : k1.val < j.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add k1 1#usize).val = k1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step*
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_loop1_loop0_total (dim : Std.Usize)
    (l_q32 : Array Std.I64 256#usize) (d_q32 : Array Std.I128 16#usize)
    (j i : Std.Usize) (sum : Std.I128) (k2 : Std.Usize) :
    blue.solve_blue_loop4_loop1_loop0 dim l_q32 d_q32 j i sum k2 ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun x : Std.I128 × Std.Usize => j.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨sum1, k21⟩ _
    unfold blue.solve_blue_loop4_loop1_loop0.body
    simp only
    split
    · have hlt : k21.val < j.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add k21 1#usize).val = k21.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step*
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_loop1_total (dim : Std.Usize) (mat : Array Std.I128 256#usize)
    (l_q32 : Array Std.I64 256#usize) (d_q32 : Array Std.I128 16#usize)
    (j : Std.Usize) (dj : Std.I128) (i : Std.Usize) :
    blue.solve_blue_loop4_loop1 dim mat l_q32 d_q32 j dj i ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop1
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I64 256#usize × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨l1, i1⟩ _
    unfold blue.solve_blue_loop4_loop1.body
    simp only
    split
    · have hlt : i1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨sum⟩
      step as ⟨sum1⟩
      step as ⟨lij⟩
      step as ⟨s, back⟩
      step as ⟨k1⟩
      step as ⟨k2⟩
      step as ⟨o, gb⟩
      have hl2 :
          (match o with
            | none => ok (back (gb none))
            | some _ => do let dst ← fixed.saturate lij; ok (back (gb (some dst))))
            ⦃ _ => True ⦄ := by
        cases o <;> step*
      apply WP.spec_bind hl2
      intro l2 _
      step as ⟨i2, hi2⟩
      rw [hi2, hnext]; omega
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_loop2_total (tree_off : Array Std.I64 17#usize)
    (idx_to_host : Array Std.Usize 16#usize) (dim : Std.Usize)
    (delta_phi : Array Std.I128 16#usize) (offsets_ns : Array Std.I64 17#usize)
    (idx : Std.Usize) :
    blue.solve_blue_loop4_loop2 tree_off idx_to_host dim delta_phi offsets_ns idx
      ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop2
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I64 17#usize × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨off1, idx1⟩ _
    unfold blue.solve_blue_loop4_loop2.body
    simp only
    split
    · have hlt : idx1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add idx1 1#usize).val = idx1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s⟩; step as ⟨host⟩; step as ⟨s1⟩; step as ⟨i⟩; step as ⟨base⟩
      step as ⟨s2⟩; step as ⟨d⟩; step as ⟨s3, back⟩; step as ⟨o, gb⟩
      have ho :
          (match o with
            | none => ok (back (gb none))
            | some _ => do let i1 ← lift (core.num.I128.saturating_add base d); let slot ← fixed.saturate i1; ok (back (gb (some slot))))
            ⦃ _ => True ⦄ := by
        cases o <;> step*
      apply WP.spec_bind ho
      intro off2 _
      step as ⟨idx2, hidx2⟩
      rw [hidx2, hnext]; omega
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_loop3_total (dim : Std.Usize) (rhs_ones : Array Std.I128 16#usize)
    (i_one : Std.Usize) :
    blue.solve_blue_loop4_loop3 dim rhs_ones i_one ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop3
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I128 16#usize × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨ro1, i1⟩ _
    unfold blue.solve_blue_loop4_loop3.body
    simp only
    split
    · have hlt : i1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨s, back⟩; step as ⟨o, gb⟩
      have ho :
          (match o with | none => ok (back (gb none)) | some _ => ok (back (gb (some blue.Q32_ONE))))
            ⦃ _ => True ⦄ := by
        cases o <;> simp
      apply WP.spec_bind ho; intro ro2 _
      step as ⟨i2, hi2⟩; rw [hi2, hnext]; omega
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_loop4_total (dim : Std.Usize) (z_com : Array Std.I128 16#usize)
    (sum_z_com : Std.I128) (i_zc : Std.Usize) :
    blue.solve_blue_loop4_loop4 dim z_com sum_z_com i_zc ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop4
  apply loop.spec_decr_nat
    (measure := fun x : Std.I128 × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨s1, i1⟩ _
    unfold blue.solve_blue_loop4_loop4.body
    simp only
    split
    · have hlt : i1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step*
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_loop5_total (dim self_dense : Std.Usize)
    (rhs_diff : Array Std.I128 16#usize) (inv_dim_q32 : Std.I128) (i_d : Std.Usize) :
    blue.solve_blue_loop4_loop5 dim self_dense rhs_diff inv_dim_q32 i_d ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop5
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I128 16#usize × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨rd1, i1⟩ _
    unfold blue.solve_blue_loop4_loop5.body
    simp only
    split
    · have hlt : i1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      have hentry :
          (if i1 = self_dense then ok (core.num.I128.wrapping_sub blue.Q32_ONE inv_dim_q32)
           else ok (core.num.I128.wrapping_sub 0#i128 inv_dim_q32)) ⦃ _ => True ⦄ := by
        split <;> simp
      apply WP.spec_bind hentry; intro entry _
      step as ⟨s, back⟩; step as ⟨o, gb⟩
      have ho :
          (match o with | none => ok (back (gb none)) | some _ => ok (back (gb (some entry))))
            ⦃ _ => True ⦄ := by
        cases o <;> simp
      apply WP.spec_bind ho; intro rd2 _
      step as ⟨i2, hi2⟩; rw [hi2, hnext]; omega
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_loop6_total (dim : Std.Usize)
    (rhs_diff z_diff : Array Std.I128 16#usize) (quad_q32 : Std.I128) (i_q : Std.Usize) :
    blue.solve_blue_loop4_loop6 dim rhs_diff z_diff quad_q32 i_q ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop6
  apply loop.spec_decr_nat
    (measure := fun x : Std.I128 × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨q1, i1⟩ _
    unfold blue.solve_blue_loop4_loop6.body
    simp only
    split
    · have hlt : i1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step*
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_loop7_total (idx_to_host : Array Std.Usize 16#usize)
    (dim : Std.Usize) (offsets_ns : Array Std.I64 17#usize)
    (self_theta rel_sum : Std.I128) (i_m : Std.Usize) :
    blue.solve_blue_loop4_loop7 idx_to_host dim offsets_ns self_theta rel_sum i_m
      ⦃ _ => True ⦄ := by
  unfold blue.solve_blue_loop4_loop7
  apply loop.spec_decr_nat
    (measure := fun x : Std.I128 × Std.Usize => dim.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨rs1, i1⟩ _
    unfold blue.solve_blue_loop4_loop7.body
    simp only
    split
    · have hlt : i1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add i1 1#usize).val = i1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step*
    · simp
  · trivial

@[step]
theorem solve_blue_loop4_spec (self_idx : Std.Usize) (reachable : Array Bool 17#usize)
    (tree_off : Array Std.I64 17#usize) (idx_to_host : Array Std.Usize 16#usize)
    (dim self_dense : Std.Usize) (v_min : Std.U64)
    (mat : Array Std.I128 256#usize) (rhs : Array Std.I128 16#usize)
    (l_q32 : Array Std.I64 256#usize) (d_q32 : Array Std.I128 16#usize) (j : Std.Usize)
    (hdim_pos : 0 < dim.val) (hdim_le : dim.val ≤ blue.MAX_PEERS.val) :
    blue.solve_blue_loop4 self_idx reachable tree_off idx_to_host dim self_dense v_min
      mat rhs l_q32 d_q32 j ⦃ res =>
        res.active_count.val ≤ blue.MAX_PEERS.val
        ∧ (res.active_count = 0#usize → res = blue.BlueResult.EMPTY)
        ∧ (0 < res.active_count.val →
            1 ≤ res.common_var_ns2.val ∧ res.common_var_ns2.val ≤ blue.MAX_OUT_VAR_NS2.val)
        ∧ (res.active_count = 1#usize → res.self_diff_var_ns2 = 0#u64)
        ∧ (1 < res.active_count.val →
            1 ≤ res.self_diff_var_ns2.val ∧ res.self_diff_var_ns2.val ≤ blue.MAX_OUT_VAR_NS2.val) ⦄ := by
  unfold blue.solve_blue_loop4
  apply loop.spec_decr_nat
    (measure := fun x : Array Std.I64 256#usize × Array Std.I128 16#usize × Std.Usize =>
      dim.val - x.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨l1, d1, j1⟩ _
    unfold blue.solve_blue_loop4.body
    simp only
    split
    · have hlt : j1.val < dim.val := by scalar_tac
      have hnext : (core.num.Usize.saturating_add j1 1#usize).val = j1.val + 1 :=
        Usize.saturating_add_val _ _ (by scalar_tac)
      step as ⟨dj⟩
      step as ⟨dj1⟩
      split
      · simp [blue.BlueResult.EMPTY]
      · step as ⟨s, back⟩; step as ⟨o, gb⟩
        have hd2 : (match o with | none => ok (back (gb none)) | some _ => ok (back (gb (some dj1)))) ⦃ _ => True ⦄ := by cases o <;> simp
        apply WP.spec_bind hd2; intro d2 _
        step as ⟨s1, back1⟩; step as ⟨i⟩; step as ⟨i1⟩; step as ⟨o1, gb1⟩
        have hl2 : (match o1 with | none => ok (back1 (gb1 none)) | some _ => ok (back1 (gb1 (some 4294967296#i64)))) ⦃ _ => True ⦄ := by cases o1 <;> simp
        apply WP.spec_bind hl2; intro l2 _
        step as ⟨i2⟩
        step as ⟨l3⟩
        step as ⟨j2, hj2⟩
        rw [hj2, hnext]; omega
    · step as ⟨delta_phi⟩
      step as ⟨offsets_ns1⟩
      step as ⟨rhs_ones1⟩
      step as ⟨z_com⟩
      step as ⟨sum_z_com⟩
      step as ⟨i⟩; step as ⟨i1⟩; step as ⟨dim_sq⟩
      step as ⟨i2⟩; step as ⟨total_com⟩; step as ⟨i3⟩
      step with clamp_out_var_spec i3 as ⟨cv, hcv_lo, hcv_hi, _, _⟩
      step as ⟨i4⟩; step as ⟨inv_dim_q32⟩
      step as ⟨rhs_diff1⟩; step as ⟨z_diff⟩; step as ⟨quad_q32⟩
      have hdv :
          (if dim <= 1#usize then ok 0#u64
           else do
             let i5 ← lift (UScalar.hcast .I128 v_min)
             let i6 ← blue.mul_shr32 quad_q32 i5
             blue.clamp_out_var i6)
            ⦃ dv =>
              (dim = 1#usize → dv = 0#u64)
              ∧ (1 < dim.val → 1 ≤ dv.val ∧ dv.val ≤ blue.MAX_OUT_VAR_NS2.val) ⦄ := by
        split
        · rename_i hle
          rw [WP.spec_ok]
          refine ⟨fun _ => rfl, fun hgt => ?_⟩
          have : dim.val ≤ 1 := by scalar_tac
          omega
        · rename_i hgt
          step as ⟨i5⟩; step as ⟨i6⟩
          step with clamp_out_var_spec i6 as ⟨dv, hdv_lo, hdv_hi, _, _⟩
          refine ⟨fun h1 => ?_, fun _ => ⟨hdv_lo, hdv_hi⟩⟩
          exfalso; apply hgt; rw [h1]
      apply WP.spec_bind hdv
      intro dv ⟨hdv1, hdvgt⟩
      step as ⟨s⟩; step as ⟨i5⟩; step as ⟨i6⟩; step as ⟨self_theta⟩
      step as ⟨rel_sum⟩; step as ⟨i7⟩; step as ⟨delta_mean⟩
      step as ⟨i8⟩; step as ⟨common_offset_ns⟩
      step as ⟨i9⟩; step as ⟨self_diff_offset_ns⟩
      refine ⟨hdim_le, fun h0 => ?_, fun _ => ⟨hcv_lo, hcv_hi⟩, hdv1, hdvgt⟩
      exfalso; rw [h0] at hdim_pos; simp at hdim_pos
  · trivial

/-- **Totality and structural invariants of `solve_blue`:** the graph BLUE
solver always terminates without panicking, caps `active_count` at `MAX_PEERS`,
clamps positive output variances into `[1, MAX_OUT_VAR_NS2]`, and sets
`self_diff_var_ns2 = 0` whenever only a single speaker (`active_count = 1`) is
active (Star mode). -/
@[step]
theorem solve_blue_spec (host_count self_idx : Std.Usize) (edges : Slice blue.EdgeObs)
    (edge_count : Std.Usize) :
    blue.solve_blue host_count self_idx edges edge_count ⦃ res =>
      res.active_count.val ≤ blue.MAX_PEERS.val
      ∧ (res.active_count = 0#usize → res = blue.BlueResult.EMPTY)
      ∧ (0 < res.active_count.val →
          1 ≤ res.common_var_ns2.val ∧ res.common_var_ns2.val ≤ blue.MAX_OUT_VAR_NS2.val)
      ∧ (res.active_count = 1#usize → res.self_diff_var_ns2 = 0#u64)
      ∧ (1 < res.active_count.val →
          1 ≤ res.self_diff_var_ns2.val ∧ res.self_diff_var_ns2.val ≤ blue.MAX_OUT_VAR_NS2.val) ⦄ := by
  unfold blue.solve_blue
  have hhosts : (if host_count > blue.MAX_HOSTS then ok blue.MAX_HOSTS else ok host_count)
      ⦃ _ => True ⦄ := by split <;> simp
  apply WP.spec_bind hhosts; intro hosts _
  have hne : (if edge_count > Slice.len edges then ok (Slice.len edges) else ok edge_count)
      ⦃ _ => True ⦄ := by split <;> simp
  apply WP.spec_bind hne; intro n_edges _
  split
  · simp [blue.BlueResult.EMPTY]
  · split
    · simp [blue.BlueResult.EMPTY]
    · split
      · simp [blue.BlueResult.EMPTY]
      · split
        · simp [blue.BlueResult.EMPTY]
        · step as ⟨s, back⟩; step as ⟨o, gb⟩
          have hr1 : (match o with | none => ok (back (gb none)) | some _ => ok (back (gb (some true)))) ⦃ _ => True ⦄ := by cases o <;> simp
          apply WP.spec_bind hr1; intro reachable1 _
          step as ⟨s1, back1⟩; step as ⟨o1, gb1⟩
          have hq1 : (match o1 with | none => ok (back1 (gb1 none)) | some _ => ok (back1 (gb1 (some 0#usize)))) ⦃ _ => True ⦄ := by cases o1 <;> simp
          apply WP.spec_bind hq1; intro queue1 _
          step as ⟨reachable2, tree_off1⟩
          step as ⟨s2⟩; step as ⟨b⟩
          split
          · step with solve_blue_loop1_spec hosts reachable2 _ _ 0#usize 1#usize (by decide)
              as ⟨hti1, ith1, dim, hdim_le⟩
            step as ⟨s3⟩; step as ⟨self_dense⟩
            split
            · simp [blue.BlueResult.EMPTY]
            · rename_i hdim_ne
              have hdim_pos : 0 < dim.val := by
                cases Nat.eq_zero_or_pos dim.val with
                | inl hz => exfalso; apply hdim_ne; exact UScalar.eq_of_val_eq hz
                | inr hp => exact hp
              split
              · simp [blue.BlueResult.EMPTY]
              · step as ⟨v_min⟩
                split
                · simp [blue.BlueResult.EMPTY]
                · step as ⟨mat1, rhs1⟩
                  exact solve_blue_loop4_spec self_idx reachable2 tree_off1 ith1 dim
                    self_dense v_min mat1 rhs1 _ _ 0#usize hdim_pos hdim_le
          · simp [blue.BlueResult.EMPTY]

/-! ## Exact Star degeneration on a single-edge two-host graph -/

private theorem array_to_slice_mut_eq {T : Type} {n : Std.Usize} (a : Array T n) :
    Array.to_slice_mut a = (a.to_slice, a.from_slice) := by
  simp [Array.to_slice_mut]

private theorem array_from_slice_set_opt {T : Type} {n : Std.Usize} (a : Array T n)
    (i : Std.Usize) (x : Option T) :
    a.from_slice (a.to_slice.set_opt i x) = a.set_opt i x := by
  cases a
  simp [Array.from_slice, Array.to_slice, Array.set_opt, Slice.set_opt]

private theorem bind_ok_pair {α β γ : Type} (a : α) (b : β) (k : α → β → Result γ) :
    (do let (x, y) ← ok (a, b); k x y) = k a b := by simp [bind_ok]

private theorem bind_ok_quad {α β γ δ ε : Type} (a : α) (b : β) (c : γ) (d : δ)
    (k : α → β → γ → δ → Result ε) :
    (do let (x, y, z, w) ← ok (a, b, c, d); k x y z w) = k a b c d := by simp [bind_ok]

private theorem slice_get_mut_val {T : Type} (s : Slice T) (i : Std.Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice T) s i =
      ok (s[i]?, s.set_opt i) := rfl

/-- Helper tactic: step across `Array.to_slice_mut` + `Slice.get_mut` when the entry is `some _`. -/
local macro "mut_set" h:term : tactic =>
  `(tactic| (rw [array_to_slice_mut_eq, show lift (_, _) = ok (_, _) from rfl, bind_ok_pair];
             rw [slice_get_mut_val, bind_ok_pair];
             rw [($h : _)];
             try dsimp +zeta only;
             rw [array_from_slice_set_opt, bind_ok]))

private theorem single_edge_loop0 (d : Std.I64) (v : Std.U64) (hv : 0 < v.val) :
    let e : blue.EdgeObs := { «from» := 0#usize, «to» := 1#usize, offset_ns := d, variance_ns2 := v }
    let edges : Slice blue.EdgeObs := Slice.from [e] (by scalar_tac)
    let r_init := (Array.repeat 17#usize false).set_opt 0#usize (some true)
    let q_init := (Array.repeat 17#usize 0#usize).set_opt 0#usize (some 0#usize)
    let t_init := Array.repeat 17#usize 0#i64
    blue.solve_blue_loop0 edges 2#usize 1#usize r_init t_init q_init 0#usize 1#usize
      ⦃ p =>
        (Array.to_slice p.1)[0#usize]? = some true
        ∧ (Array.to_slice p.1)[1#usize]? = some true
        ∧ (Array.to_slice p.2)[0#usize]? = some 0#i64
        ∧ (Array.to_slice p.2)[1#usize]? = some d ⦄ := by
  intro e edges r_init q_init t_init
  have hd_hi : d.val ≤ 2^63 - 1 := by scalar_tac
  have hd_lo : -2^63 ≤ d.val := by scalar_tac
  have he0 : edges[0#usize]? = some e := by rw [Slice.getElem?_Usize_eq]; rfl
  have hv_gt : v > 0#u64 := by scalar_tac
  have hadd0_i64 : core.num.I64.saturating_add 0#i64 d = d := by
    apply IScalar.eq_of_val_eq
    rw [I64.saturating_add_val]; change max (-2^63) (min (2^63 - 1) (0 + d.val)) = d.val; omega
  unfold blue.solve_blue_loop0
  apply loop_step; unfold blue.solve_blue_loop0.body; dsimp only
  rw [ite_t (by decide), ite_t (by unfold blue.MAX_HOSTS; decide)]
  have hq0 : (Array.to_slice q_init)[0#usize]? = some 0#usize := by simp [q_init]
  have ht0 : (Array.to_slice t_init)[0#usize]? = some 0#i64 := by simp [t_init]
  step as ⟨s_q, hs_q⟩; step as ⟨cur, hcur⟩
  have hcur0 : cur = 0#usize := by rw [hcur, hs_q, hq0]
  subst hcur0
  step as ⟨qh1, hqh1⟩
  have hqh1_eq : qh1 = 1#usize := by
    rw [hqh1]; apply UScalar.eq_of_val_eq; exact usize_sat_add_one 0#usize (by decide)
  subst hqh1_eq
  step as ⟨s_t, hs_t⟩; step as ⟨coff, hcoff⟩
  have hcoff0 : coff = 0#i64 := by rw [hcoff, hs_t, ht0]
  subst hcoff0
  have hinner0 : blue.solve_blue_loop0_loop0 edges 2#usize 1#usize r_init t_init q_init 1#usize 0#usize 0#i64 0#usize
      ⦃ res =>
        (Array.to_slice res.1)[0#usize]? = some true
        ∧ (Array.to_slice res.1)[1#usize]? = some true
        ∧ (Array.to_slice res.2.1)[0#usize]? = some 0#i64
        ∧ (Array.to_slice res.2.1)[1#usize]? = some d
        ∧ (Array.to_slice res.2.2.1)[1#usize]? = some 1#usize
        ∧ res.2.2.2 = 2#usize ⦄ := by
    unfold blue.solve_blue_loop0_loop0
    apply loop_step; unfold blue.solve_blue_loop0_loop0.body; dsimp only
    rw [ite_t (by decide)]
    simp only [lift, bind_ok, core.slice.Slice.get, core.slice.index.Usize.get, he0]
    dsimp only [e]
    rw [ite_t hv_gt, ite_t (by decide), ite_t (by decide), ite_t (by decide), ite_t rfl]
    have hr1_false : (Array.to_slice r_init)[1#usize]? = some false := by simp [r_init]
    simp only [blue.get_bool, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok, hr1_false]
    rw [ite_f (by decide)]
    simp only [bind_ok, core.slice.Slice.get_mut, core.slice.index.Usize.get_mut, Std.uncurry]
    have ht1_0 : (Array.to_slice t_init)[1#usize]? = some 0#i64 := by simp [t_init]
    have hq1_0 : (Array.to_slice q_init)[1#usize]? = some 0#usize := by simp [q_init]
    rw [array_to_slice_mut_fst r_init, hr1_false]
    dsimp +zeta only
    rw [← array_to_slice_mut_fst r_init, array_to_slice_mut_set_opt]
    simp only [bind_ok]
    rw [array_to_slice_mut_fst t_init, ht1_0]
    dsimp +zeta only
    rw [← array_to_slice_mut_fst t_init, array_to_slice_mut_set_opt, hadd0_i64]
    simp only [bind_ok]
    rw [array_to_slice_mut_fst q_init, hq1_0]
    dsimp +zeta only
    rw [← array_to_slice_mut_fst q_init, array_to_slice_mut_set_opt]
    have h11 : core.num.Usize.saturating_add 1#usize 1#usize = 2#usize :=
      UScalar.eq_of_val_eq (usize_sat_add_one 1#usize (by decide))
    have h01 : core.num.Usize.saturating_add 0#usize 1#usize = 1#usize :=
      UScalar.eq_of_val_eq (usize_sat_add_one 0#usize (by decide))
    rw [h11, h01, bind_ok_pair, bind_ok_quad, WP.spec_ok]
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
    · rw [array_set_opt_get?]; simp [r_init]
    · rw [array_set_opt_get?]; simp [r_init]
    · rw [array_set_opt_get?]; simp [t_init]
    · rw [array_set_opt_get?]; simp [t_init]
    · rw [array_set_opt_get?]; simp [q_init]
  step with hinner0 as ⟨r2, t2, q2, qt2, hr2_0, hr2_1, ht2_0, ht2_1, hq2_1, hqt2⟩
  subst qt2
  apply loop_step; dsimp only
  rw [ite_t (by decide), ite_t (by unfold blue.MAX_HOSTS; decide)]
  step as ⟨sq2, hsq2⟩; step as ⟨cur2, hcur2⟩
  have hcur2_eq : cur2 = 1#usize := by rw [hcur2, hsq2, hq2_1]
  rw [hcur2_eq]
  step as ⟨qh2, hqh2⟩
  have hqh2_eq : qh2 = 2#usize := by
    rw [hqh2]; exact UScalar.eq_of_val_eq (usize_sat_add_one 1#usize (by decide))
  rw [hqh2_eq]
  step as ⟨st2, hst2⟩; step as ⟨coff2, hcoff2⟩
  have hcoff2_eq : coff2 = d := by rw [hcoff2, hst2, ht2_1]
  rw [hcoff2_eq]
  have hinner1 : blue.solve_blue_loop0_loop0 edges 2#usize 1#usize r2 t2 q2 2#usize 1#usize d 0#usize
      ⦃ res => res.1 = r2 ∧ res.2.1 = t2 ∧ res.2.2.2 = 2#usize ⦄ := by
    unfold blue.solve_blue_loop0_loop0
    apply loop_step; unfold blue.solve_blue_loop0_loop0.body; dsimp only
    rw [ite_t (by decide)]
    simp only [lift, bind_ok, core.slice.Slice.get, core.slice.index.Usize.get, he0]
    dsimp only [e]
    rw [ite_t hv_gt, ite_t (by decide), ite_t (by decide),
      ite_t (by decide), ite_f (by decide), ite_t rfl]
    simp only [blue.get_bool, core.slice.Slice.get, core.slice.index.Usize.get, bind_ok, hr2_0]
    rw [ite_t trivial]
    simp only [bind_ok]
    have h01 : core.num.Usize.saturating_add 0#usize 1#usize = 1#usize :=
      UScalar.eq_of_val_eq (usize_sat_add_one 0#usize (by decide))
    rw [h01]
    change ok (ControlFlow.cont _) ⦃ _ ⦄
    rw [WP.spec_ok]
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
    exact ⟨rfl, rfl, rfl⟩
  step with hinner1 as ⟨r3, t3, q3, qt3, hr3, ht3, hqt3⟩
  subst r3; subst t3; subst qt3
  apply loop_step; dsimp only
  rw [ite_f (by decide), WP.spec_ok]
  exact ⟨hr2_0, hr2_1, ht2_0, ht2_1⟩

private theorem single_edge_loop1 (reach2 : Std.Array Bool 17#usize)
    (hr2_1 : (Array.to_slice reach2)[1#usize]? = some true) :
    blue.solve_blue_loop1 2#usize reach2 (Array.repeat 17#usize blue.MAX_PEERS)
      (Array.repeat 16#usize 0#usize) 0#usize 1#usize
      ⦃ p =>
        p.2.2 = 1#usize
        ∧ (Array.to_slice p.1)[1#usize]? = some 0#usize
        ∧ (Array.to_slice p.2.1)[0#usize]? = some 1#usize ⦄ := by
  unfold blue.solve_blue_loop1
  apply loop_step; unfold blue.solve_blue_loop1.body; dsimp only
  rw [ite_t (by decide), ite_t (by unfold blue.MAX_PEERS; decide)]
  step as ⟨sr, hsr⟩; step as ⟨b1, hb1⟩
  have hb1_t : b1 = true := by rw [hb1, hsr, hr2_1]
  subst hb1_t
  rw [ite_t rfl]
  have hhti1 : (Array.to_slice (Array.repeat 17#usize blue.MAX_PEERS))[1#usize]? = some blue.MAX_PEERS := by
    rw [array_repeat_get?, ite_t (by decide)]
  have hith0 : (Array.to_slice (Array.repeat 16#usize 0#usize))[0#usize]? = some 0#usize := by
    rw [array_repeat_get?]; decide
  mut_set hhti1
  mut_set hith0
  step as ⟨d1, hd1⟩
  have hd1_1 : d1 = 1#usize := by
    rw [hd1]; exact UScalar.eq_of_val_eq (usize_sat_add_one 0#usize (by decide))
  subst hd1_1
  step as ⟨h2, hh2⟩
  have hh2_2 : h2 = 2#usize := by
    rw [hh2]; exact UScalar.eq_of_val_eq (usize_sat_add_one 1#usize (by decide))
  subst hh2_2
  apply loop_step; dsimp only
  rw [ite_f (by decide), WP.spec_ok]
  refine ⟨rfl, ?_, ?_⟩
  · rw [array_set_opt_get?]; simp
  · rw [array_set_opt_get?]; simp

private theorem single_edge_loop2 (d : Std.I64) (v : Std.U64) (hv : 0 < v.val)
    (reach2 : Std.Array Bool 17#usize)
    (hr2_0 : (Array.to_slice reach2)[0#usize]? = some true)
    (hr2_1 : (Array.to_slice reach2)[1#usize]? = some true) :
    let e : blue.EdgeObs := { «from» := 0#usize, «to» := 1#usize, offset_ns := d, variance_ns2 := v }
    let edges : Slice blue.EdgeObs := Slice.from [e] (by scalar_tac)
    blue.solve_blue_loop2 edges 2#usize 1#usize reach2 0#u64 0#usize ⦃ vm => vm = v ⦄ := by
  intro e edges
  have he0 : edges[0#usize]? = some e := by rw [Slice.getElem?_Usize_eq]; rfl
  have hv_gt : v > 0#u64 := by scalar_tac
  unfold blue.solve_blue_loop2
  apply loop_step; unfold blue.solve_blue_loop2.body; dsimp only
  rw [ite_t (by decide)]
  rw [show core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice blue.EdgeObs) edges 0#usize = ok (edges[0#usize]?) from rfl, he0, bind_ok]
  dsimp only [e]
  rw [ite_t hv_gt, ite_t (by decide), ite_t (by decide), ite_t (by decide)]
  step as ⟨sr0, hsr0⟩; step as ⟨b0, hb0⟩
  have hb0_t : b0 = true := by rw [hb0, hsr0, hr2_0]
  subst hb0_t; rw [ite_t rfl]
  step as ⟨sr1, hsr1⟩; step as ⟨b1, hb1⟩
  have hb1_t : b1 = true := by rw [hb1, hsr1, hr2_1]
  subst hb1_t; rw [ite_t rfl, ite_t trivial, bind_ok]
  step as ⟨e2, he2⟩
  have he2_1 : e2 = 1#usize := by
    rw [he2]; exact UScalar.eq_of_val_eq (usize_sat_add_one 0#usize (by decide))
  subst he2_1
  apply loop_step; dsimp only
  rw [ite_f (by decide), WP.spec_ok]

private theorem single_edge_loop3 (d : Std.I64) (v : Std.U64) (hv : 0 < v.val)
    (reach2 : Std.Array Bool 17#usize) (tree2 : Std.Array Std.I64 17#usize)
    (hti : Std.Array Std.Usize 17#usize)
    (hr2_0 : (Array.to_slice reach2)[0#usize]? = some true)
    (hr2_1 : (Array.to_slice reach2)[1#usize]? = some true)
    (ht2_0 : (Array.to_slice tree2)[0#usize]? = some 0#i64)
    (ht2_1 : (Array.to_slice tree2)[1#usize]? = some d)
    (hhti_1 : (Array.to_slice hti)[1#usize]? = some 0#usize) :
    let e : blue.EdgeObs := { «from» := 0#usize, «to» := 1#usize, offset_ns := d, variance_ns2 := v }
    let edges : Slice blue.EdgeObs := Slice.from [e] (by scalar_tac)
    blue.solve_blue_loop3 edges 2#usize 1#usize reach2 tree2 hti 1#usize v
      (Array.repeat 256#usize 0#i128) (Array.repeat 16#usize 0#i128) 0#usize
      ⦃ p => (Array.to_slice p.1)[0#usize]? = some blue.Q32_ONE ∧ AllZero16 p.2 ⦄ := by
  intro e edges
  have he0 : edges[0#usize]? = some e := by rw [Slice.getElem?_Usize_eq]; rfl
  have hv_gt : v > 0#u64 := by scalar_tac
  have hv_i128 : (UScalar.hcast .I128 v).val = v.val := U64.hcast_I128_val v
  have hv_pos_i128 : 0 < (UScalar.hcast .I128 v).val := by rw [hv_i128]; omega
  have h0_128 : (0#i128 : Std.I128).val = 0 := rfl
  have hq32_val : (blue.Q32_ONE : Std.I128).val = 4294967296 := by unfold blue.Q32_ONE; rfl
  have hsub0_d : core.num.I128.wrapping_sub (IScalar.cast .I128 d) 0#i128 = IScalar.cast .I128 d := by
    apply IScalar.eq_of_val_eq
    have hcast : (IScalar.cast .I128 d).val = d.val := I64.cast_I128_val d
    have hb := d.hBounds; change -2^63 ≤ d.val ∧ d.val < 2^63 at hb
    rw [I128.wrapping_sub_val _ _ ⟨by rw [hcast, h0_128]; omega, by rw [hcast, h0_128]; omega⟩, h0_128]; omega
  have hsub_self_d : core.num.I128.wrapping_sub (IScalar.cast .I128 d) (IScalar.cast .I128 d) = 0#i128 := by
    apply IScalar.eq_of_val_eq
    rw [I128.wrapping_sub_val _ _ ⟨by omega, by omega⟩, h0_128]; omega
  unfold blue.solve_blue_loop3
  apply loop_step; unfold blue.solve_blue_loop3.body; dsimp only
  rw [ite_t (by decide)]
  rw [show core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice blue.EdgeObs) edges 0#usize = ok (edges[0#usize]?) from rfl, he0, bind_ok]
  dsimp only [e]
  rw [ite_t hv_gt, ite_t (by decide), ite_t (by decide), ite_t (by decide)]
  step as ⟨sr0, hsr0⟩; step as ⟨b0, hb0⟩
  have hb0_t : b0 = true := by rw [hb0, hsr0, hr2_0]
  subst hb0_t; rw [ite_t rfl]
  step as ⟨sr1, hsr1⟩; step as ⟨b1, hb1⟩
  have hb1_t : b1 = true := by rw [hb1, hsr1, hr2_1]
  subst hb1_t; rw [ite_t rfl]
  step as ⟨vi1, hvi1⟩; step as ⟨vi2, hvi2⟩
  subst hvi1; subst hvi2
  step with Fixed.scale_div_pow2_spec (UScalar.hcast .I128 v) 32#u32 (UScalar.hcast .I128 v)
    as ⟨w_raw, _, hw_pos⟩
  have hw_raw_eq : w_raw = blue.Q32_ONE := by
    have hq := hw_pos hv_pos_i128
    have hm : min 32 64 = 32 := by decide
    rw [hm, Int.mul_ediv_cancel_left _ (by omega)] at hq
    apply IScalar.eq_of_val_eq
    rw [hq, hq32_val, Fixed.clamp128]; omega
  subst hw_raw_eq
  rw [ite_f (by unfold blue.Q32_ONE; decide), ite_f (by unfold blue.Q32_ONE; decide), bind_ok]
  step as ⟨st1, hst1⟩; step as ⟨td1, htd1⟩
  have htd1_eq : td1 = d := by rw [htd1, hst1, ht2_1]
  clear htd1; subst td1
  step as ⟨i3, hi3⟩; subst hi3
  step as ⟨st0, hst0⟩; step as ⟨td0, htd0⟩
  have htd0_eq : td0 = 0#i64 := by rw [htd0, hst0, ht2_0]
  clear htd0; subst htd0_eq
  step as ⟨i5, hi5⟩
  have hi5_0 : i5 = 0#i128 := by rw [hi5]; apply IScalar.eq_of_val_eq; exact I64.cast_I128_val 0#i64
  clear hi5; subst hi5_0
  step as ⟨tdiff, htdiff⟩
  have htdiff_eq : tdiff = IScalar.cast .I128 d := by rw [htdiff, hsub0_d]
  clear htdiff; subst htdiff_eq
  step as ⟨i6, hi6⟩; subst hi6
  step as ⟨i7, hi7⟩
  have hi7_0 : i7 = 0#i128 := by rw [hi7, hsub_self_d]
  clear hi7; subst hi7_0
  have hcs0 : blue.clamp_sym 0#i128 blue.MAX_RESIDUAL_NS ⦃ r => r = 0#i128 ⦄ := by
    unfold blue.clamp_sym blue.MAX_RESIDUAL_NS
    have hneg : (core.num.I128.wrapping_sub 0#i128 10000000000#i128).val = -10000000000 := by
      rw [I128.wrapping_sub_val _ _ ⟨by decide, by decide⟩]; decide
    rw [show lift (core.num.I128.wrapping_sub 0#i128 10000000000#i128) = ok _ from rfl, bind_ok]
    have hnotgt : ¬ (0#i128 > 10000000000#i128) := by decide
    have hnotlt : ¬ (0#i128 < core.num.I128.wrapping_sub 0#i128 10000000000#i128) := by
      intro h; have hv0 : (0#i128 : Std.I128).val < (core.num.I128.wrapping_sub 0#i128 10000000000#i128).val := h
      omega
    rw [ite_f hnotgt, ite_f hnotlt, WP.spec_ok]
  step with hcs0 as ⟨res, hres⟩
  subst hres
  step with Fixed.saturating_mul_i128_spec blue.Q32_ONE 0#i128 as ⟨wr, hwr⟩
  have hwr0 : wr = 0#i128 := by
    apply IScalar.eq_of_val_eq; rw [hwr]; simp [Fixed.clamp128]
  clear hwr; subst hwr0
  step as ⟨s4, hs4⟩; step as ⟨u_idx, hu_idx⟩
  step as ⟨s5, hs5⟩; step as ⟨v_idx, hv_idx⟩
  have hv_idx_0 : v_idx = 0#usize := by rw [hv_idx, hs5, hhti_1]
  clear hv_idx; subst hv_idx_0
  rw [ite_f (by decide), bind_ok]
  apply WP.spec_bind
    (Pₘ := fun p : Std.Array Std.I128 256#usize × Std.Array Std.I128 16#usize =>
      (Array.to_slice p.1)[0#usize]? = some blue.Q32_ONE ∧ AllZero16 p.2)
  · suffices h :
        (do
          let (mat3, rhs3) ←
            if (1#usize != 0#usize) = true then
              if 0#usize < 1#usize then do
                let mat4 ← blue.mat_add (Array.repeat 256#usize 0#i128) 1#usize 0#usize 0#usize blue.Q32_ONE
                let (s6, to_slice_mut_back) ← lift (Array.repeat 16#usize 0#i128).to_slice_mut
                let (o1, get_mut_back) ← core.slice.Slice.get_mut
                  (core.slice.index.SliceIndexUsizeSlice Std.I128) s6 0#usize
                let a ← match o1 with
                  | none => ok (to_slice_mut_back (get_mut_back none))
                  | some b2 => do
                    let b3 ← lift (core.num.I128.saturating_add b2 0#i128)
                    ok (to_slice_mut_back (get_mut_back (some b3)))
                ok (mat4, a)
              else ok (Array.repeat 256#usize 0#i128, Array.repeat 16#usize 0#i128)
            else ok (Array.repeat 256#usize 0#i128, Array.repeat 16#usize 0#i128)
          let a ←
            if (0#usize != 0#usize) = true then
              if (1#usize != 0#usize) = true then
                if u_idx < 1#usize then
                  if 0#usize < 1#usize then do
                    let neg_w ← lift (core.num.I128.wrapping_sub 0#i128 blue.Q32_ONE)
                    let mat4 ← blue.mat_add mat3 1#usize u_idx 0#usize neg_w
                    blue.mat_add mat4 1#usize 0#usize u_idx neg_w
                  else ok mat3
                else ok mat3
              else ok mat3
            else ok mat3
          ok (a, rhs3))
        ⦃ p => p.1.to_slice[0#usize]? = some blue.Q32_ONE ∧ AllZero16 p.2 ⦄ from h
    rw [ite_t (by decide), ite_t (by decide)]
    apply WP.spec_bind
      (Pₘ := fun p : Std.Array Std.I128 256#usize × Std.Array Std.I128 16#usize =>
        (Array.to_slice p.1)[0#usize]? = some blue.Q32_ONE ∧ AllZero16 p.2)
    · have hmat_add0 : blue.mat_add (Array.repeat 256#usize 0#i128) 1#usize 0#usize 0#usize blue.Q32_ONE
          ⦃ m => (Array.to_slice m)[0#usize]? = some blue.Q32_ONE ⦄ := by
        unfold blue.mat_add
        have h00 : core.num.Usize.wrapping_mul 0#usize 1#usize = 0#usize := by
          apply UScalar.eq_of_val_eq; rw [core.num.Usize.wrapping_mul_val_eq]; simp
        have ha0 : core.num.Usize.wrapping_add 0#usize 0#usize = 0#usize := by
          apply UScalar.eq_of_val_eq; rw [core.num.Usize.wrapping_add_val_eq]; simp
        have hm0 : (Array.to_slice (Array.repeat 256#usize 0#i128))[0#usize]? = some 0#i128 := by
          rw [array_repeat_get?]; decide
        have hadd_q : core.num.I128.saturating_add 0#i128 blue.Q32_ONE = blue.Q32_ONE := by
          apply IScalar.eq_of_val_eq
          rw [I128.saturating_add_val, hq32_val]
          change max (-2^127) (min (2^127 - 1) ((0 : ℤ) + 4294967296)) = 4294967296; omega
        rw [show lift (core.num.Usize.wrapping_mul 0#usize 1#usize) = ok 0#usize from congrArg ok h00, bind_ok]
        rw [show lift (core.num.Usize.wrapping_add 0#usize 0#usize) = ok 0#usize from congrArg ok ha0, bind_ok]
        rw [array_to_slice_mut_eq, show lift (_, _) = ok (_, _) from rfl, bind_ok_pair]
        rw [slice_get_mut_val, bind_ok_pair, hm0]
        suffices hm : (do
            let cell1 ← lift (core.num.I128.saturating_add 0#i128 blue.Q32_ONE)
            ok ((Array.repeat 256#usize 0#i128).from_slice
              ((Array.repeat 256#usize 0#i128).to_slice.set_opt 0#usize (some cell1))))
            ⦃ m => m.to_slice[0#usize]? = some blue.Q32_ONE ⦄ from hm
        rw [show lift (core.num.I128.saturating_add 0#i128 blue.Q32_ONE) = ok blue.Q32_ONE from congrArg ok hadd_q, bind_ok]
        rw [array_from_slice_set_opt, WP.spec_ok, array_set_opt_get?]
        simp [hm0]
      step with hmat_add0 as ⟨mat2, hmat2⟩
      have hr0 : (Array.to_slice (Array.repeat 16#usize 0#i128))[0#usize]? = some 0#i128 := by
        rw [array_repeat_get?]; decide
      have h00_add : core.num.I128.saturating_add 0#i128 0#i128 = 0#i128 := by
        apply IScalar.eq_of_val_eq
        rw [I128.saturating_add_val]
        change max (-2^127) (min (2^127 - 1) ((0 : ℤ) + 0)) = 0; omega
      rw [array_to_slice_mut_eq, show lift (_, _) = ok (_, _) from rfl, bind_ok_pair]
      rw [slice_get_mut_val, bind_ok_pair, hr0]
      suffices hr : (do
          let a ← (do
            let b3 ← lift (core.num.I128.saturating_add 0#i128 0#i128)
            ok ((Array.repeat 16#usize 0#i128).from_slice
              ((Array.repeat 16#usize 0#i128).to_slice.set_opt 0#usize (some b3))))
          ok (mat2, a))
          ⦃ p => p.1.to_slice[0#usize]? = some blue.Q32_ONE ∧ AllZero16 p.2 ⦄ from hr
      rw [show lift (core.num.I128.saturating_add 0#i128 0#i128) = ok 0#i128 from congrArg ok h00_add, bind_ok]
      rw [array_from_slice_set_opt, bind_ok, WP.spec_ok]
      refine ⟨hmat2, ?_⟩
      have hset0 := allZero16_set_zero (Array.repeat 16#usize 0#i128) 0#usize allZero16_repeat
        (some 0#i128) (fun _ h => (Option.some.inj h).symm)
      rwa [array_to_slice_mut_set_opt] at hset0
    · rintro ⟨mat3, rhs3⟩ ⟨hmat3, hrhs3⟩
      suffices ht : (do
          let a ←
            if (0#usize != 0#usize) = true then
              if (1#usize != 0#usize) = true then
                if u_idx < 1#usize then
                  if 0#usize < 1#usize then do
                    let neg_w ← lift (core.num.I128.wrapping_sub 0#i128 blue.Q32_ONE)
                    let mat4 ← blue.mat_add mat3 1#usize u_idx 0#usize neg_w
                    blue.mat_add mat4 1#usize 0#usize u_idx neg_w
                  else ok mat3
                else ok mat3
              else ok mat3
            else ok mat3
          ok (a, rhs3))
          ⦃ p => p.1.to_slice[0#usize]? = some blue.Q32_ONE ∧ AllZero16 p.2 ⦄ from ht
      rw [ite_f (by decide), bind_ok, WP.spec_ok]
      exact ⟨hmat3, hrhs3⟩
  · rintro ⟨mat3, rhs3⟩ ⟨hmat3, hrhs3⟩
    step as ⟨e2, he2⟩
    have he2_1 : e2 = 1#usize := by
      rw [he2]; exact UScalar.eq_of_val_eq (usize_sat_add_one 0#usize (by decide))
    subst he2_1
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
    exact ⟨hmat3, hrhs3⟩

private theorem single_edge_hzcom (rhs_ones : Std.Array Std.I128 16#usize)
    (hro_0 : (Array.to_slice rhs_ones)[0#usize]? = some blue.Q32_ONE) :
    blue.solve_ldlt 1#usize
      ((Array.repeat 256#usize 0#i64).set_opt 0#usize (some 4294967296#i64))
      ((Array.repeat 16#usize 0#i128).set_opt 0#usize (some blue.Q32_ONE))
      rhs_ones 32#u32
      ⦃ zc => (Array.to_slice zc)[0#usize]? = some blue.Q32_ONE ⦄ := by
  have hq32_val : (blue.Q32_ONE : Std.I128).val = 4294967296 := by unfold blue.Q32_ONE; rfl
  let l1 := (Array.repeat 256#usize 0#i64).set_opt 0#usize (some 4294967296#i64)
  unfold blue.solve_ldlt
  have hl0 : blue.solve_ldlt_loop0 1#usize l1 rhs_ones (Array.repeat 16#usize 0#i128) 0#usize
      ⦃ y => (Array.to_slice y)[0#usize]? = some blue.Q32_ONE ⦄ := by
    unfold blue.solve_ldlt_loop0
    apply loop_step; unfold blue.solve_ldlt_loop0.body; dsimp only
    rw [ite_t (by decide)]
    step as ⟨s0, hs0⟩; step as ⟨sum0, hsum0⟩
    have hsum0_eq : sum0 = blue.Q32_ONE := by rw [hsum0, hs0, hro_0]
    clear hsum0; subst sum0
    have hinner : blue.solve_ldlt_loop0_loop0 1#usize l1 (Array.repeat 16#usize 0#i128) 0#usize blue.Q32_ONE 0#usize
        ⦃ r => r = blue.Q32_ONE ⦄ := by
      unfold blue.solve_ldlt_loop0_loop0
      apply loop_step; unfold blue.solve_ldlt_loop0_loop0.body; dsimp only
      rw [ite_f (by decide), WP.spec_ok]
    step with hinner as ⟨sum1, hsum1⟩; subst sum1
    have h0 : (Array.to_slice (Array.repeat 16#usize 0#i128))[0#usize]? = some 0#i128 := by
      rw [array_repeat_get?]; decide
    mut_set h0
    step as ⟨i2, hi2⟩
    have hi2_1 : i2 = 1#usize := by
      rw [hi2]; apply UScalar.eq_of_val_eq; exact usize_sat_add_one 0#usize (by decide)
    clear hi2; subst i2
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
    dsimp only
    rw [array_set_opt_get?]; simp
  step with hl0 as ⟨y1, hy1_0⟩
  have hl1 : blue.solve_ldlt_loop1 1#usize
      ((Array.repeat 16#usize 0#i128).set_opt 0#usize (some blue.Q32_ONE)) 32#u32 y1
      (Array.repeat 16#usize 0#i128) 0#usize
      ⦃ z => (Array.to_slice z)[0#usize]? = some blue.Q32_ONE ⦄ := by
    unfold blue.solve_ldlt_loop1
    apply loop_step; unfold blue.solve_ldlt_loop1.body; dsimp only
    rw [ite_t (by decide)]
    have hdq0 : (Array.to_slice ((Array.repeat 16#usize 0#i128).set_opt 0#usize (some blue.Q32_ONE)))[0#usize]? =
        some blue.Q32_ONE := by rw [array_set_opt_get?]; simp
    step as ⟨s0, hs0⟩; step as ⟨dk, hdk⟩
    have hdk_eq : dk = blue.Q32_ONE := by rw [hdk, hs0, hdq0]
    clear hdk; subst dk
    step as ⟨s1, hs1⟩; step as ⟨yk, hyk⟩
    have hyk_eq : yk = blue.Q32_ONE := by rw [hyk, hs1, hy1_0]
    clear hyk; subst yk
    step with Fixed.scale_div_pow2_spec blue.Q32_ONE 32#u32 blue.Q32_ONE as ⟨zk, _, hzk⟩
    have hzk_eq : zk = blue.Q32_ONE := by
      have hq := hzk (by rw [hq32_val]; omega)
      have hm : min 32 64 = 32 := by decide
      rw [hm, hq32_val] at hq
      apply IScalar.eq_of_val_eq
      rw [hq, hq32_val, Fixed.clamp128]; omega
    clear hzk; subst zk
    have h0 : (Array.to_slice (Array.repeat 16#usize 0#i128))[0#usize]? = some 0#i128 := by
      rw [array_repeat_get?]; decide
    mut_set h0
    step as ⟨k2, hk2⟩
    have hk2_1 : k2 = 1#usize := by
      rw [hk2]; apply UScalar.eq_of_val_eq; exact usize_sat_add_one 0#usize (by decide)
    clear hk2; subst k2
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
    dsimp only
    rw [array_set_opt_get?]; simp
  step with hl1 as ⟨z1, hz1_0⟩
  unfold blue.solve_ldlt_loop2
  apply loop_step; unfold blue.solve_ldlt_loop2.body; dsimp only
  rw [ite_t (by decide)]
  step as ⟨rev1, hrev1⟩
  have hrev1_0 : rev1 = 0#usize := by
    rw [hrev1]; apply UScalar.eq_of_val_eq; exact usize_wrapping_sub_one_val 1#usize (by decide)
  clear hrev1; subst rev1
  step as ⟨sz, hsz⟩; step as ⟨sum0, hsum0⟩
  have hsum0_eq : sum0 = blue.Q32_ONE := by rw [hsum0, hsz, hz1_0]
  clear hsum0; subst sum0
  step as ⟨j0, hj0⟩
  have hj0_1 : j0 = 1#usize := by
    rw [hj0]; apply UScalar.eq_of_val_eq; exact usize_sat_add_one 0#usize (by decide)
  clear hj0; subst j0
  have hinner2 : blue.solve_ldlt_loop2_loop0 1#usize l1 (Array.repeat 16#usize 0#i128) 0#usize blue.Q32_ONE 1#usize
      ⦃ r => r = blue.Q32_ONE ⦄ := by
    unfold blue.solve_ldlt_loop2_loop0
    apply loop_step; unfold blue.solve_ldlt_loop2_loop0.body; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
  step with hinner2 as ⟨sum1, hsum1⟩; subst sum1
  have h0 : (Array.to_slice (Array.repeat 16#usize 0#i128))[0#usize]? = some 0#i128 := by
    rw [array_repeat_get?]; decide
  rw [array_to_slice_mut_eq, show lift (_, _) = ok (_, _) from rfl, bind_ok_pair]
  rw [slice_get_mut_val, bind_ok_pair, h0, WP.spec_ok]
  apply loop_step; dsimp only
  rw [ite_f (by decide), WP.spec_ok]
  dsimp only
  rw [array_from_slice_set_opt, array_set_opt_get?]; simp

/-- **Exact Star degeneration of `solve_blue`:** on a two-host graph
(`host_count = 2`, `self_idx = 1`) with a single directed sender→self edge
`(0 → 1, offset_ns = d, variance_ns2 = v)` where `v > 0` and `|d| ≤ 2⁶³ - 1`,
the BLUE solver recovers:
- `active_count = 1`,
- `common_offset_ns = -d` (exact Star offset in speaker-minus-sender convention),
- `self_diff_offset_ns = 0` and `self_diff_var_ns2 = 0`,
- `common_var_ns2 = min(v, MAX_OUT_VAR_NS2)`. -/
theorem solve_blue_single_edge_star (d : Std.I64) (v : Std.U64)
    (hd : -(2^63 - 1) ≤ d.val) (hv : 0 < v.val) :
    let e : blue.EdgeObs := { «from» := 0#usize, «to» := 1#usize, offset_ns := d, variance_ns2 := v }
    let edges : Slice blue.EdgeObs := Slice.from [e] (by scalar_tac)
    blue.solve_blue 2#usize 1#usize edges 1#usize ⦃ res =>
      res.active_count = 1#usize
      ∧ res.common_offset_ns.val = -d.val
      ∧ res.self_diff_offset_ns = 0#i64
      ∧ res.self_diff_var_ns2 = 0#u64
      ∧ res.common_var_ns2.val = min v.val blue.MAX_OUT_VAR_NS2.val ⦄ := by
  intro e edges
  have hd_hi : d.val ≤ 2^63 - 1 := by scalar_tac
  have he_len : Slice.len edges = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [edges, Slice.len]
  have hv_ne : v ≠ 0#u64 := by
    intro h; rw [h] at hv; simp at hv
  have hv_i128 : (UScalar.hcast .I128 v).val = v.val := U64.hcast_I128_val v
  have h0_128 : (0#i128 : Std.I128).val = 0 := rfl
  have hself_theta_val : (core.num.I128.wrapping_sub 0#i128 (IScalar.cast .I128 d)).val = -d.val := by
    have hcast : (IScalar.cast .I128 d).val = d.val := I64.cast_I128_val d
    rw [I128.wrapping_sub_val _ _ ⟨by rw [hcast, h0_128]; omega, by rw [hcast, h0_128]; omega⟩, h0_128, hcast]; omega
  have hsat_add_d : core.num.I128.saturating_add (IScalar.cast .I128 d) 0#i128 = IScalar.cast .I128 d := by
    apply IScalar.eq_of_val_eq
    have hcast : (IScalar.cast .I128 d).val = d.val := I64.cast_I128_val d
    rw [I128.saturating_add_val, hcast]; change max (-2^127) (min (2^127 - 1) (d.val + 0)) = d.val; omega
  have hq32_val : (blue.Q32_ONE : Std.I128).val = 4294967296 := by unfold blue.Q32_ONE; rfl
  unfold blue.solve_blue
  have hhosts : (if 2#usize > blue.MAX_HOSTS then ok blue.MAX_HOSTS else ok 2#usize)
      ⦃ h => h = 2#usize ⦄ := by
    rw [ite_f (by unfold blue.MAX_HOSTS; decide), WP.spec_ok]
  apply WP.spec_bind hhosts; intro hosts hhosts_eq; subst hosts
  have hne : (if 1#usize > Slice.len edges then ok (Slice.len edges) else ok 1#usize)
      ⦃ n => n = 1#usize ⦄ := by
    rw [he_len, ite_f (by decide), WP.spec_ok]
  apply WP.spec_bind hne; intro n_edges hne_eq; subst n_edges
  rw [ite_f (by decide), ite_f (by decide), ite_f (by decide), ite_f (by decide)]
  dsimp +zeta only
  have hr0_f : (Array.to_slice (Array.repeat 17#usize false))[0#usize]? = some false := by
    rw [array_repeat_get?]; decide
  have hq0_0 : (Array.to_slice (Array.repeat 17#usize 0#usize))[0#usize]? = some 0#usize := by
    rw [array_repeat_get?]; decide
  mut_set hr0_f
  mut_set hq0_0
  step with single_edge_loop0 d v hv as ⟨reach2, tree2, hr2_0, hr2_1, ht2_0, ht2_1⟩
  step as ⟨sr2, hsr2⟩; step as ⟨b_self, hb_self⟩
  have hb_self_t : b_self = true := by rw [hb_self, hsr2, hr2_1]
  subst hb_self_t
  rw [ite_t rfl]
  step with single_edge_loop1 reach2 hr2_1 as ⟨hti, ith, dim, hdim1, hhti_1, hith_0⟩
  subst hdim1
  step as ⟨shti, hshti⟩; step as ⟨sdense, hsdense⟩
  have hsdense_0 : sdense = 0#usize := by rw [hsdense, hshti, hhti_1]
  subst hsdense_0
  rw [ite_f (by decide), ite_f (by decide)]
  step with single_edge_loop2 d v hv reach2 hr2_0 hr2_1 as ⟨vm, hvm⟩
  subst vm
  rw [ite_f hv_ne]
  step with single_edge_loop3 d v hv reach2 tree2 hti hr2_0 hr2_1 ht2_0 ht2_1 hhti_1 as ⟨mat1, rhs1, hmat1_0, hrhs1_0⟩
  -- Phase 4: loop4 (1x1 LDL^T + solve)
  unfold blue.solve_blue_loop4
  -- j = 0: pivot d_q32[0] = mat1[0] = Q32_ONE, l_q32[0] = Q32_ONE
  apply loop_step; unfold blue.solve_blue_loop4.body; dsimp only
  rw [ite_t (by scalar_tac)]
  have hmg0 : blue.mat_get mat1 1#usize 0#usize 0#usize ⦃ r => r = blue.Q32_ONE ⦄ := by
    unfold blue.mat_get
    have h00 : core.num.Usize.wrapping_mul 0#usize 1#usize = 0#usize := by
      apply UScalar.eq_of_val_eq; rw [core.num.Usize.wrapping_mul_val_eq]; simp
    have ha0 : core.num.Usize.wrapping_add 0#usize 0#usize = 0#usize := by
      apply UScalar.eq_of_val_eq; rw [core.num.Usize.wrapping_add_val_eq]; simp
    simp only [lift, bind_ok, h00, ha0]
    step as ⟨r, hr⟩
    rw [hr, hmat1_0]
  step with hmg0 as ⟨dj0, hdj0⟩
  subst hdj0
  have hl4_0 : blue.solve_blue_loop4_loop0 1#usize (Array.repeat 256#usize 0#i64)
      (Array.repeat 16#usize 0#i128) 0#usize blue.Q32_ONE 0#usize ⦃ r => r = blue.Q32_ONE ⦄ := by
    unfold blue.solve_blue_loop4_loop0
    apply loop_step; unfold blue.solve_blue_loop4_loop0.body; dsimp only
    rw [ite_f (by scalar_tac), WP.spec_ok]
  step with hl4_0 as ⟨dj1, hdj1⟩
  subst hdj1
  rw [ite_f (by unfold blue.Q32_ONE; decide)]
  have hd0_0 : (Array.to_slice (Array.repeat 16#usize 0#i128))[0#usize]? = some 0#i128 := by
    rw [array_repeat_get?]; decide
  mut_set hd0_0
  have hl0_0 : (Array.to_slice (Array.repeat 256#usize 0#i64))[0#usize]? = some 0#i64 := by
    rw [array_repeat_get?]; decide
  have hmul01 : core.num.Usize.wrapping_mul 0#usize 1#usize = 0#usize := by
    apply UScalar.eq_of_val_eq; rw [core.num.Usize.wrapping_mul_val_eq]; simp
  have hadd00 : core.num.Usize.wrapping_add 0#usize 0#usize = 0#usize := by
    apply UScalar.eq_of_val_eq; rw [core.num.Usize.wrapping_add_val_eq]; simp
  rw [array_to_slice_mut_eq, show lift (_, _) = ok (_, _) from rfl, bind_ok_pair]
  rw [show lift (core.num.Usize.wrapping_mul 0#usize 1#usize) = ok 0#usize from congrArg ok hmul01, bind_ok]
  rw [show lift (core.num.Usize.wrapping_add 0#usize 0#usize) = ok 0#usize from congrArg ok hadd00, bind_ok]
  rw [slice_get_mut_val, bind_ok_pair, hl0_0]
  dsimp +zeta only
  rw [array_from_slice_set_opt, bind_ok]
  step as ⟨i_next, hi_next⟩
  have hi_next_1 : i_next = 1#usize := by
    rw [hi_next]; exact UScalar.eq_of_val_eq (usize_sat_add_one 0#usize (by decide))
  subst hi_next_1
  have hl4_1 : blue.solve_blue_loop4_loop1 1#usize mat1
      ((Array.repeat 256#usize 0#i64).set_opt 0#usize (some 4294967296#i64))
      ((Array.repeat 16#usize 0#i128).set_opt 0#usize (some blue.Q32_ONE)) 0#usize blue.Q32_ONE 1#usize
      ⦃ l => l = (Array.repeat 256#usize 0#i64).set_opt 0#usize (some 4294967296#i64) ⦄ := by
    unfold blue.solve_blue_loop4_loop1
    apply loop_step; unfold blue.solve_blue_loop4_loop1.body; dsimp only
    rw [ite_f (by scalar_tac), WP.spec_ok]
  step with hl4_1 as ⟨lq2, hlq2⟩
  subst hlq2
  step as ⟨j_next, hj_next⟩
  have hj_next_1 : j_next = 1#usize := by
    rw [hj_next]; exact UScalar.eq_of_val_eq (usize_sat_add_one 0#usize (by decide))
  subst hj_next_1
  -- j = 1 = dim: solve phase!
  apply loop_step; dsimp only
  rw [ite_f (by scalar_tac)]
  step with solve_ldlt_zero_rhs 1#usize _ _ rhs1 0#u32 hrhs1_0 as ⟨delta_phi, hdp0⟩
  -- loop4_loop2: offsets_ns[1] = d
  have hl4_2 : blue.solve_blue_loop4_loop2 tree2 ith 1#usize delta_phi (Array.repeat 17#usize 0#i64) 0#usize
      ⦃ off => (Array.to_slice off)[1#usize]? = some d ⦄ := by
    unfold blue.solve_blue_loop4_loop2
    apply loop_step; unfold blue.solve_blue_loop4_loop2.body; dsimp only
    rw [ite_t (by decide)]
    step as ⟨s0, hs0⟩; step as ⟨host, hhost⟩
    have hhost_1 : host = 1#usize := by rw [hhost, hs0, hith_0]
    clear hhost; subst hhost_1
    step as ⟨s1, hs1⟩; step as ⟨t_val, ht_val⟩
    have ht_val_d : t_val = d := by rw [ht_val, hs1, ht2_1]
    clear ht_val; subst t_val
    step as ⟨base, hbase⟩; subst hbase
    step as ⟨s2, hs2⟩; step as ⟨dp, hdp⟩
    have hdp_zero : dp = 0#i128 := by
      rw [hdp, hs2]
      cases hget : (Array.to_slice delta_phi)[0#usize]? with
      | none => rfl
      | some val => exact hdp0 0#usize val hget
    clear hdp; subst hdp_zero
    have ho1 : (Array.to_slice (Array.repeat 17#usize 0#i64))[1#usize]? = some 0#i64 := by
      rw [array_repeat_get?]; decide
    rw [array_to_slice_mut_eq, show lift (_, _) = ok (_, _) from rfl, bind_ok_pair]
    rw [slice_get_mut_val, bind_ok_pair, ho1]
    rw [show lift (core.num.I128.saturating_add (IScalar.cast .I128 d) 0#i128) = ok (IScalar.cast .I128 d)
        from congrArg ok hsat_add_d, bind_ok]
    step with Fixed.saturate_spec (IScalar.cast .I128 d) as ⟨slot_d, hslot_d⟩
    have hslot_eq : slot_d = d := by
      apply IScalar.eq_of_val_eq
      have hcast : (IScalar.cast .I128 d).val = d.val := I64.cast_I128_val d
      rw [hslot_d, hcast, Fixed.clamp64]; omega
    clear hslot_d; subst slot_d
    rw [array_from_slice_set_opt]
    step as ⟨idx2, hidx2⟩
    have hidx2_1 : idx2 = 1#usize := by
      rw [hidx2]; apply UScalar.eq_of_val_eq; exact usize_sat_add_one 0#usize (by decide)
    clear hidx2; subst idx2
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
    dsimp only
    rw [array_set_opt_get?]; simp
  step with hl4_2 as ⟨offsets_ns, hoff_1⟩
  -- loop4_loop3: rhs_ones[0] = Q32_ONE
  have hl4_3 : blue.solve_blue_loop4_loop3 1#usize (Array.repeat 16#usize 0#i128) 0#usize
      ⦃ ro => (Array.to_slice ro)[0#usize]? = some blue.Q32_ONE ⦄ := by
    unfold blue.solve_blue_loop4_loop3
    apply loop_step; unfold blue.solve_blue_loop4_loop3.body; dsimp only
    rw [ite_t (by decide)]
    have h0 : (Array.to_slice (Array.repeat 16#usize 0#i128))[0#usize]? = some 0#i128 := by
      rw [array_repeat_get?]; decide
    mut_set h0
    step as ⟨i2, hi2⟩
    have hi2_1 : i2 = 1#usize := by
      rw [hi2]; apply UScalar.eq_of_val_eq; exact usize_sat_add_one 0#usize (by decide)
    clear hi2; subst i2
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
    dsimp only
    rw [array_set_opt_get?]; simp
  step with hl4_3 as ⟨rhs_ones, hro_0⟩
  step with single_edge_hzcom rhs_ones hro_0 as ⟨z_com, hzcom_0⟩
  -- loop4_loop4: sum_z_com = Q32_ONE
  have hl4_4 : blue.solve_blue_loop4_loop4 1#usize z_com 0#i128 0#usize ⦃ s => s = blue.Q32_ONE ⦄ := by
    unfold blue.solve_blue_loop4_loop4
    apply loop_step; unfold blue.solve_blue_loop4_loop4.body; dsimp only
    rw [ite_t (by decide)]
    step as ⟨sz, hsz⟩; step as ⟨zv, hzv⟩
    have hzv_eq : zv = blue.Q32_ONE := by rw [hzv, hsz, hzcom_0]
    clear hzv; subst hzv_eq
    step as ⟨s1, hs1⟩
    have hs1_eq : s1 = blue.Q32_ONE := by
      rw [hs1]; apply IScalar.eq_of_val_eq
      rw [I128.saturating_add_val, hq32_val]
      change max (-2^127) (min (2^127 - 1) ((0 : ℤ) + 4294967296)) = 4294967296; omega
    clear hs1; subst hs1_eq
    step as ⟨i2, hi2⟩
    have hi2_1 : i2 = 1#usize := by
      rw [hi2]; apply UScalar.eq_of_val_eq; exact usize_sat_add_one 0#usize (by decide)
    clear hi2; subst hi2_1
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
  step with hl4_4 as ⟨sum_z, hsum_z⟩
  subst hsum_z
  step as ⟨i_dim, hi_dim⟩; step as ⟨i_dim1, hi_dim1⟩
  have hi_dim_1 : i_dim = 1#i128 := by
    rw [hi_dim]; apply IScalar.eq_of_val_eq; exact Usize.hcast_I128_val 1#usize
  have hi_dim1_1 : i_dim1 = 1#i128 := by
    rw [hi_dim1]; apply IScalar.eq_of_val_eq; exact Usize.hcast_I128_val 1#usize
  clear hi_dim hi_dim1; subst hi_dim_1; subst hi_dim1_1
  step as ⟨dim_sq, hdim_sq⟩
  have hdim_sq_1 : dim_sq = 1#i128 := by
    rw [hdim_sq]; apply IScalar.eq_of_val_eq
    rw [I128.wrapping_mul_val 1#i128 1#i128 ⟨by decide, by decide⟩]; decide
  clear hdim_sq; subst hdim_sq_1
  step as ⟨vi, hvi⟩; subst hvi
  -- total_com = mul_shr32(Q32_ONE, v) = v
  have hmul_shr : blue.mul_shr32 blue.Q32_ONE (UScalar.hcast .I128 v) ⦃ r => r = UScalar.hcast .I128 v ⦄ := by
    unfold blue.mul_shr32
    have hprod_in : -2^127 ≤ (blue.Q32_ONE : Std.I128).val * (UScalar.hcast .I128 v).val ∧
        (blue.Q32_ONE : Std.I128).val * (UScalar.hcast .I128 v).val ≤ 2^127 - 1 := by
      have hv_ub : v.val < 2^64 := v.hBounds
      rw [hq32_val, hv_i128]; omega
    have hcm := I128.checked_mul_bv_spec blue.Q32_ONE (UScalar.hcast .I128 v)
    cases h : core.num.checked_mul_IScalar blue.Q32_ONE (UScalar.hcast .I128 v) with
    | none =>
      rw [h] at hcm; exfalso; apply hcm
      simp only [I128.min, I128.max, I128.numBits]
      exact hprod_in
    | some prod =>
      rw [h] at hcm
      have hcm_eq : I128.checked_mul blue.Q32_ONE (UScalar.hcast .I128 v) = some prod := by
        rw [I128.checked_mul_eq]; exact h
      rw [show lift (I128.checked_mul blue.Q32_ONE (UScalar.hcast .I128 v)) = ok (some prod)
          from congrArg ok hcm_eq, bind_ok, WP.spec_ok]
      apply IScalar.eq_of_val_eq
      rw [I128.wrapping_shr_val prod 32#u32 (by decide), hcm.2.2.1, hq32_val]
      have h32 : (32#u32 : Std.U32).val = 32 := rfl
      rw [h32]; omega
  step with hmul_shr as ⟨tc, htc⟩; subst htc
  step with Fixed.div_floor_wide_spec (UScalar.hcast .I128 v) 1#i128 as ⟨dv1, hdv1_pos, _⟩
  have hdv1_eq : dv1 = UScalar.hcast .I128 v := by
    apply IScalar.eq_of_val_eq; have h := hdv1_pos (by decide); rw [h]; simp
  clear hdv1_pos; subst hdv1_eq
  step with clamp_out_var_spec (UScalar.hcast .I128 v) as ⟨cv, _, _, hcv_eq, hcv_cap⟩
  have hcv_min : cv.val = min v.val blue.MAX_OUT_VAR_NS2.val := by
    by_cases hle : v.val ≤ blue.MAX_OUT_VAR_NS2.val
    · have := hcv_eq (by rw [hv_i128]; omega) (by rw [hv_i128]; omega)
      rw [hv_i128] at this; omega
    · have hcap := hcv_cap (by rw [hv_i128]; omega); rw [hcap]; omega
  step as ⟨i4⟩; step as ⟨inv_dim⟩
  step as ⟨rhs_diff1⟩; step as ⟨z_diff⟩; step as ⟨quad_q32⟩
  rw [ite_t (by decide), bind_ok]
  step as ⟨soff, hsoff⟩; step as ⟨off_self, hoff_self⟩
  have hoff_self_eq : off_self = d := by rw [hoff_self, hsoff, hoff_1]
  clear hoff_self; subst off_self
  step as ⟨i6, hi6⟩; subst hi6
  step as ⟨self_theta, hst⟩; subst hst
  -- loop4_loop7: rel_sum = 0
  have hl4_7 : blue.solve_blue_loop4_loop7 ith 1#usize offsets_ns
      (core.num.I128.wrapping_sub 0#i128 (IScalar.cast .I128 d)) 0#i128 0#usize
      ⦃ r => r = 0#i128 ⦄ := by
    unfold blue.solve_blue_loop4_loop7
    apply loop_step; unfold blue.solve_blue_loop4_loop7.body; dsimp only
    rw [ite_t (by decide)]
    step as ⟨s0, hs0⟩; step as ⟨h_i, hh_i⟩
    have hh_i_1 : h_i = 1#usize := by rw [hh_i, hs0, hith_0]
    clear hh_i; subst hh_i_1
    step as ⟨s1, hs1⟩; step as ⟨oh, hoh⟩
    have hoh_d : oh = d := by rw [hoh, hs1, hoff_1]
    clear hoh; subst oh
    step as ⟨oh128, hoh128⟩; subst hoh128
    step as ⟨th_i, hth_i⟩; subst hth_i
    step as ⟨rel, hrel⟩
    have hrel0 : rel = 0#i128 := by
      rw [hrel]; apply IScalar.eq_of_val_eq
      rw [I128.wrapping_sub_val _ _ ⟨by rw [hself_theta_val]; omega, by rw [hself_theta_val]; omega⟩]
      omega
    clear hrel; subst hrel0
    step as ⟨rs1, hrs1⟩
    have hrs1_0 : rs1 = 0#i128 := by
      rw [hrs1]; apply IScalar.eq_of_val_eq
      rw [I128.saturating_add_val]
      change max (-2^127) (min (2^127 - 1) ((0 : ℤ) + 0)) = 0; omega
    clear hrs1; subst hrs1_0
    step as ⟨im2, him2⟩
    have him2_1 : im2 = 1#usize := by
      rw [him2]; apply UScalar.eq_of_val_eq; exact usize_sat_add_one 0#usize (by decide)
    clear him2; subst him2_1
    apply loop_step; dsimp only
    rw [ite_f (by decide), WP.spec_ok]
  step with hl4_7 as ⟨rs, hrs⟩; subst hrs
  step as ⟨i7, hi7⟩
  have hi7_1 : i7 = 1#i128 := by
    rw [hi7]; apply IScalar.eq_of_val_eq; exact Usize.hcast_I128_val 1#usize
  clear hi7; subst hi7_1
  step with Fixed.div_floor_wide_spec 0#i128 1#i128 as ⟨dm, hdm_pos, _⟩
  have hdm0 : dm = 0#i128 := by
    apply IScalar.eq_of_val_eq; have h := hdm_pos (by decide); rw [h]; rfl
  clear hdm_pos; subst hdm0
  step as ⟨co_in, hco_in⟩
  have hco_in_eq : co_in = core.num.I128.wrapping_sub 0#i128 (IScalar.cast .I128 d) := by
    rw [hco_in]; apply IScalar.eq_of_val_eq
    rw [I128.saturating_add_val, hself_theta_val]
    change max (-2^127) (min (2^127 - 1) (-d.val + 0)) = -d.val; omega
  clear hco_in; subst hco_in_eq
  step with Fixed.saturate_spec (core.num.I128.wrapping_sub 0#i128 (IScalar.cast .I128 d)) as ⟨co, hco⟩
  step as ⟨sd_in, hsd_in⟩
  have hsd_in_0 : sd_in = 0#i128 := by
    rw [hsd_in]; apply IScalar.eq_of_val_eq
    rw [I128.wrapping_sub_val _ _ ⟨by decide, by decide⟩]; decide
  clear hsd_in; subst hsd_in_0
  step with Fixed.saturate_spec 0#i128 as ⟨sd, hsd⟩
  refine ⟨?_, ?_, hcv_min⟩
  · rw [hco, hself_theta_val, Fixed.clamp64]; omega
  · apply IScalar.eq_of_val_eq; rw [hsd, Fixed.clamp64]; simp

end Unisono.Blue
