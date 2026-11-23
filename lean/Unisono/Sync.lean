/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed
public import Unisono.Relation
public import Unisono.Arrivals
public import Unisono.MinRtt
public import Unisono.Kalman
public import Unisono.Blue

/-!
# Multi-peer synchronization engine (`unisono_core::sync`)

Totality and behavioral specifications for the Aeneas-translated `Sync` and
`SyncSnapshot` state machine:

* **Totality:** every public method and internal loop of `SyncSnapshot` and
  `Sync` terminates without panic for all inputs and all states.
* **Strict peer allowlist (`find_peer_spec`, `on_peer_probe_allowlist`):**
  `Sync.on_peer_probe` replies only to peers present and configured in the
  static peer table, on the matching stream and target identity; unconfigured
  or unknown senders always receive `none`.
* **Exact Star degeneration (`step_zero_peers_star`, `zero_peers_no_peer_traffic`):**
  when `peer_count = 0`, `Sync` emits no peer probes or relays, rejects all
  peer messages, and `Sync.step` delegates directly to `publish_star` (with
  `peer_active = false`, `active_peers = 0`, `diff_var_ns2 = 0`, and
  `common_line` equal to `sender_filter.to_line`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Sync

attribute [step]
  Unisono.Relation.eval_total

@[step]
private theorem arrivals_new_total (K : Std.Usize) :
    arrivals.Arrivals.new K ⦃ _ => True ⦄ := by
  unfold arrivals.Arrivals.new
  simp

private theorem ite_t {α : Type _} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp only [h, ↓reduceIte]

private theorem ite_f {α : Type _} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp only [h, ↓reduceIte]

private theorem loop_of_measure {α β : Type} (measure : α → ℕ) (inv : α → Prop)
    (body : α → Result (ControlFlow α β)) (P : β → Prop)
    (hBody : ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => P y
      | .cont x' => inv x' ∧ measure x' < measure x ⦄) :
    ∀ n x, inv x → measure x ≤ n → loop body x ⦃ P ⦄ := by
  intro n
  induction n with
  | zero =>
    intro x hinv hle
    unfold loop
    apply WP.spec_bind (hBody x hinv)
    intro r hr
    cases r with
    | done y => rw [WP.spec_ok]; exact hr
    | cont x' => simp only at hr; omega
  | succ n ih =>
    intro x hinv hle
    unfold loop
    apply WP.spec_bind (hBody x hinv)
    intro r hr
    cases r with
    | done y => rw [WP.spec_ok]; exact hr
    | cont x' => exact ih x' hr.1 (by omega)

private theorem loop_step {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) (P : β → Prop)
    (h : body x ⦃ r => match r with | .done y => P y | .cont x' => loop body x' ⦃ P ⦄ ⦄) :
    loop body x ⦃ P ⦄ := by
  unfold loop
  apply WP.spec_bind h
  intro r hr
  cases r with
  | done y => rw [WP.spec_ok]; exact hr
  | cont x' => exact hr

private theorem usize_sat_add_one_val (a : Std.Usize) (b : Std.Usize) (h : a.val < b.val) :
    (core.num.Usize.saturating_add a 1#usize).val = a.val + 1 := by
  have hb : b.val ≤ Usize.max := by scalar_tac
  exact Usize.saturating_add_val a 1#usize (by
    have h1 : (1#usize : Std.Usize).val = 1 := rfl
    omega)

private theorem slice_get_ok {T : Type} (s : Slice T) (i : Std.Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T) s i ⦃ o => o = s[i]? ⦄ := by
  simp [core.slice.Slice.get, core.slice.index.Usize.get]

private theorem slice_get_mut_ok {T : Type} (s : Slice T) (i : Std.Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice T) s i ⦃ _ => True ⦄ := by
  simp [core.slice.Slice.get_mut, core.slice.index.Usize.get_mut]

/-! ## SyncSnapshot and helper totality -/

@[step]
theorem snapshot_common_offset_ns_total (s : sync.SyncSnapshot) (t : Std.I64) :
    sync.SyncSnapshot.common_offset_ns s t ⦃ _ => True ⦄ := by
  unfold sync.SyncSnapshot.common_offset_ns
  split <;> step*

@[step]
theorem snapshot_diff_offset_ns_total (s : sync.SyncSnapshot) (t : Std.I64) :
    sync.SyncSnapshot.diff_offset_ns s t ⦃ _ => True ⦄ := by
  unfold sync.SyncSnapshot.diff_offset_ns
  split
  · split <;> step*
  · simp

@[step]
theorem snapshot_sender_time_total (s : sync.SyncSnapshot) (t : Std.I64) :
    sync.SyncSnapshot.sender_time s t ⦃ _ => True ⦄ := by
  unfold sync.SyncSnapshot.sender_time
  split
  · step as ⟨i⟩; step as ⟨com⟩
    have hdiff : (if s.peer_active then do
        let i1 ← relation.Line.eval s.fleet_line t
        ok (IScalar.cast .I128 i1)
      else ok 0#i128) ⦃ _ => True ⦄ := by
      split
      · step*
      · simp
    step with hdiff as ⟨diff⟩
    step*
  · simp

@[step]
theorem sync_settings_standard_total (stream : Std.U16) (identity : Std.U64) :
    sync.SyncSettings.standard stream identity ⦃ _ => True ⦄ := by
  unfold sync.SyncSettings.standard
  simp

@[step]
theorem peer_slot_empty_total (prior : kalman.NoisePrior) (settings : sync.SyncSettings) :
    sync.PeerSlot.empty prior settings ⦃ _ => True ⦄ := by
  unfold sync.PeerSlot.empty
  step*

@[step]
theorem sliding_min_rtt_len_total {W : Std.Usize} (s : min_rtt.SlidingMinRtt W) :
    min_rtt.SlidingMinRtt.impl.len s ⦃ _ => True ⦄ := by
  unfold min_rtt.SlidingMinRtt.impl.len
  simp

@[step]
theorem kalman_offset_variance_ns2_total (k : kalman.KalmanFilter) :
    kalman.KalmanFilter.offset_variance_ns2 k ⦃ _ => True ⦄ := by
  unfold kalman.KalmanFilter.offset_variance_ns2
  step with Kalman.clamp_nonneg_spec k.p00 kalman.MAX_P00 (by unfold kalman.MAX_P00; decide)
    as ⟨_, _, _⟩
  step as ⟨_⟩; step as ⟨_⟩
  split <;> simp

@[step]
theorem link_variance_ns2_total (filter_var rtt_var floor_ns2 : Std.U64) :
    sync.link_variance_ns2 filter_var rtt_var floor_ns2 ⦃ _ => True ⦄ := by
  unfold sync.link_variance_ns2
  have h1 : (if filter_var < rtt_var then ok filter_var else ok rtt_var) ⦃ _ => True ⦄ := by
    split <;> simp
  step with h1 as ⟨raw⟩
  split <;> simp

@[step]
theorem clamp_var_u64_total (v : Std.I128) :
    sync.clamp_var_u64 v ⦃ _ => True ⦄ := by
  unfold sync.clamp_var_u64
  split
  · simp
  · step as ⟨i⟩; split <;> simp

@[step]
theorem apply_weight_q16_total (var_ns2 : Std.U64) (weight_q16 : Std.U32) :
    sync.apply_weight_q16 var_ns2 weight_q16 ⦃ _ => True ⦄ := by
  unfold sync.apply_weight_q16
  split
  · split <;> simp
  · split
    · split <;> simp
    · step*

@[step]
theorem inflate_variance_total (base_var_ns2 : Std.U64) (age_ns : Std.I64)
    (prior : kalman.NoisePrior) (p11_q80 : Std.I128) :
    sync.inflate_variance base_var_ns2 age_ns prior p11_q80 ⦃ _ => True ⦄ := by
  unfold sync.inflate_variance
  split
  · split <;> simp
  · have h1 : (if age_ns > 100000000000#i64 then ok 100000000000#i64 else ok age_ns) ⦃ _ => True ⦄ := by
      split <;> simp
    step with h1 as ⟨age_ns1⟩
    step as ⟨age⟩; step as ⟨i⟩; step as ⟨wq⟩
    have h2 : (if wq > 0#i128 then ok (core.num.I128.wrapping_shr wq 16#u32) else ok 0#i128) ⦃ _ => True ⦄ := by
      split <;> simp
    step with h2 as ⟨wns⟩
    have h3 : (if p11_q80 > 0#i128 then ok p11_q80 else ok 0#i128) ⦃ _ => True ⦄ := by
      split <;> simp
    step with h3 as ⟨p11p⟩
    step as ⟨i1⟩; step as ⟨p11s1⟩; step as ⟨i2⟩; step as ⟨fns⟩
    have h4 : (if prior.q2_q80_per_s > 0#i128 then ok prior.q2_q80_per_s else ok 0#i128) ⦃ _ => True ⦄ := by
      split <;> simp
    step with h4 as ⟨q2p⟩
    step*

@[step]
theorem extrapolate_offset_total (offset_ns freq_q48 age_ns : Std.I64) :
    sync.extrapolate_offset offset_ns freq_q48 age_ns ⦃ _ => True ⦄ := by
  unfold sync.extrapolate_offset
  split
  · simp
  · split
    · simp
    · have h1 : (if age_ns > 100000000000#i64 then ok 100000000000#i64 else ok age_ns) ⦃ _ => True ⦄ := by
        split <;> simp
      step with h1 as ⟨age_ns1⟩
      step*

@[step]
theorem clamp_i64_total (x hi : Std.I64) :
    sync.clamp_i64 x hi ⦃ _ => True ⦄ := by
  unfold sync.clamp_i64
  step as ⟨lo⟩
  split
  · simp
  · split <;> simp

@[step]
theorem get_bool_total (s : Slice Bool) (idx : Std.Usize) :
    sync.get_bool s idx ⦃ _ => True ⦄ := by
  unfold sync.get_bool
  step with slice_get_ok s idx as ⟨o⟩
  cases o <;> simp

@[step]
theorem age_to_u32_total (age_ns : Std.I64) :
    sync.age_to_u32 age_ns ⦃ _ => True ⦄ := by
  unfold sync.age_to_u32
  split
  · simp
  · step as ⟨i⟩; split <;> simp

@[step]
theorem link_relay_obs_total (filter : kalman.KalmanFilter) (rtt_var : Std.U64)
    (last : min_rtt.Measurement) (now_ns age_ns : Std.I64) (floor_ns2 : Std.U64) :
    sync.link_relay_obs filter rtt_var last now_ns age_ns floor_ns2 ⦃ _ => True ⦄ := by
  unfold sync.link_relay_obs
  step as ⟨f_off⟩; step as ⟨_⟩; step as ⟨_⟩; step as ⟨_⟩
  cases f_off <;> step*

@[step]
theorem link_step_obs_total (filter : kalman.KalmanFilter) (rtt_var : Std.U64)
    (last : min_rtt.Measurement) (now_ns age_ns : Std.I64) (floor_ns2 : Std.U64)
    (pair_prior : kalman.NoisePrior) :
    sync.link_step_obs filter rtt_var last now_ns age_ns floor_ns2 pair_prior ⦃ _ => True ⦄ := by
  unfold sync.link_step_obs
  step as ⟨pred⟩; step as ⟨_⟩; step as ⟨_⟩; step as ⟨_⟩; step as ⟨_⟩
  cases pred <;> step*

/-! ## `Sync` public method totality -/

@[step]
theorem new_total (settings : sync.SyncSettings) :
    sync.Sync.new settings ⦃ s => s.peer_count = 0#usize ∧ s.peer_active = false ⦄ := by
  unfold sync.Sync.new
  step*

@[step]
theorem set_sender_weight_q16_total (self : sync.Sync) (w : Std.U32) :
    sync.Sync.set_sender_weight_q16 self w ⦃ _ => True ⦄ := by
  unfold sync.Sync.set_sender_weight_q16
  split <;> simp

@[step]
theorem add_peer_loop_total (i : Std.U16) (i1 : Std.U64) (np np1 : kalman.NoisePrior)
    (i2 i3 : Std.U64) (i4 i5 i6 i7 i8 i9 : Std.I64)
    (idx : Std.Usize) (a : Array sync.PeerSlot 15#usize) (identity : Std.U64)
    (weight_q16 : Std.U32) (i10 : Std.Usize) :
    sync.Sync.add_peer_loop i i1 np np1 i2 i3 i4 i5 i6 i7 i8 i9 idx a identity weight_q16 i10
      ⦃ _ => True ⦄ := by
  unfold sync.Sync.add_peer_loop
  apply loop_of_measure (measure := fun k : Std.Usize => idx.val - k.val) (inv := fun _ => True)
    (n := idx.val) (x := i10)
  · intro k _
    unfold sync.Sync.add_peer_loop.body
    by_cases hlt : k < idx
    · rw [ite_t hlt]
      have hk : k.val < idx.val := hlt
      have hnext := usize_sat_add_one_val k idx hk
      step as ⟨s⟩
      step with slice_get_ok s k as ⟨o⟩
      cases o with
      | none =>
        dsimp only; step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
      | some p =>
        dsimp only
        by_cases hc : p.configured = true
        · rw [ite_t hc]
          by_cases hid : p.identity = identity
          · rw [ite_t hid, WP.spec_ok]; trivial
          · rw [ite_f hid]; step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
        · rw [ite_f hc]; step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
    · rw [ite_f hlt]
      step as ⟨ppp⟩; step as ⟨slot⟩
      have hw : (if weight_q16 = 0#u32 then ok sync.WEIGHT_UNITY_Q16 else ok weight_q16) ⦃ _ => True ⦄ := by
        split <;> simp
      step with hw as ⟨wq1⟩
      step as ⟨s, back⟩
      step with slice_get_mut_ok s idx as ⟨o, gb⟩
      cases o with
      | none => simp
      | some _ => step*
  · trivial
  · omega

@[step]
theorem add_peer_total (self : sync.Sync) (identity : Std.U64) (weight_q16 : Std.U32) :
    sync.Sync.add_peer self identity weight_q16 ⦃ _ => True ⦄ := by
  unfold sync.Sync.add_peer
  split
  · simp
  · split
    · simp
    · split
      · simp
      · step*

@[step]
theorem peer_count_total (self : sync.Sync) :
    sync.Sync.impl.peer_count self ⦃ r => r = self.peer_count ⦄ := by
  unfold sync.Sync.impl.peer_count; simp

/-- **Exact specification of `find_peer_loop`:** terminates and returns `some idx`
only when `idx < self.peer_count` and slot `idx` is configured with `identity`. -/
theorem find_peer_loop_spec (self : sync.Sync) (identity : Std.U64) (i : Std.Usize) :
    sync.Sync.find_peer_loop self identity i ⦃ res =>
      ∀ idx : Std.Usize, res = some idx →
        idx.val < self.peer_count.val
        ∧ ∃ p, (Array.to_slice self.peers)[idx]? = some p
          ∧ p.configured = true ∧ p.identity = identity ⦄ := by
  unfold sync.Sync.find_peer_loop
  apply loop_of_measure (measure := fun k : Std.Usize => self.peer_count.val - k.val)
    (inv := fun _ => True) (n := self.peer_count.val) (x := i)
  · intro k _
    unfold sync.Sync.find_peer_loop.body
    by_cases hlt : k < self.peer_count
    · rw [ite_t hlt]
      have hk : k.val < self.peer_count.val := hlt
      have hnext := usize_sat_add_one_val k self.peer_count hk
      step as ⟨s, hs⟩
      step with slice_get_ok s k as ⟨o, ho⟩
      cases o with
      | none =>
        dsimp only; step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
      | some p =>
        dsimp only
        by_cases hc : p.configured = true
        · rw [ite_t hc]
          by_cases hid : p.identity = identity
          · rw [ite_t hid, WP.spec_ok]
            intro idx hidx; injection hidx with hidx; subst hidx
            exact ⟨hk, p, by rw [← hs, ← ho], hc, hid⟩
          · rw [ite_f hid]; step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
        · rw [ite_f hc]; step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]
      intro idx hidx; cases hidx
  · trivial
  · omega

@[step]
theorem find_peer_spec (self : sync.Sync) (identity : Std.U64) :
    sync.Sync.find_peer self identity ⦃ res =>
      ∀ idx : Std.Usize, res = some idx →
        idx.val < self.peer_count.val
        ∧ ∃ p, (Array.to_slice self.peers)[idx]? = some p
          ∧ p.configured = true ∧ p.identity = identity ⦄ :=
  find_peer_loop_spec self identity 0#usize

theorem find_peer_zero_peers (self : sync.Sync) (identity : Std.U64)
    (h0 : self.peer_count = 0#usize) :
    sync.Sync.find_peer self identity ⦃ res => res = none ⦄ := by
  apply WP.spec_mono (find_peer_spec self identity)
  intro res hres
  cases res with
  | none => rfl
  | some idx =>
    have hlt := (hres idx rfl).1
    rw [h0] at hlt
    have : (0#usize : Std.Usize).val = 0 := rfl
    omega

@[step]
theorem snapshot_total (self : sync.Sync) :
    sync.Sync.impl.snapshot self ⦃ r => r = self.snapshot ⦄ := by
  unfold sync.Sync.impl.snapshot; simp

@[step]
theorem probe_interval_ns_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.probe_interval_ns self now_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.probe_interval_ns
  have h1 : (if self.settings.startup_probe_ns > 0#i64
      then ok self.settings.startup_probe_ns else ok sync.DEFAULT_STARTUP_PROBE_NS) ⦃ _ => True ⦄ := by
    split <;> simp
  step with h1 as ⟨st⟩
  have h2 : (if self.settings.steady_probe_ns > 0#i64
      then ok self.settings.steady_probe_ns else ok sync.DEFAULT_STEADY_PROBE_NS) ⦃ _ => True ⦄ := by
    split <;> simp
  step with h2 as ⟨sd⟩
  split
  · step as ⟨dt⟩; split <;> simp
  · simp

@[step]
theorem note_started_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.note_started self now_ns ⦃ s' =>
      s'.peer_count = self.peer_count
      ∧ s'.peers = self.peers
      ∧ s'.peer_active = self.peer_active
      ∧ s'.sender_filter = self.sender_filter
      ∧ s'.sender_min_rtt = self.sender_min_rtt
      ∧ s'.sender_weight_q16 = self.sender_weight_q16
      ∧ s'.last_active_mask = self.last_active_mask
      ∧ s'.epoch = self.epoch ⦄ := by
  unfold sync.Sync.note_started
  split <;> simp

@[step]
theorem reset_sender_clock_loop_total (a : Array sync.RelayedSlot 128#usize) (i : Std.Usize) :
    sync.Sync.reset_sender_clock_loop a i ⦃ _ => True ⦄ := by
  unfold sync.Sync.reset_sender_clock_loop
  apply loop_of_measure (measure := fun p : Array sync.RelayedSlot 128#usize × Std.Usize =>
      sync.MAX_RELAY_TABLE.val - p.2.val)
    (inv := fun _ => True) (n := sync.MAX_RELAY_TABLE.val) (x := (a, i))
  · rintro ⟨arr, k⟩ _
    unfold sync.Sync.reset_sender_clock_loop.body
    dsimp only
    by_cases hlt : k < sync.MAX_RELAY_TABLE
    · rw [ite_t hlt]
      have hk : k.val < sync.MAX_RELAY_TABLE.val := hlt
      have hnext := usize_sat_add_one_val k sync.MAX_RELAY_TABLE hk
      step as ⟨s, back⟩
      step with slice_get_mut_ok s k as ⟨o, gb⟩
      apply WP.spec_bind (Pₘ := fun _ => True)
      · cases o with
        | none => simp
        | some slot =>
          dsimp only
          split
          · split <;> simp
          · simp
      · intro _ _
        step as ⟨k1, hk1⟩
        rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem reset_sender_clock_total (self : sync.Sync) :
    sync.Sync.reset_sender_clock self ⦃ _ => True ⦄ := by
  unfold sync.Sync.reset_sender_clock
  step*

@[step]
theorem set_sender_clock_id_total (self : sync.Sync) (clock_id : Std.U32) :
    sync.Sync.set_sender_clock_id self clock_id ⦃ _ => True ⦄ := by
  unfold sync.Sync.set_sender_clock_id
  split
  · split <;> step*
  · simp

@[step]
theorem report_departed_total (self : sync.Sync) (seq : Std.U64) (t1_ns : Std.I64) :
    sync.Sync.report_departed self seq t1_ns ⦃ s' =>
      s'.peer_count = self.peer_count ∧ s'.peers = self.peers ⦄ := by
  unfold sync.Sync.report_departed
  step*

@[step]
theorem on_sender_echo_total (self : sync.Sync) (echo : packet.Echo) (t4_ns : Std.I64) :
    sync.Sync.on_sender_echo self echo t4_ns ⦃ p =>
      p.2.peer_count = self.peer_count ∧ p.2.peers = self.peers ⦄ := by
  unfold sync.Sync.on_sender_echo
  split
  · rw [WP.spec_ok]; exact ⟨rfl, rfl⟩
  · split
    · rw [WP.spec_ok]; exact ⟨rfl, rfl⟩
    · step as ⟨self1, hpc, hp, _, _, _, _, _, _⟩
      step as ⟨o⟩
      cases o with
      | none => rw [WP.spec_ok]; exact ⟨hpc, hp⟩
      | some t1_ns =>
        step as ⟨o1, smr⟩
        cases o1 with
        | none => rw [WP.spec_ok]; exact ⟨hpc, hp⟩
        | some meas =>
          step as ⟨_, kf⟩
          exact ⟨hpc, hp⟩

@[step]
theorem next_peer_probe_at_loop_total (i : Std.Usize) (a : Array sync.PeerSlot 15#usize)
    (now_ns : Std.I64) (earliest : Option Std.I64) (i1 : Std.Usize) :
    sync.Sync.next_peer_probe_at_loop i a now_ns earliest i1 ⦃ _ => True ⦄ := by
  unfold sync.Sync.next_peer_probe_at_loop
  apply loop_of_measure (measure := fun p : Option Std.I64 × Std.Usize => i.val - p.2.val)
    (inv := fun _ => True) (n := i.val) (x := (earliest, i1))
  · rintro ⟨ea, k⟩ _
    unfold sync.Sync.next_peer_probe_at_loop.body
    dsimp only
    by_cases hlt : k < i
    · rw [ite_t hlt]
      have hk : k.val < i.val := hlt
      have hnext := usize_sat_add_one_val k i hk
      step as ⟨s⟩
      step with slice_get_ok s k as ⟨o⟩
      apply WP.spec_bind (Pₘ := fun _ => True)
      · cases o with
        | none => simp
        | some p =>
          dsimp only
          split
          · apply WP.spec_bind (Pₘ := fun _ => True)
            · split <;> simp
            · intro due _
              apply WP.spec_bind (Pₘ := fun _ => True)
              · cases ea with
                | none => simp
                | some prev => dsimp only; split <;> simp
              · intro _ _; simp
          · simp
      · intro _ _
        step as ⟨k1, hk1⟩
        rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem next_peer_probe_at_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.next_peer_probe_at self now_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.next_peer_probe_at
  split
  · simp
  · step*

@[step]
theorem next_peer_probe_loop_total (ss : sync.SyncSettings) (i : Std.Usize)
    (a : Array sync.PeerSlot 15#usize) (now_ns interval stagger_step : Std.I64) (i1 : Std.Usize) :
    sync.Sync.next_peer_probe_loop ss i a now_ns interval stagger_step i1 ⦃ _ => True ⦄ := by
  unfold sync.Sync.next_peer_probe_loop
  apply loop_of_measure (measure := fun p : Array sync.PeerSlot 15#usize × Std.Usize => i.val - p.2.val)
    (inv := fun _ => True) (n := i.val) (x := (a, i1))
  · rintro ⟨arr, k⟩ _
    unfold sync.Sync.next_peer_probe_loop.body
    dsimp only
    by_cases hlt : k < i
    · rw [ite_t hlt]
      have hk : k.val < i.val := hlt
      have hnext := usize_sat_add_one_val k i hk
      step as ⟨s, back⟩
      step with slice_get_mut_ok s k as ⟨o, gb⟩
      cases o with
      | none =>
        dsimp only; step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
      | some p =>
        dsimp only
        split
        · split
          · split
            · step*
            · step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
          · step*
        · step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem next_peer_probe_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.next_peer_probe self now_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.next_peer_probe
  by_cases h0 : self.peer_count = 0#usize
  · rw [ite_t h0, WP.spec_ok]; trivial
  · rw [ite_f h0]
    step as ⟨self1, _, _, _, _, _, _, _, _⟩
    step as ⟨interval⟩
    have hstag : (if self1.peer_count > 1#usize then do
        let i ← lift (IScalar.cast .I128 interval)
        let i1 ← lift (UScalar.hcast .I128 self1.peer_count)
        let i2 ← fixed.div_floor_wide i i1
        fixed.saturate i2
      else ok 0#i64) ⦃ _ => True ⦄ := by
      split
      · step*
      · simp
    step with hstag as ⟨stagger⟩
    step*

@[step]
theorem peer_probe_departed_total (self : sync.Sync) (peer_idx : Std.Usize)
    (seq : Std.U64) (t1_ns : Std.I64) :
    sync.Sync.peer_probe_departed self peer_idx seq t1_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.peer_probe_departed
  step as ⟨self1, _, _, _, _, _, _, _, _⟩
  step as ⟨s, back⟩
  step with slice_get_mut_ok s peer_idx as ⟨o, gb⟩
  cases o with
  | none => simp
  | some p =>
    dsimp only
    split
    · step*
    · simp

/-- **Strict allowlist enforcement on `on_peer_probe`:** returns `some echo`
only if `probe.stream = self.settings.stream`, `probe.target = self.settings.identity`,
and `probe.prober` is a configured peer in `self.peers[0..self.peer_count)`. -/
@[step]
theorem on_peer_probe_allowlist (self : sync.Sync) (probe : packet.PeerProbe)
    (arrival_ns departure_ns : Std.I64) :
    sync.Sync.on_peer_probe self probe arrival_ns departure_ns ⦃ res =>
      ∀ echo, res = some echo →
        probe.stream = self.settings.stream
        ∧ probe.target = self.settings.identity
        ∧ echo.prober = probe.prober
        ∧ echo.responder = self.settings.identity
        ∧ echo.sequence = probe.sequence
        ∧ echo.arrival = arrival_ns
        ∧ echo.departure = departure_ns
        ∧ ∃ idx : Std.Usize, idx.val < self.peer_count.val
          ∧ ∃ p, (Array.to_slice self.peers)[idx]? = some p
            ∧ p.configured = true ∧ p.identity = probe.prober ⦄ := by
  unfold sync.Sync.on_peer_probe
  by_cases hs : (probe.stream != self.settings.stream) = true
  · rw [ite_t hs, WP.spec_ok]; intro _ h; cases h
  · rw [ite_f hs]
    have hseq : probe.stream = self.settings.stream := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hs; exact hs
    by_cases ht : (probe.target != self.settings.identity) = true
    · rw [ite_t ht, WP.spec_ok]; intro _ h; cases h
    · rw [ite_f ht]
      have hteq : probe.target = self.settings.identity := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at ht; exact ht
      step with find_peer_spec self probe.prober as ⟨o, ho⟩
      cases o with
      | none =>
        simp only [Option.isNone_none, ↓reduceIte, WP.spec_ok]
        intro _ h; cases h
      | some idx =>
        simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        intro echo he; injection he with he; subst he
        obtain ⟨hlt, p, hp, hcfg, hid⟩ := ho idx rfl
        exact ⟨hseq, hteq, rfl, rfl, rfl, rfl, rfl, idx, hlt, p, hp, hcfg, hid⟩

@[step]
theorem on_peer_echo_total (self : sync.Sync) (echo : packet.PeerEcho) (t4_ns : Std.I64) :
    sync.Sync.on_peer_echo self echo t4_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.on_peer_echo
  split
  · simp
  · split
    · simp
    · step as ⟨self1, _, _, _, _, _, _, _, _⟩
      step as ⟨o⟩
      cases o with
      | none => simp
      | some peer_idx =>
        step as ⟨s, back⟩
        step with slice_get_mut_ok s peer_idx as ⟨o1, gb⟩
        cases o1 with
        | none => simp
        | some p =>
          step as ⟨o2⟩
          cases o2 with
          | none => simp
          | some t1_ns =>
            step as ⟨o3, smr⟩
            cases o3 with
            | none => simp
            | some meas => step*

@[step]
theorem next_relay_at_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.next_relay_at self now_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.next_relay_at
  split
  · simp
  · split <;> simp

@[step]
theorem should_relay_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.should_relay self now_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.should_relay
  split
  · simp
  · split
    · simp
    · split <;> step*

@[step]
theorem build_relay_loop_total (i : Std.U64) (i1 : Std.U64) (i2 : Std.I64) (i3 : Std.Usize)
    (a : Array sync.PeerSlot 15#usize) (now_ns : Std.I64)
    (a1 : Array packet.RelayEdge 16#usize) (count i4 : Std.Usize) :
    sync.Sync.build_relay_loop i i1 i2 i3 a now_ns a1 count i4 ⦃ _ => True ⦄ := by
  unfold sync.Sync.build_relay_loop
  apply loop_of_measure (measure := fun p : Array packet.RelayEdge 16#usize × Std.Usize × Std.Usize =>
      i3.val - p.2.2.val)
    (inv := fun _ => True) (n := i3.val) (x := (a1, count, i4))
  · rintro ⟨arr, cnt, k⟩ _
    unfold sync.Sync.build_relay_loop.body
    dsimp only
    by_cases hlt : k < i3
    · rw [ite_t hlt]
      by_cases hc : cnt < packet.MAX_RELAY_EDGES
      · rw [ite_t hc]
        have hk : k.val < i3.val := hlt
        have hnext := usize_sat_add_one_val k i3 hk
        step as ⟨s⟩
        step with slice_get_ok s k as ⟨o⟩
        apply WP.spec_bind (Pₘ := fun _ => True)
        · cases o with
          | none => simp
          | some p =>
            dsimp only
            split
            · split
              · step as ⟨age⟩
                split
                · split
                  · step as ⟨_⟩; step as ⟨_, _, _⟩; step as ⟨_⟩
                    step as ⟨s1, back⟩
                    step with slice_get_mut_ok s1 cnt as ⟨o1, gb⟩
                    cases o1 with
                    | none => simp
                    | some _ => dsimp only; step*
                  · simp
                · simp
              · simp
            · simp
        · rintro ⟨a2, cnt1⟩ -
          step as ⟨k1, hk1⟩
          rw [hk1, hnext]; omega
      · rw [ite_f hc, WP.spec_ok]; trivial
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem build_relay_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.build_relay self now_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.build_relay
  by_cases h0 : self.peer_count = 0#usize
  · rw [ite_t h0, WP.spec_ok]; trivial
  · rw [ite_f h0]
    step as ⟨self1, _, _, _, _, _, _, _, _⟩
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split
      · step as ⟨_⟩
        split
        · step as ⟨age⟩
          apply WP.spec_bind (Pₘ := fun _ => True)
          · split
            · split
              · step as ⟨_⟩; step as ⟨_, _, _⟩; step as ⟨_⟩
                step as ⟨s, back⟩
                step with slice_get_mut_ok s 0#usize as ⟨o, gb⟩
                cases o with
                | none => simp
                | some _ => dsimp only; step*
              · simp
            · simp
          · rintro ⟨a1, i⟩ -; simp
        · simp
      · simp
    · rintro ⟨m, a, cnt⟩ -
      step as ⟨a1, cnt1⟩
      by_cases hc0 : cnt1 = 0#usize
      · rw [ite_t hc0, WP.spec_ok]; trivial
      · rw [ite_f hc0]
        step as ⟨_⟩; step as ⟨_⟩
        apply WP.spec_bind (Pₘ := fun _ => True)
        · split <;> simp
        · intro _ _; step*

@[step]
theorem relayed_at_total (self : sync.Sync) (idx : Std.Usize) :
    sync.Sync.relayed_at self idx ⦃ _ => True ⦄ := by
  unfold sync.Sync.relayed_at
  step as ⟨s⟩
  step with slice_get_ok s idx as ⟨o⟩
  cases o <;> simp

@[step]
theorem find_oldest_relayed_loop_total (self : sync.Sync) (oldest_idx : Std.Usize)
    (oldest_rx : Std.I64) (i : Std.Usize) :
    sync.Sync.find_oldest_relayed_loop self oldest_idx oldest_rx i ⦃ _ => True ⦄ := by
  unfold sync.Sync.find_oldest_relayed_loop
  apply loop_of_measure (measure := fun p : Std.Usize × Std.I64 × Std.Usize =>
      sync.MAX_RELAY_TABLE.val - p.2.2.val)
    (inv := fun _ => True) (n := sync.MAX_RELAY_TABLE.val) (x := (oldest_idx, oldest_rx, i))
  · rintro ⟨oi, orx, k⟩ _
    unfold sync.Sync.find_oldest_relayed_loop.body
    dsimp only
    by_cases hlt : k < sync.MAX_RELAY_TABLE
    · rw [ite_t hlt]
      have hk : k.val < sync.MAX_RELAY_TABLE.val := hlt
      have hnext := usize_sat_add_one_val k sync.MAX_RELAY_TABLE hk
      step as ⟨rs⟩
      have hu : (if rs.last_rx_ns < orx then ok (k, rs.last_rx_ns) else ok (oi, orx)) ⦃ _ => True ⦄ := by
        split <;> simp
      step with hu as ⟨oi1, orx1⟩
      step as ⟨k1, hk1⟩
      rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem find_oldest_relayed_total (self : sync.Sync) :
    sync.Sync.find_oldest_relayed self ⦃ _ => True ⦄ := by
  unfold sync.Sync.find_oldest_relayed; step*

@[step]
theorem find_free_relayed_loop_total (self : sync.Sync) (i : Std.Usize) :
    sync.Sync.find_free_relayed_loop self i ⦃ _ => True ⦄ := by
  unfold sync.Sync.find_free_relayed_loop
  apply loop_of_measure (measure := fun k : Std.Usize => sync.MAX_RELAY_TABLE.val - k.val)
    (inv := fun _ => True) (n := sync.MAX_RELAY_TABLE.val) (x := i)
  · intro k _
    unfold sync.Sync.find_free_relayed_loop.body
    by_cases hlt : k < sync.MAX_RELAY_TABLE
    · rw [ite_t hlt]
      have hk : k.val < sync.MAX_RELAY_TABLE.val := hlt
      have hnext := usize_sat_add_one_val k sync.MAX_RELAY_TABLE hk
      step as ⟨rs⟩
      split
      · step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
      · simp
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem find_free_relayed_total (self : sync.Sync) :
    sync.Sync.find_free_relayed self ⦃ _ => True ⦄ :=
  find_free_relayed_loop_total self 0#usize

@[step]
theorem find_matching_relayed_loop_total (self : sync.Sync) (from_id to_id : Std.U64) (i : Std.Usize) :
    sync.Sync.find_matching_relayed_loop self from_id to_id i ⦃ _ => True ⦄ := by
  unfold sync.Sync.find_matching_relayed_loop
  apply loop_of_measure (measure := fun k : Std.Usize => sync.MAX_RELAY_TABLE.val - k.val)
    (inv := fun _ => True) (n := sync.MAX_RELAY_TABLE.val) (x := i)
  · intro k _
    unfold sync.Sync.find_matching_relayed_loop.body
    by_cases hlt : k < sync.MAX_RELAY_TABLE
    · rw [ite_t hlt]
      have hk : k.val < sync.MAX_RELAY_TABLE.val := hlt
      have hnext := usize_sat_add_one_val k sync.MAX_RELAY_TABLE hk
      step as ⟨slot⟩
      split
      · split
        · split
          · simp
          · step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
        · step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
      · step as ⟨k1, hk1⟩; rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem find_matching_relayed_total (self : sync.Sync) (from_id to_id : Std.U64) :
    sync.Sync.find_matching_relayed self from_id to_id ⦃ _ => True ⦄ :=
  find_matching_relayed_loop_total self from_id to_id 0#usize

local macro "prove_relay_slope_tail" : tactic => `(tactic| (
  step as ⟨_⟩; step as ⟨_⟩; step as ⟨_⟩; step as ⟨_⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · split <;> step*
  · rintro ⟨_, _⟩ -; simp))

@[step]
theorem ingest_relayed_edge_total (self : sync.Sync) (from_id to_id : Std.U64)
    (meas_time_ns rx_ns offset_ns : Std.I64) (variance_ns2 : Std.U64) :
    sync.Sync.ingest_relayed_edge self from_id to_id meas_time_ns rx_ns offset_ns variance_ns2
      ⦃ _ => True ⦄ := by
  unfold sync.Sync.ingest_relayed_edge
  step as ⟨mo⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · cases mo with
    | some _ => simp
    | none =>
      dsimp only
      step as ⟨o⟩
      apply WP.spec_bind (Pₘ := fun _ => True)
      · cases o with
        | some _ => simp
        | none => dsimp only; step*
      · intro _ _; simp
  · rintro ⟨matched, target⟩ -
    step as ⟨s, back⟩
    step with slice_get_mut_ok s target as ⟨o, gb⟩
    cases o with
    | none => simp
    | some slot =>
      dsimp only
      split
      · split
        · simp
        · step as ⟨dt⟩; step as ⟨i⟩; step as ⟨i1⟩; step as ⟨diff⟩
          apply WP.spec_bind (Pₘ := fun _ => True)
          · split <;> simp
          · intro abs_diff _
            apply WP.spec_bind (Pₘ := fun _ => True)
            · by_cases hjm : self.settings.jump_ns > 0#i64
              · simp only [hjm, ↓reduceIte]
                step as ⟨i5⟩
                split
                · simp
                · step as ⟨ref_dt⟩
                  split
                  · step as ⟨_⟩; step as ⟨_⟩; step as ⟨ref_diff⟩
                    apply WP.spec_bind (Pₘ := fun _ => True)
                    · split <;> simp
                    · intro abs_ref _
                      step as ⟨_⟩
                      split
                      · simp
                      · prove_relay_slope_tail
                  · simp
              · simp only [hjm, ↓reduceIte]
                step as ⟨ref_dt⟩
                split
                · step as ⟨_⟩; step as ⟨_⟩; step as ⟨ref_diff⟩
                  apply WP.spec_bind (Pₘ := fun _ => True)
                  · split <;> simp
                  · intro abs_ref _
                    prove_relay_slope_tail
                · simp
            · rintro ⟨i2, i3, b, i4⟩ -
              apply WP.spec_bind (Pₘ := fun _ => True)
              · split
                · simp
                · split <;> simp
              · intro changed _
                split <;> simp
      · simp

private theorem spec_ok_true {α : Type} (x : α) : ok x ⦃ _ => True ⦄ := by
  rw [WP.spec_ok]; trivial

private theorem spec_ite_true {α : Type} {c : Prop} [Decidable c]
    {a b : Result α} (ha : a ⦃ _ => True ⦄) (hb : b ⦃ _ => True ⦄) :
    (if c then a else b) ⦃ _ => True ⦄ := by
  by_cases h : c <;> simp only [h, ↓reduceIte] <;> assumption

local macro "prove_on_peer_relay_ingest" : tactic => `(tactic| (
  step as ⟨_⟩; step as ⟨transit⟩
  refine spec_ite_true ?_ (spec_ok_true _)
  step as ⟨mt⟩; step as ⟨b, s2⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · exact spec_ite_true (spec_ok_true _) (spec_ok_true _)
  · intro _ _; exact spec_ok_true _))

local macro "prove_on_peer_relay_loop_body" k:ident cnt:ident hlt:ident : tactic => `(tactic| (
  have hk : ($k).val < ($cnt).val := $hlt
  have hnext := usize_sat_add_one_val $k $cnt hk
  step as ⟨s⟩
  step with slice_get_ok s $k as ⟨o⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · cases o with
    | none => exact spec_ok_true _
    | some re =>
      dsimp only
      refine spec_ite_true (spec_ite_true (spec_ite_true (spec_ite_true ?_ (spec_ok_true _)) (spec_ok_true _)) (spec_ok_true _)) (spec_ok_true _)
      apply WP.spec_bind (Pₘ := fun _ => True)
      · refine spec_ite_true (spec_ok_true _) ?_
        step as ⟨_⟩; step as ⟨_⟩; step as ⟨_⟩
      · rintro ⟨c_from, c_to, c_off⟩ -
        apply WP.spec_bind (Pₘ := fun _ => True)
        · refine spec_ite_true (spec_ok_true _) ?_
          step as ⟨_⟩
        · intro fk _
          apply WP.spec_bind (Pₘ := fun _ => True)
          · refine spec_ite_true (spec_ok_true _) ?_
            step as ⟨_⟩
          · intro tk _
            refine spec_ite_true (spec_ite_true (spec_ite_true ?_ (spec_ite_true ?_ (spec_ok_true _))) (spec_ok_true _)) (spec_ok_true _)
            · prove_on_peer_relay_ingest
            · prove_on_peer_relay_ingest
  · rintro ⟨s1, acc1⟩ -
    step as ⟨e1, he1⟩
    rw [he1, hnext]; omega))

@[step]
theorem on_peer_relay_loop0_total (self : sync.Sync) (i : Std.U32)
    (a : Array packet.RelayEdge 16#usize)
    (rx_ns relayer_path_ns : Std.I64) (count accepted e : Std.Usize) :
    sync.Sync.on_peer_relay_loop0 self i a rx_ns relayer_path_ns count accepted e ⦃ _ => True ⦄ := by
  unfold sync.Sync.on_peer_relay_loop0
  apply loop_of_measure (measure := fun p : sync.Sync × Std.Usize × Std.Usize => count.val - p.2.2.val)
    (inv := fun _ => True) (n := count.val) (x := (self, accepted, e))
  · rintro ⟨s, acc, k⟩ _
    unfold sync.Sync.on_peer_relay_loop0.body; dsimp only
    by_cases hlt : k < count
    · rw [ite_t hlt]; prove_on_peer_relay_loop_body k count hlt
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem on_peer_relay_loop1_total (self : sync.Sync) (i : Std.U32)
    (a : Array packet.RelayEdge 16#usize)
    (rx_ns relayer_path_ns : Std.I64) (count accepted e : Std.Usize) :
    sync.Sync.on_peer_relay_loop1 self i a rx_ns relayer_path_ns count accepted e ⦃ _ => True ⦄ := by
  unfold sync.Sync.on_peer_relay_loop1
  apply loop_of_measure (measure := fun p : sync.Sync × Std.Usize × Std.Usize => count.val - p.2.2.val)
    (inv := fun _ => True) (n := count.val) (x := (self, accepted, e))
  · rintro ⟨s, acc, k⟩ _
    unfold sync.Sync.on_peer_relay_loop1.body; dsimp only
    by_cases hlt : k < count
    · rw [ite_t hlt]; prove_on_peer_relay_loop_body k count hlt
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem on_peer_relay_total (self : sync.Sync) (relay : packet.PeerRelay) (rx_ns : Std.I64) :
    sync.Sync.on_peer_relay self relay rx_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.on_peer_relay
  split
  · simp
  · step as ⟨o⟩
    cases o with
    | none => simp
    | some peer_idx =>
      dsimp only
      step as ⟨self1, _, _, _, _, _, _, _, _⟩
      step as ⟨s, back⟩
      step with slice_get_mut_ok s peer_idx as ⟨o1, gb⟩
      cases o1 with
      | none => simp
      | some p =>
        dsimp only
        split
        · split
          · simp
          · step as ⟨rpn⟩; step as ⟨i⟩
            apply WP.spec_bind (Pₘ := fun _ => True)
            · split
              · simp
              · step*
            · rintro ⟨a, cnt⟩ -
              step as ⟨s2, acc⟩
              split <;> simp
        · step as ⟨rpn⟩; step as ⟨i⟩
          apply WP.spec_bind (Pₘ := fun _ => True)
          · split
            · simp
            · step*
          · rintro ⟨a, cnt⟩ -
            step as ⟨s2, acc⟩
            split <;> simp

@[step]
theorem active_peer_mask_loop_total (self : sync.Sync) (now_ns : Std.I64)
    (mask : Std.U32) (i : Std.Usize) :
    sync.Sync.active_peer_mask_loop self now_ns mask i ⦃ _ => True ⦄ := by
  unfold sync.Sync.active_peer_mask_loop
  apply loop_of_measure (measure := fun p : sync.Sync × Std.U32 × Std.Usize =>
      p.1.peer_count.val - p.2.2.val)
    (inv := fun _ => True) (n := self.peer_count.val) (x := (self, mask, i))
  · rintro ⟨s, m, k⟩ _
    unfold sync.Sync.active_peer_mask_loop.body; dsimp only
    by_cases hlt : k < s.peer_count
    · rw [ite_t hlt]
      have hk : k.val < s.peer_count.val := hlt
      have hnext := usize_sat_add_one_val k s.peer_count hk
      step as ⟨sl⟩
      step with slice_get_ok sl k as ⟨o⟩
      apply WP.spec_bind (Pₘ := fun _ => True)
      · cases o with
        | none => simp
        | some p =>
          dsimp only
          split
          · split
            · step as ⟨i1⟩
              apply WP.spec_bind (Pₘ := fun _ => True)
              · split <;> step*
              · intro _ _; simp
            · simp
          · simp
      · rintro ⟨ss, m1⟩ -
        step as ⟨k1, hk1⟩
        rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · dsimp only; omega

@[step]
theorem active_peer_mask_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.active_peer_mask self now_ns ⦃ _ => True ⦄ :=
  active_peer_mask_loop_total self now_ns 0#u32 0#usize

theorem active_peer_mask_zero_peers (self : sync.Sync) (now_ns : Std.I64)
    (h0 : self.peer_count = 0#usize) :
    sync.Sync.active_peer_mask self now_ns ⦃ m => m = 0#u32 ⦄ := by
  unfold sync.Sync.active_peer_mask sync.Sync.active_peer_mask_loop
  apply loop_step; unfold sync.Sync.active_peer_mask_loop.body; dsimp only
  rw [h0, ite_f (by decide), WP.spec_ok]

@[step]
theorem fusion_interval_ns_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.fusion_interval_ns self now_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.fusion_interval_ns; step*

@[step]
theorem host_index_of_total (self : sync.Sync) (id : Std.U64) :
    sync.Sync.host_index_of self id ⦃ _ => True ⦄ := by
  unfold sync.Sync.host_index_of
  split
  · simp
  · split
    · simp
    · step as ⟨o⟩
      cases o with
      | none => simp
      | some idx => step as ⟨h⟩; split <;> simp

@[step]
theorem publish_star_spec (self : sync.Sync) :
    sync.Sync.publish_star self ⦃ p =>
      p.1.peer_active = false
      ∧ p.1.active_peers = 0#u8
      ∧ p.1.diff_var_ns2 = 0#u64
      ∧ p.1.fleet_line = sync.ZERO_LINE
      ∧ p.2.peer_count = self.peer_count
      ∧ p.2.peer_active = false
      ∧ p.2.snapshot = p.1
      ∧ (∀ line, kalman.KalmanFilter.to_line self.sender_filter = ok (some line) →
          p.1.valid = true ∧ p.1.common_line = line) ⦄ := by
  unfold sync.Sync.publish_star
  have hpa : (if self.peer_active then do
        let i4 ← lift (core.num.U32.wrapping_add self.epoch 1#u32)
        ok (false, 0#u32, 0#u32, 0#u32, i4)
      else ok (self.peer_active, self.last_direct_mask, self.last_active_mask,
               self.last_sender_relay_mask, self.epoch))
      ⦃ q => q.1 = false ⦄ := by
    split
    · step*
    · rename_i h; rw [WP.spec_ok]; cases hb : self.peer_active <;> simp_all
  step with hpa as ⟨b, i, i1, i2, i3, hb⟩
  have htl := Kalman.to_line_spec self.sender_filter
  cases ho : kalman.KalmanFilter.to_line self.sender_filter with
  | div => rw [ho] at htl; simp [WP.spec_div] at htl
  | vis e k => rw [ho] at htl; simp [WP.spec_vis] at htl
  | ret o =>
    rw [bind_ok]
    cases o with
    | none =>
      rw [WP.spec_ok]
      refine ⟨?_, ?_, ?_, ?_, rfl, hb, rfl, ?_⟩
      · unfold sync.SyncSnapshot.EMPTY; rfl
      · unfold sync.SyncSnapshot.EMPTY; rfl
      · unfold sync.SyncSnapshot.EMPTY; rfl
      · unfold sync.SyncSnapshot.EMPTY sync.ZERO_LINE; rfl
      · intro line hline; simp at hline
    | some line =>
      step as ⟨i2⟩; step as ⟨var_ns2⟩
      apply WP.spec_bind (MinRtt.path_ns_spec self.sender_min_rtt)
      intro i3 _
      rw [WP.spec_ok]
      refine ⟨rfl, rfl, rfl, rfl, rfl, hb, rfl, ?_⟩
      intro line' hline
      injection hline with heq
      exact ⟨rfl, heq⟩

@[step]
theorem initial_peer_frequencies_loop_total (self : sync.Sync) (a : Array Bool 17#usize)
    (sum_peer_freq : Std.I128) (i : Std.Usize) :
    sync.Sync.initial_peer_frequencies_loop self a sum_peer_freq i ⦃ _ => True ⦄ := by
  unfold sync.Sync.initial_peer_frequencies_loop
  apply loop_of_measure (measure := fun p : Std.I128 × Std.Usize => self.peer_count.val - p.2.val)
    (inv := fun _ => True) (n := self.peer_count.val) (x := (sum_peer_freq, i))
  · rintro ⟨spf, k⟩ _
    unfold sync.Sync.initial_peer_frequencies_loop.body; dsimp only
    by_cases hlt : k < self.peer_count
    · rw [ite_t hlt]
      have hk : k.val < self.peer_count.val := hlt
      have hnext := usize_sat_add_one_val k self.peer_count hk
      step as ⟨h⟩; step as ⟨s⟩; step as ⟨b⟩
      apply WP.spec_bind (Pₘ := fun _ => True)
      · split
        · step as ⟨s1⟩
          step with slice_get_ok s1 k as ⟨o⟩
          cases o with
          | none => simp
          | some p => dsimp only; split <;> step*
        · simp
      · intro _ _
        step as ⟨k1, hk1⟩
        rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem initial_peer_frequencies_total (self : sync.Sync) (solved : blue.BlueResult) :
    sync.Sync.initial_peer_frequencies self solved ⦃ _ => True ⦄ := by
  unfold sync.Sync.initial_peer_frequencies
  step as ⟨dim⟩
  split
  · step*
  · step as ⟨kf, spf⟩; step as ⟨_⟩; step as ⟨_⟩; step as ⟨b⟩
    split <;> step*

local macro "prove_reanchor_both_modes" : tactic => `(tactic| (
  step as ⟨x⟩
  rcases x with ⟨_, _⟩
  step*))

local macro "prove_reanchor_common_shift_diff" : tactic => `(tactic| (
  step as ⟨_⟩; step as ⟨o⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · cases o with
    | none => simp
    | some _ => step*
  · intro _ _; simp))

@[step]
theorem update_modal_filters_total (self : sync.Sync) (now_ns : Std.I64)
    (solved : blue.BlueResult) (direct_mask reachable_mask sender_relay_mask : Std.U32) :
    sync.Sync.update_modal_filters self now_ns solved direct_mask reachable_mask sender_relay_mask
      ⦃ _ => True ⦄ := by
  unfold sync.Sync.update_modal_filters
  step as ⟨dim⟩; step as ⟨np⟩; step as ⟨com_prior⟩; step as ⟨i⟩; step as ⟨diff_prior⟩
  step as ⟨kf⟩; step as ⟨kf1⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · split
    · split <;> simp
    · simp
  · intro amc _
    apply WP.spec_bind (Pₘ := fun _ => True)
    · by_cases hamc : amc = true
      · simp only [hamc, ↓reduceIte]
        step as ⟨i4⟩
        apply WP.spec_bind (Pₘ := fun _ => True)
        · by_cases hpa : self.peer_active = true
          · simp only [hpa, ↓reduceIte]
            by_cases hsr : (sender_relay_mask != self.last_sender_relay_mask) = true
            · simp only [hsr, ↓reduceIte]
              apply WP.spec_bind (Pₘ := fun _ => True)
              · step as ⟨b4⟩
                by_cases hb4 : b4 = true
                · simp only [hb4, ↓reduceIte]
                  step as ⟨b5⟩
                  apply WP.spec_bind (Pₘ := fun _ => True)
                  · split <;> step*
                  · intro c_freq _; prove_reanchor_common_shift_diff
                · simp only [hb4, Bool.false_eq_true, ↓reduceIte]; prove_reanchor_both_modes
              · rintro ⟨_, _, _, _, _⟩ -; simp
            · simp only [hsr, Bool.false_eq_true, ↓reduceIte]
              step as ⟨b3⟩
              by_cases hb3 : b3 = true
              · simp only [hb3, ↓reduceIte]
                step as ⟨b4⟩
                by_cases hb4 : b4 = true
                · simp only [hb4, ↓reduceIte]
                  step as ⟨o⟩
                  apply WP.spec_bind (Pₘ := fun _ => True)
                  · cases o with
                    | none => simp
                    | some _ => step*
                  · rintro ⟨_, _⟩ -; simp
                · simp only [hb4, Bool.false_eq_true, ↓reduceIte]
                  prove_reanchor_both_modes
              · simp only [hb3, Bool.false_eq_true, ↓reduceIte]
                prove_reanchor_both_modes
          · simp only [hpa, Bool.false_eq_true, ↓reduceIte]
            prove_reanchor_both_modes
        · rintro ⟨_, _, _, _, _, _⟩ -; simp
      · simp only [hamc, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    · rintro ⟨kf2, kf3, b, i1, i2, i3, ac, ad⟩ -
      apply WP.spec_bind (Pₘ := fun _ => True)
      · split
        · simp
        · step*
      · intro kf4 _
        split
        · simp
        · step*

@[step]
theorem step_loop0_total
    (ss : sync.SyncSettings) (b : Bool) (i : Std.I64) (i1 : Std.U32)
    (a : arrivals.Arrivals 8#usize) (smr : min_rtt.SlidingMinRtt 8#usize)
    (kf : kalman.KalmanFilter) (b1 : Bool) (i2 : Std.U64) (i3 i4 i5 : Std.I64) (i6 : Std.U64)
    (i7 : Std.U32) (b2 : Bool) (i8 : Std.Usize)
    (a1 : Array sync.PeerSlot 15#usize) (a2 : Array sync.RelayedSlot 128#usize)
    (i9 : Std.U64) (b3 : Bool) (i10 : Std.I64) (kf1 kf2 : kalman.KalmanFilter)
    (b4 : Bool) (i11 i12 i13 i14 : Std.U32) (b5 b6 : Bool) (i15 : Std.I64)
    (ss1 : sync.SyncSnapshot) (now_ns : Std.I64) (sender_relay_mask : Std.U32)
    (has_relayed_sender : Bool) (sr : Std.Usize) :
    sync.Sync.step_loop0 ss b i i1 a smr kf b1 i2 i3 i4 i5 i6 i7 b2 i8 a1 a2 i9 b3 i10 kf1 kf2
      b4 i11 i12 i13 i14 b5 b6 i15 ss1 now_ns sender_relay_mask has_relayed_sender sr
      ⦃ _ => True ⦄ := by
  unfold sync.Sync.step_loop0
  apply loop_of_measure
    (measure := fun p : sync.SyncSettings × Std.U32 × Bool × Std.Usize =>
      sync.MAX_RELAY_TABLE.val - p.2.2.2.val)
    (inv := fun _ => True) (n := sync.MAX_RELAY_TABLE.val)
    (x := (ss, sender_relay_mask, has_relayed_sender, sr))
  · rintro ⟨ss2, srm, hrs, k⟩ _
    unfold sync.Sync.step_loop0.body; dsimp only
    by_cases hlt : k < sync.MAX_RELAY_TABLE
    · rw [ite_t hlt]
      have hk : k.val < sync.MAX_RELAY_TABLE.val := hlt
      have hnext := usize_sat_add_one_val k sync.MAX_RELAY_TABLE hk
      step as ⟨sl⟩
      step with slice_get_ok sl k as ⟨o⟩
      apply WP.spec_bind (Pₘ := fun _ => True)
      · cases o with
        | none => simp
        | some slot =>
          dsimp only
          split
          · split
            · step as ⟨age⟩
              split
              · apply WP.spec_bind (Pₘ := fun _ => True)
                · split
                  · step as ⟨o1⟩
                    cases o1 with
                    | none => simp
                    | some p_idx =>
                      dsimp only; step as ⟨_⟩; step as ⟨_⟩; step as ⟨_⟩; step as ⟨_⟩
                  · simp
                · rintro ⟨_, _⟩ -; simp
              · simp
            · simp
          · simp
      · rintro ⟨_, _, _⟩ -
        step as ⟨k1, hk1⟩
        rw [hk1, hnext]; omega
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

local macro "prove_step_peer_edges_body" k:ident i1:ident ec:ident hlt:ident : tactic => `(tactic| (
  have hk : ($k).val < ($i1).val := $hlt
  have hnext := usize_sat_add_one_val $k $i1 hk
  step as ⟨_⟩; step as ⟨_⟩; step as ⟨i4⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · split
    · step as ⟨s⟩
      step with slice_get_ok s $k as ⟨o⟩
      cases o with
      | none => simp
      | some p =>
        dsimp only
        split
        · step as ⟨age⟩; step as ⟨_⟩; step as ⟨_, _⟩; step as ⟨_⟩; step as ⟨th⟩
          split
          · step as ⟨s1, back⟩
            step with slice_get_mut_ok s1 $ec as ⟨o1, gb⟩
            cases o1 with
            | none => simp
            | some _ => dsimp only; step*
          · simp
        · simp
    · simp
  · rintro ⟨e1, ec1⟩ -
    step as ⟨k1, hk1⟩
    rw [hk1, hnext]; omega))

@[step]
theorem step_loop1_total (i : Std.U64) (i1 : Std.Usize) (a : Array sync.PeerSlot 15#usize)
    (now_ns : Std.I64) (active_mask : Std.U32) (host_count : Std.Usize)
    (edges : Array blue.EdgeObs 136#usize) (edge_count : Std.Usize)
    (peer_pair_prior : kalman.NoisePrior) (i2 : Std.Usize) :
    sync.Sync.step_loop1 i i1 a now_ns active_mask host_count edges edge_count peer_pair_prior i2
      ⦃ _ => True ⦄ := by
  unfold sync.Sync.step_loop1
  apply loop_of_measure (measure := fun p : Array blue.EdgeObs 136#usize × Std.Usize × Std.Usize =>
      i1.val - p.2.2.val)
    (inv := fun _ => True) (n := i1.val) (x := (edges, edge_count, i2))
  · rintro ⟨es, ec, k⟩ _
    unfold sync.Sync.step_loop1.body; dsimp only
    by_cases hlt : k < i1
    · rw [ite_t hlt]
      by_cases hec : ec < blue.MAX_EDGES
      · rw [ite_t hec]; prove_step_peer_edges_body k i1 ec hlt
      · rw [ite_f hec, WP.spec_ok]; trivial
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem step_loop4_total (i : Std.U64) (i1 : Std.Usize) (a : Array sync.PeerSlot 15#usize)
    (now_ns : Std.I64) (active_mask : Std.U32) (host_count : Std.Usize)
    (edges : Array blue.EdgeObs 136#usize) (edge_count : Std.Usize)
    (peer_pair_prior : kalman.NoisePrior) (i2 : Std.Usize) :
    sync.Sync.step_loop4 i i1 a now_ns active_mask host_count edges edge_count peer_pair_prior i2
      ⦃ _ => True ⦄ := by
  unfold sync.Sync.step_loop4
  apply loop_of_measure (measure := fun p : Array blue.EdgeObs 136#usize × Std.Usize × Std.Usize =>
      i1.val - p.2.2.val)
    (inv := fun _ => True) (n := i1.val) (x := (edges, edge_count, i2))
  · rintro ⟨es, ec, k⟩ _
    unfold sync.Sync.step_loop4.body; dsimp only
    by_cases hlt : k < i1
    · rw [ite_t hlt]
      by_cases hec : ec < blue.MAX_EDGES
      · rw [ite_t hec]; prove_step_peer_edges_body k i1 ec hlt
      · rw [ite_f hec, WP.spec_ok]; trivial
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

local macro "prove_step_relayed_body" k:ident ec:ident hlt:ident : tactic => `(tactic| (
  have hk : ($k).val < sync.MAX_RELAY_TABLE.val := $hlt
  have hnext := usize_sat_add_one_val $k sync.MAX_RELAY_TABLE hk
  step as ⟨s⟩
  step with slice_get_ok s $k as ⟨o⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · cases o with
    | none => simp
    | some slot =>
      dsimp only
      split
      · step as ⟨age⟩
        split
        · split
          · step as ⟨from_h⟩; step as ⟨to_h⟩
            cases from_h with
            | none => simp
            | some fh =>
              dsimp only
              cases to_h with
              | none => simp
              | some th =>
                dsimp only
                split
                · split
                  · split
                    · apply WP.spec_bind (Pₘ := fun _ => True)
                      · split
                        · simp
                        · split <;> simp
                      · intro pr _
                        step as ⟨extrap⟩; step as ⟨ve⟩
                        step as ⟨s1, back⟩
                        step with slice_get_mut_ok s1 $ec as ⟨o1, gb⟩
                        cases o1 with
                        | none => simp
                        | some _ => dsimp only; step*
                    · simp
                  · simp
                · simp
          · simp
        · simp
      · simp
  · rintro ⟨e1, ec1⟩ -
    step as ⟨r1, hr1⟩
    rw [hr1, hnext]; omega))

@[step]
theorem step_loop2_total
    (i : Std.U16) (i1 : Std.U64) (np np1 : kalman.NoisePrior)
    (i2 i3 : Std.U64) (i4 i5 i6 i7 i8 i9 : Std.I64)
    (b : Bool) (i10 : Std.I64) (i11 : Std.U32)
    (a : arrivals.Arrivals 8#usize) (smr : min_rtt.SlidingMinRtt 8#usize)
    (kf : kalman.KalmanFilter) (b1 : Bool) (i12 : Std.U64) (i13 i14 i15 : Std.I64) (i16 : Std.U64)
    (i17 : Std.U32) (b2 : Bool) (i18 : Std.Usize)
    (a1 : Array sync.PeerSlot 15#usize) (a2 : Array sync.RelayedSlot 128#usize)
    (i19 : Std.U64) (b3 : Bool) (i20 : Std.I64) (kf1 kf2 : kalman.KalmanFilter)
    (b4 : Bool) (i21 i22 i23 i24 : Std.U32) (b5 b6 : Bool) (i25 : Std.I64)
    (ss : sync.SyncSnapshot) (now_ns : Std.I64) (host_count : Std.Usize)
    (edges : Array blue.EdgeObs 136#usize) (edge_count : Std.Usize)
    (sender_pair_prior peer_pair_prior : kalman.NoisePrior) (r : Std.Usize) :
    sync.Sync.step_loop2 i i1 np np1 i2 i3 i4 i5 i6 i7 i8 i9 b i10 i11 a smr kf b1 i12 i13 i14 i15
      i16 i17 b2 i18 a1 a2 i19 b3 i20 kf1 kf2 b4 i21 i22 i23 i24 b5 b6 i25 ss now_ns host_count
      edges edge_count sender_pair_prior peer_pair_prior r ⦃ _ => True ⦄ := by
  unfold sync.Sync.step_loop2
  apply loop_of_measure (measure := fun p : Array blue.EdgeObs 136#usize × Std.Usize × Std.Usize =>
      sync.MAX_RELAY_TABLE.val - p.2.2.val)
    (inv := fun _ => True) (n := sync.MAX_RELAY_TABLE.val) (x := (edges, edge_count, r))
  · rintro ⟨es, ec, k⟩ _
    unfold sync.Sync.step_loop2.body; dsimp only
    by_cases hlt : k < sync.MAX_RELAY_TABLE
    · rw [ite_t hlt]
      by_cases hec : ec < blue.MAX_EDGES
      · rw [ite_t hec]; prove_step_relayed_body k ec hlt
      · rw [ite_f hec, WP.spec_ok]; trivial
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem step_loop5_total
    (i : Std.U16) (i1 : Std.U64) (np np1 : kalman.NoisePrior)
    (i2 i3 : Std.U64) (i4 i5 i6 i7 i8 i9 : Std.I64)
    (b : Bool) (i10 : Std.I64) (i11 : Std.U32)
    (a : arrivals.Arrivals 8#usize) (smr : min_rtt.SlidingMinRtt 8#usize)
    (kf : kalman.KalmanFilter) (b1 : Bool) (i12 : Std.U64) (i13 i14 i15 : Std.I64) (i16 : Std.U64)
    (i17 : Std.U32) (b2 : Bool) (i18 : Std.Usize)
    (a1 : Array sync.PeerSlot 15#usize) (a2 : Array sync.RelayedSlot 128#usize)
    (i19 : Std.U64) (b3 : Bool) (i20 : Std.I64) (kf1 kf2 : kalman.KalmanFilter)
    (b4 : Bool) (i21 i22 i23 i24 : Std.U32) (b5 b6 : Bool) (i25 : Std.I64)
    (ss : sync.SyncSnapshot) (now_ns : Std.I64) (host_count : Std.Usize)
    (edges : Array blue.EdgeObs 136#usize) (edge_count : Std.Usize)
    (sender_pair_prior peer_pair_prior : kalman.NoisePrior) (r : Std.Usize) :
    sync.Sync.step_loop5 i i1 np np1 i2 i3 i4 i5 i6 i7 i8 i9 b i10 i11 a smr kf b1 i12 i13 i14 i15
      i16 i17 b2 i18 a1 a2 i19 b3 i20 kf1 kf2 b4 i21 i22 i23 i24 b5 b6 i25 ss now_ns host_count
      edges edge_count sender_pair_prior peer_pair_prior r ⦃ _ => True ⦄ := by
  unfold sync.Sync.step_loop5
  apply loop_of_measure (measure := fun p : Array blue.EdgeObs 136#usize × Std.Usize × Std.Usize =>
      sync.MAX_RELAY_TABLE.val - p.2.2.val)
    (inv := fun _ => True) (n := sync.MAX_RELAY_TABLE.val) (x := (edges, edge_count, r))
  · rintro ⟨es, ec, k⟩ _
    unfold sync.Sync.step_loop5.body; dsimp only
    by_cases hlt : k < sync.MAX_RELAY_TABLE
    · rw [ite_t hlt]
      by_cases hec : ec < blue.MAX_EDGES
      · rw [ite_t hec]; prove_step_relayed_body k ec hlt
      · rw [ite_f hec, WP.spec_ok]; trivial
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

local macro "prove_step_mask_body" k:ident i:ident hlt:ident : tactic => `(tactic| (
  have hk : ($k).val < ($i).val := $hlt
  have hnext := usize_sat_add_one_val $k $i hk
  step as ⟨h⟩; step as ⟨s⟩; step as ⟨b⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · split <;> step*
  · intro rm1 _
    step as ⟨k1, hk1⟩
    rw [hk1, hnext]; omega))

@[step]
theorem step_loop3_total (i : Std.Usize) (a : Array Bool 17#usize)
    (reachable_mask : Std.U32) (p_idx : Std.Usize) :
    sync.Sync.step_loop3 i a reachable_mask p_idx ⦃ _ => True ⦄ := by
  unfold sync.Sync.step_loop3
  apply loop_of_measure (measure := fun p : Std.U32 × Std.Usize => i.val - p.2.val)
    (inv := fun _ => True) (n := i.val) (x := (reachable_mask, p_idx))
  · rintro ⟨rm, k⟩ _
    unfold sync.Sync.step_loop3.body; dsimp only
    by_cases hlt : k < i
    · rw [ite_t hlt]; prove_step_mask_body k i hlt
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

@[step]
theorem step_loop6_total (i : Std.Usize) (a : Array Bool 17#usize)
    (reachable_mask : Std.U32) (p_idx : Std.Usize) :
    sync.Sync.step_loop6 i a reachable_mask p_idx ⦃ _ => True ⦄ := by
  unfold sync.Sync.step_loop6
  apply loop_of_measure (measure := fun p : Std.U32 × Std.Usize => i.val - p.2.val)
    (inv := fun _ => True) (n := i.val) (x := (reachable_mask, p_idx))
  · rintro ⟨rm, k⟩ _
    unfold sync.Sync.step_loop6.body; dsimp only
    by_cases hlt : k < i
    · rw [ite_t hlt]; prove_step_mask_body k i hlt
    · rw [ite_f hlt, WP.spec_ok]; trivial
  · trivial
  · omega

local macro "prove_sender_edge_insert" : tactic => `(tactic| (
  step as ⟨_⟩; step as ⟨_, _⟩; step as ⟨_⟩
  step as ⟨s, back⟩
  step with slice_get_mut_ok s 0#usize as ⟨o, gb⟩
  cases o with
  | none => simp
  | some _ => step*))

local macro "prove_step_fuse_branch" : tactic => `(tactic| (
  step as ⟨hc⟩
  apply WP.spec_bind (Pₘ := fun _ => True)
  · split <;> simp
  · intro hc1 _
    generalize Array.repeat 136#usize blue.EdgeObs.ZERO = edges_arr
    step as ⟨spp⟩; step as ⟨ppp⟩
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split
      · split
        · prove_sender_edge_insert
        · split
          · simp
          · prove_sender_edge_insert
      · simp
    · rintro ⟨e1, ec⟩ -
      step as ⟨e2, ec1⟩; step as ⟨e3, ec2⟩; step as ⟨s⟩; step as ⟨solved⟩
      by_cases hle : solved.active_count ≤ 1#usize
      · rw [ite_t hle]; step*
      · rw [ite_f hle]
        step as ⟨rm⟩
        step as ⟨self2⟩
        step as ⟨o⟩; step as ⟨o1⟩
        cases o with
        | none => step*
        | some _ =>
          cases o1 with
          | none => step*
          | some _ => step*))

@[step]
theorem step_total (self : sync.Sync) (now_ns : Std.I64) :
    sync.Sync.step self now_ns ⦃ _ => True ⦄ := by
  unfold sync.Sync.step
  step as ⟨self1, _, _, _, _, _, _, _, _⟩
  step as ⟨active_mask⟩
  by_cases ham : active_mask = 0#u32
  · rw [ite_t ham]; step*
  · rw [ite_f ham]
    step as ⟨sender_age⟩
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split
      · split <;> simp
      · simp
    · rintro ⟨ss, sf⟩ -
      apply WP.spec_bind (Pₘ := fun _ => True)
      · split
        · step as ⟨_⟩; split <;> simp
        · simp
      · intro srm0 _
        step as ⟨ss1, srm1, hrs⟩
        apply WP.spec_bind (Pₘ := fun _ => True)
        · split
          · split <;> simp
          · simp
        · intro mc _
          apply WP.spec_bind (Pₘ := fun _ => True)
          · split
            · step*
            · simp
          · intro fd _
            by_cases hmc : mc = true
            · rw [ite_t hmc]; prove_step_fuse_branch
            · rw [ite_f hmc]
              by_cases hdir : self1.dirty = true
              · rw [ite_t hdir]
                by_cases hfd : fd = true
                · rw [ite_t hfd]; prove_step_fuse_branch
                · rw [ite_f hfd, WP.spec_ok]; trivial
              · rw [ite_f hdir, WP.spec_ok]; trivial

/-! ## Exact Star degeneration (`peer_count = 0`) -/

/-- **Zero-peer Star silence:** when `self.peer_count = 0`, `Sync` never schedules
or builds peer probes or relays, and rejects incoming peer probes and relays. -/
theorem zero_peers_no_peer_traffic (self : sync.Sync) (now_ns arr dep : Std.I64)
    (probe : packet.PeerProbe) (relay : packet.PeerRelay) (h0 : self.peer_count = 0#usize) :
    sync.Sync.next_peer_probe_at self now_ns = ok none
    ∧ sync.Sync.next_peer_probe self now_ns = ok (none, self)
    ∧ sync.Sync.should_relay self now_ns = ok false
    ∧ sync.Sync.build_relay self now_ns = ok (none, self)
    ∧ sync.Sync.on_peer_probe self probe arr dep ⦃ r => r = none ⦄
    ∧ sync.Sync.on_peer_relay self relay now_ns ⦃ p => p = (0#usize, self) ⦄ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sync.Sync.next_peer_probe_at; rw [h0, ite_t rfl]
  · unfold sync.Sync.next_peer_probe; rw [h0, ite_t rfl]
  · unfold sync.Sync.should_relay; rw [h0, ite_t rfl]
  · unfold sync.Sync.build_relay; rw [h0, ite_t rfl]
  · apply WP.spec_mono (on_peer_probe_allowlist self probe arr dep)
    intro res hres
    cases res with
    | none => rfl
    | some echo =>
      obtain ⟨_, _, _, _, _, _, _, idx, hlt, _⟩ := hres echo rfl
      rw [h0] at hlt; have : (0#usize : Std.Usize).val = 0 := rfl; omega
  · unfold sync.Sync.on_peer_relay
    by_cases hs : (relay.stream != self.settings.stream) = true
    · rw [ite_t hs, WP.spec_ok]
    · rw [ite_f hs]
      step with find_peer_zero_peers self relay.sender h0 as ⟨o, ho⟩
      subst ho; rw [WP.spec_ok]

/-- **Exact Star degeneration of `Sync.step`:** with `peer_count = 0`, `Sync.step`
always publishes a Star snapshot (`peer_active = false`, `active_peers = 0`,
`diff_var_ns2 = 0`, `fleet_line = ZERO_LINE`). When `sender_filter.to_line`
returns `some line`, `snap.valid = true` and `snap.common_line = line`. -/
theorem step_zero_peers_star (self : sync.Sync) (now_ns : Std.I64)
    (h0 : self.peer_count = 0#usize) :
    sync.Sync.step self now_ns ⦃ p =>
      p.1.peer_active = false
      ∧ p.1.active_peers = 0#u8
      ∧ p.1.diff_var_ns2 = 0#u64
      ∧ p.1.fleet_line = sync.ZERO_LINE
      ∧ p.2.peer_count = 0#usize
      ∧ p.2.peer_active = false
      ∧ p.2.snapshot = p.1
      ∧ (∀ line, kalman.KalmanFilter.to_line self.sender_filter = ok (some line) →
          p.1.valid = true ∧ p.1.common_line = line) ⦄ := by
  unfold sync.Sync.step
  step with note_started_total self now_ns as ⟨self1, hpc1, _, _, hsf1, _, _, _, _⟩
  have hpc1_0 : self1.peer_count = 0#usize := by rw [hpc1, h0]
  step with active_peer_mask_zero_peers self1 now_ns hpc1_0 as ⟨am, ham⟩
  subst ham; rw [ite_t rfl]
  apply WP.spec_mono (publish_star_spec self1)
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
  refine ⟨h1, h2, h3, h4, by rw [h5, hpc1_0], h6, h7, ?_⟩
  intro line hline
  exact h8 line (by rw [hsf1]; exact hline)

end Unisono.Sync
