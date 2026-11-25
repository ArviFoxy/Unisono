/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay
public import Unisono.Spec.AtLatency
public import Unisono.Spec.Models.Bounded
public import Unisono.Spec.Models.Ideal
public import Unisono.Spec.Topologies

/-!
# Fundamental limits and Star-vs-Peer separation on `Unisono.Spec`

This module collects topology-dependent lower bounds, speed-bound helpers,
and the two-sided Star-vs-Peer asymmetry separation theorem directly in the
official `Unisono.Spec` event-driven run model (`Unisono.Spec.Solution`,
`Unisono.Spec.World`, `Unisono.Spec.Objectives`).

## Contents

1. **Speed-bound helper (`withinSpeed_of_step_bound`, `exists_asked_of_plays_some`).**
   Converts a per-sample frame-advance bound `|y - x - 1| ≤ u` into
   `Solution.WithinSpeed` in any world satisfying `World.WithinBounds B`.
2. **Baseline topology classification (`fixedDelay_isStar`).**
   `Unisono.Solutions.FixedDelay.solution` is a star solution (`Solution.IsStar`).
3. **Two-sided Star-vs-Peer asymmetry separation directly on `Unisono.Spec`:**
   * `star_states_eq_of_star_links_eq`: any `IsStar` solution produces identical
     runs when non-star (receiver–receiver) links are modified.
   * `star_sync_lower_bound_with_symmetric_peers`: using host-local view
     invariance (`Solution.plays_shiftHosts`), every non-Zeno star solution
     that plays every frame from some frame on suffers
     `max (w⁺.sync) (w⁻.sync) ≥ ENNReal.ofReal (varFin (fun r => Δ (w.host r)))`
     on `(w⁺, w⁻) = (shiftStarKeepPeers w Δ, shiftStarKeepPeers w (-Δ))`.
   * `peer_probe_recovers_exact_offset`: NTP clock-reading identity for a
     symmetric peer exchange.
   * **Staggered asymmetric ideal separation worlds (`sepBaseWorld`,
     `sepWorldPlus`, `sepWorldMinus`):** belong to `IdealConstantWorld`
     (with asymmetric star links and symmetric peer link `1 ↔ 2` for `A ≠ 0`).
   * **Tight forwarding-only star witness (`ForwardStar.solution`):** attains
     `sync = ENNReal.ofReal (A ^ 2)` in both `sepWorldPlus A` and
     `sepWorldMinus A`.
   * **Peer witness (`PeerSync.solution`, `peer_beats_star_asymmetry_bound`):**
     on `(sepWorldPlus A, sepWorldMinus A)` with star-link delay `1/2`,
     symmetric peer-link delay `1/10`, and star shifts `±A` for any
     `A ∈ (0, 1/4)`, every qualifying star solution suffers
     `max sync ≥ ENNReal.ofReal (A²)`, whereas `PeerSync.solution` uses only
     star links plus the symmetric peer link `1 ↔ 2`, plays every frame
     `n ≥ 2`, and achieves `sync = 0` in both worlds.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open Unisono.Solutions
open scoped ENNReal

/-! ## 0. Shared helper for `Solution.WithinSpeed` -/

section WithinSpeedHelper

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- If every pair of consecutive output samples `(k, k + 1)` that both play the
source satisfies `|y - x - 1| ≤ u` (with `0 ≤ u < 1`), then in any bounded
world `w.WithinBounds B` the solution satisfies `Solution.WithinSpeed` with
bound `(2 * B.deviceRate + (1 + B.deviceRate) * u) / (1 - B.deviceRate)`. -/
theorem withinSpeed_of_step_bound (σ : Solution H R Msg) (w : World H R) (B : Bounds H)
    (hw : w.WithinBounds B) (lookahead : ℕ+) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hstep : ∀ r k x y,
      σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y →
      |y - x - 1| ≤ u) :
    σ.WithinSpeed w lookahead
      ((2 * B.deviceRate + (1 + B.deviceRate) * u) / (1 - B.deviceRate)) := by
  obtain ⟨-, hsrc, hspk, -, -, -, -, -, -, -, -⟩ := hw
  set ε := B.deviceRate
  have hε0 : 0 ≤ ε := B.deviceRate_nonneg
  have hε1 : ε < 1 := B.deviceRate_lt_one
  have h1m : 0 < 1 - ε := by linarith
  have h1p : 0 < 1 + ε := by linarith
  have hrate : 0 < w.rate := w.rate_pos
  intro r k v hv
  unfold World.speed at hv
  cases hpk : σ.plays w lookahead r k with
  | none => simp [hpk] at hv
  | some x =>
    cases hpk1 : σ.plays w lookahead r (k + 1) with
    | none => simp [hpk, hpk1] at hv
    | some y =>
      simp only [hpk, hpk1] at hv
      split_ifs at hv with hcont
      · injection hv with hv
        subst hv
        have hstep_xy := abs_le.mp (hstep r k x y hpk hpk1)
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
            have hr : w.rate ≠ 0 := hrate.ne'
            field_simp
          rw [hsimp] at hfrac
          have hdiff : (1 + ε) * (1 + u) / (1 - ε) - 1 = (2 * ε + (1 + ε) * u) / (1 - ε) := by
            have hne : 1 - ε ≠ 0 := h1m.ne'
            field_simp; ring
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
            have hr : w.rate ≠ 0 := hrate.ne'
            field_simp
          rw [hsimp] at hfrac
          have hdiff : 1 - (1 - ε) * (1 - u) / (1 + ε) = (2 * ε + (1 - ε) * u) / (1 + ε) := by
            have hne : 1 + ε ≠ 0 := h1p.ne'
            field_simp; ring
          have hcmp : (2 * ε + (1 - ε) * u) / (1 + ε) ≤ (2 * ε + (1 + ε) * u) / (1 - ε) := by
            rw [div_le_div_iff₀ h1p h1m]
            nlinarith
          linarith
        exact abs_le.mpr ⟨hlo, hhi⟩

/-- Extracting the block request step from `σ.plays w lookahead r k = some x`. -/
theorem exists_asked_of_plays_some (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {r : Fin R} {k : ℕ} {x : ℝ} (hplay : σ.plays w lookahead r k = some x) :
    ∃ (b n : ℕ),
      k ∈ (w.speaker r).block b ∧
      (σ.states w lookahead n).askedNext r = b ∧
      earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due = some (.asked r b) ∧
      (σ (w.host r) ((σ.states w lookahead n).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
          .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩])).plays k = some x := by
  have hplay0 := hplay
  unfold Solution.plays at hplay
  split_ifs at hplay with hex
  set m := Nat.find hex
  have hm_gt : k < (w.speaker r).first ((σ.states w lookahead m).askedNext r) := Nat.find_spec hex
  have hex_b : ∃ b, k < (w.speaker r).first (b + 1) := by
    refine ⟨k, ?_⟩
    have := (w.speaker r).first_strictMono.id_le (k + 1)
    simp only [id_eq] at this
    omega
  let b := Nat.find hex_b
  have hb_hi : k < (w.speaker r).first (b + 1) := Nat.find_spec hex_b
  have hb_lo : (w.speaker r).first b ≤ k := by
    cases hb0 : b with
    | zero => rw [(w.speaker r).first_zero]; exact Nat.zero_le k
    | succ b' =>
      have := Nat.find_min hex_b (show b' < b by omega)
      omega
  have hk_mem : k ∈ (w.speaker r).block b := by
    unfold PlaybackDevice.block
    rw [List.mem_range'_1]
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self b)
    omega
  have hb_lt : b < (σ.states w lookahead m).askedNext r := by
    by_contra hle
    push Not at hle
    have := (w.speaker r).first_strictMono.monotone hle
    omega
  obtain ⟨n, -, hnb, hnearly⟩ := σ.exists_asked_step w lookahead hb_lt
  have hp := σ.plays_of_asked_step_of_lt w lookahead hnb hnearly hk_mem
    (σ.asked_lt_out_of_plays w lookahead hk_mem hplay0)
  rw [hplay0] at hp
  unfold playable at hp
  cases hopt : (σ (w.host r) ((σ.states w lookahead n).views (w.host r)
      ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
        .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩])).plays k with
  | none => simp [hopt] at hp
  | some y =>
    simp only [hopt] at hp
    split_ifs at hp
    injection hp with hxy
    exact ⟨b, n, hk_mem, hnb, hnearly, by rw [hopt, hxy]⟩

end WithinSpeedHelper

/-! ## 1. Baseline topology classification -/

/-- The fixed-delay baseline (`Unisono.Solutions.FixedDelay.solution`) is a
star solution: every message it sends either originates at `p.sender` or is
addressed to `p.sender`. -/
theorem fixedDelay_isStar {H : Type} {R : ℕ} [DecidableEq H]
    (p : Unisono.Solutions.FixedDelay.Params H) :
    (Unisono.Solutions.FixedDelay.solution p : Solution H R _).IsStar p.sender := by
  intro h view dst msg frames hmem
  unfold Unisono.Solutions.FixedDelay.solution at hmem
  cases hlast : view.getLast? with
  | none => simp [hlast] at hmem
  | some e =>
    simp only [hlast] at hmem
    unfold Unisono.Solutions.FixedDelay.act at hmem
    cases hobs : e.observation with
    | handed frames' stamp =>
      simp only [hobs] at hmem
      split_ifs at hmem with hs
      · exact Or.inl hs
      · simp at hmem
    | received i payload _ =>
      cases payload with
      | block _ _ => simp [hobs] at hmem
      | ask sent =>
        simp only [hobs] at hmem
        split_ifs at hmem with hs
        · exact Or.inl hs.1
        · simp at hmem
      | answer _ _ => simp [hobs] at hmem
    | asked r outputs stamp =>
      simp only [hobs] at hmem
      split_ifs at hmem with ha
      · rw [List.mem_replicate] at hmem
        exact Or.inr (congrArg Prod.fst hmem.2)
      · simp at hmem
    | timer => simp [hobs] at hmem


/-! ## 4. Two-sided Star-vs-Peer asymmetry separation in `Unisono.Spec` -/

section StarVsPeerSeparation

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H]

/-- **Star solutions cannot observe non-star links.** If two worlds `w₁, w₂`
are identical except possibly on network delivery over non-star edges
(`i ≠ sender ∧ j ≠ sender`), then every star solution (`σ.IsStar w₁.sender`)
has the exact same run states and playback decisions in `w₁` and `w₂`. -/
theorem star_states_eq_of_star_links_eq (σ : Solution H R Msg) (w₁ w₂ : World H R)
    (lookahead : ℕ+) (hstar : σ.IsStar w₁.sender)
    (hsender : w₂.sender = w₁.sender)
    (hhost : w₂.host = w₁.host) (hclock : w₂.clock = w₁.clock)
    (hsrc : w₂.source = w₁.source) (hspk : w₂.speaker = w₁.speaker)
    (htgt : w₂.target = w₁.target)
    (hnet : ∀ i j t q, (i = w₁.sender ∨ j = w₁.sender) →
      w₂.network.deliver i j t q = w₁.network.deliver i j t q) :
    (∀ n, σ.states w₂ lookahead n = σ.states w₁ lookahead n)
      ∧ σ.plays w₂ lookahead = σ.plays w₁ lookahead := by
  have hsendAll : ∀ (st : State H R Msg) (h : H) (t : Time) (held : Finset ℕ)
      (sends : List (H × Msg × Finset ℕ)),
      (∀ s ∈ sends, h = w₁.sender ∨ s.1 = w₁.sender) →
      st.sendAll w₂ h t held sends = st.sendAll w₁ h t held sends := by
    intro st h t held sends
    induction sends generalizing st with
    | nil => intro _; rfl
    | cons m rest ih =>
      intro hmem
      simp only [State.sendAll, List.foldl_cons]
      have hm1 : h = w₁.sender ∨ m.1 = w₁.sender := hmem m (List.mem_cons_self ..)
      have hsend : st.send w₂ h t m.1 m.2.1 (m.2.2.filter (· ∈ held))
          = st.send w₁ h t m.1 m.2.1 (m.2.2.filter (· ∈ held)) := by
        simp [State.send, hnet h m.1 t (st.sentCount h m.1) hm1]
      rw [hsend]
      exact ih _ (fun s hs => hmem s (List.mem_cons_of_mem _ hs))
  have hhandle : ∀ (st : State H R Msg) (h : H) (t : Time) (obs : Observation H R Msg),
      st.handle σ w₂ lookahead h t obs = st.handle σ w₁ lookahead h t obs := by
    intro st h t obs
    dsimp only [State.handle]
    rw [hclock, hspk]
    have hsat : ∀ s ∈ (σ h (st.views h ++ [⟨(w₁.clock h).read t, obs⟩])).sends,
        h = w₁.sender ∨ s.1 = w₁.sender :=
      fun s hs => hstar h _ s.1 s.2.1 s.2.2 hs
    rw [hsendAll _ h t _ _ hsat]
  have hidx : w₂.hostIndex = w₁.hostIndex := by
    funext h
    unfold World.hostIndex
    rw [hsender, hhost]
  have hkey : ∀ (st : State H R Msg), st.key w₂ = st.key w₁ := by
    intro st; funext d
    cases d <;> simp [State.key, hsrc, hspk, hidx]
  have hstates : ∀ n, σ.states w₂ lookahead n = σ.states w₁ lookahead n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Solution.states, ih, State.step, hkey, hsender, hhost, hsrc, hspk, htgt]
      cases earliest ((σ.states w₁ lookahead n).key w₁) (σ.states w₁ lookahead n).due with
      | none => rfl
      | some d =>
        cases d with
        | handed b => dsimp only; rw [hhandle]
        | asked r b => dsimp only; rw [hhandle]
        | arrival p =>
          dsimp only
          cases (σ.states w₁ lookahead n).inFlight[p]? with
          | none => rfl
          | some m => dsimp only; rw [hhandle]
        | timer p =>
          dsimp only
          cases (σ.states w₁ lookahead n).timers[p]? with
          | none => rfl
          | some u => dsimp only; rw [hhandle]
  refine ⟨hstates, ?_⟩
  funext r k
  classical
  unfold Solution.plays
  simp only [hspk, hstates]

/-- Auxiliary world identical to `w` on star links (`i = w.sender ∨ j = w.sender`)
and dropping all non-star (peer-to-peer) messages. -/
def dropPeerLinks (w : World H R) : World H R where
  rate := w.rate
  rate_pos := w.rate_pos
  sender := w.sender
  host := w.host
  hosts := w.hosts
  clock := w.clock
  source := w.source
  speaker := w.speaker
  network :=
    { deliver := fun i j t q =>
        if i = w.sender ∨ j = w.sender then w.network.deliver i j t q else none
      after := fun i j t q a h => by
        split_ifs at h
        · exact w.network.after i j t q a h }
  target := w.target

/-- Shift non-sender host timelines by `Δ` on star links
(`i = w.sender ∨ j = w.sender`) while keeping all direct receiver-to-receiver
links identical to `w`. Crucially, the causality condition `hstar` is required
**only on star links**, placing no minimum-delay constraint on peer links. -/
def shiftStarKeepPeers (w : World H R) (Δ : H → ℝ)
    (hstar : ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + Δ i < a + Δ j) : World H R where
  rate := w.rate
  rate_pos := w.rate_pos
  sender := w.sender
  host := w.host
  hosts := w.hosts
  clock := fun h =>
    { read := fun t => (w.clock h).read (t - Δ h)
      strictMono := fun _ _ hlt => (w.clock h).strictMono (by linarith)
      continuous := (w.clock h).continuous.comp (continuous_id.sub continuous_const) }
  source := w.source
  speaker := fun r =>
    { out := fun k => (w.speaker r).out k + Δ (w.host r)
      out_strictMono := fun _ _ hlt => by linarith [(w.speaker r).out_strictMono hlt]
      first := (w.speaker r).first
      first_zero := (w.speaker r).first_zero
      first_strictMono := (w.speaker r).first_strictMono
      asked := fun b => (w.speaker r).asked b + Δ (w.host r)
      asked_mono := fun _ _ hle => by linarith [(w.speaker r).asked_mono hle]
      reported := (w.speaker r).reported }
  network :=
    { deliver := fun i j t q =>
        if i = w.sender ∨ j = w.sender then
          (w.network.deliver i j (t - Δ i) q).map (· + Δ j)
        else
          w.network.deliver i j t q
      after := fun i j t q a h => by
        split_ifs at h with hs
        · rcases Option.map_eq_some_iff.mp h with ⟨a₀, hdel, rfl⟩
          have := hstar i j (t - Δ i) q a₀ hs hdel
          linarith
        · exact w.network.after i j t q a h }
  target := w.target

/-- **Star lower bound in worlds with arbitrary (including fast, symmetric)
peer links — no `horder` and no peer-link delay bound.**
On `(w⁺, w⁻) = (shiftStarKeepPeers w Δ, shiftStarKeepPeers w (-Δ))`, where
star links carry opposite one-way asymmetries `±Δ` (`Δ w.sender = 0`) and
direct peer links remain unmodified (of arbitrarily small delay), every
non-Zeno star solution `σ` that plays all frames from `N` onward must suffer
`max (w⁺.sync) (w⁻.sync) ≥ ENNReal.ofReal (varFin (fun r => Δ (w.host r)))`. -/
theorem star_sync_lower_bound_with_symmetric_peers (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (hstar : σ.IsStar w.sender)
    (Δ : H → ℝ) (hΔs : Δ w.sender = 0)
    (hstar₁ : ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hstar₂ : ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (hprog : ∀ T : Time, ∃ n, T < σ.eventTime w lookahead n)
    (hprog₁ : ∀ T : Time, ∃ n, T < σ.eventTime (shiftStarKeepPeers w Δ hstar₁) lookahead n)
    (hprog₂ : ∀ T : Time, ∃ n, T < σ.eventTime (shiftStarKeepPeers w (-Δ) hstar₂) lookahead n)
    (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime (σ.plays w lookahead) r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    let wPlus := shiftStarKeepPeers w Δ hstar₁
    let wMinus := shiftStarKeepPeers w (-Δ) hstar₂
    ENNReal.ofReal (varFin fun r => Δ (w.host r))
      ≤ max (wPlus.sync (σ.plays wPlus lookahead)) (wMinus.sync (σ.plays wMinus lookahead)) := by
  intro wPlus wMinus
  set wAux := dropPeerLinks w
  have hnet₁ : ∀ i j s q a, wAux.network.deliver i j s q = some a → s + Δ i < a + Δ j := by
    intro i j s q a h
    dsimp only [wAux, dropPeerLinks] at h
    split_ifs at h with hs
    · exact hstar₁ i j s q a hs h
  have hnet₂ : ∀ i j s q a, wAux.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j) := by
    intro i j s q a h
    dsimp only [wAux, dropPeerLinks] at h
    split_ifs at h with hs
    · exact hstar₂ i j s q a hs h
  have heqW := star_states_eq_of_star_links_eq σ w wAux lookahead hstar
    rfl rfl rfl rfl rfl rfl (fun i j t q hs => by simp [wAux, dropPeerLinks, hs])
  have heqPlus := star_states_eq_of_star_links_eq σ (wAux.shiftHosts Δ hnet₁) wPlus lookahead hstar
    rfl rfl rfl rfl rfl rfl (fun i j t q hs => by
      change i = w.sender ∨ j = w.sender at hs
      simp [wPlus, shiftStarKeepPeers, wAux, dropPeerLinks, World.shiftHosts, hs])
  have heqMinus := star_states_eq_of_star_links_eq σ (wAux.shiftHosts (-Δ) hnet₂) wMinus lookahead hstar
    rfl rfl rfl rfl rfl rfl (fun i j t q hs => by
      change i = w.sender ∨ j = w.sender at hs
      simp [wMinus, shiftStarKeepPeers, wAux, dropPeerLinks, World.shiftHosts, hs])
  have hevEq : ∀ (w₁ w₂ : World H R),
      w₂.source = w₁.source → w₂.speaker = w₁.speaker → w₂.hostIndex = w₁.hostIndex →
      (∀ n, σ.states w₂ lookahead n = σ.states w₁ lookahead n) →
      ∀ n, σ.eventTime w₂ lookahead n = σ.eventTime w₁ lookahead n := by
    intro w₁ w₂ hsrc hspk hidx hst n
    unfold Solution.eventTime
    have hkey : (σ.states w₂ lookahead n).key w₂ = (σ.states w₁ lookahead n).key w₁ := by
      funext d; rw [hst n]; cases d <;> simp [State.key, hsrc, hspk, hidx]
    rw [hkey, hst n]
  have hprogAux : ∀ T, ∃ n, T < σ.eventTime wAux lookahead n := fun T => by
    obtain ⟨n, hn⟩ := hprog T
    exact ⟨n, by rw [hevEq w wAux rfl rfl rfl heqW.1 n]; exact hn⟩
  have hprogAux₁ : ∀ T, ∃ n, T < σ.eventTime (wAux.shiftHosts Δ hnet₁) lookahead n := fun T => by
    obtain ⟨n, hn⟩ := hprog₁ T
    exact ⟨n, by rw [← hevEq (wAux.shiftHosts Δ hnet₁) wPlus rfl rfl rfl heqPlus.1 n]; exact hn⟩
  have hprogAux₂ : ∀ T, ∃ n, T < σ.eventTime (wAux.shiftHosts (-Δ) hnet₂) lookahead n := fun T => by
    obtain ⟨n, hn⟩ := hprog₂ T
    exact ⟨n, by rw [← hevEq (wAux.shiftHosts (-Δ) hnet₂) wMinus rfl rfl rfl heqMinus.1 n]; exact hn⟩
  have hplayAux : ∀ n, N ≤ n → ∀ r, (wAux.playTime (σ.plays wAux lookahead) r n).isSome := by
    intro n hn r
    rw [heqW.2]; exact hplay n hn r
  have hsyncPlus : wPlus.sync (σ.plays wPlus lookahead)
      = (wAux.shiftHosts Δ hnet₁).sync (σ.plays (wAux.shiftHosts Δ hnet₁) lookahead) := by
    rw [heqPlus.2]; rfl
  have hsyncMinus : wMinus.sync (σ.plays wMinus lookahead)
      = (wAux.shiftHosts (-Δ) hnet₂).sync (σ.plays (wAux.shiftHosts (-Δ) hnet₂) lookahead) := by
    rw [heqMinus.2]; rfl
  rw [hsyncPlus, hsyncMinus]
  exact σ.sync_shiftHosts_lower_bound wAux lookahead Δ hΔs hnet₁ hnet₂
    hprogAux hprogAux₁ hprogAux₂ hR N hplayAux hunb

/-- **NTP clock-reading identity on a symmetric peer link.**
In `w' = shiftStarKeepPeers w Δ hstar` where the base world `w` has unit-rate
clocks `(w.clock h).read t = t + c_h` and a symmetric direct peer link of
constant delay `d > 0` between two non-sender hosts `h₁, h₂`, evaluating the
NTP estimator `t₂ - (t₁ + t₄) / 2` on a query-reply exchange `(h₁ → h₂ → h₁)`
yields `(c₂ - Δ h₂) - (c₁ - Δ h₁)`. -/
theorem peer_probe_recovers_exact_offset (w : World H R) (Δ : H → ℝ)
    (hstar : ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    {h₁ h₂ : H} (h1s : h₁ ≠ w.sender) (h2s : h₂ ≠ w.sender)
    {c₁ c₂ d s : ℝ} {q₁ q₂ : ℕ}
    (hc₁ : ∀ t, (w.clock h₁).read t = t + c₁)
    (hc₂ : ∀ t, (w.clock h₂).read t = t + c₂)
    (hd12 : w.network.deliver h₁ h₂ s q₁ = some (s + d))
    (hd21 : w.network.deliver h₂ h₁ (s + d) q₂ = some (s + 2 * d)) :
    let w' := shiftStarKeepPeers w Δ hstar
    w'.network.deliver h₁ h₂ s q₁ = some (s + d)
      ∧ w'.network.deliver h₂ h₁ (s + d) q₂ = some (s + 2 * d)
      ∧ (w'.clock h₂).read (s + d) - ((w'.clock h₁).read s + (w'.clock h₁).read (s + 2 * d)) / 2
          = (c₂ - Δ h₂) - (c₁ - Δ h₁) := by
  intro w'
  have h12 : ¬(h₁ = w.sender ∨ h₂ = w.sender) := by tauto
  have h21 : ¬(h₂ = w.sender ∨ h₁ = w.sender) := by tauto
  refine ⟨?_, ?_, ?_⟩
  · simp [w', shiftStarKeepPeers, h12, hd12]
  · simp [w', shiftStarKeepPeers, h21, hd21]
  · simp only [w', shiftStarKeepPeers, hc₁, hc₂]
    ring

/-! ## 5. Separation Worlds, Protocol Qualification, Tight Star Witness, and Peer Witness -/

/-- Staggered request/output phase offset on `sepBaseWorld`: speaker `0` acts at
integer offsets (`0`), speaker `1` at `+ 1/3`. -/
def sepSpeakerOffset (r : Fin 2) : ℝ := if r = 0 then 0 else 1 / 3

/-- Base 3-host world (`Fin 3`: sender `0`, speaker `0` on host `1`, speaker
`1` on host `2`) with unit frame rate, star-link delay `1/2`, symmetric direct
peer-link delay `1/10`, and staggered speaker request times (`b + 1` vs.
`b + 1 + 1/3`). -/
def sepBaseWorld : World (Fin 3) 2 where
  rate := 1
  rate_pos := by norm_num
  sender := 0
  host := ![1, 2]
  hosts := fun h => by
    fin_cases h
    · exact Or.inl rfl
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
  clock := fun _ =>
    { read := id
      strictMono := strictMono_id
      continuous := continuous_id }
  source :=
    { capture := fun n => (n : ℝ)
      capture_strictMono := Nat.strictMono_cast
      first := id
      first_zero := rfl
      first_strictMono := strictMono_id
      handed := fun b => (b : ℝ)
      handed_mono := Nat.mono_cast
      handed_after := fun b => by simp
      reported := fun b => (b : ℝ) }
  speaker := fun r =>
    { out := fun k => (k : ℝ) + 2 + sepSpeakerOffset r
      out_strictMono := fun _ _ hlt => by
        have : (_ : ℝ) < _ := Nat.cast_lt.mpr hlt; linarith
      first := id
      first_zero := rfl
      first_strictMono := strictMono_id
      asked := fun b => (b : ℝ) + 1 + sepSpeakerOffset r
      asked_mono := StrictMono.monotone fun _ _ hlt => by
        have : (_ : ℝ) < _ := Nat.cast_lt.mpr hlt; linarith
      reported := fun b => (b : ℝ) + 2 + sepSpeakerOffset r }
  network :=
    { deliver := fun i j s _ =>
        if i = 0 ∨ j = 0 then some (s + 1 / 2) else some (s + 1 / 10)
      after := fun i j s _ a h => by
        split_ifs at h <;> (injection h with h; linarith) }
  target := fun _ => 2

/- Minimal forwarding-only star witness on `sepBaseWorld` / `sepWorldPlus` /
`sepWorldMinus`: sender `0` forwards each frame `f` to hosts `1` and `2`,
speaker `0` plays `k - 2`, and speaker `1` plays `k - 2 + 1/3` (matching its
`+1/3` request offset in `sepBaseWorld`). In `sepWorldPlus A` and
`sepWorldMinus A`, it satisfies every hypothesis of the star lower bound and
attains `sync = ENNReal.ofReal (A ^ 2)` exactly, proving the bound is tight. -/
namespace ForwardStar

def solution : Solution (Fin 3) 2 ℕ := fun h view =>
  match view.getLast? with
  | none => ⟨[], [], fun _ => none⟩
  | some e =>
      match h, e.observation with
      | 0, .handed frames _ =>
          match frames.head? with
          | some (f, _) =>
              { sends := [(1, f, {f}), (2, f, {f})]
                timers := []
                plays := fun _ => none }
          | none => ⟨[], [], fun _ => none⟩
      | 1, .asked 0 _ _ =>
          { sends := []
            timers := []
            plays := fun k => if 3 ≤ k then some ((k : ℝ) - 2) else none }
      | 2, .asked 1 _ _ =>
          { sends := []
            timers := []
            plays := fun k => if 3 ≤ k then some ((k : ℝ) - 2 + 1 / 3) else none }
      | _, _ => ⟨[], [], fun _ => none⟩

theorem isStar : solution.IsStar 0 := by
  intro h view dst msg frames hmem
  unfold solution at hmem
  cases hlast : view.getLast? with
  | none => simp [hlast] at hmem
  | some e =>
    simp only [hlast] at hmem
    match h with
    | 0 => left; rfl
    | 1 =>
      cases hobs : e.observation with
      | asked r _ _ =>
        simp only [hobs] at hmem; match r with | 0 => simp at hmem | 1 => simp at hmem
      | _ => simp [hobs] at hmem
    | 2 =>
      cases hobs : e.observation with
      | asked r _ _ =>
        simp only [hobs] at hmem; match r with | 0 => simp at hmem | 1 => simp at hmem
      | _ => simp [hobs] at hmem

theorem progress (Δ : Fin 3 → ℝ)
    (hstar : ∀ i j s q a, (i = sepBaseWorld.sender ∨ j = sepBaseWorld.sender) →
      sepBaseWorld.network.deliver i j s q = some a → s + Δ i < a + Δ j) (T : Time) :
    ∃ n, T < solution.eventTime (shiftStarKeepPeers sepBaseWorld Δ hstar) 1 n := by
  set w' := shiftStarKeepPeers sepBaseWorld Δ hstar
  refine Solution.progress w' solution 1 (fun _ => 1) 3 3 ?_ ?_ ?_ ?_ ?_ ?_ T
  · intro h view
    unfold solution
    cases view.getLast? with
    | none => rfl
    | some e =>
      rcases e with ⟨_, obs⟩
      dsimp only
      match h with
      | 0 => cases obs with | handed fs _ => cases hhd : fs.head? <;> simp [hhd] | _ => rfl
      | 1 =>
        cases obs with
        | asked r _ _ => match r with | 0 => rfl | 1 => rfl
        | _ => rfl
      | 2 =>
        cases obs with
        | asked r _ _ => match r with | 0 => rfl | 1 => rfl
        | _ => rfl
  · intro h view frames rep reading
    match h with
    | 0 => cases hhd : frames.head? <;> simp [solution, hhd]
    | 1 => simp [solution]
    | 2 => simp [solution]
  · intro h view r outs rep reading
    match h, r with
    | 0, _ => simp [solution]
    | 1, 0 => simp [solution]
    | 1, 1 => simp [solution]
    | 2, 0 => simp [solution]
    | 2, 1 => simp [solution]
  · intro h view i c F reading
    match h with | 0 => simp [solution] | 1 => simp [solution] | 2 => simp [solution]
  · intro T'; obtain ⟨n, hn⟩ := exists_nat_gt T'; exact ⟨n, hn⟩
  · intro r T'
    obtain ⟨n, hn⟩ := exists_nat_gt (T' - 1 - sepSpeakerOffset r - Δ (sepBaseWorld.host r))
    exact ⟨n, by change T' < (n : ℝ) + 1 + sepSpeakerOffset r + Δ (sepBaseWorld.host r); linarith⟩

/-- In `w' = shiftStarKeepPeers sepBaseWorld Δ hstar` (`Δ 0 = 0`, `|Δ 1| < 1/4`,
`|Δ 2| < 1/4`), `ForwardStar.solution` plays every frame `n ≥ 2` at `n + 4 + Δ 1`
on speaker `0` and `n + 4 + Δ 2` on speaker `1`, achieving
`w'.sync = ENNReal.ofReal ((Δ 1 - Δ 2) ^ 2 / 4)` exactly. -/
theorem sync_eq (Δ : Fin 3 → ℝ) (hΔ0 : Δ 0 = 0)
    (hΔ1 : |Δ 1| < 1 / 4) (hΔ2 : |Δ 2| < 1 / 4)
    (hstar : ∀ i j s q a, (i = sepBaseWorld.sender ∨ j = sepBaseWorld.sender) →
      sepBaseWorld.network.deliver i j s q = some a → s + Δ i < a + Δ j) :
    let w' := shiftStarKeepPeers sepBaseWorld Δ hstar
    (∀ n, 2 ≤ n → (w'.playTime (solution.plays w' 1) 0 n).isSome ∧
        (w'.playTime (solution.plays w' 1) 1 n).isSome)
      ∧ w'.sync (solution.plays w' 1) = ENNReal.ofReal ((Δ 1 - Δ 2) ^ 2 / 4) := by
  intro w'
  have h1b := abs_lt.mp hΔ1
  have h2b := abs_lt.mp hΔ2
  have hprog := progress Δ hstar
  have hframe_held : ∀ (r : Fin 2) (k : ℕ) (n : ℕ),
      (solution.states w' 1 n).askedNext r = k →
      earliest ((solution.states w' 1 n).key w') (solution.states w' 1 n).due = some (.asked r k) →
      ∀ f : ℕ, f ≤ k → f ∈ (solution.states w' 1 n).held (w'.host r) := by
    intro r k n hnk hne f hfk
    have hn_time : solution.eventTime w' 1 n = (k : ℝ) + 1 + sepSpeakerOffset r + Δ (w'.host r) := by
      unfold Solution.eventTime; rw [hne]; rfl
    have hlt_hand : f < (solution.states w' 1 n).handedNext := by
      apply solution.lt_handedNext w' 1
      have hfk' : (f : ℝ) ≤ (k : ℝ) := by exact_mod_cast hfk
      have hΔr : -(1 / 4 : ℝ) < Δ (w'.host r) := by
        fin_cases r
        · change -(1 / 4 : ℝ) < Δ 1; linarith
        · change -(1 / 4 : ℝ) < Δ 2; linarith
      have hoff_nn : 0 ≤ sepSpeakerOffset r := by fin_cases r <;> simp [sepSpeakerOffset]
      change (f : ℝ) < solution.eventTime w' 1 n
      rw [hn_time]; linarith
    obtain ⟨nh, hnh_lt, hnh_f, hnh_early⟩ := solution.exists_handed_step w' 1 hlt_hand
    have hmem_if : ∃ m ∈ (solution.states w' 1 (nh + 1)).inFlight,
        m.destination = w'.host r ∧ m.arrival = (f : ℝ) + 1 / 2 + Δ (w'.host r) ∧ f ∈ m.frames := by
      have hblk : w'.source.block f = [f] := by
        simp [w', shiftStarKeepPeers, sepBaseWorld, CaptureDevice.block]
      set obsH : Observation (Fin 3) 2 ℕ :=
        .handed ((w'.source.block f).map fun n => (n, w'.target n)) (w'.source.reported f)
      have hhand_h : solution.handled w' 1 nh = some (0, w'.source.handed f, obsH) := by
        unfold Solution.handled; rw [hnh_early]; simp [w', shiftStarKeepPeers, sepBaseWorld, obsH]
      have hS_h : (solution 0 ((solution.states w' 1 nh).views 0 ++
          [⟨(w'.clock 0).read (w'.source.handed f), obsH⟩])).sends
          = [(1, f, {f}), (2, f, {f})] := by simp [solution, obsH, hblk]
      have hf_held0 : f ∈ (solution.states w' 1 nh).held 0 ∪ obsH.frames := by
        simp [obsH, Observation.frames, hblk]
      match r with
      | 0 =>
        have hsent := solution.sent_inFlight (w := w') 1 hhand_h hS_h (i := 0) (by simp)
          (arr := (f : ℝ) + 1 / 2 + Δ 1) (by simp [w', shiftStarKeepPeers, sepBaseWorld, hΔ0])
        exact ⟨_, hsent, by rfl, by rfl, by simpa [Finset.mem_filter] using hf_held0⟩
      | 1 =>
        have hsent := solution.sent_inFlight (w := w') 1 hhand_h hS_h (i := 1) (by simp)
          (arr := (f : ℝ) + 1 / 2 + Δ 2) (by simp [w', shiftStarKeepPeers, sepBaseWorld, hΔ0])
        exact ⟨_, hsent, by rfl, by rfl, by simpa [Finset.mem_filter] using hf_held0⟩
    obtain ⟨m, hm_if, hm_dst, hm_arr, hf_m⟩ := hmem_if
    have hoff_nn : 0 ≤ sepSpeakerOffset r := by fin_cases r <;> simp [sepSpeakerOffset]
    have hsub := solution.frames_arrive w' 1 hm_if (Nat.succ_le_of_lt hnh_lt) (by
      rw [hm_arr, hn_time]
      have hfk' : (f : ℝ) ≤ (k : ℝ) := by exact_mod_cast hfk
      linarith)
    rw [hm_dst] at hsub
    exact hsub hf_m
  have hplays : ∀ (r : Fin 2) (k : ℕ), 3 ≤ k →
      solution.plays w' 1 r k = some ((k : ℝ) - 2 + sepSpeakerOffset r) := by
    intro r k hk3
    obtain ⟨m, hm⟩ := hprog ((w'.speaker r).asked k)
    obtain ⟨n, -, hnk, hne⟩ := solution.exists_asked_step w' 1 (solution.lt_askedNext w' 1 hm)
    have hmem_k : k ∈ (w'.speaker r).block k := by
      simp [w', shiftStarKeepPeers, sepBaseWorld, PlaybackDevice.block]
    have hlt_k : (w'.speaker r).asked k < (w'.speaker r).out k := by
      show (k : ℝ) + 1 + sepSpeakerOffset r + Δ (sepBaseWorld.host r)
        < (k : ℝ) + 2 + sepSpeakerOffset r + Δ (sepBaseWorld.host r)
      linarith
    rw [solution.plays_of_asked_step_of_lt w' 1 hnk hne hmem_k hlt_k]
    have hact : (solution (w'.host r) ((solution.states w' 1 n).views (w'.host r) ++
        [⟨(w'.clock (w'.host r)).read ((w'.speaker r).asked k),
          .asked r ((w'.speaker r).block k) ((w'.speaker r).reported k)⟩])).plays k
        = some ((k : ℝ) - 2 + sepSpeakerOffset r) := by
      fin_cases r
      · change (solution 1 _).plays k = _; simp [solution, sepSpeakerOffset, hk3]
      · change (solution 2 _).plays k = _; simp [solution, sepSpeakerOffset, hk3]
    rw [hact]
    unfold playable; dsimp only; split_ifs with hcond
    · rfl
    · exfalso; apply hcond
      have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      have hoff_nn : 0 ≤ sepSpeakerOffset r := by fin_cases r <;> simp [sepSpeakerOffset]
      have hoff_lt1 : sepSpeakerOffset r < 1 := by fin_cases r <;> simp [sepSpeakerOffset]; norm_num
      refine ⟨by linarith, fun f hf => ?_⟩
      have hf1 : |(f : ℝ) - ((k : ℝ) - 2 + sepSpeakerOffset r)| < 1 := by simpa using hf
      have hf' := (abs_lt.mp hf1).2
      have hfk : f ≤ k := Nat.le_of_lt (Nat.cast_lt.mp (by linarith : (f : ℝ) < (k : ℝ)))
      exact hframe_held r k n hnk hne f hfk
  have hno_lt3 : ∀ (r : Fin 2) (k : ℕ), k < 3 → solution.plays w' 1 r k = none := by
    intro r k hk3
    by_contra hne
    cases hval : solution.plays w' 1 r k with
    | none => exact hne hval
    | some x =>
      obtain ⟨_, _, _, _, _, hp⟩ := exists_asked_of_plays_some solution w' 1 hval
      fin_cases r
      · change (solution 1 _).plays k = some x at hp; simp [solution, show ¬(3 ≤ k) by omega] at hp
      · change (solution 2 _).plays k = some x at hp; simp [solution, show ¬(3 ≤ k) by omega] at hp
  have hpt_eq : ∀ n, 2 ≤ n →
      w'.playTime (solution.plays w' 1) 0 n = some ((n : ℝ) + 4 + Δ 1) ∧
      w'.playTime (solution.plays w' 1) 1 n = some ((n : ℝ) + 4 + Δ 2) := by
    intro n hn2
    have hpt_r : ∀ (r : Fin 2),
        w'.playTime (solution.plays w' 1) r n = some ((n : ℝ) + 4 + Δ (w'.host r)) := by
      classical
      intro r
      have hex : ∃ k, Covers (solution.plays w' 1 r) k n := by
        fin_cases r
        · refine ⟨n + 2, (n : ℝ), (n : ℝ) + 1, ?_, ?_, by linarith, by linarith, le_rfl, by linarith⟩
          · change solution.plays w' 1 0 (n + 2) = some (n : ℝ)
            rw [hplays 0 (n + 2) (by omega)]; congr 1; simp [sepSpeakerOffset]
          · change solution.plays w' 1 0 (n + 3) = some ((n : ℝ) + 1)
            rw [hplays 0 (n + 3) (by omega)]; congr 1; simp [sepSpeakerOffset]; ring
        · refine ⟨n + 1, (n : ℝ) - 2 / 3, (n : ℝ) + 1 / 3, ?_, ?_, by linarith, by linarith, by linarith, by linarith⟩
          · change solution.plays w' 1 1 (n + 1) = some ((n : ℝ) - 2 / 3)
            rw [hplays 1 (n + 1) (by omega)]; congr 1; simp [sepSpeakerOffset]; ring
          · change solution.plays w' 1 1 (n + 2) = some ((n : ℝ) + 1 / 3)
            rw [hplays 1 (n + 2) (by omega)]; congr 1; simp [sepSpeakerOffset]
      unfold World.playTime Spec.playTime
      simp only [hex, ↓reduceDIte]
      set k₀ := Nat.find hex
      have hcov : Covers (solution.plays w' 1 r) k₀ n := Nat.find_spec hex
      have hk₀3 : 3 ≤ k₀ := by
        obtain ⟨x, _, hx, _⟩ := hcov
        by_contra hlt; rw [hno_lt3 r k₀ (by omega)] at hx; simp at hx
      rw [hplays r k₀ hk₀3, hplays r (k₀ + 1) (by omega)]
      dsimp only; congr 1
      change ((k₀ : ℝ) + 2 + sepSpeakerOffset r + Δ (w'.host r))
          + ((n : ℝ) - ((k₀ : ℝ) - 2 + sepSpeakerOffset r))
            / (((k₀ + 1 : ℕ) : ℝ) - 2 + sepSpeakerOffset r - ((k₀ : ℝ) - 2 + sepSpeakerOffset r))
            * (((k₀ + 1 : ℕ) : ℝ) + 2 + sepSpeakerOffset r + Δ (w'.host r)
              - ((k₀ : ℝ) + 2 + sepSpeakerOffset r + Δ (w'.host r)))
        = (n : ℝ) + 4 + Δ (w'.host r)
      push_cast; ring
    exact ⟨by simpa [w', shiftStarKeepPeers, sepBaseWorld] using hpt_r 0,
      by simpa [w', shiftStarKeepPeers, sepBaseWorld] using hpt_r 1⟩
  refine ⟨fun n hn => ⟨by rw [(hpt_eq n hn).1]; rfl, by rw [(hpt_eq n hn).2]; rfl⟩, ?_⟩
  set c : ENNReal := ENNReal.ofReal ((Δ 1 - Δ 2) ^ 2 / 4)
  have hsyncCost_eq : ∀ n, 2 ≤ n → w'.syncCost (solution.plays w' 1) n = c := by
    intro n hn
    unfold World.syncCost World.pairCost
    have hfilt : (Finset.univ.filter (fun p : Fin 2 × Fin 2 => p.1 < p.2)) = {(0, 1)} := by
      ext ⟨a, b⟩; fin_cases a <;> fin_cases b <;> decide
    rw [hfilt, Finset.sum_singleton, (hpt_eq n hn).1, (hpt_eq n hn).2]
    dsimp only [c]
    have h4 : (2 : ENNReal) ^ 2 = ENNReal.ofReal 4 := by
      rw [show (4 : ℝ) = ((2 : ℕ) : ℝ) ^ 2 by norm_num, ENNReal.ofReal_pow (by norm_num)]
      simp
    rw [show ((2 : ℕ) : ENNReal) ^ 2 = ENNReal.ofReal 4 by exact_mod_cast h4,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4⁻¹)]
    congr 1; ring
  have hcap_diff : ∀ n, w'.source.capture (n + 1) - w'.source.capture n = 1 := by
    intro n; change ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1; push_cast; ring
  have hfin : ∑ n ∈ Finset.range 2,
      w'.syncCost (solution.plays w' 1) n
        * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n) ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun n _ => ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
    unfold World.syncCost World.pairCost
    apply ENNReal.mul_ne_top (by simp)
    refine ENNReal.sum_ne_top.mpr fun p _ => ?_
    cases w'.playTime (solution.plays w' 1) p.1 n <;>
      cases w'.playTime (solution.plays w' 1) p.2 n <;> simp
  apply le_antisymm
  · refine longRun_le hfin 1 fun T hT => ?_
    have hsplit : w'.accruedFrames (w'.syncCost (solution.plays w' 1)) T
        ≤ (∑ n ∈ Finset.range 2, w'.syncCost (solution.plays w' 1) n
            * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n))
          + c * ENNReal.ofReal T := by
      unfold World.accruedFrames
      set m : ℕ := Nat.ceil T + 3
      have htsum : ∑' n, (if w'.source.capture n < T then
            w'.syncCost (solution.plays w' 1) n
              * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n) else 0)
          = ∑ n ∈ Finset.range m, (if w'.source.capture n < T then
            w'.syncCost (solution.plays w' 1) n
              * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n) else 0) := by
        apply tsum_eq_sum
        intro n hn
        simp only [Finset.mem_range, not_lt] at hn
        have hge : T ≤ w'.source.capture n := by
          have hceil : T ≤ (Nat.ceil T : ℝ) := Nat.le_ceil T
          have hn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          change T ≤ (n : ℝ)
          dsimp only [m] at hn'; push_cast at hn'; linarith
        simp [not_lt.mpr hge]
      rw [htsum]
      have h2m : 2 ≤ m := by omega
      rw [← Finset.sum_range_add_sum_Ico _ h2m]
      refine add_le_add ?_ ?_
      · exact Finset.sum_le_sum fun n _ => by split_ifs <;> simp
      · have hsub : ∀ n ∈ Finset.Ico 2 m,
            (if w'.source.capture n < T then
              w'.syncCost (solution.plays w' 1) n
                * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n) else 0)
            = if n < Nat.ceil T then c else 0 := by
          intro n hn
          have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
          rw [hsyncCost_eq n hn2, hcap_diff n, ENNReal.ofReal_one, mul_one]
          have hiff : w'.source.capture n < T ↔ n < Nat.ceil T := by
            change (n : ℝ) < T ↔ n < Nat.ceil T
            exact (Nat.lt_ceil).symm
          simp [hiff]
        rw [Finset.sum_congr rfl hsub, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul, mul_comm]
        have hcard : ((Finset.Ico 2 m).filter (fun n => n < Nat.ceil T)).card ≤ Nat.ceil T - 2 := by
          calc ((Finset.Ico 2 m).filter (fun n => n < Nat.ceil T)).card
              ≤ (Finset.Ico 2 (Nat.ceil T)).card := by
                apply Finset.card_le_card
                intro n hn
                simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
                exact ⟨hn.1.1, hn.2⟩
            _ = Nat.ceil T - 2 := Nat.card_Ico _ _
        have hle_T : ((Nat.ceil T - 2 : ℕ) : ℝ) ≤ T := by
          by_cases h2 : 2 ≤ Nat.ceil T
          · rw [Nat.cast_sub h2]; push_cast
            have hlt : (Nat.ceil T : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
            linarith
          · have h0 : Nat.ceil T - 2 = 0 := by omega
            rw [h0]; norm_num; linarith
        calc c * (((Finset.Ico 2 m).filter (fun n => n < Nat.ceil T)).card : ENNReal)
            ≤ c * ((Nat.ceil T - 2 : ℕ) : ENNReal) := by gcongr
          _ = c * ENNReal.ofReal ((Nat.ceil T - 2 : ℕ) : ℝ) := by rw [ENNReal.ofReal_natCast]
          _ ≤ c * ENNReal.ofReal T := by gcongr
    simpa [add_comm] using hsplit
  · -- Lower bound `c ≤ w'.sync`: follows from `accruedFrames ≥ c * (T - 4)` for `T ≥ 4`.
    have hlow : ∀ T : ℝ, 4 ≤ T →
        c * ENNReal.ofReal (T - 4) ≤ w'.accruedFrames (w'.syncCost (solution.plays w' 1)) T := by
      intro T hT4
      have hT0 : 0 ≤ T := by linarith
      set K : ℕ := Nat.floor T
      have hK4 : 4 ≤ K := Nat.le_floor (by norm_num; linarith)
      unfold World.accruedFrames
      have hle_sum : ∑ n ∈ Finset.Ico 2 (K - 1),
          (if w'.source.capture n < T then
            w'.syncCost (solution.plays w' 1) n
              * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n) else 0)
          ≤ ∑' n, (if w'.source.capture n < T then
            w'.syncCost (solution.plays w' 1) n
              * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n) else 0) :=
        sum_le_tsum _
      have hterm : ∀ n ∈ Finset.Ico 2 (K - 1),
          (if w'.source.capture n < T then
            w'.syncCost (solution.plays w' 1) n
              * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n) else 0) = c := by
        intro n hn
        obtain ⟨hn2, hnK⟩ := Finset.mem_Ico.mp hn
        have hltT : w'.source.capture n < T := by
          change (n : ℝ) < T
          have h1 : (n : ℕ) < K := by omega
          exact lt_of_lt_of_le (by exact_mod_cast h1) (Nat.floor_le hT0)
        simp only [hltT, ↓reduceIte, hsyncCost_eq n hn2, hcap_diff n, ENNReal.ofReal_one, mul_one]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_comm] at hle_sum
      calc c * ENNReal.ofReal (T - 4)
          ≤ c * (((K - 1) - 2 : ℕ) : ENNReal) := by
            rw [← ENNReal.ofReal_natCast]
            gcongr
            have hTlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
            have hsubK : (((K - 1) - 2 : ℕ) : ℝ) = (K : ℝ) - 3 := by
              rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
            rw [hsubK]; linarith
        _ ≤ _ := hle_sum
    unfold World.sync longRun
    refine le_sInf fun b hb => ?_
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hb
    by_contra hlt
    push Not at hlt
    have hc_fin : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have hb_fin : b ≠ ⊤ := ne_top_of_lt hlt
    set δ : ℝ := c.toReal - b.toReal
    have hδ : 0 < δ := by
      have : b.toReal < c.toReal := ENNReal.toReal_strict_mono hc_fin hlt
      linarith
    set T : ℝ := max (max T₀ 4) (4 * c.toReal / δ + 1)
    have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
    have hT4 : 4 ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
    have hTpos : 0 < T := by linarith
    have hTbig : 4 * c.toReal / δ < T := by
      have : 4 * c.toReal / δ + 1 ≤ T := le_max_right _ _
      linarith
    have hle1 := hlow T hT4
    have hle2 := hT₀ T hTT₀
    have hle3 : c * ENNReal.ofReal (T - 4) / ENNReal.ofReal T ≤ b :=
      le_trans (ENNReal.div_le_div_right hle1 _) hle2
    have htr := ENNReal.toReal_mono hb_fin hle3
    rw [ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ T - 4),
      ENNReal.toReal_ofReal hTpos.le] at htr
    have hmul : c.toReal * (T - 4) ≤ b.toReal * T := (div_le_iff₀ hTpos).mp htr
    have hcontra : 4 * c.toReal < T * δ := (div_lt_iff₀ hδ).mp hTbig
    dsimp only [δ] at hcontra
    linarith

end ForwardStar

/-- Opposite speaker host shifts `Δ = ![0, A, -A]` on `Fin 3`. -/
def sepShift (A : ℝ) : Fin 3 → ℝ := ![0, A, -A]

theorem sepShift_star_net {A : ℝ} (hA : |A| < 1 / 4) :
    ∀ i j s q a, (i = sepBaseWorld.sender ∨ j = sepBaseWorld.sender) →
      sepBaseWorld.network.deliver i j s q = some a → s + sepShift A i < a + sepShift A j := by
  intro i j s q a hs hdel
  have habs := abs_lt.mp hA
  change i = 0 ∨ j = 0 at hs
  simp only [sepBaseWorld, hs, ↓reduceIte, Option.some.injEq] at hdel
  fin_cases i <;> fin_cases j <;> simp [sepShift] at hs ⊢ <;> linarith

/-- Shifted world `w⁺(A)` with star-link asymmetry `+A` on host `1`, `-A` on
host `2`, and symmetric `1/10` direct peer link between hosts `1` and `2`. -/
def sepWorldPlus {A : ℝ} (hA : |A| < 1 / 4) : World (Fin 3) 2 :=
  shiftStarKeepPeers sepBaseWorld (sepShift A) (sepShift_star_net hA)

theorem sepShift_neg_star_net {A : ℝ} (hA : |A| < 1 / 4) :
    ∀ i j s q a, (i = sepBaseWorld.sender ∨ j = sepBaseWorld.sender) →
      sepBaseWorld.network.deliver i j s q = some a →
        s + (-(sepShift A)) i < a + (-(sepShift A)) j := by
  intro i j s q a hs hdel
  have hneg : |-A| < 1 / 4 := by rwa [abs_neg]
  have h := sepShift_star_net hneg i j s q a hs hdel
  have hEq : ∀ x, (-(sepShift A)) x = sepShift (-A) x := fun x => by
    fin_cases x <;> simp [sepShift]
  rw [hEq i, hEq j]
  exact h

/-- Shifted world `w⁻(A)` with opposite star-link asymmetry `-A` on host `1`,
`+A` on host `2`, and the same symmetric `1/10` direct peer link. -/
def sepWorldMinus {A : ℝ} (hA : |A| < 1 / 4) : World (Fin 3) 2 :=
  shiftStarKeepPeers sepBaseWorld (-(sepShift A)) (sepShift_neg_star_net hA)

/-- Any shifted separation world `shiftStarKeepPeers sepBaseWorld Δ hnet`
belongs to the named `IdealConstantWorld` model class. -/
theorem shiftStarKeepPeers_sepBaseWorld_ideal (Δ : Fin 3 → ℝ) (hΔ0 : Δ 0 = 0)
    (hnet : ∀ i j s q a, (i = sepBaseWorld.sender ∨ j = sepBaseWorld.sender) →
      sepBaseWorld.network.deliver i j s q = some a → s + Δ i < a + Δ j) :
    ∃ m : IdealConstantWorld (Fin 3) 2,
      m.Holds (shiftStarKeepPeers sepBaseWorld Δ hnet)
      ∧ ∀ i j, m.delay i j = if i = 0 ∨ j = 0 then 1 / 2 + Δ j - Δ i else 1 / 10 := by
  let d : Fin 3 → Fin 3 → ℝ := fun i j => if i = 0 ∨ j = 0 then 1 / 2 + Δ j - Δ i else 1 / 10
  have hd : ∀ i j, 0 < d i j := by
    intro i j
    dsimp only [d]
    split_ifs with hs
    · have h := hnet i j 0 0 (1 / 2) hs (by simp [sepBaseWorld, hs])
      linarith
    · norm_num
  refine ⟨
    { rate := 1
      rate_pos := one_pos
      sender := 0
      host := ![1, 2]
      delay := d
      delay_pos := hd
      blockSize := 1
      blockSize_pos := one_pos
      lead := 1
      lead_pos := one_pos
      targetLatency := 2
      targetLatency_nonneg := by norm_num },
    ?_, fun _ _ => rfl⟩
  refine
    { rate_eq := rfl
      sender_eq := rfl
      host_eq := rfl
      clocks := fun h => ⟨-Δ h, fun t => by simp [shiftStarKeepPeers, sepBaseWorld, sub_eq_add_neg]⟩
      capture := ⟨0, fun n => by simp [shiftStarKeepPeers, sepBaseWorld]⟩
      capture_first := fun b => by simp [shiftStarKeepPeers, sepBaseWorld]
      capture_handed := fun b => by simp [shiftStarKeepPeers, sepBaseWorld]
      capture_reported := fun b => by
        simp [shiftStarKeepPeers, sepBaseWorld, hΔ0]
      speaker_out := fun r => ⟨2 + sepSpeakerOffset r + Δ (sepBaseWorld.host r), fun k => by
        simp only [shiftStarKeepPeers, sepBaseWorld, div_one]
        ring⟩
      speaker_first := fun r b => by simp [shiftStarKeepPeers, sepBaseWorld]
      speaker_asked := fun r b => by simp [shiftStarKeepPeers, sepBaseWorld]; ring
      speaker_reported := fun r b => by
        simp only [shiftStarKeepPeers, sepBaseWorld, id_eq]
        have h : ((b : ℝ) + 2 + sepSpeakerOffset r) -
            ((b : ℝ) + 2 + sepSpeakerOffset r + Δ (![1, 2] r) - Δ (![1, 2] r)) = 0 := by ring
        rw [h, abs_zero]
      network := fun i j s q => by
        dsimp only [shiftStarKeepPeers, sepBaseWorld, d]
        split_ifs with hs
        · simp only [Option.map_some, Option.some.injEq]; ring
        · rfl
      target_eq := fun _ => rfl }

/-- For `0 < A < 1/4`, both `sepWorldPlus` and `sepWorldMinus` belong to the
asymmetric subclass of `IdealConstantWorld`. -/
theorem sepWorlds_ideal_asymmetric {A : ℝ} (hA0 : 0 < A) (hA4 : A < 1 / 4) :
    let hA : |A| < 1 / 4 := abs_lt.mpr ⟨by linarith, hA4⟩
    (∃ m : IdealConstantWorld (Fin 3) 2, m.Holds (sepWorldPlus hA) ∧ m.Asymmetric)
    ∧ (∃ m : IdealConstantWorld (Fin 3) 2, m.Holds (sepWorldMinus hA) ∧ m.Asymmetric) := by
  intro hA
  constructor
  · obtain ⟨m, hm, hd⟩ := shiftStarKeepPeers_sepBaseWorld_ideal (sepShift A) rfl (sepShift_star_net hA)
    refine ⟨m, hm, 0, 1, ?_⟩
    rw [hd 0 1, hd 1 0]
    simp only [true_or, or_true, ↓reduceIte, sepShift, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · obtain ⟨m, hm, hd⟩ :=
      shiftStarKeepPeers_sepBaseWorld_ideal (-(sepShift A)) (by simp [sepShift])
        (sepShift_neg_star_net hA)
    refine ⟨m, hm, 0, 1, ?_⟩
    rw [hd 0 1, hd 1 0]
    simp only [true_or, or_true, ↓reduceIte, Pi.neg_apply, sepShift, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linarith

/- Idealized-world peer witness for the 3-host separation worlds
`(sepWorldPlus A, sepWorldMinus A)`. This is a witness tailored to these
rate-1, constant-delay, lossless worlds (not a general protocol):
* Sender `0` forwards each handed frame `f` to hosts `1` and `2`.
* Speaker `1` (host `2`) sends one NTP probe to speaker `0` (host `1`) on its
  first block request `b = 0`.
* Speaker `0` (host `1`) answers probes from host `2` and plays position
  `k - 2` at output sample `k ≥ 3`.
* Speaker `1` (host `2`) computes `θ = t₂ - (t₁ + t₄) / 2` from the peer reply
  and plays position `k - 2 + 1/3 + θ` at output sample `k ≥ 3` (compensating
  both its `+1/3` request offset in `sepBaseWorld` and the shift `Δ 2 - Δ 1`). -/
namespace PeerSync

inductive Payload where
  | frame (f : ℕ)
  | ask (sent : ℝ)
  | answer (sent received : ℝ)

/-- Extract the latest NTP offset `t₂ - (t₁ + t₄) / 2` from host `1`'s replies
in `view`. -/
def peerOffsetFromView : List (Event (Fin 3) 2 Payload) → Option ℝ
  | [] => none
  | e :: rest =>
      match peerOffsetFromView rest with
      | some θ => some θ
      | none =>
          match e.observation with
          | .received 1 (.answer sent received) _ => some (received - (sent + e.reading) / 2)
          | _ => none

/-- Idealized-world peer `Solution` witnessing zero synchronization error on
`(sepWorldPlus A, sepWorldMinus A)` for `|A| < 1/4`. -/
def solution : Solution (Fin 3) 2 Payload := fun h view =>
  match view.getLast? with
  | none => ⟨[], [], fun _ => none⟩
  | some e =>
      match h, e.observation with
      | 0, .handed frames _ =>
          match frames.head? with
          | some (f, _) =>
              { sends := [(1, .frame f, {f}), (2, .frame f, {f})]
                timers := []
                plays := fun _ => none }
          | none => ⟨[], [], fun _ => none⟩
      | 1, .received 2 (.ask sent) _ =>
          { sends := [(2, .answer sent e.reading, ∅)]
            timers := []
            plays := fun _ => none }
      | 1, .asked 0 _ _ =>
          { sends := []
            timers := []
            plays := fun k => if 3 ≤ k then some ((k : ℝ) - 2) else none }
      | 2, .asked 1 outs _ =>
          let sends : List (Fin 3 × Payload × Finset ℕ) :=
            if outs = [0] then [(1, .ask e.reading, ∅)] else []
          let plays : ℕ → Option ℝ := match peerOffsetFromView view.dropLast with
            | some θ => fun k => if 3 ≤ k then some ((k : ℝ) - 2 + 1 / 3 + θ) else none
            | none => fun _ => none
          { sends := sends
            timers := []
            plays := plays }
      | _, _ => ⟨[], [], fun _ => none⟩

/-- `PeerSync.solution` uses only star links and the direct peer link `1 ↔ 2`. -/
theorem usesGraph :
    solution.UsesGraph (fun i j => i = 0 ∨ j = 0 ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) := by
  intro h view dst msg frames hmem
  unfold solution at hmem
  cases hlast : view.getLast? with
  | none => simp [hlast] at hmem
  | some e =>
    simp only [hlast] at hmem
    fin_cases h
    · change (dst, msg, frames) ∈ _ at hmem
      cases hobs : e.observation with
      | handed fs _ =>
        simp only [hobs] at hmem
        cases hhd : fs.head? with
        | none => simp [hhd] at hmem
        | some p => left; rfl
      | _ => simp [hobs] at hmem
    · change (dst, msg, frames) ∈ _ at hmem
      cases hobs : e.observation with
      | received i c _ =>
        simp only [hobs] at hmem
        fin_cases i
        · simp at hmem
        · simp at hmem
        · cases c with
          | ask sent =>
            simp only [Fin.mk_one, Fin.reduceFinMk, List.mem_singleton, Prod.mk.injEq] at hmem
            obtain ⟨rfl, _, _⟩ := hmem
            right; right; left; exact ⟨rfl, rfl⟩
          | _ => simp at hmem
      | asked r _ _ =>
        simp only [hobs] at hmem
        fin_cases r <;> simp at hmem
      | _ => simp [hobs] at hmem
    · change (dst, msg, frames) ∈ _ at hmem
      cases hobs : e.observation with
      | asked r outs _ =>
        simp only [hobs] at hmem
        fin_cases r
        · simp at hmem
        · change (dst, msg, frames) ∈ (if outs = [0] then [(1, .ask e.reading, ∅)] else []) at hmem
          split_ifs at hmem
          · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
            obtain ⟨rfl, _, _⟩ := hmem
            right; right; right; exact ⟨rfl, rfl⟩
          · simp at hmem
      | _ => simp [hobs] at hmem

def msgWeight : Payload → ℕ
  | .frame _ => 1
  | .ask _ => 2
  | .answer _ _ => 1

/-- `PeerSync.solution` is non-Zeno on any shifted star world
`shiftStarKeepPeers sepBaseWorld Δ hstar`. -/
theorem progress (Δ : Fin 3 → ℝ)
    (hstar : ∀ i j s q a, (i = sepBaseWorld.sender ∨ j = sepBaseWorld.sender) →
      sepBaseWorld.network.deliver i j s q = some a → s + Δ i < a + Δ j) (T : Time) :
    ∃ n, T < solution.eventTime (shiftStarKeepPeers sepBaseWorld Δ hstar) 1 n := by
  set w' := shiftStarKeepPeers sepBaseWorld Δ hstar
  refine Solution.progress w' solution 1 msgWeight 3 3 ?_ ?_ ?_ ?_ ?_ ?_ T
  · intro h view
    unfold solution
    cases view.getLast? with
    | none => rfl
    | some e =>
      rcases e with ⟨rd, obs⟩
      dsimp only
      match h with
      | 0 =>
        cases obs with
        | handed fs _ => cases hhd : fs.head? <;> simp [hhd]
        | _ => rfl
      | 1 =>
        cases obs with
        | received i c _ =>
          match i with
          | 0 => rfl
          | 1 => rfl
          | 2 => cases c <;> rfl
        | asked r _ _ =>
          match r with
          | 0 => rfl
          | 1 => rfl
        | _ => rfl
      | 2 =>
        cases obs with
        | asked r _ _ =>
          match r with
          | 0 => rfl
          | 1 => rfl
        | _ => rfl
  · intro h view frames rep reading
    match h with
    | 0 =>
      cases hhd : frames.head? with
      | none => simp [solution, hhd]
      | some p => simp [solution, hhd, msgWeight]
    | 1 => simp [solution]
    | 2 => simp [solution]
  · intro h view r outs rep reading
    match h, r with
    | 2, 1 => by_cases houts : outs = [0] <;> simp [solution, houts, msgWeight]
    | 0, _ => simp [solution]
    | 1, 0 => simp [solution]
    | 1, 1 => simp [solution]
    | 2, 0 => simp [solution]
  · intro h view i c F reading
    match h, i with
    | 1, 2 => cases c <;> simp [solution, msgWeight]
    | 0, _ => cases c <;> simp [solution, msgWeight]
    | 1, 0 => cases c <;> simp [solution, msgWeight]
    | 1, 1 => cases c <;> simp [solution, msgWeight]
    | 2, _ => cases c <;> simp [solution, msgWeight]
  · intro T'
    obtain ⟨n, hn⟩ := exists_nat_gt T'
    exact ⟨n, hn⟩
  · intro r T'
    obtain ⟨n, hn⟩ := exists_nat_gt (T' - 1 - sepSpeakerOffset r - Δ (sepBaseWorld.host r))
    exact ⟨n, by change T' < (n : ℝ) + 1 + sepSpeakerOffset r + Δ (sepBaseWorld.host r); linarith⟩

private theorem peerOffsetFromView_append_other (l₁ l₂ : List (Event (Fin 3) 2 Payload))
    (hno : ∀ e ∈ l₂, ∀ s r, e.observation ≠ .received 1 (.answer s r) ∅)
    (hnoF : ∀ e ∈ l₂, ∀ s r F, e.observation ≠ .received 1 (.answer s r) F) :
    peerOffsetFromView (l₁ ++ l₂) = peerOffsetFromView l₁ := by
  have hnil : peerOffsetFromView l₂ = none := by
    induction l₂ with
    | nil => rfl
    | cons e rest ih =>
      simp only [peerOffsetFromView, ih (fun x hx => hno x (List.mem_cons_of_mem _ hx))
        (fun x hx => hnoF x (List.mem_cons_of_mem _ hx))]
      cases hobs : e.observation with
      | received i c F =>
        fin_cases i
        · rfl
        · cases c with
          | answer s r => exact absurd hobs (hnoF e (List.mem_cons_self ..) s r F)
          | _ => rfl
        · rfl
      | _ => rfl
  induction l₁ with
  | nil => simpa [peerOffsetFromView] using hnil
  | cons e rest ih =>
    simp only [List.cons_append, peerOffsetFromView, ih]

private theorem peerOffsetFromView_cons_answer (l₁ l₂ : List (Event (Fin 3) 2 Payload))
    (t₄ sent rec : ℝ) (F : Finset ℕ)
    (hnoF : ∀ e ∈ l₂, ∀ s r F', e.observation ≠ .received 1 (.answer s r) F') :
    peerOffsetFromView (l₁ ++ ⟨t₄, .received 1 (.answer sent rec) F⟩ :: l₂)
      = some (rec - (sent + t₄) / 2) := by
  have hnil : peerOffsetFromView l₂ = none := by
    induction l₂ with
    | nil => rfl
    | cons e rest ih =>
      simp only [peerOffsetFromView, ih (fun x hx => hnoF x (List.mem_cons_of_mem _ hx))]
      cases hobs : e.observation with
      | received i c F' =>
        fin_cases i
        · rfl
        · cases c with
          | answer s r => exact absurd hobs (hnoF e (List.mem_cons_self ..) s r F')
          | _ => rfl
        · rfl
      | _ => rfl
  induction l₁ with
  | nil => simp [peerOffsetFromView, hnil]
  | cons e rest ih => simp [peerOffsetFromView, ih]

/-- **Core Peer Half theorem.** On `w' = shiftStarKeepPeers sepBaseWorld Δ hstar`
with `Δ 0 = 0`, `|Δ 1| < 1/4`, `|Δ 2| < 1/4`:
1. `PeerSync.solution` plays every frame `n ≥ 2` at the **exact same true time**
   `n + 4 + Δ 1` on both speakers `0` and `1`!
2. Consequently `w'.sync (PeerSync.solution.plays w' 1) = 0`. -/
theorem sync_eq_zero (Δ : Fin 3 → ℝ) (hΔ0 : Δ 0 = 0)
    (hΔ1 : |Δ 1| < 1 / 4) (hΔ2 : |Δ 2| < 1 / 4)
    (hstar : ∀ i j s q a, (i = sepBaseWorld.sender ∨ j = sepBaseWorld.sender) →
      sepBaseWorld.network.deliver i j s q = some a → s + Δ i < a + Δ j) :
    let w' := shiftStarKeepPeers sepBaseWorld Δ hstar
    (∀ n, 2 ≤ n → (w'.playTime (solution.plays w' 1) 0 n).isSome ∧
        (w'.playTime (solution.plays w' 1) 1 n).isSome)
      ∧ w'.sync (solution.plays w' 1) = 0 := by
  intro w'
  have h1b := abs_lt.mp hΔ1
  have h2b := abs_lt.mp hΔ2
  have hprog := progress Δ hstar
  -- Helper: any frame `f` is handed before step `m` and delivered to hosts `1` and `2` by `f + 1/2 + Δ h`.
  have hframe_held : ∀ (r : Fin 2) (k : ℕ) (n : ℕ),
      (solution.states w' 1 n).askedNext r = k →
      earliest ((solution.states w' 1 n).key w') (solution.states w' 1 n).due = some (.asked r k) →
      ∀ f : ℕ, f ≤ k → f ∈ (solution.states w' 1 n).held (w'.host r) := by
    intro r k n hnk hne f hfk
    have hn_time : solution.eventTime w' 1 n = (k : ℝ) + 1 + sepSpeakerOffset r + Δ (w'.host r) := by
      unfold Solution.eventTime; rw [hne]; rfl
    have hoff_nn : 0 ≤ sepSpeakerOffset r := by fin_cases r <;> simp [sepSpeakerOffset]
    have hlt_hand : f < (solution.states w' 1 n).handedNext := by
      apply solution.lt_handedNext w' 1
      have hfk' : (f : ℝ) ≤ (k : ℝ) := by exact_mod_cast hfk
      have hΔr : -(1 / 4 : ℝ) < Δ (w'.host r) := by
        fin_cases r
        · change -(1 / 4 : ℝ) < Δ 1; linarith
        · change -(1 / 4 : ℝ) < Δ 2; linarith
      change (f : ℝ) < solution.eventTime w' 1 n
      rw [hn_time]; linarith
    obtain ⟨nh, hnh_lt, hnh_f, hnh_early⟩ := solution.exists_handed_step w' 1 hlt_hand
    have hmem_if : ∃ m ∈ (solution.states w' 1 (nh + 1)).inFlight,
        m.destination = w'.host r ∧ m.arrival = (f : ℝ) + 1 / 2 + Δ (w'.host r) ∧ f ∈ m.frames := by
      have hblk : w'.source.block f = [f] := by
        simp [w', shiftStarKeepPeers, sepBaseWorld, CaptureDevice.block]
      set obsH : Observation (Fin 3) 2 Payload :=
        .handed ((w'.source.block f).map fun n => (n, w'.target n)) (w'.source.reported f)
      have hhand_h : solution.handled w' 1 nh = some (0, w'.source.handed f, obsH) := by
        unfold Solution.handled
        rw [hnh_early]
        simp [w', shiftStarKeepPeers, sepBaseWorld, obsH]
      have hS_h : (solution 0 ((solution.states w' 1 nh).views 0 ++
          [⟨(w'.clock 0).read (w'.source.handed f), obsH⟩])).sends
          = [(1, .frame f, {f}), (2, .frame f, {f})] := by
        simp [solution, obsH, hblk]
      have hf_held0 : f ∈ (solution.states w' 1 nh).held 0 ∪ obsH.frames := by
        simp [obsH, Observation.frames, hblk]
      match r with
      | 0 =>
        have hsent := solution.sent_inFlight (w := w') 1 hhand_h hS_h (i := 0) (by simp)
          (arr := (f : ℝ) + 1 / 2 + Δ 1) (by simp [w', shiftStarKeepPeers, sepBaseWorld, hΔ0])
        exact ⟨_, hsent, by rfl, by rfl, by simpa [Finset.mem_filter] using hf_held0⟩
      | 1 =>
        have hsent := solution.sent_inFlight (w := w') 1 hhand_h hS_h (i := 1) (by simp)
          (arr := (f : ℝ) + 1 / 2 + Δ 2) (by simp [w', shiftStarKeepPeers, sepBaseWorld, hΔ0])
        exact ⟨_, hsent, by rfl, by rfl, by simpa [Finset.mem_filter] using hf_held0⟩
    obtain ⟨m, hm_if, hm_dst, hm_arr, hf_m⟩ := hmem_if
    have hsub := solution.frames_arrive w' 1 hm_if (Nat.succ_le_of_lt hnh_lt) (by
      rw [hm_arr, hn_time]
      have hfk' : (f : ℝ) ≤ (k : ℝ) := by exact_mod_cast hfk
      linarith)
    rw [hm_dst] at hsub
    exact hsub hf_m
  -- Helper: any `.answer` message ever in flight originated at host `1` in response to host `2`'s
  -- sole `.ask` at `b = 0` (`t₁ = 4/3`, `t₂ = 4/3 + Δ 2 + 1/10 - Δ 1`, arriving at `4/3 + Δ 2 + 2/10`).
  have hno_ask_other : ∀ m n', m ∈ (solution.states w' 1 n').inFlight →
      (∀ s, m.contents = .ask s → m.origin = 2 ∧ m.destination = 1 ∧ s = 4 / 3 ∧
        m.arrival = 4 / 3 + Δ 2 + 1 / 10) ∧
      (∀ s r, m.contents = .answer s r → m.origin = 1 ∧ m.destination = 2 ∧ s = 4 / 3 ∧
        r = 4 / 3 + Δ 2 + 1 / 10 - Δ 1 ∧ m.arrival = 4 / 3 + Δ 2 + 2 / 10) := by
    intro m n'
    induction n' generalizing m with
    | zero => intro hm; simp [Solution.states, State.start] at hm
    | succ n' ih =>
      intro hm
      have hstep := solution.mem_inFlight_succ w' 1 n' hm
      rcases hstep with hm_prev | ⟨h, t, obs, hhand, s_send, hmem_sends, hm_orig, hm_dst, hm_con, _, q, hdel⟩
      · exact ih m hm_prev
      · simp only [solution, List.getLast?_concat] at hmem_sends
        match h with
        | 0 =>
          cases obs with
          | handed fs _ =>
            cases hhd : fs.head? with
            | none => simp [hhd] at hmem_sends
            | some p =>
              simp only [hhd, List.mem_cons, List.not_mem_nil, or_false] at hmem_sends
              rcases hmem_sends with rfl | rfl <;>
                exact ⟨fun _ hc => (by rw [hm_con] at hc; cases hc),
                  fun _ _ hc => (by rw [hm_con] at hc; cases hc)⟩
          | _ => simp at hmem_sends
        | 1 =>
          cases obs with
          | received i c F =>
            match i with
            | 0 => simp at hmem_sends
            | 1 => simp at hmem_sends
            | 2 =>
              cases c with
              | ask s =>
                simp only [List.mem_singleton] at hmem_sends
                subst hmem_sends
                obtain ⟨m₀, hm₀, _, hm₀_arr, _, hm₀_con, _⟩ :=
                  solution.handled_received w' 1 hhand
                have hinfo := (ih m₀ hm₀).1 s hm₀_con
                have ht_eq : t = 4 / 3 + Δ 2 + 1 / 10 := by
                  linarith [hinfo.2.2.2, hm₀_arr]
                have hs_eq : s = 4 / 3 := hinfo.2.2.1
                have harr_eq : m.arrival = 4 / 3 + Δ 2 + 2 / 10 := by
                  simp only [w', shiftStarKeepPeers, sepBaseWorld] at hdel
                  injection hdel with hdel
                  linarith
                refine ⟨fun _ hc => (by rw [hm_con] at hc; cases hc), fun s' r' hc => ?_⟩
                rw [hm_con] at hc; injection hc with hs' hr'
                refine ⟨hm_orig, hm_dst, hs'.symm.trans hs_eq, ?_, harr_eq⟩
                rw [← hr']
                simp only [w', shiftStarKeepPeers, sepBaseWorld, id_eq, ht_eq]
              | _ => simp at hmem_sends
          | asked r _ _ =>
            match r with
            | 0 => simp at hmem_sends
            | 1 => simp at hmem_sends
          | _ => simp at hmem_sends
        | 2 =>
          cases obs with
          | asked r outs _ =>
            match r with
            | 0 => simp at hmem_sends
            | 1 =>
              simp only at hmem_sends
              split_ifs at hmem_sends with houts
              · simp only [List.mem_singleton] at hmem_sends
                subst hmem_sends
                have hearly := solution.handled_asked w' 1 hhand
                have hha := solution.handled_of_asked w' 1 hearly
                rw [hhand] at hha
                simp only [Option.some.injEq, Prod.mk.injEq, Observation.asked.injEq] at hha
                obtain ⟨_, ht_eq0, _, houts_eq, _⟩ := hha
                have hblk_eq : (w'.speaker 1).block ((solution.states w' 1 n').askedNext 1) = [0] := by
                  rw [← houts_eq, houts]
                have hb0 : (solution.states w' 1 n').askedNext 1 = 0 := by
                  have h1 : (w'.speaker 1).block ((solution.states w' 1 n').askedNext 1)
                      = [(solution.states w' 1 n').askedNext 1] := by
                    simp [w', shiftStarKeepPeers, sepBaseWorld, PlaybackDevice.block]
                  rw [h1] at hblk_eq
                  injection hblk_eq
                have ht_eq : t = 4 / 3 + Δ 2 := by
                  rw [ht_eq0, hb0]
                  simp [w', shiftStarKeepPeers, sepBaseWorld, sepSpeakerOffset]
                  ring
                have harr_eq : m.arrival = 4 / 3 + Δ 2 + 1 / 10 := by
                  simp only [w', shiftStarKeepPeers, sepBaseWorld] at hdel
                  injection hdel with hdel
                  linarith
                refine ⟨fun s' hc => ?_, fun _ _ hc => (by rw [hm_con] at hc; cases hc)⟩
                rw [hm_con] at hc; injection hc with hs'
                refine ⟨hm_orig, hm_dst, ?_, harr_eq⟩
                rw [← hs']
                simp only [w', shiftStarKeepPeers, sepBaseWorld, id_eq, ht_eq]
                ring
              · simp at hmem_sends
          | _ => simp at hmem_sends
  -- Show the single `.answer` reply IS delivered to host `2` before `4/3 + Δ 2 + 3/10 < 10/3 + Δ 2`.
  have hreply_in_view : ∀ n, (solution.states w' 1 n).askedNext 1 ≥ 3 →
      peerOffsetFromView ((solution.states w' 1 n).views 2) = some (Δ 2 - Δ 1) := by
    intro n hn3
    -- Step `na0`: host `2` handles request `b = 0` at `4/3 + Δ 2`, sending `.ask (4/3)` to host `1`.
    obtain ⟨na0, hna0_lt, hna0_b, hna0_early⟩ :=
      solution.exists_asked_step w' 1 (r := 1) (show 0 < (solution.states w' 1 n).askedNext 1 by omega)
    have hblk0 : (w'.speaker 1).block 0 = [0] := by
      simp [w', shiftStarKeepPeers, sepBaseWorld, PlaybackDevice.block]
    have hclk0 : (w'.clock 2).read ((w'.speaker 1).asked 0) = 4 / 3 := by
      simp [w', shiftStarKeepPeers, sepBaseWorld, sepSpeakerOffset]; ring
    have hhand0 : solution.handled w' 1 na0 =
        some (2, (w'.speaker 1).asked 0, .asked 1 ((w'.speaker 1).block 0) ((w'.speaker 1).reported 0)) :=
      solution.handled_of_asked w' 1 hna0_early
    have hS0 : (solution 2 ((solution.states w' 1 na0).views 2 ++
        [⟨(w'.clock 2).read ((w'.speaker 1).asked 0),
          .asked 1 ((w'.speaker 1).block 0) ((w'.speaker 1).reported 0)⟩])).sends
        = [(1, Payload.ask (4 / 3), ∅)] := by
      simp [solution, hblk0, hclk0]
    have mask_in : (⟨4 / 3 + Δ 2 + 1 / 10, 2, 1, Payload.ask (4 / 3), ∅⟩ : InFlight (Fin 3) Payload)
        ∈ (solution.states w' 1 (na0 + 1)).inFlight := by
      have hsent := solution.sent_inFlight (w := w') 1 hhand0 hS0 (i := 0) (by simp)
        (arr := 4 / 3 + Δ 2 + 1 / 10) (by simp [w', shiftStarKeepPeers, sepBaseWorld, sepSpeakerOffset]; ring)
      simpa using hsent
    -- The `.ask` is handled before step `n` (since `eventTime n ≥ asked 2 = 10/3 + Δ 2 > 4/3 + Δ 2 + 1/10`).
    have hn_gt_ask : 4 / 3 + Δ 2 + 1 / 10 < solution.eventTime w' 1 n := by
      obtain ⟨na2, hna2_lt, _, hna2_early⟩ :=
        solution.exists_asked_step w' 1 (r := 1) (show 2 < (solution.states w' 1 n).askedNext 1 by omega)
      have hmono := solution.eventTime_mono w' 1 hna2_lt.le
      have ht2 : solution.eventTime w' 1 na2 = 10 / 3 + Δ 2 := by
        unfold Solution.eventTime; rw [hna2_early]
        simp [State.key, w', shiftStarKeepPeers, sepBaseWorld, sepSpeakerOffset]; norm_num
      linarith
    obtain ⟨n_ask, _, hn_ask_lt, hhand_ask⟩ :=
      solution.handled_before w' 1 mask_in (Nat.succ_le_of_lt hna0_lt) hn_gt_ask
    -- At step `n_ask`, host `1` sends `.answer (4/3) (4/3 + Δ 2 + 1/10 - Δ 1)` arriving at `4/3 + Δ 2 + 2/10`.
    have mans_in : (⟨4 / 3 + Δ 2 + 2 / 10, 1, 2, Payload.answer (4 / 3) (4 / 3 + Δ 2 + 1 / 10 - Δ 1), ∅⟩ :
        InFlight (Fin 3) Payload) ∈ (solution.states w' 1 (n_ask + 1)).inFlight := by
      have hclk1 : (w'.clock 1).read (4 / 3 + Δ 2 + 1 / 10) = 4 / 3 + Δ 2 + 1 / 10 - Δ 1 := by
        simp [w', shiftStarKeepPeers, sepBaseWorld]
      have hS1 : (solution 1 ((solution.states w' 1 n_ask).views 1 ++
          [⟨(w'.clock 1).read (4 / 3 + Δ 2 + 1 / 10), .received 2 (.ask (4 / 3)) ∅⟩])).sends
          = [(2, Payload.answer (4 / 3) (4 / 3 + Δ 2 + 1 / 10 - Δ 1), ∅)] := by
        simp only [solution, List.getLast?_concat, hclk1]
      have hsent := solution.sent_inFlight (w := w') 1 hhand_ask hS1 (i := 0) (by simp)
        (arr := 4 / 3 + Δ 2 + 2 / 10) (by simp [w', shiftStarKeepPeers, sepBaseWorld]; ring)
      simpa using hsent
    -- That `.answer` arrives and is handled before step `n`!
    have hn_gt_ans : 4 / 3 + Δ 2 + 2 / 10 < solution.eventTime w' 1 n := by
      obtain ⟨na2, hna2_lt, _, hna2_early⟩ :=
        solution.exists_asked_step w' 1 (r := 1) (show 2 < (solution.states w' 1 n).askedNext 1 by omega)
      have hmono := solution.eventTime_mono w' 1 hna2_lt.le
      have ht2 : solution.eventTime w' 1 na2 = 10 / 3 + Δ 2 := by
        unfold Solution.eventTime; rw [hna2_early]
        simp [State.key, w', shiftStarKeepPeers, sepBaseWorld, sepSpeakerOffset]; norm_num
      linarith
    obtain ⟨n_ans, _, hn_ans_lt, hhand_ans⟩ :=
      solution.handled_before w' 1 mans_in (Nat.succ_le_of_lt hn_ask_lt) hn_gt_ans
    -- So the `.answer` event appears in `(solution.states w' 1 n).views 2`, AND every `.answer`
    -- event in `(solution.states w' 1 n).views 2` has the exact same `(sent, rec, t₄)`.
    have hmem_ans := solution.mem_views_of_handled w' 1 hhand_ans hn_ans_lt
    -- Any event in `views 2` that is `.received 1 (.answer s r) F` yields `Δ 2 - Δ 1`.
    have hall_ans : ∀ e ∈ (solution.states w' 1 n).views 2, ∀ s r F,
        e.observation = .received 1 (.answer s r) F →
        r - (s + e.reading) / 2 = Δ 2 - Δ 1 := by
      intro e he s r F hobs
      obtain ⟨i, _, t, obs, hhi, heq⟩ := solution.handled_of_mem_views w' 1 he
      rcases e with ⟨e_read, e_obs⟩
      simp only [Event.mk.injEq] at heq
      obtain ⟨hread, hobs'⟩ := heq
      dsimp only at hobs ⊢
      rw [hobs] at hobs'
      subst hobs'
      obtain ⟨m₀, hm₀, _, hm₀_arr, _, hm₀_con, _⟩ := solution.handled_received w' 1 hhi
      have hinfo := (hno_ask_other m₀ i hm₀).2 s r hm₀_con
      have ht_eq : t = 4 / 3 + Δ 2 + 2 / 10 := by linarith [hm₀_arr, hinfo.2.2.2.2]
      rw [hread, ht_eq, hinfo.2.2.1, hinfo.2.2.2.1]
      simp only [w', shiftStarKeepPeers, sepBaseWorld, id_eq]
      ring
    -- Induct on any list containing an `.answer` whose every `.answer` evaluates to `Δ 2 - Δ 1`.
    have hlist : ∀ l : List (Event (Fin 3) 2 Payload),
        (∃ e ∈ l, ∃ s r F, e.observation = .received 1 (.answer s r) F) →
        (∀ e ∈ l, ∀ s r F, e.observation = .received 1 (.answer s r) F →
          r - (s + e.reading) / 2 = Δ 2 - Δ 1) →
        peerOffsetFromView l = some (Δ 2 - Δ 1) := by
      intro l
      induction l with
      | nil => intro hex _; obtain ⟨_, h, _⟩ := hex; simp at h
      | cons e rest ih =>
        intro hex hall
        by_cases hrest : ∃ e' ∈ rest, ∃ s r F, e'.observation = .received 1 (.answer s r) F
        · rw [peerOffsetFromView, ih hrest (fun x hx => hall x (List.mem_cons_of_mem _ hx))]
        · have hnone : peerOffsetFromView rest = none := by
            clear ih hex hall
            induction rest with
            | nil => rfl
            | cons e' r' ih' =>
              have hne' : ¬ ∃ x ∈ r', ∃ s r F, x.observation = .received 1 (.answer s r) F :=
                fun ⟨x, hx, h⟩ => hrest ⟨x, List.mem_cons_of_mem _ hx, h⟩
              simp only [peerOffsetFromView, ih' hne']
              cases hobs : e'.observation with
              | received i c F =>
                match i with
                | 0 => rfl
                | 1 =>
                  cases c with
                  | answer s r =>
                    exact absurd ⟨e', List.mem_cons_self .., s, r, F, hobs⟩ hrest
                  | _ => rfl
                | 2 => rfl
              | _ => rfl
          obtain ⟨e₀, he₀, s, r, F, hobs⟩ := hex
          rcases List.mem_cons.mp he₀ with rfl | hmem_r
          · simp only [peerOffsetFromView, hnone, hobs]
            exact congrArg some (hall e₀ (List.mem_cons_self ..) s r F hobs)
          · exact absurd ⟨e₀, hmem_r, s, r, F, hobs⟩ hrest
    exact hlist _ ⟨_, hmem_ans, 4 / 3, 4 / 3 + Δ 2 + 1 / 10 - Δ 1, ∅, rfl⟩ hall_ans
  -- Compute `solution.plays w' 1 r k` for `r = 0, 1` and `k ≥ 3`.
  have hplays0 : ∀ k, 3 ≤ k → solution.plays w' 1 0 k = some ((k : ℝ) - 2) := by
    intro k hk3
    obtain ⟨m, hm⟩ := hprog ((w'.speaker 0).asked k)
    obtain ⟨n, -, hnk, hne⟩ := solution.exists_asked_step w' 1 (solution.lt_askedNext w' 1 hm)
    have hmem_k : k ∈ (w'.speaker 0).block k := by
      simp [w', shiftStarKeepPeers, sepBaseWorld, PlaybackDevice.block]
    have hlt_k : (w'.speaker 0).asked k < (w'.speaker 0).out k := by
      show (k : ℝ) + 1 + sepSpeakerOffset 0 + Δ (sepBaseWorld.host 0)
        < (k : ℝ) + 2 + sepSpeakerOffset 0 + Δ (sepBaseWorld.host 0)
      linarith
    rw [solution.plays_of_asked_step_of_lt w' 1 hnk hne hmem_k hlt_k]
    have hact : (solution (w'.host 0) ((solution.states w' 1 n).views (w'.host 0) ++
        [⟨(w'.clock (w'.host 0)).read ((w'.speaker 0).asked k),
          .asked 0 ((w'.speaker 0).block k) ((w'.speaker 0).reported k)⟩])).plays k
        = some ((k : ℝ) - 2) := by
      change (solution 1 _).plays k = _
      simp [solution, hk3]
    rw [hact]
    unfold playable
    dsimp only
    split_ifs with hcond
    · rfl
    · exfalso; apply hcond
      have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      refine ⟨by linarith, fun f hf => ?_⟩
      have hf1 : |(f : ℝ) - ((k : ℝ) - 2)| < 1 := by simpa using hf
      have hf' := (abs_lt.mp hf1).2
      have hfk : f ≤ k := by
        have hfk_r : (f : ℝ) < (k : ℝ) := by linarith
        exact Nat.le_of_lt (Nat.cast_lt.mp hfk_r)
      exact hframe_held 0 k n hnk hne f hfk
  have hplays1 : ∀ k, 3 ≤ k → solution.plays w' 1 1 k = some ((k : ℝ) - 2 + 1 / 3 + (Δ 2 - Δ 1)) := by
    intro k hk3
    obtain ⟨m, hm⟩ := hprog ((w'.speaker 1).asked k)
    obtain ⟨n, -, hnk, hne⟩ := solution.exists_asked_step w' 1 (solution.lt_askedNext w' 1 hm)
    have hmem_k : k ∈ (w'.speaker 1).block k := by
      simp [w', shiftStarKeepPeers, sepBaseWorld, PlaybackDevice.block]
    have hlt_k : (w'.speaker 1).asked k < (w'.speaker 1).out k := by
      show (k : ℝ) + 1 + sepSpeakerOffset 1 + Δ (sepBaseWorld.host 1)
        < (k : ℝ) + 2 + sepSpeakerOffset 1 + Δ (sepBaseWorld.host 1)
      linarith
    rw [solution.plays_of_asked_step_of_lt w' 1 hnk hne hmem_k hlt_k]
    have hoff := hreply_in_view n (by omega)
    have hhost1 : w'.host 1 = 2 := rfl
    have hact : (solution (w'.host 1) ((solution.states w' 1 n).views (w'.host 1) ++
        [⟨(w'.clock (w'.host 1)).read ((w'.speaker 1).asked k),
          .asked 1 ((w'.speaker 1).block k) ((w'.speaker 1).reported k)⟩])).plays k
        = some ((k : ℝ) - 2 + 1 / 3 + (Δ 2 - Δ 1)) := by
      rw [hhost1]
      simp [solution, hoff, hk3]
    rw [hact]
    unfold playable
    dsimp only
    split_ifs with hcond
    · rfl
    · exfalso; apply hcond
      have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      refine ⟨by linarith, fun f hf => ?_⟩
      have hf1 : |(f : ℝ) - ((k : ℝ) - 2 + 1 / 3 + (Δ 2 - Δ 1))| < 1 := by simpa using hf
      have hf' := (abs_lt.mp hf1).2
      have hfk : f ≤ k := by
        have hfk_r : (f : ℝ) < (k : ℝ) := by linarith
        exact Nat.le_of_lt (Nat.cast_lt.mp hfk_r)
      exact hframe_held 1 k n hnk hne f hfk
  -- Compute exact `w'.playTime` for EVERY frame `n ≥ 2` on BOTH speakers!
  have hpt_eq : ∀ n, 2 ≤ n →
      w'.playTime (solution.plays w' 1) 0 n = some ((n : ℝ) + 4 + Δ 1) ∧
      w'.playTime (solution.plays w' 1) 1 n = some ((n : ℝ) + 4 + Δ 1) := by
    intro n hn2
    have hpt_of_cov : ∀ (r : Fin 2) (c : ℝ) (hpl : ∀ k, 3 ≤ k → solution.plays w' 1 r k = some ((k : ℝ) - 2 + c))
        (hlo_cov : ∀ k, Covers (solution.plays w' 1 r) k n → 3 ≤ k)
        (hex : ∃ k, Covers (solution.plays w' 1 r) k n),
        w'.playTime (solution.plays w' 1) r n = some ((n : ℝ) + 4 + sepSpeakerOffset r - c + Δ (w'.host r)) := by
      classical
      intro r c hpl hlo_cov hex
      unfold World.playTime Spec.playTime
      simp only [hex, ↓reduceDIte]
      set k₀ := Nat.find hex
      have hcov : Covers (solution.plays w' 1 r) k₀ n := Nat.find_spec hex
      have hk₀3 : 3 ≤ k₀ := hlo_cov k₀ hcov
      have hx := hpl k₀ hk₀3
      have hy := hpl (k₀ + 1) (by omega)
      rw [hx, hy]
      dsimp only
      congr 1
      change ((k₀ : ℝ) + 2 + sepSpeakerOffset r + Δ (w'.host r))
          + ((n : ℝ) - ((k₀ : ℝ) - 2 + c)) / (((k₀ + 1 : ℕ) : ℝ) - 2 + c - ((k₀ : ℝ) - 2 + c))
            * (((k₀ + 1 : ℕ) : ℝ) + 2 + sepSpeakerOffset r + Δ (w'.host r)
              - ((k₀ : ℝ) + 2 + sepSpeakerOffset r + Δ (w'.host r)))
        = (n : ℝ) + 4 + sepSpeakerOffset r - c + Δ (w'.host r)
      push_cast
      ring
    have hno_lt3 : ∀ (r : Fin 2) (k : ℕ), k < 3 → solution.plays w' 1 r k = none := by
      intro r k hk3
      by_contra hne
      cases hval : solution.plays w' 1 r k with
      | none => exact hne hval
      | some x =>
        obtain ⟨b, m, hkb, _, _, hp⟩ := exists_asked_of_plays_some solution w' 1 hval
        match r with
        | 0 =>
          change (solution 1 _).plays k = some x at hp
          simp [solution, show ¬(3 ≤ k) by omega] at hp
        | 1 =>
          have hhost1 : w'.host 1 = 2 := rfl
          rw [hhost1] at hp
          simp only [solution, List.getLast?_concat, List.dropLast_concat] at hp
          cases hpo : peerOffsetFromView ((solution.states w' 1 m).views 2) with
          | none => rw [hpo] at hp; simp at hp
          | some θ => rw [hpo] at hp; simp [show ¬(3 ≤ k) by omega] at hp
    have hcov_ge3 : ∀ (r : Fin 2) (k : ℕ), Covers (solution.plays w' 1 r) k n → 3 ≤ k := by
      intro r k ⟨x, _, hx, _⟩
      by_contra hlt
      rw [hno_lt3 r k (by omega)] at hx
      simp at hx
    constructor
    · have hex0 : ∃ k, Covers (solution.plays w' 1 0) k n := by
        refine ⟨n + 2, (n : ℝ), (n : ℝ) + 1, ?_, ?_, by linarith, by linarith, le_rfl, by linarith⟩
        · have := hplays0 (n + 2) (by omega)
          rw [this]; congr 1; push_cast; ring
        · have := hplays0 (n + 3) (by omega)
          rw [this]; congr 1; push_cast; ring
      have h0 := hpt_of_cov 0 0 (fun k hk => by simpa using hplays0 k hk) (hcov_ge3 0) hex0
      simpa [w', shiftStarKeepPeers, sepBaseWorld, sepSpeakerOffset] using h0
    · set c₁ : ℝ := 1 / 3 + (Δ 2 - Δ 1)
      have hc₁_lo : -(1 / 6 : ℝ) < c₁ := by dsimp [c₁]; linarith
      have hc₁_hi : c₁ < 5 / 6 := by dsimp [c₁]; linarith
      have hex1 : ∃ k, Covers (solution.plays w' 1 1) k n := by
        by_cases hsign : 0 < c₁
        · refine ⟨n + 1, (n : ℝ) - 1 + c₁, (n : ℝ) + c₁, ?_, ?_,
            by linarith, by linarith, by linarith, by linarith⟩
          · have := hplays1 (n + 1) (by omega)
            rw [this]; congr 1; dsimp [c₁]; push_cast; ring
          · have := hplays1 (n + 2) (by omega)
            rw [this]; congr 1; dsimp [c₁]; push_cast; ring
        · refine ⟨n + 2, (n : ℝ) + c₁, (n : ℝ) + 1 + c₁, ?_, ?_,
            by linarith, by linarith, by linarith, by linarith⟩
          · have := hplays1 (n + 2) (by omega)
            rw [this]; congr 1; dsimp [c₁]; push_cast; ring
          · have := hplays1 (n + 3) (by omega)
            rw [this]; congr 1; dsimp [c₁]; push_cast; ring
      have h1 := hpt_of_cov 1 c₁
        (fun k hk => by rw [hplays1 k hk]; congr 1; dsimp [c₁]; ring) (hcov_ge3 1) hex1
      rw [h1]; congr 1
      change (n : ℝ) + 4 + (1 / 3 : ℝ) - (1 / 3 + (Δ 2 - Δ 1)) + Δ 2 = (n : ℝ) + 4 + Δ 1
      ring
  refine ⟨fun n hn => ⟨by rw [(hpt_eq n hn).1]; rfl, by rw [(hpt_eq n hn).2]; rfl⟩, ?_⟩
  -- Every frame `n ≥ 2` has `w'.syncCost (solution.plays w' 1) n = 0`, so `w'.sync = 0`.
  have hsyncCost_zero : ∀ n, 2 ≤ n → w'.syncCost (solution.plays w' 1) n = 0 := by
    intro n hn
    unfold World.syncCost World.pairCost
    have hfilt : (Finset.univ.filter (fun p : Fin 2 × Fin 2 => p.1 < p.2)) = {(0, 1)} := by
      ext ⟨a, b⟩; fin_cases a <;> fin_cases b <;> decide
    rw [hfilt, Finset.sum_singleton, (hpt_eq n hn).1, (hpt_eq n hn).2]
    simp
  refine le_antisymm ?_ zero_le
  have hfin : ∑ n ∈ Finset.range 2,
      w'.syncCost (solution.plays w' 1) n
        * ENNReal.ofReal (w'.source.capture (n + 1) - w'.source.capture n) ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun n _ => ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
    unfold World.syncCost World.pairCost
    apply ENNReal.mul_ne_top (by simp)
    refine ENNReal.sum_ne_top.mpr fun p _ => ?_
    cases w'.playTime (solution.plays w' 1) p.1 n <;>
      cases w'.playTime (solution.plays w' 1) p.2 n <;> simp
  refine longRun_le hfin 0 fun T _ => ?_
  simp only [zero_mul, zero_add]
  unfold World.accruedFrames
  rw [tsum_eq_sum (s := Finset.range 2)]
  · exact Finset.sum_le_sum fun n _ => by split_ifs <;> simp
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [hsyncCost_zero n hn]

end PeerSync

/-- **Two-sided Star-vs-Peer asymmetry separation theorem on `Unisono.Spec`.**
For any star asymmetry `A` with `0 < A < 1/4` (including `A = 1/5`, where the
symmetric peer link delay `1/10` is strictly smaller than `2 A`), consider the
exact same pair of 3-host worlds `(w⁺, w⁻) = (sepWorldPlus A, sepWorldMinus A)`:

1. **Star lower bound:** Every non-Zeno star solution `σ` (`σ.IsStar 0`)
   that plays all frames from some `N` onward must suffer
   `ENNReal.ofReal (A ^ 2) ≤ max (w⁺.sync) (w⁻.sync)`.
2. **Concrete peer upper bound:** `PeerSync.solution` uses only star links and
   the symmetric peer link `1 ↔ 2`, is non-Zeno, plays every frame `n ≥ 2` on
   both speakers, and achieves **`w⁺.sync = 0` AND `w⁻.sync = 0`**! -/
theorem peer_beats_star_asymmetry_bound {A : ℝ} (hA0 : 0 < A) (hA4 : A < 1 / 4) :
    let hA : |A| < 1 / 4 := abs_lt.mpr ⟨by linarith, hA4⟩
    let wPlus := sepWorldPlus hA
    let wMinus := sepWorldMinus hA
    (∀ {Msg : Type} (σ : Solution (Fin 3) 2 Msg),
      σ.IsStar 0 →
      (∀ T : Time, ∃ n, T < σ.eventTime sepBaseWorld 1 n) →
      (∀ T : Time, ∃ n, T < σ.eventTime wPlus 1 n) →
      (∀ T : Time, ∃ n, T < σ.eventTime wMinus 1 n) →
      ∀ N : ℕ, (∀ n, N ≤ n → ∀ r, (sepBaseWorld.playTime (σ.plays sepBaseWorld 1) r n).isSome) →
      ENNReal.ofReal (A ^ 2)
        ≤ max (wPlus.sync (σ.plays wPlus 1)) (wMinus.sync (σ.plays wMinus 1)))
    ∧ (PeerSync.solution.UsesGraph (fun i j => i = 0 ∨ j = 0 ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1))
        ∧ (∀ T : Time, ∃ n, T < PeerSync.solution.eventTime wPlus 1 n)
        ∧ (∀ T : Time, ∃ n, T < PeerSync.solution.eventTime wMinus 1 n)
        ∧ (∀ n, 2 ≤ n → (wPlus.playTime (PeerSync.solution.plays wPlus 1) 0 n).isSome ∧
            (wPlus.playTime (PeerSync.solution.plays wPlus 1) 1 n).isSome)
        ∧ (∀ n, 2 ≤ n → (wMinus.playTime (PeerSync.solution.plays wMinus 1) 0 n).isSome ∧
            (wMinus.playTime (PeerSync.solution.plays wMinus 1) 1 n).isSome)
        ∧ wPlus.sync (PeerSync.solution.plays wPlus 1) = 0
        ∧ wMinus.sync (PeerSync.solution.plays wMinus 1) = 0) := by
  intro hA wPlus wMinus
  refine ⟨?_, ?_⟩
  · intro Msg σ hstar hprog hprog₁ hprog₂ N hplay
    have hvar : varFin (fun r : Fin 2 => sepShift A (sepBaseWorld.host r)) = A ^ 2 := by
      unfold varFin meanFin
      simp only [Fin.sum_univ_two, sepBaseWorld, sepShift, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Nat.cast_ofNat]
      ring
    have hunb : ∀ T : Time, ∃ n, T ≤ sepBaseWorld.source.capture n := fun T => by
      obtain ⟨n, hn⟩ := exists_nat_ge T
      exact ⟨n, hn⟩
    have hlb := star_sync_lower_bound_with_symmetric_peers σ sepBaseWorld 1 hstar (sepShift A) rfl
      (sepShift_star_net hA) (sepShift_neg_star_net hA)
      hprog hprog₁ hprog₂ (by norm_num) N hplay hunb
    rw [hvar] at hlb
    exact hlb
  · have hplus := PeerSync.sync_eq_zero (sepShift A) rfl hA (by simpa [sepShift] using hA)
      (sepShift_star_net hA)
    have hminus := PeerSync.sync_eq_zero (-(sepShift A)) (by simp [sepShift])
      (by simpa [sepShift] using hA) (by simpa [sepShift] using hA) (sepShift_neg_star_net hA)
    exact ⟨PeerSync.usesGraph,
      PeerSync.progress (sepShift A) (sepShift_star_net hA),
      PeerSync.progress (-(sepShift A)) (sepShift_neg_star_net hA),
      hplus.1, hminus.1, hplus.2, hminus.2⟩

end StarVsPeerSeparation

end Unisono.Spec
