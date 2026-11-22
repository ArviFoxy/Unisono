/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Model.Regulation
public import Unisono.Solutions.FixedDelay
public import Unisono.Spec.AtLatency
public import Unisono.Spec.Models.Bounded
public import Unisono.Spec.Topologies

/-!
# Concrete `Unisono.Spec.Solution` protocols and Star-vs-Peer separation

This module defines concrete `Unisono.Spec.Solution` protocols in the formal
specification's event-driven run model (`Unisono.Spec.Solution`,
`Unisono.Spec.World`, `Unisono.Spec.Objectives`) and establishes a two-sided
Star-vs-Peer asymmetry separation theorem directly on `Unisono.Spec`.

## Scope and honesty note

The two concrete protocols below (`StarProtocol` and `PeerProtocol`) are
simplified per-sample reference protocols in the `Unisono.Spec` run model; they
do **not** implement the two-state Kalman filter or per-cycle optimal control
analyzed in `ModalControl`, `Spectral`, `Estimation`, and `Level`, and no
theorem here bounds their synchronization, tracking, roughness, or missed-sample
objectives. What we formally prove for `StarProtocol` and `PeerProtocol` are
topology membership (`IsStar` / `UsesGraph`), non-Zeno progress (`progress`,
`request_step`), exact matching of `stepSample` to `Regulation.next`, and the
`Unisono.Spec.Solution.WithinSpeed` safety property in every bounded world.

## Contents

1. **Baseline topology (`fixedDelay_isStar`).** `FixedDelay.solution` is a star
   solution (`Solution.IsStar`).
2. **Concrete Star protocol (`StarProtocol.solution`).** Uses sliding-window
   minimum-RTT clock probes (`ask` / `answer`) and per-sample
   `Unisono.Model.Regulation.law` speed regulation with exact lag state
   `((goal - 1) - prevPos, prevPace - 1)` (`stepSample_matches_regulation_next`)
   and speed clamping. Proves `isStar`, `progress`, `request_step`, and
   `withinSpeed`.
3. **Concrete Peer protocol (`PeerProtocol.solution`).** Extends the protocol
   with direct peer clock probes, one-hop peer path averaging in `senderOffset`,
   periodic `Payload.peerState` exchanges, and separated common/differential
   modal regulation. Proves `usesGraph`, `progress` (under a per-host peer-count
   bound `∀ h, (p.peers h).length ≤ maxPeers`), `request_step`, and
   `withinSpeed`.
4. **Two-sided Star-vs-Peer asymmetry separation directly on `Unisono.Spec`:**
   * `star_states_eq_of_star_links_eq`: any `IsStar` solution produces
     identical runs when non-star (receiver–receiver) links are modified.
   * `star_sync_lower_bound_with_symmetric_peers`: using host-local view
     invariance (`Solution.plays_shiftHosts`, with **no** global event-order
     `horder` assumption and **no** delay restriction on peer links — only
     star-link delays must exceed `|Δ|`), every non-Zeno star solution without
     simultaneous cross-origin arrivals suffers
     `max (w⁺.sync) (w⁻.sync) ≥ ENNReal.ofReal (varFin (fun r => Δ (w.host r)))`
     on `(w⁺, w⁻) = (shiftStarKeepPeers w Δ, shiftStarKeepPeers w (-Δ))`.
   * `peer_probe_recovers_exact_offset`: NTP clock-reading identity for a
     symmetric peer exchange.
   * **`peer_beats_star_asymmetry_bound`** (the concrete peer half): on an
     explicit 3-host world pair `(sepWorldPlus A, sepWorldMinus A)` with
     star-link delay `1/2`, symmetric peer-link delay `1/10`, and star shifts
     `±A` for any `A ∈ (0, 1/4)` (allowing `1/10 < 2 A`, e.g., `A = 1/5`),
     every qualifying star solution suffers `max sync ≥ ENNReal.ofReal (A²)`,
     whereas the concrete causal peer solution `PeerSync.solution` uses only
     star links plus the symmetric peer link `1 ↔ 2`, plays every frame
     `n ≥ 2`, and achieves `sync = 0` in **both** worlds.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Optimal

open Unisono.Spec Unisono.Model.Regulation
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
  have hp := σ.plays_of_asked_step w lookahead hnb hnearly hk_mem
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

/-! ## 2. Concrete Star protocol (`StarProtocol`) -/

namespace StarProtocol

variable {H : Type} {R : ℕ}

/-- Message payload for the concrete star protocol. -/
inductive Payload where
  /-- Stream block carrying first frame index, capture timestamp, and announced
  playout level `L`. -/
  | block (first : ℕ) (stamp : ℝ) (level : ℝ)
  /-- Non-blocking clock probe carrying requester timestamp `t₁`. -/
  | ask (sent : ℝ)
  /-- Reply to a clock probe carrying `(t₁, t₂)`. -/
  | answer (sent : ℝ) (received : ℝ)

/-- Parameters of the concrete star protocol. -/
structure Params (H : Type) where
  sender : H
  speakers : List H
  rate : ℝ
  level : ℝ
  copies : ℕ
  period : ℝ
  /-- Regulation gain `g ∈ (0, 1)` for `Unisono.Model.Regulation.law`. -/
  gain : ℝ
  /-- Maximum per-sample speed deviation (e.g. `1e-4` for 100 ppm). -/
  maxSlew : ℝ
  /-- Sliding-window capacity for minimum-RTT probe selection. -/
  windowSize : ℕ

/-- Per-host state reconstructed from a host's event view. -/
structure Memory (H : Type) (R : ℕ) where
  /-- Latest received stream block: `(first, stamp, level)`. -/
  block : Option (ℕ × ℝ × ℝ)
  /-- Recent `(sent, rtt, rawOffset)` clock probe replies (newest last). -/
  rttWindow : List (ℝ × ℝ × ℝ)
  /-- Current minimum-RTT raw offset `(lastSent, offset)` (no Kalman filter). -/
  offset : Option (ℝ × ℝ)
  /-- Clock reading of the last outgoing clock query. -/
  asked : Option ℝ
  /-- At the sender: latest query timestamp answered per host. -/
  answered : H → Option ℝ
  /-- Per-speaker regulator state `(lastSample, position, pace)`. -/
  reg : Fin R → Option (ℕ × ℝ × ℝ)

def Memory.empty : Memory H R where
  block := none
  rttWindow := []
  offset := none
  asked := none
  answered := fun _ => none
  reg := fun _ => none

def clamp (w x : ℝ) : ℝ := max (-w) (min w x)

theorem clamp_mem {w x : ℝ} (hw : 0 ≤ w) : -w ≤ clamp w x ∧ clamp w x ≤ w := by
  unfold clamp
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Select the offset sample with minimum RTT from a nonempty sliding window. -/
def minRttOffset : List (ℝ × ℝ × ℝ) → Option (ℝ × ℝ)
  | [] => none
  | (s, rtt, off) :: rest =>
      match minRttOffset rest with
      | none => some (s, off)
      | some (s', off') =>
          let bestRtt := rest.foldl (fun acc x => min acc x.2.1) rtt
          if rtt ≤ bestRtt then some (s, off) else some (s', off')

variable (p : Params H)

def target (m : Memory H R) (first : ℕ) (stamp : ℝ) (k : ℕ) : Option ℝ :=
  match m.block, m.offset with
  | some (f, captured, lvl), some (_, off) =>
      some (f + ((stamp + ((k : ℝ) - first) / p.rate + off - lvl) - captured) * p.rate)
  | _, _ => none

/-- Advance one output sample using `Unisono.Model.Regulation.law p.gain` on
the exact Regulation state `(E, v) = ((goal - 1) - prevPos, prevPace - 1)`,
clamping playback pace to `[1 - maxSlew, 1 + maxSlew]`. -/
def stepSample (prevPos prevPace goal : ℝ) : ℝ × ℝ :=
  let err := (goal - 1) - prevPos
  let delta := law p.gain (err, prevPace - 1)
  let newPace := 1 + clamp p.maxSlew ((prevPace - 1) + delta)
  (prevPos + newPace, newPace)

/-- When the slew clamp does not saturate, `stepSample` transitions the
`(lag, excessPace)` state identically to `Unisono.Model.Regulation.next`. -/
theorem stepSample_matches_regulation_next (prevPos prevPace goal : ℝ)
    (hunclamped : |(prevPace - 1) + law p.gain ((goal - 1) - prevPos, prevPace - 1)| ≤ p.maxSlew) :
    let res := stepSample p prevPos prevPace goal
    (goal - res.1, res.2 - 1)
      = next ((goal - 1) - prevPos, prevPace - 1)
          (law p.gain ((goal - 1) - prevPos, prevPace - 1)) (0, 0) := by
  intro res
  have hle := abs_le.mp hunclamped
  have hcl : clamp p.maxSlew ((prevPace - 1) + law p.gain ((goal - 1) - prevPos, prevPace - 1))
      = (prevPace - 1) + law p.gain ((goal - 1) - prevPos, prevPace - 1) := by
    unfold clamp
    rw [min_eq_right hle.2, max_eq_right hle.1]
  simp only [res, stepSample, hcl, next, Prod.mk.injEq]
  constructor <;> ring

def chooseSample (m : Memory H R) (first : ℕ) (stamp : ℝ)
    (prev : Option (ℕ × ℝ × ℝ)) (k : ℕ) : Option (ℝ × ℝ) :=
  match target p m first stamp k, prev with
  | some goal, some (j, pos, pace) =>
      if j + 1 = k then some (stepSample p pos pace goal) else some (goal, 1)
  | some goal, none => some (goal, 1)
  | none, _ => none

def decideBlock (m : Memory H R) (r : Fin R) (outputs : List ℕ) (stamp : ℝ) :
    List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ) :=
  outputs.foldl
    (fun (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ)) k =>
      match chooseSample p m (outputs.headD 0) stamp acc.2 k with
      | some (pos, pace) => (acc.1 ++ [(k, some pos)], some (k, pos, pace))
      | none => (acc.1 ++ [(k, none)], none))
    ([], m.reg r)

def answers (m : Memory H R) (i : H) (sent : ℝ) : Bool :=
  match m.answered i with
  | some a => decide (a < sent)
  | none => true

variable [DecidableEq H]

def asks (h : H) (m : Memory H R) (t : ℝ) : Bool :=
  h != p.sender && match m.asked with
    | some a => decide (a + p.period ≤ t)
    | none => true

def remember (h : H) (m : Memory H R) (e : Event H R Payload) : Memory H R :=
  match e.observation with
  | .handed frames stamp =>
      if h = p.sender then
        match frames.head? with
        | some (f, _) => { m with block := some (f, stamp, p.level), offset := some (0, 0) }
        | none => m
      else m
  | .received _ (.block f stamp lvl) _ =>
      if h = p.sender then m
      else
        match m.block with
        | some (f', _, _) =>
            if f' < f then { m with block := some (f, stamp, lvl) } else m
        | none => { m with block := some (f, stamp, lvl) }
  | .received i (.ask sent) _ =>
      if h = p.sender ∧ answers m i sent = true then
        { m with answered := Function.update m.answered i (some sent) }
      else m
  | .received _ (.answer sent received) _ =>
      if h = p.sender then m
      else
        let rtt := e.reading - sent
        let rawOff := received - (sent + e.reading) / 2
        let appended := m.rttWindow ++ [(sent, rtt, rawOff)]
        let trimmed := appended.drop (appended.length - max 1 p.windowSize)
        { m with rttWindow := trimmed, offset := minRttOffset trimmed }
  | .asked r outputs stamp =>
      let res := decideBlock p m r outputs stamp
      { m with
        reg := Function.update m.reg r res.2
        asked := if asks p h m e.reading then some e.reading else m.asked }
  | _ => m

def act (h : H) (m : Memory H R) (e : Event H R Payload) : Action H Payload :=
  match e.observation with
  | .handed frames stamp =>
      if h = p.sender then
        match frames.head? with
        | some (f, _) =>
            { sends := (p.speakers.filter (· ≠ p.sender)).flatMap fun j =>
                List.replicate p.copies
                  (j, Payload.block f stamp p.level, (frames.map Prod.fst).toFinset)
              timers := []
              plays := fun _ => none }
        | none => ⟨[], [], fun _ => none⟩
      else ⟨[], [], fun _ => none⟩
  | .received i (.ask sent) _ =>
      if h = p.sender ∧ answers m i sent = true then
        { sends := List.replicate p.copies (i, Payload.answer sent e.reading, ∅)
          timers := []
          plays := fun _ => none }
      else ⟨[], [], fun _ => none⟩
  | .asked r outputs stamp =>
      let res := decideBlock p m r outputs stamp
      { sends := if asks p h m e.reading then
          List.replicate p.copies (p.sender, Payload.ask e.reading, ∅) else []
        timers := []
        plays := fun k => (res.1.lookup k).join }
  | _ => ⟨[], [], fun _ => none⟩

/-- Concrete star `Unisono.Spec.Solution`. -/
def solution : Solution H R Payload := fun h view =>
  match view.getLast? with
  | some e => act p h (view.dropLast.foldl (remember p h) Memory.empty) e
  | none => ⟨[], [], fun _ => none⟩

theorem solution_append (h : H) (view : List (Event H R Payload)) (e : Event H R Payload) :
    solution p h (view ++ [e]) = act p h (view.foldl (remember p h) Memory.empty) e := by
  simp [solution]

/-- `StarProtocol.solution` obeys the star communication graph. -/
theorem isStar : (solution p : Solution H R Payload).IsStar p.sender := by
  intro h view dst msg frames hmem
  unfold solution at hmem
  cases hlast : view.getLast? with
  | none => simp [hlast] at hmem
  | some e =>
    simp only [hlast] at hmem
    unfold act at hmem
    cases hobs : e.observation with
    | handed frames' stamp =>
      simp only [hobs] at hmem
      split_ifs at hmem with hs
      · exact Or.inl hs
      · simp at hmem
    | received i payload _ =>
      cases payload with
      | block _ _ _ => simp [hobs] at hmem
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

def msgWeight : Payload → ℕ
  | .block _ _ _ => 1
  | .ask _ => 1 + p.copies
  | .answer _ _ => 1

omit [DecidableEq H] in
private theorem weight_copies (l : List H) (c : ℕ) (x : Payload × Finset ℕ)
    (hx : msgWeight p x.1 = 1) :
    ((l.flatMap fun j => List.replicate c (j, x)).map fun s => msgWeight p s.2.1).sum
      = c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_replicate,
      List.sum_replicate, hx, smul_eq_mul, mul_one, List.length_cons]
    ring

/-- **Non-Zeno progress of `StarProtocol.solution`.** In any bounded world, the
run advances past every true time `T`. -/
theorem progress (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (T : Time) :
    ∃ n, T < (solution p : Solution H R Payload).eventTime w lookahead n := by
  obtain ⟨-, hsrc, hspk, -, -, -, hlead, -, -, -, -⟩ := hw
  refine Solution.progress w (solution p) lookahead (msgWeight p)
    (p.copies * (p.speakers.filter (· ≠ p.sender)).length + 1) (p.copies * (1 + p.copies) + 1)
    ?_ ?_ ?_ ?_ (CaptureDevice.handed_unbounded w.rate_pos hsrc B.deviceRate_lt_one)
    (fun r => PlaybackDevice.asked_unbounded w.rate_pos (hspk r) B.deviceRate_lt_one (hlead r)) T
  · intro h view
    unfold solution act
    split
    · split <;> (try split) <;> (try split) <;> simp
    · rfl
  · intro h view frames rep reading
    rw [solution_append]
    simp only [act]
    split_ifs
    · split
      · rw [weight_copies p _ _ _ rfl]
      · simp
    · simp
  · intro h view r outs rep reading
    rw [solution_append]
    simp only [act]
    split_ifs <;> simp [msgWeight, List.sum_replicate]
  · intro h view i c F reading
    rw [solution_append]
    cases c with
    | block _ _ _ => simp [act, msgWeight]
    | ask sent =>
      simp only [act]
      split_ifs <;> simp [msgWeight, List.sum_replicate]
    | answer _ _ => simp [act, msgWeight]

/-- Every speaker block request is handled in every bounded world. -/
theorem request_step (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (r : Fin R) (b : ℕ) :
    ∃ n, ((solution p : Solution H R Payload).states w lookahead n).askedNext r = b ∧
      earliest (((solution p : Solution H R Payload).states w lookahead n).key w)
        ((solution p : Solution H R Payload).states w lookahead n).due = some (.asked r b) := by
  obtain ⟨m, hm⟩ := progress p w B hw lookahead ((w.speaker r).asked b)
  obtain ⟨n, -, h1, h2⟩ := Solution.exists_asked_step w (solution p) lookahead
    (Solution.lt_askedNext (solution p) w lookahead hm)
  exact ⟨n, h1, h2⟩

/-! ### Speed-bound verification (`WithinSpeed`) -/

omit [DecidableEq H] in
private theorem lookup_append_of_not_mem {α β : Type*} [BEq α] [LawfulBEq α]
    (l₁ l₂ : List (α × β)) (k : α) (hnot : ∀ x ∈ l₁, x.1 ≠ k) :
    (l₁ ++ l₂).lookup k = l₂.lookup k := by
  induction l₁ with
  | nil => rfl
  | cons a rest ih =>
    have hne : (k == a.1) = false := beq_eq_false_iff_ne.mpr (Ne.symm (hnot a (List.mem_cons_self ..)))
    simp only [List.cons_append, List.lookup, hne]
    exact ih fun x hx => hnot x (List.mem_cons_of_mem _ hx)

omit [DecidableEq H] in
private theorem lookup_append_of_mem {α β : Type*} [BEq α] [LawfulBEq α]
    (l₁ l₂ : List (α × β)) (k : α) (hmem : ∃ v, l₁.lookup k = some v) :
    (l₁ ++ l₂).lookup k = l₁.lookup k := by
  induction l₁ with
  | nil => simp at hmem
  | cons a rest ih =>
    cases h : (k == a.1) with
    | true => simp [List.lookup, h]
    | false =>
      simp only [List.cons_append, List.lookup, h] at hmem ⊢
      exact ih hmem

omit [DecidableEq H] in
private theorem decideFold_inv (m : Memory H R) (first : ℕ) (stamp : ℝ)
    (hslew : 0 ≤ p.maxSlew) :
    ∀ (outs : List ℕ) (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ)),
      (∀ pair ∈ acc.1, pair.1 ∉ outs) →
      outs.Nodup →
      let step := fun (a : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ)) (k : ℕ) =>
        match chooseSample p m first stamp a.2 k with
        | some (pos, pace) => (a.1 ++ [(k, some pos)], some (k, pos, pace))
        | none => (a.1 ++ [(k, none)], none)
      let res := outs.foldl step acc
      -- (1) Every pair already in `acc.1` has the same lookup in `res.1`.
      (∀ k, (∃ v, acc.1.lookup k = some v) → res.1.lookup k = acc.1.lookup k)
      -- (2) If `outs` starts with `a :: rest` and `acc.2 = some (j, x, pc)` with `j + 1 = a`,
      --     and `res.1.lookup a = some (some y)`, then `|y - x - 1| ≤ p.maxSlew`.
      ∧ (∀ a rest j x pc y, outs = a :: rest → acc.2 = some (j, x, pc) → j + 1 = a →
          (res.1.lookup a).join = some y → |y - x - 1| ≤ p.maxSlew)
      -- (3) For consecutive elements `k, k + 1` adjacent in `outs`, if both play `some x`, `some y`,
      --     then `|y - x - 1| ≤ p.maxSlew`.
      ∧ (∀ l₁ l₂ k x y, outs = l₁ ++ k :: (k + 1) :: l₂ →
          (res.1.lookup k).join = some x → (res.1.lookup (k + 1)).join = some y →
          |y - x - 1| ≤ p.maxSlew)
      -- (4) If `outs` ends with `k` and `(res.1.lookup k).join = some x`, then `res.2` is `some (k, x, _)`.
      ∧ (∀ l₁ k x, outs = l₁ ++ [k] → (res.1.lookup k).join = some x →
          ∃ pc, res.2 = some (k, x, pc)) := by
  intro outs
  induction outs with
  | nil =>
    intro acc _ _
    refine ⟨fun _ _ => rfl, fun _ _ _ _ _ _ h => by simp at h,
      fun l₁ _ _ _ _ h => by cases l₁ <;> simp at h,
      fun l₁ _ _ h => by cases l₁ <;> simp at h⟩
  | cons a rest ih =>
    intro acc hdisj hnodup
    rw [List.nodup_cons] at hnodup
    obtain ⟨ha_not, hnodup_rest⟩ := hnodup
    set step := fun (ac : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ)) (k : ℕ) =>
      match chooseSample p m first stamp ac.2 k with
      | some (pos, pace) => (ac.1 ++ [(k, some pos)], some (k, pos, pace))
      | none => (ac.1 ++ [(k, none)], none)
    set acc1 := step acc a
    have hdisj1 : ∀ pair ∈ acc1.1, pair.1 ∉ rest := by
      intro pair hpair hmem
      have h1 : pair ∈ acc.1 ∨ pair.1 = a := by
        dsimp only [acc1, step] at hpair
        cases hch : chooseSample p m first stamp acc.2 a with
        | none =>
          rw [hch] at hpair; simp only [List.mem_append, List.mem_singleton] at hpair
          rcases hpair with h | rfl; exact Or.inl h; exact Or.inr rfl
        | some v =>
          rw [hch] at hpair; simp only [List.mem_append, List.mem_singleton] at hpair
          rcases hpair with h | rfl; exact Or.inl h; exact Or.inr rfl
      rcases h1 with h | heq
      · exact hdisj pair h (List.mem_cons_of_mem _ hmem)
      · exact ha_not (heq ▸ hmem)
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih acc1 hdisj1 hnodup_rest
    have hacc1_pres : ∀ k, (∃ v, acc.1.lookup k = some v) → acc1.1.lookup k = acc.1.lookup k := by
      intro k hk
      dsimp only [acc1, step]
      cases chooseSample p m first stamp acc.2 a with
      | none => exact lookup_append_of_mem _ _ k hk
      | some v => exact lookup_append_of_mem _ _ k hk
    have ha_not_acc : ∀ pair ∈ acc.1, pair.1 ≠ a := fun pair hp heq =>
      hdisj pair hp (heq ▸ List.mem_cons_self ..)
    have hacc1_a : acc1.1.lookup a = some ((chooseSample p m first stamp acc.2 a).map Prod.fst) := by
      dsimp only [acc1, step]
      cases hch : chooseSample p m first stamp acc.2 a with
      | none =>
        rw [lookup_append_of_not_mem _ _ a ha_not_acc]
        simp
      | some v =>
        rw [lookup_append_of_not_mem _ _ a ha_not_acc]
        simp
    have hres_a : (rest.foldl step acc1).1.lookup a
        = some ((chooseSample p m first stamp acc.2 a).map Prod.fst) := by
      rw [ih1 a ⟨_, hacc1_a⟩, hacc1_a]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      change (rest.foldl step acc1).1.lookup k = acc.1.lookup k
      rw [ih1 k ⟨_, by rw [hacc1_pres k hk]; exact hk.choose_spec⟩, hacc1_pres k hk]
    · intro a' rest' j x pc y heq hacc2 hj hlu
      injection heq with ha' hrest'; subst ha'; subst hrest'
      change ((rest.foldl step acc1).1.lookup a).join = some y at hlu
      rw [hres_a] at hlu
      simp only [Option.join_some] at hlu
      unfold chooseSample at hlu
      rw [hacc2] at hlu
      cases htg : target p m first stamp a with
      | none => simp [htg] at hlu
      | some goal =>
        simp only [htg, hj, ↓reduceIte, Option.map_some, Option.some.injEq] at hlu
        unfold stepSample at hlu
        have hcl := clamp_mem hslew (x := (pc - 1) + law p.gain ((goal - 1) - x, pc - 1))
        rw [abs_le]
        constructor <;> linarith
    · intro l₁ l₂ k x y heq hkx hky
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        obtain ⟨ha_eq, hrest_eq⟩ := heq
        subst ha_eq
        change ((rest.foldl step acc1).1.lookup a).join = some x at hkx
        rw [hres_a] at hkx
        simp only [Option.join_some] at hkx
        cases hch : chooseSample p m first stamp acc.2 a with
        | none => simp [hch] at hkx
        | some v =>
          rcases v with ⟨pos, pc⟩
          rw [hch] at hkx
          simp only [Option.map_some, Option.some.injEq] at hkx
          subst hkx
          have hacc1_2 : acc1.2 = some (a, pos, pc) := by
            dsimp only [acc1, step]; rw [hch]
          exact ih2 (a + 1) l₂ a pos pc y hrest_eq hacc1_2 rfl hky
      | cons b l₁' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨_, hrest_eq⟩ := heq
        exact ih3 l₁' l₂ k x y hrest_eq hkx hky
    · intro l₁ k x heq hkx
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        obtain ⟨ha_eq, hrest_eq⟩ := heq
        subst ha_eq; subst hrest_eq
        change (acc1.1.lookup a).join = some x at hkx
        rw [hacc1_a] at hkx
        simp only [Option.join_some] at hkx
        cases hch : chooseSample p m first stamp acc.2 a with
        | none => simp [hch] at hkx
        | some v =>
          rcases v with ⟨pos, pc⟩
          rw [hch] at hkx
          simp only [Option.map_some, Option.some.injEq] at hkx
          subst hkx
          refine ⟨pc, ?_⟩
          change acc1.2 = some (a, pos, pc)
          dsimp only [acc1, step]; rw [hch]
      | cons b l₁' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨_, hrest_eq⟩ := heq
        exact ih4 l₁' k x hrest_eq hkx

private theorem reg_after_request (h : H) (r : Fin R) (m : Memory H R) (l : List (Event H R Payload))
    (hno : ∀ e ∈ l, ∀ outs st, e.observation ≠ .asked r outs st) :
    (l.foldl (remember p h) m).reg r = m.reg r := by
  induction l generalizing m with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.foldl_cons]
    have hstep : (remember p h m e).reg r = m.reg r := by
      rcases e with ⟨reading, obs⟩
      cases obs with
      | handed frames stamp =>
        simp only [remember]
        split_ifs
        · cases frames.head? <;> rfl
        · rfl
      | received i payload F =>
        cases payload with
        | block f st lvl =>
          simp only [remember]
          split_ifs
          · rfl
          · cases m.block with
            | none => rfl
            | some b => dsimp only; split_ifs <;> rfl
        | ask sent => simp only [remember]; split_ifs <;> rfl
        | answer sent rec => simp only [remember]; split_ifs <;> rfl
      | asked r' outs st =>
        have hne : r' ≠ r := fun heq => hno ⟨reading, .asked r' outs st⟩ (List.mem_cons_self ..) outs st (by rw [heq])
        simp [remember, Function.update_of_ne (Ne.symm hne)]
      | timer => rfl
    rw [ih (remember p h m e) (fun e' he' => hno e' (List.mem_cons_of_mem _ he')), hstep]

/-- **Speed-bound guarantee (`Solution.WithinSpeed`) for `StarProtocol.solution`.**
In any bounded world `w.WithinBounds B`, whenever `0 ≤ p.maxSlew < 1`, every
continuous playback step of `StarProtocol.solution` stays within
`(2 * B.deviceRate + (1 + B.deviceRate) * p.maxSlew) / (1 - B.deviceRate)` of
unit speed. -/
theorem withinSpeed (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hs0 : 0 ≤ p.maxSlew) (hs1 : p.maxSlew < 1) :
    (solution p : Solution H R Payload).WithinSpeed w lookahead
      ((2 * B.deviceRate + (1 + B.deviceRate) * p.maxSlew) / (1 - B.deviceRate)) := by
  refine withinSpeed_of_step_bound (solution p) w B hw lookahead hs0 hs1 fun r k x y hx hy => ?_
  obtain ⟨b₁, n₁, hk1, hnb1, hne1, hp1⟩ := exists_asked_of_plays_some (solution p) w lookahead hx
  obtain ⟨b₂, n₂, hk2, hnb2, hne2, hp2⟩ := exists_asked_of_plays_some (solution p) w lookahead hy
  have hmem_iff : ∀ b j, j ∈ (w.speaker r).block b ↔
      (w.speaker r).first b ≤ j ∧ j < (w.speaker r).first (b + 1) := by
    intro b j
    unfold PlaybackDevice.block
    rw [List.mem_range'_1]
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self b)
    omega
  have hb1_bounds := (hmem_iff b₁ k).mp hk1
  have hb2_bounds := (hmem_iff b₂ (k + 1)).mp hk2
  have hnodup : ∀ b, ((w.speaker r).block b).Nodup := fun b => by
    unfold PlaybackDevice.block; exact List.nodup_range'
  rw [solution_append] at hp1 hp2
  dsimp only [act] at hp1 hp2
  set m₁ := ((solution p : Solution H R Payload).states w lookahead n₁).views (w.host r) |>.foldl
    (remember p (w.host r)) Memory.empty
  set m₂ := ((solution p : Solution H R Payload).states w lookahead n₂).views (w.host r) |>.foldl
    (remember p (w.host r)) Memory.empty
  by_cases hsame : b₁ = b₂
  · subst hsame
    have hn_eq : n₁ = n₂ := by
      rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
      · exfalso
        have hsucc := (solution p : Solution H R Payload).askedNext_succ w lookahead (hnb1 ▸ hne1)
        have hmono := (solution p : Solution H R Payload).askedNext_mono w lookahead r (Nat.succ_le_of_lt hlt)
        change ((solution p : Solution H R Payload).states w lookahead (n₁ + 1)).askedNext r
          = ((solution p : Solution H R Payload).states w lookahead n₁).askedNext r + 1 at hsucc
        change ((solution p : Solution H R Payload).states w lookahead (n₁ + 1)).askedNext r
          ≤ ((solution p : Solution H R Payload).states w lookahead n₂).askedNext r at hmono
        omega
      · exact heq
      · exfalso
        have hsucc := (solution p : Solution H R Payload).askedNext_succ w lookahead (hnb2 ▸ hne2)
        have hmono := (solution p : Solution H R Payload).askedNext_mono w lookahead r (Nat.succ_le_of_lt hgt)
        change ((solution p : Solution H R Payload).states w lookahead (n₂ + 1)).askedNext r
          = ((solution p : Solution H R Payload).states w lookahead n₂).askedNext r + 1 at hsucc
        change ((solution p : Solution H R Payload).states w lookahead (n₂ + 1)).askedNext r
          ≤ ((solution p : Solution H R Payload).states w lookahead n₁).askedNext r at hmono
        omega
    subst hn_eq
    have hsplit : ∃ l₁ l₂, (w.speaker r).block b₁ = l₁ ++ k :: (k + 1) :: l₂ := by
      unfold PlaybackDevice.block
      set a := (w.speaker r).first b₁
      set c := (w.speaker r).first (b₁ + 1)
      refine ⟨List.range' a (k - a), List.range' (k + 2) (c - (k + 2)), ?_⟩
      have hlen : c - a = (k - a) + (2 + (c - (k + 2))) := by omega
      have ha1 : a + (k - a) = k := by omega
      calc List.range' a (c - a)
          = List.range' a ((k - a) + (2 + (c - (k + 2)))) := by rw [hlen]
        _ = List.range' a (k - a) ++ List.range' (a + (k - a)) (2 + (c - (k + 2))) := by simp
        _ = List.range' a (k - a) ++ k :: (k + 1) :: List.range' (k + 2) (c - (k + 2)) := by
            rw [ha1, show 2 + (c - (k + 2)) = ((c - (k + 2)) + 1) + 1 by omega]
            simp only [List.range'_succ, Nat.add_assoc]
    obtain ⟨l₁, l₂, hsplit⟩ := hsplit
    exact (decideFold_inv p m₁ (((w.speaker r).block b₁).headD 0) ((w.speaker r).reported b₁) hs0
      ((w.speaker r).block b₁) ([], m₁.reg r) (by simp) (hnodup b₁)).2.2.1 l₁ l₂ k x y hsplit hp1 hp2
  · -- `k` is the last sample of `b₁` and `k + 1` is the first sample of `b₂ = b₁ + 1`.
    have hb2_eq : b₂ = b₁ + 1 := by
      have hlt : b₁ < b₂ := by
        by_contra hge; push Not at hge
        have hle' : (w.speaker r).first (b₂ + 1) ≤ (w.speaker r).first b₁ :=
          (w.speaker r).first_strictMono.monotone (by omega)
        omega
      by_contra hne
      have hge : b₁ + 1 < b₂ := by omega
      have hlt' := (w.speaker r).first_strictMono hge
      omega
    subst hb2_eq
    have hk_end : k + 1 = (w.speaker r).first (b₁ + 1) := by omega
    have hsplit1 : ∃ l₁, (w.speaker r).block b₁ = l₁ ++ [k] := by
      unfold PlaybackDevice.block
      set a := (w.speaker r).first b₁
      refine ⟨List.range' a (k - a), ?_⟩
      have hlen : (w.speaker r).first (b₁ + 1) - a = (k - a) + 1 := by omega
      have ha1 : a + (k - a) = k := by omega
      calc List.range' a ((w.speaker r).first (b₁ + 1) - a)
          = List.range' a ((k - a) + 1) := by rw [hlen]
        _ = List.range' a (k - a) ++ [a + (k - a)] := by simp [List.range'_concat]
        _ = List.range' a (k - a) ++ [k] := by rw [ha1]
    obtain ⟨l₁, hsplit1⟩ := hsplit1
    have hsplit2 : ∃ rest, (w.speaker r).block (b₁ + 1) = (k + 1) :: rest := by
      unfold PlaybackDevice.block
      have hpos := (w.speaker r).first_strictMono (Nat.lt_succ_self (b₁ + 1))
      refine ⟨List.range' (k + 2) ((w.speaker r).first (b₁ + 2) - (k + 2)), ?_⟩
      have hlen : (w.speaker r).first (b₁ + 2) - (w.speaker r).first (b₁ + 1)
          = ((w.speaker r).first (b₁ + 2) - (k + 2)) + 1 := by
        have : (w.speaker r).first (b₁ + 1) < (w.speaker r).first (b₁ + 2) := hpos
        omega
      rw [hlen, ← hk_end]
      simp [List.range'_succ]
    obtain ⟨rest, hsplit2⟩ := hsplit2
    obtain ⟨pc, hres1⟩ :=
      (decideFold_inv p m₁ (((w.speaker r).block b₁).headD 0) ((w.speaker r).reported b₁) hs0
        ((w.speaker r).block b₁) ([], m₁.reg r) (by simp) (hnodup b₁)).2.2.2 l₁ k x hsplit1 hp1
    have hn_lt : n₁ < n₂ := by
      by_contra hge; push Not at hge
      have hmono := (solution p : Solution H R Payload).askedNext_mono w lookahead r hge
      simp only at hmono; omega
    -- Show `m₂.reg r = some (k, x, pc)` via `no_request_between`.
    have hsucc := (solution p : Solution H R Payload).askedNext_succ w lookahead (hnb1 ▸ hne1)
    rw [hnb1] at hsucc
    have hv1 : ((solution p : Solution H R Payload).states w lookahead (n₁ + 1)).views (w.host r)
        = ((solution p : Solution H R Payload).states w lookahead n₁).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b₁),
            .asked r ((w.speaker r).block b₁) ((w.speaker r).reported b₁)⟩] := by
      rw [(solution p : Solution H R Payload).views_succ w lookahead n₁ (w.host r),
        (solution p : Solution H R Payload).handled_of_asked w lookahead hne1]
      simp
    obtain ⟨l, hl, hev⟩ :=
      (solution p : Solution H R Payload).views_append w lookahead (Nat.succ_le_of_lt hn_lt) (w.host r)
    have hm2_reg : m₂.reg r = some (k, x, pc) := by
      dsimp only [m₂]
      rw [hl, hv1, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [reg_after_request p (w.host r) r _ l]
      · simp only [remember, Function.update_self]
        exact hres1
      · intro e he outs st heo
        obtain ⟨i, hi1, hi2, t, obs, hhi, rfl⟩ := hev e he
        simp only at heo; subst heo
        exact (solution p : Solution H R Payload).no_request_between w lookahead
          (hsucc.trans hnb2.symm) hi1 hi2 hhi
    exact (decideFold_inv p m₂ (((w.speaker r).block (b₁ + 1)).headD 0)
      ((w.speaker r).reported (b₁ + 1)) hs0 ((w.speaker r).block (b₁ + 1)) ([], m₂.reg r)
      (by simp) (hnodup (b₁ + 1))).2.1 (k + 1) rest k x pc y hsplit2 hm2_reg rfl hp2

end StarProtocol

/-! ## 3. Concrete Peer / Receiver–Receiver protocol (`PeerProtocol`) -/

namespace PeerProtocol

variable {H : Type} {R : ℕ}

/-- Message payload for the concrete peer (receiver–receiver) protocol. -/
inductive Payload (H : Type) where
  /-- Stream block from the sender. -/
  | block (first : ℕ) (stamp : ℝ) (level : ℝ)
  /-- Pairwise clock probe to either the sender or a direct receiver peer. -/
  | ask (sent : ℝ)
  /-- Reply to a pairwise clock probe. -/
  | answer (sent : ℝ) (received : ℝ)
  /-- Peer state message carrying the peer's latest direct sender-offset
  estimate (for one-hop triangulation), its latest lag `dev`, and its latest
  excess pace `pace`. -/
  | peerState (senderEst : Option ℝ) (dev : ℝ) (pace : ℝ)

/-- Parameters of the concrete peer protocol. -/
structure Params (H : Type) where
  sender : H
  speakers : List H
  /-- Direct peer neighbors of each host `h` (excluding `h` itself). -/
  peers : H → List H
  rate : ℝ
  level : ℝ
  copies : ℕ
  period : ℝ
  /-- Common-mode gain (`gCom > 0` holds target latency; `0` fixes mean pace). -/
  gCom : ℝ
  /-- Differential-mode gain (`gDiff ∈ (0, 1)`). -/
  gDiff : ℝ
  maxSlew : ℝ

/-- Per-host state reconstructed from a host's event view. -/
structure Memory (H : Type) (R : ℕ) where
  block : Option (ℕ × ℝ × ℝ)
  /-- Latest pairwise clock offset estimate `clock(neighbor) - clock(self)` per
  neighbor `j`. -/
  peerOffset : H → Option (ℝ × ℝ)
  /-- Latest received `(senderEst, dev, excessPace)` from each peer `j`. -/
  peerInfo : H → Option (Option ℝ × ℝ × ℝ)
  asked : Option ℝ
  answered : H → Option ℝ
  /-- Per-speaker regulator state `(lastSample, position, pace, lastLag)`. -/
  reg : Fin R → Option (ℕ × ℝ × ℝ × ℝ)

def Memory.empty : Memory H R where
  block := none
  peerOffset := fun _ => none
  peerInfo := fun _ => none
  asked := none
  answered := fun _ => none
  reg := fun _ => none

def clamp (w x : ℝ) : ℝ := max (-w) (min w x)

theorem clamp_mem {w x : ℝ} (hw : 0 ≤ w) : -w ≤ clamp w x ∧ clamp w x ≤ w := by
  unfold clamp
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

variable (p : Params H)

/-- Estimate of sender offset combining the direct sender probe (when present)
and all available one-hop peer paths `peerOffset j + peerSenderEst j` over
configured peers `j ∈ p.peers h` via equal-weight averaging. -/
def senderOffset (h : H) (m : Memory H R) : Option ℝ :=
  let direct : List ℝ := match m.peerOffset p.sender with
    | some (_, off) => [off]
    | none => []
  let viaPeers : List ℝ := (p.peers h).filterMap fun j =>
    match m.peerOffset j, m.peerInfo j with
    | some (_, offPeer), some (some offPeerSender, _, _) => some (offPeer + offPeerSender)
    | _, _ => none
  let all := direct ++ viaPeers
  match all with
  | [] => none
  | _ :: _ => some (all.sum / (all.length : ℝ))

def target (h : H) (m : Memory H R) (first : ℕ) (stamp : ℝ) (k : ℕ) : Option ℝ :=
  match m.block, senderOffset p h m with
  | some (f, captured, lvl), some off =>
      some (f + ((stamp + ((k : ℝ) - first) / p.rate + off - lvl) - captured) * p.rate)
  | _, _ => none

/-- Two-mode sample advance on exact lag `err = (goal - 1) - prevPos` and
excess pace `v = prevPace - 1`. Separates both lag and excess pace into
estimated common mode `(meanErr, meanPace)` and differential mode
`(diffErr, diffPace)` across reporting peers (so `meanPace + diffPace = v`,
never double-damping `v`), clamped to `[1 - maxSlew, 1 + maxSlew]`. -/
def stepSample (p : Params H) (h : H) (m : Memory H R) (prevPos prevPace goal : ℝ) : ℝ × ℝ × ℝ :=
  let err := (goal - 1) - prevPos
  let v := prevPace - 1
  let reported := (p.peers h).filterMap fun j =>
    match m.peerInfo j with
    | some (_, dev, pc) => some (dev, pc)
    | none => none
  let nCount : ℝ := (reported.length : ℝ) + 1
  let meanErr := (err + (reported.map Prod.fst).sum) / nCount
  let meanPace := (v + (reported.map Prod.snd).sum) / nCount
  let diffErr := err - meanErr
  let diffPace := v - meanPace
  let deltaCom := if p.gCom = 0 then 0 else law p.gCom (meanErr, meanPace)
  let deltaDiff := law p.gDiff (diffErr, diffPace)
  let newPace := 1 + clamp p.maxSlew (v + deltaCom + deltaDiff)
  (prevPos + newPace, newPace, err)

theorem stepSample_step_bound (p : Params H) (h : H) (m : Memory H R)
    (prevPos prevPace goal : ℝ) (hslew : 0 ≤ p.maxSlew) :
    |(stepSample p h m prevPos prevPace goal).1 - prevPos - 1| ≤ p.maxSlew := by
  unfold stepSample
  dsimp only
  rw [show prevPos + (1 + clamp p.maxSlew _) - prevPos - 1 = clamp p.maxSlew _ by ring]
  exact abs_le.mpr (clamp_mem hslew)

def chooseSample (h : H) (m : Memory H R) (first : ℕ) (stamp : ℝ)
    (prev : Option (ℕ × ℝ × ℝ × ℝ)) (k : ℕ) : Option (ℝ × ℝ × ℝ) :=
  match target p h m first stamp k, prev with
  | some goal, some (j, pos, pace, _) =>
      if j + 1 = k then some (stepSample p h m pos pace goal) else some (goal, 1, 0)
  | some goal, none => some (goal, 1, 0)
  | none, _ => none

def decideBlock (h : H) (m : Memory H R) (r : Fin R) (outputs : List ℕ) (stamp : ℝ) :
    List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ × ℝ) :=
  outputs.foldl
    (fun (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ × ℝ)) k =>
      match chooseSample p h m (outputs.headD 0) stamp acc.2 k with
      | some (pos, pace, lag) => (acc.1 ++ [(k, some pos)], some (k, pos, pace, lag))
      | none => (acc.1 ++ [(k, none)], none))
    ([], m.reg r)

def answers (m : Memory H R) (i : H) (sent : ℝ) : Bool :=
  match m.answered i with
  | some a => decide (a < sent)
  | none => true

variable [DecidableEq H]

def asks (h : H) (m : Memory H R) (t : ℝ) : Bool :=
  h != p.sender && match m.asked with
    | some a => decide (a + p.period ≤ t)
    | none => true

/-- Peer-only targets (excluding self and the sender). -/
def peerTargets (h : H) : List H :=
  (p.peers h).filter (fun j => j ≠ p.sender ∧ j ≠ h)

/-- Query targets for a non-sender host: the sender plus all configured direct
peers (excluding itself and the sender). -/
def probeTargets (h : H) : List H :=
  p.sender :: peerTargets p h

def remember (h : H) (m : Memory H R) (e : Event H R (Payload H)) : Memory H R :=
  match e.observation with
  | .handed frames stamp =>
      if h = p.sender then
        match frames.head? with
        | some (f, _) =>
            { m with
              block := some (f, stamp, p.level)
              peerOffset := Function.update m.peerOffset p.sender (some (0, 0)) }
        | none => m
      else m
  | .received _ (.block f stamp lvl) _ =>
      if h = p.sender then m
      else
        match m.block with
        | some (f', _, _) => if f' < f then { m with block := some (f, stamp, lvl) } else m
        | none => { m with block := some (f, stamp, lvl) }
  | .received i (.ask sent) _ =>
      if answers m i sent = true ∧ (h = p.sender ∨ i ∈ p.peers h ∨ h ∈ p.peers i) then
        { m with answered := Function.update m.answered i (some sent) }
      else m
  | .received i (.answer sent received) _ =>
      let est := (sent, received - (sent + e.reading) / 2)
      match m.peerOffset i with
      | some (prevSent, _) =>
          if prevSent < sent then
            { m with peerOffset := Function.update m.peerOffset i (some est) }
          else m
      | none => { m with peerOffset := Function.update m.peerOffset i (some est) }
  | .received i (.peerState sEst dev pc) _ =>
      { m with peerInfo := Function.update m.peerInfo i (some (sEst, dev, pc)) }
  | .asked r outputs stamp =>
      let res := decideBlock p h m r outputs stamp
      { m with
        reg := Function.update m.reg r res.2
        asked := if asks p h m e.reading then some e.reading else m.asked }
  | _ => m

def act (h : H) (m : Memory H R) (e : Event H R (Payload H)) : Action H (Payload H) :=
  match e.observation with
  | .handed frames stamp =>
      if h = p.sender then
        match frames.head? with
        | some (f, _) =>
            { sends := (p.speakers.filter (· ≠ p.sender)).flatMap fun j =>
                List.replicate p.copies
                  (j, Payload.block f stamp p.level, (frames.map Prod.fst).toFinset)
              timers := []
              plays := fun _ => none }
        | none => ⟨[], [], fun _ => none⟩
      else ⟨[], [], fun _ => none⟩
  | .received i (.ask sent) _ =>
      if answers m i sent = true ∧ (h = p.sender ∨ i ∈ p.peers h ∨ h ∈ p.peers i) then
        { sends := List.replicate p.copies (i, Payload.answer sent e.reading, ∅)
          timers := []
          plays := fun _ => none }
      else ⟨[], [], fun _ => none⟩
  | .asked r outputs stamp =>
      let res := decideBlock p h m r outputs stamp
      let curState : ℝ × ℝ := match res.2 with
        | some (_, _, pace, lag) => (lag, pace - 1)
        | none => (0, 0)
      let probes :=
        if asks p h m e.reading then
          ((probeTargets p h).flatMap fun j =>
            List.replicate p.copies (j, Payload.ask e.reading, ∅))
          ++ ((peerTargets p h).flatMap fun j =>
            List.replicate p.copies
              (j, Payload.peerState ((m.peerOffset p.sender).map Prod.snd) curState.1 curState.2, ∅))
        else []
      { sends := probes
        timers := []
        plays := fun k => (res.1.lookup k).join }
  | _ => ⟨[], [], fun _ => none⟩

/-- Concrete peer `Unisono.Spec.Solution`. -/
def solution : Solution H R (Payload H) := fun h view =>
  match view.getLast? with
  | some e => act p h (view.dropLast.foldl (remember p h) Memory.empty) e
  | none => ⟨[], [], fun _ => none⟩

theorem solution_append (h : H) (view : List (Event H R (Payload H)))
    (e : Event H R (Payload H)) :
    solution p h (view ++ [e]) = act p h (view.foldl (remember p h) Memory.empty) e := by
  simp [solution]

/-- `PeerProtocol.solution` uses only star edges and configured undirected peer
edges `dst ∈ p.peers h ∨ h ∈ p.peers dst`. -/
theorem usesGraph :
    (solution p : Solution H R (Payload H)).UsesGraph
      (fun h dst => h = p.sender ∨ dst = p.sender ∨ dst ∈ p.peers h ∨ h ∈ p.peers dst) := by
  intro h view dst msg frames hmem
  unfold solution at hmem
  cases hlast : view.getLast? with
  | none => simp [hlast] at hmem
  | some e =>
    simp only [hlast] at hmem
    unfold act at hmem
    cases hobs : e.observation with
    | handed frames' stamp =>
      simp only [hobs] at hmem
      split_ifs at hmem with hs
      · exact Or.inl hs
      · simp at hmem
    | received i payload _ =>
      cases payload with
      | block _ _ _ => simp [hobs] at hmem
      | ask sent =>
        simp only [hobs] at hmem
        split_ifs at hmem with ha
        · rw [List.mem_replicate] at hmem
          have hdst : dst = i := congrArg Prod.fst hmem.2
          subst hdst
          rcases ha.2 with hs | hp | hp
          · exact Or.inl hs
          · exact Or.inr (Or.inr (Or.inl hp))
          · exact Or.inr (Or.inr (Or.inr hp))
        · simp at hmem
      | answer _ _ => simp [hobs] at hmem
      | peerState _ _ _ => simp [hobs] at hmem
    | asked r outputs stamp =>
      simp only [hobs] at hmem
      split_ifs at hmem with ha
      · rw [List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · rw [List.mem_flatMap] at hmem
          obtain ⟨j, hj, hrep⟩ := hmem
          rw [List.mem_replicate] at hrep
          have hdst : dst = j := congrArg Prod.fst hrep.2
          subst hdst
          simp only [probeTargets, peerTargets, List.mem_cons, List.mem_filter,
            decide_eq_true_eq] at hj
          rcases hj with rfl | ⟨hpeer, _⟩
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl hpeer))
        · rw [List.mem_flatMap] at hmem
          obtain ⟨j, hj, hrep⟩ := hmem
          rw [List.mem_replicate] at hrep
          have hdst : dst = j := congrArg Prod.fst hrep.2
          subst hdst
          simp only [peerTargets, List.mem_filter, decide_eq_true_eq] at hj
          exact Or.inr (Or.inr (Or.inl hj.1))
      · simp at hmem
    | timer => simp [hobs] at hmem

def msgWeight : Payload H → ℕ
  | .block _ _ _ => 1
  | .ask _ => 1 + p.copies
  | .answer _ _ => 1
  | .peerState _ _ _ => 1

omit [DecidableEq H] in
private theorem weight_flatMap (l : List H) (c : ℕ) (w : ℕ) (x : Payload H × Finset ℕ)
    (hx : msgWeight p x.1 = w) :
    ((l.flatMap fun j => List.replicate c (j, x)).map fun s => msgWeight p s.2.1).sum
      = c * w * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_replicate,
      List.sum_replicate, hx, smul_eq_mul, List.length_cons]
    ring

/-- **Non-Zeno progress of `PeerProtocol.solution`.** Requires an explicit
bound `maxPeers` on each host's peer list (`∀ h, (p.peers h).length ≤ maxPeers`).
Then in every bounded world the run advances past every true time `T`. -/
theorem progress (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (maxPeers : ℕ) (hmax : ∀ h : H, (p.peers h).length ≤ maxPeers) (T : Time) :
    ∃ n, T < (solution p : Solution H R (Payload H)).eventTime w lookahead n := by
  obtain ⟨-, hsrc, hspk, -, -, -, hlead, -, -, -, -⟩ := hw
  refine Solution.progress w (solution p) lookahead (msgWeight p)
    (p.copies * (p.speakers.filter (· ≠ p.sender)).length + 1)
    (p.copies * (1 + p.copies) * (1 + maxPeers) + p.copies * maxPeers + 1)
    ?_ ?_ ?_ ?_ (CaptureDevice.handed_unbounded w.rate_pos hsrc B.deviceRate_lt_one)
    (fun r => PlaybackDevice.asked_unbounded w.rate_pos (hspk r) B.deviceRate_lt_one (hlead r)) T
  · intro h view
    unfold solution act
    split
    · split <;> (try split) <;> (try split) <;> simp
    · rfl
  · intro h view frames rep reading
    rw [solution_append]
    simp only [act]
    split_ifs
    · split
      · rw [weight_flatMap p _ _ 1 _ rfl, mul_one]
      · simp
    · simp
  · intro h view r outs rep reading
    rw [solution_append]
    simp only [act]
    split_ifs
    · rw [List.map_append, List.sum_append,
        weight_flatMap p _ _ (1 + p.copies) _ rfl,
        weight_flatMap p _ _ 1 _ rfl, mul_one]
      have hlenP : (peerTargets p h).length ≤ maxPeers :=
        le_trans (List.length_filter_le _ _) (hmax h)
      have hlenPr : (probeTargets p h).length ≤ 1 + maxPeers := by
        simp only [probeTargets, List.length_cons]; omega
      have h1 : p.copies * (1 + p.copies) * (probeTargets p h).length
          ≤ p.copies * (1 + p.copies) * (1 + maxPeers) := Nat.mul_le_mul_left _ hlenPr
      have h2 : p.copies * (peerTargets p h).length ≤ p.copies * maxPeers :=
        Nat.mul_le_mul_left _ hlenP
      omega
    · simp
  · intro h view i c F reading
    rw [solution_append]
    cases c with
    | block _ _ _ => simp [act, msgWeight]
    | ask sent =>
      simp only [act]
      split_ifs <;> simp [msgWeight, List.sum_replicate]
    | answer _ _ => simp [act, msgWeight]
    | peerState _ _ _ => simp [act, msgWeight]

/-- Every speaker block request is handled in every bounded world. -/
theorem request_step (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (maxPeers : ℕ) (hmax : ∀ h : H, (p.peers h).length ≤ maxPeers) (r : Fin R) (b : ℕ) :
    ∃ n, ((solution p : Solution H R (Payload H)).states w lookahead n).askedNext r = b ∧
      earliest (((solution p : Solution H R (Payload H)).states w lookahead n).key w)
        ((solution p : Solution H R (Payload H)).states w lookahead n).due = some (.asked r b) := by
  obtain ⟨m, hm⟩ := progress p w B hw lookahead maxPeers hmax ((w.speaker r).asked b)
  obtain ⟨n, -, h1, h2⟩ := Solution.exists_asked_step w (solution p) lookahead
    (Solution.lt_askedNext (solution p) w lookahead hm)
  exact ⟨n, h1, h2⟩

/-! ### Speed-bound verification (`WithinSpeed`) -/

omit [DecidableEq H] in
private theorem lookup_append_of_not_mem {α β : Type*} [BEq α] [LawfulBEq α]
    (l₁ l₂ : List (α × β)) (k : α) (hnot : ∀ x ∈ l₁, x.1 ≠ k) :
    (l₁ ++ l₂).lookup k = l₂.lookup k := by
  induction l₁ with
  | nil => rfl
  | cons a rest ih =>
    have hne : (k == a.1) = false := beq_eq_false_iff_ne.mpr (Ne.symm (hnot a (List.mem_cons_self ..)))
    simp only [List.cons_append, List.lookup, hne]
    exact ih fun x hx => hnot x (List.mem_cons_of_mem _ hx)

omit [DecidableEq H] in
private theorem lookup_append_of_mem {α β : Type*} [BEq α] [LawfulBEq α]
    (l₁ l₂ : List (α × β)) (k : α) (hmem : ∃ v, l₁.lookup k = some v) :
    (l₁ ++ l₂).lookup k = l₁.lookup k := by
  induction l₁ with
  | nil => simp at hmem
  | cons a rest ih =>
    cases h : (k == a.1) with
    | true => simp [List.lookup, h]
    | false =>
      simp only [List.cons_append, List.lookup, h] at hmem ⊢
      exact ih hmem

omit [DecidableEq H] in
private theorem decideFold_inv (h : H) (m : Memory H R) (first : ℕ) (stamp : ℝ)
    (hslew : 0 ≤ p.maxSlew) :
    ∀ (outs : List ℕ) (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ × ℝ)),
      (∀ pair ∈ acc.1, pair.1 ∉ outs) →
      outs.Nodup →
      let step := fun (a : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ × ℝ)) (k : ℕ) =>
        match chooseSample p h m first stamp a.2 k with
        | some (pos, pace, lag) => (a.1 ++ [(k, some pos)], some (k, pos, pace, lag))
        | none => (a.1 ++ [(k, none)], none)
      let res := outs.foldl step acc
      (∀ k, (∃ v, acc.1.lookup k = some v) → res.1.lookup k = acc.1.lookup k)
      ∧ (∀ a rest j x pc lg y, outs = a :: rest → acc.2 = some (j, x, pc, lg) → j + 1 = a →
          (res.1.lookup a).join = some y → |y - x - 1| ≤ p.maxSlew)
      ∧ (∀ l₁ l₂ k x y, outs = l₁ ++ k :: (k + 1) :: l₂ →
          (res.1.lookup k).join = some x → (res.1.lookup (k + 1)).join = some y →
          |y - x - 1| ≤ p.maxSlew)
      ∧ (∀ l₁ k x, outs = l₁ ++ [k] → (res.1.lookup k).join = some x →
          ∃ pc lg, res.2 = some (k, x, pc, lg)) := by
  intro outs
  induction outs with
  | nil =>
    intro acc _ _
    refine ⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ h' => by simp at h',
      fun l₁ _ _ _ _ h' => by cases l₁ <;> simp at h',
      fun l₁ _ _ h' => by cases l₁ <;> simp at h'⟩
  | cons a rest ih =>
    intro acc hdisj hnodup
    rw [List.nodup_cons] at hnodup
    obtain ⟨ha_not, hnodup_rest⟩ := hnodup
    set step := fun (ac : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ × ℝ)) (k : ℕ) =>
      match chooseSample p h m first stamp ac.2 k with
      | some (pos, pace, lag) => (ac.1 ++ [(k, some pos)], some (k, pos, pace, lag))
      | none => (ac.1 ++ [(k, none)], none)
    set acc1 := step acc a
    have hdisj1 : ∀ pair ∈ acc1.1, pair.1 ∉ rest := by
      intro pair hpair hmem
      have h1 : pair ∈ acc.1 ∨ pair.1 = a := by
        dsimp only [acc1, step] at hpair
        cases hch : chooseSample p h m first stamp acc.2 a with
        | none =>
          rw [hch] at hpair; simp only [List.mem_append, List.mem_singleton] at hpair
          rcases hpair with h' | rfl; exact Or.inl h'; exact Or.inr rfl
        | some v =>
          rw [hch] at hpair; simp only [List.mem_append, List.mem_singleton] at hpair
          rcases hpair with h' | rfl; exact Or.inl h'; exact Or.inr rfl
      rcases h1 with h' | heq
      · exact hdisj pair h' (List.mem_cons_of_mem _ hmem)
      · exact ha_not (heq ▸ hmem)
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih acc1 hdisj1 hnodup_rest
    have hacc1_pres : ∀ k, (∃ v, acc.1.lookup k = some v) → acc1.1.lookup k = acc.1.lookup k := by
      intro k hk
      dsimp only [acc1, step]
      cases chooseSample p h m first stamp acc.2 a with
      | none => exact lookup_append_of_mem _ _ k hk
      | some v => exact lookup_append_of_mem _ _ k hk
    have ha_not_acc : ∀ pair ∈ acc.1, pair.1 ≠ a := fun pair hp heq =>
      hdisj pair hp (heq ▸ List.mem_cons_self ..)
    have hacc1_a : acc1.1.lookup a = some ((chooseSample p h m first stamp acc.2 a).map Prod.fst) := by
      dsimp only [acc1, step]
      cases hch : chooseSample p h m first stamp acc.2 a with
      | none => rw [lookup_append_of_not_mem _ _ a ha_not_acc]; simp
      | some v => rw [lookup_append_of_not_mem _ _ a ha_not_acc]; simp
    have hres_a : (rest.foldl step acc1).1.lookup a
        = some ((chooseSample p h m first stamp acc.2 a).map Prod.fst) := by
      rw [ih1 a ⟨_, hacc1_a⟩, hacc1_a]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      change (rest.foldl step acc1).1.lookup k = acc.1.lookup k
      rw [ih1 k ⟨_, by rw [hacc1_pres k hk]; exact hk.choose_spec⟩, hacc1_pres k hk]
    · intro a' rest' j x pc lg y heq hacc2 hj hlu
      injection heq with ha' hrest'; subst ha'; subst hrest'
      change ((rest.foldl step acc1).1.lookup a).join = some y at hlu
      rw [hres_a] at hlu
      simp only [Option.join_some] at hlu
      unfold chooseSample at hlu
      rw [hacc2] at hlu
      cases htg : target p h m first stamp a with
      | none => simp [htg] at hlu
      | some goal =>
        simp only [htg, hj, ↓reduceIte, Option.map_some, Option.some.injEq] at hlu
        rw [← hlu]
        exact stepSample_step_bound p h m x pc goal hslew
    · intro l₁ l₂ k x y heq hkx hky
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        obtain ⟨ha_eq, hrest_eq⟩ := heq
        subst ha_eq
        change ((rest.foldl step acc1).1.lookup a).join = some x at hkx
        rw [hres_a] at hkx
        simp only [Option.join_some] at hkx
        cases hch : chooseSample p h m first stamp acc.2 a with
        | none => simp [hch] at hkx
        | some v =>
          rcases v with ⟨pos, pc, lg⟩
          rw [hch] at hkx
          simp only [Option.map_some, Option.some.injEq] at hkx
          subst hkx
          have hacc1_2 : acc1.2 = some (a, pos, pc, lg) := by
            dsimp only [acc1, step]; rw [hch]
          exact ih2 (a + 1) l₂ a pos pc lg y hrest_eq hacc1_2 rfl hky
      | cons b l₁' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨_, hrest_eq⟩ := heq
        exact ih3 l₁' l₂ k x y hrest_eq hkx hky
    · intro l₁ k x heq hkx
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        obtain ⟨ha_eq, hrest_eq⟩ := heq
        subst ha_eq; subst hrest_eq
        change (acc1.1.lookup a).join = some x at hkx
        rw [hacc1_a] at hkx
        simp only [Option.join_some] at hkx
        cases hch : chooseSample p h m first stamp acc.2 a with
        | none => simp [hch] at hkx
        | some v =>
          rcases v with ⟨pos, pc, lg⟩
          rw [hch] at hkx
          simp only [Option.map_some, Option.some.injEq] at hkx
          subst hkx
          refine ⟨pc, lg, ?_⟩
          change acc1.2 = some (a, pos, pc, lg)
          dsimp only [acc1, step]; rw [hch]
      | cons b l₁' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨_, hrest_eq⟩ := heq
        exact ih4 l₁' k x hrest_eq hkx

private theorem reg_after_request (h : H) (r : Fin R) (m : Memory H R)
    (l : List (Event H R (Payload H)))
    (hno : ∀ e ∈ l, ∀ outs st, e.observation ≠ .asked r outs st) :
    (l.foldl (remember p h) m).reg r = m.reg r := by
  induction l generalizing m with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.foldl_cons]
    have hstep : (remember p h m e).reg r = m.reg r := by
      rcases e with ⟨reading, obs⟩
      cases obs with
      | handed frames stamp =>
        simp only [remember]
        split_ifs
        · cases frames.head? <;> rfl
        · rfl
      | received i payload F =>
        cases payload with
        | block f st lvl =>
          simp only [remember]
          split_ifs
          · rfl
          · cases m.block with
            | none => rfl
            | some b => dsimp only; split_ifs <;> rfl
        | ask sent => simp only [remember]; split_ifs <;> rfl
        | answer sent rec =>
          simp only [remember]
          cases m.peerOffset i with
          | none => rfl
          | some po => dsimp only; split_ifs <;> rfl
        | peerState _ _ _ => rfl
      | asked r' outs st =>
        have hne : r' ≠ r := fun heq => hno ⟨reading, .asked r' outs st⟩ (List.mem_cons_self ..) outs st (by rw [heq])
        simp [remember, Function.update_of_ne (Ne.symm hne)]
      | timer => rfl
    rw [ih (remember p h m e) (fun e' he' => hno e' (List.mem_cons_of_mem _ he')), hstep]

/-- **Speed-bound guarantee (`Solution.WithinSpeed`) for `PeerProtocol.solution`.** -/
theorem withinSpeed (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hs0 : 0 ≤ p.maxSlew) (hs1 : p.maxSlew < 1) :
    (solution p : Solution H R (Payload H)).WithinSpeed w lookahead
      ((2 * B.deviceRate + (1 + B.deviceRate) * p.maxSlew) / (1 - B.deviceRate)) := by
  refine withinSpeed_of_step_bound (solution p) w B hw lookahead hs0 hs1 fun r k x y hx hy => ?_
  obtain ⟨b₁, n₁, hk1, hnb1, hne1, hp1⟩ := exists_asked_of_plays_some (solution p) w lookahead hx
  obtain ⟨b₂, n₂, hk2, hnb2, hne2, hp2⟩ := exists_asked_of_plays_some (solution p) w lookahead hy
  have hmem_iff : ∀ b j, j ∈ (w.speaker r).block b ↔
      (w.speaker r).first b ≤ j ∧ j < (w.speaker r).first (b + 1) := by
    intro b j
    unfold PlaybackDevice.block
    rw [List.mem_range'_1]
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self b)
    omega
  have hb1_bounds := (hmem_iff b₁ k).mp hk1
  have hb2_bounds := (hmem_iff b₂ (k + 1)).mp hk2
  have hnodup : ∀ b, ((w.speaker r).block b).Nodup := fun b => by
    unfold PlaybackDevice.block; exact List.nodup_range'
  rw [solution_append] at hp1 hp2
  dsimp only [act] at hp1 hp2
  set m₁ := ((solution p : Solution H R (Payload H)).states w lookahead n₁).views (w.host r) |>.foldl
    (remember p (w.host r)) Memory.empty
  set m₂ := ((solution p : Solution H R (Payload H)).states w lookahead n₂).views (w.host r) |>.foldl
    (remember p (w.host r)) Memory.empty
  by_cases hsame : b₁ = b₂
  · subst hsame
    have hn_eq : n₁ = n₂ := by
      rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
      · exfalso
        have hsucc := (solution p : Solution H R (Payload H)).askedNext_succ w lookahead (hnb1 ▸ hne1)
        have hmono := (solution p : Solution H R (Payload H)).askedNext_mono w lookahead r (Nat.succ_le_of_lt hlt)
        change ((solution p : Solution H R (Payload H)).states w lookahead (n₁ + 1)).askedNext r
          = ((solution p : Solution H R (Payload H)).states w lookahead n₁).askedNext r + 1 at hsucc
        change ((solution p : Solution H R (Payload H)).states w lookahead (n₁ + 1)).askedNext r
          ≤ ((solution p : Solution H R (Payload H)).states w lookahead n₂).askedNext r at hmono
        omega
      · exact heq
      · exfalso
        have hsucc := (solution p : Solution H R (Payload H)).askedNext_succ w lookahead (hnb2 ▸ hne2)
        have hmono := (solution p : Solution H R (Payload H)).askedNext_mono w lookahead r (Nat.succ_le_of_lt hgt)
        change ((solution p : Solution H R (Payload H)).states w lookahead (n₂ + 1)).askedNext r
          = ((solution p : Solution H R (Payload H)).states w lookahead n₂).askedNext r + 1 at hsucc
        change ((solution p : Solution H R (Payload H)).states w lookahead (n₂ + 1)).askedNext r
          ≤ ((solution p : Solution H R (Payload H)).states w lookahead n₁).askedNext r at hmono
        omega
    subst hn_eq
    have hsplit : ∃ l₁ l₂, (w.speaker r).block b₁ = l₁ ++ k :: (k + 1) :: l₂ := by
      unfold PlaybackDevice.block
      set a := (w.speaker r).first b₁
      set c := (w.speaker r).first (b₁ + 1)
      refine ⟨List.range' a (k - a), List.range' (k + 2) (c - (k + 2)), ?_⟩
      have hlen : c - a = (k - a) + (2 + (c - (k + 2))) := by omega
      have ha1 : a + (k - a) = k := by omega
      calc List.range' a (c - a)
          = List.range' a ((k - a) + (2 + (c - (k + 2)))) := by rw [hlen]
        _ = List.range' a (k - a) ++ List.range' (a + (k - a)) (2 + (c - (k + 2))) := by simp
        _ = List.range' a (k - a) ++ k :: (k + 1) :: List.range' (k + 2) (c - (k + 2)) := by
            rw [ha1, show 2 + (c - (k + 2)) = ((c - (k + 2)) + 1) + 1 by omega]
            simp only [List.range'_succ, Nat.add_assoc]
    obtain ⟨l₁, l₂, hsplit⟩ := hsplit
    exact (decideFold_inv p (w.host r) m₁ (((w.speaker r).block b₁).headD 0)
      ((w.speaker r).reported b₁) hs0 ((w.speaker r).block b₁) ([], m₁.reg r)
      (by simp) (hnodup b₁)).2.2.1 l₁ l₂ k x y hsplit hp1 hp2
  · have hb2_eq : b₂ = b₁ + 1 := by
      have hlt : b₁ < b₂ := by
        by_contra hge; push Not at hge
        have hle' : (w.speaker r).first (b₂ + 1) ≤ (w.speaker r).first b₁ :=
          (w.speaker r).first_strictMono.monotone (by omega)
        omega
      by_contra hne
      have hlt' := (w.speaker r).first_strictMono (show b₁ + 1 < b₂ by omega)
      omega
    subst hb2_eq
    have hk_end : k + 1 = (w.speaker r).first (b₁ + 1) := by omega
    have hsplit1 : ∃ l₁, (w.speaker r).block b₁ = l₁ ++ [k] := by
      unfold PlaybackDevice.block
      set a := (w.speaker r).first b₁
      refine ⟨List.range' a (k - a), ?_⟩
      have hlen : (w.speaker r).first (b₁ + 1) - a = (k - a) + 1 := by omega
      have ha1 : a + (k - a) = k := by omega
      calc List.range' a ((w.speaker r).first (b₁ + 1) - a)
          = List.range' a ((k - a) + 1) := by rw [hlen]
        _ = List.range' a (k - a) ++ [a + (k - a)] := by simp [List.range'_concat]
        _ = List.range' a (k - a) ++ [k] := by rw [ha1]
    obtain ⟨l₁, hsplit1⟩ := hsplit1
    have hsplit2 : ∃ rest, (w.speaker r).block (b₁ + 1) = (k + 1) :: rest := by
      unfold PlaybackDevice.block
      have hpos := (w.speaker r).first_strictMono (Nat.lt_succ_self (b₁ + 1))
      refine ⟨List.range' (k + 2) ((w.speaker r).first (b₁ + 2) - (k + 2)), ?_⟩
      have hlen : (w.speaker r).first (b₁ + 2) - (w.speaker r).first (b₁ + 1)
          = ((w.speaker r).first (b₁ + 2) - (k + 2)) + 1 := by
        have : (w.speaker r).first (b₁ + 1) < (w.speaker r).first (b₁ + 2) := hpos
        omega
      rw [hlen, ← hk_end]; simp [List.range'_succ]
    obtain ⟨rest, hsplit2⟩ := hsplit2
    obtain ⟨pc, lg, hres1⟩ :=
      (decideFold_inv p (w.host r) m₁ (((w.speaker r).block b₁).headD 0)
        ((w.speaker r).reported b₁) hs0 ((w.speaker r).block b₁) ([], m₁.reg r)
        (by simp) (hnodup b₁)).2.2.2 l₁ k x hsplit1 hp1
    have hn_lt : n₁ < n₂ := by
      by_contra hge; push Not at hge
      have hmono := (solution p : Solution H R (Payload H)).askedNext_mono w lookahead r hge
      simp only at hmono; omega
    have hsucc := (solution p : Solution H R (Payload H)).askedNext_succ w lookahead (hnb1 ▸ hne1)
    rw [hnb1] at hsucc
    have hv1 : ((solution p : Solution H R (Payload H)).states w lookahead (n₁ + 1)).views (w.host r)
        = ((solution p : Solution H R (Payload H)).states w lookahead n₁).views (w.host r)
          ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b₁),
            .asked r ((w.speaker r).block b₁) ((w.speaker r).reported b₁)⟩] := by
      rw [(solution p : Solution H R (Payload H)).views_succ w lookahead n₁ (w.host r),
        (solution p : Solution H R (Payload H)).handled_of_asked w lookahead hne1]
      simp
    obtain ⟨l, hl, hev⟩ :=
      (solution p : Solution H R (Payload H)).views_append w lookahead (Nat.succ_le_of_lt hn_lt) (w.host r)
    have hm2_reg : m₂.reg r = some (k, x, pc, lg) := by
      dsimp only [m₂]
      rw [hl, hv1, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [reg_after_request p (w.host r) r _ l]
      · simp only [remember, Function.update_self]
        exact hres1
      · intro e he outs st heo
        obtain ⟨i, hi1, hi2, t, obs, hhi, rfl⟩ := hev e he
        simp only at heo; subst heo
        exact (solution p : Solution H R (Payload H)).no_request_between w lookahead
          (hsucc.trans hnb2.symm) hi1 hi2 hhi
    exact (decideFold_inv p (w.host r) m₂ (((w.speaker r).block (b₁ + 1)).headD 0)
      ((w.speaker r).reported (b₁ + 1)) hs0 ((w.speaker r).block (b₁ + 1)) ([], m₂.reg r)
      (by simp) (hnodup (b₁ + 1))).2.1 (k + 1) rest k x pc lg y hsplit2 hm2_reg rfl hp2

end PeerProtocol

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
    rw [hclock]
    have hsat : ∀ s ∈ (σ h (st.views h ++ [⟨(w₁.clock h).read t, obs⟩])).sends,
        h = w₁.sender ∨ s.1 = w₁.sender :=
      fun s hs => hstar h _ s.1 s.2.1 s.2.2 hs
    rw [hsendAll _ h t _ _ hsat]
  have hkey : ∀ (st : State H R Msg), st.key w₂ = st.key w₁ := by
    intro st; funext d
    cases d <;> simp [State.key, hsrc, hspk]
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
      asked_strictMono := fun _ _ hlt => by linarith [(w.speaker r).asked_strictMono hlt]
      asked_before := fun b => by linarith [(w.speaker r).asked_before b]
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
non-Zeno star solution `σ` without simultaneous cross-origin arrivals in `w`
that plays all frames from `N` onward must suffer
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
    (harr : σ.NoCrossOriginCollision w lookahead)
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
      w₂.source = w₁.source → w₂.speaker = w₁.speaker →
      (∀ n, σ.states w₂ lookahead n = σ.states w₁ lookahead n) →
      ∀ n, σ.eventTime w₂ lookahead n = σ.eventTime w₁ lookahead n := by
    intro w₁ w₂ hsrc hspk hst n
    unfold Solution.eventTime
    have hkey : (σ.states w₂ lookahead n).key w₂ = (σ.states w₁ lookahead n).key w₁ := by
      funext d; rw [hst n]; cases d <;> simp [State.key, hsrc, hspk]
    rw [hkey, hst n]
  have hprogAux : ∀ T, ∃ n, T < σ.eventTime wAux lookahead n := fun T => by
    obtain ⟨n, hn⟩ := hprog T
    exact ⟨n, by rw [hevEq w wAux rfl rfl heqW.1 n]; exact hn⟩
  have hprogAux₁ : ∀ T, ∃ n, T < σ.eventTime (wAux.shiftHosts Δ hnet₁) lookahead n := fun T => by
    obtain ⟨n, hn⟩ := hprog₁ T
    exact ⟨n, by rw [← hevEq (wAux.shiftHosts Δ hnet₁) wPlus rfl rfl heqPlus.1 n]; exact hn⟩
  have hprogAux₂ : ∀ T, ∃ n, T < σ.eventTime (wAux.shiftHosts (-Δ) hnet₂) lookahead n := fun T => by
    obtain ⟨n, hn⟩ := hprog₂ T
    exact ⟨n, by rw [← hevEq (wAux.shiftHosts (-Δ) hnet₂) wMinus rfl rfl heqMinus.1 n]; exact hn⟩
  have harrAux : σ.NoCrossOriginCollision wAux lookahead := by
    intro n m₁ m₂ hm₁ hm₂ hd ha
    rw [heqW.1 n] at hm₁ hm₂
    exact harr n m₁ m₂ hm₁ hm₂ hd ha
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
    hprogAux hprogAux₁ hprogAux₂ harrAux hR N hplayAux hunb

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

/-! ## 5. Concrete Peer Half: `PeerSync` beats the Star Asymmetry Bound -/

/-- Base 3-host world (`Fin 3`: sender `0`, speaker `0` on host `1`, speaker
`1` on host `2`) with unit frame rate, star-link delay `1/2`, and symmetric
direct peer-link delay `1/10`. -/
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
      handed_strictMono := Nat.strictMono_cast
      handed_after := fun b => by simp
      reported := fun b => (b : ℝ) }
  speaker := fun _ =>
    { out := fun k => (k : ℝ) + 2
      out_strictMono := fun _ _ hlt => by
        have : (_ : ℝ) < _ := Nat.cast_lt.mpr hlt; linarith
      first := id
      first_zero := rfl
      first_strictMono := strictMono_id
      asked := fun b => (b : ℝ) + 1
      asked_strictMono := fun _ _ hlt => by
        have : (_ : ℝ) < _ := Nat.cast_lt.mpr hlt; linarith
      asked_before := fun b => by dsimp; linarith
      reported := fun b => (b : ℝ) + 2 }
  network :=
    { deliver := fun i j s _ =>
        if i = 0 ∨ j = 0 then some (s + 1 / 2) else some (s + 1 / 10)
      after := fun i j s _ a h => by
        split_ifs at h <;> (injection h with h; linarith) }
  target := fun _ => 2

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

/- Concrete causal peer protocol for the 3-host separation witness:
* Sender `0` forwards each handed frame `f` to hosts `1` and `2`.
* Speaker `1` (host `2`) sends one NTP probe to speaker `0` (host `1`) on its
  first block request `b = 0`.
* Speaker `0` (host `1`) answers probes from host `2` and plays position
  `k - 2` at output sample `k ≥ 3`.
* Speaker `1` (host `2`) computes `θ = t₂ - (t₁ + t₄) / 2` from the peer reply
  and plays position `k - 2 + θ` at output sample `k ≥ 3`. -/
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

/-- The concrete causal peer `Solution` witnessing zero synchronization error
under arbitrary opposite star asymmetries `±A` (`|A| < 1/4`). -/
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
            | some θ => fun k => if 3 ≤ k then some ((k : ℝ) - 2 + θ) else none
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
    obtain ⟨n, hn⟩ := exists_nat_gt (T' - 1 - Δ (sepBaseWorld.host r))
    exact ⟨n, by change T' < (n : ℝ) + 1 + Δ (sepBaseWorld.host r); linarith⟩

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
    have hn_time : solution.eventTime w' 1 n = (k : ℝ) + 1 + Δ (w'.host r) := by
      unfold Solution.eventTime; rw [hne]; rfl
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
  -- sole `.ask` at `b = 0` (`t₁ = 1`, `t₂ = 1 + Δ 2 + 1/10 - Δ 1`, arriving at `1 + Δ 2 + 2/10`).
  have hno_ask_other : ∀ m n', m ∈ (solution.states w' 1 n').inFlight →
      (∀ s, m.contents = .ask s → m.origin = 2 ∧ m.destination = 1 ∧ s = 1 ∧
        m.arrival = 1 + Δ 2 + 1 / 10) ∧
      (∀ s r, m.contents = .answer s r → m.origin = 1 ∧ m.destination = 2 ∧ s = 1 ∧
        r = 1 + Δ 2 + 1 / 10 - Δ 1 ∧ m.arrival = 1 + Δ 2 + 2 / 10) := by
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
                have ht_eq : t = 1 + Δ 2 + 1 / 10 := by
                  linarith [hinfo.2.2.2, hm₀_arr]
                have hs_eq : s = 1 := hinfo.2.2.1
                have harr_eq : m.arrival = 1 + Δ 2 + 2 / 10 := by
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
                have ht_eq : t = 1 + Δ 2 := by
                  rw [ht_eq0, hb0]
                  simp [w', shiftStarKeepPeers, sepBaseWorld]
                have harr_eq : m.arrival = 1 + Δ 2 + 1 / 10 := by
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
  -- Show the single `.answer` reply IS delivered to host `2` before `1 + Δ 2 + 3 / 10 < 4 + Δ 2`.
  have hreply_in_view : ∀ n, (solution.states w' 1 n).askedNext 1 ≥ 3 →
      peerOffsetFromView ((solution.states w' 1 n).views 2) = some (Δ 2 - Δ 1) := by
    intro n hn3
    -- Step `na0`: host `2` handles request `b = 0` at `1 + Δ 2`, sending `.ask 1` to host `1`.
    obtain ⟨na0, hna0_lt, hna0_b, hna0_early⟩ :=
      solution.exists_asked_step w' 1 (r := 1) (show 0 < (solution.states w' 1 n).askedNext 1 by omega)
    have hblk0 : (w'.speaker 1).block 0 = [0] := by
      simp [w', shiftStarKeepPeers, sepBaseWorld, PlaybackDevice.block]
    have hclk0 : (w'.clock 2).read ((w'.speaker 1).asked 0) = 1 := by
      simp [w', shiftStarKeepPeers, sepBaseWorld]
    have hhand0 : solution.handled w' 1 na0 =
        some (2, (w'.speaker 1).asked 0, .asked 1 ((w'.speaker 1).block 0) ((w'.speaker 1).reported 0)) :=
      solution.handled_of_asked w' 1 hna0_early
    have hS0 : (solution 2 ((solution.states w' 1 na0).views 2 ++
        [⟨(w'.clock 2).read ((w'.speaker 1).asked 0),
          .asked 1 ((w'.speaker 1).block 0) ((w'.speaker 1).reported 0)⟩])).sends
        = [(1, Payload.ask 1, ∅)] := by
      simp [solution, hblk0, hclk0]
    have mask_in : (⟨1 + Δ 2 + 1 / 10, 2, 1, Payload.ask 1, ∅⟩ : InFlight (Fin 3) Payload)
        ∈ (solution.states w' 1 (na0 + 1)).inFlight := by
      have hsent := solution.sent_inFlight (w := w') 1 hhand0 hS0 (i := 0) (by simp)
        (arr := 1 + Δ 2 + 1 / 10) (by simp [w', shiftStarKeepPeers, sepBaseWorld])
      simpa using hsent
    -- The `.ask` is handled before step `n` (since `eventTime n ≥ asked 2 = 3 + Δ 2 > 1 + Δ 2 + 1/10`).
    have hn_gt_ask : 1 + Δ 2 + 1 / 10 < solution.eventTime w' 1 n := by
      obtain ⟨na2, hna2_lt, _, hna2_early⟩ :=
        solution.exists_asked_step w' 1 (r := 1) (show 2 < (solution.states w' 1 n).askedNext 1 by omega)
      have hmono := solution.eventTime_mono w' 1 hna2_lt.le
      have ht2 : solution.eventTime w' 1 na2 = 3 + Δ 2 := by
        unfold Solution.eventTime; rw [hna2_early]
        simp [State.key, w', shiftStarKeepPeers, sepBaseWorld]; norm_num
      linarith
    obtain ⟨n_ask, _, hn_ask_lt, hhand_ask⟩ :=
      solution.handled_before w' 1 mask_in (Nat.succ_le_of_lt hna0_lt) hn_gt_ask
    -- At step `n_ask`, host `1` sends `.answer 1 (1 + Δ 2 + 1/10 - Δ 1)` arriving at `1 + Δ 2 + 2/10`.
    have mans_in : (⟨1 + Δ 2 + 2 / 10, 1, 2, Payload.answer 1 (1 + Δ 2 + 1 / 10 - Δ 1), ∅⟩ :
        InFlight (Fin 3) Payload) ∈ (solution.states w' 1 (n_ask + 1)).inFlight := by
      have hclk1 : (w'.clock 1).read (1 + Δ 2 + 1 / 10) = 1 + Δ 2 + 1 / 10 - Δ 1 := by
        simp [w', shiftStarKeepPeers, sepBaseWorld]
      have hS1 : (solution 1 ((solution.states w' 1 n_ask).views 1 ++
          [⟨(w'.clock 1).read (1 + Δ 2 + 1 / 10), .received 2 (.ask 1) ∅⟩])).sends
          = [(2, Payload.answer 1 (1 + Δ 2 + 1 / 10 - Δ 1), ∅)] := by
        simp only [solution, List.getLast?_concat, hclk1]
      have hsent := solution.sent_inFlight (w := w') 1 hhand_ask hS1 (i := 0) (by simp)
        (arr := 1 + Δ 2 + 2 / 10) (by simp [w', shiftStarKeepPeers, sepBaseWorld]; ring)
      simpa using hsent
    -- That `.answer` arrives and is handled before step `n`!
    have hn_gt_ans : 1 + Δ 2 + 2 / 10 < solution.eventTime w' 1 n := by
      obtain ⟨na2, hna2_lt, _, hna2_early⟩ :=
        solution.exists_asked_step w' 1 (r := 1) (show 2 < (solution.states w' 1 n).askedNext 1 by omega)
      have hmono := solution.eventTime_mono w' 1 hna2_lt.le
      have ht2 : solution.eventTime w' 1 na2 = 3 + Δ 2 := by
        unfold Solution.eventTime; rw [hna2_early]
        simp [State.key, w', shiftStarKeepPeers, sepBaseWorld]; norm_num
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
      have ht_eq : t = 1 + Δ 2 + 2 / 10 := by linarith [hm₀_arr, hinfo.2.2.2.2]
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
    exact hlist _ ⟨_, hmem_ans, 1, 1 + Δ 2 + 1 / 10 - Δ 1, ∅, rfl⟩ hall_ans
  -- Compute `solution.plays w' 1 r k` for `r = 0, 1` and `k ≥ 3`.
  have hplays0 : ∀ k, 3 ≤ k → solution.plays w' 1 0 k = some ((k : ℝ) - 2) := by
    intro k hk3
    obtain ⟨m, hm⟩ := hprog ((w'.speaker 0).asked k)
    obtain ⟨n, -, hnk, hne⟩ := solution.exists_asked_step w' 1 (solution.lt_askedNext w' 1 hm)
    have hmem_k : k ∈ (w'.speaker 0).block k := by
      simp [w', shiftStarKeepPeers, sepBaseWorld, PlaybackDevice.block]
    rw [solution.plays_of_asked_step w' 1 hnk hne hmem_k]
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
  have hplays1 : ∀ k, 3 ≤ k → solution.plays w' 1 1 k = some ((k : ℝ) - 2 + (Δ 2 - Δ 1)) := by
    intro k hk3
    obtain ⟨m, hm⟩ := hprog ((w'.speaker 1).asked k)
    obtain ⟨n, -, hnk, hne⟩ := solution.exists_asked_step w' 1 (solution.lt_askedNext w' 1 hm)
    have hmem_k : k ∈ (w'.speaker 1).block k := by
      simp [w', shiftStarKeepPeers, sepBaseWorld, PlaybackDevice.block]
    rw [solution.plays_of_asked_step w' 1 hnk hne hmem_k]
    have hoff := hreply_in_view n (by omega)
    have hhost1 : w'.host 1 = 2 := rfl
    have hact : (solution (w'.host 1) ((solution.states w' 1 n).views (w'.host 1) ++
        [⟨(w'.clock (w'.host 1)).read ((w'.speaker 1).asked k),
          .asked 1 ((w'.speaker 1).block k) ((w'.speaker 1).reported k)⟩])).plays k
        = some ((k : ℝ) - 2 + (Δ 2 - Δ 1)) := by
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
      have hf1 : |(f : ℝ) - ((k : ℝ) - 2 + (Δ 2 - Δ 1))| < 1 := by simpa using hf
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
        w'.playTime (solution.plays w' 1) r n = some ((n : ℝ) + 4 - c + Δ (w'.host r)) := by
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
      change ((k₀ : ℝ) + 2 + Δ (w'.host r))
          + ((n : ℝ) - ((k₀ : ℝ) - 2 + c)) / (((k₀ + 1 : ℕ) : ℝ) - 2 + c - ((k₀ : ℝ) - 2 + c))
            * (((k₀ + 1 : ℕ) : ℝ) + 2 + Δ (w'.host r) - ((k₀ : ℝ) + 2 + Δ (w'.host r)))
        = (n : ℝ) + 4 - c + Δ (w'.host r)
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
      simpa [w', shiftStarKeepPeers, sepBaseWorld] using h0
    · have hex1 : ∃ k, Covers (solution.plays w' 1 1) k n := by
        by_cases hsign : 0 ≤ Δ 2 - Δ 1
        · refine ⟨n + 1, (n : ℝ) - 1 + (Δ 2 - Δ 1), (n : ℝ) + (Δ 2 - Δ 1), ?_, ?_,
            by linarith, by linarith, by linarith, by linarith⟩
          · have := hplays1 (n + 1) (by omega)
            rw [this]; congr 1; push_cast; ring
          · have := hplays1 (n + 2) (by omega)
            rw [this]; congr 1; push_cast; ring
        · refine ⟨n + 2, (n : ℝ) + (Δ 2 - Δ 1), (n : ℝ) + 1 + (Δ 2 - Δ 1), ?_, ?_,
            by linarith, by linarith, by linarith, by linarith⟩
          · have := hplays1 (n + 2) (by omega)
            rw [this]; congr 1; push_cast; ring
          · have := hplays1 (n + 3) (by omega)
            rw [this]; congr 1; push_cast; ring
      have h1 := hpt_of_cov 1 (Δ 2 - Δ 1) hplays1 (hcov_ge3 1) hex1
      rw [h1]; congr 1
      change (n : ℝ) + 4 - (Δ 2 - Δ 1) + Δ 2 = (n : ℝ) + 4 + Δ 1
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
   without simultaneous cross-origin arrivals in `sepBaseWorld` that plays all
   frames from some `N` onward must suffer
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
      σ.NoCrossOriginCollision sepBaseWorld 1 →
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
  · intro Msg σ hstar hprog hprog₁ hprog₂ harr N hplay
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
      hprog hprog₁ hprog₂ harr (by norm_num) N hplay hunb
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

end Unisono.Solutions.Optimal
