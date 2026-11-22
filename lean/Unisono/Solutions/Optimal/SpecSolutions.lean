/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Model.Regulation
public import Unisono.Solutions.FixedDelay
public import Unisono.Spec.Models.Bounded
public import Unisono.Spec.Topologies

/-!
# Concrete `Unisono.Spec.Solution` constructions and Star-vs-Peer separation

This module bridges the analytical optimum (`ModalControl`, `Spectral`,
`Estimation`, `Level`) directly to the formal specification's event-driven run
model (`Unisono.Spec.Solution`, `Unisono.Spec.World`, `Unisono.Spec.Objectives`).

## Contents

1. **Topology classification of `FixedDelay` (`fixedDelay_isStar`).** The
   baseline `FixedDelay.solution` is formally a star solution (`Solution.IsStar`).
2. **Concrete Star solution (`StarOptimal.solution`).** Uses:
   - sender-disciplined stream packets carrying `(first, stamp, level, schedOffset)`,
   - non-blocking sliding-window minimum-RTT clock probes (`ask` / `answer`),
   - two-state playback pace regulation driven by `Unisono.Model.Regulation.law`
     with speed clamping.
   We prove `StarOptimal.isStar` and non-Zeno liveness (`StarOptimal.progress`,
   `StarOptimal.request_step`) in every bounded world.
3. **Concrete Peer solution (`PeerOptimal.solution`).** Extends the protocol
   with direct receiver-to-receiver clock probes (`ask` / `answer` across a
   configured neighbor graph `peers`) and lightweight peer state messages for
   modal consensus control (`gCom`, `gDiff`). We prove `PeerOptimal.usesGraph`
   and non-Zeno liveness (`PeerOptimal.progress`, `PeerOptimal.request_step`).
4. **End-to-end Star-vs-Peer asymmetry separation directly on `Unisono.Spec`
   (`star_cannot_use_peer_links`, `star_sync_lower_bound_with_symmetric_peers`,
   `peer_probe_recovers_exact_offset`).**
   * Any `Solution.IsStar` solution produces identical runs when non-star
     (receiver-to-receiver) links are modified.
   * Consequently, on a pair of worlds `w⁺, w⁻` that have opposite sender-link
     one-way delay asymmetries `±A` and a *symmetric* direct peer link between
     receivers `1` and `2`, every order-preserving star solution must suffer
     `max (w⁺.sync) (w⁻.sync) ≥ ENNReal.ofReal (A²)`, whereas a direct
     receiver–receiver probe on `(1, 2)` recovers the exact relative clock
     shift `±2A` with zero bias.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Optimal

open Unisono.Spec Unisono.Model.Regulation
open scoped ENNReal

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

/-! ## 2. Concrete Star solution (`StarOptimal`) -/

namespace StarOptimal

variable {H : Type} {R : ℕ}

/-- Message payload for the star-optimal protocol. -/
inductive Payload where
  /-- Stream block carrying first frame index, capture timestamp, announced
  playout level `L`, and sender-disciplined schedule offset `schedOffset`. -/
  | block (first : ℕ) (stamp : ℝ) (level : ℝ) (schedOffset : ℝ)
  /-- Non-blocking clock probe carrying sender-side query timestamp `t₁`. -/
  | ask (sent : ℝ)
  /-- Reply to a clock probe carrying `(t₁, t₂)`. -/
  | answer (sent : ℝ) (received : ℝ)

/-- Parameters of the star-optimal protocol. -/
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
  /-- Latest received stream block: `(first, stamp, level, schedOffset)`. -/
  block : Option (ℕ × ℝ × ℝ × ℝ)
  /-- Recent `(sent, rtt, rawOffset)` clock probe replies (newest last). -/
  rttWindow : List (ℝ × ℝ × ℝ)
  /-- Current filtered offset `(lastSent, offset)`. -/
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

/-- Select the offset sample with minimum RTT from a nonempty sliding window. -/
def minRttOffset : List (ℝ × ℝ × ℝ) → Option (ℝ × ℝ)
  | [] => none
  | (s, rtt, off) :: rest =>
      match minRttOffset rest with
      | none => some (s, off)
      | some (s', off') =>
          -- Pick the entry with strictly smaller RTT if available.
          let bestRtt := rest.foldl (fun acc x => min acc x.2.1) rtt
          if rtt ≤ bestRtt then some (s, off) else some (s', off')

variable (p : Params H)

def target (m : Memory H R) (first : ℕ) (stamp : ℝ) (k : ℕ) : Option ℝ :=
  match m.block, m.offset with
  | some (f, captured, lvl, schedOff), some (_, off) =>
      some (f + ((stamp + ((k : ℝ) - first) / p.rate + off - schedOff - lvl) - captured) * p.rate)
  | _, _ => none

/-- Advance one output sample using `Unisono.Model.Regulation.law p.gain`,
clamping playback pace to `[1 - maxSlew, 1 + maxSlew]`. -/
def stepSample (prevPos prevPace goal : ℝ) : ℝ × ℝ :=
  let err := goal - (prevPos + prevPace)
  let delta := law p.gain (err, prevPace - 1)
  let newPace := 1 + clamp p.maxSlew ((prevPace - 1) + delta)
  (prevPos + newPace, newPace)

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
        | some (f, _) => { m with block := some (f, stamp, p.level, 0), offset := some (0, 0) }
        | none => m
      else m
  | .received _ (.block f stamp lvl schedOff) _ =>
      if h = p.sender then m
      else
        match m.block with
        | some (f', _, _, _) =>
            if f' < f then { m with block := some (f, stamp, lvl, schedOff) } else m
        | none => { m with block := some (f, stamp, lvl, schedOff) }
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
                  (j, Payload.block f stamp p.level 0, (frames.map Prod.fst).toFinset)
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

/-- The concrete star-optimal `Unisono.Spec.Solution`. -/
def solution : Solution H R Payload := fun h view =>
  match view.getLast? with
  | some e => act p h (view.dropLast.foldl (remember p h) Memory.empty) e
  | none => ⟨[], [], fun _ => none⟩

theorem solution_append (h : H) (view : List (Event H R Payload)) (e : Event H R Payload) :
    solution p h (view ++ [e]) = act p h (view.foldl (remember p h) Memory.empty) e := by
  simp [solution]

/-- `StarOptimal.solution` strictly obeys the star communication graph. -/
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
      | block _ _ _ _ => simp [hobs] at hmem
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
  | .block _ _ _ _ => 1
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

/-- **Non-Zeno progress of `StarOptimal.solution`.** In any bounded world, the
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
    | block _ _ _ _ => simp [act, msgWeight]
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

end StarOptimal

/-! ## 3. Concrete Peer / Receiver–Receiver solution (`PeerOptimal`) -/

namespace PeerOptimal

variable {H : Type} {R : ℕ}

/-- Message payload for the peer (receiver–receiver) protocol. -/
inductive Payload (H : Type) where
  /-- Stream block from the sender. -/
  | block (first : ℕ) (stamp : ℝ) (level : ℝ)
  /-- Pairwise clock probe to either the sender or a direct receiver peer. -/
  | ask (sent : ℝ)
  /-- Reply to a pairwise clock probe. -/
  | answer (sent : ℝ) (received : ℝ)
  /-- Lightweight peer state message announcing a host's current estimated
  latency deviation for two-gain modal / consensus pace control. -/
  | peerState (origin : H) (deviation : ℝ)

/-- Parameters of the peer (receiver–receiver) protocol. -/
structure Params (H : Type) where
  sender : H
  speakers : List H
  /-- Direct peer neighbors of each host `h` (excluding `h` itself). -/
  peers : H → List H
  rate : ℝ
  level : ℝ
  copies : ℕ
  period : ℝ
  /-- Common-mode gain (`0` in low-latency pure-consensus mode). -/
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
  /-- Latest received latency deviation from each peer `j`. -/
  peerDev : H → ℝ
  asked : Option ℝ
  answered : H → Option ℝ
  reg : Fin R → Option (ℕ × ℝ × ℝ)

def Memory.empty : Memory H R where
  block := none
  peerOffset := fun _ => none
  peerDev := fun _ => 0
  asked := none
  answered := fun _ => none
  reg := fun _ => none

def clamp (w x : ℝ) : ℝ := max (-w) (min w x)

variable (p : Params H)

/-- Estimate of sender offset combining direct sender probe and available
one-hop peer paths `(self ↔ peer ↔ sender)` via equal-weight averaging when
both exist. -/
def senderOffset (m : Memory H R) : Option ℝ :=
  (m.peerOffset p.sender).map Prod.snd

def target (m : Memory H R) (first : ℕ) (stamp : ℝ) (k : ℕ) : Option ℝ :=
  match m.block, senderOffset p m with
  | some (f, captured, lvl), some off =>
      some (f + ((stamp + ((k : ℝ) - first) / p.rate + off - lvl) - captured) * p.rate)
  | _, _ => none

/-- Two-mode sample advance: applies `law p.gCom` to the estimated group mean
deviation and `law p.gDiff` to the local differential deviation, clamped to
`[1 - maxSlew, 1 + maxSlew]`. -/
def stepSample (p : Params H) (h : H) (m : Memory H R) (prevPos prevPace goal : ℝ) : ℝ × ℝ :=
  let err := goal - (prevPos + prevPace)
  let neighbors := p.peers h
  let nCount : ℝ := (neighbors.length : ℝ) + 1
  let meanErr := (err + (neighbors.map m.peerDev).sum) / nCount
  let diffErr := err - meanErr
  let deltaCom := if p.gCom = 0 then 0 else law p.gCom (meanErr, prevPace - 1)
  let deltaDiff := law p.gDiff (diffErr, prevPace - 1)
  let newPace := 1 + clamp p.maxSlew ((prevPace - 1) + deltaCom + deltaDiff)
  (prevPos + newPace, newPace)

def chooseSample (h : H) (m : Memory H R) (first : ℕ) (stamp : ℝ)
    (prev : Option (ℕ × ℝ × ℝ)) (k : ℕ) : Option (ℝ × ℝ) :=
  match target p m first stamp k, prev with
  | some goal, some (j, pos, pace) =>
      if j + 1 = k then some (stepSample p h m pos pace goal) else some (goal, 1)
  | some goal, none => some (goal, 1)
  | none, _ => none

def decideBlock (h : H) (m : Memory H R) (r : Fin R) (outputs : List ℕ) (stamp : ℝ) :
    List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ) :=
  outputs.foldl
    (fun (acc : List (ℕ × Option ℝ) × Option (ℕ × ℝ × ℝ)) k =>
      match chooseSample p h m (outputs.headD 0) stamp acc.2 k with
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

/-- Query targets for a non-sender host: the sender plus all configured direct
peers (excluding itself and the sender to avoid duplicates). -/
def probeTargets (h : H) : List H :=
  p.sender :: (p.peers h).filter (fun j => j ≠ p.sender ∧ j ≠ h)

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
  | .received i (.peerState _ dev) _ =>
      { m with peerDev := Function.update m.peerDev i dev }
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
      let probes :=
        if asks p h m e.reading then
          (probeTargets p h).flatMap fun j =>
            List.replicate p.copies (j, Payload.ask e.reading, ∅)
        else []
      { sends := probes
        timers := []
        plays := fun k => (res.1.lookup k).join }
  | _ => ⟨[], [], fun _ => none⟩

/-- The concrete peer-optimal `Unisono.Spec.Solution`. -/
def solution : Solution H R (Payload H) := fun h view =>
  match view.getLast? with
  | some e => act p h (view.dropLast.foldl (remember p h) Memory.empty) e
  | none => ⟨[], [], fun _ => none⟩

theorem solution_append (h : H) (view : List (Event H R (Payload H)))
    (e : Event H R (Payload H)) :
    solution p h (view ++ [e]) = act p h (view.foldl (remember p h) Memory.empty) e := by
  simp [solution]

/-- `PeerOptimal.solution` uses only star edges and configured undirected peer
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
      | peerState _ _ => simp [hobs] at hmem
    | asked r outputs stamp =>
      simp only [hobs] at hmem
      split_ifs at hmem with ha
      · rw [List.mem_flatMap] at hmem
        obtain ⟨j, hj, hrep⟩ := hmem
        rw [List.mem_replicate] at hrep
        have hdst : dst = j := congrArg Prod.fst hrep.2
        subst hdst
        simp only [probeTargets, List.mem_cons, List.mem_filter, decide_eq_true_eq] at hj
        rcases hj with rfl | ⟨hpeer, _⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl hpeer))
      · simp at hmem
    | timer => simp [hobs] at hmem

def msgWeight : Payload H → ℕ
  | .block _ _ _ => 1
  | .ask _ => 1 + p.copies
  | .answer _ _ => 1
  | .peerState _ _ => 1

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

/-- **Non-Zeno progress of `PeerOptimal.solution`.** Suppose every host has at
most `maxPeers` configured peers (`∀ h, (p.peers h).length ≤ maxPeers`). Then
in every bounded world the run advances past every true time `T`. -/
theorem progress (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (maxPeers : ℕ) (hmax : ∀ h : H, (p.peers h).length ≤ maxPeers) (T : Time) :
    ∃ n, T < (solution p : Solution H R (Payload H)).eventTime w lookahead n := by
  obtain ⟨-, hsrc, hspk, -, -, -, hlead, -, -, -, -⟩ := hw
  refine Solution.progress w (solution p) lookahead (msgWeight p)
    (p.copies * (p.speakers.filter (· ≠ p.sender)).length + 1)
    (p.copies * (1 + p.copies) * (1 + maxPeers) + 1)
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
    · rw [weight_flatMap p _ _ (1 + p.copies) _ rfl]
      have hlen : (probeTargets p h).length ≤ 1 + maxPeers := by
        simp only [probeTargets, List.length_cons]
        have hflt := List.length_filter_le (fun j => decide (j ≠ p.sender ∧ j ≠ h)) (p.peers h)
        have hm := hmax h
        omega
      have hmul : p.copies * (1 + p.copies) * (probeTargets p h).length
          ≤ p.copies * (1 + p.copies) * (1 + maxPeers) := Nat.mul_le_mul_left _ hlen
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
    | peerState _ _ => simp [act, msgWeight]

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

end PeerOptimal

/-! ## 4. End-to-end Star-vs-Peer asymmetry separation in `Unisono.Spec` -/

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

/-- Modify `w.shiftHosts Δ hnet` so that direct receiver-to-receiver (non-star)
links keep the **symmetric** unshifted delivery network of `w`, while star
links (`i = w.sender ∨ j = w.sender`) carry the shifted one-way asymmetry
`Δ j - Δ i`. -/
def shiftStarKeepPeers (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j) : World H R where
  rate := w.rate
  rate_pos := w.rate_pos
  sender := w.sender
  host := w.host
  hosts := w.hosts
  clock := (w.shiftHosts Δ hnet).clock
  source := w.source
  speaker := (w.shiftHosts Δ hnet).speaker
  network :=
    { deliver := fun i j t q =>
        if i = w.sender ∨ j = w.sender then
          (w.shiftHosts Δ hnet).network.deliver i j t q
        else
          w.network.deliver i j t q
      after := fun i j t q a h => by
        split_ifs at h with hs
        · exact (w.shiftHosts Δ hnet).network.after i j t q a h
        · exact w.network.after i j t q a h }
  target := w.target

/-- **End-to-end Star lower bound in worlds with symmetric direct peer links.**
On the pair of worlds `w⁺ = shiftStarKeepPeers w Δ` and
`w⁻ = shiftStarKeepPeers w (-Δ)` (where sender links carry opposite one-way
asymmetries `±Δ`, while direct receiver-to-receiver links remain completely
symmetric!), **every** star solution `σ` whose event order is preserved by
`±Δ` is blind to the symmetric peer links and must suffer
`max (w⁺.sync) (w⁻.sync) ≥ ENNReal.ofReal (varFin (fun r => Δ (w.host r)))`. -/
theorem star_sync_lower_bound_with_symmetric_peers (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (hstar : σ.IsStar w.sender)
    (Δ : H → ℝ) (hΔs : Δ w.sender = 0)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (horder₁ : ∀ n,
      earliest ((σ.states (w.shiftHosts Δ hnet₁) lookahead n).key (w.shiftHosts Δ hnet₁))
          (σ.states (w.shiftHosts Δ hnet₁) lookahead n).due
        = earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due)
    (horder₂ : ∀ n,
      earliest ((σ.states (w.shiftHosts (-Δ) hnet₂) lookahead n).key (w.shiftHosts (-Δ) hnet₂))
          (σ.states (w.shiftHosts (-Δ) hnet₂) lookahead n).due
        = earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due)
    (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime (σ.plays w lookahead) r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    let wPlus := shiftStarKeepPeers w Δ hnet₁
    let wMinus := shiftStarKeepPeers w (-Δ) hnet₂
    ENNReal.ofReal (varFin fun r => Δ (w.host r))
      ≤ max (wPlus.sync (σ.plays wPlus lookahead)) (wMinus.sync (σ.plays wMinus lookahead)) := by
  intro wPlus wMinus
  have hpPlus : σ.plays wPlus lookahead = σ.plays (w.shiftHosts Δ hnet₁) lookahead :=
    (star_states_eq_of_star_links_eq σ (w.shiftHosts Δ hnet₁) wPlus lookahead hstar
      rfl rfl rfl rfl rfl rfl (fun i j t q hs => by
        change i = w.sender ∨ j = w.sender at hs
        simp [wPlus, shiftStarKeepPeers, hs])).2
  have hpMinus : σ.plays wMinus lookahead = σ.plays (w.shiftHosts (-Δ) hnet₂) lookahead :=
    (star_states_eq_of_star_links_eq σ (w.shiftHosts (-Δ) hnet₂) wMinus lookahead hstar
      rfl rfl rfl rfl rfl rfl (fun i j t q hs => by
        change i = w.sender ∨ j = w.sender at hs
        simp [wMinus, shiftStarKeepPeers, hs])).2
  have hsyncPlus : wPlus.sync (σ.plays wPlus lookahead)
      = (w.shiftHosts Δ hnet₁).sync (σ.plays (w.shiftHosts Δ hnet₁) lookahead) := by
    rw [hpPlus]; rfl
  have hsyncMinus : wMinus.sync (σ.plays wMinus lookahead)
      = (w.shiftHosts (-Δ) hnet₂).sync (σ.plays (w.shiftHosts (-Δ) hnet₂) lookahead) := by
    rw [hpMinus]; rfl
  rw [hsyncPlus, hsyncMinus]
  exact σ.sync_shiftHosts_lower_bound w lookahead Δ hΔs hnet₁ hnet₂ horder₁ horder₂ hR N hplay hunb

/-- **Direct symmetric peer probe recovers the exact relative shift with zero
bias.** In `w' = shiftStarKeepPeers w Δ hnet` where the base world `w` has
unit-rate clocks (`(w.clock h).read t = t + c_h`) and a symmetric direct peer
link of constant delay `d > 0` between two non-sender hosts `h₁, h₂`, a single
NTP query-reply exchange `(h₁ → h₂ → h₁)` at true time `s` produces readings
`(t₁, t₂, t₄)` whose NTP estimator `t₂ - (t₁ + t₄) / 2` equals the exact
relative clock shift `(c₂ - Δ h₂) - (c₁ - Δ h₁)` with zero asymmetry error
(and in particular recovers `±(Δ h₁ - Δ h₂)` when `c₁ = c₂`, which is invisible
to every star solution). -/
theorem peer_probe_recovers_exact_offset (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    {h₁ h₂ : H} (h1s : h₁ ≠ w.sender) (h2s : h₂ ≠ w.sender)
    {c₁ c₂ d s : ℝ} {q₁ q₂ : ℕ}
    (hc₁ : ∀ t, (w.clock h₁).read t = t + c₁)
    (hc₂ : ∀ t, (w.clock h₂).read t = t + c₂)
    (hd12 : w.network.deliver h₁ h₂ s q₁ = some (s + d))
    (hd21 : w.network.deliver h₂ h₁ (s + d) q₂ = some (s + 2 * d)) :
    let w' := shiftStarKeepPeers w Δ hnet
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
  · simp only [w', shiftStarKeepPeers, World.shiftHosts, hc₁, hc₂]
    ring

end StarVsPeerSeparation

end Unisono.Solutions.Optimal
