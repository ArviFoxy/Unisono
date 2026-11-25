/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.HeldLevel
public import Unisono.Model.Descent

/-!
# A level rule that steps against the reported needs

The controller takes the rule by which the sender chooses the level as a
parameter (`LevelRule`). This file defines a rule and proves that what it
announces is continuous from block to block, which is the condition under
which `speaker_plays_of_levels` says what every speaker plays.

* `announced`: what a level rule announces with each capture block in a
  run: its value at the step that handles the handover of the block.
  `announced_eq` says that this is the value at any such step.
* `steppedLevel`: the rule. The sender keeps a level that it aims at and the
  level of the first frame of the next block. A clock query that carries a
  need moves the aim one step against the slope of the cost of that need
  (`Unisono.Model.Descent.needSlope`), within bounds. At a handover the
  sender announces the level of the block's first frame and a slope that
  moves the level toward the aim, by at most `slopeMax` per frame, and the
  next block starts where this one ends.
* `announced_steppedLevel_succ`: the level announced with block `b + 1` is
  the level announced with block `b` plus `blockSize` times its slope, in
  every world.
* `abs_announced_slope_le`: every announced slope is at most
  `slopeMax` in absolute value.
* `speaker_plays_of_steppedLevel`: with clocks at constant rates, the
  conclusion of `speaker_plays_of_levels` holds for this rule when
  `slopeMax` is less than the time from one frame to the next on the
  sender's clock.

The hosts that play do not measure needs yet: the clock queries of the
controller carry none, so in its runs the aim never moves. What the rule
achieves is not stated here; no cost is bounded.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld
open Unisono.Model.Descent (clampTo clampTo_mem needSlope)

variable {H : Type} {R : ℕ}

/-- The settings of the level rule that steps against the reported needs. -/
structure LevelSettings where
  /-- The level at the start, in seconds of the sender's clock. -/
  start : ℝ
  /-- The least level. -/
  lo : ℝ
  /-- The largest level. -/
  hi : ℝ
  /-- The step: by how much a unit of slope moves the aim. -/
  step : ℝ
  /-- What a second of level costs for one report. -/
  latencyCost : ℝ
  /-- What a second by which a need exceeds the level costs. -/
  lateCost : ℝ
  /-- The largest change of the level from one frame to the next. -/
  slopeMax : ℝ
  /-- The number of frames of a block of the source. -/
  blockSize : ℕ

/-- What the level rule remembers: the level that it aims at, and the level
of the first frame of the next block. -/
structure LevelState where
  aim : ℝ
  level : ℝ

/-- The change of the level from one frame to the next that the rule
announces in the state `st`: the change that would reach the aim at the end
of the block, cut to at most `slopeMax` in absolute value. -/
def slopeTo (q : LevelSettings) (st : LevelState) : ℝ :=
  clampTo (-q.slopeMax) q.slopeMax ((st.aim - st.level) / q.blockSize)

/-- How an event at the sender changes what the level rule remembers. A
clock query that carries the need `y` moves the aim one step against the
slope of the cost of that need, within the bounds. A handover moves the
level to the end of the block. Other events change nothing. -/
def levelStep (q : LevelSettings) (st : LevelState) (e : Event H R Payload) : LevelState :=
  match e.observation with
  | .received _ (.ask _ (some y)) _ =>
      ⟨clampTo q.lo q.hi (st.aim - q.step * needSlope q.latencyCost q.lateCost y st.aim),
        st.level⟩
  | .handed _ _ => ⟨st.aim, st.level + q.blockSize * slopeTo q st⟩
  | _ => st

/-- What the level rule remembers after the events `l` at the sender. -/
def levelState (q : LevelSettings) (l : List (Event H R Payload)) : LevelState :=
  l.foldl (levelStep q) ⟨q.start, q.start⟩

/-- **The level rule that steps against the reported needs.** At a
handover, from the sender's view up to the handover: the level of the
block's first frame, and the slope that moves the level toward the aim. -/
def steppedLevel (q : LevelSettings) : LevelRule H R := fun view _ =>
  ((levelState q view.dropLast).level, slopeTo q (levelState q view.dropLast))

/-- The announced slope is at most `slopeMax` in absolute value. -/
theorem abs_slopeTo_le (q : LevelSettings) (hq : 0 ≤ q.slopeMax) (st : LevelState) :
    |slopeTo q st| ≤ q.slopeMax := by
  have h := clampTo_mem (lo := -q.slopeMax) (hi := q.slopeMax) (by linarith)
    ((st.aim - st.level) / q.blockSize)
  exact abs_le.mpr ⟨h.1, h.2⟩

/-- An event that is not a handover leaves the level of the next block in
place. -/
theorem levelStep_level (q : LevelSettings) (st : LevelState) {e : Event H R Payload}
    (he : ∀ frames stamp, e.observation ≠ .handed frames stamp) :
    (levelStep q st e).level = st.level := by
  unfold levelStep
  cases hobs : e.observation with
  | handed frames stamp => exact absurd hobs (he frames stamp)
  | asked r outputs stamp => rfl
  | timer => rfl
  | received i c F =>
    cases c with
    | block first stamp capture period level slope => rfl
    | answer sent received => rfl
    | ask sent need =>
      cases need with
      | none => rfl
      | some y => rfl

/-- Events that are not handovers leave the level of the next block in
place. -/
theorem foldl_levelStep_level (q : LevelSettings) (l : List (Event H R Payload))
    (st : LevelState) (hl : ∀ e ∈ l, ∀ frames stamp, e.observation ≠ .handed frames stamp) :
    (l.foldl (levelStep q) st).level = st.level := by
  induction l generalizing st with
  | nil => rfl
  | cons e l ih =>
    rw [List.foldl_cons, ih _ fun e' he' => hl e' (List.mem_cons_of_mem e he'),
      levelStep_level q st (hl e List.mem_cons_self)]

variable [DecidableEq H] (p : FixedDelay.Params H) (clockEst : ClockEstimator)
  (deviceEst : DeviceEstimator) (levelRule : LevelRule H R) (w : World H R) (lookahead : ℕ+)

open Classical in
/-- **What a level rule announces with capture block `b` in a run of the
controller**: the level of the block's first frame and its slope, by the
rule at the step that handles the handover of the block; `(0, 0)` if no
step does. -/
def announced (b : ℕ) : ℝ × ℝ :=
  if h : ∃ i, (solution p clockEst deviceEst levelRule : Solution H R Payload).handled w
      lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))
  then levelRule
    (((solution p clockEst deviceEst levelRule : Solution H R Payload).states w lookahead
        (Classical.choose h)).views w.sender
      ++ [⟨(w.clock w.sender).read (w.source.handed b),
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)⟩])
    (w.source.first b)
  else (0, 0)

/-- At a step that handles the handover of block `b`, the level rule gives
what it announces with that block. -/
theorem announced_eq {i b : ℕ}
    (hi : (solution p clockEst deviceEst levelRule : Solution H R Payload).handled w
      lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    levelRule
        (((solution p clockEst deviceEst levelRule : Solution H R Payload).states w lookahead
            i).views w.sender
          ++ [⟨(w.clock w.sender).read (w.source.handed b),
            .handed ((w.source.block b).map fun k => (k, w.target k))
              (w.source.reported b)⟩])
        (w.source.first b)
      = announced p clockEst deviceEst levelRule w lookahead b := by
  classical
  have hex : ∃ i, (solution p clockEst deviceEst levelRule : Solution H R Payload).handled w
      lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)) :=
    ⟨i, hi⟩
  have hu : Classical.choose hex = i := Solution.handed_step_unique _ w lookahead
    (Solution.earliest_of_handled_handed _ w lookahead (Classical.choose_spec hex))
    (Solution.earliest_of_handled_handed _ w lookahead hi)
  unfold announced
  rw [dite_eq_left hex, hu]

/-- **The level rule that steps against the needs is continuous from block
to block**, in every world: when the handovers of blocks `b` and `b + 1`
are both handled, the level announced with block `b + 1` is the level
announced with block `b` plus `blockSize` times the slope announced with
block `b`. -/
theorem announced_steppedLevel_succ (q : LevelSettings) {i i' b : ℕ}
    (hi : (solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).handled w
      lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (hi' : (solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).handled w
      lookahead i' = some (w.sender, w.source.handed (b + 1),
        .handed ((w.source.block (b + 1)).map fun k => (k, w.target k))
          (w.source.reported (b + 1)))) :
    (announced p clockEst deviceEst (steppedLevel q) w lookahead (b + 1)).1
      = (announced p clockEst deviceEst (steppedLevel q) w lookahead b).1
        + (q.blockSize : ℝ)
          * (announced p clockEst deviceEst (steppedLevel q) w lookahead b).2 := by
  rw [← announced_eq p clockEst deviceEst (steppedLevel q) w lookahead hi,
    ← announced_eq p clockEst deviceEst (steppedLevel q) w lookahead hi']
  simp only [steppedLevel, List.dropLast_concat]
  have hE := Solution.earliest_of_handled_handed _ w lookahead hi
  have hE' := Solution.earliest_of_handled_handed _ w lookahead hi'
  obtain ⟨hn1, hn2⟩ := Solution.handedNext_of_earliest _ w lookahead hE
  obtain ⟨hn1', -⟩ := Solution.handedNext_of_earliest _ w lookahead hE'
  have hmono := Solution.handedNext_mono
    (solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload) w lookahead
  have hlt : i < i' := by
    by_contra hcon
    have h1 := hmono (not_lt.mp hcon)
    simp only at h1
    omega
  -- The sender's view at the later handover.
  have hV1 : ((solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).states w
        lookahead (i + 1)).views w.sender
      = ((solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).states w
          lookahead i).views w.sender
        ++ [⟨(w.clock w.sender).read (w.source.handed b),
          .handed ((w.source.block b).map fun k => (k, w.target k))
            (w.source.reported b)⟩] := by
    rw [Solution.views_succ _ w lookahead i w.sender, hi]
    simp
  obtain ⟨mid, hmid, hev⟩ := Solution.views_append w
    (solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload) lookahead
    (show i + 1 ≤ i' from hlt) w.sender
  -- No handover is handled between the two.
  have hno : ∀ e ∈ mid, ∀ frames stamp, e.observation ≠ .handed frames stamp := by
    intro e he frames stamp hobs
    obtain ⟨j, hij, hji', t, obs, hj, rfl⟩ := hev e he
    dsimp only at hobs
    subst hobs
    obtain ⟨b', -, rfl, -, -⟩ := Solution.handled_handed w _ lookahead hj
    have hEj := Solution.earliest_of_handled_handed _ w lookahead hj
    obtain ⟨hj1, hj2⟩ := Solution.handedNext_of_earliest _ w lookahead hEj
    have h1 := hmono hij
    have h2 := hmono (show j + 1 ≤ i' from hji')
    simp only at h1 h2
    omega
  rw [hmid, hV1]
  unfold levelState
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
    foldl_levelStep_level q mid _ hno]
  rfl

/-- **Every slope that the rule announces is at most `slopeMax` in absolute
value**, for `slopeMax ≥ 0`. -/
theorem abs_announced_slope_le (q : LevelSettings) (hq : 0 ≤ q.slopeMax) (b : ℕ) :
    |(announced p clockEst deviceEst (steppedLevel q) w lookahead b).2| ≤ q.slopeMax := by
  classical
  by_cases hex : ∃ i, (solution p clockEst deviceEst (steppedLevel q) :
      Solution H R Payload).handled w lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))
  · obtain ⟨i, hi⟩ := hex
    rw [← announced_eq p clockEst deviceEst (steppedLevel q) w lookahead hi]
    exact abs_slopeTo_le q hq _
  · unfold announced
    rw [dite_eq_right hex, abs_zero]
    exact hq

variable {w} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}

/-- With clocks at constant rates, the run of the controller handles the
handover of every capture block. -/
theorem exists_handover_step (hS : ConstantRates m f d w) (b : ℕ) :
    ∃ i, (solution p clockEst deviceEst levelRule : Solution H R Payload).handled w
      lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)) := by
  have hmore := sendsMore (R := R) p clockEst deviceEst levelRule
  obtain ⟨n, hn⟩ := FixedDelay.progress_of_unbounded p w lookahead hS.handed_unbounded
    hS.asked_unbounded (w.source.handed b)
  rw [← Solution.eventTime_forget w Payload.plain lookahead hmore n] at hn
  obtain ⟨i, -, -, hE⟩ := Solution.exists_handed_step w _ lookahead
    (Solution.lt_handedNext w _ lookahead hn)
  exact ⟨i, Solution.handled_of_handed _ w lookahead hE⟩

/-- **What a speaker plays under the level rule that steps against the
needs.** In the setting of `speaker_plays_of_levels`, with the rule
`steppedLevel q` for the block size of the model: if `slopeMax` is not
negative and less than the time from one frame to the next on the sender's
clock, the three statements of that theorem hold with what the rule
announces (`announced`). -/
theorem speaker_plays_of_steppedLevel (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact)
    (q : LevelSettings) (hqB : q.blockSize = m.blockSize) (hq0 : 0 ≤ q.slopeMax)
    (hq : q.slopeMax < Real.exp (d.logRate m.sender)
      / (m.rate * Real.exp (d.deviceLogRate none)))
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst (steppedLevel q)) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K, ∀ k, K ≤ k →
      (∀ n b, k ∈ (w.speaker r).block b →
        ((solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).states w
          lookahead n).askedNext r = b →
        earliest (((solution p clockEst deviceEst (steppedLevel q) :
              Solution H R Payload).states w lookahead n).key w)
            ((solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).states w
              lookahead n).due = some (.asked r b) →
        ((solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).chosenAt w
            lookahead n r b k = none
          ∨ ∃ x, (solution p clockEst deviceEst (steppedLevel q) :
              Solution H R Payload).chosenAt w lookahead n r b k = some x
            ∧ IsDue m f d w (announced p clockEst deviceEst (steppedLevel q) w lookahead)
              r k x))
      ∧ ((solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).plays w
          lookahead r k = none
        ∨ ∃ x, (solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).plays w
            lookahead r k = some x
          ∧ IsDue m f d w (announced p clockEst deviceEst (steppedLevel q) w lookahead) r k x
          ∧ d.arrival f m.sender (m.host r) (w.source.handed (neededBlock m lookahead x))
            < (w.speaker r).asked (k / m.blockSize))
      ∧ ∀ x, IsDue m f d w (announced p clockEst deviceEst (steppedLevel q) w lookahead)
          r k x →
        d.arrival f m.sender (m.host r) (w.source.handed (neededBlock m lookahead x))
          < (w.speaker r).asked (k / m.blockSize) →
        (solution p clockEst deviceEst (steppedLevel q) : Solution H R Payload).plays w
          lookahead r k = some x := by
  refine speaker_plays_of_levels p hS lookahead hdev (steppedLevel q)
    (announced p clockEst deviceEst (steppedLevel q) w lookahead)
    (fun i b _ hi => announced_eq p clockEst deviceEst (steppedLevel q) w lookahead hi)
    (fun b _ => ?_) (fun b _ => ?_) hps hnodup hcopies r hnos hpsp hline
  · obtain ⟨i, hi⟩ := exists_handover_step p clockEst deviceEst (steppedLevel q) lookahead hS b
    obtain ⟨i', hi'⟩ :=
      exists_handover_step p clockEst deviceEst (steppedLevel q) lookahead hS (b + 1)
    rw [← hqB]
    exact announced_steppedLevel_succ p clockEst deviceEst w lookahead q hi hi'
  · have h1 := abs_le.mp
      (abs_announced_slope_le p clockEst deviceEst w lookahead q hq0 b)
    linarith [h1.1]

end Unisono.Solutions.Controller
