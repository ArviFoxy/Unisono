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
* `levelState_aim`, `sum_needCost_aimAfter_sub_le`: the aim depends on the
  sender's view only through the needs that its clock queries carried, and
  on those needs it costs at most what any fixed level costs, plus a
  constant, plus a term proportional to the step for each need. No world
  model is involved.
* `speaker_plays_of_steppedLevel`: with clocks at constant rates, the
  conclusion of `speaker_plays_of_levels` holds for this rule when
  `slopeMax` is less than the time from one frame to the next on the
  sender's clock.

What a host reports in its clock queries is a parameter of the rule
(`need`); `Unisono.Solutions.Controller.measuredNeed` is a measurement
meant for it. What the rule achieves is not stated here; no cost is
bounded.
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
block's first frame, and the slope that moves the level toward the aim.
What a host reports in a clock query is the parameter `need`. -/
def steppedLevel (q : LevelSettings) (need : H → List (Event H R Payload) → Option ℝ) :
    LevelRule H R :=
  ⟨fun view _ =>
    ((levelState q view.dropLast).level, slopeTo q (levelState q view.dropLast)), need⟩

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

/-- **The aim and the level stay within the bounds.** If both lie between
`q.lo` and `q.hi`, they do after any event, for `q.lo ≤ q.hi` and
`q.slopeMax ≥ 0`: a clock query moves the aim within the bounds, and a
handover moves the level toward the aim and not past it. -/
theorem levelStep_mem (q : LevelSettings) (hq : 0 ≤ q.slopeMax) (hlohi : q.lo ≤ q.hi)
    {st : LevelState} (ha : st.aim ∈ Set.Icc q.lo q.hi) (hl : st.level ∈ Set.Icc q.lo q.hi)
    (e : Event H R Payload) :
    (levelStep q st e).aim ∈ Set.Icc q.lo q.hi
      ∧ (levelStep q st e).level ∈ Set.Icc q.lo q.hi := by
  unfold levelStep
  cases hobs : e.observation with
  | asked r outputs stamp => exact ⟨ha, hl⟩
  | timer => exact ⟨ha, hl⟩
  | received i c F =>
    cases c with
    | block first stamp capture period level slope => exact ⟨ha, hl⟩
    | answer sent received => exact ⟨ha, hl⟩
    | ask sent need =>
      cases need with
      | none => exact ⟨ha, hl⟩
      | some y => exact ⟨clampTo_mem hlohi _, hl⟩
  | handed frames stamp =>
    refine ⟨ha, ?_⟩
    show st.level + (q.blockSize : ℝ) * slopeTo q st ∈ Set.Icc q.lo q.hi
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hl1, hl2⟩ := hl
    have hB0 : (0 : ℝ) ≤ (q.blockSize : ℝ) := Nat.cast_nonneg _
    unfold slopeTo clampTo
    rcases Nat.eq_zero_or_pos q.blockSize with hB | hB
    · rw [hB, Nat.cast_zero, zero_mul, add_zero]
      exact ⟨hl1, hl2⟩
    · have hBpos : (0 : ℝ) < (q.blockSize : ℝ) := by exact_mod_cast hB
      rcases le_total 0 (st.aim - st.level) with h0 | h0
      · -- The aim is above: the level rises, and not past the aim.
        have hv : 0 ≤ (st.aim - st.level) / q.blockSize := div_nonneg h0 hB0
        have h1 : 0 ≤ min q.slopeMax ((st.aim - st.level) / q.blockSize) := le_min hq hv
        rw [max_eq_right (by linarith)]
        have h2 : (q.blockSize : ℝ) * min q.slopeMax ((st.aim - st.level) / q.blockSize)
            ≤ st.aim - st.level := by
          calc (q.blockSize : ℝ) * min q.slopeMax ((st.aim - st.level) / q.blockSize)
              ≤ (q.blockSize : ℝ) * ((st.aim - st.level) / q.blockSize) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hB0
            _ = st.aim - st.level := mul_div_cancel₀ _ hBpos.ne'
        have h3 := mul_nonneg hB0 h1
        constructor <;> linarith
      · -- The aim is below: the level falls, and not past the aim.
        have hv : (st.aim - st.level) / q.blockSize ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg h0 hB0
        rw [min_eq_right (by linarith)]
        have h1 : (st.aim - st.level) / q.blockSize
            ≤ max (-q.slopeMax) ((st.aim - st.level) / q.blockSize) := le_max_right _ _
        have h2 : max (-q.slopeMax) ((st.aim - st.level) / q.blockSize) ≤ 0 :=
          max_le (by linarith) hv
        have h3 : st.aim - st.level
            ≤ (q.blockSize : ℝ) * max (-q.slopeMax) ((st.aim - st.level) / q.blockSize) := by
          calc st.aim - st.level
              = (q.blockSize : ℝ) * ((st.aim - st.level) / q.blockSize) :=
                (mul_div_cancel₀ _ hBpos.ne').symm
            _ ≤ _ := mul_le_mul_of_nonneg_left h1 hB0
        have h4 := mul_nonpos_of_nonneg_of_nonpos hB0 h2
        constructor <;> linarith

/-- After any events, the aim and the level of the rule lie between `q.lo`
and `q.hi`, when the start does, `q.lo ≤ q.hi` and `q.slopeMax ≥ 0`. -/
theorem levelState_mem (q : LevelSettings) (hq : 0 ≤ q.slopeMax) (hlohi : q.lo ≤ q.hi)
    (hstart : q.start ∈ Set.Icc q.lo q.hi) (l : List (Event H R Payload)) :
    (levelState q l).aim ∈ Set.Icc q.lo q.hi ∧ (levelState q l).level ∈ Set.Icc q.lo q.hi := by
  have hgen : ∀ (l : List (Event H R Payload)) (st : LevelState),
      st.aim ∈ Set.Icc q.lo q.hi → st.level ∈ Set.Icc q.lo q.hi →
      (l.foldl (levelStep q) st).aim ∈ Set.Icc q.lo q.hi
        ∧ (l.foldl (levelStep q) st).level ∈ Set.Icc q.lo q.hi := by
    intro l
    induction l with
    | nil => exact fun st ha hl => ⟨ha, hl⟩
    | cons e l ih =>
      intro st ha hl
      obtain ⟨h1, h2⟩ := levelStep_mem q hq hlohi ha hl e
      exact ih _ h1 h2
  exact hgen l _ hstart hstart

/-! ## The aim as a function of the needs that reached the sender -/

/-- The needs that the clock queries in a view carry, oldest first. -/
def needsOf (l : List (Event H R Payload)) : List ℝ :=
  l.filterMap fun e =>
    match e.observation with
    | .received _ (.ask _ (some y)) _ => some y
    | _ => none

/-- One step of the aim `x` for the need `y`. -/
def aimStep (q : LevelSettings) (x y : ℝ) : ℝ :=
  clampTo q.lo q.hi (x - q.step * needSlope q.latencyCost q.lateCost y x)

/-- The aim after the needs `ys`, oldest first. -/
def aimAfter (q : LevelSettings) (ys : List ℝ) : ℝ :=
  ys.foldl (aimStep q) q.start

/-- **The aim depends on the sender's view only through the needs that its
clock queries carried**, in their order. -/
theorem levelState_aim (q : LevelSettings) (l : List (Event H R Payload)) :
    (levelState q l).aim = aimAfter q (needsOf l) := by
  have hgen : ∀ (l : List (Event H R Payload)) (st : LevelState),
      (l.foldl (levelStep q) st).aim = (needsOf l).foldl (aimStep q) st.aim := by
    intro l
    induction l with
    | nil => exact fun st => rfl
    | cons e l ih =>
      intro st
      rw [List.foldl_cons, ih]
      cases hobs : e.observation with
      | handed frames stamp => simp [needsOf, levelStep, hobs]
      | asked r outputs stamp => simp [needsOf, levelStep, hobs]
      | timer => simp [needsOf, levelStep, hobs]
      | received i c F =>
        cases c with
        | block first stamp capture period level slope => simp [needsOf, levelStep, hobs]
        | answer sent received => simp [needsOf, levelStep, hobs]
        | ask sent need =>
          cases need with
          | none => simp [needsOf, levelStep, hobs]
          | some y => simp [needsOf, levelStep, hobs, aimStep]
  exact hgen l _

/-- **The rule against every fixed level, on the needs that reached the
sender.** Let `ys` be needs in the order in which they reached the sender,
with a step `q.step > 0`, bounds `q.lo ≤ q.hi` that hold the start, and
costs `q.latencyCost ≥ 0`, `q.lateCost ≥ 0`. For need number `t`, compare
the cost of the aim that the sender had when the need arrived
(`needCost` at `aimAfter` of the needs before it) with the cost of a fixed
level `z` between the bounds. Summed over all the needs, the aims cost at
most what `z` costs, plus `(q.start - z) ^ 2 / (2 * q.step)`, plus
`q.step * (max q.latencyCost q.lateCost) ^ 2 / 2` for each need. Nothing is
assumed about the needs. -/
theorem sum_needCost_aimAfter_sub_le (q : LevelSettings) (hη : 0 < q.step)
    (hlohi : q.lo ≤ q.hi) (ha : 0 ≤ q.latencyCost) (hc : 0 ≤ q.lateCost)
    (hstart : q.start ∈ Set.Icc q.lo q.hi) (ys : List ℝ) {z : ℝ}
    (hz : z ∈ Set.Icc q.lo q.hi) :
    ∑ t ∈ Finset.range ys.length,
        (Model.Descent.needCost q.latencyCost q.lateCost (ys.getD t 0) (aimAfter q (ys.take t))
          - Model.Descent.needCost q.latencyCost q.lateCost (ys.getD t 0) z)
      ≤ (q.start - z) ^ 2 / (2 * q.step)
        + q.step * max q.latencyCost q.lateCost ^ 2 * ys.length / 2 := by
  -- The aims as a sequence, continued past the last need with needs of zero.
  obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → ℝ, x 0 = q.start
      ∧ ∀ t, x (t + 1) = aimStep q (x t) (ys.getD t 0) :=
    ⟨fun t => Nat.rec q.start (fun t xt => aimStep q xt (ys.getD t 0)) t, rfl, fun _ => rfl⟩
  have hxt : ∀ t, t ≤ ys.length → x t = aimAfter q (ys.take t) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [hx0]
      rfl
    | succ t ih =>
      intro ht
      have hlt : t < ys.length := ht
      rw [hxs, ih hlt.le, List.take_add_one, List.getElem?_eq_getElem hlt]
      unfold aimAfter
      rw [List.foldl_append]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  have h := Model.Descent.sum_needCost_sub_le (d := 0) (x := x)
    (y := fun t => ys.getD t 0) hη hlohi ha hc hstart
    (fun t ht => by
      have h0 : t = 0 := Nat.le_zero.mp ht
      rw [h0, hx0])
    (fun t => hxs t) hz ys.length
  have hsum : ∑ t ∈ Finset.range ys.length,
        (Model.Descent.needCost q.latencyCost q.lateCost (ys.getD t 0)
            (aimAfter q (ys.take t))
          - Model.Descent.needCost q.latencyCost q.lateCost (ys.getD t 0) z)
      = ∑ t ∈ Finset.range ys.length,
        (Model.Descent.needCost q.latencyCost q.lateCost (ys.getD t 0) (x t)
          - Model.Descent.needCost q.latencyCost q.lateCost (ys.getD t 0) z) :=
    Finset.sum_congr rfl fun t ht => by
      rw [hxt t (Finset.mem_range.mp ht).le]
  rw [hsum]
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

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
  then levelRule.announce
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
    levelRule.announce
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
theorem announced_steppedLevel_succ (q : LevelSettings)
    (need : H → List (Event H R Payload) → Option ℝ) {i i' b : ℕ}
    (hi : (solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).handled w
      lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (hi' : (solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).handled w
      lookahead i' = some (w.sender, w.source.handed (b + 1),
        .handed ((w.source.block (b + 1)).map fun k => (k, w.target k))
          (w.source.reported (b + 1)))) :
    (announced p clockEst deviceEst (steppedLevel q need) w lookahead (b + 1)).1
      = (announced p clockEst deviceEst (steppedLevel q need) w lookahead b).1
        + (q.blockSize : ℝ)
          * (announced p clockEst deviceEst (steppedLevel q need) w lookahead b).2 := by
  rw [← announced_eq p clockEst deviceEst (steppedLevel q need) w lookahead hi,
    ← announced_eq p clockEst deviceEst (steppedLevel q need) w lookahead hi']
  show (levelState q (_ ++ [_]).dropLast).level
    = (levelState q (_ ++ [_]).dropLast).level
      + (q.blockSize : ℝ) * slopeTo q (levelState q (_ ++ [_]).dropLast)
  simp only [List.dropLast_concat]
  have hE := Solution.earliest_of_handled_handed _ w lookahead hi
  have hE' := Solution.earliest_of_handled_handed _ w lookahead hi'
  obtain ⟨hn1, hn2⟩ := Solution.handedNext_of_earliest _ w lookahead hE
  obtain ⟨hn1', -⟩ := Solution.handedNext_of_earliest _ w lookahead hE'
  have hmono := Solution.handedNext_mono
    (solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload) w lookahead
  have hlt : i < i' := by
    by_contra hcon
    have h1 := hmono (not_lt.mp hcon)
    simp only at h1
    omega
  -- The sender's view at the later handover.
  have hV1 : ((solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).states w
        lookahead (i + 1)).views w.sender
      = ((solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).states w
          lookahead i).views w.sender
        ++ [⟨(w.clock w.sender).read (w.source.handed b),
          .handed ((w.source.block b).map fun k => (k, w.target k))
            (w.source.reported b)⟩] := by
    rw [Solution.views_succ _ w lookahead i w.sender, hi]
    simp
  obtain ⟨mid, hmid, hev⟩ := Solution.views_append w
    (solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload) lookahead
    (show i + 1 ≤ i' from hlt) w.sender
  -- No handover is handled between the two.
  have hno : ∀ e ∈ mid, ∀ frames stamp, e.observation ≠ .handed frames stamp := by
    intro e he frames stamp hobs
    obtain ⟨j, hij, hji', t, obs, hj, rfl⟩ := hev e he
    dsimp only at hobs
    subst hobs
    obtain ⟨b', -, -, rfl, -⟩ := Solution.handled_handed w _ lookahead hj
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
theorem abs_announced_slope_le (q : LevelSettings)
    (need : H → List (Event H R Payload) → Option ℝ) (hq : 0 ≤ q.slopeMax) (b : ℕ) :
    |(announced p clockEst deviceEst (steppedLevel q need) w lookahead b).2| ≤ q.slopeMax := by
  classical
  by_cases hex : ∃ i, (solution p clockEst deviceEst (steppedLevel q need) :
      Solution H R Payload).handled w lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))
  · obtain ⟨i, hi⟩ := hex
    rw [← announced_eq p clockEst deviceEst (steppedLevel q need) w lookahead hi]
    exact abs_slopeTo_le q hq _
  · unfold announced
    rw [dite_eq_right hex, abs_zero]
    exact hq

/-- **Every level that the rule announces at a handover lies between `q.lo`
and `q.hi`**, when the start does, `q.lo ≤ q.hi` and `q.slopeMax ≥ 0`. -/
theorem announced_fst_mem (q : LevelSettings)
    (need : H → List (Event H R Payload) → Option ℝ) (hq : 0 ≤ q.slopeMax)
    (hlohi : q.lo ≤ q.hi) (hstart : q.start ∈ Set.Icc q.lo q.hi) {i b : ℕ}
    (hi : (solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).handled
      w lookahead i = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    (announced p clockEst deviceEst (steppedLevel q need) w lookahead b).1
      ∈ Set.Icc q.lo q.hi := by
  rw [← announced_eq p clockEst deviceEst (steppedLevel q need) w lookahead hi]
  exact (levelState_mem q hq hlohi hstart _).2

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
    (q : LevelSettings) (need : H → List (Event H R Payload) → Option ℝ)
    (hqB : q.blockSize = m.blockSize) (hq0 : 0 ≤ q.slopeMax)
    (hq : q.slopeMax < Real.exp (d.logRate m.sender)
      / (m.rate * Real.exp (d.deviceLogRate none)))
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst (steppedLevel q need)) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K, ∀ k, K ≤ k →
      (∀ n b, k ∈ (w.speaker r).block b →
        ((solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).states w
          lookahead n).askedNext r = b →
        earliest (((solution p clockEst deviceEst (steppedLevel q need) :
              Solution H R Payload).states w lookahead n).key w)
            ((solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).states w
              lookahead n).due = some (.asked r b) →
        ((solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).chosenAt w
            lookahead n r b k = none
          ∨ ∃ x, (solution p clockEst deviceEst (steppedLevel q need) :
              Solution H R Payload).chosenAt w lookahead n r b k = some x
            ∧ IsDue m f d w (announced p clockEst deviceEst (steppedLevel q need) w lookahead)
              r k x))
      ∧ ((solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).plays w
          lookahead r k = none
        ∨ ∃ x, (solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).plays w
            lookahead r k = some x
          ∧ IsDue m f d w (announced p clockEst deviceEst (steppedLevel q need) w lookahead) r k x
          ∧ d.arrival f m.sender (m.host r) (w.source.handed (neededBlock m lookahead x))
            < (w.speaker r).asked (k / m.blockSize))
      ∧ ∀ x, IsDue m f d w (announced p clockEst deviceEst (steppedLevel q need) w lookahead)
          r k x →
        d.arrival f m.sender (m.host r) (w.source.handed (neededBlock m lookahead x))
          < (w.speaker r).asked (k / m.blockSize) →
        (solution p clockEst deviceEst (steppedLevel q need) : Solution H R Payload).plays w
          lookahead r k = some x := by
  refine speaker_plays_of_levels p hS lookahead hdev (steppedLevel q need)
    (announced p clockEst deviceEst (steppedLevel q need) w lookahead)
    (fun i b _ hi => announced_eq p clockEst deviceEst (steppedLevel q need) w lookahead hi)
    (fun b _ => ?_) (fun b _ => ?_) hps hnodup hcopies r hnos hpsp hline
  · obtain ⟨i, hi⟩ := exists_handover_step p clockEst deviceEst (steppedLevel q need) lookahead hS b
    obtain ⟨i', hi'⟩ :=
      exists_handover_step p clockEst deviceEst (steppedLevel q need) lookahead hS (b + 1)
    rw [← hqB]
    exact announced_steppedLevel_succ p clockEst deviceEst w lookahead q need hi hi'
  · have h1 := abs_le.mp
      (abs_announced_slope_le p clockEst deviceEst w lookahead q need hq0 b)
    linarith [h1.1]

end Unisono.Solutions.Controller
