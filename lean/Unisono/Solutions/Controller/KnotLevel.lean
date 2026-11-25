/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Knots
public import Unisono.Solutions.Controller.SteppedLevel

/-!
# A level rule whose schedule always advances

The position that is due when the sender's clock reads `s` is the one whose
capture time plus level is `s`. For that position to be unique, capture
time plus level has to increase with the position: within every block, the
time from one frame to the next plus the change of the level from one frame
to the next has to be positive. The rule `steppedLevel` limits the change
of the level by a fixed number, which is less than the time from one frame
to the next only while the sender's clock and the capture device run at
ordinary rates.

`knotLevel` is the same rule with one more limit: within a block the level
changes, from one frame to the next, by at most the share `share` of the
block's time from one frame to the next on the schedule of the knots
(`World.knotPeriod`). The sender knows that time at the handover, from the
readings of its clock at this handover and at the one before. For
`0 ≤ share < 1` the schedule then advances in every block of every world.

For the run of any solution in any world, with `announcedAt` the level and
the slope that the rule gives at the handover of a block:

* `announcedAt_succ`: the rule is continuous from block to block.
* `abs_announcedAt_slope_le`: the slope of block `b` is at most `share`
  times the block's time from one frame to the next, in absolute value, and
  at most `q.slopeMax`.
* `knotPeriod_add_slope_pos`: **the schedule advances in every block**: the
  time from one frame to the next plus the slope is at least `1 - share`
  times that time, which is positive.
* `announcedAt_fst_mem`: the level lies between `q.lo` and `q.hi`.
* `knotLevelState_aim`: the aim depends on the sender's view only through
  the needs that its clock queries carried; it is the aim of
  `steppedLevel`, so `sum_needCost_aimAfter_sub_le` applies to it.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Model.Descent

variable {H : Type} {R : ℕ}

/-- What the level rule remembers: the level that it aims at, the level of
the first frame of the next block, and the knot of the last block handed
over with its advance (`knotStep`), if a block was handed over. -/
structure KnotLevelState where
  aim : ℝ
  level : ℝ
  knot : Option (ℝ × ℝ)

/-- The time from one frame to the next, on the schedule of the knots, of a
block of `count` frames that is handed over when the sender's clock reads
`σ`, given the knot `prev` of the block before and its advance, if there
was one: the advance of the block's knot (`knotStep`) divided by the number
of frames. -/
def periodFrom (nominal : ℝ) (prev : Option (ℝ × ℝ)) (σ : ℝ) (count : ℕ) : ℝ :=
  (knotStep nominal prev σ count).2 / count

/-- The largest change of the level from one frame to the next that the
rule allows in a block whose time from one frame to the next is `period`:
`q.slopeMax` or `share * period`, whichever is less, and never less than
zero. -/
def slopeLimit (q : LevelSettings) (share period : ℝ) : ℝ :=
  max 0 (min q.slopeMax (share * period))

/-- The change of the level from one frame to the next that the rule
announces for a block of `count` frames: the change that would reach the
aim at the end of the block, cut to at most `slopeLimit` in absolute
value. -/
def knotSlope (q : LevelSettings) (share aim level : ℝ) (count : ℕ) (period : ℝ) : ℝ :=
  clampTo (-slopeLimit q share period) (slopeLimit q share period) ((aim - level) / count)

/-- How an event at the sender changes what the level rule remembers. A
clock query that carries a need moves the aim one step, as in
`steppedLevel`. A handover moves the level to the end of the block and
records the knot of the block. Other events change nothing. -/
def knotLevelStep (q : LevelSettings) (share nominal : ℝ) (st : KnotLevelState)
    (e : Event H R Payload) : KnotLevelState :=
  match e.observation with
  | .received _ (.ask _ (some y)) _ => ⟨aimStep q st.aim y, st.level, st.knot⟩
  | .handed frames _ =>
      ⟨st.aim,
        st.level + frames.length * knotSlope q share st.aim st.level frames.length
          (periodFrom nominal st.knot e.reading frames.length),
        some (knotStep nominal st.knot e.reading frames.length)⟩
  | _ => st

/-- What the level rule remembers after the events `l` at the sender. -/
def knotLevelState (q : LevelSettings) (share nominal : ℝ) (l : List (Event H R Payload)) :
    KnotLevelState :=
  l.foldl (knotLevelStep q share nominal) ⟨q.start, q.start, none⟩

/-- **The level rule for the schedule of the knots.** At a handover, from
the sender's view up to and including the handover: the level of the left
end of the block, and the slope that moves the level toward the aim within
the limit for the block. What a host reports in a clock query is the
parameter `need`. -/
def knotLevel (q : LevelSettings) (share nominal : ℝ)
    (need : H → List (Event H R Payload) → Option ℝ) : LevelRule H R :=
  ⟨fun view _ =>
    match view.getLast? with
    | some e =>
        match e.observation with
        | .handed frames _ =>
            ((knotLevelState q share nominal view.dropLast).level,
              knotSlope q share (knotLevelState q share nominal view.dropLast).aim
                (knotLevelState q share nominal view.dropLast).level frames.length
                (periodFrom nominal (knotLevelState q share nominal view.dropLast).knot
                  e.reading frames.length))
        | _ => ((knotLevelState q share nominal view.dropLast).level, 0)
    | none => (q.start, 0), need⟩

theorem slopeLimit_nonneg (q : LevelSettings) (share period : ℝ) :
    0 ≤ slopeLimit q share period := le_max_left _ _

/-- The slope is at most the limit in absolute value. -/
theorem abs_knotSlope_le (q : LevelSettings) (share aim level : ℝ) (count : ℕ) (period : ℝ) :
    |knotSlope q share aim level count period| ≤ slopeLimit q share period := by
  have h := clampTo_mem (lo := -slopeLimit q share period) (hi := slopeLimit q share period)
    (by linarith [slopeLimit_nonneg q share period]) ((aim - level) / count)
  exact abs_le.mpr ⟨h.1, h.2⟩

/-- **A block's worth of slope moves the level toward the aim and not past
it.** -/
theorem knotSlope_between (q : LevelSettings) (share aim level : ℝ) (count : ℕ) (period : ℝ) :
    (level ≤ aim → level ≤ level + count * knotSlope q share aim level count period
        ∧ level + count * knotSlope q share aim level count period ≤ aim)
      ∧ (aim ≤ level → aim ≤ level + count * knotSlope q share aim level count period
        ∧ level + count * knotSlope q share aim level count period ≤ level) := by
  have hm := slopeLimit_nonneg q share period
  have hB0 : (0 : ℝ) ≤ (count : ℝ) := Nat.cast_nonneg _
  unfold knotSlope clampTo
  rcases Nat.eq_zero_or_pos count with hB | hB
  · subst hB
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact ⟨fun h => ⟨le_rfl, h⟩, fun h => ⟨h, le_rfl⟩⟩
  · have hBpos : (0 : ℝ) < (count : ℝ) := by exact_mod_cast hB
    constructor
    · intro h0
      have hv : 0 ≤ (aim - level) / count := div_nonneg (by linarith) hB0
      have h1 : 0 ≤ min (slopeLimit q share period) ((aim - level) / count) := le_min hm hv
      rw [max_eq_right (by linarith)]
      have h2 : (count : ℝ) * min (slopeLimit q share period) ((aim - level) / count)
          ≤ aim - level := by
        calc (count : ℝ) * min (slopeLimit q share period) ((aim - level) / count)
            ≤ (count : ℝ) * ((aim - level) / count) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hB0
          _ = aim - level := mul_div_cancel₀ _ hBpos.ne'
      have h3 := mul_nonneg hB0 h1
      constructor <;> linarith
    · intro h0
      have hv : (aim - level) / count ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hB0
      rw [min_eq_right (by linarith)]
      have h1 : (aim - level) / count
          ≤ max (-slopeLimit q share period) ((aim - level) / count) := le_max_right _ _
      have h2 : max (-slopeLimit q share period) ((aim - level) / count) ≤ 0 :=
        max_le (by linarith) hv
      have h3 : aim - level
          ≤ (count : ℝ) * max (-slopeLimit q share period) ((aim - level) / count) := by
        calc aim - level
            = (count : ℝ) * ((aim - level) / count) := (mul_div_cancel₀ _ hBpos.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 hB0
      have h4 := mul_nonpos_of_nonneg_of_nonpos hB0 h2
      constructor <;> linarith

/-- What the rule remembers after one more event. -/
theorem knotLevelState_concat (q : LevelSettings) (share nominal : ℝ)
    (l : List (Event H R Payload)) (e : Event H R Payload) :
    knotLevelState q share nominal (l ++ [e])
      = knotLevelStep q share nominal (knotLevelState q share nominal l) e := by
  unfold knotLevelState
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- An event that is not a handover leaves the level of the next block and
the recorded reading in place. -/
theorem knotLevelStep_level (q : LevelSettings) (share nominal : ℝ) (st : KnotLevelState)
    {e : Event H R Payload} (he : ∀ frames stamp, e.observation ≠ .handed frames stamp) :
    (knotLevelStep q share nominal st e).level = st.level
      ∧ (knotLevelStep q share nominal st e).knot = st.knot := by
  unfold knotLevelStep
  cases hobs : e.observation with
  | handed frames stamp => exact absurd hobs (he frames stamp)
  | asked r outputs stamp => exact ⟨rfl, rfl⟩
  | timer => exact ⟨rfl, rfl⟩
  | received i c F =>
    cases c with
    | block first stamp capture period level slope => exact ⟨rfl, rfl⟩
    | answer sent received => exact ⟨rfl, rfl⟩
    | ask sent need =>
      cases need with
      | none => exact ⟨rfl, rfl⟩
      | some y => exact ⟨rfl, rfl⟩

/-- Events that are not handovers leave the level of the next block and the
recorded reading in place. -/
theorem foldl_knotLevelStep_level (q : LevelSettings) (share nominal : ℝ)
    (l : List (Event H R Payload)) (st : KnotLevelState)
    (hl : ∀ e ∈ l, ∀ frames stamp, e.observation ≠ .handed frames stamp) :
    (l.foldl (knotLevelStep q share nominal) st).level = st.level
      ∧ (l.foldl (knotLevelStep q share nominal) st).knot = st.knot := by
  induction l generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons e l ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (knotLevelStep q share nominal st e)
      fun e' he' => hl e' (List.mem_cons_of_mem e he')
    obtain ⟨h3, h4⟩ := knotLevelStep_level q share nominal st (hl e List.mem_cons_self)
    exact ⟨h1.trans h3, h2.trans h4⟩

/-- Events that are not handovers, after the events `l`, leave the level of
the next block in place. -/
theorem knotLevelState_append_level (q : LevelSettings) (share nominal : ℝ)
    (l mid : List (Event H R Payload))
    (hl : ∀ e ∈ mid, ∀ frames stamp, e.observation ≠ .handed frames stamp) :
    (knotLevelState q share nominal (l ++ mid)).level
      = (knotLevelState q share nominal l).level := by
  unfold knotLevelState
  rw [List.foldl_append]
  exact (foldl_knotLevelStep_level q share nominal mid _ hl).1

/-- **The recorded knot is the knot after the handovers of the view.** -/
theorem knotLevelState_knot (q : LevelSettings) (share nominal : ℝ)
    (l : List (Event H R Payload)) :
    (knotLevelState q share nominal l).knot = knotsOf nominal (handoversOf l) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    rw [knotLevelState_concat, handoversOf_append]
    cases hobs : e.observation with
    | handed frames stamp =>
      have h1 : handoversOf [e] = [e] := by simp [handoversOf, hobs]
      rw [h1, knotsOf_concat, ← ih]
      simp [knotLevelStep, hobs, handedCount]
    | asked r outputs stamp =>
      have h1 : handoversOf [e] = [] := by simp [handoversOf, hobs]
      rw [h1, List.append_nil, ← ih]
      exact (knotLevelStep_level q share nominal _ (by simp [hobs])).2
    | timer =>
      have h1 : handoversOf [e] = [] := by simp [handoversOf, hobs]
      rw [h1, List.append_nil, ← ih]
      exact (knotLevelStep_level q share nominal _ (by simp [hobs])).2
    | received i c F =>
      have h1 : handoversOf [e] = [] := by simp [handoversOf, hobs]
      rw [h1, List.append_nil, ← ih]
      exact (knotLevelStep_level q share nominal _ (by simp [hobs])).2

/-- **The aim and the level stay within the bounds.** If both lie between
`q.lo` and `q.hi`, they do after any event, for `q.lo ≤ q.hi`. -/
theorem knotLevelStep_mem (q : LevelSettings) (share nominal : ℝ) (hlohi : q.lo ≤ q.hi)
    {st : KnotLevelState} (ha : st.aim ∈ Set.Icc q.lo q.hi)
    (hl : st.level ∈ Set.Icc q.lo q.hi) (e : Event H R Payload) :
    (knotLevelStep q share nominal st e).aim ∈ Set.Icc q.lo q.hi
      ∧ (knotLevelStep q share nominal st e).level ∈ Set.Icc q.lo q.hi := by
  unfold knotLevelStep
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
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hl1, hl2⟩ := hl
    obtain ⟨hup, hdown⟩ := knotSlope_between q share st.aim st.level frames.length
      (periodFrom nominal st.knot e.reading frames.length)
    rcases le_total st.level st.aim with h | h
    · obtain ⟨h1, h2⟩ := hup h
      exact ⟨by linarith, by linarith⟩
    · obtain ⟨h1, h2⟩ := hdown h
      exact ⟨by linarith, by linarith⟩

/-- After any events, the aim and the level of the rule lie between `q.lo`
and `q.hi`, when the start does and `q.lo ≤ q.hi`. -/
theorem knotLevelState_mem (q : LevelSettings) (share nominal : ℝ) (hlohi : q.lo ≤ q.hi)
    (hstart : q.start ∈ Set.Icc q.lo q.hi) (l : List (Event H R Payload)) :
    (knotLevelState q share nominal l).aim ∈ Set.Icc q.lo q.hi
      ∧ (knotLevelState q share nominal l).level ∈ Set.Icc q.lo q.hi := by
  have hgen : ∀ (l : List (Event H R Payload)) (st : KnotLevelState),
      st.aim ∈ Set.Icc q.lo q.hi → st.level ∈ Set.Icc q.lo q.hi →
      (l.foldl (knotLevelStep q share nominal) st).aim ∈ Set.Icc q.lo q.hi
        ∧ (l.foldl (knotLevelStep q share nominal) st).level ∈ Set.Icc q.lo q.hi := by
    intro l
    induction l with
    | nil => exact fun st ha hl => ⟨ha, hl⟩
    | cons e l ih =>
      intro st ha hl
      obtain ⟨h1, h2⟩ := knotLevelStep_mem q share nominal hlohi ha hl e
      exact ih _ h1 h2
  exact hgen l _ hstart hstart

/-- **The aim depends on the sender's view only through the needs that its
clock queries carried**, in their order; it is the aim of `steppedLevel`. -/
theorem knotLevelState_aim (q : LevelSettings) (share nominal : ℝ)
    (l : List (Event H R Payload)) :
    (knotLevelState q share nominal l).aim = aimAfter q (needsOf l) := by
  have hgen : ∀ (l : List (Event H R Payload)) (st : KnotLevelState),
      (l.foldl (knotLevelStep q share nominal) st).aim
        = (needsOf l).foldl (aimStep q) st.aim := by
    intro l
    induction l with
    | nil => exact fun st => rfl
    | cons e l ih =>
      intro st
      rw [List.foldl_cons, ih]
      cases hobs : e.observation with
      | handed frames stamp => simp [needsOf, knotLevelStep, hobs]
      | asked r outputs stamp => simp [needsOf, knotLevelStep, hobs]
      | timer => simp [needsOf, knotLevelStep, hobs]
      | received i c F =>
        cases c with
        | block first stamp capture period level slope => simp [needsOf, knotLevelStep, hobs]
        | answer sent received => simp [needsOf, knotLevelStep, hobs]
        | ask sent need =>
          cases need with
          | none => simp [needsOf, knotLevelStep, hobs]
          | some y => simp [needsOf, knotLevelStep, hobs]
  exact hgen l _

/-! ## The rule along a run -/

variable [DecidableEq H] (σ : Solution H R Payload) (w : World H R) (lookahead : ℕ+)

/-- What the rule `knotLevel` announces with block `b` in the run of `σ`:
the rule at the sender's view when it handles the handover of `b`. -/
def announcedAt (q : LevelSettings) (share nominal : ℝ) (b : ℕ) : ℝ × ℝ :=
  (knotLevel q share nominal (fun (_ : H) _ => none)).announce
    (σ.handoverView w lookahead b) (w.source.first b)

/-- The sender's view just before it handles the handover of block `b`. -/
theorem handoverView_dropLast {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    (σ.handoverView w lookahead b).dropLast = (σ.states w lookahead i).views w.sender
      ∧ (σ.handoverView w lookahead b).getLast? = some (w.handedEvent b) := by
  rw [σ.handoverView_eq w lookahead hi]
  exact ⟨List.dropLast_concat, by simp⟩

/-- **What the rule announces at a handover.** When the run handles the
handover of block `b`: the level that the rule has reached, and the slope
toward its aim within the limit for the block's time from one frame to the
next on the schedule of the knots. -/
theorem announcedAt_eq (q : LevelSettings) (share nominal : ℝ) {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    announcedAt σ w lookahead q share nominal b
      = ((knotLevelState q share nominal ((σ.states w lookahead i).views w.sender)).level,
        knotSlope q share
          (knotLevelState q share nominal ((σ.states w lookahead i).views w.sender)).aim
          (knotLevelState q share nominal ((σ.states w lookahead i).views w.sender)).level
          (w.blockLength b) (w.knotPeriod nominal b)) := by
  obtain ⟨hdrop, hlast⟩ := handoverView_dropLast σ w lookahead hi
  have hE := σ.earliest_of_handled_handed w lookahead hi
  obtain ⟨hn, -⟩ := σ.handedNext_of_earliest w lookahead hE
  have hlen : ((w.source.block b).map fun k => (k, w.target k)).length = w.blockLength b := by
    simp [CaptureDevice.block, World.blockLength]
  have hknot : (knotLevelState q share nominal ((σ.states w lookahead i).views w.sender)).knot
      = knotsOf nominal ((List.range b).map (w.handedEvent : ℕ → Event H R Payload)) := by
    rw [knotLevelState_knot, σ.handoversOf_views w lookahead i, hn]
  have hperiod : periodFrom nominal
      (knotLevelState q share nominal ((σ.states w lookahead i).views w.sender)).knot
      (w.handedEvent b : Event H R Payload).reading (w.blockLength b)
      = w.knotPeriod nominal b := by
    rw [hknot]
    unfold periodFrom
    show (knotStep nominal _ (w.handedReading b) (w.blockLength b)).2 / _ = _
    rw [knotStep_knotsOf_range]
    rfl
  unfold announcedAt knotLevel
  simp only [hlast, hdrop]
  show (_, knotSlope q share _ _
      ((w.source.block b).map fun k => (k, w.target k)).length
      (periodFrom nominal _ (w.handedEvent b : Event H R Payload).reading
        ((w.source.block b).map fun k => (k, w.target k)).length)) = _
  rw [hlen, hperiod]

/-- **The rule is continuous from block to block**, in every world: when
the handovers of blocks `b` and `b + 1` are both handled, the level
announced with block `b + 1` is the level announced with block `b` plus the
number of frames of block `b` times the slope announced with block `b`. -/
theorem announcedAt_succ (q : LevelSettings) (share nominal : ℝ) {i i' b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (hi' : σ.handled w lookahead i' = some (w.sender, w.source.handed (b + 1),
      .handed ((w.source.block (b + 1)).map fun k => (k, w.target k))
        (w.source.reported (b + 1)))) :
    (announcedAt σ w lookahead q share nominal (b + 1)).1
      = (announcedAt σ w lookahead q share nominal b).1
        + (w.blockLength b : ℝ) * (announcedAt σ w lookahead q share nominal b).2 := by
  rw [announcedAt_eq σ w lookahead q share nominal hi,
    announcedAt_eq σ w lookahead q share nominal hi']
  obtain ⟨mid, hmid, hno⟩ := σ.handoverView_succ w lookahead hi hi'
  rw [σ.handoverView_eq w lookahead hi, σ.handoverView_eq w lookahead hi'] at hmid
  have hviews : (σ.states w lookahead i').views w.sender
      = ((σ.states w lookahead i).views w.sender ++ [w.handedEvent b]) ++ mid :=
    List.append_cancel_right hmid
  have hlen : ((w.source.block b).map fun k => (k, w.target k)).length = w.blockLength b := by
    simp [CaptureDevice.block, World.blockLength]
  have hE := σ.earliest_of_handled_handed w lookahead hi
  obtain ⟨hn, -⟩ := σ.handedNext_of_earliest w lookahead hE
  have hknot : (knotLevelState q share nominal ((σ.states w lookahead i).views w.sender)).knot
      = knotsOf nominal ((List.range b).map (w.handedEvent : ℕ → Event H R Payload)) := by
    rw [knotLevelState_knot, σ.handoversOf_views w lookahead i, hn]
  have hperiod : periodFrom nominal
      (knotLevelState q share nominal ((σ.states w lookahead i).views w.sender)).knot
      (w.handedEvent b : Event H R Payload).reading (w.blockLength b)
      = w.knotPeriod nominal b := by
    rw [hknot]
    unfold periodFrom
    show (knotStep nominal _ (w.handedReading b) (w.blockLength b)).2 / _ = _
    rw [knotStep_knotsOf_range]
    rfl
  show (knotLevelState q share nominal ((σ.states w lookahead i').views w.sender)).level = _
  rw [hviews, knotLevelState_append_level q share nominal _ mid hno, knotLevelState_concat]
  show (knotLevelState q share nominal ((σ.states w lookahead i).views w.sender)).level
      + (((w.source.block b).map fun k => (k, w.target k)).length : ℝ)
        * knotSlope q share _ _ ((w.source.block b).map fun k => (k, w.target k)).length
          (periodFrom nominal _ (w.handedEvent b : Event H R Payload).reading
            ((w.source.block b).map fun k => (k, w.target k)).length) = _
  rw [hlen, hperiod]

/-- **The slope of a block is within the limit for the block.** When the
run handles the handover of block `b`, the slope that the rule announces is
at most `slopeLimit` for the block's time from one frame to the next on the
schedule of the knots, in absolute value. -/
theorem abs_announcedAt_slope_le (q : LevelSettings) (share nominal : ℝ) {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    |(announcedAt σ w lookahead q share nominal b).2|
      ≤ slopeLimit q share (w.knotPeriod nominal b) := by
  rw [announcedAt_eq σ w lookahead q share nominal hi]
  exact abs_knotSlope_le q share _ _ _ _

/-- **The schedule advances in every block.** For `0 ≤ share < 1` and a
positive time from one frame to the next for the first block: when the run
handles the handover of block `b`, the block's time from one frame to the
next on the schedule of the knots, plus the slope that the rule announces,
is at least `1 - share` times that time, which is positive. This holds in
every world. -/
theorem knotPeriod_add_slope_pos (q : LevelSettings) {share nominal : ℝ} (hs0 : 0 ≤ share)
    (hs1 : share < 1) (hnominal : 0 < nominal) {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    0 < (1 - share) * w.knotPeriod nominal b
      ∧ (1 - share) * w.knotPeriod nominal b
        ≤ w.knotPeriod nominal b + (announcedAt σ w lookahead q share nominal b).2 := by
  have hp := w.knotPeriod_pos hnominal b
  have habs := abs_announcedAt_slope_le σ w lookahead q share nominal hi
  have hlim : slopeLimit q share (w.knotPeriod nominal b) ≤ share * w.knotPeriod nominal b := by
    unfold slopeLimit
    exact max_le (mul_nonneg hs0 hp.le) (min_le_right _ _)
  have h1 := (abs_le.mp habs).1
  exact ⟨mul_pos (by linarith) hp, by nlinarith⟩

/-- **Every level that the rule announces at a handover lies between `q.lo`
and `q.hi`**, when the start does and `q.lo ≤ q.hi`. -/
theorem announcedAt_fst_mem (q : LevelSettings) (share nominal : ℝ) (hlohi : q.lo ≤ q.hi)
    (hstart : q.start ∈ Set.Icc q.lo q.hi) {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    (announcedAt σ w lookahead q share nominal b).1 ∈ Set.Icc q.lo q.hi := by
  rw [announcedAt_eq σ w lookahead q share nominal hi]
  exact (knotLevelState_mem q share nominal hlohi hstart _).2

end Unisono.Solutions.Controller
