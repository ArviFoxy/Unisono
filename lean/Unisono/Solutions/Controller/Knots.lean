/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Ruled
public import Unisono.Solutions.Controller.Schedule
public import Unisono.Model.Descent

/-!
# A capture schedule from the sender's readings at handovers

The sender's host handles each handover of the capture device at some
reading of its own clock (`World.handedReading`). The capture device hands
a block over when the block's last frame is captured, and the host handles
the handover then or, when it is busy, later. This file makes a schedule of
capture times from those readings and from the timestamps of the blocks,
with no estimate.

The schedule counts positions from one frame before the frames of the
source: its coordinate `z` stands for the position `z - 1`. In that
coordinate block `b` covers the coordinates from its first frame to just
before the first frame of the next block. Its left end stands for the last
frame of block `b - 1`, and its right end stands for its own last frame.

**The knots.** The schedule has a knot for each block (`World.knot`): the
reading of the sender's clock at which it puts the block's right end. The
settings (`KnotSettings`) are the nominal time from one frame to the next,
a bound `bound` between zero and one, and a slack.

* The knot of a block aims at the block's input (`knotInput`,
  `World.knotInput`): the reading at the block's handover, or, if that is
  less, the block's timestamp plus the nominal time of the block's frames,
  longer by the share `bound`, plus the slack. The timestamp belongs to the
  block's first frame, so the second value is about when the block's last
  frame was captured, also when the host handled the handover late.
* The knot of block zero is its input. After that a knot advances over the
  knot before by the distance to its input, kept between the nominal time of
  the block's frames shorter by the share `bound` and that time longer by
  the share `bound` (`knotStep`).

So **every block's time from one frame to the next is within the share
`bound` of the nominal one** (`World.knotPeriod_mem`), in every world: the
schedule never compresses blocks whose handovers were handled together and
never stretches a block across a pause. The knot is its input whenever the
input lies that far after the knot before
(`World.knot_succ_eq_knotInput`); otherwise the knot moves toward its input
at the largest or the least allowed advance.

* Every knot is later than the knot before (`World.knot_strictMono`).
* Within block `b ≥ 1` the schedule is the line from the knot of block
  `b - 1`, at the left end, to the knot of block `b`, at the right end
  (`World.knotStart`, `World.knotPeriod`). Block zero has no knot before it;
  its line ends at its own knot and has the nominal time from one frame to
  the next.
* **The schedule is continuous from block to block**: every block starts at
  the value at which the block before it ends, which is the knot between
  them (`World.knotStart_succ`, `World.knotStart_add`).
* `knotCapture` computes the schedule of a block from the sender's view at
  its handover, and in the run of any solution in any world it gives the
  line above (`knotCapture_eq`). The header of a block gives the line in
  two parts (`runHeader_knots`): a line that ends at the reading of the
  handover, so that a host that receives the block knows the reading of the
  sender's clock at which the block was sent, and the time by which the knot
  is later than that reading, which is added to the level.
* `ruled_chosen_knots`: when a host of the controller with this capture
  schedule chooses a position, the value of the schedule at that position
  plus the announced level of that position is the host's estimate of the
  reading of the sender's clock when the output sample leaves.

All of this holds in every world. Not proved here: how far a knot is from
its input, and how far the schedule is from the true capture times.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open Unisono.Model.Descent

variable {H : Type} {R : ℕ}

/-- The settings of the capture schedule of the knots. -/
structure KnotSettings where
  /-- The nominal time from one frame to the next. -/
  nominal : ℝ
  /-- The largest distance from one of a block's time from one frame to the
  next on the schedule, divided by the nominal time. -/
  bound : ℝ
  /-- The time added to a block's timestamp, beyond the nominal time of the
  block's frames, when the timestamp stands in for the reading at a handover
  that was handled late. -/
  slack : ℝ

/-- The settings give a schedule that advances: the nominal time is
positive, and the bound is at least zero and less than one. -/
def KnotSettings.Valid (kn : KnotSettings) : Prop :=
  0 < kn.nominal ∧ 0 ≤ kn.bound ∧ kn.bound < 1

/-- The reading of the sender's clock when its host handles the handover of
capture block `b`. -/
def World.handedReading (w : World H R) (b : ℕ) : ℝ :=
  (w.clock w.sender).read (w.source.handed b)

/-- The handover of a later block is handled at a reading that is no
earlier. -/
theorem World.handedReading_mono (w : World H R) : Monotone w.handedReading :=
  fun _ _ h => (w.clock w.sender).strictMono.monotone (w.source.handed_mono h)

/-- **The input of a knot**, from the reading `σ` of the sender's clock at
the block's handover, the block's timestamp and its number `count` of
frames: the reading, or, if that is less, the timestamp plus the nominal
time of the block's frames, longer by the share `bound`, plus the slack. -/
def knotInput (kn : KnotSettings) (σ stamp : ℝ) (count : ℕ) : ℝ :=
  min σ (stamp + count * kn.nominal * (1 + kn.bound) + kn.slack)

/-- **One step of the knots.** From the knot and the advance of the block
before (`none` before the first handover), the reading `σ` of the sender's
clock at a handover, the block's timestamp and the number `count` of frames
of the block: the knot of the block, and by how much it advances over the
knot before. The first knot is its input, and its advance counts as the
nominal time of the block. After that the knot advances by the distance to
its input, kept between the nominal time of the block's frames shorter by
the share `bound` and that time longer by the share `bound`. -/
def knotStep (kn : KnotSettings) (prev : Option (ℝ × ℝ)) (σ stamp : ℝ) (count : ℕ) : ℝ × ℝ :=
  match prev with
  | none => (knotInput kn σ stamp count, count * kn.nominal)
  | some κ =>
      (κ.1 + clampTo (count * kn.nominal * (1 - kn.bound)) (count * kn.nominal * (1 + kn.bound))
          (knotInput kn σ stamp count - κ.1),
        clampTo (count * kn.nominal * (1 - kn.bound)) (count * kn.nominal * (1 + kn.bound))
          (knotInput kn σ stamp count - κ.1))

/-- **A knot advances by the nominal time of its block's frames, within the
share `bound`.** -/
theorem knotStep_snd_mem {kn : KnotSettings} (hkn : kn.Valid) (prev : Option (ℝ × ℝ))
    (σ stamp : ℝ) (count : ℕ) :
    count * kn.nominal * (1 - kn.bound) ≤ (knotStep kn prev σ stamp count).2
      ∧ (knotStep kn prev σ stamp count).2 ≤ count * kn.nominal * (1 + kn.bound) := by
  obtain ⟨hn, hb0, -⟩ := hkn
  have hcn : (0 : ℝ) ≤ count * kn.nominal := mul_nonneg (Nat.cast_nonneg _) hn.le
  have hlohi : count * kn.nominal * (1 - kn.bound) ≤ count * kn.nominal * (1 + kn.bound) :=
    mul_le_mul_of_nonneg_left (by linarith) hcn
  cases prev with
  | none =>
    refine ⟨?_, ?_⟩
    · show count * kn.nominal * (1 - kn.bound) ≤ count * kn.nominal
      nlinarith
    · show count * kn.nominal ≤ count * kn.nominal * (1 + kn.bound)
      nlinarith
  | some κ => exact clampTo_mem hlohi _

/-- A knot advances by a positive time, when the block has a frame. -/
theorem knotStep_snd_pos {kn : KnotSettings} (hkn : kn.Valid) (prev : Option (ℝ × ℝ))
    (σ stamp : ℝ) {count : ℕ} (hc : 0 < count) :
    0 < (knotStep kn prev σ stamp count).2 := by
  have h := (knotStep_snd_mem hkn prev σ stamp count).1
  obtain ⟨hn, -, hb1⟩ := hkn
  have hcn : (0 : ℝ) < count * kn.nominal := mul_pos (by exact_mod_cast hc) hn
  have hpos : 0 < count * kn.nominal * (1 - kn.bound) := mul_pos hcn (by linarith)
  linarith

/-- The input of the knot of capture block `b`: the reading at the block's
handover, or, if that is less, what the block's timestamp gives
(`knotInput`). -/
def World.knotInput (w : World H R) (kn : KnotSettings) (b : ℕ) : ℝ :=
  Unisono.Spec.knotInput kn (w.handedReading b) (w.source.reported b) (w.blockLength b)

/-- The knot of capture block `b` and its advance over the knot of the
block before, by `knotStep` from the readings and the timestamps of the
blocks up to `b`. -/
def World.knotState (w : World H R) (kn : KnotSettings) : ℕ → ℝ × ℝ
  | 0 => knotStep kn none (w.handedReading 0) (w.source.reported 0) (w.blockLength 0)
  | b + 1 =>
      knotStep kn (some (w.knotState kn b)) (w.handedReading (b + 1))
        (w.source.reported (b + 1)) (w.blockLength (b + 1))

/-- The knot of capture block `b`: the reading of the sender's clock at
which the schedule puts the block's right end (`knotStep`). -/
def World.knot (w : World H R) (kn : KnotSettings) (b : ℕ) : ℝ := (w.knotState kn b).1

/-- By how much the knot of block `b` advances over the knot of the block
before; for block zero, the nominal time of the block. -/
def World.knotInc (w : World H R) (kn : KnotSettings) (b : ℕ) : ℝ := (w.knotState kn b).2

/-- The time from one frame to the next, on the sender's clock, that the
schedule of the knots gives within block `b`: the advance of the block's
knot divided by the number of frames of the block. -/
def World.knotPeriod (w : World H R) (kn : KnotSettings) (b : ℕ) : ℝ :=
  w.knotInc kn b / w.blockLength b

/-- The value of the schedule of the knots at the left end of block `b`:
the knot of `b` minus the block's number of frames times its time from one
frame to the next. -/
def World.knotStart (w : World H R) (kn : KnotSettings) (b : ℕ) : ℝ :=
  w.knot kn b - w.blockLength b * w.knotPeriod kn b

/-- **Every knot advances by the nominal time of its block's frames, within
the share `bound`**, in every world. -/
theorem World.knotInc_mem (w : World H R) {kn : KnotSettings} (hkn : kn.Valid) (b : ℕ) :
    w.blockLength b * kn.nominal * (1 - kn.bound) ≤ w.knotInc kn b
      ∧ w.knotInc kn b ≤ w.blockLength b * kn.nominal * (1 + kn.bound) := by
  cases b with
  | zero => exact knotStep_snd_mem hkn none _ _ _
  | succ b => exact knotStep_snd_mem hkn (some (w.knotState kn b)) _ _ _

/-- **Every knot advances by a positive time.** -/
theorem World.knotInc_pos (w : World H R) {kn : KnotSettings} (hkn : kn.Valid) (b : ℕ) :
    0 < w.knotInc kn b := by
  cases b with
  | zero => exact knotStep_snd_pos hkn none _ _ (w.blockLength_pos 0)
  | succ b =>
    exact knotStep_snd_pos hkn (some (w.knotState kn b)) _ _ (w.blockLength_pos (b + 1))

/-- The knot of a block is the knot of the block before plus its advance. -/
theorem World.knot_succ (w : World H R) (kn : KnotSettings) (b : ℕ) :
    w.knot kn (b + 1) = w.knot kn b + w.knotInc kn (b + 1) := rfl

/-- The knot of block zero is its input. -/
theorem World.knot_zero (w : World H R) (kn : KnotSettings) :
    w.knot kn 0 = w.knotInput kn 0 := rfl

/-- **A later block has a later knot**, in every world. -/
theorem World.knot_strictMono (w : World H R) {kn : KnotSettings} (hkn : kn.Valid) :
    StrictMono (w.knot kn) :=
  strictMono_nat_of_lt_succ fun b => by
    rw [w.knot_succ kn b]
    linarith [w.knotInc_pos hkn (b + 1)]

/-- **The knot of a block is its input when the input lies a normal block's
time after the knot before**: at least the nominal time of the block's
frames shorter by the share `bound`, and at most that time longer by the
share `bound`. -/
theorem World.knot_succ_eq_knotInput (w : World H R) (kn : KnotSettings) {b : ℕ}
    (hlo : w.blockLength (b + 1) * kn.nominal * (1 - kn.bound)
      ≤ w.knotInput kn (b + 1) - w.knot kn b)
    (hhi : w.knotInput kn (b + 1) - w.knot kn b
      ≤ w.blockLength (b + 1) * kn.nominal * (1 + kn.bound)) :
    w.knot kn (b + 1) = w.knotInput kn (b + 1) := by
  show w.knot kn b + clampTo _ _ (w.knotInput kn (b + 1) - w.knot kn b) = _
  unfold clampTo
  rw [min_eq_right hhi, max_eq_right hlo]
  ring

/-- **Every block ends at its knot.** -/
theorem World.knotStart_add (w : World H R) (kn : KnotSettings) (b : ℕ) :
    w.knotStart kn b + w.blockLength b * w.knotPeriod kn b = w.knot kn b := by
  unfold World.knotStart
  ring

/-- **Every block after the first starts at the knot of the block before
it**, so the schedule of the knots is continuous from block to block. -/
theorem World.knotStart_succ (w : World H R) (kn : KnotSettings) (b : ℕ) :
    w.knotStart kn (b + 1) = w.knot kn b := by
  have hpos : (w.blockLength (b + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (w.blockLength_pos (b + 1)).ne'
  unfold World.knotStart World.knotPeriod
  rw [w.knot_succ kn b, mul_div_cancel₀ _ hpos]
  ring

/-- **Every block's time from one frame to the next is the nominal one,
within the share `bound`**, in every world. -/
theorem World.knotPeriod_mem (w : World H R) {kn : KnotSettings} (hkn : kn.Valid) (b : ℕ) :
    kn.nominal * (1 - kn.bound) ≤ w.knotPeriod kn b
      ∧ w.knotPeriod kn b ≤ kn.nominal * (1 + kn.bound) := by
  have hpos : (0 : ℝ) < w.blockLength b := by exact_mod_cast w.blockLength_pos b
  obtain ⟨h1, h2⟩ := w.knotInc_mem hkn b
  unfold World.knotPeriod
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hpos]
    linarith
  · rw [div_le_iff₀ hpos]
    linarith

/-- **The time from one frame to the next is positive in every block**, in
every world. -/
theorem World.knotPeriod_pos (w : World H R) {kn : KnotSettings} (hkn : kn.Valid) (b : ℕ) :
    0 < w.knotPeriod kn b :=
  div_pos (w.knotInc_pos hkn b) (by exact_mod_cast w.blockLength_pos b)

/-- Block zero has the nominal time from one frame to the next. -/
theorem World.knotPeriod_zero (w : World H R) (kn : KnotSettings) :
    w.knotPeriod kn 0 = kn.nominal := by
  have hpos : (w.blockLength 0 : ℝ) ≠ 0 := by exact_mod_cast (w.blockLength_pos 0).ne'
  show (w.blockLength 0 : ℝ) * kn.nominal / w.blockLength 0 = kn.nominal
  field_simp

/-- The value of the schedule of the knots at the coordinate `z`, by the
line of block `b`. -/
def World.knotTime (w : World H R) (kn : KnotSettings) (b : ℕ) (z : ℝ) : ℝ :=
  w.knotStart kn b + (z - w.source.first b) * w.knotPeriod kn b

/-- The line of a block reaches the block's knot at the block's right end,
which is the first frame of the next block. -/
theorem World.knotTime_right (w : World H R) (kn : KnotSettings) (b : ℕ) :
    w.knotTime kn b (w.source.first (b + 1)) = w.knot kn b := by
  have hle : w.source.first b ≤ w.source.first (b + 1) :=
    (w.source.first_strictMono (Nat.lt_succ_self b)).le
  have hcast : ((w.blockLength b : ℕ) : ℝ)
      = (w.source.first (b + 1) : ℝ) - w.source.first b := by
    unfold World.blockLength
    rw [Nat.cast_sub hle]
  unfold World.knotTime
  rw [← hcast]
  exact w.knotStart_add kn b

/-- The line of a block after the first starts, at the block's left end, at
the knot of the block before. -/
theorem World.knotTime_left (w : World H R) (kn : KnotSettings) (b : ℕ) :
    w.knotTime kn (b + 1) (w.source.first (b + 1)) = w.knot kn b := by
  unfold World.knotTime
  rw [sub_self, zero_mul, add_zero]
  exact w.knotStart_succ kn b

end Unisono.Spec

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The number of frames that a handover brings; zero for any other
event. -/
def handedCount (e : Event H R Payload) : ℕ :=
  match e.observation with
  | .handed frames _ => frames.length
  | _ => 0

/-- The timestamp that a handover brings; zero for any other event. -/
def handedStamp (e : Event H R Payload) : ℝ :=
  match e.observation with
  | .handed _ stamp => stamp
  | _ => 0

/-- The handover of a block brings the frames of the block. -/
theorem handedCount_handedEvent (w : World H R) (b : ℕ) :
    handedCount (w.handedEvent b : Event H R Payload) = w.blockLength b := by
  simp [handedCount, World.handedEvent, CaptureDevice.block, World.blockLength]

/-- The handover of a block brings the timestamp of the block. -/
theorem handedStamp_handedEvent (w : World H R) (b : ℕ) :
    handedStamp (w.handedEvent b : Event H R Payload) = w.source.reported b := rfl

/-- The knot and its advance after the handovers `hs`, oldest first, by
`knotStep`; `none` when there is no handover. -/
def knotsOf (kn : KnotSettings) (hs : List (Event H R Payload)) : Option (ℝ × ℝ) :=
  hs.foldl
    (fun acc e => some (knotStep kn acc e.reading (handedStamp e) (handedCount e))) none

/-- The knot after one more handover. -/
theorem knotsOf_concat (kn : KnotSettings) (hs : List (Event H R Payload))
    (e : Event H R Payload) :
    knotsOf kn (hs ++ [e])
      = some (knotStep kn (knotsOf kn hs) e.reading (handedStamp e) (handedCount e)) := by
  unfold knotsOf
  rw [List.foldl_append]
  rfl

/-- **The knots of a view are the knots of the world.** One step from the
knot after the handovers of the blocks before `b`, with the reading at the
handover of `b` and the timestamp of `b`, gives the knot of block `b` and
its advance. -/
theorem knotStep_knotsOf_range (w : World H R) (kn : KnotSettings) (b : ℕ) :
    knotStep kn
        (knotsOf kn ((List.range b).map (w.handedEvent : ℕ → Event H R Payload)))
        (w.handedReading b) (w.source.reported b) (w.blockLength b)
      = w.knotState kn b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, knotsOf_concat,
      handedCount_handedEvent, handedStamp_handedEvent]
    show knotStep kn (some (knotStep kn _ (w.handedReading b) (w.source.reported b)
      (w.blockLength b))) _ _ _ = _
    rw [ih]
    rfl

/-- The line that the header of a block gives, from the block's knot and
its advance `st`, the reading `σ` at the handover and the number `count` of
frames: the value at the block's left end of the line that ends at the
reading, the time from one frame to the next, and by how much the knot is
later than the reading. -/
def knotLine (st : ℝ × ℝ) (σ : ℝ) (count : ℕ) : ℝ × ℝ × ℝ :=
  (σ - count * (st.2 / count), st.2 / count, st.1 - σ)

/-- **The capture schedule of a block from the knots.** From the sender's
view up to and including the handover of a block: the schedule of the knots
within the block, as the header gives it (`knotLine`). The knots come from
the readings and the timestamps of all handovers of the view (`knotsOf`,
`knotStep`). -/
def knotCapture (kn : KnotSettings) (view : List (Event H R Payload)) (_f : ℕ) (_stamp : ℝ) :
    ℝ × ℝ × ℝ :=
  match (handoversOf view).getLast? with
  | some e =>
      knotLine
        (knotStep kn (knotsOf kn (handoversOf view).dropLast) e.reading (handedStamp e)
          (handedCount e))
        e.reading (handedCount e)
  | none => (0, kn.nominal, 0)

variable [DecidableEq H]

/-- **At the handover of block `b`, `knotCapture` gives the schedule of the
knots**: the value at the block's left end of the line that ends at the
reading of the handover, the block's time from one frame to the next
(`World.knotPeriod`), and by how much the block's knot is later than the
reading. This holds in the run of every solution in every world. -/
theorem knotCapture_eq (σ : Solution H R Payload) (w : World H R) (lookahead : ℕ+)
    (kn : KnotSettings) {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (f : ℕ) (stamp : ℝ) :
    knotCapture kn ((σ.states w lookahead i).views w.sender ++ [w.handedEvent b]) f stamp
      = (w.handedReading b - w.blockLength b * w.knotPeriod kn b,
        w.knotPeriod kn b, w.knot kn b - w.handedReading b) := by
  have hE := σ.earliest_of_handled_handed w lookahead hi
  obtain ⟨hn, -⟩ := σ.handedNext_of_earliest w lookahead hE
  have hlast : handoversOf [(w.handedEvent b : Event H R Payload)] = [w.handedEvent b] := by
    simp [handoversOf, World.handedEvent]
  unfold knotCapture
  rw [handoversOf_append, σ.handoversOf_views w lookahead i, hn, hlast, List.getLast?_concat,
    List.dropLast_concat]
  show knotLine (knotStep kn _ (w.handedReading b)
      (handedStamp (w.handedEvent b : Event H R Payload))
      (handedCount (w.handedEvent b : Event H R Payload))) (w.handedReading b) _ = _
  rw [handedCount_handedEvent, handedStamp_handedEvent, knotStep_knotsOf_range]
  rfl

/-- What the rules announce with block `b` in the run of the controller: the
level of the left end of the block and the change of the level from one
frame to the next, by the level rule at the sender's view when it handles
the handover of `b`. -/
def Rules.announced (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)
    (lookahead : ℕ+) (b : ℕ) : ℝ × ℝ :=
  rules.level.announce ((ruled p rules : Solution H R Payload).handoverView w lookahead b)
    (w.source.first b)

/-- **The header of a block under a capture schedule from the knots.** When
the run handles the handover of block `b`, the header that the rules give to
the block holds: the line that ends at the reading of the handover and has
the block's time from one frame to the next on the schedule of the knots;
the level that the level rule announces, plus the time by which the block's
knot is later than the reading; and the slope that the level rule
announces. -/
theorem runHeader_knots (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)
    (lookahead : ℕ+) {kn : KnotSettings} (hcap : rules.capture = knotCapture kn) {i b : ℕ}
    (hi : (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    rules.runHeader p w lookahead b
      = ⟨w.source.first b, w.handedReading b - w.blockLength b * w.knotPeriod kn b,
        w.knotPeriod kn b,
        (rules.announced p w lookahead b).1 + (w.knot kn b - w.handedReading b),
        (rules.announced p w lookahead b).2⟩ := by
  have hk : knotCapture kn ((ruled p rules : Solution H R Payload).handoverView w lookahead b)
      (w.source.first b) (w.source.reported b)
      = (w.handedReading b - w.blockLength b * w.knotPeriod kn b,
        w.knotPeriod kn b, w.knot kn b - w.handedReading b) := by
    rw [Solution.handoverView_eq _ w lookahead hi]
    exact knotCapture_eq _ w lookahead kn hi _ _
  unfold Rules.runHeader Rules.header Rules.announced
  rw [hcap, hk]

/-- **What a host chooses, under a capture schedule from the knots.** In the
setting of `ruled_chosen`, let the capture schedule of the rules come from
the knots. If the host of speaker `r` chooses the position `x` for an output
sample, then with `z = x + rules.back`, the coordinate of the schedule that
stands for `x`: there are an estimate `s` of the host, and a block `b` that
arrived at the host before every request not yet handled, such that

* `z` lies among the coordinates of block `b`;
* within block `b` the time from one frame to the next plus the change of
  the level from one frame to the next is positive;
* the value of the schedule of the knots at `z`, plus the level that the
  rules announce for `z`, is `s`;
* the host's view holds the arrival of block `b`, with the block's
  timestamp and the header of the knots, and that header covers the
  position that it says is due at `s`.

This holds in every world. -/
theorem ruled_chosen_knots (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)
    {kn : KnotSettings} (hcap : rules.capture = knotCapture kn) (hsender : p.sender = w.sender)
    (lookahead : ℕ+) {n : ℕ} {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ} {x : ℝ}
    (hx : (ruled p rules : Solution H R Payload).chosenAt w lookahead n r β k = some x) :
    ∃ s b t,
      rules.reading (w.host r)
          (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r β]) r k = some s
      ∧ (∃ q, w.network.deliver w.sender (w.host r) (w.source.handed b) q = some t)
      ∧ (∀ r' : Fin R, t < (w.speaker r').asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r'))
      ∧ (w.source.first b : ℝ) ≤ x + rules.back
      ∧ x + rules.back < w.source.first b + w.blockLength b
      ∧ 0 < w.knotPeriod kn b + (rules.announced p w lookahead b).2
      ∧ w.knotTime kn b (x + rules.back)
          + ((rules.announced p w lookahead b).1
            + (x + rules.back - w.source.first b) * (rules.announced p w lookahead b).2) = s
      ∧ ∃ e ∈ ((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r),
          ∃ i F, e.observation
              = .received i (.block (w.source.first b) (w.source.reported b)
                  (w.handedReading b - w.blockLength b * w.knotPeriod kn b)
                  (w.knotPeriod kn b)
                  ((rules.announced p w lookahead b).1 + (w.knot kn b - w.handedReading b))
                  (rules.announced p w lookahead b).2) F
            ∧ F.card = w.blockLength b
            ∧ (⟨w.source.first b, w.handedReading b - w.blockLength b * w.knotPeriod kn b,
                w.knotPeriod kn b,
                (rules.announced p w lookahead b).1 + (w.knot kn b - w.handedReading b),
                (rules.announced p w lookahead b).2⟩ : Header).Covers F.card s := by
  obtain ⟨s, b, t, hs, hq, hlt, ⟨i, hi⟩, hcov, hdue, e, he, j, F, hobs, hcard⟩ :=
    ruled_chosen p rules w hsender lookahead hr hx
  rw [runHeader_knots p rules w lookahead hcap hi] at hcov hdue hobs
  have hcov' := hcov
  obtain ⟨hpos, hlo, hhi⟩ := hcov
  rw [← hdue] at hlo hhi
  refine ⟨s, b, t, hs, hq, hlt, hlo, hhi, hpos, ?_, e, he, j, F, hobs, hcard,
    by rw [hcard]; exact hcov'⟩
  have := Header.eq_of_due hpos hdue.symm
  unfold World.knotTime World.knotStart
  linarith

end Unisono.Solutions.Controller
