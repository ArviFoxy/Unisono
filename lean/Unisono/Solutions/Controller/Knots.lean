/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Ruled
public import Unisono.Solutions.Controller.Schedule

/-!
# A capture schedule from the sender's readings at handovers

The sender's host handles each handover of the capture device at some
reading of its own clock (`World.handedReading`). The capture device hands
a block over when the block's last frame is captured, and the host handles
the handover then or, when it is busy, later. This file makes a schedule of
capture times from those readings alone, with no estimate.

The schedule counts positions from one frame before the frames of the
source: its coordinate `z` stands for the position `z - 1`. In that
coordinate block `b` covers the coordinates from its first frame to just
before the first frame of the next block. Its left end stands for the last
frame of block `b - 1`, and its right end stands for its own last frame.

**The published knots.** A host that was busy handles several handovers at
the same reading, so the readings themselves do not always advance. The
schedule therefore uses a knot for each block (`World.knot`) that always
advances (`knotStep`). The knot of block zero is its reading. After that
the knot of a block is its reading, unless that would advance the knot by
less than half of the advance of the block before, or by less than half of
the nominal time of one frame if that is less; then the knot advances by
that half.

* Every knot is later than the knot before (`World.knot_strictMono`), and no
  earlier than the block's reading (`World.handedReading_le_knot`). A knot
  is at most the nominal time of one frame after its reading
  (`World.knot_sub_le`), so the knots of blocks that are handed over
  together lie within one frame's nominal time. A knot is the reading
  whenever the reading advances enough
  (`World.knot_succ_eq_handedReading`), which is so while no two handovers
  are handled close together.
* Within block `b ≥ 1` the schedule is the line from the knot of block
  `b - 1`, at the left end, to the knot of block `b`, at the right end
  (`World.knotStart`, `World.knotPeriod`). Block zero has no knot before it;
  its line ends at its own knot and has the time `nominal` from one frame to
  the next.
* **The schedule is continuous from block to block**: every block starts at
  the value at which the block before it ends, which is the knot between
  them (`World.knotStart_succ`, `World.knotStart_add`).
* **The time from one frame to the next is positive in every block**
  (`World.knotPeriod_pos`).
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

All of this holds in every world. Not proved here: how far the schedule is
from the true capture times. After a pause of the sender's host the knots
of the blocks that were handed over together lie within one frame's nominal
time, so the schedule asks for all of their frames at once, and playback
that follows the schedule skips them with one jump.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The reading of the sender's clock when its host handles the handover of
capture block `b`. -/
def World.handedReading (w : World H R) (b : ℕ) : ℝ :=
  (w.clock w.sender).read (w.source.handed b)

/-- The handover of a later block is handled at a reading that is no
earlier. -/
theorem World.handedReading_mono (w : World H R) : Monotone w.handedReading :=
  fun _ _ h => (w.clock w.sender).strictMono.monotone (w.source.handed_mono h)

/-- **One step of the published knots.** From the knot and the advance of
the block before (`none` before the first handover), the reading `σ` of the
sender's clock at a handover and the number `count` of frames of the block:
the knot of the block, and by how much it advances over the knot before.
The first knot is the reading, and its advance counts as the nominal time
of the block. After that the knot is the reading, unless that would advance
it by less than half of the advance before, or by less than half of the
nominal time of one frame if that is less; then it advances by that half. -/
def knotStep (nominal : ℝ) (prev : Option (ℝ × ℝ)) (σ : ℝ) (count : ℕ) : ℝ × ℝ :=
  match prev with
  | none => (σ, count * nominal)
  | some κ =>
      (κ.1 + max (σ - κ.1) (min κ.2 nominal / 2), max (σ - κ.1) (min κ.2 nominal / 2))

/-- A knot advances by a positive time, when the advance before was
positive, the nominal time is positive and the block has a frame. -/
theorem knotStep_snd_pos {nominal : ℝ} (hn : 0 < nominal) {prev : Option (ℝ × ℝ)}
    (hprev : ∀ κ, prev = some κ → 0 < κ.2) (σ : ℝ) {count : ℕ} (hc : 0 < count) :
    0 < (knotStep nominal prev σ count).2 := by
  have hcn : (0 : ℝ) < count * nominal := mul_pos (by exact_mod_cast hc) hn
  cases prev with
  | none => exact hcn
  | some κ =>
    have hκ := hprev κ rfl
    exact lt_of_lt_of_le (half_pos (lt_min hκ hn)) (le_max_right _ _)

/-- A knot is no earlier than the reading of its handover. -/
theorem le_knotStep_fst (nominal : ℝ) (prev : Option (ℝ × ℝ)) (σ : ℝ) (count : ℕ) :
    σ ≤ (knotStep nominal prev σ count).1 := by
  cases prev with
  | none => exact le_rfl
  | some κ =>
    have h := le_max_left (σ - κ.1) (min κ.2 nominal / 2)
    show σ ≤ κ.1 + max (σ - κ.1) (min κ.2 nominal / 2)
    linarith

/-- The knot of capture block `b` and its advance over the knot of the
block before, by `knotStep` from the readings at the handovers of the
blocks up to `b`. -/
def World.knotState (w : World H R) (nominal : ℝ) : ℕ → ℝ × ℝ
  | 0 => knotStep nominal none (w.handedReading 0) (w.blockLength 0)
  | b + 1 =>
      knotStep nominal (some (w.knotState nominal b)) (w.handedReading (b + 1))
        (w.blockLength (b + 1))

/-- The knot of capture block `b`: the reading of the sender's clock at
which the schedule puts the block's right end. It is the reading at the
block's handover, or later when handovers are handled close together
(`knotStep`). -/
def World.knot (w : World H R) (nominal : ℝ) (b : ℕ) : ℝ := (w.knotState nominal b).1

/-- By how much the knot of block `b` advances over the knot of the block
before; for block zero, the nominal time of the block. -/
def World.knotInc (w : World H R) (nominal : ℝ) (b : ℕ) : ℝ := (w.knotState nominal b).2

/-- The time from one frame to the next, on the sender's clock, that the
schedule of the knots gives within block `b`: the advance of the block's
knot divided by the number of frames of the block. -/
def World.knotPeriod (w : World H R) (nominal : ℝ) (b : ℕ) : ℝ :=
  w.knotInc nominal b / w.blockLength b

/-- The value of the schedule of the knots at the left end of block `b`:
the knot of `b` minus the block's number of frames times its time from one
frame to the next. -/
def World.knotStart (w : World H R) (nominal : ℝ) (b : ℕ) : ℝ :=
  w.knot nominal b - w.blockLength b * w.knotPeriod nominal b

/-- **Every knot advances by a positive time.** -/
theorem World.knotInc_pos (w : World H R) {nominal : ℝ} (hn : 0 < nominal) (b : ℕ) :
    0 < w.knotInc nominal b := by
  induction b with
  | zero =>
    exact knotStep_snd_pos hn (fun κ h => absurd h (by simp)) _ (w.blockLength_pos 0)
  | succ b ih =>
    refine knotStep_snd_pos hn (fun κ h => ?_) _ (w.blockLength_pos (b + 1))
    obtain rfl := Option.some.inj h
    exact ih

/-- The knot of a block is the knot of the block before plus its advance. -/
theorem World.knot_succ (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knot nominal (b + 1) = w.knot nominal b + w.knotInc nominal (b + 1) := rfl

/-- **A later block has a later knot**, in every world. -/
theorem World.knot_strictMono (w : World H R) {nominal : ℝ} (hn : 0 < nominal) :
    StrictMono (w.knot nominal) :=
  strictMono_nat_of_lt_succ fun b => by
    rw [w.knot_succ nominal b]
    linarith [w.knotInc_pos hn (b + 1)]

/-- **A knot is no earlier than the reading at the block's handover.** -/
theorem World.handedReading_le_knot (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.handedReading b ≤ w.knot nominal b := by
  cases b with
  | zero => exact le_knotStep_fst nominal none _ _
  | succ b => exact le_knotStep_fst nominal (some (w.knotState nominal b)) _ _

/-- **The knot of a block is the reading at its handover when the reading
advances enough**: by at least half of the advance of the knot before, or
of the nominal time of one frame if that is less. -/
theorem World.knot_succ_eq_handedReading (w : World H R) (nominal : ℝ) {b : ℕ}
    (h : min (w.knotInc nominal b) nominal / 2
      ≤ w.handedReading (b + 1) - w.knot nominal b) :
    w.knot nominal (b + 1) = w.handedReading (b + 1) := by
  show w.knot nominal b + max (w.handedReading (b + 1) - w.knot nominal b)
      (min (w.knotInc nominal b) nominal / 2) = _
  rw [max_eq_left h]
  ring

/-- **A knot is at most the nominal time of one frame after its reading.**
For every block, the time from the reading at its handover to its knot,
plus the lesser of the knot's advance and the nominal time of one frame, is
at most that nominal time. So the knots of blocks that are handed over
together lie within one frame's nominal time. -/
theorem World.knot_sub_le (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knot nominal b - w.handedReading b + min (w.knotInc nominal b) nominal ≤ nominal := by
  induction b with
  | zero =>
    have h0 : w.knot nominal 0 = w.handedReading 0 := rfl
    rw [h0, sub_self, zero_add]
    exact min_le_right _ _
  | succ b ih =>
    have hR := w.handedReading_mono (Nat.le_add_right b 1)
    have hinc : w.knotInc nominal (b + 1)
        = max (w.handedReading (b + 1) - w.knot nominal b)
          (min (w.knotInc nominal b) nominal / 2) := rfl
    rw [w.knot_succ nominal b, hinc]
    rcases le_total (w.handedReading (b + 1) - w.knot nominal b)
        (min (w.knotInc nominal b) nominal / 2) with hle | hle
    · rw [max_eq_right hle]
      have h1 := min_le_left (min (w.knotInc nominal b) nominal / 2) nominal
      linarith
    · rw [max_eq_left hle]
      have h1 := min_le_right (w.handedReading (b + 1) - w.knot nominal b) nominal
      linarith

/-- **Every block ends at its knot.** -/
theorem World.knotStart_add (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knotStart nominal b + w.blockLength b * w.knotPeriod nominal b = w.knot nominal b := by
  unfold World.knotStart
  ring

/-- **Every block after the first starts at the knot of the block before
it**, so the schedule of the knots is continuous from block to block. -/
theorem World.knotStart_succ (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knotStart nominal (b + 1) = w.knot nominal b := by
  have hpos : (w.blockLength (b + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (w.blockLength_pos (b + 1)).ne'
  unfold World.knotStart World.knotPeriod
  rw [w.knot_succ nominal b, mul_div_cancel₀ _ hpos]
  ring

/-- **The time from one frame to the next is positive in every block**, in
every world, when the nominal time is positive. -/
theorem World.knotPeriod_pos (w : World H R) {nominal : ℝ} (hnominal : 0 < nominal) (b : ℕ) :
    0 < w.knotPeriod nominal b :=
  div_pos (w.knotInc_pos hnominal b) (by exact_mod_cast w.blockLength_pos b)

/-- Block zero has the nominal time from one frame to the next. -/
theorem World.knotPeriod_zero (w : World H R) (nominal : ℝ) :
    w.knotPeriod nominal 0 = nominal := by
  have hpos : (w.blockLength 0 : ℝ) ≠ 0 := by exact_mod_cast (w.blockLength_pos 0).ne'
  show (w.blockLength 0 : ℝ) * nominal / w.blockLength 0 = nominal
  field_simp

/-- The value of the schedule of the knots at the coordinate `z`, by the
line of block `b`. -/
def World.knotTime (w : World H R) (nominal : ℝ) (b : ℕ) (z : ℝ) : ℝ :=
  w.knotStart nominal b + (z - w.source.first b) * w.knotPeriod nominal b

/-- The line of a block reaches the block's knot at the block's right end,
which is the first frame of the next block. -/
theorem World.knotTime_right (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knotTime nominal b (w.source.first (b + 1)) = w.knot nominal b := by
  have hle : w.source.first b ≤ w.source.first (b + 1) :=
    (w.source.first_strictMono (Nat.lt_succ_self b)).le
  have hcast : ((w.blockLength b : ℕ) : ℝ)
      = (w.source.first (b + 1) : ℝ) - w.source.first b := by
    unfold World.blockLength
    rw [Nat.cast_sub hle]
  unfold World.knotTime
  rw [← hcast]
  exact w.knotStart_add nominal b

/-- The line of a block after the first starts, at the block's left end, at
the knot of the block before. -/
theorem World.knotTime_left (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knotTime nominal (b + 1) (w.source.first (b + 1)) = w.knot nominal b := by
  unfold World.knotTime
  rw [sub_self, zero_mul, add_zero]
  exact w.knotStart_succ nominal b

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

/-- The handover of a block brings the frames of the block. -/
theorem handedCount_handedEvent (w : World H R) (b : ℕ) :
    handedCount (w.handedEvent b : Event H R Payload) = w.blockLength b := by
  simp [handedCount, World.handedEvent, CaptureDevice.block, World.blockLength]

/-- The knot and its advance after the handovers `hs`, oldest first, by
`knotStep`; `none` when there is no handover. -/
def knotsOf (nominal : ℝ) (hs : List (Event H R Payload)) : Option (ℝ × ℝ) :=
  hs.foldl (fun acc e => some (knotStep nominal acc e.reading (handedCount e))) none

/-- The knot after one more handover. -/
theorem knotsOf_concat (nominal : ℝ) (hs : List (Event H R Payload)) (e : Event H R Payload) :
    knotsOf nominal (hs ++ [e])
      = some (knotStep nominal (knotsOf nominal hs) e.reading (handedCount e)) := by
  unfold knotsOf
  rw [List.foldl_append]
  rfl

/-- **The knots of a view are the knots of the world.** One step from the
knot after the handovers of the blocks before `b`, with the reading at the
handover of `b`, gives the knot of block `b` and its advance. -/
theorem knotStep_knotsOf_range (w : World H R) (nominal : ℝ) (b : ℕ) :
    knotStep nominal
        (knotsOf nominal ((List.range b).map (w.handedEvent : ℕ → Event H R Payload)))
        (w.handedReading b) (w.blockLength b)
      = w.knotState nominal b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, knotsOf_concat,
      handedCount_handedEvent]
    show knotStep nominal (some (knotStep nominal _ (w.handedReading b) (w.blockLength b)))
      _ _ = _
    rw [ih]
    rfl

/-- The line that the header of a block gives, from the block's knot and
its advance `st`, the reading `σ` at the handover and the number `count` of
frames: the value at the block's left end of the line that ends at the
reading, the time from one frame to the next, and by how much the knot is
later than the reading. -/
def knotLine (st : ℝ × ℝ) (σ : ℝ) (count : ℕ) : ℝ × ℝ × ℝ :=
  (σ - count * (st.2 / count), st.2 / count, st.1 - σ)

/-- **The capture schedule of a block from the readings at handovers.** From
the sender's view up to and including the handover of a block: the schedule
of the knots within the block, as the header gives it (`knotLine`). The
knots come from the readings at all handovers of the view (`knotsOf`,
`knotStep`). -/
def knotCapture (nominal : ℝ) (view : List (Event H R Payload)) (_f : ℕ) (_stamp : ℝ) :
    ℝ × ℝ × ℝ :=
  match (handoversOf view).getLast? with
  | some e =>
      knotLine
        (knotStep nominal (knotsOf nominal (handoversOf view).dropLast) e.reading (handedCount e))
        e.reading (handedCount e)
  | none => (0, nominal, 0)

variable [DecidableEq H]

/-- **At the handover of block `b`, `knotCapture` gives the schedule of the
knots**: the value at the block's left end of the line that ends at the
reading of the handover, the block's time from one frame to the next
(`World.knotPeriod`), and by how much the block's knot is later than the
reading. This holds in the run of every solution in every world. -/
theorem knotCapture_eq (σ : Solution H R Payload) (w : World H R) (lookahead : ℕ+)
    (nominal : ℝ) {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (f : ℕ) (stamp : ℝ) :
    knotCapture nominal ((σ.states w lookahead i).views w.sender ++ [w.handedEvent b]) f stamp
      = (w.handedReading b - w.blockLength b * w.knotPeriod nominal b,
        w.knotPeriod nominal b, w.knot nominal b - w.handedReading b) := by
  have hE := σ.earliest_of_handled_handed w lookahead hi
  obtain ⟨hn, -⟩ := σ.handedNext_of_earliest w lookahead hE
  have hlast : handoversOf [(w.handedEvent b : Event H R Payload)] = [w.handedEvent b] := by
    simp [handoversOf, World.handedEvent]
  unfold knotCapture
  rw [handoversOf_append, σ.handoversOf_views w lookahead i, hn, hlast, List.getLast?_concat,
    List.dropLast_concat]
  show knotLine (knotStep nominal _ (w.handedReading b)
      (handedCount (w.handedEvent b : Event H R Payload))) (w.handedReading b) _ = _
  rw [handedCount_handedEvent, knotStep_knotsOf_range]
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
    (lookahead : ℕ+) {nominal : ℝ} (hcap : rules.capture = knotCapture nominal) {i b : ℕ}
    (hi : (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    rules.runHeader p w lookahead b
      = ⟨w.source.first b, w.handedReading b - w.blockLength b * w.knotPeriod nominal b,
        w.knotPeriod nominal b,
        (rules.announced p w lookahead b).1 + (w.knot nominal b - w.handedReading b),
        (rules.announced p w lookahead b).2⟩ := by
  have hk : knotCapture nominal ((ruled p rules : Solution H R Payload).handoverView w lookahead b)
      (w.source.first b) (w.source.reported b)
      = (w.handedReading b - w.blockLength b * w.knotPeriod nominal b,
        w.knotPeriod nominal b, w.knot nominal b - w.handedReading b) := by
    rw [Solution.handoverView_eq _ w lookahead hi]
    exact knotCapture_eq _ w lookahead nominal hi _ _
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
  rules announce for `z`, is `s`.

This holds in every world. -/
theorem ruled_chosen_knots (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)
    {nominal : ℝ} (hcap : rules.capture = knotCapture nominal) (hsender : p.sender = w.sender)
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
      ∧ 0 < w.knotPeriod nominal b + (rules.announced p w lookahead b).2
      ∧ w.knotTime nominal b (x + rules.back)
          + ((rules.announced p w lookahead b).1
            + (x + rules.back - w.source.first b) * (rules.announced p w lookahead b).2) = s
      ∧ ∃ e ∈ ((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r),
          ∃ i F, e.observation
              = .received i (.block (w.source.first b) (w.source.reported b)
                  (w.handedReading b - w.blockLength b * w.knotPeriod nominal b)
                  (w.knotPeriod nominal b)
                  ((rules.announced p w lookahead b).1 + (w.knot nominal b - w.handedReading b))
                  (rules.announced p w lookahead b).2) F
            ∧ F.card = w.blockLength b
            ∧ (⟨w.source.first b, w.handedReading b - w.blockLength b * w.knotPeriod nominal b,
                w.knotPeriod nominal b,
                (rules.announced p w lookahead b).1 + (w.knot nominal b - w.handedReading b),
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
