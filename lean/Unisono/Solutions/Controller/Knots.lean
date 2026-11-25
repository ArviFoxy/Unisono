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

The sender's host observes each handover of the capture device when it
happens, with the reading of its own clock at that moment. This file makes a
schedule of capture times from those readings alone, with no estimate.

The schedule counts positions from one frame before the frames of the
source: its coordinate `z` stands for the position `z - 1`. In that
coordinate block `b` covers the coordinates from its first frame to just
before the first frame of the next block. Its left end stands for the last
frame of block `b - 1`, and its right end stands for its own last frame.
The capture device hands a block over when the block's last frame is
captured, so the reading of the sender's clock at the handover of block `b`
is a time for the right end of block `b` and for the left end of block
`b + 1`. Call that reading the knot of block `b` (`World.knot`).

* Within block `b ≥ 1` the schedule is the line from the knot of block
  `b - 1`, at the left end, to the knot of block `b`, at the right end
  (`World.knotStart`, `World.knotPeriod`). Block zero has no knot before it;
  its line ends at its own knot and has a given time from one frame to the
  next, for example the nominal one.
* **The schedule is continuous from block to block**: every block starts at
  the value at which the block before it ends, which is the knot between
  them (`World.knotStart_succ`, `World.knotStart_add`). This holds in every
  world.
* The time from one frame to the next is positive in every block
  (`World.knotPeriod_pos`), in a world in which no two handovers are handled
  at the same true time. A sender's host that was busy handles several
  handovers at the same true time; their knots are equal and the schedule
  stands still between them. So this schedule does not serve a world whose
  sender's host pauses.
* `knotCapture` computes the schedule of a block from the sender's view at
  its handover, and in the run of any solution in any world it gives the
  line above (`knotCapture_eq`).
* `ruled_chosen_knots`: when a host of the controller with this capture
  schedule chooses a position, the value of the schedule at that position
  plus the announced level of that position is the host's estimate of the
  reading of the sender's clock when the output sample leaves. This holds
  in every world.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The knot of capture block `b`: the reading of the sender's clock when
the capture device hands the block over. -/
def World.knot (w : World H R) (b : ℕ) : ℝ := (w.clock w.sender).read (w.source.handed b)

/-- The time from one frame to the next, on the sender's clock, that the
schedule of the knots gives within block `b`: the time from the knot of the
block before to the knot of `b`, divided by the number of frames of `b`.
Block zero gets the time `nominal`. -/
def World.knotPeriod (w : World H R) (nominal : ℝ) : ℕ → ℝ
  | 0 => nominal
  | b + 1 => (w.knot (b + 1) - w.knot b) / w.blockLength (b + 1)

/-- The value of the schedule of the knots at the left end of block `b`:
the knot of `b` minus the block's number of frames times its time from one
frame to the next. -/
def World.knotStart (w : World H R) (nominal : ℝ) (b : ℕ) : ℝ :=
  w.knot b - w.blockLength b * w.knotPeriod nominal b

/-- A later block has a later knot, when no two handovers are handled at the
same true time. A sender's host that was busy handles several handovers at
the same true time; their knots are then equal. -/
theorem World.knot_strictMono (w : World H R) (hstrict : StrictMono w.source.handed) :
    StrictMono w.knot :=
  fun _ _ h => (w.clock w.sender).strictMono (hstrict h)

/-- **Every block ends at its knot.** -/
theorem World.knotStart_add (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knotStart nominal b + w.blockLength b * w.knotPeriod nominal b = w.knot b := by
  unfold World.knotStart
  ring

/-- **Every block after the first starts at the knot of the block before
it**, so the schedule of the knots is continuous from block to block. -/
theorem World.knotStart_succ (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knotStart nominal (b + 1) = w.knot b := by
  have hpos : (0 : ℝ) < w.blockLength (b + 1) := by exact_mod_cast w.blockLength_pos (b + 1)
  unfold World.knotStart
  show w.knot (b + 1)
    - w.blockLength (b + 1) * ((w.knot (b + 1) - w.knot b) / w.blockLength (b + 1)) = _
  field_simp
  ring

/-- **The time from one frame to the next is positive in every block**, when
the time given to block zero is. -/
theorem World.knotPeriod_pos (w : World H R) {nominal : ℝ} (hnominal : 0 < nominal)
    (hstrict : StrictMono w.source.handed) (b : ℕ) :
    0 < w.knotPeriod nominal b := by
  cases b with
  | zero => exact hnominal
  | succ b =>
    have hpos : (0 : ℝ) < w.blockLength (b + 1) := by exact_mod_cast w.blockLength_pos (b + 1)
    exact div_pos (sub_pos.mpr (w.knot_strictMono hstrict (Nat.lt_succ_self b))) hpos

/-- The value of the schedule of the knots at the coordinate `z`, by the
line of block `b`. -/
def World.knotTime (w : World H R) (nominal : ℝ) (b : ℕ) (z : ℝ) : ℝ :=
  w.knotStart nominal b + (z - w.source.first b) * w.knotPeriod nominal b

/-- The line of a block reaches the block's knot at the block's right end,
which is the first frame of the next block. -/
theorem World.knotTime_right (w : World H R) (nominal : ℝ) (b : ℕ) :
    w.knotTime nominal b (w.source.first (b + 1)) = w.knot b := by
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
    w.knotTime nominal (b + 1) (w.source.first (b + 1)) = w.knot b := by
  unfold World.knotTime
  rw [sub_self, zero_mul, add_zero]
  exact w.knotStart_succ nominal b

end Unisono.Spec

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- **The capture schedule of a block from the readings at handovers.** From
the sender's view up to and including the handover of a block: the value of
the schedule at the block's left end, and the time from one frame to the
next. The schedule is the line that ends at the reading of this handover
and that passes, one block earlier, through the reading of the handover
before; at the first handover its time from one frame to the next is
`nominal`. -/
def knotCapture (nominal : ℝ) (view : List (Event H R Payload)) (_f : ℕ) (_stamp : ℝ) : ℝ × ℝ :=
  match (handoversOf view).reverse with
  | e :: rest =>
      (e.reading
          - ((match e.observation with
              | .handed frames _ => frames.length
              | _ => 0 : ℕ) : ℝ)
            * (match rest with
              | e' :: _ => (e.reading - e'.reading)
                  / ((match e.observation with
                    | .handed frames _ => frames.length
                    | _ => 0 : ℕ) : ℝ)
              | [] => nominal),
        match rest with
        | e' :: _ => (e.reading - e'.reading)
            / ((match e.observation with
              | .handed frames _ => frames.length
              | _ => 0 : ℕ) : ℝ)
        | [] => nominal)
  | [] => (0, nominal)

variable [DecidableEq H]

/-- **At the handover of block `b`, `knotCapture` gives the schedule of the
knots**: the value at the left end of the block and the time from one frame
to the next (`World.knotStart`, `World.knotPeriod`). This holds in the run of
every solution in every world. -/
theorem knotCapture_eq (σ : Solution H R Payload) (w : World H R) (lookahead : ℕ+)
    (nominal : ℝ) {i b : ℕ}
    (hi : σ.handled w lookahead i = some (w.sender, w.source.handed b,
      .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (f : ℕ) (stamp : ℝ) :
    knotCapture nominal ((σ.states w lookahead i).views w.sender ++ [w.handedEvent b]) f stamp
      = (w.knotStart nominal b, w.knotPeriod nominal b) := by
  have hE := σ.earliest_of_handled_handed w lookahead hi
  obtain ⟨hn, -⟩ := σ.handedNext_of_earliest w lookahead hE
  have hlast : handoversOf [(w.handedEvent b : Event H R Payload)] = [w.handedEvent b] := by
    simp [handoversOf, World.handedEvent]
  have hlen : ((w.source.block b).map fun k => (k, w.target k)).length = w.blockLength b := by
    simp [CaptureDevice.block, World.blockLength]
  unfold knotCapture
  rw [handoversOf_append, σ.handoversOf_views w lookahead i, hn, hlast, List.reverse_append,
    List.reverse_singleton, List.singleton_append]
  cases b with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.reverse_nil]
    show ((w.handedEvent 0 : Event H R Payload).reading
        - (((w.source.block 0).map fun k => (k, w.target k)).length : ℝ) * nominal, nominal) = _
    rw [hlen]
    rfl
  | succ b =>
    rw [List.range_succ, List.map_append, List.reverse_append]
    simp only [List.map_cons, List.map_nil, List.reverse_singleton, List.singleton_append]
    show ((w.handedEvent (b + 1) : Event H R Payload).reading
        - (((w.source.block (b + 1)).map fun k => (k, w.target k)).length : ℝ)
          * (((w.handedEvent (b + 1) : Event H R Payload).reading
              - (w.handedEvent b : Event H R Payload).reading)
            / (((w.source.block (b + 1)).map fun k => (k, w.target k)).length : ℝ)),
        ((w.handedEvent (b + 1) : Event H R Payload).reading
            - (w.handedEvent b : Event H R Payload).reading)
          / (((w.source.block (b + 1)).map fun k => (k, w.target k)).length : ℝ)) = _
    rw [hlen]
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
the block holds the schedule of the knots and what the level rule
announces. -/
theorem runHeader_knots (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)
    (lookahead : ℕ+) {nominal : ℝ} (hcap : rules.capture = knotCapture nominal) {i b : ℕ}
    (hi : (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    rules.runHeader p w lookahead b
      = ⟨w.source.first b, w.knotStart nominal b, w.knotPeriod nominal b,
        (rules.announced p w lookahead b).1, (rules.announced p w lookahead b).2⟩ := by
  have hk : knotCapture nominal ((ruled p rules : Solution H R Payload).handoverView w lookahead b)
      (w.source.first b) (w.source.reported b)
      = (w.knotStart nominal b, w.knotPeriod nominal b) := by
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
            + (x + rules.back - w.source.first b) * (rules.announced p w lookahead b).2) = s := by
  obtain ⟨s, b, t, hs, hq, hlt, ⟨i, hi⟩, hcov, hdue⟩ :=
    ruled_chosen p rules w hsender lookahead hr hx
  rw [runHeader_knots p rules w lookahead hcap hi] at hcov hdue
  obtain ⟨hpos, hlo, hhi⟩ := hcov
  rw [← hdue] at hlo hhi
  refine ⟨s, b, t, hs, hq, hlt, hlo, hhi, hpos, ?_⟩
  have := Header.eq_of_due hpos hdue.symm
  unfold World.knotTime
  linarith

end Unisono.Solutions.Controller
