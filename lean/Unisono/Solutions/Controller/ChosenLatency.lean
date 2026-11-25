/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Timing

/-!
# The latency of the position that a host chooses, in parts

The controller with the timing rules (`timedRules`) chooses a position for
each output sample. This file writes the time from the capture of that
position to the output sample, on the sender's clock, as a sum of parts
that each have one cause. The statements are identities. They hold in the
run of the controller in every world, and nothing is assumed about clocks,
delays or pauses.

**The schedule against the capture times.** `World.captureReading n` is the
reading of the sender's clock when frame `n` is captured, and
`World.knotLate b` is by how much the knot of block `b` is later than the
reading at the capture of the block's last frame; it is negative when the
knot is earlier. Within a block after the first, the schedule of the knots
is the line between two knots (`World.knotTime_succ`), so its distance from
any reading `G` is a mean of the lateness of the two knots, plus the
distance of `G` from the line between the two capture readings
(`World.knotTime_succ_sub`).

**The parts** (`timed_chosen_parts`). Let the host of speaker `r` choose the
position `x` for output sample `k`. For every true time `o` and every
reading `G`, the reading of the sender's clock at `o` minus `G` is the sum
of:

1. the level that the sender announced for the position;
2. the value of the schedule of the knots at the position, minus `G`;
3. the time on the sender's clock that a block `b'` took from its handover
   to its arrival, minus half of the round trip that the host uses;
4. the time on the sender's clock from the arrival of `b'` to `o`, minus
   the host's slope times the same time on the host's clock;
5. the slope times the reading of the host's clock at `o` minus the reading
   that the host expects when the output sample leaves.

With `o` the true time at which the output sample leaves and `G` the
reading of the sender's clock when the position was captured, the left side
is the latency of the position on the sender's clock. Part 2 is then the
error of the schedule, parts 3 and 4 are the error of the host's estimate of
the sender's clock, and part 5 is the error of the time at which the host
expects the output sample to leave.

Not proved here: any bound on a part.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The reading of the sender's clock when frame `n` is captured. -/
def World.captureReading (w : World H R) (n : ℕ) : ℝ :=
  (w.clock w.sender).read (w.source.capture n)

/-- By how much the knot of block `b` is later, on the sender's clock, than
the capture of the block's last frame; negative when the knot is earlier. -/
def World.knotLate (w : World H R) (kn : KnotSettings) (b : ℕ) : ℝ :=
  w.knot kn b - w.captureReading (w.source.first (b + 1) - 1)

/-- **Within a block after the first, the schedule of the knots is the line
between two knots**: at the coordinate `z` its value is the knot of the
block before plus the share of the block that lies before `z` times the
advance of the knot. -/
theorem World.knotTime_succ (w : World H R) (kn : KnotSettings) (b : ℕ) (z : ℝ) :
    w.knotTime kn (b + 1) z
      = w.knot kn b
        + (z - w.source.first (b + 1)) / w.blockLength (b + 1)
          * (w.knot kn (b + 1) - w.knot kn b) := by
  unfold World.knotTime World.knotPeriod
  rw [w.knotStart_succ kn b, w.knot_succ kn b]
  ring

/-- **The schedule of the knots against a reading.** Within a block after
the first, with `θ` the share of the block that lies before the coordinate
`z`: the value of the schedule at `z` minus any reading `G` is the mean,
with the weights `1 - θ` and `θ`, of the lateness of the knot before and of
the block's own knot, plus the same mean of the readings at the captures of
the two blocks' last frames, minus `G`. -/
theorem World.knotTime_succ_sub (w : World H R) (kn : KnotSettings) (b : ℕ) (z G : ℝ) :
    w.knotTime kn (b + 1) z - G
      = (1 - (z - w.source.first (b + 1)) / w.blockLength (b + 1)) * w.knotLate kn b
        + (z - w.source.first (b + 1)) / w.blockLength (b + 1) * w.knotLate kn (b + 1)
        + ((1 - (z - w.source.first (b + 1)) / w.blockLength (b + 1))
              * w.captureReading (w.source.first (b + 1) - 1)
            + (z - w.source.first (b + 1)) / w.blockLength (b + 1)
              * w.captureReading (w.source.first (b + 1 + 1) - 1)
            - G) := by
  rw [w.knotTime_succ kn b z]
  unfold World.knotLate
  ring

end Unisono.Spec

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- **The latency of the position that a host chooses, in parts.** Take the
controller with the timing rules, any settings and any level rule, in any
world. Let speaker `r` be on a host other than the sender's, and let the
host choose the position `x` for output sample `k` at the step that handles
the request of block `β`. Then there are a block `b` whose coordinates hold
`x + 1`, and a block `b'` that arrived at the host at a true time `tb'`
before the request, such that for every true time `o` and every reading
`G`: the reading of the sender's clock at `o` minus `G` is the sum of

1. the level announced for the coordinate `x + 1`;
2. the value of the schedule of the knots at `x + 1`, minus `G`;
3. the time on the sender's clock from the handover of `b'` to its arrival,
   minus half of the round trip that the host uses;
4. the time on the sender's clock from the arrival of `b'` to `o`, minus
   the host's slope times the same time on the host's clock;
5. the slope times the reading of the host's clock at `o` minus the reading
   that the host expects when the output sample leaves (`outputAt`). -/
theorem timed_chosen_parts (p : FixedDelay.Params H) (w : World H R) (t : TimingSettings)
    (level : LevelRule H R) (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ}
    {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ} {x : ℝ}
    (hE : earliest (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w
          lookahead n).key w)
        ((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead n).due
      = some (.asked r β))
    (hx : (ruled p (timedRules w.sender t level) : Solution H R Payload).chosenAt w lookahead n
      r β k = some x) :
    ∃ b b' tb',
      (w.source.first b : ℝ) ≤ x + 1 ∧ x + 1 < w.source.first b + w.blockLength b
      ∧ (∃ q, w.network.deliver w.sender (w.host r) (w.source.handed b') q = some tb')
      ∧ tb' < (w.speaker r).asked β
      ∧ ∀ (o : Time) (G : ℝ), (w.clock w.sender).read o - G
          = (((timedRules w.sender t level).announced p w lookahead b).1
              + (x + 1 - w.source.first b)
                * ((timedRules w.sender t level).announced p w lookahead b).2)
            + (w.knotTime t.knots b (x + 1) - G)
            + ((w.clock w.sender).read tb' - w.handedReading b'
              - halfTrip t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β]))
            + ((w.clock w.sender).read o - (w.clock w.sender).read tb'
              - arrivalSlope t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])
                * ((w.clock (w.host r)).read o - (w.clock (w.host r)).read tb'))
            + arrivalSlope t (((ruled p (timedRules w.sender t level) :
                  Solution H R Payload).states w lookahead n).views (w.host r)
                ++ [w.askedEvent r β])
              * ((w.clock (w.host r)).read o - outputAt t w r β k) := by
  obtain ⟨s, b, tb, b', tb', -, -, -, hlo, hhi, -, heq, hq', hlt', herr, -, -⟩ :=
    timed_chosen p w t level hsender lookahead hr hE hx
  refine ⟨b, b', tb', hlo, hhi, hq', hlt', fun o G => ?_⟩
  have h := herr o
  linarith

end Unisono.Solutions.Controller
