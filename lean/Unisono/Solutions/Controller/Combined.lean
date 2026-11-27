/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Needs
public import Unisono.Solutions.Controller.Timing
public import Unisono.Solutions.Controller.DueSchedule
public import Unisono.Spec.Follower

/-!
# The combined solution

One solution that puts the parts of the controller together. Nothing is
told to it about the pauses, the rates of the clocks, their wander or the
errors of the timestamps. It is told the nominal rate, the request lead and
the block size of the playback devices, and its own settings.

* **The capture schedule.** The sender takes the capture time of each block
  from the readings of its clock at the handovers of the capture device and
  from the timestamps of the blocks. The schedule is continuous from block
  to block, and in every block its time from one frame to the next is the
  nominal one within a set share, also when the sender's host handles
  several handovers at the same time (`knotCapture`, `knotStep`,
  `World.knotPeriod_mem`).
* **When output samples leave.** Each host takes the time at which an output
  sample leaves from the readings of its clock at the requests of the
  playback device (`requestOutput`).
* **The sender's clock.** Each receiving host estimates the sender's clock
  from the arrivals of the blocks of the stream, and takes half of the least
  round trip from its clock exchanges (`envelopeReading`, `timingParts`).
* **Two checks.** A host plays an output sample only where a clock exchange
  confirms its estimate of the sender's clock and the schedule of the block
  that is due agrees with the block's reading and timestamp
  (`checkedReading`).
* **Needs.** Each host reports, in its clock queries, the largest need of
  the blocks that arrived since its last answered query (`timedNeed`).
* **The level.** The sender steps the level against the reported needs and
  announces a level that is continuous from block to block. Within a block
  the level changes, from one frame to the next, by at most the share
  `share` of the block's time from one frame to the next, so that the
  schedule on which positions are due advances in every block of every
  world (`knotLevel`, `dueSlope_pos`).
* **Playback.** A speaker aims at the position that is due by the sender's
  schedule and its host's estimates, and follows it within the step bound
  `u`, with jumps beyond `J` frames (`Solution.followed`).

Every estimate uses a bounded stretch of what a host has observed. Two facts
hold in every world:

* `isStar`, `combined_isStar`: its hosts exchange messages only with the
  sender.
* `combined_withinStep`: in every step of continuous playback its position
  advances by one frame per output sample within `u`, for `u ≥ 0` and
  `J ≥ 1`.

What its hosts choose before the follower moves toward it, and the exact
error of each host's estimate of the sender's clock, are stated for every
world in `timed_chosen`. No cost of this solution is bounded here, and
nothing is said about how well it does.

`isStar` is the statement for the controller of
`Unisono.Solutions.Controller`, whose estimates come from clock exchanges
and from the timestamps of the devices.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : FixedDelay.Params H)

/-- **The hosts of the controller exchange messages only with the sender**,
whatever the estimators and the level rule are. -/
theorem isStar (clockEst : ClockEstimator) (deviceEst : DeviceEstimator)
    (levelRule : LevelRule H R) :
    (solution p clockEst deviceEst levelRule : Solution H R Payload).IsStar p.sender := by
  intro h view dst msg frames hmem
  change (dst, msg, frames) ∈ ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
      (view.map (Event.mapMsg Payload.plain))).sends.map
    (fun s => (s.1, enrich p deviceEst levelRule h view s.2.1, s.2.2)) at hmem
  obtain ⟨s₀, hs₀, heq⟩ := List.mem_map.mp hmem
  have h1 := fixedDelay_isStar (R := R) p h (view.map (Event.mapMsg Payload.plain)) s₀.1
    s₀.2.1 s₀.2.2 hs₀
  have hdst : s₀.1 = dst := congrArg Prod.fst heq
  rw [← hdst]
  exact h1

/-- **The combined solution**: the controller with the timing rules for the
settings `t`, the level rule that steps against the needs with the slope
limited to the share `share` of a block's time from one frame to the next
(`knotLevel q share`), hosts that report the needs that they measure
(`timedNeed t`), and playback that follows the position that is due within
the step bound `u`, with jumps beyond `J` frames. -/
def combined (t : TimingSettings) (q : LevelSettings) (share u J : ℝ) :
    Solution H R Payload :=
  (ruled p (timedRules p.sender t
    (knotLevel q share t.knots (timedNeed t)))).followed u J

/-- The hosts of the combined solution exchange messages only with the
sender. -/
theorem combined_isStar (t : TimingSettings) (q : LevelSettings) (share u J : ℝ) :
    (combined p t q share u J : Solution H R Payload).IsStar p.sender :=
  Solution.stepped_isStar _ _ (ruled_isStar p _)

/-- **The combined solution keeps the step bound in every world**, for
`u ≥ 0` and `J ≥ 1`: in every step of continuous playback its position
advances by one frame per output sample within `u`. Nothing is assumed
about the world. -/
theorem combined_withinStep (t : TimingSettings) (q : LevelSettings) (share : ℝ) {u J : ℝ}
    (hu : 0 ≤ u) (hJ : 1 ≤ J) (w : World H R) (lookahead : ℕ+) :
    (combined p t q share u J : Solution H R Payload).WithinStep w lookahead u :=
  Solution.followed_withinStep _ hu hJ w lookahead

end Unisono.Solutions.Controller
