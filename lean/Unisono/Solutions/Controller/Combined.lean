/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Needs
public import Unisono.Spec.Follower

/-!
# The combined solution

One solution that puts the parts of the controller together. Nothing is
told to it about the pauses, the rates of the clocks, their wander or the
errors of the timestamps.

* **Estimates.** Each receiving host estimates the sender's clock from its
  clock exchanges, and each host estimates when its devices' samples occur
  from the devices' timestamps (`ClockEstimator`, `DeviceEstimator`; they
  are parameters).
* **Needs.** Each host reports, in its clock queries, the largest need of
  the blocks that arrived since its last answered query (`measuredNeed`).
* **The level.** The sender steps the level against the reported needs and
  announces a level that is continuous from block to block
  (`steppedLevel`).
* **Playback.** A speaker aims at the position that is due by the sender's
  schedule and its host's estimates, and follows it within the step bound
  `u`, with jumps beyond `J` frames (`Solution.followed`).

Two facts hold in every world, whatever the estimators are:

* `isStar`, `combined_isStar`: its hosts exchange messages only with the
  sender.
* `combined_withinStep`: in every step of continuous playback its position
  advances by one frame per output sample within `u`, for `u ≥ 0` and
  `J ≥ 1`.

Not part of this solution yet: a schedule of capture times that is
continuous from block to block when the sender's estimate of the capture
device changes. No cost of this solution is bounded here, and nothing is
said about how well it does.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : FixedDelay.Params H)
  (clockEst : ClockEstimator) (deviceEst : DeviceEstimator)

/-- **The hosts of the controller exchange messages only with the sender**,
whatever the estimators and the level rule are. -/
theorem isStar (levelRule : LevelRule H R) :
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

/-- **The combined solution**: the controller with the level rule that steps
against the needs (`steppedLevel q`), hosts that report the needs that they
measure (`measuredNeed` with the settings `s`), and playback that follows
the position that is due within the step bound `u`, with jumps beyond `J`
frames. -/
def combined (q : LevelSettings) (s : NeedSettings) (u J : ℝ) : Solution H R Payload :=
  (solution p clockEst deviceEst
    (steppedLevel q (measuredNeed p clockEst deviceEst s))).followed u J

/-- The hosts of the combined solution exchange messages only with the
sender. -/
theorem combined_isStar (q : LevelSettings) (s : NeedSettings) (u J : ℝ) :
    (combined p clockEst deviceEst q s u J : Solution H R Payload).IsStar p.sender :=
  Solution.stepped_isStar _ _ (isStar p clockEst deviceEst _)

/-- **The combined solution keeps the step bound in every world**, for
`u ≥ 0` and `J ≥ 1`: in every step of continuous playback its position
advances by one frame per output sample within `u`. Nothing is assumed
about the world or about the estimators. -/
theorem combined_withinStep (q : LevelSettings) (s : NeedSettings) {u J : ℝ} (hu : 0 ≤ u)
    (hJ : 1 ≤ J) (w : World H R) (lookahead : ℕ+) :
    (combined p clockEst deviceEst q s u J : Solution H R Payload).WithinStep w lookahead u :=
  Solution.followed_withinStep _ hu hJ w lookahead

end Unisono.Solutions.Controller
