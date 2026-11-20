/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Fixed
public import Unisono.Relation

/-!
# Timing and the regulator

The functions of `unisono_core::timing` and `unisono_core::player` return for
every argument and every state: no reading of a clock, no schedule and no
state of the regulator makes the planning of a cycle fail.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Player

attribute [local step] Unisono.Relation.div_floor_total Unisono.Relation.saturate_total

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

@[step]
theorem sender_time_total (line : relation.Line) (path time : Std.I64) :
    timing.sender_time line path time ⦃ _ => True ⦄ := by
  unfold timing.sender_time
  run

@[step]
theorem due_total (schedule : timing.Schedule) (time : Std.I64) :
    timing.due schedule time ⦃ _ => True ⦄ := by
  unfold timing.due
  run

@[step]
theorem distance_total (a b : timing.Position) : timing.distance a b ⦃ _ => True ⦄ := by
  unfold timing.distance
  run

@[step]
theorem advance_total (start : timing.Position) (frames : Std.U32) (step : Std.I64) :
    timing.advance start frames step ⦃ _ => True ⦄ := by
  unfold timing.advance
  run

@[step]
theorem gain_total (p : player.Player) (duration : Std.I64) :
    player.Player.gain p duration ⦃ _ => True ⦄ := by
  unfold player.Player.gain
  run

@[step]
theorem regulate_total (p : player.Player) (behind duration : Std.I64) :
    player.Player.regulate p behind duration ⦃ _ => True ⦄ := by
  unfold player.Player.regulate
  run

@[step]
theorem limited_total (p : player.Player) (correction : Std.I64) (frames : Std.U32)
    (scheduled : Std.I64) :
    player.Player.limited p correction frames scheduled ⦃ _ => True ⦄ := by
  unfold player.Player.limited
  run

@[step]
theorem play_total (p : player.Player) (frames : Std.U32) (scheduled behind duration : Std.I64) :
    player.Player.play p frames scheduled behind duration ⦃ _ => True ⦄ := by
  unfold player.Player.play
  run

@[step]
theorem jumps_total (p : player.Player) (behind : Std.I64) :
    player.Player.jumps p behind ⦃ _ => True ⦄ := by
  unfold player.Player.jumps
  run

/-- Planning a cycle returns, for every state of the regulator and every
schedule. -/
@[step]
theorem cycle_total (p : player.Player) (now later : timing.Position) (frames : Std.U32)
    (duration : Std.I64) :
    player.Player.cycle p now later frames duration ⦃ _ => True ⦄ := by
  unfold player.Player.cycle
  run

@[step]
theorem stop_total (p : player.Player) : player.Player.stop p ⦃ _ => True ⦄ := by
  unfold player.Player.stop
  simp

end Unisono.Player
