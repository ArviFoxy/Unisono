/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Solution

/-!
# The objectives

What we want of a playback, measured in true time, from what each speaker
plays at each of its output samples: the sound of the source at a position,
or something else.

* **Synchronization:** every speaker plays each frame of the source at the
  same true time.
* **Latency:** every speaker plays each frame soon after it was captured.
* **Tracking** (lip-sync mode): every speaker plays each frame at the target
  latency that the application sets for it.
* **Roughness:** the speed at which a speaker plays the source changes
  slowly. A speed of one is the original pitch and tempo. The roughness is
  the integral of the square of the speed's derivative, the earlier work's
  warp cost; it also charges a change of speed across a break in playback.
* **Missed samples:** every output sample plays the original sound in its
  place. Each output sample that does not, and each frame that a jump skips
  or plays a second time, counts once, whatever is played instead.
* **Discontinuities:** playback is continuous. Each break (the start of a
  gap, or a jump forward or back) counts once, however long it lasts.

Each objective is a long-run average over true time. The cost of a playback
is the long-run average of their weighted sum; the weights are parameters,
and so are the solutions designed for them. The two modes are two kinds of
weights: low-latency mode has a zero weight for tracking, lip-sync mode a
zero weight for latency.

A speed bound, a parameter like the network's capacity, limits how far from
one the speed may be (`Solution.WithinSpeed`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-! ## A speaker's playback

`plays k` is what a speaker plays at its output sample `k`: the sound of the
source at a position in frames, or `none` for anything else. -/

/-- Playback is continuous from output sample `k` to the next: both play the
source, and the position advances by more than zero and less than two
frames, so that no frame is skipped and none is played twice. -/
def PlaysContinuously (plays : ℕ → Option ℝ) (k : ℕ) : Prop :=
  ∃ x y, plays k = some x ∧ plays (k + 1) = some y ∧ x < y ∧ y < x + 2

/-- The step of the playback from output sample `k` to the next is
continuous and passes frame `n`. -/
def Covers (plays : ℕ → Option ℝ) (k n : ℕ) : Prop :=
  ∃ x y, plays k = some x ∧ plays (k + 1) = some y ∧ x < y ∧ y < x + 2
    ∧ x ≤ n ∧ (n : ℝ) ≤ y

/-- When a playback plays frame `n` of the source, given when each output
sample leaves (`out`): within the first step that passes the frame, between
the times at which the step's two output samples leave, in proportion.
`none` if no step passes it. -/
def playTime (out : ℕ → Time) (plays : ℕ → Option ℝ) (n : ℕ) : Option Time := by
  classical
  exact if h : ∃ k, Covers plays k n then
    match plays (Nat.find h), plays (Nat.find h + 1) with
    | some x, some y =>
        some (out (Nat.find h) + (n - x) / (y - x) * (out (Nat.find h + 1) - out (Nat.find h)))
    | _, _ => none
  else none

/-- The missed samples counted at output sample `k` of a playback.

* An output sample that does not play the source counts one.
* An output sample that plays the source, after earlier ones did, counts the
  frames that its position skips or plays again, beyond those that the
  output samples in between, which played something else, already counted.

Its position advances from that of the last output sample before it that
played the source by `y - x`. In continuous playback it advances by one
frame for each output sample, `gap + 1` frames after `gap` output samples
that played something else. It skips `⌊y - x - 1⌋` frames when that is
positive, of which `gap` are counted already, and plays `⌊1 - (y - x)⌋`
frames again when that is positive. -/
def missedAt (plays : ℕ → Option ℝ) (k : ℕ) : ℕ := by
  classical
  exact match plays k with
  | none => 1
  | some y =>
      if ∃ j < k, (plays j).isSome then
        match plays (Nat.findGreatest (fun j => (plays j).isSome) (k - 1)) with
        | some x =>
            (⌊y - x - 1⌋ - ((k - 1 - Nat.findGreatest (fun j => (plays j).isSome) (k - 1) : ℕ) : ℤ)).toNat
              + ⌊1 - (y - x)⌋.toNat
        | none => 0
      else 0

/-- The discontinuities counted at output sample `k`: one if playback breaks
there, when output sample `k` plays the source and the next one does not
continue it (it plays something else, or jumps forward or back); none
otherwise. A gap counts once, at its start, however long it lasts. -/
def discontinuityAt (plays : ℕ → Option ℝ) (k : ℕ) : ℕ := by
  classical
  exact if (plays k).isSome ∧ ¬ PlaysContinuously plays k then 1 else 0

/-- The next step after step `k` at which playback is continuous, if there
is one. -/
def nextContinuous (plays : ℕ → Option ℝ) (k : ℕ) : Option ℕ := by
  classical
  exact if h : ∃ j, k < j ∧ PlaysContinuously plays j then some (Nat.find h) else none

namespace World

variable (w : World H R) (plays : Fin R → ℕ → Option ℝ)

/-- When speaker `r` plays frame `n`. -/
def playTime (r : Fin R) (n : ℕ) : Option Time :=
  Spec.playTime (w.speaker r).out (plays r) n

/-- The latency of frame `n` at speaker `r`: how long after the frame was
captured the speaker plays it. -/
def latency (r : Fin R) (n : ℕ) : Option ℝ :=
  (w.playTime plays r n).map (· - w.source.capture n)

/-- The speed at which speaker `r` plays the source over the step from
output sample `k` to the next: the time between the captures of the sound at
the positions played at either end of the step, divided by the time between
the two output samples leaving the device. A speed of one is the original
pitch and tempo. `none` where playback is not continuous. -/
def speed (r : Fin R) (k : ℕ) : Option ℝ := by
  classical
  exact match plays r k, plays r (k + 1) with
  | some x, some y =>
      if x < y ∧ y < x + 2 then
        some ((w.captured y - w.captured x) / ((w.speaker r).out (k + 1) - (w.speaker r).out k))
      else none
  | _, _ => none

/-! ## The cost of each objective at a frame or an output sample -/

/-- The square of the difference between the times at which speakers `r` and
`r'` play frame `n`; zero unless both play it. -/
def pairCost (r r' : Fin R) (n : ℕ) : ℝ≥0∞ :=
  match w.playTime plays r n, w.playTime plays r' n with
  | some t, some t' => ENNReal.ofReal ((t - t') ^ 2)
  | _, _ => 0

/-- Synchronization at frame `n`: the squares of the differences between the
times at which two speakers play the frame, summed over all pairs of
speakers that both play it, divided by the square of the number of speakers.
When every speaker plays the frame this is the variance of their times. -/
def syncCost (n : ℕ) : ℝ≥0∞ :=
  ((R : ℝ≥0∞) ^ 2)⁻¹ * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
    w.pairCost plays p.1 p.2 n

/-- The latency of frame `n` at speaker `r`; zero if the speaker does not
play the frame, which counts missed samples instead. -/
def latencyAt (r : Fin R) (n : ℕ) : ℝ≥0∞ :=
  match w.latency plays r n with
  | some l => ENNReal.ofReal l
  | none => 0

/-- Latency at frame `n`: its latency at each speaker that plays it, summed
and divided by the number of speakers. -/
def latencyCost (n : ℕ) : ℝ≥0∞ :=
  (R : ℝ≥0∞)⁻¹ * ∑ r, w.latencyAt plays r n

/-- The square of the difference between the latency of frame `n` at speaker
`r` and the target latency; zero if the speaker does not play the frame. -/
def trackingAt (r : Fin R) (n : ℕ) : ℝ≥0∞ :=
  match w.latency plays r n with
  | some l => ENNReal.ofReal ((l - w.target n) ^ 2)
  | none => 0

/-- Tracking at frame `n`: the square of the difference between its latency
and the target latency, summed over the speakers that play it and divided by
the number of speakers. -/
def trackingCost (n : ℕ) : ℝ≥0∞ :=
  (R : ℝ≥0∞)⁻¹ * ∑ r, w.trackingAt plays r n

/-- Roughness between step `k` of speaker `r`'s playback, from output sample
`k` to the next, and the next step at which playback is continuous: the
square of the change of speed between the two steps, divided by the time
between their midpoints. In continuous playback the two steps are
neighbours, and the sum is the integral of the square of the speed's
derivative. Across a break it is what a speed changing linearly over the
break would cost, the least that any change of speed over that time costs,
so a break does not hide a change of speed. -/
def roughnessCost (r : Fin R) (k : ℕ) : ℝ≥0∞ :=
  match w.speed plays r k, nextContinuous (plays r) k with
  | some v, some j =>
      match w.speed plays r j with
      | some v' =>
          ENNReal.ofReal ((v' - v) ^ 2 / (((w.speaker r).out j + (w.speaker r).out (j + 1)
            - (w.speaker r).out k - (w.speaker r).out (k + 1)) / 2))
      | none => 0
  | _, _ => 0

/-! ## Long-run averages -/

/-- A cost of each frame of the source, accrued until true time `T`: each
frame captured before `T` adds its cost times the time until the next frame
is captured, so that the sum is an integral over the time of capture. -/
def accruedFrames (cost : ℕ → ℝ≥0∞) (T : Time) : ℝ≥0∞ :=
  ∑' n, if w.source.capture n < T then
    cost n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0

/-- A cost of each output sample of each speaker, accrued until true time
`T` and averaged over the speakers: each output sample that leaves before
`T` adds its cost. -/
def accruedOutputs (cost : Fin R → ℕ → ℝ≥0∞) (T : Time) : ℝ≥0∞ :=
  (R : ℝ≥0∞)⁻¹ * ∑ r, ∑' k, if (w.speaker r).out k < T then cost r k else 0

end World

/-- The long-run average of a cost accrued over time: the limit superior, as
the horizon `T` grows, of the cost accrued per second. -/
def longRun (accrued : Time → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup (fun T : Time => accrued T / ENNReal.ofReal T) Filter.atTop

/-- The weights of the objectives. A solution is designed for given weights;
the specification leaves them as parameters. Low-latency mode has a zero
weight for tracking; lip-sync mode has a zero weight for latency. -/
structure Weights where
  sync : ℝ≥0
  latency : ℝ≥0
  tracking : ℝ≥0
  roughness : ℝ≥0
  missed : ℝ≥0
  discontinuities : ℝ≥0

namespace World

variable (w : World H R) (plays : Fin R → ℕ → Option ℝ)

/-- Synchronization, as a long-run average: the variance, over the speakers,
of when they play the same frame, in s². -/
def sync : ℝ≥0∞ := longRun (w.accruedFrames (w.syncCost plays))

/-- Latency, as a long-run average over the speakers, in s. -/
def meanLatency : ℝ≥0∞ := longRun (w.accruedFrames (w.latencyCost plays))

/-- Tracking of the target latency, as a long-run average: the mean square
of the difference between latency and target, in s². -/
def tracking : ℝ≥0∞ := longRun (w.accruedFrames (w.trackingCost plays))

/-- Roughness, as a long-run average over the speakers: the square of the
derivative of the speed, in s⁻². -/
def roughness : ℝ≥0∞ := longRun (w.accruedOutputs (w.roughnessCost plays))

/-- Missed samples, as a long-run average over the speakers, per second. -/
def missed : ℝ≥0∞ := longRun (w.accruedOutputs fun r k => (missedAt (plays r) k : ℝ≥0∞))

/-- Discontinuities, as a long-run average over the speakers, per second. -/
def discontinuities : ℝ≥0∞ :=
  longRun (w.accruedOutputs fun r k => (discontinuityAt (plays r) k : ℝ≥0∞))

/-- The cost of a playback, for weights `c`: the long-run average of the
weighted sum of what the six objectives accrue. -/
def cost (c : Weights) : ℝ≥0∞ :=
  longRun fun T =>
    c.sync * w.accruedFrames (w.syncCost plays) T
      + c.latency * w.accruedFrames (w.latencyCost plays) T
      + c.tracking * w.accruedFrames (w.trackingCost plays) T
      + c.roughness * w.accruedOutputs (w.roughnessCost plays) T
      + c.missed * w.accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) T
      + c.discontinuities * w.accruedOutputs (fun r k => (discontinuityAt (plays r) k : ℝ≥0∞)) T

end World

variable {Msg : Type} [DecidableEq H]

/-- The cost of a solution in a world, for a resampler lookahead of
`lookahead` frames and weights `c`: the cost of what its speakers play in
its run there. -/
def Solution.cost (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (c : Weights) :
    ℝ≥0∞ :=
  w.cost (σ.plays w lookahead) c

/-- The expected cost of a solution when the world is random: the world is
`world ω`, with `ω` drawn from the probability measure `P`. -/
def Solution.expectedCost {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (world : Ω → World H R) (σ : Solution H R Msg) (lookahead : ℕ+) (c : Weights) : ℝ≥0∞ :=
  ∫⁻ ω, σ.cost (world ω) lookahead c ∂P

/-- The run stays within the speed bound `uMax`: at every step of continuous
playback, every speaker's speed is within `uMax` of one. -/
def Solution.WithinSpeed (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+) (uMax : ℝ) :
    Prop :=
  ∀ r k v, w.speed (σ.plays w lookahead) r k = some v → |v - 1| ≤ uMax

end Unisono.Spec
