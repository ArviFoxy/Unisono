/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Solution

/-!
# The objectives

What we want of a run, measured in true time, from what each speaker plays at
each of its output samples: the source's content at a position, or not.

* **Synchronisation:** every speaker plays a frame of the source at the same
  true time.
* **Latency:** every speaker plays a frame soon after it was captured.
* **Tracking** (lip-sync mode): every speaker plays a frame a target latency
  after it was captured.
* **Roughness:** the speed at which a speaker plays the source, against the
  speed at which it was captured, changes slowly. A speed of one is the
  original pitch and tempo; the roughness is the integral of the square of
  the derivative of the speed, as in the earlier warp cost.
* **Missed samples:** every output sample plays the original sample in its
  place. An output sample that plays anything else, and a frame of the
  source that a jump skips or plays a second time, is a missed sample; it
  counts once whatever caused it.

Each objective is a long-run average over true time. The cost of a run is
the long-run average of their weighted sum; the weights are parameters, and
so are the solutions that answer them. The two modes are two kinds of
weights: low latency weighs latency and not tracking, lip sync the reverse.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-! ## A speaker's playback

`plays k` is what a speaker plays at its output sample `k`: the source's
content at a position in frames, or `none` for anything else. -/

/-- The playback goes on from output sample `k` to the next: both play the
source, and the content advances by more than nothing and by less than two
frames, so that no frame is skipped and none is played twice. -/
def Continues (plays : ℕ → Option ℝ) (k : ℕ) : Prop :=
  ∃ x y, plays k = some x ∧ plays (k + 1) = some y ∧ x < y ∧ y < x + 2

/-- The step of the playback from output sample `k` to the next goes on and
passes frame `n`. -/
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
  frames that its content skips or plays again, beyond those that the output
  samples in between, which played something else, already counted.

Its content advances from that of the last output sample before it that
played the source by `y - x`. Going on, it advances by one frame for each
output sample, `gap + 1` frames after `gap` output samples that played
something else. It skips `⌊y - x - 1⌋` frames when that is positive, of
which `gap` are counted already, and plays `⌊1 - (y - x)⌋` frames again
when that is positive. -/
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
output sample `k` to the next: the time between the captures of the content
at either end of the step, divided by the time between the two output
samples leaving the device. A speed of one is the original pitch and tempo.
`none` where the playback does not go on. -/
def speed (r : Fin R) (k : ℕ) : Option ℝ := by
  classical
  exact match plays r k, plays r (k + 1) with
  | some x, some y =>
      if x < y ∧ y < x + 2 then
        some ((w.captured y - w.captured x) / ((w.speaker r).out (k + 1) - (w.speaker r).out k))
      else none
  | _, _ => none

/-! ## The cost of each objective at a frame or an output sample -/

/-- Synchronisation at frame `n`: the squares of the differences between the
times at which two speakers play the frame, over all pairs of speakers that
both play it, divided by the square of the number of speakers. When every
speaker plays the frame this is the variance of their times. -/
def syncCost (n : ℕ) : ℝ≥0∞ :=
  ((R : ℝ≥0∞) ^ 2)⁻¹ * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
    match w.playTime plays p.1 n, w.playTime plays p.2 n with
    | some t, some t' => ENNReal.ofReal ((t - t') ^ 2)
    | _, _ => 0

/-- Latency at frame `n`: its latency at each speaker that plays it, summed
and divided by the number of speakers. A speaker that does not play the
frame adds nothing here, and counts missed samples instead. -/
def latencyCost (n : ℕ) : ℝ≥0∞ :=
  (R : ℝ≥0∞)⁻¹ * ∑ r, match w.latency plays r n with
    | some l => ENNReal.ofReal l
    | none => 0

/-- Tracking at frame `n`, for target latencies `target`: the square of the
difference between its latency and the target, averaged over the speakers
that play it. -/
def trackingCost (target : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  (R : ℝ≥0∞)⁻¹ * ∑ r, match w.latency plays r n with
    | some l => ENNReal.ofReal ((l - target n) ^ 2)
    | none => 0

/-- Roughness at output sample `k + 1` of speaker `r`: the square of how much
the speed changes there, divided by how long it takes to change, half the
time from output sample `k` to `k + 2`. Over a playback that goes on, the
sum is the integral of the square of the speed's derivative. -/
def roughnessCost (r : Fin R) (k : ℕ) : ℝ≥0∞ :=
  match w.speed plays r k, w.speed plays r (k + 1) with
  | some v, some v' =>
      ENNReal.ofReal ((v' - v) ^ 2 / (((w.speaker r).out (k + 2) - (w.speaker r).out k) / 2))
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
the horizon grows, of the cost accrued per second. -/
def longRun (accrued : Time → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup (fun T : Time => accrued T / ENNReal.ofReal T) Filter.atTop

/-- The weights of the objectives. A solution is designed for given weights;
the specification leaves them as parameters. Low latency mode has a zero
weight for tracking; lip-sync mode has a zero weight for latency. -/
structure Weights where
  sync : ℝ≥0
  latency : ℝ≥0
  tracking : ℝ≥0
  roughness : ℝ≥0
  missed : ℝ≥0

namespace World

variable (w : World H R) (plays : Fin R → ℕ → Option ℝ)

/-- Synchronisation, as a long-run average: the variance, over the speakers,
of when they play the same frame, in square seconds. -/
def sync : ℝ≥0∞ := longRun (w.accruedFrames (w.syncCost plays))

/-- Latency, as a long-run average over the speakers, in seconds. -/
def meanLatency : ℝ≥0∞ := longRun (w.accruedFrames (w.latencyCost plays))

/-- Tracking of the target latencies `target`, as a long-run average: the
mean square of the difference between latency and target, in square
seconds. -/
def tracking (target : ℕ → ℝ) : ℝ≥0∞ := longRun (w.accruedFrames (w.trackingCost plays target))

/-- Roughness, as a long-run average over the speakers: the square of the
derivative of the speed, per second. -/
def roughness : ℝ≥0∞ := longRun (w.accruedOutputs (w.roughnessCost plays))

/-- Missed samples, as a long-run average over the speakers: missed samples
per second. -/
def missed : ℝ≥0∞ := longRun (w.accruedOutputs fun r k => (missedAt (plays r) k : ℝ≥0∞))

/-- The cost of a playback, for target latencies `target` and weights `c`:
the long-run average of the weighted sum of what the five objectives
accrue. -/
def cost (target : ℕ → ℝ) (c : Weights) : ℝ≥0∞ :=
  longRun fun T =>
    c.sync * w.accruedFrames (w.syncCost plays) T
      + c.latency * w.accruedFrames (w.latencyCost plays) T
      + c.tracking * w.accruedFrames (w.trackingCost plays target) T
      + c.roughness * w.accruedOutputs (w.roughnessCost plays) T
      + c.missed * w.accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) T

end World

variable {Msg : Type}

/-- The cost of a solution in a world: that of its worst run there. -/
def Solution.cost [DecidableEq H] (σ : Solution H R Msg) (w : World H R) (target : ℕ → ℝ)
    (c : Weights) : ℝ≥0∞ :=
  ⨆ ρ ∈ σ.runs w, w.cost ρ.plays target c

/-- The expected cost of a solution when the world is random: the world is
`world ω`, with `ω` drawn from the probability measure `P`. -/
def Solution.expectedCost [DecidableEq H] {Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (world : Ω → World H R) (σ : Solution H R Msg)
    (target : ℕ → ℝ) (c : Weights) : ℝ≥0∞ :=
  ∫⁻ ω, σ.cost (world ω) target c ∂P

end Unisono.Spec
