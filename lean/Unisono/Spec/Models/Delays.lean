/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.World
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# A model of the network with laws of chance: delays, pauses and losses

The model of the earlier work. On each way from one host to another, a
message sent at true time `s` takes

* the **baseline** at `s`: the least time a message takes, which changes
  slowly;
* plus the **jitter** at `s`: how much longer than the baseline it takes.
  It is never negative and rarely large; it has the same law at all times,
  and at times far apart it is nearly independent;
* plus, when `s` falls in a **pause** of the way, the time until the pause
  ends. The way holds back every message sent during a pause and lets them
  go when it ends, so the first message sent in a pause is late by the
  pause's whole length.

Two kinds of loss come on top: a pause may lose the messages sent during it
instead of holding them back (an outage), and single messages may be lost.

`Way` and `World.HasDelays` say what the delays are made of, with no chance
in it; `DelayModel.Holds` gives the laws of chance. Nothing is assumed
independent: the ways between different hosts may be alike, pauses may come
in clusters, and the jitter, the pauses and the losses may depend on each
other.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory Filter Topology
open scoped ENNReal

/-- A pause of a way: from true time `start`, for `length` seconds. -/
structure Pause where
  start : Time
  length : ℝ
  /-- Whether the way loses the messages sent during the pause, instead of
  holding them back until it ends. -/
  loses : Bool

/-- A pause is on at true time `u`. -/
def Pause.On (p : Pause) (u : Time) : Prop :=
  p.start ≤ u ∧ u < p.start + p.length

/-- The delays of one way, from one host to another. -/
structure Way where
  /-- The least time that a message sent at each true time takes. -/
  baseline : Time → ℝ
  /-- How much longer than the baseline a message sent at each true time
  takes. -/
  jitter : Time → ℝ
  /-- The pauses of the way. -/
  pauses : Set Pause
  /-- The messages lost on their own, by their number on the way, counted
  from zero as in `Network.deliver`. -/
  lost : Set ℕ

namespace Way

/-- The way holds back the messages sent at true time `u`. -/
def Holds (d : Way) (u : Time) : Prop :=
  ∃ p ∈ d.pauses, p.loses = false ∧ p.On u

/-- The way loses the messages sent at true time `u`. -/
def Loses (d : Way) (u : Time) : Prop :=
  ∃ p ∈ d.pauses, p.loses = true ∧ p.On u

/-- When the way lets go of a message sent at true time `s`: the first
moment from `s` on at which it holds nothing back; `none` if that never
comes. -/
def release (d : Way) (s : Time) : Option Time := by
  classical
  exact if ∃ u, s ≤ u ∧ ¬ d.Holds u then some (sInf {u | s ≤ u ∧ ¬ d.Holds u}) else none

/-- When the message sent at true time `s` as the `q`-th on the way arrives:
when the way lets it go, plus the baseline and the jitter at `s`; `none` if
it is lost. -/
def deliver (d : Way) (s : Time) (q : ℕ) : Option Time := by
  classical
  exact if q ∈ d.lost ∨ d.Loses s then none
    else (d.release s).map fun u => u + d.baseline s + d.jitter s

/-- A message arrives after it is sent, when the baseline is positive and the
jitter is not negative. -/
theorem deliver_after (d : Way) {s : Time} {q : ℕ} {a : Time} (hb : 0 < d.baseline s)
    (hj : 0 ≤ d.jitter s) (h : d.deliver s q = some a) : s < a := by
  unfold deliver release at h
  split_ifs at h with hlost hex
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have : s ≤ sInf {u | s ≤ u ∧ ¬ d.Holds u} := by
      obtain ⟨u, hu⟩ := hex
      exact le_csInf ⟨u, hu⟩ fun v hv => hv.1
    linarith
  · simp at h

end Way

/-- The network of a world is made of the ways `d`: the messages from host
`i` to host `j` take the delays of `d i j`. -/
def World.HasDelays {H : Type} {R : ℕ} (w : World H R) (d : H → H → Way) : Prop :=
  ∀ i j s q, w.network.deliver i j s q = (d i j).deliver s q

/-- The parameters of the model. -/
structure DelayModel where
  /-- The baseline changes by at most `slope` seconds per second. -/
  slope : ℝ
  /-- A jitter above `x` seconds has probability at most
  `tailFactor * exp (-x / tailScale)`. -/
  tailFactor : ℝ
  tailScale : ℝ
  /-- How many pauses start on a way per second, on average: of pauses that
  hold messages back for `false`, of pauses that lose them for `true`. -/
  pauseRate : Bool → ℝ
  /-- The law of the length of a pause, for each kind. -/
  pauseLength : Bool → Measure ℝ
  pauseLength_probability : ∀ kind, IsProbabilityMeasure (pauseLength kind)
  /-- The probability that a message is lost on its own. -/
  lossProbability : ℝ

variable {H : Type} {Ω : Type} [MeasurableSpace Ω]

/-- The jitters of all the ways of the network `d ω`, at all times. -/
def jitters (d : Ω → H → H → Way) (ω : Ω) : H → H → Time → ℝ :=
  fun i j s => (d ω i j).jitter s

/-- Jitters at all times, moved by `τ` seconds: the value at time `s` is the
one at time `s + τ`. -/
def shiftTime (τ : ℝ) (x : H → H → Time → ℝ) : H → H → Time → ℝ :=
  fun i j s => x i j (s + τ)

/-- A random network, `d ω` for `ω` drawn from `P`, follows the laws of the
model. -/
structure DelayModel.Holds (m : DelayModel) (P : Measure Ω) (d : Ω → H → H → Way) : Prop where
  /-- The baseline is positive. -/
  baseline_pos : ∀ ω i j s, 0 < (d ω i j).baseline s
  /-- The baseline changes by at most `slope` seconds per second. -/
  baseline_slow : ∀ ω i j s s',
    |(d ω i j).baseline s - (d ω i j).baseline s'| ≤ m.slope * |s - s'|
  /-- The jitter is never negative. -/
  jitter_nonneg : ∀ ω i j s, 0 ≤ (d ω i j).jitter s
  /-- The jitter of each way at each time is a random variable. -/
  jitter_measurable : ∀ i j s, Measurable fun ω => (d ω i j).jitter s
  /-- Large jitter is rare: a jitter above `x` seconds has probability at
  most `tailFactor * exp (-x / tailScale)`. -/
  jitter_tail : ∀ i j s x, 0 ≤ x →
    P {ω | x < (d ω i j).jitter s} ≤ ENNReal.ofReal (m.tailFactor * Real.exp (-x / m.tailScale))
  /-- The jitter has the same law at all times: moving the jitters of all
  the ways in time does not change their joint law. -/
  jitter_stationary : ∀ τ, P.map (fun ω => shiftTime τ (jitters d ω)) = P.map (jitters d)
  /-- The jitter at times far apart is nearly independent: for any two
  events about the jitters, the probability that the first holds and the
  second holds `τ` seconds later tends, as `τ` grows, to the product of
  their probabilities. -/
  jitter_mixing : ∀ A B : Set (H → H → Time → ℝ), MeasurableSet A → MeasurableSet B →
    Tendsto (fun τ => P {ω | jitters d ω ∈ A ∧ shiftTime τ (jitters d ω) ∈ B}) atTop
      (𝓝 (P {ω | jitters d ω ∈ A} * P {ω | jitters d ω ∈ B}))
  /-- Pauses of each kind start at the rate `pauseRate`, with lengths of the
  law `pauseLength`: on any way, the mean number of pauses of a kind that
  start within any `t` seconds and whose length is in a set `A` is
  `pauseRate * t * pauseLength A`. -/
  pauses : ∀ i j kind (a t : ℝ) (A : Set ℝ), 0 ≤ t → MeasurableSet A →
    ∫⁻ ω, (((d ω i j).pauses ∩
        {p | p.loses = kind ∧ a ≤ p.start ∧ p.start < a + t ∧ p.length ∈ A}).encard : ℝ≥0∞) ∂P
      = ENNReal.ofReal (m.pauseRate kind * t) * m.pauseLength kind A
  /-- Each message is lost on its own with probability `lossProbability`. -/
  lost : ∀ i j q, P {ω | q ∈ (d ω i j).lost} = ENNReal.ofReal m.lossProbability

/-- A random world, `world ω` for `ω` drawn from `P`, follows the model: `P`
is a probability measure, and the network of each world is made of ways that
follow the model's laws. -/
def DelayModel.Random (m : DelayModel) {R : ℕ} (P : Measure Ω) (world : Ω → World H R) :
    Prop :=
  IsProbabilityMeasure P ∧ ∃ d : Ω → H → H → Way, (∀ ω, (world ω).HasDelays (d ω)) ∧ m.Holds P d

end Unisono.Spec
