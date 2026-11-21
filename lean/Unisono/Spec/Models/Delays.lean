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
# A probabilistic model of the network: delays, pauses and losses

The model decomposes the delay as the design document `docs/model.md`
does in its section on disturbances. On each link from one host to another, a
message sent at true time `s` waits, if the link is paused at `s`, until the
link releases it: at the first moment `u ≥ s` at which the link holds
nothing back. The message is then lost if the link is in an outage at `u`,
or if it is one of the messages that the link drops individually. Otherwise
it arrives at `u + baseline u + jitter u`.

* The **baseline** is the least time a message takes. It is positive and
  changes slowly.
* The **jitter** is how much longer than the baseline a message takes. It is
  never negative, comes arbitrarily close to zero, and large values are
  rare.
* A **pause** holds back every message sent during it and releases them all
  when it ends, so the first message sent in a pause is late by the pause's
  whole length. Messages released together arrive together: the model
  ignores the time a link takes to send out the messages it held. An
  **outage** is a pause that drops the messages instead.

`Link` and `World.HasDelays` define what the delays consist of, without
probability; `DelayModel.Holds` gives their distribution. The state of all
links over time (each link's jitter, and whether it is paused or in an
outage) is jointly stationary and mixing, and so is the sequence of
individually dropped messages. Mixing makes long-run averages, taken at
regularly spaced times, equal their expectations almost surely. Together
with the conditions that a pause or an outage is under way at a given time
with probability less than one, that a message is dropped individually with
probability less than one, and that episodes have finite mean length, this
means that almost surely no link drops every message or holds a message
forever. Nothing else is assumed independent: links may be correlated,
pauses may come in clusters, and the jitter, the pauses and the losses may
depend on each other. Two messages sent on the same link at the same instant
arrive at the same time if both are delivered.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory Filter Topology
open scoped ENNReal

/-- An episode of a link: from true time `start`, for `length` seconds, the
link holds back the messages sent on it (a pause) or, if `loses`, drops them
(an outage). -/
structure Pause where
  start : Time
  length : ℝ
  loses : Bool

/-- An episode is under way at true time `u`. -/
def Pause.On (p : Pause) (u : Time) : Prop :=
  p.start ≤ u ∧ u < p.start + p.length

/-- The delays of one link, from one host to another. -/
structure Link where
  /-- The least time that a message released at each true time takes. -/
  baseline : Time → ℝ
  /-- How much longer than the baseline a message released at each true
  time takes. -/
  jitter : Time → ℝ
  /-- The pauses and outages of the link. -/
  pauses : Set Pause
  /-- The messages that the link drops individually, by their number on the
  link, counted from zero as in `Network.deliver`. -/
  lost : Set ℕ

namespace Link

/-- The link holds back the messages sent at true time `u`: a pause is
under way. -/
def Holds (d : Link) (u : Time) : Prop :=
  ∃ p ∈ d.pauses, p.loses = false ∧ p.On u

/-- The link drops the messages it releases at true time `u`: an outage is
under way. -/
def Loses (d : Link) (u : Time) : Prop :=
  ∃ p ∈ d.pauses, p.loses = true ∧ p.On u

/-- When the link releases a message sent at true time `s`: at the first
moment from `s` on at which it holds nothing back; `none`, and the message
is dropped, if that moment never comes. -/
def release (d : Link) (s : Time) : Option Time := by
  classical
  exact if ∃ u, s ≤ u ∧ ¬ d.Holds u then some (sInf {u | s ≤ u ∧ ¬ d.Holds u}) else none

/-- When the `q`-th message on the link, sent at true time `s`, arrives:
the baseline and the jitter after the link releases it, at the time of the
release; `none` if the link drops it. -/
def deliver (d : Link) (s : Time) (q : ℕ) : Option Time := by
  classical
  exact match d.release s with
    | some u => if q ∈ d.lost ∨ d.Loses u then none else some (u + d.baseline u + d.jitter u)
    | none => none

/-- The state of a link at true time `u`: its jitter, whether a pause is
under way, and whether an outage is under way. -/
def state (d : Link) (u : Time) : ℝ × Bool × Bool := by
  classical
  exact (d.jitter u, decide (d.Holds u), decide (d.Loses u))

/-- A link releases a message no earlier than it is sent. -/
theorem le_release (d : Link) {s u : Time} (h : d.release s = some u) : s ≤ u := by
  unfold release at h
  split_ifs at h with hex
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨v, hv⟩ := hex
  exact le_csInf ⟨v, hv⟩ fun x hx => hx.1

/-- A message arrives after it is sent, when the baseline is positive and the
jitter is not negative. -/
theorem deliver_after (d : Link) {s : Time} {q : ℕ} {a : Time} (hb : ∀ u, 0 < d.baseline u)
    (hj : ∀ u, 0 ≤ d.jitter u) (h : d.deliver s q = some a) : s < a := by
  unfold deliver at h
  split at h
  · rename_i u hu
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    linarith [d.le_release hu, hb u, hj u]
  · simp at h

end Link

/-- The network of a world consists of the links `d`: messages from host `i`
to host `j` take the delays of `d i j`. -/
def World.HasDelays {H : Type} {R : ℕ} (w : World H R) (d : H → H → Link) : Prop :=
  ∀ i j s q, w.network.deliver i j s q = (d i j).deliver s q

/-- The parameters of the model. -/
structure DelayModel where
  /-- The baseline changes by at most `slope` seconds per second. -/
  slope : ℝ
  slope_nonneg : 0 ≤ slope
  /-- A jitter above `x` seconds has probability at most
  `tailFactor * exp (-x / tailScale)`. -/
  tailFactor : ℝ
  tailFactor_pos : 0 < tailFactor
  tailScale : ℝ
  tailScale_pos : 0 < tailScale
  /-- How many episodes start on a link per second, on average: pauses for
  `false`, outages for `true`. -/
  pauseRate : Bool → ℝ
  pauseRate_nonneg : ∀ kind, 0 ≤ pauseRate kind
  /-- The distribution of the length of an episode, for each kind. Lengths
  are positive. -/
  pauseLength : Bool → Measure ℝ
  pauseLength_probability : ∀ kind, IsProbabilityMeasure (pauseLength kind)
  pauseLength_pos : ∀ kind, pauseLength kind (Set.Iic 0) = 0
  /-- Episodes have a finite mean length. -/
  pauseLength_mean : ∀ kind, ∫⁻ x, ENNReal.ofReal x ∂(pauseLength kind) < ⊤
  /-- The probability that the link drops a message individually; less than
  one, since a link that drops every message carries nothing. -/
  lossProbability : ℝ
  lossProbability_nonneg : 0 ≤ lossProbability
  lossProbability_lt_one : lossProbability < 1

variable {H : Type} {Ω : Type} [MeasurableSpace Ω]

/-- A random variable `X` is stationary under the shifts `shift`: shifting
it does not change its distribution. -/
def Stationary {β : Type} [MeasurableSpace β] {T : Type} (P : Measure Ω) (X : Ω → β)
    (shift : T → β → β) : Prop :=
  ∀ τ, P.map (fun ω => shift τ (X ω)) = P.map X

/-- A random variable `X` is mixing under the shifts `shift`: for any two
events about `X`, the probability that the first holds and the second holds
after a shift by `τ` tends, as `τ` grows, to the product of their
probabilities. -/
def Mixing {β : Type} [MeasurableSpace β] {T : Type} [Preorder T] (P : Measure Ω) (X : Ω → β)
    (shift : T → β → β) : Prop :=
  ∀ A B : Set β, MeasurableSet A → MeasurableSet B →
    Tendsto (fun τ => P {ω | X ω ∈ A ∧ shift τ (X ω) ∈ B}) atTop
      (𝓝 (P {ω | X ω ∈ A} * P {ω | X ω ∈ B}))

/-- The states of all the links of the network `d ω`, at all times. -/
def linkStates (d : Ω → H → H → Link) (ω : Ω) : H → H → Time → ℝ × Bool × Bool :=
  fun i j u => (d ω i j).state u

/-- The individually dropped messages on all the links of the network
`d ω`, by their number on the link. -/
def droppedMessages (d : Ω → H → H → Link) (ω : Ω) : H → H → ℕ → Bool := by
  classical
  exact fun i j q => decide (q ∈ (d ω i j).lost)

/-- A function of time on every link, shifted by `τ` seconds: its value at
`u` is the one at `u + τ`. -/
def shiftTime {α : Type} (τ : ℝ) (x : H → H → Time → α) : H → H → Time → α :=
  fun i j u => x i j (u + τ)

/-- A function of the message number on every link, shifted by `m`
messages. -/
def shiftCount {α : Type} (m : ℕ) (x : H → H → ℕ → α) : H → H → ℕ → α :=
  fun i j q => x i j (q + m)

/-- A random network, `d ω` for `ω` drawn from `P`, follows the model. -/
structure DelayModel.Holds (m : DelayModel) (P : Measure Ω) (d : Ω → H → H → Link) : Prop where
  /-- The baseline is positive. -/
  baseline_pos : ∀ ω i j u, 0 < (d ω i j).baseline u
  /-- The baseline changes by at most `slope` seconds per second. -/
  baseline_slow : ∀ ω i j u u',
    |(d ω i j).baseline u - (d ω i j).baseline u'| ≤ m.slope * |u - u'|
  /-- The jitter is never negative. -/
  jitter_nonneg : ∀ ω i j u, 0 ≤ (d ω i j).jitter u
  /-- The jitter comes arbitrarily close to zero, so that the baseline is the
  least time a message takes. -/
  jitter_near_zero : ∀ i j u δ, 0 < δ → 0 < P {ω | (d ω i j).jitter u < δ}
  /-- Large jitter is rare: a jitter above `x` seconds has probability at
  most `tailFactor * exp (-x / tailScale)`. -/
  jitter_tail : ∀ i j u x, 0 ≤ x →
    P {ω | x < (d ω i j).jitter u} ≤ ENNReal.ofReal (m.tailFactor * Real.exp (-x / m.tailScale))
  /-- Episodes have positive lengths. -/
  pause_length_pos : ∀ ω i j p, p ∈ (d ω i j).pauses → 0 < p.length
  /-- A pause is under way at a given time with probability less than one. -/
  paused_lt_one : ∀ i j u, P {ω | (d ω i j).Holds u} < 1
  /-- An outage is under way at a given time with probability less than
  one. -/
  outage_lt_one : ∀ i j u, P {ω | (d ω i j).Loses u} < 1
  /-- Episodes of each kind start at the rate `pauseRate`, with lengths
  distributed as `pauseLength`: on any link, the mean number of episodes of
  a kind that start within any `t` seconds and whose length is in a set `A`
  is `pauseRate * t * pauseLength A`. -/
  pauses : ∀ i j kind (a t : ℝ) (A : Set ℝ), 0 ≤ t → MeasurableSet A →
    ∫⁻ ω, (((d ω i j).pauses ∩
        {p | p.loses = kind ∧ a ≤ p.start ∧ p.start < a + t ∧ p.length ∈ A}).encard : ℝ≥0∞) ∂P
      = ENNReal.ofReal (m.pauseRate kind * t) * m.pauseLength kind A
  /-- Each message is dropped individually with probability
  `lossProbability`. -/
  lost : ∀ i j q, P {ω | q ∈ (d ω i j).lost} = ENNReal.ofReal m.lossProbability
  /-- The state of each link at each time is a random variable. -/
  state_measurable : ∀ i j u, Measurable fun ω => (d ω i j).state u
  /-- Whether each message is dropped individually is a random event. -/
  lost_measurable : ∀ i j q, MeasurableSet {ω | q ∈ (d ω i j).lost}
  /-- The states of all links over time are jointly stationary. -/
  states_stationary : Stationary P (linkStates d) shiftTime
  /-- The states of all links over time are jointly mixing. -/
  states_mixing : Mixing P (linkStates d) shiftTime
  /-- The individually dropped messages of all links are jointly stationary
  in the message number. -/
  dropped_stationary : Stationary P (droppedMessages d) shiftCount
  /-- The individually dropped messages of all links are jointly mixing in
  the message number. -/
  dropped_mixing : Mixing P (droppedMessages d) shiftCount

/-- A random world, `world ω` for `ω` drawn from `P`, follows the model: `P`
is a probability measure, and the network of each world consists of links
that follow the model. -/
def DelayModel.Random (m : DelayModel) {R : ℕ} (P : Measure Ω) (world : Ω → World H R) :
    Prop :=
  IsProbabilityMeasure P ∧ ∃ d : Ω → H → H → Link, (∀ ω, (world ω).HasDelays (d ω)) ∧ m.Holds P d

end Unisono.Spec
