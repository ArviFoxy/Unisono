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
# Stationary network disturbances (delays, pauses, outages, and drops)

A probabilistic network-only model class (`StationaryNetworkDisturbances`) that
decomposes the end-to-end network delay of every directed link `(i, j)` into
slow baseline, exponential-tail jitter, pauses, outages, and individual packet
drops. Here a *link* from host `i` to host `j` covers the entire path between
the application's send and receive calls—including both hosts' kernel network
stacks, drivers, NICs, switches/APs, and the wire or wireless medium—which is
one reason links sharing a host or medium may exhibit correlated jitter.

On each directed link `(i, j)`, the `q`-th message sent at true time `s` waits,
if the link is paused at `s`, until the link releases it at the first moment
`u ≥ s` at which the link holds nothing back. The message is then dropped if
the link is in an outage at `u`, or if `q` is in the link's individually dropped
set `lost`. Otherwise it arrives at `u + baseline u + jitter u q`.

* **Baseline (`baseline : Time → ℝ`):** the least time a message takes on the
  link. It is positive and Lipschitz with per-link slope `slope i j`.
* **Per-packet jitter (`jitter : Time → ℕ → ℝ`):** how much longer than the
  baseline the `q`-th message takes when released at true time `u`. Indexing
  by `(u, q)` lets simultaneous messages (including a burst released at the
  end of a pause) experience distinct sequential jitter. Jitter is nonnegative,
  comes arbitrarily close to zero, and has per-link exponential upper tails
  `tailFactor i j * exp (-x / tailScale i j)`.
* **Pauses and outages (`pauses : Set Pause`):** a pause holds back messages
  sent during it and releases them when it ends; an outage drops messages
  released during it. Each directed link `(i, j)` has its own episode arrival
  rate `pauseRate i j kind` and length distribution `pauseLength i j kind`
  with finite mean, admitting mixed topologies (for example, reliable wired
  peer links combined with a lossy or bursty wireless sender link).
* **Individual drops (`lost : Set ℕ`):** each message on link `(i, j)` is
  dropped individually with per-link probability `lossProbability i j < 1`.

`Link` and `World.HasDelays` define the delay decomposition without
probability; `StationaryNetworkDisturbances.Holds` specifies the probabilistic
assumptions (joint stationarity and mixing of all links' states under time
shifts and of all links' individual drops under message-index shifts, with no
cross-link independence assumed). Combine this network-only model class with
`SecondOrderMoments` and device/blocking bounds in `StochasticWorld` for a
full-world probabilistic model class.
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

/-- The delays of one directed link, from one host to another (covering both
hosts' network stacks as well as the physical/wireless path between them). -/
structure Link where
  /-- The least time that a message released at each true time takes. -/
  baseline : Time → ℝ
  /-- How much longer than the baseline the `q`-th message on the link takes
  when released at true time `u`. Indexing by `(u, q)` allows simultaneous
  messages (such as a post-pause burst) to incur distinct sequential jitter. -/
  jitter : Time → ℕ → ℝ
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
the baseline and the `q`-th message's jitter after the link releases it, at
the time of release; `none` if the link drops it. -/
def deliver (d : Link) (s : Time) (q : ℕ) : Option Time := by
  classical
  exact match d.release s with
    | some u => if q ∈ d.lost ∨ d.Loses u then none else some (u + d.baseline u + d.jitter u q)
    | none => none

/-- The state of a link at true time `u` for message index `q`: its jitter,
whether a pause is under way, and whether an outage is under way. -/
def state (d : Link) (u : Time) (q : ℕ) : ℝ × Bool × Bool := by
  classical
  exact (d.jitter u q, decide (d.Holds u), decide (d.Loses u))

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
    (hj : ∀ u q, 0 ≤ d.jitter u q) (h : d.deliver s q = some a) : s < a := by
  unfold deliver at h
  split at h
  · rename_i u hu
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    linarith [d.le_release hu, hb u, hj u q]
  · simp at h

end Link

/-- The network of a world consists of the links `d`: messages from host `i`
to host `j` take the delays of `d i j`. -/
def World.HasDelays {H : Type} {R : ℕ} (w : World H R) (d : H → H → Link) : Prop :=
  ∀ i j s q, w.network.deliver i j s q = (d i j).deliver s q

/-- Per-directed-link parameters of the stationary network disturbances model
class for hosts `H`. Every parameter is indexed by the directed link `(i, j)`
so mixed topologies (for example, reliable wired links alongside lossy or
bursty wireless links) are directly representable. -/
structure StationaryNetworkDisturbances (H : Type) where
  /-- On link `(i, j)`, the baseline changes by at most `slope i j` seconds
  per second. -/
  slope : H → H → ℝ
  slope_nonneg : ∀ i j, 0 ≤ slope i j
  /-- On link `(i, j)`, jitter above `x` seconds has probability at most
  `tailFactor i j * exp (-x / tailScale i j)`. -/
  tailFactor : H → H → ℝ
  tailFactor_pos : ∀ i j, 0 < tailFactor i j
  tailScale : H → H → ℝ
  tailScale_pos : ∀ i j, 0 < tailScale i j
  /-- How many episodes start on link `(i, j)` per second, on average: pauses
  for `false`, outages for `true`. -/
  pauseRate : H → H → Bool → ℝ
  pauseRate_nonneg : ∀ i j kind, 0 ≤ pauseRate i j kind
  /-- The distribution of the length of an episode on link `(i, j)`, for each
  kind. Lengths are positive. -/
  pauseLength : H → H → Bool → Measure ℝ
  pauseLength_probability : ∀ i j kind, IsProbabilityMeasure (pauseLength i j kind)
  pauseLength_pos : ∀ i j kind, pauseLength i j kind (Set.Iic 0) = 0
  /-- Episodes on every link have a finite mean length. -/
  pauseLength_mean : ∀ i j kind, ∫⁻ x, ENNReal.ofReal x ∂(pauseLength i j kind) < ⊤
  /-- The probability that link `(i, j)` drops a message individually; less
  than one, since a link that drops every message carries nothing. -/
  lossProbability : H → H → ℝ
  lossProbability_nonneg : ∀ i j, 0 ≤ lossProbability i j
  lossProbability_lt_one : ∀ i j, lossProbability i j < 1

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

/-- The states of all the links of the network `d ω`, at all release times
and message indices. -/
def linkStates (d : Ω → H → H → Link) (ω : Ω) : H → H → Time → ℕ → ℝ × Bool × Bool :=
  fun i j u q => (d ω i j).state u q

/-- The individually dropped messages on all the links of the network
`d ω`, by their number on the link. -/
def droppedMessages (d : Ω → H → H → Link) (ω : Ω) : H → H → ℕ → Bool := by
  classical
  exact fun i j q => decide (q ∈ (d ω i j).lost)

/-- A function of time and message index on every link, shifted in time by
`τ` seconds: its value at `(u, q)` is the one at `(u + τ, q)`. -/
def shiftTime {α : Type} (τ : ℝ) (x : H → H → Time → ℕ → α) : H → H → Time → ℕ → α :=
  fun i j u q => x i j (u + τ) q

/-- A function of the message number on every link, shifted by `m`
messages. -/
def shiftCount {α : Type} (m : ℕ) (x : H → H → ℕ → α) : H → H → ℕ → α :=
  fun i j q => x i j (q + m)

/-- A random network, `d ω` for `ω` drawn from `P`, belongs to the
`StationaryNetworkDisturbances` model class `m`. -/
structure StationaryNetworkDisturbances.Holds (m : StationaryNetworkDisturbances H)
    (P : Measure Ω) (d : Ω → H → H → Link) : Prop where
  /-- The baseline is positive. -/
  baseline_pos : ∀ ω i j u, 0 < (d ω i j).baseline u
  /-- The baseline changes by at most `m.slope i j` seconds per second. -/
  baseline_slow : ∀ ω i j u u',
    |(d ω i j).baseline u - (d ω i j).baseline u'| ≤ m.slope i j * |u - u'|
  /-- The jitter is never negative. -/
  jitter_nonneg : ∀ ω i j u q, 0 ≤ (d ω i j).jitter u q
  /-- The jitter comes arbitrarily close to zero, so that the baseline is the
  least time a message takes. -/
  jitter_near_zero : ∀ i j u q δ, 0 < δ → 0 < P {ω | (d ω i j).jitter u q < δ}
  /-- Large jitter is rare: on link `(i, j)`, jitter above `x` seconds has
  probability at most `m.tailFactor i j * exp (-x / m.tailScale i j)`. -/
  jitter_tail : ∀ i j u q x, 0 ≤ x →
    P {ω | x < (d ω i j).jitter u q}
      ≤ ENNReal.ofReal (m.tailFactor i j * Real.exp (-x / m.tailScale i j))
  /-- Episodes have positive lengths. -/
  pause_length_pos : ∀ ω i j p, p ∈ (d ω i j).pauses → 0 < p.length
  /-- A pause is under way at a given time with probability less than one. -/
  paused_lt_one : ∀ i j u, P {ω | (d ω i j).Holds u} < 1
  /-- An outage is under way at a given time with probability less than
  one. -/
  outage_lt_one : ∀ i j u, P {ω | (d ω i j).Loses u} < 1
  /-- Episodes of each kind start on link `(i, j)` at the rate
  `m.pauseRate i j kind`, with lengths distributed as `m.pauseLength i j kind`:
  the mean number of episodes of a kind that start within any `t` seconds and
  whose length is in a set `A` is `m.pauseRate i j kind * t * m.pauseLength i j kind A`. -/
  pauses : ∀ i j kind (a t : ℝ) (A : Set ℝ), 0 ≤ t → MeasurableSet A →
    ∫⁻ ω, (((d ω i j).pauses ∩
        {p | p.loses = kind ∧ a ≤ p.start ∧ p.start < a + t ∧ p.length ∈ A}).encard : ℝ≥0∞) ∂P
      = ENNReal.ofReal (m.pauseRate i j kind * t) * m.pauseLength i j kind A
  /-- Each message on link `(i, j)` is dropped individually with probability
  `m.lossProbability i j`. -/
  lost : ∀ i j q, P {ω | q ∈ (d ω i j).lost} = ENNReal.ofReal (m.lossProbability i j)
  /-- The state of each link at each release time and message index is a
  random variable. -/
  state_measurable : ∀ i j u q, Measurable fun ω => (d ω i j).state u q
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

/-- A random world, `world ω` for `ω` drawn from `P`, follows the stationary
network disturbances model class `m`: `P` is a probability measure, and each
realization's network consists of links satisfying `m.Holds P d`. -/
def StationaryNetworkDisturbances.Random (m : StationaryNetworkDisturbances H) {R : ℕ}
    (P : Measure Ω) (world : Ω → World H R) : Prop :=
  IsProbabilityMeasure P ∧ ∃ d : Ω → H → H → Link, (∀ ω, (world ω).HasDelays (d ω)) ∧ m.Holds P d

end Unisono.Spec
