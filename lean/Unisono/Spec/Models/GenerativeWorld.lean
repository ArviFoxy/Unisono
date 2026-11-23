/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Optimality
public import Mathlib.Data.Sym.Sym2
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Moments.Covariance

/-!
# A generative model of the world

A model that gives a probability law to the world, so that the expected cost
of a solution is a number and solutions can be compared by it
(`Unisono.Spec.Optimality`). The model is a family of laws. A solution is
told a few things, the same for every member of the family; everything else
it has to estimate from what it observes.

## What a solution is told (`GenerativeWorld`)

The hosts, which one is the sender, which host drives each speaker, and the
settings of the devices and of the application: the nominal rate, the number
of frames in a block, the request lead (how long before a block starts to
play its device asks for it) and the target latency. A solution is also told
one number of the prior: the shape `k > 0` of the law of the split of a pair
of hosts (below). The weights of the objectives are known to a solution as
well, because optimality is stated for given weights
(`Unisono.Spec.Optimality`).

## What a solution has to estimate (`GenerativeWorld.Member`)

Each choice of these numbers is one member of the family. A solution is not
told them.

* `roundTrip i j`: the least round-trip time between hosts `i` and `j`.
* `trafficRate i j` and `trafficWork i j`: on the link from `i` to `j`, how
  many packets of other traffic arrive per second, and how long the link
  needs on average to carry one of them. Their product is less than one.
* `rateSpread`: the standard deviation of the logarithm of a clock's mean
  rate.
* `wanderSize h` and `wanderTime h`: the standard deviation of the changes of
  the rate of host `h`'s clock, and the time over which those changes lose
  their correlation.
* `offsetRange`: clock offsets lie within this distance of zero.

A member also fixes the readings of their hosts' clocks at which the devices
start (`captureStart`, `speakerStart`). They are not known before the devices
start, and nothing about them has to be estimated: each host reads the start
of its own device from the first timestamp that the device reports.

## What is drawn at random (`GenerativeWorld.Draw`, `GenerativeWorld.Prior`)

All of the following are independent of one another.

* The **split** of each pair of distinct hosts `i` and `j`: the share of
  their least round-trip time that the direction from `i` to `j` takes. It
  has the Beta law with both parameters equal to `k`, on the interval from
  zero to one. The direction from `j` to `i` takes the rest. The split
  measures the asymmetry of the pair; one half is a symmetric pair, and no
  pair is assumed symmetric.
* The **offset** of each clock, uniform between `-offsetRange` and
  `offsetRange`.
* The logarithm of the **mean rate** of each clock, Gaussian with mean zero
  and standard deviation `rateSpread`.
* The **wander** of each clock: a stationary Gaussian process with mean zero
  whose covariance between true times `s` and `t` is
  `wanderSize ^ 2 * exp (-|s - t| / wanderTime)`, with continuous paths.
* The **other traffic** of each directed link: packets arrive at the instants
  of a Poisson process of rate `trafficRate`, and each brings an
  exponentially distributed amount of work with mean `trafficWork`. The draw
  records the work that has arrived since true time zero (`trafficLaw`).

## The world built from a draw (`GenerativeWorld.Builds`)

* The clock of host `h` reads, at true time `t`, its offset plus the
  integral from `0` to `t` of `exp (logRate h + wander h x)`
  (`Draw.reading`). Its rate is positive for every draw.
* A message sent at true time `s` from `i` to `j` arrives after the least
  delay of that direction, `split i j * roundTrip i j`, plus the backlog of
  the link at `s`: the work of other traffic that the link has not yet
  carried, which falls by one second per second while it is positive
  (`Draw.IsBacklog`). Delays are positive for every draw. No message is lost.
* Every audio device runs on the clock of its host, in blocks of a fixed
  size, and reports exact timestamps. The target latency is constant.

## A random world of the model (`GenerativeWorld.Holds`, `GenerativeWorld.laws`)

A random world belongs to a member when it is built, for every outcome, from
a draw that has the law above.

## The solutions that are compared (`GenerativeWorld.measurableCost`)

Optimality under this model compares the solutions whose cost is, in almost
every outcome, a measurable function of what is drawn. A solution outside
this class has a cost that is not a random variable, and its expected cost,
a lower integral, can lie below its cost in almost every outcome.

## What the model leaves out

Loss, pauses and outages of links; jitter and asymmetry that several links
share because they share a host, a switch or a radio channel; least delays
and traffic that change over time; audio devices with their own oscillators
and inexact timestamps; clocks whose rate has more than one time scale. The
specification document lists these limitations and what each one distorts.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- What a solution is told about a generative world, for hosts `H` and `R`
speakers. -/
structure GenerativeWorld (H : Type) (R : ℕ) where
  /-- The nominal rate of every device, in frames per second. -/
  rate : ℝ
  rate_pos : 0 < rate
  /-- The sender's host. -/
  sender : H
  /-- The host of each speaker. -/
  host : Fin R → H
  /-- The shape `k` of the law of every split: the split has the Beta law
  with both parameters equal to `shape`. A large shape means nearly symmetric
  pairs; shape one means that a direction's share of the round trip is
  uniform between zero and one. -/
  shape : ℝ
  shape_pos : 0 < shape
  /-- Frames per capture block and output samples per playback block. -/
  blockSize : ℕ
  blockSize_pos : 0 < blockSize
  /-- The request lead: how long before a block's first output sample leaves,
  measured on the clock of the speaker's host, the playback device asks its
  host for the block. -/
  lead : ℝ
  lead_pos : 0 < lead
  /-- The target latency of every frame, in seconds. -/
  targetLatency : ℝ
  targetLatency_nonneg : 0 ≤ targetLatency

namespace GenerativeWorld

variable {H : Type} {R : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- One member of the family: the numbers that a solution is not told and
that are not drawn at random. A solution has to estimate them, except the
readings at which the devices start, which each host reads from its own
device. -/
structure Member (H : Type) (R : ℕ) where
  /-- The least round-trip time between two hosts, in seconds: the sum of the
  least delays of the two directions. -/
  roundTrip : H → H → ℝ
  roundTrip_pos : ∀ i j, 0 < roundTrip i j
  roundTrip_symm : ∀ i j, roundTrip i j = roundTrip j i
  /-- How many packets of other traffic arrive on the link from `i` to `j`
  per second, on average. Zero means that the link carries no other
  traffic. -/
  trafficRate : H → H → ℝ
  trafficRate_nonneg : ∀ i j, 0 ≤ trafficRate i j
  /-- How long the link from `i` to `j` needs to carry one packet of other
  traffic, on average, in seconds. -/
  trafficWork : H → H → ℝ
  trafficWork_pos : ∀ i j, 0 < trafficWork i j
  /-- Other traffic keeps a link busy less than all of the time. -/
  load_lt_one : ∀ i j, trafficRate i j * trafficWork i j < 1
  /-- The standard deviation of the logarithm of a clock's mean rate. -/
  rateSpread : ℝ
  rateSpread_nonneg : 0 ≤ rateSpread
  /-- The standard deviation of the wander of each clock: of the changes of
  the logarithm of its rate around its mean. Zero means a constant rate. -/
  wanderSize : H → ℝ
  wanderSize_nonneg : ∀ h, 0 ≤ wanderSize h
  /-- The time, in seconds, over which the wander of each clock loses its
  correlation: the correlation between the wander at two true times this far
  apart is `exp (-1)`. -/
  wanderTime : H → ℝ
  wanderTime_pos : ∀ h, 0 < wanderTime h
  /-- Clock offsets are uniform between `-offsetRange` and `offsetRange`, in
  seconds. -/
  offsetRange : ℝ
  offsetRange_pos : 0 < offsetRange
  /-- The reading of the sender's clock at which frame zero is captured. It
  is not known before the device starts; the sender's host reads it from the
  first timestamp that the capture device reports. -/
  captureStart : ℝ
  /-- The reading of its host's clock at which output sample zero of each
  speaker leaves. It is not known before the device starts; the speaker's
  host reads it from the first timestamp that the playback device reports. -/
  speakerStart : Fin R → ℝ

/-- What is drawn at random: one outcome. -/
structure Draw (H : Type) where
  /-- The share of the least round-trip time of hosts `i` and `j` that the
  direction from `i` to `j` takes. -/
  split : H → H → ℝ
  /-- The offset of each host's clock, in seconds. -/
  offset : H → ℝ
  /-- The logarithm of the mean rate of each host's clock. -/
  logRate : H → ℝ
  /-- The wander of each host's clock at each true time: the logarithm of its
  rate minus `logRate`. -/
  wander : H → Time → ℝ
  /-- The work that other traffic has brought to the link from `i` to `j`
  between true time zero and each true time, in seconds; the work that
  arrives between true times `s` and `t` is the difference of the values at
  `t` and at `s`. -/
  traffic : H → H → Time → ℝ

/-- What the clock of host `h` reads at true time `t`: its offset plus the
integral of its rate, which is the exponential of `logRate h + wander h`. -/
def Draw.reading (d : Draw H) (h : H) (t : Time) : ℝ :=
  d.offset h + ∫ x in (0 : ℝ)..t, Real.exp (d.logRate h + d.wander h x)

/-- `v` is the backlog of the link from `i` to `j` at true time `t`: the work
of other traffic that the link has not yet carried. The link carries one
second of work per second while any is left, so the backlog is the largest,
over the earlier true times `s`, of the work that arrived between `s` and `t`
minus the time between them. -/
def Draw.IsBacklog (d : Draw H) (i j : H) (t : Time) (v : ℝ) : Prop :=
  IsLUB {x | ∃ s ≤ t, x = d.traffic i j t - d.traffic i j s - (t - s)} v

/-- The law of the work that other traffic brings to a link over a period in
which `count` packets arrive on average, each needing `work` seconds on
average. The number of packets has the Poisson law with mean `count`. Each
packet brings an independent, exponentially distributed amount of work; the
total work of `n ≥ 1` packets therefore has the gamma law with shape `n` and
rate `1 / work`, and no packets bring no work. -/
def trafficLaw (count : ℝ≥0) (work : ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    poissonMeasure count {n} •
      (if n = 0 then Measure.dirac 0 else gammaMeasure (n : ℝ) (1 / work))

/-- The measurable sets of draws: those that the values of the splits, the
offsets, the mean rates, the wander and the traffic determine. A function of
a draw is measurable when it is a measurable function of these values. -/
instance : MeasurableSpace (Draw H) :=
  MeasurableSpace.comap
    (fun d : Draw H => (d.split, d.offset, d.logRate, d.wander, d.traffic)) inferInstance

/-- The components of a draw: the parts that are drawn independently of one another: the
split of each pair of distinct hosts, the offset and the mean rate of each
clock, the wander of each clock, and the other traffic of each directed
link. -/
inductive Component (H : Type) where
  | split (z : {z : Sym2 H // ¬ z.IsDiag})
  | offset (h : H)
  | logRate (h : H)
  | wander (h : H)
  | traffic (i j : H)

/-- What kind of value each component is: a number, or a function of true
time. -/
def Component.Val : Component H → Type
  | .split _ => ℝ
  | .offset _ => ℝ
  | .logRate _ => ℝ
  | .wander _ => Time → ℝ
  | .traffic _ _ => Time → ℝ

instance (p : Component H) : MeasurableSpace p.Val := by
  cases p
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))

/-- A choice of one of the two orders of every pair of distinct hosts. The
split of a pair in one order determines its split in the other, so the
independence of the splits is stated for one order of each pair. -/
abbrev Orientation (H : Type) : Type :=
  (z : {z : Sym2 H // ¬ z.IsDiag}) → {p : H × H // s(p.1, p.2) = z.1}

/-- The value of each component of a draw, with each pair of hosts taken in
the order that `o` chooses. -/
def Draw.component (d : Draw H) (o : Orientation H) : (p : Component H) → p.Val
  | .split z => d.split (o z).1.1 (o z).1.2
  | .offset h => d.offset h
  | .logRate h => d.logRate h
  | .wander h => d.wander h
  | .traffic i j => d.traffic i j

/-- **The prior.** The random draw `D ω`, for `ω` drawn from `P`, has the law
of the member `f` of the model `m`. -/
structure Prior (m : GenerativeWorld H R) (f : Member H R) (P : Measure Ω)
    (D : Ω → Draw H) : Prop where
  prob : IsProbabilityMeasure P
  /-- The two directions of a pair share its least round-trip time. -/
  split_swap : ∀ ω i j, (D ω).split i j + (D ω).split j i = 1
  /-- Every split lies strictly between zero and one, so that both least
  delays of a pair are positive in every outcome. -/
  split_mem : ∀ ω i j, (D ω).split i j ∈ Set.Ioo (0 : ℝ) 1
  /-- The split of two distinct hosts has the Beta law with both parameters
  equal to the shape. -/
  split_law : ∀ i j, i ≠ j →
    HasLaw (fun ω => (D ω).split i j) (betaMeasure m.shape m.shape) P
  /-- Each clock's offset is uniform between `-f.offsetRange` and
  `f.offsetRange`. -/
  offset_law : ∀ h, MeasureTheory.pdf.IsUniform (fun ω => (D ω).offset h)
    (Set.Icc (-f.offsetRange) f.offsetRange) P
  /-- The logarithm of each clock's mean rate is Gaussian with mean zero and
  standard deviation `f.rateSpread`. -/
  logRate_law : ∀ h,
    HasLaw (fun ω => (D ω).logRate h) (gaussianReal 0 (Real.toNNReal (f.rateSpread ^ 2))) P
  /-- The wander of each clock is a Gaussian process. -/
  wander_gaussian : ∀ h, IsGaussianProcess (fun t ω => (D ω).wander h t) P
  /-- The wander has mean zero. -/
  wander_mean : ∀ h t, ∫ ω, (D ω).wander h t ∂P = 0
  /-- The covariance of the wander at two true times falls exponentially with
  the time between them. -/
  wander_covariance : ∀ h s t,
    cov[fun ω => (D ω).wander h s, fun ω => (D ω).wander h t; P]
      = f.wanderSize h ^ 2 * Real.exp (-|s - t| / f.wanderTime h)
  /-- The wander is continuous in time, in every outcome. -/
  wander_continuous : ∀ ω h, Continuous ((D ω).wander h)
  /-- The work that has arrived never decreases. -/
  traffic_monotone : ∀ ω i j, Monotone ((D ω).traffic i j)
  /-- The work is counted from true time zero. -/
  traffic_zero : ∀ ω i j, (D ω).traffic i j 0 = 0
  /-- Work that arrives at an instant counts from that instant on. -/
  traffic_rightContinuous : ∀ ω i j t,
    ContinuousWithinAt ((D ω).traffic i j) (Set.Ici t) t
  /-- The work that arrives in periods that do not overlap is independent. -/
  traffic_increments : ∀ i j, HasIndepIncrements (fun t ω => (D ω).traffic i j t) P
  /-- The work that arrives between true times `s` and `t` has the law
  `trafficLaw`, for the number of packets that arrive in that time on
  average. -/
  traffic_law : ∀ i j s t, s ≤ t →
    HasLaw (fun ω => (D ω).traffic i j t - (D ω).traffic i j s)
      (trafficLaw (Real.toNNReal (f.trafficRate i j * (t - s))) (f.trafficWork i j)) P
  /-- The components of the draw are independent, whichever order each pair of
  hosts is taken in. -/
  independent : ∀ o : Orientation H, iIndepFun (fun p ω => (D ω).component o p) P

/-- The world `w` is the one built from the draw `d`, in the member `f` of
the model `m`. -/
structure Builds (m : GenerativeWorld H R) (f : Member H R) (d : Draw H)
    (w : World H R) : Prop where
  rate_eq : w.rate = m.rate
  sender_eq : w.sender = m.sender
  host_eq : w.host = m.host
  /-- Each host's clock reads what the draw says. -/
  clock : ∀ h t, (w.clock h).read t = d.reading h t
  /-- A message arrives after the least delay of its direction plus the
  backlog of the link when it is sent. No message is lost. -/
  network : ∀ i j s q, ∃ v, d.IsBacklog i j s v ∧
    w.network.deliver i j s q = some (s + d.split i j * f.roundTrip i j + v)
  /-- The capture device runs on the sender's clock: frame `n` is captured
  when that clock reads `f.captureStart + n / m.rate`. -/
  capture : ∀ n : ℕ,
    (w.clock w.sender).read (w.source.capture n) = f.captureStart + (n : ℝ) / m.rate
  /-- Capture blocks hold `m.blockSize` frames. -/
  capture_first : ∀ b : ℕ, w.source.first b = b * m.blockSize
  /-- A capture block is handed over when its last frame is captured. -/
  capture_handed : ∀ b : ℕ,
    w.source.handed b = w.source.capture (w.source.first (b + 1) - 1)
  /-- Capture timestamps are exact. -/
  capture_reported : ∀ b : ℕ,
    w.source.reported b = (w.clock w.sender).read (w.source.capture (w.source.first b))
  /-- Each playback device runs on the clock of its host: output sample `k`
  of speaker `r` leaves when that clock reads `f.speakerStart r + k / m.rate`. -/
  speaker_out : ∀ (r : Fin R) (k : ℕ),
    (w.clock (w.host r)).read ((w.speaker r).out k) = f.speakerStart r + (k : ℝ) / m.rate
  /-- Playback blocks hold `m.blockSize` output samples. -/
  speaker_first : ∀ (r : Fin R) (b : ℕ), (w.speaker r).first b = b * m.blockSize
  /-- A playback device requests each block `m.lead` seconds, measured on the
  clock of its host, before the block's first output sample leaves. -/
  speaker_asked : ∀ (r : Fin R) (b : ℕ),
    (w.clock (w.host r)).read ((w.speaker r).out ((w.speaker r).first b))
      - (w.clock (w.host r)).read ((w.speaker r).asked b) = m.lead
  /-- Playback timestamps are exact. -/
  speaker_reported : ∀ (r : Fin R) (b : ℕ),
    (w.speaker r).reported b
      = (w.clock (w.host r)).read ((w.speaker r).out ((w.speaker r).first b))
  /-- The target latency is constant. -/
  target_eq : ∀ n : ℕ, w.target n = m.targetLatency

/-- A random world, `world ω` for `ω` drawn from `P`, belongs to the member
`f` of the model `m`: in every outcome it is the world built from a draw, and
the draw has the law of the member. -/
def Holds (m : GenerativeWorld H R) (f : Member H R) (P : Measure Ω)
    (world : Ω → World H R) : Prop :=
  ∃ D : Ω → Draw H, m.Prior f P D ∧ ∀ ω, m.Builds f (D ω) (world ω)

/-- The family of laws of the model: the random worlds of each member. -/
def laws (m : GenerativeWorld H R) : Member H R → RandomWorlds H R :=
  fun f _ _ P world => m.Holds f P world

/-- **The solutions that are compared.** The solutions whose cost is a
measurable function of what is drawn: for each member there is a measurable
function `F` of the draw such that, in every random world of the member, the
cost of the solution is `F` of the draw in almost every outcome. The weights
`c` and the lookahead are those for which the cost is taken. -/
def measurableCost [DecidableEq H] (m : GenerativeWorld H R) (lookahead : ℕ+) (c : Weights) :
    SolutionClass H R :=
  fun _ τ => ∀ f : Member H R, ∃ F : Draw H → ℝ≥0∞, Measurable F ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') (D : Ω' → Draw H)
      (world : Ω' → World H R),
      m.Prior f P D → (∀ ω, m.Builds f (D ω) (world ω)) →
        ∀ᵐ ω ∂P, τ.cost (world ω) lookahead c = F (D ω)

/-! ## Checks of the definitions -/

/-- **Both least delays of a pair are positive**, in every outcome. -/
theorem Prior.leastDelay_pos {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω}
    {D : Ω → Draw H} (h : m.Prior f P D) (ω : Ω) (i j : H) :
    0 < (D ω).split i j * f.roundTrip i j :=
  mul_pos (h.split_mem ω i j).1 (f.roundTrip_pos i j)

/-- **The two directions of a pair share its least round-trip time**, in
every outcome. -/
theorem Prior.leastDelay_add {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω}
    {D : Ω → Draw H} (h : m.Prior f P D) (ω : Ω) (i j : H) :
    (D ω).split i j * f.roundTrip i j + (D ω).split j i * f.roundTrip j i
      = f.roundTrip i j := by
  rw [f.roundTrip_symm j i, ← add_mul, h.split_swap, one_mul]

/-- **The law of the work that arrives is a probability law**: its total mass
is one. -/
theorem trafficLaw_univ (count : ℝ≥0) {work : ℝ} (hwork : 0 < work) :
    trafficLaw count work Set.univ = 1 := by
  have hterm : ∀ n : ℕ,
      (if n = 0 then Measure.dirac (0 : ℝ) else gammaMeasure (n : ℝ) (1 / work)) Set.univ
        = 1 := by
    intro n
    split_ifs with h
    · simp
    · have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
      have := isProbabilityMeasure_gammaMeasure hn (one_div_pos.mpr hwork)
      exact measure_univ
  have hsum : poissonMeasure count Set.univ = ∑' n : ℕ, poissonMeasure count {n} := by
    simp only [poissonMeasure_singleton]
    rw [poissonMeasure, Measure.sum_apply _ MeasurableSet.univ]
    simp
  rw [trafficLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [smul_apply, smul_eq_mul, hterm, mul_one]
  rw [← hsum, measure_univ]

/-! ## Facts about the laws of the model -/

/-- The density of the Beta law with equal parameters is the same at `x` and
at `1 - x`. -/
theorem betaPDF_one_sub (k x : ℝ) : betaPDF k k (1 - x) = betaPDF k k x := by
  simp only [betaPDF_eq]
  congr 1
  split_ifs with h1 h2 h2
  · rw [sub_sub_cancel]; ring
  · exact absurd ⟨by linarith [h1.2], by linarith [h1.1]⟩ h2
  · exact absurd ⟨by linarith [h2.2], by linarith [h2.1]⟩ h1
  · rfl

/-- **The law of a split does not prefer a direction.** If a split has the
Beta law with equal parameters, the split of the other direction, one minus
it, has the same law. -/
theorem betaMeasure_map_one_sub (k : ℝ) :
    (betaMeasure k k).map (fun x : ℝ => 1 - x) = betaMeasure k k := by
  have hmp : MeasurePreserving (fun x : ℝ => 1 - x) volume volume :=
    volume.measurePreserving_sub_left 1
  have hpdf : Measurable (betaPDF k k) := (measurable_betaPDFReal k k).ennreal_ofReal
  ext s hs
  rw [Measure.map_apply hmp.measurable hs, betaMeasure,
    withDensity_apply _ (hmp.measurable hs), withDensity_apply _ hs,
    ← hmp.setLIntegral_comp_preimage hs hpdf]
  exact setLIntegral_congr_fun (hmp.measurable hs) (fun x _ => (betaPDF_one_sub k x).symm)

/-- A Beta law gives no mass to the numbers outside the interval from zero
to one. -/
theorem betaMeasure_compl_Ioo (a b : ℝ) : betaMeasure a b (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
  rw [betaMeasure, withDensity_apply _ measurableSet_Ioo.compl]
  refine setLIntegral_eq_zero measurableSet_Ioo.compl (fun x hx => ?_)
  simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hx
  by_cases h0 : 0 < x
  · exact betaPDF_eq_zero_of_one_le (hx h0)
  · exact betaPDF_eq_zero_of_nonpos (not_lt.mp h0)

/-- **No traffic brings no work.** When no packets arrive on average, the
work that arrives is zero. -/
theorem trafficLaw_zero (work : ℝ) : trafficLaw 0 work = Measure.dirac 0 := by
  ext s hs
  rw [trafficLaw, Measure.sum_apply _ hs, tsum_eq_single 0]
  · simp [poissonMeasure_singleton]
  · intro n hn
    simp [poissonMeasure_singleton, hn]

end GenerativeWorld

end Unisono.Spec
