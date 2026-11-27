/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Optimality
public import Mathlib.Data.Sym.Sym2
public import Mathlib.MeasureTheory.Group.Convolution
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

The hosts, which one is the sender, which host drives each speaker, which
speakers are outputs of one audio device, and the settings of the devices and
of the application: the nominal rate, the number of frames in a block, the
request lead (how long before a block starts to play its device asks for it)
and the target latency. A solution is also told
one number of the prior: the shape `k > 0` of the law of the split of a pair
of hosts (below). The weights of the objectives are known to a solution as
well, because optimality is stated for given weights
(`Unisono.Spec.Optimality`).

## What a solution has to estimate (`GenerativeWorld.Member`)

Each choice of these numbers is one member of the family. A solution is not
told them.

* `roundTrip i j`: the least round-trip time between hosts `i` and `j`.
* `linkPauseRate i j` and `linkPauseLength i j`: how many pauses of the link
  from `i` to `j` begin per second, and the law of the length of a pause. A
  pause is a stretch of time in which the link passes nothing: it carries a
  packet of other traffic, repeats a transmission, or is out. The law may be
  any law of positive lengths that has a mean, so one member can have pauses
  of a fraction of a millisecond and pauses of a second. The rate times the
  mean length is less than one.
* `hostPauseRate h` and `hostPauseLength h`: the same for the pauses of host
  `h`, during which the host sends nothing and handles nothing that arrives.
* `rateSpread`: the standard deviation of the logarithm of a clock's mean
  rate.
* `wanderSize h` and `wanderTime h`: the standard deviation of the changes of
  the rate of host `h`'s clock, and the time over which those changes lose
  their correlation.
* `deviceWanderSize x` and `deviceWanderTime x`: the same for the clock of the
  audio device `x`. The audio devices are the capture device and the
  playback devices.
* `reportSize x` and `reportTime x`: the standard deviation of the error of
  the timestamps that the audio device `x` reports, and the time over which
  that error loses its correlation.
* `offsetRange`: clock offsets lie within this distance of zero.

A member also fixes the readings of their hosts' clocks at which the devices
start (`captureStart`, `speakerStart`). They are not known before the devices
start; each host learns the start of its own device from the timestamps that
the device reports.

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
* The logarithm of the **mean rate** of the clock of each audio device, with
  the same law as that of a host's clock, and the **wander** of that clock:
  a stationary Gaussian process of the same kind, with the size and the time
  of the device.
* The **error of the reports** of each audio device: a stationary Gaussian
  process with mean zero whose covariance between true times `s` and `t` is
  `reportSize ^ 2 * exp (-|s - t| / reportTime)`, with continuous paths.
* The **pauses** of each directed link and of each host: pauses begin at the
  instants of a Poisson process of the member's rate, and their lengths are
  independent of one another and have the member's law. The draw records the
  paused time that has begun since true time zero (`pauseLaw`).

## The world built from a draw (`GenerativeWorld.Builds`)

* The clock of host `h` reads, at true time `t`, its offset plus the
  integral from `0` to `t` of `exp (logRate h + wander h x)`
  (`Draw.reading`). Its rate is positive for every draw.
* The backlog of a link or of a host is its paused time that has begun and
  is not yet over. It rises by the length of a pause when the pause begins
  and falls by one second per second while it is positive (`IsBacklog`).
* A message that host `i` sends to host `j` at true time `s` leaves `i`
  after the backlog of host `i` at `s`. It reaches `j` after the least delay
  of that direction, `split i j * roundTrip i j`, plus the backlog of the
  link when it leaves. Host `j` observes it after the backlog of host `j`
  when it reaches it. So a pause of length `x` delays what is sent at its
  start by `x` and what is sent later by less, and everything that it
  withheld arrives together when it ends. A pause of the sender's host
  delays every receiver at once: links and hosts are drawn independently,
  and the delays of two receivers are not independent. Delays are positive
  for every draw. No message is lost.
* Every audio device has a clock of its own, which advances by the integral
  of `exp (deviceLogRate x + deviceWander x)` (`Draw.deviceReading`). A
  device starts when the clock of its host reads the member's start, and its
  frame or output sample `n` occurs when its own clock has advanced by `n`
  divided by the nominal rate since then. Speakers that are outputs of one
  device share its clock. Blocks have a fixed size.
* A host handles the events of its audio devices after its backlog, like
  the messages that reach it. The capture device hands a block over when
  the block's last frame is captured, and the sender's host handles the
  handover after its backlog at that time. A playback device asks for a
  block the request lead before the block's first output sample leaves,
  measured on the device's clock, and its host handles the request after
  its backlog at that time. Events of a device that occur while its host is
  paused are handled together when the pause ends. When the backlog is
  longer than the request lead, output samples of the block leave before
  the host handles the request; they play nothing of the source
  (`State.handle`).
* The timestamp that a device reports for a block is the reading of its
  host's clock at the true time of the block's first frame or output sample,
  plus the error of the device's reports at that time. A constant part of
  such an error is not modelled: no host can tell it from a delay inside the
  device.
* The target latency is constant.

## A random world of the model (`GenerativeWorld.Holds`, `GenerativeWorld.laws`)

A random world belongs to a member when it is built, for every outcome, from
a draw that has the law above.

## The solutions that are compared (`GenerativeWorld.measurableCost`)

Optimality under this model compares, at each member, the solutions whose
cost in that member is, in almost every outcome, a measurable function of
what is drawn. A solution outside this class has a cost that is not a random
variable, and its expected cost, a lower integral, can lie below its cost in
almost every outcome. Optimality under the model is always stated for every
member (`GenerativeWorld.OptimalWithin`).

A second class holds the solutions whose playback in a member is a
measurable function of what is drawn (`GenerativeWorld.measurablePlays`):
at every output sample of every speaker, whether the speaker plays the
source, and at which position. A bound that reasons about what a solution
has played before a pause begins needs what was played to be a random
variable, and is stated for the solutions in both classes.

## What the model leaves out

Loss; pauses that cluster in time; pauses and asymmetry that some links
share because they share a switch or a radio channel; least delays and rates
of pauses that change over time; time stamps that a kernel takes for
messages while the program is paused; timestamps of an audio device that are
grossly wrong for a while; clocks whose rate has more than one time scale.
The specification document lists these limitations and what each one
distorts.
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
  /-- The speaker that stands for the audio device of speaker `r`. Speakers
  that are outputs of one device have the same one, and a speaker with a
  device of its own stands for itself. -/
  device : Fin R → Fin R
  device_idem : ∀ r, device (device r) = device r
  /-- The outputs of one device are driven by one host. -/
  device_host : ∀ r, host (device r) = host r
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
  /-- How many pauses of the link from `i` to `j` begin per second, on
  average. Zero means that the link never pauses. -/
  linkPauseRate : H → H → ℝ
  linkPauseRate_nonneg : ∀ i j, 0 ≤ linkPauseRate i j
  /-- The law of the length of a pause of the link from `i` to `j`, in
  seconds. It may be any law of positive lengths that has a mean. -/
  linkPauseLength : H → H → Measure ℝ
  linkPauseLength_prob : ∀ i j, IsProbabilityMeasure (linkPauseLength i j)
  linkPauseLength_pos : ∀ i j, linkPauseLength i j (Set.Iic 0) = 0
  linkPauseLength_mean : ∀ i j, Integrable (fun x : ℝ => x) (linkPauseLength i j)
  /-- A link is paused less than all of the time. -/
  linkLoad_lt_one : ∀ i j, linkPauseRate i j * ∫ x, x ∂(linkPauseLength i j) < 1
  /-- How many pauses of host `h` begin per second, on average. Zero means
  that the host never pauses. -/
  hostPauseRate : H → ℝ
  hostPauseRate_nonneg : ∀ h, 0 ≤ hostPauseRate h
  /-- The law of the length of a pause of host `h`, in seconds. It may be
  any law of positive lengths that has a mean. -/
  hostPauseLength : H → Measure ℝ
  hostPauseLength_prob : ∀ h, IsProbabilityMeasure (hostPauseLength h)
  hostPauseLength_pos : ∀ h, hostPauseLength h (Set.Iic 0) = 0
  hostPauseLength_mean : ∀ h, Integrable (fun x : ℝ => x) (hostPauseLength h)
  /-- A host is paused less than all of the time. -/
  hostLoad_lt_one : ∀ h, hostPauseRate h * ∫ x, x ∂(hostPauseLength h) < 1
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
  /-- The standard deviation of the wander of the clock of each audio device.
  The device `none` is the capture device, and `some r` is the playback
  device that speaker `r` stands for. -/
  deviceWanderSize : Option (Fin R) → ℝ
  deviceWanderSize_nonneg : ∀ x, 0 ≤ deviceWanderSize x
  /-- The time, in seconds, over which the wander of the clock of each audio
  device loses its correlation. -/
  deviceWanderTime : Option (Fin R) → ℝ
  deviceWanderTime_pos : ∀ x, 0 < deviceWanderTime x
  /-- The standard deviation of the error of the timestamps that each audio
  device reports, in seconds. Zero means exact timestamps. -/
  reportSize : Option (Fin R) → ℝ
  reportSize_nonneg : ∀ x, 0 ≤ reportSize x
  /-- The time, in seconds, over which the error of the timestamps of each
  audio device loses its correlation. -/
  reportTime : Option (Fin R) → ℝ
  reportTime_pos : ∀ x, 0 < reportTime x
  /-- Clock offsets are uniform between `-offsetRange` and `offsetRange`, in
  seconds. -/
  offsetRange : ℝ
  offsetRange_pos : 0 < offsetRange
  /-- The reading of the sender's clock at which frame zero is captured. It
  is not known before the device starts; the sender's host learns it from
  the timestamps that the capture device reports. -/
  captureStart : ℝ
  /-- The reading of its host's clock at which output sample zero of each
  speaker leaves. The speakers of one device start together, at the start of
  the speaker that stands for the device. It is not known before the device
  starts; the speaker's host learns it from the timestamps that the playback
  device reports. -/
  speakerStart : Fin R → ℝ

/-- What is drawn at random: one outcome. -/
structure Draw (H : Type) (R : ℕ) where
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
  /-- The paused time of the link from `i` to `j` that has begun between
  true time zero and each true time, in seconds: the sum of the lengths of
  the pauses that began in between. The paused time that begins between
  true times `s` and `t` is the difference of the values at `t` and at `s`. -/
  linkPaused : H → H → Time → ℝ
  /-- The paused time of host `h` that has begun between true time zero and
  each true time, in seconds. -/
  hostPaused : H → Time → ℝ
  /-- The logarithm of the mean rate of the clock of each audio device. The
  device `none` is the capture device, and `some r` is the playback device
  that speaker `r` stands for. -/
  deviceLogRate : Option (Fin R) → ℝ
  /-- The wander of the clock of each audio device at each true time. -/
  deviceWander : Option (Fin R) → Time → ℝ
  /-- The error of the timestamps that each audio device reports, as a
  function of the true time of what is reported, in seconds. -/
  reportError : Option (Fin R) → Time → ℝ

/-- What the clock of host `h` reads at true time `t`: its offset plus the
integral of its rate, which is the exponential of `logRate h + wander h`. -/
def Draw.reading (d : Draw H R) (h : H) (t : Time) : ℝ :=
  d.offset h + ∫ x in (0 : ℝ)..t, Real.exp (d.logRate h + d.wander h x)

/-- By how much the clock of the audio device `x` advances between true time
zero and true time `t`: the integral of its rate, which is the exponential
of `deviceLogRate x + deviceWander x`. -/
def Draw.deviceReading (d : Draw H R) (x : Option (Fin R)) (t : Time) : ℝ :=
  ∫ y in (0 : ℝ)..t, Real.exp (d.deviceLogRate x + d.deviceWander x y)

/-- `v` is the backlog at true time `t` of a link or a host whose paused time
is recorded by `paused`: the paused time that has begun and is not yet over.
A link or a host works one second of it off per second while any is left,
so the backlog is the largest, over the earlier true times `s`, of the paused
time that began between `s` and `t` minus the time between them. -/
def IsBacklog (paused : Time → ℝ) (t : Time) (v : ℝ) : Prop :=
  IsLUB {x | ∃ s ≤ t, x = paused t - paused s - (t - s)} v

/-- The law of the sum of `n` independent lengths, each with the law `F`. -/
def sumLaw (F : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => sumLaw F n ∗ F

/-- The law of the paused time that begins in a period in which `count`
pauses begin on average, when the length of a pause has the law `F`. The
number of pauses has the Poisson law with mean `count`, and their lengths are
independent. -/
def pauseLaw (count : ℝ≥0) (F : Measure ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ => poissonMeasure count {n} • sumLaw F n

/-- The measurable sets of draws: those that the values of the splits, the
offsets, the mean rates, the wander, the paused times, the clocks of the
audio devices and the errors of their reports determine. A function of
a draw is measurable when it is a measurable function of these values. -/
instance : MeasurableSpace (Draw H R) :=
  MeasurableSpace.comap
    (fun d : Draw H R =>
      (d.split, d.offset, d.logRate, d.wander, d.linkPaused, d.hostPaused,
        d.deviceLogRate, d.deviceWander, d.reportError)) inferInstance

/-- The components of a draw: the parts that are drawn independently of one another: the
split of each pair of distinct hosts, the offset and the mean rate of each
clock, the wander of each clock, the paused time of each directed link and
of each host, and for each audio device the mean rate and the wander of its
clock and the error of its reports. -/
inductive Component (H : Type) (R : ℕ) where
  | split (z : {z : Sym2 H // ¬ z.IsDiag})
  | offset (h : H)
  | logRate (h : H)
  | wander (h : H)
  | linkPaused (i j : H)
  | hostPaused (h : H)
  | deviceLogRate (x : Option (Fin R))
  | deviceWander (x : Option (Fin R))
  | reportError (x : Option (Fin R))

/-- What kind of value each component is: a number, or a function of true
time. -/
def Component.Val : Component H R → Type
  | .split _ => ℝ
  | .offset _ => ℝ
  | .logRate _ => ℝ
  | .wander _ => Time → ℝ
  | .linkPaused _ _ => Time → ℝ
  | .hostPaused _ => Time → ℝ
  | .deviceLogRate _ => ℝ
  | .deviceWander _ => Time → ℝ
  | .reportError _ => Time → ℝ

instance (p : Component H R) : MeasurableSpace p.Val := by
  cases p
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
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
def Draw.component (d : Draw H R) (o : Orientation H) : (p : Component H R) → p.Val
  | .split z => d.split (o z).1.1 (o z).1.2
  | .offset h => d.offset h
  | .logRate h => d.logRate h
  | .wander h => d.wander h
  | .linkPaused i j => d.linkPaused i j
  | .hostPaused h => d.hostPaused h
  | .deviceLogRate x => d.deviceLogRate x
  | .deviceWander x => d.deviceWander x
  | .reportError x => d.reportError x

/-- **The prior.** The random draw `D ω`, for `ω` drawn from `P`, has the law
of the member `f` of the model `m`. -/
structure Prior (m : GenerativeWorld H R) (f : Member H R) (P : Measure Ω)
    (D : Ω → Draw H R) : Prop where
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
  /-- The logarithm of the mean rate of the clock of each audio device is
  Gaussian with mean zero and standard deviation `f.rateSpread`. -/
  deviceLogRate_law : ∀ x,
    HasLaw (fun ω => (D ω).deviceLogRate x)
      (gaussianReal 0 (Real.toNNReal (f.rateSpread ^ 2))) P
  /-- The wander of the clock of each audio device is a Gaussian process. -/
  deviceWander_gaussian : ∀ x, IsGaussianProcess (fun t ω => (D ω).deviceWander x t) P
  /-- The wander of a device's clock has mean zero. -/
  deviceWander_mean : ∀ x t, ∫ ω, (D ω).deviceWander x t ∂P = 0
  /-- The covariance of the wander of a device's clock at two true times
  falls exponentially with the time between them. -/
  deviceWander_covariance : ∀ x s t,
    cov[fun ω => (D ω).deviceWander x s, fun ω => (D ω).deviceWander x t; P]
      = f.deviceWanderSize x ^ 2 * Real.exp (-|s - t| / f.deviceWanderTime x)
  /-- The wander of a device's clock is continuous in time, in every
  outcome. -/
  deviceWander_continuous : ∀ ω x, Continuous ((D ω).deviceWander x)
  /-- The error of the reports of each audio device is a Gaussian process. -/
  reportError_gaussian : ∀ x, IsGaussianProcess (fun t ω => (D ω).reportError x t) P
  /-- The error of the reports has mean zero. -/
  reportError_mean : ∀ x t, ∫ ω, (D ω).reportError x t ∂P = 0
  /-- The covariance of the error of the reports at two true times falls
  exponentially with the time between them. -/
  reportError_covariance : ∀ x s t,
    cov[fun ω => (D ω).reportError x s, fun ω => (D ω).reportError x t; P]
      = f.reportSize x ^ 2 * Real.exp (-|s - t| / f.reportTime x)
  /-- The error of the reports is continuous in time, in every outcome. -/
  reportError_continuous : ∀ ω x, Continuous ((D ω).reportError x)
  /-- The paused time of a link that has begun never decreases. -/
  linkPaused_monotone : ∀ ω i j, Monotone ((D ω).linkPaused i j)
  /-- The paused time of a link is counted from true time zero. -/
  linkPaused_zero : ∀ ω i j, (D ω).linkPaused i j 0 = 0
  /-- A pause counts from the instant at which it begins. -/
  linkPaused_rightContinuous : ∀ ω i j t,
    ContinuousWithinAt ((D ω).linkPaused i j) (Set.Ici t) t
  /-- The paused time of a link that begins in periods that do not overlap
  is independent. -/
  linkPaused_increments : ∀ i j, HasIndepIncrements (fun t ω => (D ω).linkPaused i j t) P
  /-- The paused time of a link that begins between true times `s` and `t`
  has the law `pauseLaw`, for the number of pauses that begin in that time
  on average and the member's law of their lengths. -/
  linkPaused_law : ∀ i j s t, s ≤ t →
    HasLaw (fun ω => (D ω).linkPaused i j t - (D ω).linkPaused i j s)
      (pauseLaw (Real.toNNReal (f.linkPauseRate i j * (t - s))) (f.linkPauseLength i j)) P
  /-- The paused time of a host that has begun never decreases. -/
  hostPaused_monotone : ∀ ω h, Monotone ((D ω).hostPaused h)
  /-- The paused time of a host is counted from true time zero. -/
  hostPaused_zero : ∀ ω h, (D ω).hostPaused h 0 = 0
  /-- A pause counts from the instant at which it begins. -/
  hostPaused_rightContinuous : ∀ ω h t,
    ContinuousWithinAt ((D ω).hostPaused h) (Set.Ici t) t
  /-- The paused time of a host that begins in periods that do not overlap
  is independent. -/
  hostPaused_increments : ∀ h, HasIndepIncrements (fun t ω => (D ω).hostPaused h t) P
  /-- The paused time of a host that begins between true times `s` and `t`
  has the law `pauseLaw`, for the number of pauses that begin in that time
  on average and the member's law of their lengths. -/
  hostPaused_law : ∀ h s t, s ≤ t →
    HasLaw (fun ω => (D ω).hostPaused h t - (D ω).hostPaused h s)
      (pauseLaw (Real.toNNReal (f.hostPauseRate h * (t - s))) (f.hostPauseLength h)) P
  /-- The components of the draw are independent, whichever order each pair of
  hosts is taken in. -/
  independent : ∀ o : Orientation H, iIndepFun (fun p ω => (D ω).component o p) P

/-- The world `w` is the one built from the draw `d`, in the member `f` of
the model `m`. -/
structure Builds (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R)
    (w : World H R) : Prop where
  rate_eq : w.rate = m.rate
  sender_eq : w.sender = m.sender
  host_eq : w.host = m.host
  /-- Each host's clock reads what the draw says. -/
  clock : ∀ h t, (w.clock h).read t = d.reading h t
  /-- A message that host `i` sends to host `j` at true time `s` leaves `i`
  after the backlog `v₁` of host `i` at `s`, reaches `j` after the least
  delay of the direction plus the backlog `v₂` of the link when it leaves,
  and is handled by the program of `j` after the backlog `v₃` of host `j`
  when it reaches it. The kernel of `j` stamps the message when it reaches
  `j`, before the backlog of `j`. No message is lost. -/
  network : ∀ i j s q, ∃ v₁ v₂ v₃,
    IsBacklog (d.hostPaused i) s v₁ ∧
    IsBacklog (d.linkPaused i j) (s + v₁) v₂ ∧
    IsBacklog (d.hostPaused j) (s + v₁ + d.split i j * f.roundTrip i j + v₂) v₃ ∧
    w.network.deliver i j s q
      = some (s + v₁ + d.split i j * f.roundTrip i j + v₂ + v₃) ∧
    w.network.reach i j s q = s + v₁ + d.split i j * f.roundTrip i j + v₂
  /-- What the clock of each audio device advances by is a clock: it never
  stands still. -/
  deviceClock : ∀ x, ∃ c : Clock, ∀ t, c.read t = d.deviceReading x t
  /-- The capture device starts when the sender's clock reads
  `f.captureStart`. -/
  capture_start : (w.clock w.sender).read (w.source.capture 0) = f.captureStart
  /-- The capture device runs on its own clock: frame `n` is captured when
  that clock has advanced by `n / m.rate` since frame zero. -/
  capture : ∀ n : ℕ,
    d.deviceReading none (w.source.capture n) - d.deviceReading none (w.source.capture 0)
      = (n : ℝ) / m.rate
  /-- Capture blocks hold `m.blockSize` frames. -/
  capture_first : ∀ b : ℕ, w.source.first b = b * m.blockSize
  /-- The capture device hands a block over when the block's last frame is
  captured. The sender's host handles the handover after its backlog `v` at
  that time. -/
  capture_handed : ∀ b : ℕ, ∃ v,
    IsBacklog (d.hostPaused w.sender) (w.source.capture (w.source.first (b + 1) - 1)) v ∧
    w.source.handed b = w.source.capture (w.source.first (b + 1) - 1) + v
  /-- The timestamp of a capture block is the reading of the sender's clock
  when the block's first frame is captured, plus the error of the capture
  device's reports at that time. -/
  capture_reported : ∀ b : ℕ,
    w.source.reported b
      = (w.clock w.sender).read (w.source.capture (w.source.first b))
        + d.reportError none (w.source.capture (w.source.first b))
  /-- The playback device of speaker `r` starts when the clock of its host
  reads the start of the speaker that stands for the device. -/
  speaker_start : ∀ r : Fin R,
    (w.clock (w.host r)).read ((w.speaker r).out 0) = f.speakerStart (m.device r)
  /-- Each playback device runs on its own clock: output sample `k` of
  speaker `r` leaves when the clock of its device has advanced by
  `k / m.rate` since output sample zero. -/
  speaker_out : ∀ (r : Fin R) (k : ℕ),
    d.deviceReading (some (m.device r)) ((w.speaker r).out k)
        - d.deviceReading (some (m.device r)) ((w.speaker r).out 0)
      = (k : ℝ) / m.rate
  /-- Playback blocks hold `m.blockSize` output samples. -/
  speaker_first : ∀ (r : Fin R) (b : ℕ), (w.speaker r).first b = b * m.blockSize
  /-- A playback device requests each block at the true time `ρ` that is
  `m.lead` seconds, measured on its own clock, before the block's first
  output sample leaves. The speaker's host handles the request after its
  backlog `v` at that time. -/
  speaker_asked : ∀ (r : Fin R) (b : ℕ), ∃ ρ v,
    d.deviceReading (some (m.device r)) ((w.speaker r).out ((w.speaker r).first b))
      - d.deviceReading (some (m.device r)) ρ = m.lead ∧
    IsBacklog (d.hostPaused (w.host r)) ρ v ∧
    (w.speaker r).asked b = ρ + v
  /-- The timestamp of a playback block is the reading of the host's clock
  when the block's first output sample leaves, plus the error of the
  device's reports at that time. -/
  speaker_reported : ∀ (r : Fin R) (b : ℕ),
    (w.speaker r).reported b
      = (w.clock (w.host r)).read ((w.speaker r).out ((w.speaker r).first b))
        + d.reportError (some (m.device r)) ((w.speaker r).out ((w.speaker r).first b))
  /-- The target latency is constant. -/
  target_eq : ∀ n : ℕ, w.target n = m.targetLatency

/-- A random world, `world ω` for `ω` drawn from `P`, belongs to the member
`f` of the model `m`: in every outcome it is the world built from a draw, and
the draw has the law of the member. -/
def Holds (m : GenerativeWorld H R) (f : Member H R) (P : Measure Ω)
    (world : Ω → World H R) : Prop :=
  ∃ D : Ω → Draw H R, m.Prior f P D ∧ ∀ ω, m.Builds f (D ω) (world ω)

/-- The family of laws of the model: the random worlds of each member. -/
def laws (m : GenerativeWorld H R) : Member H R → RandomWorlds H R :=
  fun f _ _ P world => m.Holds f P world

/-- **The solutions that are compared at a member.** The solutions whose
cost, in the member `f`, is a measurable function of what is drawn: there is
a measurable function `F` of the draw such that, in every random world of the
member, the cost of the solution is `F` of the draw in almost every outcome.
The class asks nothing of a solution in other members. The weights `c` and
the lookahead are those for which the cost is taken. -/
def measurableCost [DecidableEq H] (m : GenerativeWorld H R) (f : Member H R)
    (lookahead : ℕ+) (c : Weights) : SolutionClass H R :=
  fun _ τ => ∃ F : Draw H R → ℝ≥0∞, Measurable F ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') (D : Ω' → Draw H R)
      (world : Ω' → World H R),
      m.Prior f P D → (∀ ω, m.Builds f (D ω) (world ω)) →
        ∀ᵐ ω ∂P, τ.cost (world ω) lookahead c = F (D ω)

/-- **The solutions whose playback is a measurable function of what is
drawn.** For every speaker `r` and every output sample `k` there are a
measurable set `S` of draws and a measurable function `G` of the draw such
that, in every random world of the member `f`, in almost every outcome: the
speaker plays the source at that output sample exactly when the draw is in
`S`, and then it plays the position `G` of the draw. The class asks nothing
of a solution in other members. The lookahead is the one for which the
playback is taken. -/
def measurablePlays [DecidableEq H] (m : GenerativeWorld H R) (f : Member H R)
    (lookahead : ℕ+) : SolutionClass H R :=
  fun _ τ => ∀ (r : Fin R) (k : ℕ), ∃ (S : Set (Draw H R)) (G : Draw H R → ℝ),
    MeasurableSet S ∧ Measurable G ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') (D : Ω' → Draw H R)
      (world : Ω' → World H R),
      m.Prior f P D → (∀ ω, m.Builds f (D ω) (world ω)) →
        ∀ᵐ ω ∂P, ∀ x : ℝ,
          τ.plays (world ω) lookahead r k = some x ↔ D ω ∈ S ∧ G (D ω) = x

/-- **Optimality under the generative model.** In every random world of
every member `f` of the model, the expected cost of the solution `σ` exceeds
that of no solution compared at `f` by more than `ε f`
(`Unisono.Spec.OptimalWithin`). The statement is always about every member:
a statement that covers only some members gives each of the others the
margin `⊤`. -/
def OptimalWithin [DecidableEq H] (m : GenerativeWorld H R)
    (allowed : Member H R → SolutionClass H R) (lookahead : ℕ+) (c : Weights)
    (ε : Member H R → ℝ≥0∞) {Msg : Type} (σ : Solution H R Msg) : Prop :=
  Unisono.Spec.OptimalWithin m.laws allowed lookahead c ε σ

/-! ## Checks of the definitions -/

/-- **Both least delays of a pair are positive**, in every outcome. -/
theorem Prior.leastDelay_pos {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω}
    {D : Ω → Draw H R} (h : m.Prior f P D) (ω : Ω) (i j : H) :
    0 < (D ω).split i j * f.roundTrip i j :=
  mul_pos (h.split_mem ω i j).1 (f.roundTrip_pos i j)

/-- **The two directions of a pair share its least round-trip time**, in
every outcome. -/
theorem Prior.leastDelay_add {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω}
    {D : Ω → Draw H R} (h : m.Prior f P D) (ω : Ω) (i j : H) :
    (D ω).split i j * f.roundTrip i j + (D ω).split j i * f.roundTrip j i
      = f.roundTrip i j := by
  rw [f.roundTrip_symm j i, ← add_mul, h.split_swap, one_mul]

/-- The sum of independent lengths has a probability law. -/
instance sumLaw_prob (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    IsProbabilityMeasure (sumLaw F n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | succ n ih => exact inferInstanceAs (IsProbabilityMeasure (sumLaw F n ∗ F))

/-- **The law of the paused time of a period is a probability law**: its
total mass is one. -/
theorem pauseLaw_univ (count : ℝ≥0) (F : Measure ℝ) [IsProbabilityMeasure F] :
    pauseLaw count F Set.univ = 1 := by
  have hsum : poissonMeasure count Set.univ = ∑' n : ℕ, poissonMeasure count {n} := by
    simp only [poissonMeasure_singleton]
    rw [poissonMeasure, Measure.sum_apply _ MeasurableSet.univ]
    simp
  rw [pauseLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [smul_apply, smul_eq_mul, measure_univ, mul_one]
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

/-- **No pauses, no paused time.** When no pauses begin on average, the
paused time that begins is zero. -/
theorem pauseLaw_zero (F : Measure ℝ) : pauseLaw 0 F = Measure.dirac 0 := by
  ext s hs
  rw [pauseLaw, Measure.sum_apply _ hs, tsum_eq_single 0]
  · simp [poissonMeasure_singleton, sumLaw]
  · intro n hn
    simp [poissonMeasure_singleton, hn]

end GenerativeWorld

end Unisono.Spec
