/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeDelivery
public import Mathlib.Probability.ProductMeasure

/-!
# Proposed: the generative model with jitter, loss, kernel stamps and a bandwidth limit

**Status: a proposal under review.** This file replaces nothing in the
specification until it is reviewed. What is proved under it so far: the
model is not empty, since every member has a random world
(`Unisono.Spec.ProposedWorld.exists_holds`); and, in one outcome, each
disturbance of a link gives a stretch during which nothing arrives
(`Unisono.Spec.ProposedWorld.Builds.quiet_of_jitter` and the theorems beside
it). No bound on expected cost is proved under it.

In `Unisono.Spec.GenerativeWorld` a message that meets no pause takes
exactly the least delay of its link, and no message is lost. This file
changes that, and nothing that the review of 2026-11-25 did not ask for.

## What changes against `GenerativeWorld`

* **Jitter.** Every message is late by the jitter of its link at the moment
  it is released onto the link. The jitter is never negative, has a law of
  the link that the member fixes, and comes arbitrarily close to zero only
  by chance. It stands for everything between the sending program and the
  kernel of the receiving host that varies from one message to the next,
  including the timing of the two programs. The jitter of a link is a value
  that is redrawn: it holds for a while and is then drawn again from the
  link's law, at the instants of a Poisson process with a rate of the link
  (`redrawn`, `Draw.jitter`). Messages released together therefore share
  their jitter, and messages released further apart have independent
  jitter. A jitter drawn independently for each message would reward a
  solution for sending the same block many times at once, which a real link
  does not.
* **Loss.** A link has outages: stretches of time during which it drops
  what is released onto it. They begin at the instants of a Poisson process
  with a rate of the link, and their lengths have a law of the link, any law
  of positive lengths with a mean. Besides, every message is dropped on its
  own with a probability of the link, independently of the other messages
  (`Draw.lost`).
* **The kernel's stamp.** A message that reaches a host is stamped by the
  kernel with the reading of the host's clock at that moment
  (`Draw.stamp`). The program handles the message at that moment or, when
  the host is paused, later (`Draw.observed`), and reads its clock then.
  Both readings are observed.
* **Clocks.** The wander of a clock is a sum of `scales` independent parts,
  each a stationary Gaussian process with its own size and its own time
  over which it loses its correlation.
* **Bandwidth.** The solutions that are compared stay within a limit that
  they are told: in any second, a host sends another host at most
  `messages` messages with at most `frames` frames
  (`Unisono.Spec.Solution.WithinBudget`). The limit is a condition on the
  solutions that are admitted, not a term of the cost, and it is meant to be
  set large.

Unchanged: the least delay of each direction of each pair of hosts, which is
one number of the member times the split; the pauses of links and of hosts,
which begin at the instants of independent Poisson processes; the audio
devices and their reports.

## The world of a draw

`Builds` says which world a draw gives. `Devices` states its clocks and
audio devices. Its network (`Unisono.Spec.Network`) drops the messages that
the draw loses (`Draw.delivery`), hands every other message to the program
of the receiving host at `Draw.observed`, and gives `Draw.reaches` as the
true time at which the message reaches the host. The run of a solution
(`Unisono.Spec.Solution.states`) gives the receiving program the reading of
its clock at that time as the kernel's stamp, in `Observation.received`,
and the reading of its clock when it handles the message as the reading of
the event.

## The solutions that are compared

`Compared` holds, at each member, the solutions whose cost is a measurable
function of what is drawn (`measurableCost`), that keep the speed bound
(`Unisono.Spec.Solution.WithinStep`) and that stay within the limit of the
bandwidth (`Unisono.Spec.Solution.WithinBudget` with the numbers that the
solutions are told), the last two almost surely.

## Decided against, with the reason

* A least delay that grows with the size of a message. Which pair of hosts a
  link joins is what decides its least delay.
* Pauses that cluster in time, and pauses that several links share. To be
  considered later.
* A separate lateness of each host's program. It is part of the jitter.
* A delay inside each audio device. No host can observe it, and it adds the
  same amount to the cost of every solution.

## Not decided

* Whether a host handles the events of its audio devices (the request of a
  playback block, the handover of a capture block) a jitter late, like a
  message. In this file it handles them on time, as in `GenerativeWorld`,
  unless it is paused.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- What a solution is told: what it is told in `GenerativeWorld`, and the
limit of the bandwidth: how many messages, with how many frames, a host may
send another host in any second. -/
structure Told (H : Type) (R : ℕ) extends GenerativeWorld H R where
  /-- The largest number of messages that a host sends another host in any
  second. -/
  messages : ℕ
  /-- The largest number of frames that those messages carry together. -/
  frames : ℕ

/-- One member of the family: the numbers and the laws that a solution is
not told and that are not drawn at random. -/
structure Member (H : Type) (R : ℕ) where
  /-- The least round-trip time between two hosts, in seconds. -/
  roundTrip : H → H → ℝ
  roundTrip_pos : ∀ i j, 0 < roundTrip i j
  roundTrip_symm : ∀ i j, roundTrip i j = roundTrip j i
  /-- How often the jitter of the link from `i` to `j` is redrawn, per
  second. -/
  jitterRate : H → H → ℝ
  jitterRate_pos : ∀ i j, 0 < jitterRate i j
  /-- The law of the jitter of the link from `i` to `j`, in seconds. -/
  jitterLaw : H → H → Measure ℝ
  jitterLaw_prob : ∀ i j, IsProbabilityMeasure (jitterLaw i j)
  jitterLaw_nonneg : ∀ i j, jitterLaw i j (Set.Iio 0) = 0
  jitterLaw_mean : ∀ i j, Integrable (fun x : ℝ => x) (jitterLaw i j)
  /-- The jitter comes arbitrarily close to zero: whatever every message
  takes belongs to the least delay. -/
  jitterLaw_near_zero : ∀ i j (ε : ℝ), 0 < ε → 0 < jitterLaw i j (Set.Iio ε)
  /-- How many pauses of the link from `i` to `j` begin per second, on
  average. -/
  linkPauseRate : H → H → ℝ
  linkPauseRate_nonneg : ∀ i j, 0 ≤ linkPauseRate i j
  /-- The law of the length of a pause of the link from `i` to `j`. -/
  linkPauseLength : H → H → Measure ℝ
  linkPauseLength_prob : ∀ i j, IsProbabilityMeasure (linkPauseLength i j)
  linkPauseLength_pos : ∀ i j, linkPauseLength i j (Set.Iic 0) = 0
  linkPauseLength_mean : ∀ i j, Integrable (fun x : ℝ => x) (linkPauseLength i j)
  linkLoad_lt_one : ∀ i j, linkPauseRate i j * ∫ x, x ∂(linkPauseLength i j) < 1
  /-- How many outages of the link from `i` to `j` begin per second, on
  average. -/
  outageRate : H → H → ℝ
  outageRate_nonneg : ∀ i j, 0 ≤ outageRate i j
  /-- The law of the length of an outage of the link from `i` to `j`. -/
  outageLength : H → H → Measure ℝ
  outageLength_prob : ∀ i j, IsProbabilityMeasure (outageLength i j)
  outageLength_pos : ∀ i j, outageLength i j (Set.Iic 0) = 0
  outageLength_mean : ∀ i j, Integrable (fun x : ℝ => x) (outageLength i j)
  outageLoad_lt_one : ∀ i j, outageRate i j * ∫ x, x ∂(outageLength i j) < 1
  /-- The probability that the link from `i` to `j` drops a message on its
  own. -/
  lossProbability : H → H → ℝ
  lossProbability_nonneg : ∀ i j, 0 ≤ lossProbability i j
  lossProbability_lt_one : ∀ i j, lossProbability i j < 1
  /-- How many pauses of host `h` begin per second. -/
  hostPauseRate : H → ℝ
  hostPauseRate_nonneg : ∀ h, 0 ≤ hostPauseRate h
  /-- The law of the length of a pause of host `h`. -/
  hostPauseLength : H → Measure ℝ
  hostPauseLength_prob : ∀ h, IsProbabilityMeasure (hostPauseLength h)
  hostPauseLength_pos : ∀ h, hostPauseLength h (Set.Iic 0) = 0
  hostPauseLength_mean : ∀ h, Integrable (fun x : ℝ => x) (hostPauseLength h)
  hostLoad_lt_one : ∀ h, hostPauseRate h * ∫ x, x ∂(hostPauseLength h) < 1
  /-- The standard deviation of the logarithm of a clock's mean rate. -/
  rateSpread : ℝ
  rateSpread_nonneg : 0 ≤ rateSpread
  /-- The number of parts of the wander of a clock. -/
  scales : ℕ
  /-- The standard deviation of part `k` of the wander of the clock of host
  `h`. -/
  wanderSize : H → ℕ → ℝ
  wanderSize_nonneg : ∀ h k, 0 ≤ wanderSize h k
  /-- The time over which part `k` of the wander of the clock of host `h`
  loses its correlation, in seconds. -/
  wanderTime : H → ℕ → ℝ
  wanderTime_pos : ∀ h k, 0 < wanderTime h k
  /-- The standard deviation of part `k` of the wander of the clock of the
  audio device `x`. The device `none` is the capture device. -/
  deviceWanderSize : Option (Fin R) → ℕ → ℝ
  deviceWanderSize_nonneg : ∀ x k, 0 ≤ deviceWanderSize x k
  /-- The time over which part `k` of the wander of the clock of the audio
  device `x` loses its correlation. -/
  deviceWanderTime : Option (Fin R) → ℕ → ℝ
  deviceWanderTime_pos : ∀ x k, 0 < deviceWanderTime x k
  /-- The standard deviation of the error of the reports of the audio device
  `x`, in seconds. -/
  reportSize : Option (Fin R) → ℝ
  reportSize_nonneg : ∀ x, 0 ≤ reportSize x
  /-- The time over which the error of the reports of the audio device `x`
  loses its correlation. -/
  reportTime : Option (Fin R) → ℝ
  reportTime_pos : ∀ x, 0 < reportTime x
  /-- Clock offsets are uniform between `-offsetRange` and `offsetRange`. -/
  offsetRange : ℝ
  offsetRange_pos : 0 < offsetRange
  /-- The reading of the sender's clock at which frame zero is captured. -/
  captureStart : ℝ
  /-- The reading of its host's clock at which output sample zero of each
  speaker leaves. -/
  speakerStart : Fin R → ℝ

/-- What is drawn at random: one outcome. -/
structure Draw (H : Type) (R : ℕ) where
  /-- The share of the least round trip of `i` and `j` that the direction
  from `i` to `j` takes. -/
  split : H → H → ℝ
  /-- The offset of each host's clock. -/
  offset : H → ℝ
  /-- The logarithm of the mean rate of each host's clock. -/
  logRate : H → ℝ
  /-- Part `k` of the wander of each host's clock at each true time. -/
  wander : H → ℕ → Time → ℝ
  /-- The logarithm of the mean rate of the clock of each audio device. -/
  deviceLogRate : Option (Fin R) → ℝ
  /-- Part `k` of the wander of the clock of each audio device. -/
  deviceWander : Option (Fin R) → ℕ → Time → ℝ
  /-- The error of the reports of each audio device, as a function of the
  true time of what is reported. -/
  reportError : Option (Fin R) → Time → ℝ
  /-- The count of the jitter of each directed link: it rises by one at each
  instant at which the jitter is redrawn, and is zero at true time zero. -/
  jitterCount : H → H → Time → ℝ
  /-- The values that the jitter of each directed link takes, numbered by
  the count; value zero is the one at true time zero. -/
  jitterLevel : H → H → ℤ → ℝ
  /-- The paused time of each directed link that has begun by each true
  time. -/
  linkPaused : H → H → Time → ℝ
  /-- The outage time of each directed link that has begun by each true
  time. -/
  outage : H → H → Time → ℝ
  /-- Whether each directed link drops, on its own, the message with each
  number among the messages sent on the link. -/
  dropped : H → H → ℕ → Bool
  /-- The paused time of each host that has begun by each true time. -/
  hostPaused : H → Time → ℝ

/-- **A value that is redrawn.** Its value at the true time `t` is the level
whose number is the count at `t`. -/
def redrawn {α : Type} (count : Time → ℝ) (level : ℤ → α) (t : Time) : α :=
  level ⌊count t⌋

namespace Draw

variable (d : Draw H R) (f : Member H R)

/-- What the clock of host `h` reads at true time `t`: its offset plus the
integral of its rate, which is the exponential of the logarithm of its mean
rate plus the parts of its wander. -/
def reading (h : H) (t : Time) : ℝ :=
  d.offset h
    + ∫ x in (0 : ℝ)..t, Real.exp (d.logRate h + ∑ k ∈ Finset.range f.scales, d.wander h k x)

/-- By how much the clock of the audio device `x` advances between true time
zero and true time `t`. -/
def deviceReading (x : Option (Fin R)) (t : Time) : ℝ :=
  ∫ y in (0 : ℝ)..t,
    Real.exp (d.deviceLogRate x + ∑ k ∈ Finset.range f.scales, d.deviceWander x k y)

/-- **The jitter** of the link from `i` to `j` at the true time `u`. -/
def jitter (i j : H) (u : Time) : ℝ := redrawn (d.jitterCount i j) (d.jitterLevel i j) u

/-- When a message that host `i` sends at the true time `s` leaves its
program: after the backlog of the host's pauses. -/
def leaves (i : H) (s : Time) : Time := s + GenerativeWorld.backlog (d.hostPaused i) s

/-- When a message from `i` to `j`, sent at `s`, is released onto the link:
after the backlog of the link's pauses when it leaves the program. -/
def released (i j : H) (s : Time) : Time :=
  d.leaves i s + GenerativeWorld.backlog (d.linkPaused i j) (d.leaves i s)

/-- **A message is lost** when the link is in an outage at the true time at
which the message is released onto it, or drops the message on its own.
The message is the one with the number `q` among those sent from `i` to
`j`. -/
def lost (i j : H) (s : Time) (q : ℕ) : Prop :=
  0 < GenerativeWorld.backlog (d.outage i j) (d.released i j s) ∨ d.dropped i j q = true

/-- **When a message reaches the receiving host**, if it is not lost: the
least delay of the direction and the jitter of the moment of its release,
after that release. -/
def reaches (i j : H) (s : Time) : Time :=
  d.released i j s + d.split i j * f.roundTrip i j + d.jitter i j (d.released i j s)

/-- **The kernel's stamp**: the reading of the receiving host's clock when
the message reaches the host. -/
def stamp (i j : H) (s : Time) : ℝ := d.reading f j (d.reaches f i j s)

/-- **When the program of the receiving host handles a message**: when the
message reaches the host, or after the backlog of the host's pauses at that
time. -/
def observed (i j : H) (s : Time) : Time :=
  d.reaches f i j s + GenerativeWorld.backlog (d.hostPaused j) (d.reaches f i j s)

/-- **Whether and when the program of the receiving host handles a
message**: `none` for a message that is lost, and otherwise the true time
`observed`. The message is the one with the number `q` among those sent from
`i` to `j`, sent at the true time `s`. -/
def delivery (i j : H) (s : Time) (q : ℕ) : Option Time := by
  classical
  exact if d.lost i j s q then none else some (d.observed f i j s)

end Draw

/-- **The devices and the clocks of the world `w` are those of the draw
`d`**, in the member `f`: as in `GenerativeWorld.Builds`, with the clocks of
this model. This is the part of the world that needs no change of the
specification's interface. -/
structure Devices (m : Told H R) (f : Member H R) (d : Draw H R) (w : World H R) : Prop where
  rate_eq : w.rate = m.rate
  sender_eq : w.sender = m.sender
  host_eq : w.host = m.host
  /-- Each host's clock reads what the draw says. -/
  clock : ∀ h t, (w.clock h).read t = d.reading f h t
  /-- The capture device starts when the sender's clock reads
  `f.captureStart`. -/
  capture_start : (w.clock w.sender).read (w.source.capture 0) = f.captureStart
  /-- The capture device runs on its own clock. -/
  capture : ∀ n : ℕ,
    d.deviceReading f none (w.source.capture n) - d.deviceReading f none (w.source.capture 0)
      = (n : ℝ) / m.rate
  /-- Capture blocks hold `m.blockSize` frames. -/
  capture_first : ∀ b : ℕ, w.source.first b = b * m.blockSize
  /-- The capture device hands a block over when the block's last frame is
  captured, and the sender's host handles the handover after the backlog of
  its pauses at that time. -/
  capture_handed : ∀ b : ℕ,
    w.source.handed b
      = w.source.capture (w.source.first (b + 1) - 1)
        + GenerativeWorld.backlog (d.hostPaused w.sender)
            (w.source.capture (w.source.first (b + 1) - 1))
  /-- The timestamp of a capture block is the reading of the sender's clock
  when the block's first frame is captured, plus the error of the device's
  reports at that time. -/
  capture_reported : ∀ b : ℕ,
    w.source.reported b
      = (w.clock w.sender).read (w.source.capture (w.source.first b))
        + d.reportError none (w.source.capture (w.source.first b))
  /-- The playback device of speaker `r` starts when the clock of its host
  reads the start of the speaker that stands for the device. -/
  speaker_start : ∀ r : Fin R,
    (w.clock (w.host r)).read ((w.speaker r).out 0) = f.speakerStart (m.device r)
  /-- Each playback device runs on its own clock. -/
  speaker_out : ∀ (r : Fin R) (k : ℕ),
    d.deviceReading f (some (m.device r)) ((w.speaker r).out k)
        - d.deviceReading f (some (m.device r)) ((w.speaker r).out 0)
      = (k : ℝ) / m.rate
  /-- Playback blocks hold `m.blockSize` output samples. -/
  speaker_first : ∀ (r : Fin R) (b : ℕ), (w.speaker r).first b = b * m.blockSize
  /-- A playback device requests each block at the true time `ρ` that is
  `m.lead`, on its own clock, before the block's first output sample leaves.
  The speaker's host handles the request after the backlog of its pauses at
  that time. -/
  speaker_asked : ∀ (r : Fin R) (b : ℕ), ∃ ρ,
    d.deviceReading f (some (m.device r)) ((w.speaker r).out ((w.speaker r).first b))
        - d.deviceReading f (some (m.device r)) ρ = m.lead
      ∧ (w.speaker r).asked b = ρ + GenerativeWorld.backlog (d.hostPaused (w.host r)) ρ
  /-- The timestamp of a playback block is the reading of the host's clock
  when the block's first output sample leaves, plus the error of the
  device's reports at that time. -/
  speaker_reported : ∀ (r : Fin R) (b : ℕ),
    (w.speaker r).reported b
      = (w.clock (w.host r)).read ((w.speaker r).out ((w.speaker r).first b))
        + d.reportError (some (m.device r)) ((w.speaker r).out ((w.speaker r).first b))
  /-- The target latency is constant. -/
  target_eq : ∀ n : ℕ, w.target n = m.targetLatency

/-- **Episodes that begin at the instants of a Poisson process.** The path
`X` records the total length of the episodes that have begun, counted from
true time zero: it never decreases, an episode counts from the instant at
which it begins, what begins in stretches that do not overlap is
independent, and what begins in a stretch of length `t - s` has the law
`pauseLaw` for `rate * (t - s)` episodes on average with lengths of the law
`F`. With `F` the unit mass at one, `X` counts instants. -/
structure IsEpisodePath (rate : ℝ) (F : Measure ℝ) (X : Time → Ω → ℝ) (P : Measure Ω) :
    Prop where
  zero : ∀ ω, X 0 ω = 0
  monotone : ∀ ω, Monotone fun t => X t ω
  rightContinuous : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t
  increments : HasIndepIncrements X P
  law : ∀ s t, s ≤ t →
    HasLaw (fun ω => X t ω - X s ω)
      (GenerativeWorld.pauseLaw (Real.toNNReal (rate * (t - s))) F) P

/-- The law of a value that is `true` with probability `p`. -/
def dropLaw (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

theorem dropLaw_true (p : ℝ) : dropLaw p {b | b = true} = ENNReal.ofReal p := by
  simp [dropLaw]

theorem dropLaw_prob {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (dropLaw p) := by
  refine ⟨?_⟩
  simp only [dropLaw, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

instance (f : Member H R) (i j : H) : IsProbabilityMeasure (f.jitterLaw i j) :=
  f.jitterLaw_prob i j

/-- The parts of a draw that are drawn independently of one another. -/
inductive Part (H : Type) (R : ℕ) where
  | split (z : {z : Sym2 H // ¬ z.IsDiag})
  | offset (h : H)
  | logRate (h : H)
  | wander (h : H) (k : ℕ)
  | deviceLogRate (x : Option (Fin R))
  | deviceWander (x : Option (Fin R)) (k : ℕ)
  | reportError (x : Option (Fin R))
  | jitterCount (i j : H)
  | jitterLevel (i j : H)
  | linkPaused (i j : H)
  | outage (i j : H)
  | dropped (i j : H) (q : ℕ)
  | hostPaused (h : H)

/-- What kind of value each part is: a number, a function of time, a
sequence of values, or yes or no. -/
def Part.Val : Part H R → Type
  | .split _ => ℝ
  | .offset _ => ℝ
  | .logRate _ => ℝ
  | .wander _ _ => Time → ℝ
  | .deviceLogRate _ => ℝ
  | .deviceWander _ _ => Time → ℝ
  | .reportError _ => Time → ℝ
  | .jitterCount _ _ => Time → ℝ
  | .jitterLevel _ _ => ℤ → ℝ
  | .linkPaused _ _ => Time → ℝ
  | .outage _ _ => Time → ℝ
  | .dropped _ _ _ => Bool
  | .hostPaused _ => Time → ℝ

instance (p : Part H R) : MeasurableSpace p.Val := by
  cases p
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace ℝ)
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace (ℤ → ℝ))
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))
  · exact inferInstanceAs (MeasurableSpace Bool)
  · exact inferInstanceAs (MeasurableSpace (Time → ℝ))

/-- The value of each part of a draw, with each pair of hosts taken in the
order that `o` chooses. -/
def Draw.part (d : Draw H R) (o : GenerativeWorld.Orientation H) : (p : Part H R) → p.Val
  | .split z => d.split (o z).1.1 (o z).1.2
  | .offset h => d.offset h
  | .logRate h => d.logRate h
  | .wander h k => d.wander h k
  | .deviceLogRate x => d.deviceLogRate x
  | .deviceWander x k => d.deviceWander x k
  | .reportError x => d.reportError x
  | .jitterCount i j => d.jitterCount i j
  | .jitterLevel i j => d.jitterLevel i j
  | .linkPaused i j => d.linkPaused i j
  | .outage i j => d.outage i j
  | .dropped i j q => d.dropped i j q
  | .hostPaused h => d.hostPaused h

/-- **The prior.** The random draw `D ω`, for `ω` drawn from `P`, has the
law of the member `f`, for what the solution is told in `m`. -/
structure Prior (m : Told H R) (f : Member H R) (P : Measure Ω) (D : Ω → Draw H R) :
    Prop where
  prob : IsProbabilityMeasure P
  /-- The two directions of a pair share its least round-trip time. -/
  split_swap : ∀ ω i j, (D ω).split i j + (D ω).split j i = 1
  split_mem : ∀ ω i j, (D ω).split i j ∈ Set.Ioo (0 : ℝ) 1
  /-- The split of two distinct hosts has the Beta law with both parameters
  equal to the shape. -/
  split_law : ∀ i j, i ≠ j →
    HasLaw (fun ω => (D ω).split i j) (betaMeasure m.shape m.shape) P
  offset_law : ∀ h, MeasureTheory.pdf.IsUniform (fun ω => (D ω).offset h)
    (Set.Icc (-f.offsetRange) f.offsetRange) P
  logRate_law : ∀ h,
    HasLaw (fun ω => (D ω).logRate h) (gaussianReal 0 (Real.toNNReal (f.rateSpread ^ 2))) P
  /-- Each part of the wander of a clock is a stationary Gaussian process
  with mean zero, continuous in time. -/
  wander_gaussian : ∀ h k, IsGaussianProcess (fun t ω => (D ω).wander h k t) P
  wander_mean : ∀ h k t, ∫ ω, (D ω).wander h k t ∂P = 0
  wander_covariance : ∀ h k s t,
    cov[fun ω => (D ω).wander h k s, fun ω => (D ω).wander h k t; P]
      = f.wanderSize h k ^ 2 * Real.exp (-|s - t| / f.wanderTime h k)
  wander_continuous : ∀ ω h k, Continuous ((D ω).wander h k)
  deviceLogRate_law : ∀ x,
    HasLaw (fun ω => (D ω).deviceLogRate x)
      (gaussianReal 0 (Real.toNNReal (f.rateSpread ^ 2))) P
  deviceWander_gaussian : ∀ x k, IsGaussianProcess (fun t ω => (D ω).deviceWander x k t) P
  deviceWander_mean : ∀ x k t, ∫ ω, (D ω).deviceWander x k t ∂P = 0
  deviceWander_covariance : ∀ x k s t,
    cov[fun ω => (D ω).deviceWander x k s, fun ω => (D ω).deviceWander x k t; P]
      = f.deviceWanderSize x k ^ 2 * Real.exp (-|s - t| / f.deviceWanderTime x k)
  deviceWander_continuous : ∀ ω x k, Continuous ((D ω).deviceWander x k)
  reportError_gaussian : ∀ x, IsGaussianProcess (fun t ω => (D ω).reportError x t) P
  reportError_mean : ∀ x t, ∫ ω, (D ω).reportError x t ∂P = 0
  reportError_covariance : ∀ x s t,
    cov[fun ω => (D ω).reportError x s, fun ω => (D ω).reportError x t; P]
      = f.reportSize x ^ 2 * Real.exp (-|s - t| / f.reportTime x)
  reportError_continuous : ∀ ω x, Continuous ((D ω).reportError x)
  /-- The jitter of each directed link is redrawn at the instants of a
  Poisson process, and its values are independent with the link's law. -/
  jitterCount_law : ∀ i j,
    IsEpisodePath (f.jitterRate i j) (Measure.dirac 1) (fun t ω => (D ω).jitterCount i j t) P
  jitterLevel_law : ∀ i j,
    HasLaw (fun ω => (D ω).jitterLevel i j)
      (Measure.infinitePi fun _ : ℤ => f.jitterLaw i j) P
  jitterLevel_nonneg : ∀ ω i j n, 0 ≤ (D ω).jitterLevel i j n
  /-- The pauses of each directed link. -/
  linkPaused_law : ∀ i j,
    IsEpisodePath (f.linkPauseRate i j) (f.linkPauseLength i j)
      (fun t ω => (D ω).linkPaused i j t) P
  /-- The outages of each directed link. -/
  outage_law : ∀ i j,
    IsEpisodePath (f.outageRate i j) (f.outageLength i j) (fun t ω => (D ω).outage i j t) P
  /-- Each directed link drops each message on its own with the link's
  probability. -/
  dropped_law : ∀ i j q,
    HasLaw (fun ω => (D ω).dropped i j q) (dropLaw (f.lossProbability i j)) P
  /-- The pauses of each host. -/
  hostPaused_law : ∀ h,
    IsEpisodePath (f.hostPauseRate h) (f.hostPauseLength h)
      (fun t ω => (D ω).hostPaused h t) P
  /-- The parts of the draw are independent, whichever order each pair of
  hosts is taken in. -/
  independent : ∀ o : GenerativeWorld.Orientation H, iIndepFun (fun p ω => (D ω).part o p) P

/-- **The world `w` is the world built from the draw `d`** in the member
`f`. Its clocks and audio devices are those of the draw (`Devices`). Its
network drops the messages that the draw loses and hands every other message
to the program of the receiving host at `Draw.observed` (`Draw.delivery`);
a message reaches the receiving host, where the kernel stamps it, at
`Draw.reaches`. -/
structure Builds (m : Told H R) (f : Member H R) (d : Draw H R) (w : World H R) : Prop
    extends Devices m f d w where
  deliver : ∀ i j s q, w.network.deliver i j s q = d.delivery f i j s q
  reach : ∀ i j s q, w.network.reach i j s q = d.reaches f i j s

instance : MeasurableSpace (Draw H R) :=
  MeasurableSpace.comap
    (fun d : Draw H R =>
      (d.split, d.offset, d.logRate, d.wander, d.deviceLogRate, d.deviceWander, d.reportError,
        d.jitterCount, d.jitterLevel, d.linkPaused, d.outage, d.dropped, d.hostPaused))
    inferInstance

/-- A random world, `world ω` for `ω` drawn from `P`, belongs to the member
`f` of the model: in every outcome it is the world built from a draw, and
the draw has the law of the member. -/
def Holds (m : Told H R) (f : Member H R) (P : Measure Ω) (world : Ω → World H R) : Prop :=
  ∃ D : Ω → Draw H R, Prior m f P D ∧ ∀ ω, Builds m f (D ω) (world ω)

/-- The family of laws of the model: the random worlds of each member. -/
def laws (m : Told H R) : Member H R → RandomWorlds H R :=
  fun f _ _ P world => Holds m f P world

/-- A property of the world holds almost surely for the member `f`: in
almost every outcome of every random world of the member. -/
def AlmostSurely (m : Told H R) (f : Member H R) (p : World H R → Prop) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → Draw H R) (world : Ω → World H R),
    Prior m f P D → (∀ ω, Builds m f (D ω) (world ω)) → ∀ᵐ ω ∂P, p (world ω)

/-- **The solutions whose cost is a measurable function of what is drawn**,
in the member `f`: there is a measurable function `F` of the draw such that,
in every random world of the member, the cost of the solution is `F` of the
draw in almost every outcome. The class asks nothing of a solution in other
members. -/
def measurableCost [DecidableEq H] (m : Told H R) (f : Member H R) (lookahead : ℕ+)
    (c : Weights) : SolutionClass H R :=
  fun _ τ => ∃ F : Draw H R → ℝ≥0∞, Measurable F ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') (D : Ω' → Draw H R)
      (world : Ω' → World H R),
      Prior m f P D → (∀ ω, Builds m f (D ω) (world ω)) →
        ∀ᵐ ω ∂P, τ.cost (world ω) lookahead c = F (D ω)

/-- **The solutions that are compared at the member `f`**, for a lookahead,
weights and a speed bound `u`. -/
structure Compared [DecidableEq H] (m : Told H R) (f : Member H R) (lookahead : ℕ+)
    (c : Weights) (u : ℝ) (Msg : Type) (τ : Solution H R Msg) : Prop where
  /-- The cost in the member is a measurable function of what is drawn. -/
  measurable : measurableCost m f lookahead c Msg τ
  /-- Almost surely, the position advances by one frame per output sample
  within `u`, in every step of continuous playback. -/
  withinStep : AlmostSurely m f fun w => τ.WithinStep w lookahead u
  /-- Almost surely, in any second a host sends another host at most
  `m.messages` messages with at most `m.frames` frames. -/
  withinBudget : AlmostSurely m f fun w => τ.WithinBudget w lookahead m.messages m.frames

/-- **Optimality under the model.** In every random world of every member
`f`, the expected cost of the solution `σ` exceeds that of no solution
compared at `f` by more than `ε f` (`Unisono.Spec.OptimalWithin`). A
statement that covers only some members gives each of the others the margin
`⊤`. -/
def OptimalWithin [DecidableEq H] (m : Told H R)
    (allowed : Member H R → SolutionClass H R) (lookahead : ℕ+) (c : Weights)
    (ε : Member H R → ℝ≥0∞) {Msg : Type} (σ : Solution H R Msg) : Prop :=
  Unisono.Spec.OptimalWithin (laws m) allowed lookahead c ε σ

end Unisono.Spec.ProposedWorld
