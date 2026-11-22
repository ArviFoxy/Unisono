/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.Delays
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A second-order model of the world

The second-order model states the means and covariances of the world's
noise: of the clocks, of the delays and of the devices. The objectives of
synchronization, latency, tracking and roughness are quadratic in the
latency errors. For them, and for solutions that are linear in their
measurements, the means and covariances are all that matters. Missed samples
depend on more than the second moments: on how long the holds of the delay
model (`Unisono.Spec.Models.Delays`) last.

* **Clocks.** A host's clock reads `t + φ t` at true time `t`, where `φ` is
  the clock's phase. The one-sided spectral density of the clock's
  fractional frequency, the derivative of `φ`, is
  `white + flicker / f + walk / f²` at frequency `f` (`ClockNoise`): white,
  flicker and random-walk frequency noise, the power-law components that
  dominate in quartz oscillators. The model states the covariances of the
  second differences `φ (t + 2τ) - 2 φ (t + τ) + φ t` of the phase
  (`FollowsNoise`), because the first differences of a phase with
  random-walk frequency noise are not stationary. The phases of different
  hosts are uncorrelated.
* **Delays.** A link's delay is its floor, its jitter and its holds, as in
  the delay model. The jitter of a link is the sum of a part common to all
  links that leave one host and a part of its own. Each part has a constant
  mean and a covariance that depends only on the time between two messages
  (`JitterNoise`), and the parts of different links are uncorrelated. The
  holds of a link are those common to all links that leave its host and
  those of its own.
* **Devices.** A device's timing deviates from its host's clock as a clock
  deviates from true time, with a power-law spectrum. The device's
  timestamps add white noise of a given variance.

The parts common to all links are the sender's clock, the jitter and the
holds common to the sender's links, and the capture device. The parts of
each link are a receiving host's clock, the link's own jitter and holds, and
the playback devices on that host.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory

/-- Power-law frequency noise of a clock or a device: the one-sided spectral
density of its fractional frequency is `white + flicker / f + walk / f ^ 2`
at frequency `f > 0`, in hertz. -/
structure ClockNoise where
  /-- The level of white frequency noise, in 1/Hz. -/
  white : ℝ
  white_nonneg : 0 ≤ white
  /-- The level of flicker frequency noise, dimensionless. -/
  flicker : ℝ
  flicker_nonneg : 0 ≤ flicker
  /-- The level of random-walk frequency noise, in Hz. -/
  walk : ℝ
  walk_nonneg : 0 ≤ walk

/-- The one-sided spectral density of the fractional frequency at `f`. -/
def ClockNoise.density (n : ClockNoise) (f : ℝ) : ℝ :=
  n.white + n.flicker / f + n.walk / f ^ 2

/-- No noise at all. -/
def ClockNoise.zero : ClockNoise :=
  ⟨0, le_rfl, 0, le_rfl, 0, le_rfl⟩

/-- The second difference of `φ` with lag `τ` at `t`. -/
def secondDifference (φ : ℝ → ℝ) (t τ : ℝ) : ℝ :=
  φ (t + 2 * τ) - 2 * φ (t + τ) + φ t

/-- The covariance of two second differences, with lags `τ₁` and `τ₂` at
times `t₁` and `t₂`, of a phase whose fractional frequency has the one-sided
spectral density `S`. The integrand is the spectral density of the phase,
`S f / (2π f)²`, times the product of the two second differences' transfer
functions `(e^{2πifτ} - 1)²`. For white, flicker and random-walk frequency
noise the integral converges at both ends. -/
def secondDifferenceCovariance (S : ℝ → ℝ) (t₁ τ₁ t₂ τ₂ : ℝ) : ℝ :=
  ∫ f in Set.Ioi 0, S f / (2 * Real.pi * f) ^ 2 *
    (Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
      * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
      * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re

variable {Ω : Type} [MeasurableSpace Ω]

/-- A random phase `φ` follows the noise `n`: its second differences have
mean zero and the covariances of the power-law spectrum. -/
def FollowsNoise (P : Measure Ω) (φ : Ω → ℝ → ℝ) (n : ClockNoise) : Prop :=
  (∀ t τ, ∫ ω, secondDifference (φ ω) t τ ∂P = 0) ∧
    ∀ t₁ τ₁ t₂ τ₂, ∫ ω, secondDifference (φ ω) t₁ τ₁ * secondDifference (φ ω) t₂ τ₂ ∂P
      = secondDifferenceCovariance n.density t₁ τ₁ t₂ τ₂

/-- Two random phases are uncorrelated: the products of their second
differences have mean zero. -/
def Uncorrelated (P : Measure Ω) (φ ψ : Ω → ℝ → ℝ) : Prop :=
  ∀ t₁ τ₁ t₂ τ₂, ∫ ω, secondDifference (φ ω) t₁ τ₁ * secondDifference (ψ ω) t₂ τ₂ ∂P = 0

/-- The phase of a device at its `k`-th frame or output sample, against its
host's clock `C`: the reading of `C` when the frame is captured or the
output sample leaves, minus `k / rate`. -/
def devicePhase (C : Clock) (times : ℕ → Time) (rate : ℝ) (k : ℕ) : ℝ :=
  C.read (times k) - k / rate

/-- The second difference of a sequence `ψ` with lag `j` at `k`. -/
def gridDifference (ψ : ℕ → ℝ) (k j : ℕ) : ℝ :=
  ψ (k + 2 * j) - 2 * ψ (k + j) + ψ k

/-- A random sequence of phases `ψ`, one for each frame or output sample of a
device with the nominal rate `rate`, follows the noise `n`: its second
differences have mean zero and the covariances of the power-law spectrum,
taken at the nominal times `k / rate`. -/
def FollowsNoiseOnGrid (P : Measure Ω) (ψ : Ω → ℕ → ℝ) (rate : ℝ) (n : ClockNoise) : Prop :=
  (∀ k j, ∫ ω, gridDifference (ψ ω) k j ∂P = 0) ∧
    ∀ k₁ j₁ k₂ j₂, ∫ ω, gridDifference (ψ ω) k₁ j₁ * gridDifference (ψ ω) k₂ j₂ ∂P
      = secondDifferenceCovariance n.density (k₁ / rate) (j₁ / rate) (k₂ / rate) (j₂ / rate)

/-- The second moments of a stationary jitter: its mean, and its covariance
as a function of the time between two messages. -/
structure JitterNoise where
  /-- The mean, in seconds. -/
  mean : ℝ
  /-- The covariance of the jitter of two messages sent `u` seconds apart,
  in square seconds. -/
  covariance : ℝ → ℝ

/-- A random jitter `x` has the second moments `n`. -/
def HasMoments (P : Measure Ω) (x : Ω → Time → ℝ) (n : JitterNoise) : Prop :=
  (∀ s, ∫ ω, x ω s ∂P = n.mean) ∧
    ∀ s u, ∫ ω, (x ω s - n.mean) * (x ω u - n.mean) ∂P = n.covariance (u - s)

/-- Two random jitters are uncorrelated. -/
def UncorrelatedJitter (P : Measure Ω) (x y : Ω → Time → ℝ) : Prop :=
  ∀ s u, ∫ ω, (x ω s - ∫ ω', x ω' s ∂P) * (y ω u - ∫ ω', y ω' u ∂P) ∂P = 0

/-- The parameters of the second-order model, for hosts `H` and `R`
speakers. -/
structure SecondOrderModel (H : Type) (R : ℕ) where
  /-- The noise of each host's clock against true time. -/
  clock : H → ClockNoise
  /-- The jitter common to all links that leave each host. -/
  commonJitter : H → JitterNoise
  /-- The jitter of each link of its own. -/
  ownJitter : H → H → JitterNoise
  /-- The noise of the capture device against the sender's clock. -/
  capture : ClockNoise
  /-- The noise of each speaker's playback device against its host's clock. -/
  playback : Fin R → ClockNoise
  /-- The variance of the white noise of the devices' timestamps, in square
  seconds. -/
  timestampVariance : ℝ
  timestampVariance_nonneg : 0 ≤ timestampVariance

/-- The error of the capture device's timestamp of block `b`: the timestamp
minus the reading of the sender's clock when the block's first frame is
captured. -/
def captureError {H : Type} {R : ℕ} (w : World H R) (b : ℕ) : ℝ :=
  w.source.reported b - (w.clock w.sender).read (w.source.capture (w.source.first b))

/-- The error of speaker `r`'s timestamp of block `b`: the timestamp minus
the reading of its host's clock when the block's first output sample
leaves. -/
def playbackError {H : Type} {R : ℕ} (w : World H R) (r : Fin R) (b : ℕ) : ℝ :=
  (w.speaker r).reported b - (w.clock (w.host r)).read ((w.speaker r).out ((w.speaker r).first b))

/-- Random errors `e` of timestamps are white with variance `v`: their means
are zero, and the mean of the product of two of them is `v` for the same
block and zero for different blocks. -/
def WhiteErrors (P : Measure Ω) (e : Ω → ℕ → ℝ) (v : ℝ) : Prop :=
  (∀ b, ∫ ω, e ω b ∂P = 0) ∧
    ∀ b b', ∫ ω, e ω b * e ω b' ∂P = if b = b' then v else 0

/-- A random world `world ω`, with `ω` drawn from `P`, follows the
second-order model `m`, with the network made of the random links `d`.

* Every clock's phase follows its noise, and the phases of different hosts
  are uncorrelated.
* The jitter of each link is the sum of a part common to all links that
  leave its host and a part of its own. Each part has its second moments,
  and the parts are uncorrelated with each other, link by link.
* The holds of each link are those common to all links that leave its host
  and those of its own.
* The capture device follows its noise against the sender's clock, and each
  playback device against its host's clock.
* The timestamps' errors are white. -/
structure SecondOrderModel.Holds {H : Type} {R : ℕ} (m : SecondOrderModel H R)
    (P : Measure Ω) (world : Ω → World H R) (d : Ω → H → H → Link) : Prop where
  /-- The network of each world consists of the links `d`. -/
  network : ∀ ω, (world ω).HasDelays (d ω)
  /-- Every clock's phase follows its noise. -/
  clocks : ∀ i, FollowsNoise P (fun ω t => ((world ω).clock i).read t - t) (m.clock i)
  /-- The phases of different hosts are uncorrelated. -/
  clocks_uncorrelated : ∀ i j, i ≠ j →
    Uncorrelated P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω t => ((world ω).clock j).read t - t)
  /-- The jitter of each link splits into a part common to the links that
  leave its host and a part of its own, with their second moments; the parts
  are uncorrelated. -/
  jitter : ∃ common : Ω → H → Time → ℝ, ∃ own : Ω → H → H → Time → ℝ,
    (∀ ω i j u, (d ω i j).jitter u = common ω i u + own ω i j u)
      ∧ (∀ i, HasMoments P (fun ω => common ω i) (m.commonJitter i))
      ∧ (∀ i j, HasMoments P (fun ω => own ω i j) (m.ownJitter i j))
      ∧ (∀ i j i', UncorrelatedJitter P (fun ω => own ω i j) (fun ω => common ω i'))
      ∧ (∀ i j i' j', (i, j) ≠ (i', j') →
          UncorrelatedJitter P (fun ω => own ω i j) (fun ω => own ω i' j'))
  /-- The holds of each link are those common to the links that leave its
  host and those of its own. -/
  holds : ∃ common : Ω → H → Set Pause, ∃ own : Ω → H → H → Set Pause,
    ∀ ω i j, (d ω i j).pauses = common ω i ∪ own ω i j
  /-- The capture device follows its noise against the sender's clock. The
  nominal rate is the same in every world. -/
  capture : ∃ rate, (∀ ω, (world ω).rate = rate) ∧ FollowsNoiseOnGrid P
    (fun ω => devicePhase ((world ω).clock (world ω).sender) (world ω).source.capture rate)
    rate m.capture
  /-- Each playback device follows its noise against its host's clock. -/
  playback : ∀ r, ∃ rate, (∀ ω, (world ω).rate = rate) ∧ FollowsNoiseOnGrid P
    (fun ω => devicePhase ((world ω).clock ((world ω).host r)) ((world ω).speaker r).out rate)
    rate (m.playback r)
  /-- The capture device's timestamps have white errors. -/
  capture_timestamps : WhiteErrors P (fun ω => captureError (world ω)) m.timestampVariance
  /-- Each playback device's timestamps have white errors. -/
  playback_timestamps : ∀ r,
    WhiteErrors P (fun ω => playbackError (world ω) r) m.timestampVariance

end Unisono.Spec
