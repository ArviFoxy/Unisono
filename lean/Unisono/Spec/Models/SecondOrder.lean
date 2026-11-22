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
# A second-order noise model of the world

The second-order model specifies the means and covariances of continuous timing
noise in a random world: host clocks, network link jitter, audio device clocks,
and device timestamp errors.

In `Unisono.Spec.Objectives`, synchronization (`syncCost`), target tracking
(`trackingCost`), and linearized roughness (`roughnessCost`) are quadratic in
timing errors, whereas mean latency (`latencyCost`) is linear, and missed
samples (`missedAt`) and discontinuities (`discontinuityAt`) depend on the full
tail of network pauses and outages (`Unisono.Spec.Models.Delays`). Second
moments alone therefore characterize the quadratic objectives for linear
estimators and controllers, while pauses, outages, and packet drops are
governed separately by `DelayModel`.

* **Clocks (`ClockNoise`, `FollowsNoise`).** Host `i`'s clock reads
  `t + φ_i(t)` at true time `t`. Its fractional frequency `y_i = φ_i'` has the
  IEEE 1139 one-sided power spectral density
  `S_y(f) = white + flicker / f + walk / f²` for `f > 0` (white, flicker, and
  random-walk frequency noise). Because random-walk frequency noise has
  non-stationary first differences, the model specifies the zero means and
  exact covariances of second differences
  `Δ²_τ φ(t) = φ(t + 2τ) - 2 φ(t + τ) + φ(t)`. For the white and random-walk
  components, the equivalent continuous-time phase and frequency diffusion
  variance rates are `white / 2` and `2 π² * walk` respectively.
* **Link jitter (`JitterNoise`, `HasMoments`).** Each directed link `(i, j)`
  splits its jitter into three mutually uncorrelated stationary components:
  sender-side shared jitter `txCommon i` (common to all links leaving host
  `i`), receiver-side shared jitter `rxCommon j` (common to all links arriving
  at host `j`, such as shared Wi-Fi channel contention), and link-specific
  jitter `own i j`.
* **Audio devices (`devicePhase`, `FollowsNoiseOnGrid`, `WhiteErrors`).** The
  capture device's phase against the sender's clock, and each speaker's
  playback device phase against its host's clock, follow power-law frequency
  noise sampled on the nominal frame grid `k / rate`. Device timestamp errors
  are zero-mean and white across blocks, with per-device variances.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory

/-- Power-law frequency noise of a clock or audio device: the IEEE 1139
one-sided power spectral density of its fractional frequency at `f > 0` Hz is
`white + flicker / f + walk / f²`. -/
structure ClockNoise where
  /-- White frequency noise coefficient `h₀`, in `Hz⁻¹`. The corresponding
  phase diffusion variance rate is `white / 2` (`s² / s`). -/
  white : ℝ
  white_nonneg : 0 ≤ white
  /-- Flicker frequency noise coefficient `h₋₁`, dimensionless. -/
  flicker : ℝ
  flicker_nonneg : 0 ≤ flicker
  /-- Random-walk frequency noise coefficient `h₋₂`, in `Hz`. The
  corresponding fractional-frequency Brownian-motion variance rate is
  `2 π² * walk` (`s⁻¹`). -/
  walk : ℝ
  walk_nonneg : 0 ≤ walk

/-- The one-sided fractional-frequency power spectral density at `f > 0` Hz. -/
def ClockNoise.density (n : ClockNoise) (f : ℝ) : ℝ :=
  n.white + n.flicker / f + n.walk / f ^ 2

/-- Phase diffusion variance rate (in `s`) corresponding to white frequency
noise `h₀`: `Var(φ(t + τ) - φ(t)) = (h₀ / 2) * τ`. -/
def ClockNoise.whiteVarianceRate (n : ClockNoise) : ℝ :=
  n.white / 2

/-- Fractional-frequency random-walk variance rate (in `s⁻¹`) corresponding to
IEEE 1139 coefficient `h₋₂`: `Var(y(t + τ) - y(t)) = 2 π² h₋₂ τ`, matching
Allan variance `σ_y²(τ) = (2 π² / 3) h₋₂ τ`. -/
def ClockNoise.walkVarianceRate (n : ClockNoise) : ℝ :=
  2 * Real.pi ^ 2 * n.walk

/-- Zero frequency noise. -/
def ClockNoise.zero : ClockNoise :=
  ⟨0, le_rfl, 0, le_rfl, 0, le_rfl⟩

theorem ClockNoise.density_nonneg (n : ClockNoise) {f : ℝ} (hf : 0 < f) :
    0 ≤ n.density f := by
  unfold density
  have h1 : 0 ≤ n.flicker / f := div_nonneg n.flicker_nonneg hf.le
  have h2 : 0 ≤ n.walk / f ^ 2 := div_nonneg n.walk_nonneg (sq_nonneg f)
  linarith [n.white_nonneg]

theorem ClockNoise.whiteVarianceRate_nonneg (n : ClockNoise) : 0 ≤ n.whiteVarianceRate := by
  unfold whiteVarianceRate
  linarith [n.white_nonneg]

theorem ClockNoise.walkVarianceRate_nonneg (n : ClockNoise) : 0 ≤ n.walkVarianceRate := by
  unfold walkVarianceRate
  positivity [n.walk_nonneg]

/-- Second difference `Δ²_τ φ(t) = φ(t + 2τ) - 2 φ(t + τ) + φ(t)`. -/
def secondDifference (φ : ℝ → ℝ) (t τ : ℝ) : ℝ :=
  φ (t + 2 * τ) - 2 * φ (t + τ) + φ t

/-- Covariance between two phase second differences `Δ²_{τ₁} φ(t₁)` and
`Δ²_{τ₂} φ(t₂)` for a clock with one-sided fractional-frequency spectral
density `S`. The phase spectral density is `S(f) / (2πf)²`, and each second
difference contributes the frequency response `(e^{2πifτ} - 1)²`. -/
def secondDifferenceCovariance (S : ℝ → ℝ) (t₁ τ₁ t₂ τ₂ : ℝ) : ℝ :=
  ∫ f in Set.Ioi 0, S f / (2 * Real.pi * f) ^ 2 *
    (Complex.exp (2 * Real.pi * f * (t₁ - t₂) * Complex.I)
      * (Complex.exp (2 * Real.pi * f * τ₁ * Complex.I) - 1) ^ 2
      * (starRingEnd ℂ) ((Complex.exp (2 * Real.pi * f * τ₂ * Complex.I) - 1) ^ 2)).re

theorem secondDifferenceCovariance_zero (t₁ τ₁ t₂ τ₂ : ℝ) :
    secondDifferenceCovariance ClockNoise.zero.density t₁ τ₁ t₂ τ₂ = 0 := by
  simp [secondDifferenceCovariance, ClockNoise.density, ClockNoise.zero]

variable {Ω : Type} [MeasurableSpace Ω]

/-- A random clock phase `φ` follows `ClockNoise` `n`: every second difference
has mean zero and covariance `secondDifferenceCovariance n.density`. -/
def FollowsNoise (P : Measure Ω) (φ : Ω → ℝ → ℝ) (n : ClockNoise) : Prop :=
  (∀ t τ, ∫ ω, secondDifference (φ ω) t τ ∂P = 0) ∧
    ∀ t₁ τ₁ t₂ τ₂, ∫ ω, secondDifference (φ ω) t₁ τ₁ * secondDifference (φ ω) t₂ τ₂ ∂P
      = secondDifferenceCovariance n.density t₁ τ₁ t₂ τ₂

/-- Two random phase processes have uncorrelated second differences. -/
def Uncorrelated (P : Measure Ω) (φ ψ : Ω → ℝ → ℝ) : Prop :=
  ∀ t₁ τ₁ t₂ τ₂, ∫ ω, secondDifference (φ ω) t₁ τ₁ * secondDifference (ψ ω) t₂ τ₂ ∂P = 0

/-- Device phase at frame or output sample `k` relative to host clock `C`:
`C(times k) - k / rate`. -/
def devicePhase (C : Clock) (times : ℕ → Time) (rate : ℝ) (k : ℕ) : ℝ :=
  C.read (times k) - k / rate

/-- Second difference `ψ(k + 2j) - 2 ψ(k + j) + ψ(k)` on a discrete grid. -/
def gridDifference (ψ : ℕ → ℝ) (k j : ℕ) : ℝ :=
  ψ (k + 2 * j) - 2 * ψ (k + j) + ψ k

/-- A discrete device phase process `ψ` follows `ClockNoise` `n` on the nominal
grid `k / rate`. -/
def FollowsNoiseOnGrid (P : Measure Ω) (ψ : Ω → ℕ → ℝ) (rate : ℝ) (n : ClockNoise) : Prop :=
  (∀ k j, ∫ ω, gridDifference (ψ ω) k j ∂P = 0) ∧
    ∀ k₁ j₁ k₂ j₂, ∫ ω, gridDifference (ψ ω) k₁ j₁ * gridDifference (ψ ω) k₂ j₂ ∂P
      = secondDifferenceCovariance n.density (k₁ / rate) (j₁ / rate) (k₂ / rate) (j₂ / rate)

/-- A continuous phase process and a discrete device phase process have
uncorrelated second differences. -/
def UncorrelatedGrid (P : Measure Ω) (φ : Ω → ℝ → ℝ) (ψ : Ω → ℕ → ℝ) : Prop :=
  ∀ t τ k j, ∫ ω, secondDifference (φ ω) t τ * gridDifference (ψ ω) k j ∂P = 0

/-- Two discrete device phase processes have uncorrelated second differences. -/
def UncorrelatedGrids (P : Measure Ω) (ψ₁ ψ₂ : Ω → ℕ → ℝ) : Prop :=
  ∀ k₁ j₁ k₂ j₂, ∫ ω, gridDifference (ψ₁ ω) k₁ j₁ * gridDifference (ψ₂ ω) k₂ j₂ ∂P = 0

/-- First and second moments of a stationary jitter process. -/
structure JitterNoise where
  /-- Mean jitter, in seconds. -/
  mean : ℝ
  /-- Covariance of jitter between two messages released `u` seconds apart,
  in `s²`. -/
  covariance : ℝ → ℝ

/-- A random jitter process `x` has mean `n.mean` and lag covariance
`n.covariance`. -/
def HasMoments (P : Measure Ω) (x : Ω → Time → ℝ) (n : JitterNoise) : Prop :=
  (∀ s, ∫ ω, x ω s ∂P = n.mean) ∧
    ∀ s u, ∫ ω, (x ω s - n.mean) * (x ω u - n.mean) ∂P = n.covariance (u - s)

/-- Two random jitter processes have zero cross-covariance at every pair of
release times. -/
def UncorrelatedJitter (P : Measure Ω) (x y : Ω → Time → ℝ) : Prop :=
  ∀ s u, ∫ ω, (x ω s - ∫ ω', x ω' s ∂P) * (y ω u - ∫ ω', y ω' u ∂P) ∂P = 0

/-- A phase process and a jitter process are uncorrelated. -/
def UncorrelatedPhaseJitter (P : Measure Ω) (φ : Ω → ℝ → ℝ) (x : Ω → Time → ℝ) : Prop :=
  ∀ t τ s, ∫ ω, secondDifference (φ ω) t τ * (x ω s - ∫ ω', x ω' s ∂P) ∂P = 0

/-- Capture device timestamp error on block `b`: reported timestamp minus the
sender's clock reading when the block's first frame was captured. -/
def captureError {H : Type} {R : ℕ} (w : World H R) (b : ℕ) : ℝ :=
  w.source.reported b - (w.clock w.sender).read (w.source.capture (w.source.first b))

/-- Playback device timestamp error on speaker `r`, block `b`: reported
timestamp minus the host's clock reading when the block's first output sample
leaves. -/
def playbackError {H : Type} {R : ℕ} (w : World H R) (r : Fin R) (b : ℕ) : ℝ :=
  (w.speaker r).reported b - (w.clock (w.host r)).read ((w.speaker r).out ((w.speaker r).first b))

/-- Timestamp error sequence `e` is zero-mean and white across blocks with
variance `v`. -/
def WhiteErrors (P : Measure Ω) (e : Ω → ℕ → ℝ) (v : ℝ) : Prop :=
  (∀ b, ∫ ω, e ω b ∂P = 0) ∧
    ∀ b b', ∫ ω, e ω b * e ω b' ∂P = if b = b' then v else 0

/-- Two zero-mean timestamp error sequences are uncorrelated across all pairs
of blocks. -/
def UncorrelatedErrors (P : Measure Ω) (e₁ e₂ : Ω → ℕ → ℝ) : Prop :=
  ∀ b₁ b₂, ∫ ω, e₁ ω b₁ * e₂ ω b₂ ∂P = 0

/-- Parameters of the second-order noise model for hosts `H` and `R` speakers. -/
structure SecondOrderModel (H : Type) (R : ℕ) where
  /-- Common nominal sample rate of all realizations, in frames per second. -/
  rate : ℝ
  rate_pos : 0 < rate
  /-- Frequency noise of each host's clock relative to true time. -/
  clock : H → ClockNoise
  /-- Shared outgoing jitter for all links leaving host `i`. -/
  txJitter : H → JitterNoise
  /-- Shared incoming jitter for all links arriving at host `j` (for example,
  shared wireless channel contention). -/
  rxJitter : H → JitterNoise
  /-- Link-specific jitter for each directed link `(i, j)`. -/
  ownJitter : H → H → JitterNoise
  /-- Frequency noise of the capture device relative to the sender's clock. -/
  capture : ClockNoise
  /-- Frequency noise of each speaker's playback device relative to its host's
  clock. -/
  playback : Fin R → ClockNoise
  /-- Variance of the capture device's white timestamp errors, in `s²`. -/
  captureTimestampVariance : ℝ
  captureTimestampVariance_nonneg : 0 ≤ captureTimestampVariance
  /-- Variance of each speaker's white timestamp errors, in `s²`. -/
  playbackTimestampVariance : Fin R → ℝ
  playbackTimestampVariance_nonneg : ∀ r, 0 ≤ playbackTimestampVariance r

/-- A random world `world` under probability measure `P`, with links `d`,
satisfies the second-order noise model `m`:

* Every host clock follows `m.clock i`, and distinct host clocks have
  uncorrelated second differences.
* Every link's jitter decomposes into `txCommon i + rxCommon j + own i j`,
  with the specified stationary means and covariances and all distinct
  components mutually uncorrelated.
* The capture device and each playback device share a deterministic nominal
  rate `rate`, follow their grid noise spectra relative to their host clocks,
  and are uncorrelated with host clocks and with each other.
* Clock phases and link jitters are uncorrelated.
* Capture and playback timestamp errors are white with their per-device
  variances and mutually uncorrelated across devices.

Network pauses, outages, and packet drops are not constrained here; combine
this structure with `DelayModel.Holds` when modeling losses and pauses. -/
structure SecondOrderModel.Holds {H : Type} {R : ℕ} (m : SecondOrderModel H R)
    (P : Measure Ω) (world : Ω → World H R) (d : Ω → H → H → Link) : Prop where
  /-- Each realization's network is given by the links `d ω`. -/
  network : ∀ ω, (world ω).HasDelays (d ω)
  /-- All realizations share the model's nominal sample rate `m.rate`. -/
  rate_eq : ∀ ω, (world ω).rate = m.rate
  /-- Every host clock follows its power-law noise spectrum. -/
  clocks : ∀ i, FollowsNoise P (fun ω t => ((world ω).clock i).read t - t) (m.clock i)
  /-- Distinct hosts have uncorrelated clock phases. -/
  clocks_uncorrelated : ∀ i j, i ≠ j →
    Uncorrelated P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω t => ((world ω).clock j).read t - t)
  /-- Link jitter splits into mutually uncorrelated sender-common,
  receiver-common, and link-specific stationary components, all uncorrelated
  with host clocks. -/
  jitter : ∃ tx : Ω → H → Time → ℝ, ∃ rx : Ω → H → Time → ℝ,
      ∃ own : Ω → H → H → Time → ℝ,
    (∀ ω i j u, (d ω i j).jitter u = tx ω i u + rx ω j u + own ω i j u)
      ∧ (∀ i, HasMoments P (fun ω => tx ω i) (m.txJitter i))
      ∧ (∀ j, HasMoments P (fun ω => rx ω j) (m.rxJitter j))
      ∧ (∀ i j, HasMoments P (fun ω => own ω i j) (m.ownJitter i j))
      ∧ (∀ i i', i ≠ i' → UncorrelatedJitter P (fun ω => tx ω i) (fun ω => tx ω i'))
      ∧ (∀ j j', j ≠ j' → UncorrelatedJitter P (fun ω => rx ω j) (fun ω => rx ω j'))
      ∧ (∀ i j, UncorrelatedJitter P (fun ω => tx ω i) (fun ω => rx ω j))
      ∧ (∀ i j i', UncorrelatedJitter P (fun ω => own ω i j) (fun ω => tx ω i'))
      ∧ (∀ i j j', UncorrelatedJitter P (fun ω => own ω i j) (fun ω => rx ω j'))
      ∧ (∀ i j i' j', (i, j) ≠ (i', j') →
          UncorrelatedJitter P (fun ω => own ω i j) (fun ω => own ω i' j'))
      ∧ (∀ h i, UncorrelatedPhaseJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => tx ω i))
      ∧ (∀ h j, UncorrelatedPhaseJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => rx ω j))
      ∧ (∀ h i j, UncorrelatedPhaseJitter P (fun ω t => ((world ω).clock h).read t - t)
          (fun ω => own ω i j))
  /-- The capture device follows its power-law noise against the sender's clock. -/
  capture : FollowsNoiseOnGrid P
    (fun ω => devicePhase ((world ω).clock (world ω).sender) (world ω).source.capture m.rate)
    m.rate m.capture
  /-- Each playback device follows its power-law noise against its host's clock. -/
  playback : ∀ r, FollowsNoiseOnGrid P
    (fun ω => devicePhase ((world ω).clock ((world ω).host r)) ((world ω).speaker r).out m.rate)
    m.rate (m.playback r)
  /-- Device phases are uncorrelated with host clocks and with each other. -/
  capture_clock_uncorrelated : ∀ i,
    UncorrelatedGrid P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω => devicePhase ((world ω).clock (world ω).sender) (world ω).source.capture m.rate)
  playback_clock_uncorrelated : ∀ i r,
    UncorrelatedGrid P (fun ω t => ((world ω).clock i).read t - t)
      (fun ω => devicePhase ((world ω).clock ((world ω).host r)) ((world ω).speaker r).out m.rate)
  capture_playback_uncorrelated : ∀ r,
    UncorrelatedGrids P
      (fun ω => devicePhase ((world ω).clock (world ω).sender) (world ω).source.capture m.rate)
      (fun ω => devicePhase ((world ω).clock ((world ω).host r)) ((world ω).speaker r).out m.rate)
  playback_uncorrelated : ∀ r r', r ≠ r' →
    UncorrelatedGrids P
      (fun ω => devicePhase ((world ω).clock ((world ω).host r)) ((world ω).speaker r).out m.rate)
      (fun ω => devicePhase ((world ω).clock ((world ω).host r')) ((world ω).speaker r').out m.rate)
  /-- Capture timestamp errors are white with `m.captureTimestampVariance`. -/
  capture_timestamps : WhiteErrors P (fun ω => captureError (world ω)) m.captureTimestampVariance
  /-- Playback timestamp errors are white with `m.playbackTimestampVariance r`. -/
  playback_timestamps : ∀ r,
    WhiteErrors P (fun ω => playbackError (world ω) r) (m.playbackTimestampVariance r)
  /-- Timestamp errors are uncorrelated across capture and playback devices. -/
  capture_playback_timestamps_uncorrelated : ∀ r,
    UncorrelatedErrors P (fun ω => captureError (world ω)) (fun ω => playbackError (world ω) r)
  playback_timestamps_uncorrelated : ∀ r r', r ≠ r' →
    UncorrelatedErrors P (fun ω => playbackError (world ω) r) (fun ω => playbackError (world ω) r')

end Unisono.Spec
