/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ProposedWorld
public import Unisono.Spec.Models.GenerativePauses
public import Unisono.Spec.Models.ClockAdvance

/-!
# The world of a draw of the proposed model

A draw of `Unisono.Spec.ProposedWorld` from which a world can be built
(`Draw.Regular`), and that world (`drawWorld`, `drawWorld_builds`).

A draw is regular when its splits lie between zero and one, the wander of
its clocks is continuous, every clock advances without bound in both
directions of time, its jitter is never negative, and the paused times of
its links and hosts never decrease and leave a finite backlog. In the world
of a regular draw:

* the clock of a host reads what the draw says (`Draw.reading`);
* the capture device starts when the sender's clock reads the member's
  start, and frame `n` is captured when the device's own clock has advanced
  by `n / rate` since (`Draw.captureAt`); a playback device does the same
  for its output samples (`Draw.outAt`), and requests each block the request
  lead, on its own clock, before the block's first output sample
  (`Draw.requestAt`);
* a host handles the handovers and the requests of its audio devices after
  the backlog of its pauses;
* the network drops the messages that the draw loses, hands every other
  message to the program of the receiving host at `Draw.observed`, and the
  kernel stamps it at `Draw.reaches`.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open MeasureTheory Filter Topology
open GenerativeWorld (backlog handledAt Tame)

variable {H : Type} {R : ℕ}

namespace Draw

variable (d : Draw H R) (f : Member H R)

/-- The logarithm of the rate of the clock of host `h` at each true time. -/
def logRateAt (h : H) (x : Time) : ℝ :=
  d.logRate h + ∑ k ∈ Finset.range f.scales, d.wander h k x

/-- The logarithm of the rate of the clock of the audio device `x` at each
true time. -/
def deviceLogRateAt (x : Option (Fin R)) (y : Time) : ℝ :=
  d.deviceLogRate x + ∑ k ∈ Finset.range f.scales, d.deviceWander x k y

theorem reading_eq (h : H) (t : Time) :
    d.reading f h t = d.offset h + clockAdvance (d.logRateAt f h) t := rfl

theorem deviceReading_eq (x : Option (Fin R)) (t : Time) :
    d.deviceReading f x t = clockAdvance (d.deviceLogRateAt f x) t := rfl

/-- **A draw from which a world can be built.** -/
structure Regular : Prop where
  split_mem : ∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1
  wander_continuous : ∀ h k, Continuous (d.wander h k)
  deviceWander_continuous : ∀ x k, Continuous (d.deviceWander x k)
  /-- The clock of every host advances without bound toward later times. -/
  clock_top : ∀ h, Tendsto (clockAdvance (d.logRateAt f h)) atTop atTop
  /-- The clock of every host advances without bound toward earlier
  times. -/
  clock_bot : ∀ h, Tendsto (clockAdvance (d.logRateAt f h)) atBot atBot
  device_top : ∀ x, Tendsto (clockAdvance (d.deviceLogRateAt f x)) atTop atTop
  device_bot : ∀ x, Tendsto (clockAdvance (d.deviceLogRateAt f x)) atBot atBot
  jitter_nonneg : ∀ i j n, 0 ≤ d.jitterLevel i j n
  linkPaused_monotone : ∀ i j, Monotone (d.linkPaused i j)
  linkPaused_tame : ∀ i j, Tame (d.linkPaused i j)
  hostPaused_monotone : ∀ h, Monotone (d.hostPaused h)
  hostPaused_tame : ∀ h, Tame (d.hostPaused h)

/-- The true time at which the clock of host `h` reads `c`. -/
def timeOf (h : H) (c : ℝ) : Time := clockAdvanceTime (d.logRateAt f h) (c - d.offset h)

/-- The true time at which the clock of the audio device `x` has advanced by
`a` since the true time `t₀`. -/
def deviceTime (x : Option (Fin R)) (t₀ : Time) (a : ℝ) : Time :=
  clockAdvanceTime (d.deviceLogRateAt f x) (clockAdvance (d.deviceLogRateAt f x) t₀ + a)

/-- When frame `n` is captured: when the capture device's clock has advanced
by `n / rate` since the sender's clock read the member's start. -/
def captureAt (m : Told H R) (n : ℕ) : Time :=
  d.deviceTime f none (d.timeOf f m.sender f.captureStart) ((n : ℝ) / m.rate)

/-- When output sample `k` of speaker `r` leaves. -/
def outAt (m : Told H R) (r : Fin R) (k : ℕ) : Time :=
  d.deviceTime f (some (m.device r))
    (d.timeOf f (m.host r) (f.speakerStart (m.device r))) ((k : ℝ) / m.rate)

/-- When the device of speaker `r` requests block `b`: the request lead, on
its own clock, before the block's first output sample leaves. -/
def requestAt (m : Told H R) (r : Fin R) (b : ℕ) : Time :=
  d.deviceTime f (some (m.device r))
    (d.timeOf f (m.host r) (f.speakerStart (m.device r)))
    (((b * m.blockSize : ℕ) : ℝ) / m.rate - m.lead)

variable {d f}

namespace Regular

variable (hd : d.Regular f)
include hd

theorem clock_continuous (h : H) : Continuous (d.logRateAt f h) :=
  continuous_const.add (continuous_finsetSum _ fun k _ => hd.wander_continuous h k)

theorem device_continuous (x : Option (Fin R)) :
    Continuous (d.deviceLogRateAt f x) :=
  continuous_const.add (continuous_finsetSum _ fun k _ => hd.deviceWander_continuous x k)

theorem clock_surjective (h : H) : Function.Surjective (clockAdvance (d.logRateAt f h)) :=
  clockAdvance_surjective (hd.clock_continuous h) (hd.clock_top h) (hd.clock_bot h)

theorem device_surjective (x : Option (Fin R)) :
    Function.Surjective (clockAdvance (d.deviceLogRateAt f x)) :=
  clockAdvance_surjective (hd.device_continuous x) (hd.device_top x) (hd.device_bot x)

/-- The clock of a host reads `c` at the true time `timeOf c`. -/
theorem reading_timeOf (h : H) (c : ℝ) : d.reading f h (d.timeOf f h c) = c := by
  rw [reading_eq, timeOf, clockAdvance_clockAdvanceTime (hd.clock_surjective h)]
  ring

theorem reading_deviceTime (x : Option (Fin R)) (t₀ : Time) (a : ℝ) :
    d.deviceReading f x (d.deviceTime f x t₀ a) = d.deviceReading f x t₀ + a := by
  rw [deviceReading_eq, deviceReading_eq, deviceTime,
    clockAdvance_clockAdvanceTime (hd.device_surjective x)]

theorem deviceTime_zero (x : Option (Fin R)) (t₀ : Time) : d.deviceTime f x t₀ 0 = t₀ := by
  rw [deviceTime, add_zero, clockAdvanceTime_clockAdvance (hd.device_continuous x)]

theorem deviceTime_strict (x : Option (Fin R)) (t₀ : Time) :
    StrictMono (d.deviceTime f x t₀) := fun a b hab =>
  clockAdvanceTime_strictMono (hd.device_continuous x) (hd.device_surjective x)
    (by linarith)

theorem hostBacklog_nonneg (h : H) (t : Time) : 0 ≤ backlog (d.hostPaused h) t :=
  (GenerativeWorld.isBacklog_backlog (hd.hostPaused_tame h) (hd.hostPaused_monotone h) t).nonneg

theorem linkBacklog_nonneg (i j : H) (t : Time) : 0 ≤ backlog (d.linkPaused i j) t :=
  (GenerativeWorld.isBacklog_backlog (hd.linkPaused_tame i j)
    (hd.linkPaused_monotone i j) t).nonneg

/-- A message reaches the receiving host after it is sent. -/
theorem lt_reaches (i j : H) (s : Time) : s < d.reaches f i j s := by
  have h1 := hd.hostBacklog_nonneg i s
  have h2 := hd.linkBacklog_nonneg i j (d.leaves i s)
  have h3 : 0 < d.split i j * f.roundTrip i j :=
    mul_pos (hd.split_mem i j).1 (f.roundTrip_pos i j)
  have h4 : 0 ≤ d.jitter i j (d.released i j s) := hd.jitter_nonneg i j _
  unfold reaches released leaves at *
  linarith

/-- The program of the receiving host handles a message when it reaches the
host, or later. -/
theorem reaches_le_observed (i j : H) (s : Time) : d.reaches f i j s ≤ d.observed f i j s := by
  have := hd.hostBacklog_nonneg j (d.reaches f i j s)
  unfold observed
  linarith

theorem reach_mem (i j : H) (s : Time) (q : ℕ) (a : Time)
    (h : d.delivery f i j s q = some a) :
    s < d.reaches f i j s ∧ d.reaches f i j s ≤ a := by
  classical
  unfold delivery at h
  split_ifs at h with hl
  have ha : d.observed f i j s = a := Option.some.inj h
  rw [← ha]
  exact ⟨hd.lt_reaches i j s, hd.reaches_le_observed i j s⟩

end Regular

end Draw

/-- **The world of a regular draw.** -/
def drawWorld (m : Told H R) (f : Member H R) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h)
    (d : Draw H R) (hd : d.Regular f) : World H R where
  rate := m.rate
  rate_pos := m.rate_pos
  sender := m.sender
  host := m.host
  hosts := hex
  clock := fun h =>
    { read := d.reading f h
      strictMono := fun a b hab => by
        have := clockAdvance_strictMono (hd.clock_continuous h) hab
        rw [Draw.reading_eq, Draw.reading_eq]
        linarith
      continuous :=
        continuous_const.add (continuous_clockAdvance (hd.clock_continuous h)) }
  source :=
    { capture := d.captureAt f m
      capture_strictMono := fun a b hab =>
        hd.deviceTime_strict none _
          (div_lt_div_of_pos_right (Nat.cast_lt.mpr hab) m.rate_pos)
      first := fun b => b * m.blockSize
      first_zero := Nat.zero_mul _
      first_strictMono := fun _ _ hab => Nat.mul_lt_mul_of_pos_right hab m.blockSize_pos
      handed := fun b =>
        handledAt (d.hostPaused m.sender) (d.captureAt f m ((b + 1) * m.blockSize - 1))
      handed_mono := fun a b hab => by
        refine GenerativeWorld.handledAt_mono (hd.hostPaused_tame _)
          (hd.hostPaused_monotone _) ?_
        have hle : (a + 1) * m.blockSize - 1 ≤ (b + 1) * m.blockSize - 1 :=
          Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (Nat.succ_le_succ hab)) 1
        exact (hd.deviceTime_strict none _).monotone
          (div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) m.rate_pos.le)
      handed_after := fun _ =>
        GenerativeWorld.le_handledAt (hd.hostPaused_tame _) (hd.hostPaused_monotone _) _
      reported := fun b =>
        d.reading f m.sender (d.captureAt f m (b * m.blockSize))
          + d.reportError none (d.captureAt f m (b * m.blockSize)) }
  speaker := fun r =>
    { out := d.outAt f m r
      out_strictMono := fun a b hab =>
        hd.deviceTime_strict _ _
          (div_lt_div_of_pos_right (Nat.cast_lt.mpr hab) m.rate_pos)
      first := fun b => b * m.blockSize
      first_zero := Nat.zero_mul _
      first_strictMono := fun _ _ hab => Nat.mul_lt_mul_of_pos_right hab m.blockSize_pos
      asked := fun b => handledAt (d.hostPaused (m.host r)) (d.requestAt f m r b)
      asked_mono := fun a b hab => by
        refine GenerativeWorld.handledAt_mono (hd.hostPaused_tame _)
          (hd.hostPaused_monotone _) ?_
        have hle : a * m.blockSize ≤ b * m.blockSize := Nat.mul_le_mul_right _ hab
        have h1 : ((a * m.blockSize : ℕ) : ℝ) / m.rate
            ≤ ((b * m.blockSize : ℕ) : ℝ) / m.rate :=
          div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) m.rate_pos.le
        exact (hd.deviceTime_strict _ _).monotone (by linarith)
      reported := fun b =>
        d.reading f (m.host r) (d.outAt f m r (b * m.blockSize))
          + d.reportError (some (m.device r)) (d.outAt f m r (b * m.blockSize)) }
  network :=
    { deliver := d.delivery f
      reach := fun i j s _ => d.reaches f i j s
      reach_mem := hd.reach_mem }
  target := fun _ => m.targetLatency

/-- **The world of a regular draw is the world built from the draw.** -/
theorem drawWorld_builds (m : Told H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (d : Draw H R) (hd : d.Regular f) :
    Builds m f d (drawWorld m f hex d hd) where
  rate_eq := rfl
  sender_eq := rfl
  host_eq := rfl
  clock := fun _ _ => rfl
  capture_start := by
    show d.reading f m.sender (d.captureAt f m 0) = f.captureStart
    unfold Draw.captureAt
    rw [Nat.cast_zero, zero_div, hd.deviceTime_zero, hd.reading_timeOf]
  capture := fun n => by
    show d.deviceReading f none (d.captureAt f m n) - d.deviceReading f none (d.captureAt f m 0)
      = (n : ℝ) / m.rate
    unfold Draw.captureAt
    rw [hd.reading_deviceTime, hd.reading_deviceTime, Nat.cast_zero, zero_div]
    ring
  capture_first := fun _ => rfl
  capture_handed := fun _ => rfl
  capture_reported := fun _ => rfl
  speaker_start := fun r => by
    show d.reading f (m.host r) (d.outAt f m r 0) = f.speakerStart (m.device r)
    unfold Draw.outAt
    rw [Nat.cast_zero, zero_div, hd.deviceTime_zero, hd.reading_timeOf]
  speaker_out := fun r k => by
    show d.deviceReading f (some (m.device r)) (d.outAt f m r k)
        - d.deviceReading f (some (m.device r)) (d.outAt f m r 0) = (k : ℝ) / m.rate
    unfold Draw.outAt
    rw [hd.reading_deviceTime, hd.reading_deviceTime, Nat.cast_zero, zero_div]
    ring
  speaker_first := fun _ _ => rfl
  speaker_asked := fun r b => by
    refine ⟨d.requestAt f m r b, ?_, rfl⟩
    show d.deviceReading f (some (m.device r)) (d.outAt f m r (b * m.blockSize))
        - d.deviceReading f (some (m.device r)) (d.requestAt f m r b) = m.lead
    unfold Draw.outAt Draw.requestAt
    rw [hd.reading_deviceTime, hd.reading_deviceTime]
    ring
  speaker_reported := fun _ _ => rfl
  target_eq := fun _ => rfl
  deliver := fun _ _ _ _ => rfl
  reach := fun _ _ _ _ => rfl

end Unisono.Spec.ProposedWorld
