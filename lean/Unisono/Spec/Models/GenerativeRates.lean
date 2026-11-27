/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.Bounded
public import Unisono.Spec.Models.GenerativeDelivery
public import Unisono.Spec.Models.GenerativeNoiseless

/-!
# Worlds whose clocks run at constant rates

A world built from a draw of the generative model in which no clock wanders,
of a host or of an audio device, the audio devices report exact timestamps,
and no host pauses (`ConstantRates`). The clocks of the hosts and of the
audio devices may all run at different rates, and links may pause. A host
that pauses handles the events of its audio devices late; such worlds are
not covered here. In such a world

* the clock of host `h` reads its offset plus its rate times true time
  (`ConstantRates.clock`), where the rate is the exponential of the
  draw's `logRate h`, and the clock of the audio device `x` advances by its
  rate times true time (`ConstantRates.deviceReading`);
* the capture device and the playback devices run at the rates of their own
  clocks (`ConstantRates.capture`, `ConstantRates.handed`,
  `ConstantRates.out`, `ConstantRates.asked`), without end
  (`ConstantRates.handed_unbounded`,
  `ConstantRates.asked_unbounded`), and the capture time of a position
  is linear in the position (`ConstantRates.captured`);
* the timestamp of a block is a line in the number of the block's first
  frame or output sample, whose slope is the rate of the host's clock divided
  by the nominal rate and by the rate of the device's clock
  (`ConstantRates.capture_reported`,
  `ConstantRates.speaker_reported`);
* a message sent later on a link arrives no earlier
  (`ConstantRates.arrival_mono`).

When moreover nothing pauses (`ConstantDelays`), every message from `i` to `j`
takes the least delay of the direction (`ConstantDelays.deliver`). When every
rate is then within `ε < 1 / 2` of one, the world satisfies the bounds
`rateBounds` (`ConstantDelays.withinBounds`), so the theorems about bounded
worlds apply to it. A world with pauses satisfies no such bounds: its delays
have no upper bound.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R}

/-- The world `w` is built from the draw `d`, and in the draw no clock
wanders, the audio devices report exact timestamps and no host pauses: the
clocks of the hosts and of the audio devices run at constant rates, each its
own, and every host handles the events of its audio devices when they
occur. Links may pause, and the paused time of a link that has begun never
decreases. -/
structure ConstantRates (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R)
    (w : World H R) : Prop where
  builds : m.Builds f d w
  no_wander : ∀ h t, d.wander h t = 0
  no_deviceWander : ∀ x t, d.deviceWander x t = 0
  no_reportError : ∀ x t, d.reportError x t = 0
  delay_pos : ∀ i j, 0 < d.split i j * f.roundTrip i j
  linkPaused_monotone : ∀ i j, Monotone (d.linkPaused i j)
  no_hostPauses : ∀ h s t, d.hostPaused h s = d.hostPaused h t

/-- The world `w` is built from the draw `d`, and in the draw no clock
wanders, nothing pauses and the audio devices report exact timestamps: the
clocks of the hosts and of the audio devices run at constant rates, and the
links have constant delays. -/
structure ConstantDelays (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R)
    (w : World H R) : Prop where
  builds : m.Builds f d w
  no_wander : ∀ h t, d.wander h t = 0
  no_deviceWander : ∀ x t, d.deviceWander x t = 0
  no_reportError : ∀ x t, d.reportError x t = 0
  no_linkPauses : ∀ i j s t, d.linkPaused i j s = d.linkPaused i j t
  no_hostPauses : ∀ h s t, d.hostPaused h s = d.hostPaused h t
  delay_pos : ∀ i j, 0 < d.split i j * f.roundTrip i j

namespace ConstantRates

/-- The paused time of a host that has begun never decreases: there is
none. -/
theorem hostPaused_mono (hS : ConstantRates m f d w) (h : H) : Monotone (d.hostPaused h) :=
  fun s t _ => (hS.no_hostPauses h s t).le

/-- Each clock reads its offset plus its rate times true time. -/
theorem clock (hS : ConstantRates m f d w) (h : H) (t : Time) :
    (w.clock h).read t = d.offset h + Real.exp (d.logRate h) * t := by
  rw [hS.builds.clock h t]
  unfold Draw.reading
  simp only [hS.no_wander, add_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

/-- The clock of each audio device advances by its rate times true time. -/
theorem deviceReading (hS : ConstantRates m f d w) (x : Option (Fin R)) (t : Time) :
    d.deviceReading x t = Real.exp (d.deviceLogRate x) * t := by
  unfold Draw.deviceReading
  simp only [hS.no_deviceWander, add_zero, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]
  ring

/-- When each frame is captured: the capture device starts when the sender's
clock reads the member's start, and then counts its frames on its own
clock. -/
theorem capture (hS : ConstantRates m f d w) (n : ℕ) :
    w.source.capture n
      = (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender)
        + (n : ℝ) / (m.rate * Real.exp (d.deviceLogRate none)) := by
  have hr := Real.exp_pos (d.logRate m.sender)
  have hg := Real.exp_pos (d.deviceLogRate none)
  have hρ := m.rate_pos
  have h0 := hS.builds.capture_start
  rw [hS.builds.sender_eq, hS.clock] at h0
  have e0 : w.source.capture 0
      = (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender) := by
    rw [eq_div_iff hr.ne']
    linarith
  have h := hS.builds.capture n
  rw [hS.deviceReading, hS.deviceReading, eq_div_iff hρ.ne'] at h
  have e1 : w.source.capture n - w.source.capture 0
      = (n : ℝ) / (m.rate * Real.exp (d.deviceLogRate none)) := by
    rw [eq_div_iff (mul_pos hρ hg).ne']
    linarith
  linarith

/-- The timestamp of a capture block is a line in the number of its first
frame. -/
theorem capture_reported (hS : ConstantRates m f d w) (b : ℕ) :
    w.source.reported b
      = f.captureStart + Real.exp (d.logRate m.sender)
          / (m.rate * Real.exp (d.deviceLogRate none)) * (w.source.first b : ℝ) := by
  have hr := (Real.exp_pos (d.logRate m.sender)).ne'
  have hg := (Real.exp_pos (d.deviceLogRate none)).ne'
  have hρ := m.rate_pos.ne'
  rw [hS.builds.capture_reported, hS.no_reportError, add_zero, hS.builds.sender_eq, hS.clock,
    hS.capture]
  field_simp
  ring

/-- When each output sample leaves: the playback device starts when the
clock of its host reads the member's start, and then counts its output
samples on its own clock. -/
theorem out (hS : ConstantRates m f d w) (r : Fin R) (k : ℕ) :
    (w.speaker r).out k
      = (f.speakerStart (m.device r) - d.offset (m.host r)) / Real.exp (d.logRate (m.host r))
        + (k : ℝ) / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := by
  have hr := Real.exp_pos (d.logRate (m.host r))
  have hg := Real.exp_pos (d.deviceLogRate (some (m.device r)))
  have hρ := m.rate_pos
  have h0 := hS.builds.speaker_start r
  rw [hS.builds.host_eq, hS.clock] at h0
  have e0 : (w.speaker r).out 0
      = (f.speakerStart (m.device r) - d.offset (m.host r))
        / Real.exp (d.logRate (m.host r)) := by
    rw [eq_div_iff hr.ne']
    linarith
  have h := hS.builds.speaker_out r k
  rw [hS.deviceReading, hS.deviceReading, eq_div_iff hρ.ne'] at h
  have e1 : (w.speaker r).out k - (w.speaker r).out 0
      = (k : ℝ) / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := by
    rw [eq_div_iff (mul_pos hρ hg).ne']
    linarith
  linarith

/-- The timestamp of a playback block is a line in the number of its first
output sample. -/
theorem speaker_reported (hS : ConstantRates m f d w) (r : Fin R) (b : ℕ) :
    (w.speaker r).reported b
      = f.speakerStart (m.device r) + Real.exp (d.logRate (m.host r))
          / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          * ((w.speaker r).first b : ℝ) := by
  have hr := (Real.exp_pos (d.logRate (m.host r))).ne'
  have hg := (Real.exp_pos (d.deviceLogRate (some (m.device r)))).ne'
  have hρ := m.rate_pos.ne'
  rw [hS.builds.speaker_reported, hS.no_reportError, add_zero, hS.builds.host_eq, hS.clock,
    hS.out]
  field_simp
  ring

/-- A playback device requests a block the request lead, divided by the rate
of the device's clock, before the block's first output sample leaves. -/
theorem asked (hS : ConstantRates m f d w) (r : Fin R) (b : ℕ) :
    (w.speaker r).out ((w.speaker r).first b) - (w.speaker r).asked b
      = m.lead / Real.exp (d.deviceLogRate (some (m.device r))) := by
  have hg := Real.exp_pos (d.deviceLogRate (some (m.device r)))
  have h := hS.builds.asked_of_const (r := r) (hS.no_hostPauses _) b
  rw [hS.deviceReading, hS.deviceReading] at h
  rw [eq_div_iff hg.ne']
  linarith

/-- The host of a speaker handles the request of every block before the
block's first output sample leaves. -/
theorem asked_lt_out (hS : ConstantRates m f d w) (r : Fin R) (b : ℕ) :
    (w.speaker r).asked b < (w.speaker r).out ((w.speaker r).first b) := by
  have h := hS.asked r b
  have hpos := div_pos m.lead_pos (Real.exp_pos (d.deviceLogRate (some (m.device r))))
  linarith

/-- The host of a speaker handles the request of every block before any
output sample of the block leaves. -/
theorem asked_lt_of_le (hS : ConstantRates m f d w) {r : Fin R} {b k : ℕ}
    (hk : (w.speaker r).first b ≤ k) : (w.speaker r).asked b < (w.speaker r).out k :=
  lt_of_lt_of_le (hS.asked_lt_out r b) ((w.speaker r).out_strictMono.monotone hk)

/-- The capture time of a position is linear in the position. -/
theorem captured (hS : ConstantRates m f d w) (x : ℝ) :
    w.captured x
      = (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender)
        + x / (m.rate * Real.exp (d.deviceLogRate none)) := by
  have hρ := m.rate_pos.ne'
  have hr := (Real.exp_pos (d.logRate m.sender)).ne'
  have hg := (Real.exp_pos (d.deviceLogRate none)).ne'
  unfold World.captured
  rw [hS.capture, hS.capture]
  push_cast
  field_simp
  ring

/-- When each capture block is handed over: when its last frame is
captured. -/
theorem handed (hS : ConstantRates m f d w) (b : ℕ) :
    w.source.handed b
      = (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender)
        + (((b : ℝ) + 1) * m.blockSize - 1) / (m.rate * Real.exp (d.deviceLogRate none)) := by
  have hB : 1 ≤ (b + 1) * m.blockSize :=
    Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos b) m.blockSize_pos)
  have e : (((b + 1) * m.blockSize - 1 : ℕ) : ℝ) = ((b : ℝ) + 1) * m.blockSize - 1 := by
    rw [Nat.cast_sub hB]
    simp
  rw [hS.builds.handed_of_const (hS.no_hostPauses _), hS.builds.capture_first, hS.capture, e]

/-- **The capture device hands over blocks without end.** -/
theorem handed_unbounded (hS : ConstantRates m f d w) (T : Time) :
    ∃ b, T < w.source.handed b := by
  have hc : 0 < m.rate * Real.exp (d.deviceLogRate none) :=
    mul_pos m.rate_pos (Real.exp_pos _)
  obtain ⟨b, hb⟩ := exists_nat_gt
    ((T - (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender))
      * (m.rate * Real.exp (d.deviceLogRate none)))
  refine ⟨b, ?_⟩
  rw [hS.handed]
  have hB : (1 : ℝ) ≤ m.blockSize := by exact_mod_cast m.blockSize_pos
  have hb0 : (0 : ℝ) ≤ (b : ℝ) + 1 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hB hb0
  have h2 : T - (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender)
      < (((b : ℝ) + 1) * m.blockSize - 1) / (m.rate * Real.exp (d.deviceLogRate none)) := by
    rw [lt_div_iff₀ hc]
    linarith
  linarith

/-- **Every playback device requests blocks without end.** -/
theorem asked_unbounded (hS : ConstantRates m f d w) (r : Fin R) (T : Time) :
    ∃ b, T < (w.speaker r).asked b := by
  have hc : 0 < m.rate * Real.exp (d.deviceLogRate (some (m.device r))) :=
    mul_pos m.rate_pos (Real.exp_pos _)
  obtain ⟨b, hb⟩ := exists_nat_gt
    ((T + m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
        - (f.speakerStart (m.device r) - d.offset (m.host r))
          / Real.exp (d.logRate (m.host r)))
      * (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))))
  refine ⟨b, ?_⟩
  have ha := hS.asked r b
  rw [hS.builds.speaker_first, hS.out] at ha
  have hB : (1 : ℝ) ≤ m.blockSize := by exact_mod_cast m.blockSize_pos
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have h1 := mul_le_mul_of_nonneg_left hB hb0
  have e : ((b * m.blockSize : ℕ) : ℝ) = (b : ℝ) * m.blockSize := by push_cast; ring
  rw [e] at ha
  have h2 : T + m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
        - (f.speakerStart (m.device r) - d.offset (m.host r))
          / Real.exp (d.logRate (m.host r))
      < (b : ℝ) * m.blockSize / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := by
    rw [lt_div_iff₀ hc]
    linarith
  linarith

/-- **Messages do not overtake one another**: a message sent later from `i`
to `j` arrives no earlier. -/
theorem arrival_mono (hS : ConstantRates m f d w) (i j : H) :
    Monotone (d.arrival f i j) :=
  hS.builds.arrival_mono (hS.linkPaused_monotone i j) (hS.hostPaused_mono i)
    (hS.hostPaused_mono j)

end ConstantRates

namespace ConstantDelays

/-- A world with constant rates and constant delays is a world whose clocks
run at constant rates. -/
theorem toConstantRates (hS : ConstantDelays m f d w) : ConstantRates m f d w where
  builds := hS.builds
  no_wander := hS.no_wander
  no_deviceWander := hS.no_deviceWander
  no_reportError := hS.no_reportError
  delay_pos := hS.delay_pos
  linkPaused_monotone := fun i j s t _ => (hS.no_linkPauses i j s t).le
  no_hostPauses := hS.no_hostPauses

/-- Every message takes the least delay of its direction. -/
theorem deliver (hS : ConstantDelays m f d w) (i j : H) (s : Time) (q : ℕ) :
    w.network.deliver i j s q = some (s + d.split i j * f.roundTrip i j) := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, hd, -⟩ := hS.builds.network i j s q
  have h₁ : v₁ = 0 := hv₁.unique (isBacklog_zero_of_const (hS.no_hostPauses i) s)
  have h₂ : v₂ = 0 := hv₂.unique (isBacklog_zero_of_const (hS.no_linkPauses i j) _)
  have h₃ : v₃ = 0 := hv₃.unique (isBacklog_zero_of_const (hS.no_hostPauses j) _)
  rw [hd, h₁, h₂, h₃]
  simp only [add_zero]

/-- Every message arrives the least delay of its direction after it is
sent. -/
theorem arrival (hS : ConstantDelays m f d w) (i j : H) (s : Time) :
    d.arrival f i j s = s + d.split i j * f.roundTrip i j := by
  have h := hS.builds.deliver i j s 0
  rw [hS.deliver] at h
  exact (Option.some.inj h).symm

end ConstantDelays

/-- A rate within `ε < 1` of one has an inverse within `ε / (1 - ε)` of
one. -/
theorem abs_inv_sub_one_le {r ε : ℝ} (hr : |r - 1| ≤ ε) (hε : ε < 1) :
    |1 / r - 1| ≤ ε / (1 - ε) := by
  have h := abs_le.mp hr
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hr
  have hr0 : 0 < r := by linarith
  have h1 : 0 < 1 - ε := by linarith
  have e : 1 / r - 1 = (1 - r) / r := by
    field_simp
  rw [e, abs_div, abs_of_pos hr0, abs_sub_comm]
  calc |r - 1| / r ≤ ε / r := by gcongr
    _ ≤ ε / (1 - ε) := by
        gcongr
        linarith

/-- The bounds that a world with constant rates within `ε` of one satisfies:
the rate errors of the clocks are at most `ε` and those of the devices at
most `ε / (1 - ε)`, the timestamps are exact, blocks are handed over at once,
and every message takes the least delay of its direction. -/
def rateBounds (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (hpos : ∀ i j, 0 < d.split i j * f.roundTrip i j) :
    Bounds H where
  clockRate := ε
  clockRate_nonneg := hε0
  clockRate_lt_one := by linarith
  deviceRate := ε / (1 - ε)
  deviceRate_nonneg := div_nonneg hε0 (by linarith)
  deviceRate_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  report := 0
  report_nonneg := le_rfl
  handoff := 0
  handoff_nonneg := le_rfl
  leadLeast := m.lead / (1 + ε)
  leadMost := m.lead / (1 - ε)
  leadLeast_pos := div_pos m.lead_pos (by linarith)
  leadLeast_le := by
    have := m.lead_pos
    have h1 : 0 < 1 - ε := by linarith
    gcongr
    linarith
  blockLeast := m.blockSize
  blockMost := m.blockSize
  blockLeast_pos := m.blockSize_pos
  blockLeast_le := le_rfl
  delayLeast := fun i j => d.split i j * f.roundTrip i j
  delayMost := fun i j => d.split i j * f.roundTrip i j
  delayLeast_pos := hpos
  delayLeast_le := fun _ _ => le_rfl
  lossRun := 0

/-- **A world with constant rates within `ε` of one satisfies the bounds
`rateBounds`.** -/
theorem ConstantDelays.withinBounds (hS : ConstantDelays m f d w) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 2) (hrates : ∀ h, |Real.exp (d.logRate h) - 1| ≤ ε)
    (hdevices : ∀ x, |Real.exp (d.deviceLogRate x) - 1| ≤ ε) :
    w.WithinBounds (rateBounds m f d ε hε0 hε hS.delay_pos) := by
  have hρ := m.rate_pos
  have hC := hS.toConstantRates
  have hrate : w.rate = m.rate := hS.builds.rate_eq
  have h1ε : 0 < 1 - ε := by linarith
  have hinv : ∀ x, |1 / Real.exp (d.deviceLogRate x) - 1| ≤ ε / (1 - ε) := fun x =>
    abs_inv_sub_one_le (hdevices x) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h s t hst
    have e : (w.clock h).read t - (w.clock h).read s - (t - s)
        = (Real.exp (d.logRate h) - 1) * (t - s) := by
      rw [hC.clock, hC.clock]
      ring
    rw [e, abs_mul, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact mul_le_mul_of_nonneg_right (hrates h) (sub_nonneg.mpr hst)
  · intro n
    have hg := (Real.exp_pos (d.deviceLogRate none)).ne'
    have e : w.source.capture (n + 1) - w.source.capture n - 1 / w.rate
        = (1 / Real.exp (d.deviceLogRate none) - 1) / m.rate := by
      rw [hC.capture, hC.capture, hrate]
      push_cast
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hρ, hrate]
    show |1 / Real.exp (d.deviceLogRate none) - 1| / m.rate ≤ ε / (1 - ε) / m.rate
    gcongr
    exact hinv none
  · intro r k
    have hg := (Real.exp_pos (d.deviceLogRate (some (m.device r)))).ne'
    have e : (w.speaker r).out (k + 1) - (w.speaker r).out k - 1 / w.rate
        = (1 / Real.exp (d.deviceLogRate (some (m.device r))) - 1) / m.rate := by
      rw [hC.out, hC.out, hrate]
      push_cast
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hρ, hrate]
    show |1 / Real.exp (d.deviceLogRate (some (m.device r))) - 1| / m.rate
      ≤ ε / (1 - ε) / m.rate
    gcongr
    exact hinv (some (m.device r))
  · intro b
    rw [hS.builds.capture_reported b, hS.no_reportError, add_zero, sub_self, abs_zero]
    exact le_rfl
  · intro r b
    rw [hS.builds.speaker_reported r b, hS.no_reportError, add_zero, sub_self, abs_zero]
    exact le_rfl
  · intro b
    rw [hS.builds.handed_of_const (hS.no_hostPauses _) b, sub_self]
    exact le_rfl
  · intro r b
    have hg0 := Real.exp_pos (d.deviceLogRate (some (m.device r)))
    have hb := abs_le.mp (hdevices (some (m.device r)))
    rw [hC.asked]
    have hl := m.lead_pos
    constructor
    · show m.lead / (1 + ε) ≤ m.lead / Real.exp (d.deviceLogRate (some (m.device r)))
      gcongr
      linarith
    · show m.lead / Real.exp (d.deviceLogRate (some (m.device r))) ≤ m.lead / (1 - ε)
      gcongr
      linarith
  · intro b
    have e : w.source.first (b + 1) - w.source.first b = m.blockSize := by
      rw [hS.builds.capture_first, hS.builds.capture_first, Nat.add_mul, one_mul,
        Nat.add_sub_cancel_left]
    rw [e]
    exact ⟨le_rfl, le_rfl⟩
  · intro r b
    have e : (w.speaker r).first (b + 1) - (w.speaker r).first b = m.blockSize := by
      rw [hS.builds.speaker_first, hS.builds.speaker_first, Nat.add_mul, one_mul,
        Nat.add_sub_cancel_left]
    rw [e]
    exact ⟨le_rfl, le_rfl⟩
  · intro i j s q a h
    rw [hS.deliver] at h
    obtain rfl := Option.some.inj h
    show d.split i j * f.roundTrip i j ≤ s + d.split i j * f.roundTrip i j - s
      ∧ s + d.split i j * f.roundTrip i j - s ≤ d.split i j * f.roundTrip i j
    constructor <;> linarith
  · intro i j q send
    exact ⟨0, le_rfl, by rw [hS.deliver]; rfl⟩

end Unisono.Spec.GenerativeWorld
