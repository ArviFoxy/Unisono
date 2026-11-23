/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.Bounded

/-!
# Ideal constant worlds

A deterministic full-world model class (`IdealConstantWorld`) representing the
noiseless baseline:

* Every host's clock runs at exact unit rate (`read t = t + c₀ h`) with an
  arbitrary constant initial offset `c₀ h` (so synchronization must still
  recover unknown clock offsets across hosts).
* The capture device and every playback device run at the exact nominal rate
  `rate`, produce fixed-size blocks of `blockSize` frames/samples, report
  exact timestamps (`ReportsWithin 0`), hand over capture blocks with zero
  delay, and request playback blocks with constant lead `lead`.
* Every directed link `(i, j)` delivers every message with a constant positive
  delay `delay i j`, zero jitter, no pauses, no outages, and no packet loss.
* The target latency is constant (`targetLatency`).

`IdealConstantWorld.Symmetric` restricts to symmetric link delays
(`delay i j = delay j i`); `IdealConstantWorld.Asymmetric` asserts that at
least one link pair has asymmetric delays (`delay i j ≠ delay j i`), the
exact setting of the Star-vs-Peer separation results in `Unisono.Spec.Limits`.

Every `IdealConstantWorld` is a special case of `BoundedWorld`
(`IdealConstantWorld.withinBounds`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- Parameters of an ideal noiseless world with constant per-link delays,
exact clocks (up to constant initial offsets), exact audio devices, and zero
packet loss. -/
structure IdealConstantWorld (H : Type) (R : ℕ) where
  /-- Common nominal sample rate of all devices, in frames per second. -/
  rate : ℝ
  rate_pos : 0 < rate
  /-- The sender host. -/
  sender : H
  /-- The host carrying each speaker. -/
  host : Fin R → H
  /-- Constant positive one-way delay of each directed link `(i, j)`, in seconds. -/
  delay : H → H → ℝ
  delay_pos : ∀ i j, 0 < delay i j
  /-- Constant block size (frames per capture block and samples per playback block). -/
  blockSize : ℕ
  blockSize_pos : 0 < blockSize
  /-- Constant playback request lead, in seconds. -/
  lead : ℝ
  lead_pos : 0 < lead
  /-- Constant application target latency, in seconds. -/
  targetLatency : ℝ
  targetLatency_nonneg : 0 ≤ targetLatency

namespace IdealConstantWorld

variable {H : Type} {R : ℕ}

/-- All directed link delays are symmetric (`delay i j = delay j i`). -/
def Symmetric (m : IdealConstantWorld H R) : Prop :=
  ∀ i j, m.delay i j = m.delay j i

/-- At least one pair of hosts has asymmetric one-way delays. -/
def Asymmetric (m : IdealConstantWorld H R) : Prop :=
  ∃ i j, m.delay i j ≠ m.delay j i

/-- A world `w` belongs to the `IdealConstantWorld` model class `m`. -/
structure Holds (m : IdealConstantWorld H R) (w : World H R) : Prop where
  rate_eq : w.rate = m.rate
  sender_eq : w.sender = m.sender
  host_eq : w.host = m.host
  /-- Every host clock runs at exact unit rate, with an arbitrary constant
  initial offset. -/
  clocks : ∀ h, ∃ c₀ : ℝ, ∀ t : Time, (w.clock h).read t = t + c₀
  /-- Capture frames occur at exact nominal spacing from some start time. -/
  capture : ∃ t₀ : Time, ∀ n : ℕ, w.source.capture n = t₀ + (n : ℝ) / m.rate
  /-- Capture blocks have exact constant size `m.blockSize`. -/
  capture_first : ∀ b : ℕ, w.source.first b = b * m.blockSize
  /-- Capture blocks are handed over immediately when their last frame is captured. -/
  capture_handed : ∀ b : ℕ, w.source.handed b = w.source.capture (w.source.first (b + 1) - 1)
  /-- Capture timestamps are exact. -/
  capture_reported : w.source.ReportsWithin (w.clock w.sender) 0
  /-- Playback output samples leave at exact nominal spacing from some start time. -/
  speaker_out : ∀ r : Fin R, ∃ t₀ : Time, ∀ k : ℕ, (w.speaker r).out k = t₀ + (k : ℝ) / m.rate
  /-- Playback blocks have exact constant size `m.blockSize`. -/
  speaker_first : ∀ r : Fin R, ∀ b : ℕ, (w.speaker r).first b = b * m.blockSize
  /-- Playback blocks are requested with exact constant lead `m.lead`. -/
  speaker_asked : ∀ r : Fin R, ∀ b : ℕ,
    (w.speaker r).out ((w.speaker r).first b) - (w.speaker r).asked b = m.lead
  /-- Playback timestamps are exact. -/
  speaker_reported : ∀ r : Fin R, (w.speaker r).ReportsWithin (w.clock (w.host r)) 0
  /-- Every message on link `(i, j)` arrives with exact constant delay `m.delay i j`. -/
  network : ∀ i j s q, w.network.deliver i j s q = some (s + m.delay i j)
  /-- Application target latency is constant. -/
  target_eq : ∀ n : ℕ, w.target n = m.targetLatency

/-- The tight `Bounds` corresponding to an `IdealConstantWorld`: zero rate
errors, zero report error, zero handoff delay, zero loss, and exact constant
delays `m.delay i j`. -/
def toBounds (m : IdealConstantWorld H R) : Bounds H where
  clockRate := 0
  clockRate_nonneg := le_rfl
  clockRate_lt_one := one_pos
  deviceRate := 0
  deviceRate_nonneg := le_rfl
  deviceRate_lt_one := one_pos
  report := 0
  report_nonneg := le_rfl
  handoff := 0
  handoff_nonneg := le_rfl
  leadLeast := m.lead
  leadMost := m.lead
  leadLeast_pos := m.lead_pos
  leadLeast_le := le_rfl
  blockLeast := m.blockSize
  blockMost := m.blockSize
  blockLeast_pos := m.blockSize_pos
  blockLeast_le := le_rfl
  delayLeast := m.delay
  delayMost := m.delay
  delayLeast_pos := m.delay_pos
  delayLeast_le := fun _ _ => le_rfl
  lossRun := 0

/-- Every world in `IdealConstantWorld` satisfies `World.WithinBounds m.toBounds`. -/
theorem withinBounds {m : IdealConstantWorld H R} {w : World H R} (hw : m.Holds w) :
    w.WithinBounds m.toBounds := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h s t _
    obtain ⟨c₀, hc⟩ := hw.clocks h
    simp [toBounds, hc]
  · intro n
    obtain ⟨t₀, ht⟩ := hw.capture
    simp only [toBounds, hw.rate_eq, ht, zero_div]
    push_cast
    have hsub : (t₀ + ((n : ℝ) + 1) / m.rate) - (t₀ + (n : ℝ) / m.rate) - 1 / m.rate = 0 := by
      ring
    rw [hsub, abs_zero]
  · intro r k
    obtain ⟨t₀, ht⟩ := hw.speaker_out r
    simp only [toBounds, hw.rate_eq, ht, zero_div]
    push_cast
    have hsub : (t₀ + ((k : ℝ) + 1) / m.rate) - (t₀ + (k : ℝ) / m.rate) - 1 / m.rate = 0 := by
      ring
    rw [hsub, abs_zero]
  · exact hw.capture_reported
  · exact hw.speaker_reported
  · intro b
    simp [toBounds, hw.capture_handed b]
  · intro r b
    simp [toBounds, hw.speaker_asked r b]
  · intro b
    have hdiff : (b + 1) * m.blockSize - b * m.blockSize = m.blockSize := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    simp [toBounds, hw.capture_first, hdiff]
  · intro r b
    have hdiff : (b + 1) * m.blockSize - b * m.blockSize = m.blockSize := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    simp [toBounds, hw.speaker_first, hdiff]
  · intro i j s q a ha
    rw [hw.network i j s q, Option.some.injEq] at ha
    simp only [toBounds]
    constructor <;> linarith
  · intro i j q send
    exact ⟨0, le_rfl, by simp [hw.network]⟩

end IdealConstantWorld

end Unisono.Spec
