/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Timing
public import Unisono.Spec.Models.GenerativeUndisturbed

/-!
# The requests of a playback device while nothing disturbs the stream

In a world built from a regular draw, let the stream to a speaker be
undisturbed from the true time `a₀` to `b₀` (`Draw.Undisturbed`). The
speaker's host is then idle, so it handles each request when the device
raises it. `outputLead m w r β k` is the time on the device's clock from
the request of block `β` to output sample `k`: the request lead plus the
nominal time from the block's first output sample to `k`.

For a request that the host handles after `a₀` and by `b₀`:

* `out_sub_asked_of_idle`: the device's clock advances by `outputLead` from
  the request to output sample `k`.
* `out_sub_asked_mem`: so output sample `k`, if it leaves by `b₀`, leaves
  between `outputLead` divided by the largest rate of the device's clock and
  `outputLead` divided by the least rate after the request.
* `hostReading_out_sub_asked_mem`: the host's clock advances between those
  two times multiplied by its least and by its largest rate.
* `ratioAt_mem_of_undisturbed`: the ratio of its own clock to the device's
  clock that the host takes at the next request lies between the least rate
  of the host's clock divided by the largest rate of the device's clock and
  the largest divided by the least, provided those two numbers are within
  `slopeBound` of one.
* `abs_out_sub_outputAt_le`: the reading of the host's clock
  when output sample `k` leaves differs from the reading that the host
  expects (`outputAt`) by at most `outputLead` times the difference of those
  two numbers.

Nothing here depends on the solution.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld Unisono.Model.Descent

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R}

/-- The time on the device's clock from the request of block `β` of speaker
`r`, when its host handles the request as the device raises it, to output
sample `k`: the request lead plus the nominal time from the block's first
output sample to `k`. -/
def outputLead (m : GenerativeWorld H R) (w : World H R) (r : Fin R) (β k : ℕ) : ℝ :=
  m.lead + ((k : ℝ) - (w.speaker r).first β) / m.rate

/-- **From a request handled by an idle host to an output sample, the
device's clock advances by `outputLead`.** -/
theorem out_sub_asked_of_idle (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    {a₀ b₀ : Time} (hidle : IdleOn (d.hostPaused (w.host r)) a₀ b₀) {β : ℕ}
    (ha : a₀ < (w.speaker r).asked β) (hb : (w.speaker r).asked β ≤ b₀) (k : ℕ) :
    d.deviceReading (some (m.device r)) ((w.speaker r).out k)
        - d.deviceReading (some (m.device r)) ((w.speaker r).asked β)
      = outputLead m w r β k := by
  have h1 := hB.asked_of_idleOn (hd.hostPaused_monotone _) hidle ha hb
  have h2 := hB.speaker_out r k
  have h3 := hB.speaker_out r ((w.speaker r).first β)
  unfold outputLead
  have e : ((k : ℝ) - (w.speaker r).first β) / m.rate
      = (k : ℝ) / m.rate - ((w.speaker r).first β : ℝ) / m.rate := by ring
  rw [e]
  linarith

variable {B : RateBands} {ρ : ℝ} {a₀ b₀ : Time}

/-- **When an output sample leaves, after its request.** While nothing
disturbs the stream, an output sample `k` whose `outputLead` from the request
of block `β` is not negative leaves at or after the request; and if it
leaves by `b₀`, the time from the request to it is between `outputLead`
divided by the largest rate of the device's clock and `outputLead` divided by
the least rate. -/
theorem out_sub_asked_mem (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    {β k : ℕ} (ha : a₀ < (w.speaker r).asked β) (hb : (w.speaker r).asked β ≤ b₀)
    (hlead : 0 ≤ outputLead m w r β k) (hout : (w.speaker r).out k ≤ b₀) :
    (w.speaker r).asked β ≤ (w.speaker r).out k
      ∧ outputLead m w r β k / B.outputHi ≤ (w.speaker r).out k - (w.speaker r).asked β
      ∧ (w.speaker r).out k - (w.speaker r).asked β ≤ outputLead m w r β k / B.outputLo := by
  have hadv := out_sub_asked_of_idle hB hd hU.forward.target ha hb k
  obtain ⟨c, hc⟩ := hB.deviceClock (some (m.device r))
  have hle : (w.speaker r).asked β ≤ (w.speaker r).out k := by
    have : c.read ((w.speaker r).asked β) ≤ c.read ((w.speaker r).out k) := by
      rw [hc, hc]
      linarith
    exact c.strictMono.le_iff_le.mp this
  obtain ⟨h1, h2⟩ := hU.output_sub hd ha.le hle hout
  rw [hadv] at h1 h2
  have hHi : 0 < B.outputHi := lt_of_lt_of_le hBv.output_pos hBv.output_le
  refine ⟨hle, ?_, ?_⟩
  · rw [div_le_iff₀ hHi]
    linarith
  · rw [le_div_iff₀ hBv.output_pos]
    linarith

/-- **The advance of the host's clock from a request to an output sample**,
while nothing disturbs the stream: at least the least rate of the host's
clock times `outputLead` divided by the largest rate of the device's clock,
and at most the largest rate times `outputLead` divided by the least. -/
theorem hostReading_out_sub_asked_mem (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    {β k : ℕ} (ha : a₀ < (w.speaker r).asked β) (hb : (w.speaker r).asked β ≤ b₀)
    (hlead : 0 ≤ outputLead m w r β k) (hout : (w.speaker r).out k ≤ b₀) :
    B.hostLo * (outputLead m w r β k / B.outputHi)
        ≤ (w.clock (w.host r)).read ((w.speaker r).out k)
          - (w.clock (w.host r)).read ((w.speaker r).asked β)
      ∧ (w.clock (w.host r)).read ((w.speaker r).out k)
          - (w.clock (w.host r)).read ((w.speaker r).asked β)
        ≤ B.hostHi * (outputLead m w r β k / B.outputLo) := by
  obtain ⟨hle, h1, h2⟩ := out_sub_asked_mem hB hd hU hBv ha hb hlead hout
  obtain ⟨h3, h4⟩ := hU.host_sub hd ha.le hle hout
  rw [← hB.clock, ← hB.clock] at h3 h4
  have hHi : 0 ≤ B.hostHi := hBv.host_pos.le.trans hBv.host_le
  exact ⟨(mul_le_mul_of_nonneg_left h1 hBv.host_pos.le).trans h3,
    h4.trans (mul_le_mul_of_nonneg_left h2 hHi)⟩

/-- **The ratio that a host takes while nothing disturbs the stream.** Let
the host handle the request of block `β` after `a₀` and that of block
`β + 1` by `b₀`, and let the told rate be the model's. If the least rate of
the host's clock divided by the largest rate of the device's clock, and the
largest divided by the least, are within `slopeBound` of one, then the ratio
that the host takes at the request of block `β + 1` lies between those two
numbers. -/
theorem ratioAt_mem_of_undisturbed (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    (t : TimingSettings) (hrate : t.rate = m.rate)
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    (hlo : 1 - t.slopeBound ≤ B.hostLo / B.outputHi)
    (hhi : B.hostHi / B.outputLo ≤ 1 + t.slopeBound) {β : ℕ}
    (ha : a₀ < (w.speaker r).asked β) (hb : (w.speaker r).asked (β + 1) ≤ b₀) :
    ratioAt t w r (β + 1) ∈ Set.Icc (B.hostLo / B.outputHi) (B.hostHi / B.outputLo) := by
  have hmono := (w.speaker r).asked_mono (Nat.le_succ β)
  have hidle := hU.forward.target
  have h1 := hB.asked_of_idleOn (hd.hostPaused_monotone _) hidle ha (hmono.trans hb)
  have h2 := hB.asked_of_idleOn (hd.hostPaused_monotone _) hidle (lt_of_lt_of_le ha hmono) hb
  have h3 := hB.speaker_out r ((w.speaker r).first β)
  have h4 := hB.speaker_out r ((w.speaker r).first (β + 1))
  have hr := m.rate_pos
  have hN : (0 : ℝ) < ((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β := by
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self β)
    have : ((w.speaker r).first β : ℝ) < (w.speaker r).first (β + 1) := by exact_mod_cast this
    linarith
  -- The device's clock advances by the nominal time of a block between the requests.
  have hadv : d.deviceReading (some (m.device r)) ((w.speaker r).asked (β + 1))
        - d.deviceReading (some (m.device r)) ((w.speaker r).asked β)
      = (((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β) / m.rate := by
    have e : (((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β) / m.rate
        = ((w.speaker r).first (β + 1) : ℝ) / m.rate - ((w.speaker r).first β : ℝ) / m.rate := by
      ring
    rw [e]
    linarith
  obtain ⟨h5, h6⟩ := hU.output_sub hd ha.le hmono hb
  obtain ⟨h7, h8⟩ := hU.host_sub hd ha.le hmono hb
  rw [hadv] at h5 h6
  rw [← hB.clock, ← hB.clock] at h7 h8
  have hHi : 0 < B.outputHi := lt_of_lt_of_le hBv.output_pos hBv.output_le
  have hhHi : 0 ≤ B.hostHi := hBv.host_pos.le.trans hBv.host_le
  -- In frames: `N ≤ outputHi * L * rate` and `outputLo * L * rate ≤ N`.
  have h5' : B.outputLo * ((w.speaker r).asked (β + 1) - (w.speaker r).asked β) * m.rate
      ≤ ((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β := by
    have := mul_le_mul_of_nonneg_right h5 hr.le
    rwa [div_mul_cancel₀ _ hr.ne'] at this
  have h6' : ((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β
      ≤ B.outputHi * ((w.speaker r).asked (β + 1) - (w.speaker r).asked β) * m.rate := by
    have := mul_le_mul_of_nonneg_right h6 hr.le
    rwa [div_mul_cancel₀ _ hr.ne'] at this
  have hraw1 : B.hostLo / B.outputHi
      ≤ (requestReading w r (β + 1) - requestReading w r β) * t.rate
        / (((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β) := by
    rw [hrate, le_div_iff₀ hN, div_mul_eq_mul_div, div_le_iff₀ hHi]
    unfold requestReading
    have h9 := mul_le_mul_of_nonneg_left h6' hBv.host_pos.le
    have h10 := mul_le_mul_of_nonneg_right h7 (mul_nonneg hr.le hHi.le)
    nlinarith
  have hraw2 : (requestReading w r (β + 1) - requestReading w r β) * t.rate
        / (((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β)
      ≤ B.hostHi / B.outputLo := by
    rw [hrate, div_le_iff₀ hN, div_mul_eq_mul_div, le_div_iff₀ hBv.output_pos]
    unfold requestReading
    have h9 := mul_le_mul_of_nonneg_left h5' hhHi
    have h10 := mul_le_mul_of_nonneg_right h8 (mul_nonneg hr.le hBv.output_pos.le)
    nlinarith
  show clampTo (1 - t.slopeBound) (1 + t.slopeBound)
      ((requestReading w r (β + 1) - requestReading w r β) * t.rate
        / (((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β)) ∈ _
  unfold clampTo
  rw [min_eq_right (hraw2.trans hhi), max_eq_right (hlo.trans hraw1)]
  exact ⟨hraw1, hraw2⟩

/-- **How well a host expects the reading of its clock when an output sample
leaves**, while nothing disturbs the stream. In the setting of
`ratioAt_mem_of_undisturbed`, with the told lead the model's, let output
sample `k` have an `outputLead` from the request of block `β + 1` that is
not negative, and let it leave by `b₀`. Then the reading of the host's clock
when it leaves differs from the reading that the host expects at that
request by at most `outputLead` times the largest rate of the host's clock
divided by the least rate of the device's clock, minus the least divided by
the largest. -/
theorem abs_out_sub_outputAt_le (hB : m.Builds f d w) (hd : d.Regular) {r : Fin R}
    (t : TimingSettings) (hrate : t.rate = m.rate) (hleadEq : t.lead = m.lead)
    (hU : d.Undisturbed w.sender (w.host r) (m.device r) B ρ a₀ b₀) (hBv : B.Valid)
    (hlo : 1 - t.slopeBound ≤ B.hostLo / B.outputHi)
    (hhi : B.hostHi / B.outputLo ≤ 1 + t.slopeBound) {β k : ℕ}
    (ha : a₀ < (w.speaker r).asked β) (hb : (w.speaker r).asked (β + 1) ≤ b₀)
    (hlead : 0 ≤ outputLead m w r (β + 1) k) (hout : (w.speaker r).out k ≤ b₀) :
    |(w.clock (w.host r)).read ((w.speaker r).out k) - outputAt t w r (β + 1) k|
      ≤ (B.hostHi / B.outputLo - B.hostLo / B.outputHi) * outputLead m w r (β + 1) k := by
  have hmono := (w.speaker r).asked_mono (Nat.le_succ β)
  obtain ⟨hr1, hr2⟩ := ratioAt_mem_of_undisturbed hB hd t hrate hU hBv hlo hhi ha hb
  obtain ⟨h1, h2⟩ := hostReading_out_sub_asked_mem hB hd hU hBv (lt_of_lt_of_le ha hmono) hb
    hlead hout
  have e : outputAt t w r (β + 1) k
      = (w.clock (w.host r)).read ((w.speaker r).asked (β + 1))
        + outputLead m w r (β + 1) k * ratioAt t w r (β + 1) := by
    unfold outputAt outputLead requestReading
    rw [hrate, hleadEq]
  rw [e, abs_le]
  have h3 := mul_le_mul_of_nonneg_left hr1 hlead
  have h4 := mul_le_mul_of_nonneg_left hr2 hlead
  have e1 : B.hostLo * (outputLead m w r (β + 1) k / B.outputHi)
      = outputLead m w r (β + 1) k * (B.hostLo / B.outputHi) := by ring
  have e2 : B.hostHi * (outputLead m w r (β + 1) k / B.outputLo)
      = outputLead m w r (β + 1) k * (B.hostHi / B.outputLo) := by ring
  rw [e1] at h1
  rw [e2] at h2
  constructor <;> nlinarith

end Unisono.Solutions.Controller
