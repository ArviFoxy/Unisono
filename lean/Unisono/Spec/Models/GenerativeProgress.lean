/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeWorld

/-!
# The devices of a built world never stop

In every world built from a draw, in every member of the generative model,
the capture device hands over blocks without end and every playback device
requests blocks without end: for every true time there is a later handover
and a later request (`Builds.handed_unbounded`, `Builds.asked_unbounded`).
The reason is that a device's clock is continuous and never stands still,
so it shows a finite reading at every true time, while the reading at the
`n`-th frame grows with `n`.

Clocks may wander and links and hosts may pause; nothing is assumed about
the draw.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R}

/-- **The capture device hands over blocks without end**, in every built
world. -/
theorem Builds.handed_unbounded (hB : m.Builds f d w) (T : Time) :
    ∃ b, T < w.source.handed b := by
  obtain ⟨c, hc⟩ := hB.deviceClock none
  obtain ⟨b, hb⟩ := exists_nat_gt ((c.read T - c.read (w.source.capture 0)) * m.rate)
  refine ⟨b, ?_⟩
  by_contra hle
  have hle' : w.source.handed b ≤ T := not_lt.mp hle
  have hmono := c.strictMono.monotone hle'
  have hcap := hB.capture (w.source.first (b + 1) - 1)
  rw [← hc, ← hc, ← hB.capture_handed] at hcap
  have hfirst : b ≤ w.source.first (b + 1) - 1 := by
    rw [hB.capture_first]
    have hpos := m.blockSize_pos
    have : b + 1 ≤ (b + 1) * m.blockSize := Nat.le_mul_of_pos_right _ hpos
    omega
  have hcast : (b : ℝ) ≤ ((w.source.first (b + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hfirst
  have hrate := m.rate_pos
  have h1 : ((w.source.first (b + 1) - 1 : ℕ) : ℝ) / m.rate
      ≤ c.read T - c.read (w.source.capture 0) := by linarith
  rw [div_le_iff₀ hrate] at h1
  linarith

/-- **Every playback device requests blocks without end**, in every built
world. -/
theorem Builds.asked_unbounded (hB : m.Builds f d w) (r : Fin R) (T : Time) :
    ∃ b, T < (w.speaker r).asked b := by
  obtain ⟨c, hc⟩ := hB.deviceClock (some (m.device r))
  obtain ⟨b, hb⟩ := exists_nat_gt
    ((c.read T - c.read ((w.speaker r).out 0) + m.lead) * m.rate)
  refine ⟨b, ?_⟩
  by_contra hle
  have hle' : (w.speaker r).asked b ≤ T := not_lt.mp hle
  have hmono := c.strictMono.monotone hle'
  have hout := hB.speaker_out r ((w.speaker r).first b)
  have hask := hB.speaker_asked r b
  rw [← hc, ← hc] at hout hask
  have hfirst : b ≤ (w.speaker r).first b := by
    rw [hB.speaker_first]
    exact Nat.le_mul_of_pos_right _ m.blockSize_pos
  have hcast : (b : ℝ) ≤ (((w.speaker r).first b : ℕ) : ℝ) := by exact_mod_cast hfirst
  have hrate := m.rate_pos
  have h1 : (((w.speaker r).first b : ℕ) : ℝ) / m.rate
      ≤ c.read T - c.read ((w.speaker r).out 0) + m.lead := by linarith
  rw [div_le_iff₀ hrate] at h1
  linarith

end Unisono.Spec.GenerativeWorld
