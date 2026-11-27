/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeWorld

/-!
# The clocks of the generative world as integrals of their rates

In the generative model the clock of a host reads its offset plus the
integral of its rate, and the clock of an audio device advances by the
integral of its rate (`Draw.reading`, `Draw.deviceReading`). The rate is the
exponential of the logarithm of the mean rate plus the wander. This file
states what follows when the wander is continuous in time, which holds in
every outcome of a random world of the model.

* `Draw.rate`, `Draw.deviceRate`: the rate of a host's clock and of a
  device's clock at a true time. Both are positive.
* `Draw.reading_sub`, `Draw.deviceReading_sub`: the advance of a clock
  between two true times is the integral of its rate.
* `Draw.reading_sub_mem`, `Draw.deviceReading_sub_mem`: **a clock whose rate
  stays between two bounds over a stretch of time advances, over every part
  of the stretch, by between the lower bound and the upper bound times the
  length of the part.**
* `Builds.capture_succ_sub_mem`, `Builds.out_succ_sub_mem`: in a world built
  from a draw, while the rate of a device's clock stays between two positive
  bounds, the time from one frame to the next, or from one output sample to
  the next, is between the nominal time divided by the upper bound and the
  nominal time divided by the lower bound.

Nothing here is about a solution.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory

variable {H : Type} {R : ℕ}

/-- The rate of the clock of host `h` at true time `t`, by the draw: the
exponential of the logarithm of its mean rate plus its wander at `t`. -/
def Draw.rate (d : Draw H R) (h : H) (t : Time) : ℝ :=
  Real.exp (d.logRate h + d.wander h t)

/-- The rate of the clock of the audio device `x` at true time `t`, by the
draw. -/
def Draw.deviceRate (d : Draw H R) (x : Option (Fin R)) (t : Time) : ℝ :=
  Real.exp (d.deviceLogRate x + d.deviceWander x t)

/-- The rate of a host's clock is positive. -/
theorem Draw.rate_pos (d : Draw H R) (h : H) (t : Time) : 0 < d.rate h t := Real.exp_pos _

/-- The rate of a device's clock is positive. -/
theorem Draw.deviceRate_pos (d : Draw H R) (x : Option (Fin R)) (t : Time) :
    0 < d.deviceRate x t := Real.exp_pos _

/-- The rate of a host's clock is continuous in time when its wander is. -/
theorem Draw.continuous_rate (d : Draw H R) (h : H) (hc : Continuous (d.wander h)) :
    Continuous (d.rate h) :=
  Real.continuous_exp.comp (continuous_const.add hc)

/-- The rate of a device's clock is continuous in time when its wander
is. -/
theorem Draw.continuous_deviceRate (d : Draw H R) (x : Option (Fin R))
    (hc : Continuous (d.deviceWander x)) : Continuous (d.deviceRate x) :=
  Real.continuous_exp.comp (continuous_const.add hc)

/-- **The advance of a host's clock is the integral of its rate.** -/
theorem Draw.reading_sub (d : Draw H R) (h : H) (hc : Continuous (d.wander h)) (a b : Time) :
    d.reading h b - d.reading h a = ∫ x in a..b, d.rate h x := by
  have hi : ∀ u v : ℝ, IntervalIntegrable (d.rate h) volume u v :=
    fun u v => (d.continuous_rate h hc).intervalIntegrable u v
  have h1 := intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)
  show d.offset h + (∫ x in (0 : ℝ)..b, d.rate h x)
    - (d.offset h + ∫ x in (0 : ℝ)..a, d.rate h x) = _
  linarith

/-- **The advance of a device's clock is the integral of its rate.** -/
theorem Draw.deviceReading_sub (d : Draw H R) (x : Option (Fin R))
    (hc : Continuous (d.deviceWander x)) (a b : Time) :
    d.deviceReading x b - d.deviceReading x a = ∫ y in a..b, d.deviceRate x y := by
  have hi : ∀ u v : ℝ, IntervalIntegrable (d.deviceRate x) volume u v :=
    fun u v => (d.continuous_deviceRate x hc).intervalIntegrable u v
  exact intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)

/-- The integral of a continuous function that stays between two bounds
over a stretch lies between the bounds times the length of any part of the
stretch. -/
theorem integral_mem_of_band {g : ℝ → ℝ} (hg : Continuous g) {lo hi a b : ℝ}
    (hband : ∀ z ∈ Set.Icc a b, lo ≤ g z ∧ g z ≤ hi) {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y)
    (hyb : y ≤ b) :
    lo * (y - x) ≤ ∫ z in x..y, g z ∧ ∫ z in x..y, g z ≤ hi * (y - x) := by
  have hi' : IntervalIntegrable g volume x y := hg.intervalIntegrable x y
  have hsub : ∀ z ∈ Set.Icc x y, z ∈ Set.Icc a b :=
    fun z hz => ⟨hax.trans hz.1, hz.2.trans hyb⟩
  constructor
  · have h1 := intervalIntegral.integral_mono_on hxy
      (intervalIntegrable_const (c := lo)) hi'
      (fun z hz => (hband z (hsub z hz)).1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    linarith
  · have h1 := intervalIntegral.integral_mono_on hxy hi'
      (intervalIntegrable_const (c := hi))
      (fun z hz => (hband z (hsub z hz)).2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    linarith

/-- **A host's clock whose rate stays between two bounds advances between
them.** If the rate of the clock of host `h` lies between `lo` and `hi` from
the true time `a` to the true time `b`, then from `x` to `y`, with
`a ≤ x ≤ y ≤ b`, the clock advances by at least `lo * (y - x)` and at most
`hi * (y - x)`. -/
theorem Draw.reading_sub_mem (d : Draw H R) (h : H) (hc : Continuous (d.wander h))
    {lo hi a b : ℝ} (hband : ∀ z ∈ Set.Icc a b, lo ≤ d.rate h z ∧ d.rate h z ≤ hi)
    {x y : Time} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    lo * (y - x) ≤ d.reading h y - d.reading h x
      ∧ d.reading h y - d.reading h x ≤ hi * (y - x) := by
  rw [d.reading_sub h hc x y]
  exact integral_mem_of_band (d.continuous_rate h hc) hband hax hxy hyb

/-- **A device's clock whose rate stays between two bounds advances between
them.** -/
theorem Draw.deviceReading_sub_mem (d : Draw H R) (x : Option (Fin R))
    (hc : Continuous (d.deviceWander x)) {lo hi a b : ℝ}
    (hband : ∀ z ∈ Set.Icc a b, lo ≤ d.deviceRate x z ∧ d.deviceRate x z ≤ hi)
    {y y' : Time} (hay : a ≤ y) (hyy' : y ≤ y') (hyb : y' ≤ b) :
    lo * (y' - y) ≤ d.deviceReading x y' - d.deviceReading x y
      ∧ d.deviceReading x y' - d.deviceReading x y ≤ hi * (y' - y) := by
  rw [d.deviceReading_sub x hc y y']
  exact integral_mem_of_band (d.continuous_deviceRate x hc) hband hay hyy' hyb

variable {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R} {w : World H R}

/-- **The time from one frame to the next while the capture device's clock
keeps its rate between two bounds.** In a world built from a draw, let the
rate of the capture device's clock lie between `lo > 0` and `hi` from the
true time `a` to the true time `b`, and let frames `n` and `n + 1` be
captured in that stretch. Then the time from frame `n` to frame `n + 1` is at
least the nominal time divided by `hi` and at most the nominal time divided
by `lo`. -/
theorem Builds.capture_succ_sub_mem (hB : m.Builds f d w)
    (hc : Continuous (d.deviceWander none)) {lo hi a b : ℝ} (hlo : 0 < lo)
    (hband : ∀ z ∈ Set.Icc a b, lo ≤ d.deviceRate none z ∧ d.deviceRate none z ≤ hi) {n : ℕ}
    (han : a ≤ w.source.capture n) (hnb : w.source.capture (n + 1) ≤ b) :
    1 / (m.rate * hi) ≤ w.source.capture (n + 1) - w.source.capture n
      ∧ w.source.capture (n + 1) - w.source.capture n ≤ 1 / (m.rate * lo) := by
  have hstep : w.source.capture n < w.source.capture (n + 1) :=
    w.source.capture_strictMono (Nat.lt_succ_self n)
  have h1 := hB.capture (n + 1)
  have h2 := hB.capture n
  have hadv : d.deviceReading none (w.source.capture (n + 1))
      - d.deviceReading none (w.source.capture n) = 1 / m.rate := by
    have hr := m.rate_pos.ne'
    have e : ((n + 1 : ℕ) : ℝ) / m.rate - (n : ℝ) / m.rate = 1 / m.rate := by
      push_cast
      field_simp
      ring
    linarith
  obtain ⟨h3, h4⟩ := d.deviceReading_sub_mem none hc hband han hstep.le hnb
  rw [hadv] at h3 h4
  have hhi : 0 < hi := lt_of_lt_of_le hlo ((hband _ ⟨han, hstep.le.trans hnb⟩).1.trans
    (hband _ ⟨han, hstep.le.trans hnb⟩).2)
  have hr := m.rate_pos
  constructor
  · rw [div_le_iff₀ (mul_pos hr hhi)]
    have := mul_le_mul_of_nonneg_left h4 hr.le
    rw [mul_one_div_cancel hr.ne'] at this
    nlinarith
  · rw [le_div_iff₀ (mul_pos hr hlo)]
    have := mul_le_mul_of_nonneg_left h3 hr.le
    rw [mul_one_div_cancel hr.ne'] at this
    nlinarith

/-- **The time from one output sample to the next while the playback
device's clock keeps its rate between two bounds.** In a world built from a
draw, let the rate of the clock of the device of speaker `r` lie between
`lo > 0` and `hi` from the true time `a` to the true time `b`, and let
output samples `k` and `k + 1` of the speaker leave in that stretch. Then the
time from output sample `k` to output sample `k + 1` is at least the nominal
time divided by `hi` and at most the nominal time divided by `lo`. -/
theorem Builds.out_succ_sub_mem (hB : m.Builds f d w) (r : Fin R)
    (hc : Continuous (d.deviceWander (some (m.device r)))) {lo hi a b : ℝ} (hlo : 0 < lo)
    (hband : ∀ z ∈ Set.Icc a b, lo ≤ d.deviceRate (some (m.device r)) z
      ∧ d.deviceRate (some (m.device r)) z ≤ hi) {k : ℕ}
    (hak : a ≤ (w.speaker r).out k) (hkb : (w.speaker r).out (k + 1) ≤ b) :
    1 / (m.rate * hi) ≤ (w.speaker r).out (k + 1) - (w.speaker r).out k
      ∧ (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ 1 / (m.rate * lo) := by
  have hstep : (w.speaker r).out k < (w.speaker r).out (k + 1) :=
    (w.speaker r).out_strictMono (Nat.lt_succ_self k)
  have h1 := hB.speaker_out r (k + 1)
  have h2 := hB.speaker_out r k
  have hadv : d.deviceReading (some (m.device r)) ((w.speaker r).out (k + 1))
      - d.deviceReading (some (m.device r)) ((w.speaker r).out k) = 1 / m.rate := by
    have hr := m.rate_pos.ne'
    have e : ((k + 1 : ℕ) : ℝ) / m.rate - (k : ℝ) / m.rate = 1 / m.rate := by
      push_cast
      field_simp
      ring
    linarith
  obtain ⟨h3, h4⟩ := d.deviceReading_sub_mem (some (m.device r)) hc hband hak hstep.le hkb
  rw [hadv] at h3 h4
  have hhi : 0 < hi := lt_of_lt_of_le hlo ((hband _ ⟨hak, hstep.le.trans hkb⟩).1.trans
    (hband _ ⟨hak, hstep.le.trans hkb⟩).2)
  have hr := m.rate_pos
  constructor
  · rw [div_le_iff₀ (mul_pos hr hhi)]
    have := mul_le_mul_of_nonneg_left h4 hr.le
    rw [mul_one_div_cancel hr.ne'] at this
    nlinarith
  · rw [le_div_iff₀ (mul_pos hr hlo)]
    have := mul_le_mul_of_nonneg_left h3 hr.le
    rw [mul_one_div_cancel hr.ne'] at this
    nlinarith

end Unisono.Spec.GenerativeWorld
