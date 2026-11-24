/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Pauses
public import Unisono.Spec.OutputRate

/-!
# The cost of a held level when links and hosts pause

The controller (`Unisono.Solutions.Controller`) holds the level at `L` in a
world whose clocks run at constant rates, with exact timestamps and with
pauses of links and of hosts. By `Unisono.Solutions.Controller.HeldLevel`,
each output sample plays the position that is due, or nothing of the source
when the block it needs is late. An output sample is *late* when the message
of the capture block it needs takes at least the sample's margin (`lateAt`).
The *late rate* at the level `L` is the long-run number of late output
samples per second, averaged over the speakers (`lateRate`).

**Theorem** (`cost_le_of_heldLevel`). The cost of the controller in that
world, for any weights, is at most

* the weight of synchronization times the mean square difference of the
  speakers' latencies, which differ only by the asymmetries of their hosts,
* plus the weight of latency times the mean of the speakers' latencies,
* plus the weight of tracking times the mean square of the latency minus the
  target latency,
* plus the weight of missed samples times `1 + 2 δ`, plus the weight of
  discontinuities, times the late rate.

Here `δ` bounds how much faster the capture device's clock runs than the
clock of any playback device, as a fraction. Roughness costs nothing: a gap
does not change the speed of playback on either side of it.

The first three terms rise with the level and the last falls with it:
raising the level by one second of the sender's clock raises every latency
and every margin by one second divided by the rate of that clock. The late
rate is at most the long-run number of output samples whose block takes more
than the least margin (`lateRate_le`), a number that depends on the world
only through how long the blocks take.

The theorem needs the capture device's clock to run less than twice as fast
as the clock of every playback device. Without that condition, the last
term becomes the weight of missed samples times `1 + 2 δ`, plus the weight
of discontinuities, times the number of output samples per second in true
time, averaged over the speakers (`cost_le_outputs_of_heldLevel`).

Neither bound uses how the controller comes to play what it plays. The first
holds for any playback that, from some output sample on, plays the position
that is due exactly when the block that the sample needs is on time
(`cost_le_of_plays_margin`). The second holds for any playback that, from
some output sample on, plays only positions that are due
(`cost_le_outputs_of_plays_due`). Both come from one statement about such
a playback (`cost_le_of_duePositions`). The controller with a limiter
(`Unisono.Solutions.Controller.Limited`) is bounded through them.

The theorems are upper bounds in one outcome. How large the late rate is
under the generative model is in `Unisono.Solutions.Controller.LateRate`,
and the mean of the bound is in `Unisono.Solutions.Controller.ExpectedCost`.
The theorems do not say that no other solution has a lower cost.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} (p : FixedDelay.Params H)

/-- One if output sample `k` of speaker `r` is late at the level `L`: the
message of the capture block that the sample needs takes at least the
sample's margin. Zero otherwise. -/
def lateAt (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (lookahead : ℕ+) (L : ℝ) (r : Fin R) (k : ℕ) : ℕ :=
  if margin m f d w lookahead L r k
      ≤ blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
  then 1 else 0

/-- The late rate at the level `L`: the long-run number of late output
samples per second, averaged over the speakers. -/
def lateRate (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (lookahead : ℕ+) (L : ℝ) : ℝ≥0∞ :=
  longRun (w.accruedOutputs fun r k => (lateAt m f d w lookahead L r k : ℝ≥0∞))

/-- One if the message of the capture block that output sample `k` of
speaker `r` needs takes more than the least margin of the level `L`. Zero
otherwise. -/
def slowAt (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (lookahead : ℕ+) (L : ℝ) (r : Fin R) (k : ℕ) : ℕ :=
  if marginLeast m f d lookahead L r
      < blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
  then 1 else 0

omit [DecidableEq H] in
/-- From some output sample on, the position that is due is past the start
of the stream. -/
theorem exists_duePosition_nonneg (hS : ConstantRates m f d w) (L : ℝ) (r : Fin R) :
    ∃ K, ∀ k, K ≤ k → 0 ≤ duePosition m f d w L r k := by
  obtain ⟨bK, hbK⟩ := hS.asked_unbounded r (latencyOf m f d L r + w.source.capture 0)
  refine ⟨bK * m.blockSize, fun k hk => ?_⟩
  have hout : (w.speaker r).out ((w.speaker r).first bK) ≤ (w.speaker r).out k :=
    (w.speaker r).out_strictMono.monotone (by rw [hS.builds.speaker_first]; exact hk)
  have hask := (w.speaker r).asked_before bK
  unfold duePosition
  exact mul_nonneg (mul_pos m.rate_pos (Real.exp_pos _)).le (by linarith)

omit [DecidableEq H] in
/-- **The late rate is at most the rate of blocks that take more than the
least margin.** An output sample is late only if the message of the capture
block it needs takes more than the least margin of its speaker. -/
theorem lateRate_le (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ) :
    lateRate m f d w lookahead L
      ≤ longRun (w.accruedOutputs fun r k => (slowAt m f d w lookahead L r k : ℝ≥0∞)) := by
  choose K hK using fun r => exists_duePosition_nonneg hS L r
  unfold lateRate
  refine w.longRun_outputs_le (Finset.univ.sup K) (fun r k hk => ?_)
    (fun r k => ENNReal.natCast_ne_top _)
  have hx0 := hK r k (le_trans (Finset.le_sup (Finset.mem_univ r)) hk)
  have hlo := (margin_mem hS lookahead L r k hx0).1
  have hle1 : lateAt m f d w lookahead L r k ≤ 1 := by
    unfold lateAt
    split_ifs <;> simp
  by_cases hlate : margin m f d w lookahead L r k
      ≤ blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
  · have e : slowAt m f d w lookahead L r k = 1 := by
      simp [slowAt, lt_of_lt_of_le hlo hlate]
    rw [e]
    exact_mod_cast hle1
  · have e : lateAt m f d w lookahead L r k = 0 := by simp [lateAt, hlate]
    rw [e]
    simp

omit [DecidableEq H] in
/-- The position that is due is a line in the output sample. Its slope is
the rate of the capture device's clock divided by the rate of the playback
device's clock. -/
theorem duePosition_eq (hS : ConstantRates m f d w) (L : ℝ) (r : Fin R) (k : ℕ) :
    duePosition m f d w L r k
      = duePosition m f d w L r 0
        + Real.exp (d.deviceLogRate none) / Real.exp (d.deviceLogRate (some (m.device r)))
          * k := by
  have hρ := m.rate_pos.ne'
  have hg := (Real.exp_pos (d.deviceLogRate (some (m.device r)))).ne'
  simp only [duePosition]
  rw [hS.out, hS.out]
  push_cast
  field_simp
  ring

omit [DecidableEq H] in
/-- **The cost of playing the positions that are due, or nothing.** In a
world whose clocks run at constant rates, consider a playback in which, from
some output sample on, every position played is the position that is due at
the level `L`. Its cost is at most the costs of the speakers' latencies in
synchronization, latency and tracking, plus the weighted long-run numbers of
its missed samples and of its discontinuities. Roughness costs nothing. -/
theorem cost_le_of_duePositions (hS : ConstantRates m f d w) (L : ℝ)
    {plays : Fin R → ℕ → Option ℝ} {K₀ : ℕ}
    (hdue : ∀ r k, K₀ ≤ k → ∀ x, plays r k = some x → x = duePosition m f d w L r k)
    (c : Weights) :
    w.cost plays c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + (c.missed : ℝ≥0∞) * w.missed plays
        + (c.discontinuities : ℝ≥0∞) * w.discontinuities plays := by
  have honly : w.PlaysOnlyAtLatencies plays (latencyOf m f d L) K₀ := by
    intro r k hk x hx
    rw [hdue r k hk x hx, captured_duePosition hS]
  have hcap : ∀ x : ℝ, w.captured x
      = (f.captureStart - d.offset m.sender) / Real.exp (d.logRate m.sender)
        + x / (m.rate * Real.exp (d.deviceLogRate none)) := hS.captured
  have htarget : ∀ n, w.target n = m.targetLatency := hS.builds.target_eq
  have hsync := w.sync_le_of_playsOnly plays honly hcap
  have hlat := w.meanLatency_le_of_playsOnly plays honly hcap
  have htrack := w.tracking_le_of_playsOnly plays honly hcap htarget
  have hrough := w.roughness_eq_zero_of_playsOnly plays honly
  calc w.cost plays c
      ≤ c.sync * w.sync plays + c.latency * w.meanLatency plays
        + c.tracking * w.tracking plays + c.roughness * w.roughness plays
        + c.missed * w.missed plays + c.discontinuities * w.discontinuities plays :=
        w.cost_le plays c
    _ ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + (c.roughness : ℝ≥0∞) * 0
        + (c.missed : ℝ≥0∞) * w.missed plays
        + (c.discontinuities : ℝ≥0∞) * w.discontinuities plays := by
        rw [hrough]
        gcongr
    _ = (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + (c.missed : ℝ≥0∞) * w.missed plays
        + (c.discontinuities : ℝ≥0∞) * w.discontinuities plays := by
        ring

omit [DecidableEq H] in
/-- **The cost of playing the position that is due exactly when its block
is on time.** In a world whose clocks run at constant rates, consider a
playback in which, from some output sample on, each output sample of each
speaker plays the position that is due at the level `L` if the message of
the capture block that it needs takes less than the sample's margin, and
nothing of the source otherwise. Suppose that the capture device's clock
runs less than twice as fast as the clock of every playback device, and
faster by a fraction of at most `δ`. Then the cost is at most the costs of
the speakers' latencies in synchronization, latency and tracking, plus the
weight of missed samples times `1 + 2 δ`, plus the weight of
discontinuities, times the late rate. -/
theorem cost_le_of_plays_margin (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ)
    {plays : Fin R → ℕ → Option ℝ} {K₀ : ℕ}
    (hpl : ∀ r k, K₀ ≤ k →
      plays r k
        = if blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
            < margin m f d w lookahead L r k
          then some (duePosition m f d w L r k) else none)
    (hratio : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) < 2)
    {δ : ℝ≥0} (hδ : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1 ≤ δ) (c : Weights) :
    w.cost plays c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * lateRate m f d w lookahead L := by
  -- Whatever a late output sample plays is the position that is due.
  have hdue : ∀ r k, K₀ ≤ k → ∀ x, plays r k = some x → x = duePosition m f d w L r k := by
    intro r k hk x hx
    rw [hpl r k hk] at hx
    split_ifs at hx with h
    exact (Option.some.inj hx).symm
  -- The positions that are due lie on a line in the output sample.
  have hlinepos : ∀ r k, K₀ ≤ k → ∀ x, plays r k = some x →
      x = duePosition m f d w L r 0
        + Real.exp (d.deviceLogRate none) / Real.exp (d.deviceLogRate (some (m.device r)))
          * k := by
    intro r k hk x hx
    rw [hdue r k hk x hx]
    exact duePosition_eq hS L r k
  have hc : ∀ r, 0 < Real.exp (d.deviceLogRate none)
        / Real.exp (d.deviceLogRate (some (m.device r)))
      ∧ Real.exp (d.deviceLogRate none)
        / Real.exp (d.deviceLogRate (some (m.device r))) < 2 :=
    fun r => ⟨div_pos (Real.exp_pos _) (Real.exp_pos _), hratio r⟩
  have hout : ∀ r (T : Time), ∃ k, T ≤ (w.speaker r).out k := by
    intro r T
    obtain ⟨b, hb⟩ := hS.asked_unbounded r T
    exact ⟨(w.speaker r).first b, (hb.trans ((w.speaker r).asked_before b)).le⟩
  have hmissed := w.missed_le_of_line plays hlinepos hc hδ hout
  have hdisc := w.discontinuities_le_of_line plays hlinepos hc hout
  -- An output sample plays nothing exactly when it is late.
  have hlate : longRun (w.accruedOutputs fun r k => (missingAt (plays r) k : ℝ≥0∞))
      ≤ lateRate m f d w lookahead L := by
    unfold lateRate
    refine w.longRun_outputs_le K₀ (fun r k hk => ?_) (fun r k => ENNReal.natCast_ne_top _)
    have hp := hpl r k hk
    by_cases hd : blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
        < margin m f d w lookahead L r k
    · have e : missingAt (plays r) k = 0 := by simp [missingAt, hp, hd]
      rw [e]
      simp
    · have e1 : missingAt (plays r) k = 1 := by simp [missingAt, hp, hd]
      have e2 : lateAt m f d w lookahead L r k = 1 := by simp [lateAt, not_lt.mp hd]
      rw [e1, e2]
  have hmissed' : w.missed plays
      ≤ ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) * lateRate m f d w lookahead L :=
    hmissed.trans (by gcongr)
  have hdisc' : w.discontinuities plays ≤ lateRate m f d w lookahead L := hdisc.trans hlate
  calc w.cost plays c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + (c.missed : ℝ≥0∞) * w.missed plays
        + (c.discontinuities : ℝ≥0∞) * w.discontinuities plays :=
        cost_le_of_duePositions hS L hdue c
    _ ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + (c.missed : ℝ≥0∞) * (((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) * lateRate m f d w lookahead L)
        + (c.discontinuities : ℝ≥0∞) * lateRate m f d w lookahead L := by
        gcongr
    _ = (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * lateRate m f d w lookahead L := by
        ring

omit [DecidableEq H] in
/-- **The cost of playing positions that are due, at any rates of the
devices' clocks.** In a world whose clocks run at constant rates, consider a
playback in which, from some output sample on, every position played is the
position that is due at the level `L`. Suppose that the capture device's
clock runs faster than the clock of each playback device by a fraction of at
most `δ`. Then the cost is at most the costs of the speakers' latencies in
synchronization, latency and tracking, plus the weight of missed samples
times `1 + 2 δ`, plus the weight of discontinuities, times the number of
output samples per second in true time, averaged over the speakers. -/
theorem cost_le_outputs_of_plays_due (hS : ConstantRates m f d w) (L : ℝ)
    {plays : Fin R → ℕ → Option ℝ} {K₀ : ℕ}
    (hdue : ∀ r k, K₀ ≤ k → ∀ x, plays r k = some x → x = duePosition m f d w L r k)
    {δ : ℝ≥0} (hδ : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1 ≤ δ) (c : Weights) :
    w.cost plays c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
            (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))) := by
  have hlinepos : ∀ r k, K₀ ≤ k → ∀ x, plays r k = some x →
      x = duePosition m f d w L r 0
        + Real.exp (d.deviceLogRate none) / Real.exp (d.deviceLogRate (some (m.device r)))
          * k := by
    intro r k hk x hx
    rw [hdue r k hk x hx]
    exact duePosition_eq hS L r k
  have hc : ∀ r, 0 < Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) :=
    fun r => div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hout : ∀ r (T : Time), ∃ k, T ≤ (w.speaker r).out k := by
    intro r T
    obtain ⟨b, hb⟩ := hS.asked_unbounded r T
    exact ⟨(w.speaker r).first b, (hb.trans ((w.speaker r).asked_before b)).le⟩
  have hrate : longRun (w.accruedOutputs fun _ _ => 1)
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
        (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) :=
    w.longRun_outputs_le_rate
      (a := fun r => (f.speakerStart (m.device r) - d.offset (m.host r))
        / Real.exp (d.logRate (m.host r)))
      (s := fun r => m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
      (fun r => mul_pos m.rate_pos (Real.exp_pos _)) (fun r k => hS.out r k)
  have hmissed : w.missed plays
      ≤ ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
        (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))) :=
    (w.missed_le_of_slope plays hlinepos hc hδ hout).trans (by gcongr)
  have hdisc : w.discontinuities plays
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
        (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) :=
    (w.discontinuities_le_outputs plays).trans hrate
  calc w.cost plays c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + (c.missed : ℝ≥0∞) * w.missed plays
        + (c.discontinuities : ℝ≥0∞) * w.discontinuities plays :=
        cost_le_of_duePositions hS L hdue c
    _ ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + (c.missed : ℝ≥0∞) * (((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
            (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))))
        + (c.discontinuities : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
            (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))) := by
        gcongr
    _ = (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
            (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))) := by
        ring

/-- **What the controller plays at a held level.** Consider a world whose
clocks run at constant rates, with exact timestamps and with pauses of links
and of hosts, in which no speaker is on the sender's host. The controller
uses a device estimator that is exact on undisturbed reports and holds the
level at `L`, and from some true time on the estimate of the sender's clock
at every speaker's host is the line of its undelayed exchanges. Then from
some output sample on, each output sample of each speaker plays the position
that is due if the message of the capture block that it needs takes less
than the sample's margin, and nothing of the source otherwise. -/
theorem exists_plays_heldLevel (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hline : ∀ r, ∃ T₀, ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w
      lookahead clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K₀, ∀ r k, K₀ ≤ k →
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
          lookahead r k
        = if blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
            < margin m f d w lookahead L r k
          then some (duePosition m f d w L r k) else none := by
  choose T₀ hT₀ using hline
  choose K hK using fun r => plays_eq_of_margin p hS lookahead hdev L hps hnodup hcopies r
    (hnos r) (hpsp r) (hT₀ r)
  exact ⟨Finset.univ.sup K, fun r k hk =>
    (hK r k ((Finset.le_sup (Finset.mem_univ r)).trans hk)).2⟩

/-- **The cost of a held level when links and hosts pause.** Consider a
world whose clocks run at constant rates, with exact timestamps and with
pauses of links and of hosts, in which no speaker is on the sender's host.
The controller uses a device estimator that is exact on undisturbed reports
and holds the level at `L`, and from some true time on the estimate of the
sender's clock at every speaker's host is the line of its undelayed
exchanges. Suppose that the capture device's clock runs less than twice as
fast as the clock of every playback device, and faster by a fraction of at
most `δ`. Then the cost is at most the costs of the speakers' latencies in
synchronization, latency and tracking, plus the weight of missed samples
times `1 + 2 δ`, plus the weight of discontinuities, times the late rate. -/
theorem cost_le_of_heldLevel (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hline : ∀ r, ∃ T₀, ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w
      lookahead clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀)
    (hratio : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) < 2)
    {δ : ℝ≥0} (hδ : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1 ≤ δ) (c : Weights) :
    (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).cost w lookahead c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * lateRate m f d w lookahead L := by
  obtain ⟨K₀, hK₀⟩ := exists_plays_heldLevel p hS lookahead hdev L hps hnodup hcopies hnos hpsp
    hline
  exact cost_le_of_plays_margin hS lookahead L hK₀ hratio hδ c

/-- **The cost of a held level at any rates of the devices' clocks.**
Consider the world and the controller of `cost_le_of_heldLevel`, without the
condition that the capture device's clock runs less than twice as fast as
the clock of every playback device. Suppose that it runs faster than each by
a fraction of at most `δ`. Then the cost is at most the costs of the
speakers' latencies in synchronization, latency and tracking, plus the
weight of missed samples times `1 + 2 δ`, plus the weight of
discontinuities, times the number of output samples per second in true
time, averaged over the speakers. -/
theorem cost_le_outputs_of_heldLevel (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hline : ∀ r, ∃ T₀, ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w
      lookahead clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀)
    {δ : ℝ≥0} (hδ : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1 ≤ δ) (c : Weights) :
    (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).cost w lookahead c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
            (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))) := by
  obtain ⟨K₀, hK₀⟩ := exists_plays_heldLevel p hS lookahead hdev L hps hnodup hcopies hnos hpsp
    hline
  refine cost_le_outputs_of_plays_due hS L (K₀ := K₀) (fun r k hk x hx => ?_) hδ c
  rw [hK₀ r k hk] at hx
  split_ifs at hx with h
  exact (Option.some.inj hx).symm

/-- **The cost of a held level under pauses, with the least-round-trip
estimator.** The bound of `cost_le_of_heldLevel` for the controller that
uses the least-round-trip estimator for the sender's clock and the
two-report estimator for the devices, once two clock exchanges of every
speaker's host were not delayed. -/
theorem cost_le_under_pauses (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hund : ∀ r, ∃ n₀, TwoUndelayed (solution p leastRoundTrip twoReports (constantLevel L)) w
      lookahead m f d (m.host r) n₀)
    (hratio : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) < 2)
    {δ : ℝ≥0} (hδ : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1 ≤ δ) (c : Weights) :
    (solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).cost w
        lookahead c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * lateRate m f d w lookahead L :=
  cost_le_of_heldLevel p hS lookahead twoReports_exact L hps hnodup hcopies hnos hpsp
    (fun r => by
      obtain ⟨n₀, hn₀⟩ := hund r
      exact ⟨_, clockLineFrom_of_undelayed p hS lookahead leastRoundTrip_exactFromLeast
        twoReports (constantLevel L) hps hn₀⟩)
    hratio hδ c

/-- **The cost of a held level under pauses at any rates of the devices'
clocks, with the least-round-trip estimator.** The bound of
`cost_le_outputs_of_heldLevel` for the controller that uses the
least-round-trip estimator for the sender's clock and the two-report
estimator for the devices, once two clock exchanges of every speaker's host
were not delayed. -/
theorem cost_le_outputs_under_pauses (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hund : ∀ r, ∃ n₀, TwoUndelayed (solution p leastRoundTrip twoReports (constantLevel L)) w
      lookahead m f d (m.host r) n₀)
    {δ : ℝ≥0} (hδ : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1 ≤ δ) (c : Weights) :
    (solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).cost w
        lookahead c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
            (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))) :=
  cost_le_outputs_of_heldLevel p hS lookahead twoReports_exact L hps hnodup hcopies hnos hpsp
    (fun r => by
      obtain ⟨n₀, hn₀⟩ := hund r
      exact ⟨_, clockLineFrom_of_undelayed p hS lookahead leastRoundTrip_exactFromLeast
        twoReports (constantLevel L) hps hn₀⟩)
    hδ c

end Unisono.Solutions.Controller
