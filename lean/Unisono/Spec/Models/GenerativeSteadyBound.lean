/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeLevelProgram
public import Unisono.Spec.Models.GenerativePauses

/-!
# The lower bound for clocks at constant rates, in closed form

`lintegral_fixedClockBound_le` bounds the expected cost of a solution from
below by the mean of `fixedClockBound`, the largest value over the valid
choices for the clocks of each outcome. This file constructs valid choices
when the clocks of the hosts and of the audio devices run at constant rates
(`ConstantRates`), and evaluates what they give.

* `capturePeriodOf`, `outputPeriodOf`, `leadOf`: the time between two
  captured frames, the time between two output samples of a speaker, and
  the time from the request of a playback block to its first output sample,
  in true time, as functions of the draw.
* `steadyChoices`, `steadyChoices_valid`: the choices and
  their validity.
* `steadyRate`, `steadyBound`: the bound in closed form, a function of the
  draw.
* `ConstantRates.steadyBound_le`: `steadyBound` is at most
  `fixedClockBound`.
* `lintegral_steadyBound_le`: in every random world of a member whose
  clocks do not wander and whose audio devices report exact timestamps, the
  expected cost of a solution of the compared class with measurable
  playback is at least the mean of `steadyBound`.

Which outcomes: the members with steady clocks (`Member.SteadyClocks`);
links and hosts pause with any laws, and the rates of the clocks are
spread. Members whose clocks wander are not covered by the closed form:
for them only `lintegral_fixedClockBound_le` holds so far. This is a lower
bound, not a statement that a solution is optimal.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R}

/-- The time between two captured frames in true time, when the clock of
the capture device runs at a constant rate. -/
def capturePeriodOf (m : GenerativeWorld H R) (d : Draw H R) : ℝ :=
  1 / (m.rate * Real.exp (d.deviceLogRate none))

/-- The time between two output samples of speaker `r` in true time, when
the clock of its playback device runs at a constant rate. -/
def outputPeriodOf (m : GenerativeWorld H R) (d : Draw H R) (r : Fin R) : ℝ :=
  1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))

/-- The true time from the request of a playback block of speaker `r` to
its first output sample, when the clock of its playback device runs at a
constant rate. -/
def leadOf (m : GenerativeWorld H R) (d : Draw H R) (r : Fin R) : ℝ :=
  m.lead / Real.exp (d.deviceLogRate (some (m.device r)))

theorem capturePeriodOf_pos (m : GenerativeWorld H R) (d : Draw H R) :
    0 < capturePeriodOf m d :=
  one_div_pos.mpr (mul_pos m.rate_pos (Real.exp_pos _))

theorem outputPeriodOf_pos (m : GenerativeWorld H R) (d : Draw H R) (r : Fin R) :
    0 < outputPeriodOf m d r :=
  one_div_pos.mpr (mul_pos m.rate_pos (Real.exp_pos _))

theorem leadOf_pos (m : GenerativeWorld H R) (d : Draw H R) (r : Fin R) : 0 < leadOf m d r :=
  div_pos m.lead_pos (Real.exp_pos _)

/-- With clocks at constant rates, two frames in a row are captured
`capturePeriodOf` apart. -/
theorem ConstantRates.capture_succ_sub (hS : ConstantRates m f d w) (n : ℕ) :
    w.source.capture (n + 1) - w.source.capture n = capturePeriodOf m d := by
  rw [hS.capture, hS.capture]
  unfold capturePeriodOf
  push_cast
  ring

/-- With clocks at constant rates, output sample `k` of speaker `r` leaves
`k` times `outputPeriodOf` after output sample `0`. -/
theorem ConstantRates.out_eq (hS : ConstantRates m f d w) (r : Fin R) (k : ℕ) :
    (w.speaker r).out k = (w.speaker r).out 0 + (k : ℝ) * outputPeriodOf m d r := by
  rw [hS.out r k, hS.out r 0]
  unfold outputPeriodOf
  push_cast
  ring

/-- With clocks at constant rates, the requests of the playback blocks of
speaker `r` are `blockSize * outputPeriodOf` apart. -/
theorem ConstantRates.asked_eq (hS : ConstantRates m f d w) (r : Fin R) (b : ℕ) :
    (w.speaker r).asked b = (w.speaker r).out 0 - leadOf m d r
      + (b : ℝ) * ((m.blockSize : ℝ) * outputPeriodOf m d r) := by
  have h := hS.asked r b
  rw [hS.builds.speaker_first, hS.out_eq r (b * m.blockSize)] at h
  unfold leadOf
  push_cast at h
  linarith

/-- The horizons that are used for clocks at constant rates: one second
apart, the first later than the first output sample of every speaker of
`𝒮`. -/
def steadyHorizon (w : World H R) (𝒮 : Finset (Fin R)) (n : ℕ) : ℝ :=
  (n : ℝ) + 1 + ∑ r ∈ 𝒮, |(w.speaker r).out 0|

/-- The largest number `N` of playback blocks of speaker `r` such that the
first output sample of block `N` leaves before `T`, if there is one. -/
def blocksBefore (m : GenerativeWorld H R) (w : World H R) (r : Fin R) (T : ℝ) : ℕ :=
  firstFrom (fun N : ℕ => (w.speaker r).out (N * m.blockSize)) T - 1

/-- With clocks at constant rates and `T` after the first output sample of
speaker `r`: the first output sample of block `blocksBefore` leaves before
`T`, and that of the next block at or after `T`. -/
theorem blocksBefore_spec (hS : ConstantRates m f d w) (r : Fin R) {T : ℝ}
    (hT : (w.speaker r).out 0 < T) :
    (w.speaker r).out (blocksBefore m w r T * m.blockSize) < T
      ∧ T ≤ (w.speaker r).out ((blocksBefore m w r T + 1) * m.blockSize) := by
  have hA : 0 < (m.blockSize : ℝ) * outputPeriodOf m d r :=
    mul_pos (by exact_mod_cast m.blockSize_pos) (outputPeriodOf_pos m d r)
  have hex : ∃ N : ℕ, T ≤ (fun N : ℕ => (w.speaker r).out (N * m.blockSize)) N := by
    obtain ⟨N, hN⟩ := exists_nat_ge
      ((T - (w.speaker r).out 0) / ((m.blockSize : ℝ) * outputPeriodOf m d r))
    refine ⟨N, ?_⟩
    show T ≤ (w.speaker r).out (N * m.blockSize)
    rw [hS.out_eq]
    push_cast
    have h1 := (div_le_iff₀ hA).mp hN
    linarith
  have hpos : 0 < firstFrom (fun N : ℕ => (w.speaker r).out (N * m.blockSize)) T := by
    by_contra h0
    have h1 := le_asked_firstFrom hex
    rw [Nat.eq_zero_of_not_pos h0] at h1
    have h2 : T ≤ (w.speaker r).out (0 * m.blockSize) := h1
    rw [Nat.zero_mul] at h2
    linarith
  unfold blocksBefore
  refine ⟨asked_lt_of_lt_firstFrom hex (Nat.sub_lt hpos Nat.one_pos), ?_⟩
  rw [Nat.sub_add_cancel hpos]
  exact le_asked_firstFrom hex

/-- **The choices for clocks at constant rates.** The bounds for the audio
devices are the exact periods of the draw `d`; a cell counts a pause when
the link pauses nothing in the `⌈Xmax / ℓ⌉` cells before it; the horizons
are `steadyHorizon`; at each horizon all the playback blocks that begin
before it and all the cells that can be counted (`countedCells`) are
counted. -/
def steadyChoices (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (𝒮 : Finset (Fin R)) (ℓ Xmax Gcap : ℝ) (Nbar : ℕ) (w' : ℝ≥0∞) : CellChoices R where
  longestPause := Xmax
  windowBlocks := Nbar
  clearCells := ⌈Xmax / ℓ⌉₊
  latencyCap := Gcap
  referencePeriod := capturePeriodOf m d
  capturePeriod := fun _ _ => capturePeriodOf m d
  outputPeriod := fun r _ => outputPeriodOf m d r
  pauseWeight := w'
  horizon := steadyHorizon w 𝒮
  blocks := fun n r => blocksBefore m w r (steadyHorizon w 𝒮 n)
  cells := fun n r => countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar
    (blocksBefore m w r (steadyHorizon w 𝒮 n)) ⌈steadyHorizon w 𝒮 n / ℓ⌉₊

theorem steadyHorizon_pos (w : World H R) (𝒮 : Finset (Fin R)) (n : ℕ) :
    1 ≤ steadyHorizon w 𝒮 n := by
  unfold steadyHorizon
  have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : (0 : ℝ) ≤ ∑ r ∈ 𝒮, |(w.speaker r).out 0| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

theorem out_zero_lt_steadyHorizon (w : World H R) {𝒮 : Finset (Fin R)} {r : Fin R}
    (hr : r ∈ 𝒮) (n : ℕ) : |(w.speaker r).out 0| < steadyHorizon w 𝒮 n := by
  unfold steadyHorizon
  have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : |(w.speaker r).out 0| ≤ ∑ r ∈ 𝒮, |(w.speaker r).out 0| :=
    Finset.single_le_sum (f := fun r => |(w.speaker r).out 0|) (fun _ _ => abs_nonneg _) hr
  linarith

/-- **The choices for clocks at constant rates are valid**, when the set
`𝒮` of speakers is not empty, `ℓ > 0`, `Gcap ≥ 0`, and the weights
satisfy the two conditions of `CellChoices.Valid` for the capture period of
the draw. -/
theorem steadyChoices_valid (hS : ConstantRates m f d w) (c : Weights)
    {𝒮 : Finset (Fin R)} (hne : 𝒮.Nonempty) {s ℓ Gcap : ℝ} (hℓ : 0 < ℓ) (hcap : 0 ≤ Gcap)
    (Xmax : ℝ) (Nbar : ℕ) {w' : ℝ≥0∞}
    (hw1 : (c.latency : ℝ≥0∞) * ENNReal.ofReal (capturePeriodOf m d
        * ((1 + 2 * s) * (2 + 1 / s) * Gcap
          + s * ((m.blockSize : ℝ) - 1) * capturePeriodOf m d * (2 * s + 1)))
      + w' ≤ c.missed)
    (hw2 : w' * ENNReal.ofReal s ≤ c.discontinuities) :
    (steadyChoices m f d w 𝒮 ℓ Xmax Gcap Nbar w').Valid m f d w c 𝒮 s ℓ := by
  have hpc := capturePeriodOf_pos m d
  have hBpos : (0 : ℝ) < (m.blockSize : ℝ) := by exact_mod_cast m.blockSize_pos
  have hA : ∀ r, 0 < (m.blockSize : ℝ) * outputPeriodOf m d r := fun r =>
    mul_pos hBpos (outputPeriodOf_pos m d r)
  have hTpos : ∀ n, 0 < steadyHorizon w 𝒮 n := fun n =>
    lt_of_lt_of_le one_pos (steadyHorizon_pos w 𝒮 n)
  have hTr : ∀ n, ∀ r ∈ 𝒮, (w.speaker r).out 0 < steadyHorizon w 𝒮 n := fun n r hr =>
    lt_of_le_of_lt (le_abs_self _) (out_zero_lt_steadyHorizon w hr n)
  refine
    { longestPause_le := ?_
      latencyCap_nonneg := hcap
      referencePeriod_nonneg := hpc.le
      capturePeriod_nonneg := fun _ _ _ => hpc.le
      capturePeriod_le := fun _ _ _ => le_rfl
      out_sub_le := fun r _ b k _ _ => ?_
      le_capture_sub := fun _ _ _ i _ _ => (hS.capture_succ_sub i).ge
      missed_ge := hw1
      discontinuities_ge := hw2
      horizon_tendsto := ?_
      horizon_pos := hTpos
      out_lt_horizon := fun n r hr => (blocksBefore_spec hS r (hTr n r hr)).1
      cells_spec := fun n r _ j hj => ?_
      bounded := ?_ }
  · show Xmax ≤ (((⌈Xmax / ℓ⌉₊ : ℕ) : ℝ) + 1) * ℓ
    have h1 := (div_le_iff₀ hℓ).mp (Nat.le_ceil (Xmax / ℓ))
    nlinarith
  · show (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ outputPeriodOf m d r
    rw [hS.out_eq r (k + 1), hS.out_eq r k]
    push_cast
    linarith
  · show Tendsto (steadyHorizon w 𝒮) atTop atTop
    unfold steadyHorizon
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_add
      tendsto_const_nhds
  · obtain ⟨-, h1, h2, h3⟩ := mem_countedCells.mp hj
    exact ⟨h1, h2, h3⟩
  · obtain ⟨r₀, -⟩ := hne
    have hR : (R : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (by exact_mod_cast (Nat.pos_iff_ne_zero.mp (Fin.pos r₀)))
    have hw' : w' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (le_trans le_add_self hw1)
    refine ⟨(R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ENNReal.ofReal (1 / ℓ + 1)
      * ((c.latency : ℝ≥0∞) * ENNReal.ofReal
          (ℓ / ((m.blockSize : ℝ) * outputPeriodOf m d r)
            * (capturePeriodOf m d * (s * ((m.blockSize : ℝ) - 1) * Gcap)))
        + w' * ENNReal.ofReal (s * ((Nbar : ℝ) * m.blockSize))), ?_, fun n => ?_⟩
    · exact ENNReal.mul_ne_top hR (ENNReal.sum_ne_top.mpr fun r _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
          ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top,
            ENNReal.mul_ne_top hw' ENNReal.ofReal_ne_top⟩))
    · have hper : ∀ r ∈ 𝒮, cellsCap m w r s ℓ (leastDelayTo m f d r)
            (fun _ => capturePeriodOf m d) Gcap (c.latency : ℝ≥0∞) Nbar w'
            (countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar
              (blocksBefore m w r (steadyHorizon w 𝒮 n)) ⌈steadyHorizon w 𝒮 n / ℓ⌉₊)
          ≤ ENNReal.ofReal (steadyHorizon w 𝒮 n) * (ENNReal.ofReal (1 / ℓ + 1)
            * ((c.latency : ℝ≥0∞) * ENNReal.ofReal
                (ℓ / ((m.blockSize : ℝ) * outputPeriodOf m d r)
                  * (capturePeriodOf m d * (s * ((m.blockSize : ℝ) - 1) * Gcap)))
              + w' * ENNReal.ofReal (s * ((Nbar : ℝ) * m.blockSize)))) := by
        intro r _
        unfold cellsCap
        have hterm : ∀ j ∈ countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar
            (blocksBefore m w r (steadyHorizon w 𝒮 n)) ⌈steadyHorizon w 𝒮 n / ℓ⌉₊,
            (c.latency : ℝ≥0∞) * ENNReal.ofReal
                (ℓ / ((w.speaker r).asked (cellBlock w r ℓ (leastDelayTo m f d r) j)
                    - (w.speaker r).asked (cellBlock w r ℓ (leastDelayTo m f d r) j - 1))
                  * (capturePeriodOf m d * (s * ((m.blockSize : ℝ) - 1) * Gcap)))
              + w' * ENNReal.ofReal (s * ((Nbar : ℝ) * m.blockSize))
            = (c.latency : ℝ≥0∞) * ENNReal.ofReal
                (ℓ / ((m.blockSize : ℝ) * outputPeriodOf m d r)
                  * (capturePeriodOf m d * (s * ((m.blockSize : ℝ) - 1) * Gcap)))
              + w' * ENNReal.ofReal (s * ((Nbar : ℝ) * m.blockSize)) := by
          intro j hj
          obtain ⟨-, h1, -, -⟩ := mem_countedCells.mp hj
          have h1' : 1 ≤ cellBlock w r ℓ (leastDelayTo m f d r) j := h1
          have hgap : (w.speaker r).asked (cellBlock w r ℓ (leastDelayTo m f d r) j)
              - (w.speaker r).asked (cellBlock w r ℓ (leastDelayTo m f d r) j - 1)
              = (m.blockSize : ℝ) * outputPeriodOf m d r := by
            rw [hS.asked_eq, hS.asked_eq, Nat.cast_sub h1', Nat.cast_one]
            ring
          rw [hgap]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
          ← mul_assoc (ENNReal.ofReal (steadyHorizon w 𝒮 n))]
        refine mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_mul (hTpos n).le, ← ENNReal.ofReal_natCast]
        refine ENNReal.ofReal_le_ofReal ?_
        have hcard : ((countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar
            (blocksBefore m w r (steadyHorizon w 𝒮 n)) ⌈steadyHorizon w 𝒮 n / ℓ⌉₊).card : ℝ)
            ≤ ((⌈steadyHorizon w 𝒮 n / ℓ⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast card_countedCells_le _ _ _ _ _ _
        have hceil := Nat.ceil_lt_add_one (div_nonneg (hTpos n).le hℓ.le)
        have h1 := steadyHorizon_pos w 𝒮 n
        have e : steadyHorizon w 𝒮 n * (1 / ℓ + 1)
            = steadyHorizon w 𝒮 n / ℓ + steadyHorizon w 𝒮 n := by ring
        rw [e]
        linarith
      calc (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, cellsCap m w r s ℓ (leastDelayTo m f d r)
              (fun _ => capturePeriodOf m d) Gcap (c.latency : ℝ≥0∞) Nbar w'
              (countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar
                (blocksBefore m w r (steadyHorizon w 𝒮 n)) ⌈steadyHorizon w 𝒮 n / ℓ⌉₊)
          ≤ (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ENNReal.ofReal (steadyHorizon w 𝒮 n)
              * (ENNReal.ofReal (1 / ℓ + 1)
                * ((c.latency : ℝ≥0∞) * ENNReal.ofReal
                    (ℓ / ((m.blockSize : ℝ) * outputPeriodOf m d r)
                      * (capturePeriodOf m d * (s * ((m.blockSize : ℝ) - 1) * Gcap)))
                  + w' * ENNReal.ofReal (s * ((Nbar : ℝ) * m.blockSize)))) :=
            mul_le_mul' le_rfl (Finset.sum_le_sum hper)
        _ = _ := by
            show _ = _ * ENNReal.ofReal (steadyHorizon w 𝒮 n)
            simp only [← Finset.mul_sum]
            ring

/-- **What a second of true time costs at least at speaker `r`, with clocks
at constant rates**, before the share of the time that the counted cells
cover: `exp (-pauseCount)` times `q` times the level program per second
(`levelValue`) plus `1 - q` times its least latency term (`levelFloor`).
Here `q = exp (-rate * ⌈Xmax / ℓ⌉ * ℓ)` for the rate of the pauses of the
link to the speaker's host, and the level program is taken with the least
delay, the lead and the periods of the draw `d`, and with requests
`blockSize * outputPeriodOf` apart. -/
def steadyRate (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (lookahead : ℕ+)
    (c : Weights) (r : Fin R) (s ℓ Xmax Gcap : ℝ) (Nbar : ℕ) (w' : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(pauseCount m f ℓ r : ℝ)))
    * (ENNReal.ofReal
          (Real.exp (-(f.linkPauseRate m.sender (m.host r) * ((⌈Xmax / ℓ⌉₊ : ℕ) * ℓ))))
        * levelValue m f lookahead r s (leastDelayTo m f d r) (leadOf m d r)
          ((m.blockSize : ℝ) * outputPeriodOf m d r) (capturePeriodOf m d)
          (outputPeriodOf m d r) Gcap (c.latency : ℝ≥0∞) Xmax Nbar w'
      + ENNReal.ofReal
          (1 - Real.exp (-(f.linkPauseRate m.sender (m.host r) * ((⌈Xmax / ℓ⌉₊ : ℕ) * ℓ))))
        * levelFloor m lookahead s (leastDelayTo m f d r) (leadOf m d r)
          ((m.blockSize : ℝ) * outputPeriodOf m d r) (capturePeriodOf m d)
          (outputPeriodOf m d r) Gcap (c.latency : ℝ≥0∞))

/-- `steadyRate` is finite for `s ≥ 0` and a finite weight `w'`. -/
theorem steadyRate_ne_top (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R)
    (lookahead : ℕ+) (c : Weights) (r : Fin R) {s : ℝ} (hs : 0 ≤ s) (ℓ Xmax Gcap : ℝ)
    (Nbar : ℕ) {w' : ℝ≥0∞} (hw' : w' ≠ ⊤) :
    steadyRate m f d lookahead c r s ℓ Xmax Gcap Nbar w' ≠ ⊤ := by
  have hV := levelValue_ne_top m f lookahead r hs (leastDelayTo m f d r) (leadOf m d r)
    ((m.blockSize : ℝ) * outputPeriodOf m d r) (capturePeriodOf m d) (outputPeriodOf m d r)
    Gcap (cl := (c.latency : ℝ≥0∞)) ENNReal.coe_ne_top Xmax Nbar hw'
  have hF := ne_top_of_le_ne_top hV (levelFloor_le_levelValue m f lookahead r s
    (leastDelayTo m f d r) (leadOf m d r) ((m.blockSize : ℝ) * outputPeriodOf m d r)
    (capturePeriodOf m d) (outputPeriodOf m d r) Gcap (c.latency : ℝ≥0∞) Xmax Nbar w')
  unfold steadyRate
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF⟩)

/-- **With clocks at constant rates, a counted cell is worth at least its
length times `steadyRate`.** -/
theorem mul_steadyRate_le (hS : ConstantRates m f d w) (lookahead : ℕ+)
    (c : Weights) (r : Fin R) {s ℓ Gcap : ℝ} (hs : 0 ≤ s) (hℓ : 0 < ℓ) (hcap : 0 ≤ Gcap)
    (Xmax : ℝ) (Nbar : ℕ) (w' : ℝ≥0∞) {N K j : ℕ}
    (hj : j ∈ countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar N K) :
    ENNReal.ofReal ℓ * steadyRate m f d lookahead c r s ℓ Xmax Gcap Nbar w'
      ≤ ENNReal.ofReal (Real.exp (-(pauseCount m f ℓ r : ℝ)))
        * (ENNReal.ofReal
              (Real.exp (-(f.linkPauseRate m.sender (m.host r) * ((⌈Xmax / ℓ⌉₊ : ℕ) * ℓ))))
            * cellValue m f d w lookahead r s ℓ (leastDelayTo m f d r)
              (fun _ => capturePeriodOf m d) (fun _ => outputPeriodOf m d r) Gcap
              (c.latency : ℝ≥0∞) Xmax Nbar (pauseCount m f ℓ r) w' j
          + ENNReal.ofReal
              (1 - Real.exp (-(f.linkPauseRate m.sender (m.host r) * ((⌈Xmax / ℓ⌉₊ : ℕ) * ℓ))))
            * cellFloor m f d w lookahead r s ℓ (leastDelayTo m f d r)
              (fun _ => capturePeriodOf m d) (fun _ => outputPeriodOf m d r) Gcap
              (c.latency : ℝ≥0∞) j) := by
  obtain ⟨-, h1, -, h3⟩ := mem_countedCells.mp hj
  obtain ⟨b, hb⟩ : ∃ b, cellBlock w r ℓ (leastDelayTo m f d r) j = b := ⟨_, rfl⟩
  have hb' : firstFrom (w.speaker r).asked (((j : ℝ) + 1) * ℓ + leastDelayTo m f d r) = b := hb
  rw [hb'] at h1 h3
  have hA : 0 < (m.blockSize : ℝ) * outputPeriodOf m d r :=
    mul_pos (by exact_mod_cast m.blockSize_pos) (outputPeriodOf_pos m d r)
  have hgapeq : (w.speaker r).asked b - (w.speaker r).asked (b - 1)
      = (m.blockSize : ℝ) * outputPeriodOf m d r := by
    rw [hS.asked_eq, hS.asked_eq, Nat.cast_sub h1, Nat.cast_one]
    ring
  have hleadeq : (w.speaker r).out (b * m.blockSize) - (w.speaker r).asked b
      = leadOf m d r := by
    rw [hS.out_eq, hS.asked_eq]
    push_cast
    ring
  have hfirst : (w.speaker r).asked b
      ≤ (j : ℝ) * ℓ + leastDelayTo m f d r + (m.blockSize : ℝ) * outputPeriodOf m d r := by
    have h4 := h3 (b - 1) (Nat.sub_lt h1 Nat.one_pos)
    linarith
  have hspace : ∀ i, i < Nbar → (w.speaker r).asked (b + i)
      ≤ (w.speaker r).asked b + (i : ℝ) * ((m.blockSize : ℝ) * outputPeriodOf m d r) := by
    intro i _
    rw [hS.asked_eq, hS.asked_eq]
    push_cast
    exact le_of_eq (by ring)
  have hgap0 : 0 < (w.speaker r).asked b - (w.speaker r).asked (b - 1) := by
    rw [hgapeq]
    exact hA
  have hV := mul_levelValue_le_cellValue m f d w lookahead r hs hℓ.le hA
    (capturePeriodOf_pos m d).le hcap (pc := fun _ => capturePeriodOf m d)
    (pr := fun _ => outputPeriodOf m d r) (c.latency : ℝ≥0∞) Xmax Nbar w' hb h1 rfl rfl hgap0
    hgapeq.le hleadeq.ge hfirst hspace
  have hF := mul_levelFloor_le_cellFloor m f d w lookahead r hs hℓ.le hA
    (capturePeriodOf_pos m d).le hcap (pc := fun _ => capturePeriodOf m d)
    (pr := fun _ => outputPeriodOf m d r) (c.latency : ℝ≥0∞) hb h1 rfl rfl hgap0 hgapeq.le
    hleadeq.ge
  unfold steadyRate
  refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl
    (add_le_add (mul_le_mul' le_rfl hV) (mul_le_mul' le_rfl hF)))
  ring

open Classical in
/-- **The lower bound for clocks at constant rates, in closed form**, as a
function of the draw `d`. If the weight of missed samples covers the weight
of latency times the losses of the blocks, for the capture period of the
draw, plus `w'`: the average over the speakers of `𝒮` of the share
`1 - ℓ / (blockSize * outputPeriodOf)` of the time that the counted cells
cover times `steadyRate`, minus the weight of latency times the average of
`capturePeriodOf * (1 + s) * Gcap` for each playback block per second.
Otherwise zero. -/
def steadyBound (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (lookahead : ℕ+)
    (c : Weights) (𝒮 : Finset (Fin R)) (s ℓ Xmax Gcap : ℝ) (Nbar : ℕ) (w' : ℝ≥0∞) : ℝ≥0∞ :=
  if (c.latency : ℝ≥0∞) * ENNReal.ofReal (capturePeriodOf m d
        * ((1 + 2 * s) * (2 + 1 / s) * Gcap
          + s * ((m.blockSize : ℝ) - 1) * capturePeriodOf m d * (2 * s + 1)))
      + w' ≤ c.missed then
    (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
        ENNReal.ofReal (1 - ℓ / ((m.blockSize : ℝ) * outputPeriodOf m d r))
          * steadyRate m f d lookahead c r s ℓ Xmax Gcap Nbar w'
      - (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
          ENNReal.ofReal (capturePeriodOf m d * ((1 + s) * Gcap)
            / ((m.blockSize : ℝ) * outputPeriodOf m d r)))
  else 0

/-- **With clocks at constant rates, the closed form is at most the lower
bound for fixed clocks.** For `s ≥ 0`, cells of length `ℓ > 0`, a cap
`Gcap ≥ 0`, and a weight `w'` of a pause with
`w' * s ≤` the weight of discontinuities. -/
theorem ConstantRates.steadyBound_le (hS : ConstantRates m f d w) (lookahead : ℕ+)
    (c : Weights) (𝒮 : Finset (Fin R)) {s ℓ Gcap : ℝ} (hs : 0 ≤ s) (hℓ : 0 < ℓ)
    (hcap : 0 ≤ Gcap) (Xmax : ℝ) (Nbar : ℕ) {w' : ℝ≥0∞}
    (hw2 : w' * ENNReal.ofReal s ≤ c.discontinuities) :
    steadyBound m f d lookahead c 𝒮 s ℓ Xmax Gcap Nbar w'
      ≤ fixedClockBound m f d w lookahead c 𝒮 s ℓ := by
  classical
  unfold steadyBound
  split_ifs with hw1
  swap
  · exact zero_le
  rcases 𝒮.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.sum_empty, mul_zero, zero_tsub]
    exact zero_le
  have hvalid := steadyChoices_valid hS c hne hℓ hcap Xmax Nbar hw1 hw2
  refine le_trans ?_ (le_fixedClockBound hvalid lookahead)
  obtain ⟨r₀, -⟩ := hne
  have hR : (R : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (by exact_mod_cast (Nat.pos_iff_ne_zero.mp (Fin.pos r₀)))
  have hw' : w' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (le_trans le_add_self hw1)
  have hpc := capturePeriodOf_pos m d
  have hA : ∀ r, 0 < (m.blockSize : ℝ) * outputPeriodOf m d r := fun r =>
    mul_pos (by exact_mod_cast m.blockSize_pos) (outputPeriodOf_pos m d r)
  have hTpos : ∀ n, 0 < steadyHorizon w 𝒮 n := fun n =>
    lt_of_lt_of_le one_pos (steadyHorizon_pos w 𝒮 n)
  have hdef : ∀ T', w.captureDeficit (capturePeriodOf m d) T' = 0 := by
    intro T'
    unfold World.captureDeficit
    simp only [hS.capture_succ_sub, sub_self, ENNReal.ofReal_zero, ite_self, tsum_zero]
  have hspec : ∀ n, ∀ r ∈ 𝒮,
      (w.speaker r).out 0
          + (blocksBefore m w r (steadyHorizon w 𝒮 n) : ℝ)
            * ((m.blockSize : ℝ) * outputPeriodOf m d r) < steadyHorizon w 𝒮 n
        ∧ steadyHorizon w 𝒮 n ≤ (w.speaker r).out 0
          + ((blocksBefore m w r (steadyHorizon w 𝒮 n) : ℝ) + 1)
            * ((m.blockSize : ℝ) * outputPeriodOf m d r) := by
    intro n r hr
    have h := blocksBefore_spec hS r
      (lt_of_le_of_lt (le_abs_self _) (out_zero_lt_steadyHorizon w hr n))
    have e1 := hS.out_eq r (blocksBefore m w r (steadyHorizon w 𝒮 n) * m.blockSize)
    have e2 := hS.out_eq r ((blocksBefore m w r (steadyHorizon w 𝒮 n) + 1) * m.blockSize)
    push_cast at e1 e2
    constructor <;> linarith [h.1, h.2]
  unfold CellChoices.value
  simp only [steadyChoices]
  refine le_limsup_sub_div (T := steadyHorizon w 𝒮) hvalid.horizon_tendsto hTpos
    (C₁ := (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ENNReal.ofReal (|(w.speaker r).out 0|
        + ((Nbar : ℝ) + 1) * ((m.blockSize : ℝ) * outputPeriodOf m d r)
        + max (leastDelayTo m f d r - ((w.speaker r).out 0 - leadOf m d r)) 0 + 2 * ℓ)
      * steadyRate m f d lookahead c r s ℓ Xmax Gcap Nbar w')
    (C₂ := (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ENNReal.ofReal
      (|(w.speaker r).out 0| * (capturePeriodOf m d * ((1 + s) * Gcap)
        / ((m.blockSize : ℝ) * outputPeriodOf m d r)))))
    ?_ ?_ (fun n => ?_) (fun n => ?_)
  · exact ENNReal.mul_ne_top hR (ENNReal.sum_ne_top.mpr fun r _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (steadyRate_ne_top m f d lookahead c r hs ℓ Xmax Gcap Nbar hw'))
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hR
      (ENNReal.sum_ne_top.mpr fun r _ => ENNReal.ofReal_ne_top))
  · -- The cells, at one horizon.
    have hper : ∀ r ∈ 𝒮, ENNReal.ofReal (steadyHorizon w 𝒮 n)
          * (ENNReal.ofReal (1 - ℓ / ((m.blockSize : ℝ) * outputPeriodOf m d r))
            * steadyRate m f d lookahead c r s ℓ Xmax Gcap Nbar w')
        ≤ ∑ j ∈ countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar
              (blocksBefore m w r (steadyHorizon w 𝒮 n)) ⌈steadyHorizon w 𝒮 n / ℓ⌉₊,
            ENNReal.ofReal (Real.exp (-(pauseCount m f ℓ r : ℝ)))
              * (ENNReal.ofReal (Real.exp
                    (-(f.linkPauseRate m.sender (m.host r) * ((⌈Xmax / ℓ⌉₊ : ℕ) * ℓ))))
                  * cellValue m f d w lookahead r s ℓ (leastDelayTo m f d r)
                    (fun _ => capturePeriodOf m d) (fun _ => outputPeriodOf m d r) Gcap
                    (c.latency : ℝ≥0∞) Xmax Nbar (pauseCount m f ℓ r) w' j
                + ENNReal.ofReal (1 - Real.exp
                    (-(f.linkPauseRate m.sender (m.host r) * ((⌈Xmax / ℓ⌉₊ : ℕ) * ℓ))))
                  * cellFloor m f d w lookahead r s ℓ (leastDelayTo m f d r)
                    (fun _ => capturePeriodOf m d) (fun _ => outputPeriodOf m d r) Gcap
                    (c.latency : ℝ≥0∞) j)
          + ENNReal.ofReal (|(w.speaker r).out 0|
              + ((Nbar : ℝ) + 1) * ((m.blockSize : ℝ) * outputPeriodOf m d r)
              + max (leastDelayTo m f d r - ((w.speaker r).out 0 - leadOf m d r)) 0 + 2 * ℓ)
            * steadyRate m f d lookahead c r s ℓ Xmax Gcap Nbar w' := by
      intro r hr
      obtain ⟨hlt, hle⟩ := hspec n r hr
      have hcells := Finset.card_nsmul_le_sum
        (countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar
          (blocksBefore m w r (steadyHorizon w 𝒮 n)) ⌈steadyHorizon w 𝒮 n / ℓ⌉₊) _ _
        (fun j hj => mul_steadyRate_le hS lookahead c r hs hℓ hcap Xmax Nbar w' hj)
      rw [nsmul_eq_mul] at hcells
      have hδ : 0 < leastDelayTo m f d r := hS.delay_pos m.sender (m.host r)
      have hK : ((w.speaker r).asked (blocksBefore m w r (steadyHorizon w 𝒮 n) - Nbar)
            - leastDelayTo m f d r) / ℓ
          ≤ ((⌈steadyHorizon w 𝒮 n / ℓ⌉₊ : ℕ) : ℝ) := by
        have h1 : (w.speaker r).asked (blocksBefore m w r (steadyHorizon w 𝒮 n) - Nbar)
            ≤ (w.speaker r).asked (blocksBefore m w r (steadyHorizon w 𝒮 n)) :=
          (w.speaker r).asked_strictMono.monotone (Nat.sub_le _ _)
        have h2 := hS.asked_eq r (blocksBefore m w r (steadyHorizon w 𝒮 n))
        have h3 := leadOf_pos m d r
        have h4 : (w.speaker r).asked (blocksBefore m w r (steadyHorizon w 𝒮 n) - Nbar)
            - leastDelayTo m f d r ≤ steadyHorizon w 𝒮 n := by linarith
        exact le_trans (div_le_div_of_nonneg_right h4 hℓ.le) (Nat.le_ceil _)
      have hcount : ENNReal.ofReal (steadyHorizon w 𝒮 n)
            * ENNReal.ofReal (1 - ℓ / ((m.blockSize : ℝ) * outputPeriodOf m d r))
          ≤ ENNReal.ofReal (((countedCells (w.speaker r).asked ℓ (leastDelayTo m f d r) Nbar
                (blocksBefore m w r (steadyHorizon w 𝒮 n))
                ⌈steadyHorizon w 𝒮 n / ℓ⌉₊).card : ℝ) * ℓ)
            + ENNReal.ofReal (|(w.speaker r).out 0|
              + ((Nbar : ℝ) + 1) * ((m.blockSize : ℝ) * outputPeriodOf m d r)
              + max (leastDelayTo m f d r - ((w.speaker r).out 0 - leadOf m d r)) 0
              + 2 * ℓ) := by
        by_cases hℓA : ℓ ≤ (m.blockSize : ℝ) * outputPeriodOf m d r
        · rw [← ENNReal.ofReal_mul (hTpos n).le]
          refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
          exact mul_le_card_countedCells_mul (hA r) (fun b => hS.asked_eq r b) hℓ hℓA hK hle
        · have h0 : 1 - ℓ / ((m.blockSize : ℝ) * outputPeriodOf m d r) ≤ 0 := by
            rw [sub_nonpos, one_le_div (hA r)]
            exact (not_le.mp hℓA).le
          rw [ENNReal.ofReal_of_nonpos h0, mul_zero]
          exact zero_le
      rw [← mul_assoc]
      refine le_trans (mul_le_mul' hcount le_rfl) ?_
      rw [add_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
      exact add_le_add hcells le_rfl
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul' (le_refl (R : ℝ≥0∞)⁻¹)
      (Finset.sum_le_sum hper)) (le_of_eq ?_))
    · simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    · rw [Finset.sum_add_distrib, mul_add]
  · -- The losses of the blocks, at one horizon.
    have hper : ∀ r ∈ 𝒮, ENNReal.ofReal Gcap
            * w.captureDeficit (capturePeriodOf m d) (steadyHorizon w 𝒮 n)
          + ENNReal.ofReal (capturePeriodOf m d
            * ((blocksBefore m w r (steadyHorizon w 𝒮 n) : ℝ) * ((1 + s) * Gcap)))
        ≤ ENNReal.ofReal (steadyHorizon w 𝒮 n) * ENNReal.ofReal
            (capturePeriodOf m d * ((1 + s) * Gcap)
              / ((m.blockSize : ℝ) * outputPeriodOf m d r))
          + ENNReal.ofReal (|(w.speaker r).out 0| * (capturePeriodOf m d * ((1 + s) * Gcap)
            / ((m.blockSize : ℝ) * outputPeriodOf m d r))) := by
      intro r hr
      obtain ⟨hlt, -⟩ := hspec n r hr
      rw [hdef, mul_zero, zero_add, ← ENNReal.ofReal_mul (hTpos n).le]
      refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
      have hX : 0 ≤ capturePeriodOf m d * ((1 + s) * Gcap) :=
        mul_nonneg hpc.le (mul_nonneg (by linarith) hcap)
      have h1 : (blocksBefore m w r (steadyHorizon w 𝒮 n) : ℝ)
          ≤ (steadyHorizon w 𝒮 n + |(w.speaker r).out 0|)
            / ((m.blockSize : ℝ) * outputPeriodOf m d r) := by
        rw [le_div_iff₀ (hA r)]
        have h2 := neg_abs_le ((w.speaker r).out 0)
        linarith
      calc capturePeriodOf m d
            * ((blocksBefore m w r (steadyHorizon w 𝒮 n) : ℝ) * ((1 + s) * Gcap))
          = (blocksBefore m w r (steadyHorizon w 𝒮 n) : ℝ)
            * (capturePeriodOf m d * ((1 + s) * Gcap)) := by ring
        _ ≤ (steadyHorizon w 𝒮 n + |(w.speaker r).out 0|)
              / ((m.blockSize : ℝ) * outputPeriodOf m d r)
            * (capturePeriodOf m d * ((1 + s) * Gcap)) := mul_le_mul_of_nonneg_right h1 hX
        _ = _ := by ring
    refine le_trans (mul_le_mul' (le_refl (c.latency : ℝ≥0∞))
      (mul_le_mul' (le_refl (R : ℝ≥0∞)⁻¹) (Finset.sum_le_sum hper))) (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

/-- **A lower bound on the expected cost in closed form, for members with
steady clocks.** Take a member whose clocks do not wander and whose audio
devices report exact timestamps; its links and hosts may pause and the
rates of its clocks may be spread. Take a random world of it and a solution
of the compared class (`StarSolutions`, with the step bound `u`,
`0 ≤ u < 1`) whose playback is a measurable function of what is drawn
(`measurablePlays`). Let `𝒮` be a set of speakers whose hosts are not the
sender's, `ℓ > 0` a length of cells, `Gcap ≥ 0` a cap on the latency, and
`w'` a weight with `w' * (1 - u) ≤` the weight of discontinuities. Then the
expected cost of the solution is at least the mean of `steadyBound`, with
the least advance `1 - u` of a step. -/
theorem lintegral_steadyBound_le [DecidableEq H] [Countable H] {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → Draw H R} {Msg : Type}
    {σ : Solution H R Msg} {lookahead : ℕ+} {c : Weights} {u : ℝ} (hf : f.SteadyClocks)
    (hσ : m.StarSolutions f lookahead c u Msg σ)
    (hplays : m.measurablePlays f lookahead Msg σ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hD : m.Prior f P D) {world : Ω → World H R} (hB : ∀ ω, m.Builds f (D ω) (world ω))
    (𝒮 : Finset (Fin R)) (h𝒮 : ∀ r ∈ 𝒮, m.host r ≠ m.sender) {ℓ Gcap : ℝ} (hℓ : 0 < ℓ)
    (hcap : 0 ≤ Gcap) (Xmax : ℝ) (Nbar : ℕ) {w' : ℝ≥0∞}
    (hw2 : w' * ENNReal.ofReal (1 - u) ≤ c.discontinuities) :
    ∫⁻ ω, steadyBound m f (D ω) lookahead c 𝒮 (1 - u) ℓ Xmax Gcap Nbar w' ∂P
      ≤ σ.expectedCost P world lookahead c := by
  refine le_trans (lintegral_mono_ae ?_)
    (lintegral_fixedClockBound_le hσ hplays hu0 hu1 hD hB 𝒮 h𝒮 hℓ)
  filter_upwards [hD.ae_constantRates hf hB] with ω hS
  exact hS.steadyBound_le lookahead c 𝒮 (by linarith) hℓ hcap Xmax Nbar hw2

end Unisono.Spec.GenerativeWorld
