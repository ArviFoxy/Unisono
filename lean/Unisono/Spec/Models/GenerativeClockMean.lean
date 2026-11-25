/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeFrameBound
public import Unisono.Spec.Models.GenerativeStar

/-!
# A lower bound on the expected cost: the mean over the clocks

`Prior.limsup_cells_le_cost` bounds the mean cost over the pauses from below
when the clocks are those of a fixed outcome. This file takes the mean over
the clocks, and so bounds the expected cost of a solution in a random world
of any member of the generative model.

* `cellsCap`, `cellsCost_le_cellsCap`: what the cells cost at least
  (`cellsCost`) is at most a number that depends on the clocks only.
* `CellChoices`: what the bound for fixed clocks leaves open: the caps, the
  bounds for the audio devices, the weight of a pause, the horizons, and at
  each horizon the playback blocks and the cells that are counted.
  `CellChoices.Valid` states the conditions on them for the clocks of a draw
  and its world, and `CellChoices.value` is the bound that they give.
* `fixedClockBound`: the largest value over the valid choices.
* `Prior.value_le_lintegral_cost`: the bound for fixed clocks, restated for
  valid choices.
* `lintegral_fixedClockBound_le`: for a solution through the sender that
  keeps the step bound and whose playback is a measurable function of what
  is drawn, the mean of `fixedClockBound` over the outcomes is at most the
  expected cost.

Which outcomes: every random world of every member; the clocks may wander
and the reports may have errors. Which solutions: those of
`GenerativeWorld.StarSolutions` and `GenerativeWorld.measurablePlays`. The
bound is not evaluated here: no valid choices are constructed, so nothing
here says how large `fixedClockBound` is. This is a lower bound, not a
statement that a solution is optimal.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {Ω : Type} [MeasurableSpace Ω]
  {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R}

/-- The least delay of a message from the sender to the host of speaker `r`,
in the draw `d`. -/
def leastDelayTo (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (r : Fin R) : ℝ :=
  d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)

/-- The mean number of pauses of the link from the sender to the host of
speaker `r` that begin within a period of length `ℓ`. -/
def pauseCount (m : GenerativeWorld H R) (f : Member H R) (ℓ : ℝ) (r : Fin R) : ℝ≥0 :=
  Real.toNNReal (f.linkPauseRate m.sender (m.host r) * ℓ)

/-- **What the cells of `J` cost at most**, whatever is played and whatever
pauses: for each cell, the latency term of the cell with the cap `Gcap` in
place of the latency, plus `w'` times `s * Nbar * blockSize`. It depends on
the world `w₁` only through the times at which speaker `r` requests its
playback blocks. -/
def cellsCap (m : GenerativeWorld H R) (w₁ : World H R) (r : Fin R) (s ℓ δ : ℝ) (pc : ℕ → ℝ)
    (Gcap : ℝ) (cl : ℝ≥0∞) (Nbar : ℕ) (w' : ℝ≥0∞) (J : Finset ℕ) : ℝ≥0∞ :=
  ∑ j ∈ J, (cl * ENNReal.ofReal
      (ℓ / ((w₁.speaker r).asked (cellBlock w₁ r ℓ δ j)
          - (w₁.speaker r).asked (cellBlock w₁ r ℓ δ j - 1))
        * (pc (cellBlock w₁ r ℓ δ j - 1) * (s * ((m.blockSize : ℝ) - 1) * Gcap)))
    + w' * ENNReal.ofReal (s * ((Nbar : ℝ) * m.blockSize)))

/-- **What the cells cost at least is at most a number that depends on the
clocks only.** For `s ≥ 0`, a cap `Gcap ≥ 0` and bounds `pc b ≥ 0`. -/
theorem cellsCost_le_cellsCap (m : GenerativeWorld H R) (f : Member H R) (d₁ : Draw H R)
    (w₁ : World H R) (lookahead : ℕ+) (r : Fin R) {s : ℝ} (hs : 0 ≤ s) (ℓ δ : ℝ)
    {pc : ℕ → ℝ} (hpc0 : ∀ b, 0 ≤ pc b) (pr : ℕ → ℝ) {Gcap : ℝ} (hcap : 0 ≤ Gcap)
    (cl : ℝ≥0∞) (Xmax : ℝ) (Nbar : ℕ) (w' : ℝ≥0∞) (m₀ : ℕ) (J : Finset ℕ) (e : Draw H R)
    (w : World H R) (plays : ℕ → Option ℝ) :
    cellsCost m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl Xmax Nbar w' m₀ J e w plays
      ≤ cellsCap m w₁ r s ℓ δ pc Gcap cl Nbar w' J := by
  classical
  have hB1 : (0 : ℝ) ≤ (m.blockSize : ℝ) - 1 := by
    have h1 : 1 ≤ m.blockSize := m.blockSize_pos
    have h2 : (1 : ℝ) ≤ (m.blockSize : ℝ) := by exact_mod_cast h1
    linarith
  unfold cellsCost cellsCap
  refine Finset.sum_le_sum fun j _ => add_le_add ?_ ?_
  · unfold cellLatency
    refine mul_le_mul' le_rfl ?_
    by_cases hshare : 0 ≤ ℓ / ((w₁.speaker r).asked (cellBlock w₁ r ℓ δ j)
        - (w₁.speaker r).asked (cellBlock w₁ r ℓ δ j - 1))
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _)
          (mul_nonneg hs hB1)) (hpc0 _)) hshare)
    · rw [ENNReal.ofReal_of_nonpos]
      · exact zero_le
      · refine mul_nonpos_of_nonpos_of_nonneg (not_le.mp hshare).le
          (mul_nonneg (hpc0 _) (mul_nonneg (mul_nonneg hs hB1) ?_))
        exact le_min (le_max_right _ _) hcap
  · split_ifs
    · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    · exact zero_le

/-- **What the lower bound for fixed clocks leaves open.** The bound of
`Prior.limsup_cells_le_cost` holds for every choice of these numbers that
satisfies the conditions of `CellChoices.Valid`. -/
structure CellChoices (R : ℕ) where
  /-- The longest paused time of a cell that is counted, in seconds. -/
  longestPause : ℝ
  /-- The largest number of playback blocks in the window of a cell. -/
  windowBlocks : ℕ
  /-- A cell counts a pause only if the link pauses nothing in this number
  of cells before it. -/
  clearCells : ℕ
  /-- The cap on the latency that is counted for a frame, in seconds. -/
  latencyCap : ℝ
  /-- An upper bound for the bounds `capturePeriod`, in seconds. -/
  referencePeriod : ℝ
  /-- For each speaker and each of its playback blocks: a lower bound for
  the time between two frames captured near the block, in seconds. -/
  capturePeriod : Fin R → ℕ → ℝ
  /-- For each speaker and each of its playback blocks: an upper bound for
  the time between two output samples of the block, in seconds. -/
  outputPeriod : Fin R → ℕ → ℝ
  /-- The weight of what a pause costs: of a missed sample, and of a
  discontinuity divided by the least advance of a step. -/
  pauseWeight : ℝ≥0∞
  /-- The horizons, in seconds of true time. -/
  horizon : ℕ → ℝ
  /-- For each horizon and each speaker: the number of its playback blocks
  that are counted. -/
  blocks : ℕ → Fin R → ℕ
  /-- For each horizon and each speaker: the cells that are counted. -/
  cells : ℕ → Fin R → Finset ℕ

/-- **The conditions on the choices**, for the clocks of the draw `d₁` and
its world `w₁`, the weights `c`, the speakers of `𝒮`, the least advance `s`
of a step of continuous playback and cells of length `ℓ`. They are the
conditions of `Prior.limsup_cells_le_cost`; the last one bounds `cellsCap`,
which depends on the clocks only. -/
structure CellChoices.Valid (q : CellChoices R) (m : GenerativeWorld H R) (f : Member H R)
    (d₁ : Draw H R) (w₁ : World H R) (c : Weights) (𝒮 : Finset (Fin R)) (s ℓ : ℝ) : Prop where
  /-- Windows of counted cells do not overlap. -/
  longestPause_le : q.longestPause ≤ ((q.clearCells : ℝ) + 1) * ℓ
  latencyCap_nonneg : 0 ≤ q.latencyCap
  referencePeriod_nonneg : 0 ≤ q.referencePeriod
  capturePeriod_nonneg : ∀ r ∈ 𝒮, ∀ b, 0 ≤ q.capturePeriod r b
  capturePeriod_le : ∀ r ∈ 𝒮, ∀ b, q.capturePeriod r b ≤ q.referencePeriod
  /-- Two output samples of a playback block are at most `outputPeriod`
  apart. -/
  out_sub_le : ∀ r ∈ 𝒮, ∀ b k, b * m.blockSize ≤ k → k < (b + 1) * m.blockSize →
    (w₁.speaker r).out (k + 1) - (w₁.speaker r).out k ≤ q.outputPeriod r b
  /-- Two frames captured after the first output sample of block `b` minus
  the cap, and by the request of block `b + 1`, are at least
  `capturePeriod` apart. -/
  le_capture_sub : ∀ r ∈ 𝒮, ∀ b i,
    (w₁.speaker r).out (b * m.blockSize) - q.latencyCap < w₁.source.capture i →
    w₁.source.capture (i + 1) ≤ (w₁.speaker r).asked (b + 1) →
    q.capturePeriod r b ≤ w₁.source.capture (i + 1) - w₁.source.capture i
  /-- The weight of missed samples covers the losses of the blocks and the
  weight of a pause. -/
  missed_ge : (c.latency : ℝ≥0∞) * ENNReal.ofReal (q.referencePeriod
      * ((1 + 2 * s) * (2 + 1 / s) * q.latencyCap
        + s * ((m.blockSize : ℝ) - 1) * q.referencePeriod * (2 * s + 1)))
    + q.pauseWeight ≤ c.missed
  discontinuities_ge : q.pauseWeight * ENNReal.ofReal s ≤ c.discontinuities
  horizon_tendsto : Tendsto q.horizon atTop atTop
  horizon_pos : ∀ n, 0 < q.horizon n
  /-- The counted playback blocks end before the horizon. -/
  out_lt_horizon : ∀ n, ∀ r ∈ 𝒮,
    (w₁.speaker r).out (q.blocks n r * m.blockSize) < q.horizon n
  /-- The window of a counted cell starts after the first playback block
  and ends by the last counted block, and no playback block is requested in
  the cell, shifted by the least delay. -/
  cells_spec : ∀ n, ∀ r ∈ 𝒮, ∀ j ∈ q.cells n r,
    1 ≤ cellBlock w₁ r ℓ (leastDelayTo m f d₁ r) j
      ∧ cellBlock w₁ r ℓ (leastDelayTo m f d₁ r) j + q.windowBlocks ≤ q.blocks n r
      ∧ ∀ b' < cellBlock w₁ r ℓ (leastDelayTo m f d₁ r) j,
          (w₁.speaker r).asked b' < (j : ℝ) * ℓ + leastDelayTo m f d₁ r
  /-- What the counted cells cost at most is at most a finite number times
  the horizon. -/
  bounded : ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n, (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
      cellsCap m w₁ r s ℓ (leastDelayTo m f d₁ r) (q.capturePeriod r) q.latencyCap
        (c.latency : ℝ≥0∞) q.windowBlocks q.pauseWeight (q.cells n r)
    ≤ M * ENNReal.ofReal (q.horizon n)

/-- **The bound that the choices give**, for the clocks of the draw `d₁` and
its world `w₁`: the limit superior, over the horizons, of the following
divided by the horizon. The average over the speakers of `𝒮` of the sum over
the counted cells of `exp (-pauseCount)` times `q` times the level program
of the cell (`cellValue`) plus `1 - q` times its least latency term
(`cellFloor`), where `q = exp (-rate * clearCells * ℓ)` for the rate of the
pauses of the link to the speaker's host; minus the weight of latency times
the average of `latencyCap * captureDeficit` and of
`referencePeriod * (1 + s) * latencyCap` for each counted block. -/
def CellChoices.value (q : CellChoices R) (m : GenerativeWorld H R) (f : Member H R)
    (d₁ : Draw H R) (w₁ : World H R) (lookahead : ℕ+) (c : Weights) (𝒮 : Finset (Fin R))
    (s ℓ : ℝ) : ℝ≥0∞ :=
  limsup (fun n =>
    ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ∑ j ∈ q.cells n r,
        ENNReal.ofReal (Real.exp (-(pauseCount m f ℓ r : ℝ)))
          * (ENNReal.ofReal
                (Real.exp (-(f.linkPauseRate m.sender (m.host r) * (q.clearCells * ℓ))))
              * cellValue m f d₁ w₁ lookahead r s ℓ (leastDelayTo m f d₁ r)
                (q.capturePeriod r) (q.outputPeriod r) q.latencyCap (c.latency : ℝ≥0∞)
                q.longestPause q.windowBlocks (pauseCount m f ℓ r) q.pauseWeight j
            + ENNReal.ofReal
                (1 - Real.exp (-(f.linkPauseRate m.sender (m.host r) * (q.clearCells * ℓ))))
              * cellFloor m f d₁ w₁ lookahead r s ℓ (leastDelayTo m f d₁ r)
                (q.capturePeriod r) (q.outputPeriod r) q.latencyCap (c.latency : ℝ≥0∞) j)
      - (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
          (ENNReal.ofReal q.latencyCap * w₁.captureDeficit q.referencePeriod (q.horizon n)
            + ENNReal.ofReal
              (q.referencePeriod * ((q.blocks n r : ℝ) * ((1 + s) * q.latencyCap))))))
      / ENNReal.ofReal (q.horizon n)) atTop

/-- **The lower bound for the clocks of a fixed outcome**: the largest value
that valid choices give, for the clocks of the draw `d₁` and its world `w₁`,
the weights `c`, the speakers of `𝒮`, the least advance `s` of a step of
continuous playback and cells of length `ℓ`. -/
def fixedClockBound (m : GenerativeWorld H R) (f : Member H R) (d₁ : Draw H R)
    (w₁ : World H R) (lookahead : ℕ+) (c : Weights) (𝒮 : Finset (Fin R)) (s ℓ : ℝ) : ℝ≥0∞ :=
  ⨆ (q : CellChoices R) (_ : q.Valid m f d₁ w₁ c 𝒮 s ℓ), q.value m f d₁ w₁ lookahead c 𝒮 s ℓ

omit [DecidableEq H] in
/-- The value of valid choices is at most the lower bound for fixed clocks. -/
theorem le_fixedClockBound {d₁ : Draw H R} {w₁ : World H R} {c : Weights}
    {𝒮 : Finset (Fin R)} {s ℓ : ℝ} {q : CellChoices R} (hq : q.Valid m f d₁ w₁ c 𝒮 s ℓ)
    (lookahead : ℕ+) :
    q.value m f d₁ w₁ lookahead c 𝒮 s ℓ ≤ fixedClockBound m f d₁ w₁ lookahead c 𝒮 s ℓ :=
  le_iSup₂ (f := fun (q : CellChoices R) (_ : q.Valid m f d₁ w₁ c 𝒮 s ℓ) =>
    q.value m f d₁ w₁ lookahead c 𝒮 s ℓ) q hq

/-- **The lower bound on the mean cost over the pauses, for valid choices.**
The statement of `Prior.limsup_cells_le_cost` with its choices collected in
`CellChoices`: the clocks are those of the draw `d₁` and its world `w₁`, the
pauses those of a random world of the member, and `w ω` is the world built
from `d₁` with the pauses of the outcome `ω`. For a solution through the
sender whose position advances by at least `s`, with `0 < s ≤ 1`, in every
step of continuous playback at the speakers of `𝒮`, and whose playback in
the worlds without the pauses of each cell is described by measurable sets
and functions of the draw, the value of valid choices is at most the mean
cost over the pauses. -/
theorem Prior.value_le_lintegral_cost {Msg : Type} (hD : m.Prior f P D)
    (hm : AEMeasurable D P) {d₁ : Draw H R} {w₁ : World H R} (hB₁ : m.Builds f d₁ w₁)
    (hpos₁ : ∀ i j, 0 ≤ d₁.split i j * f.roundTrip i j)
    (hhost₁ : ∀ h, Monotone (d₁.hostPaused h)) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) (c : Weights) (𝒮 : Finset (Fin R))
    (h𝒮 : ∀ r ∈ 𝒮, m.host r ≠ m.sender) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {w : Ω → World H R} {wOut : Fin R → ℕ → Ω → World H R}
    (hw : ∀ ω, m.Builds f (d₁.withLinks (D ω)) (w ω))
    (hOut : ∀ r j ω, m.Builds f (frameOutside m d₁ (D ω) r ℓ j) (wOut r j ω))
    (hslow : ∀ r ∈ 𝒮, ∀ᵐ ω ∂P, ∀ k x y, σ.plays (w ω) lookahead r k = some x →
      σ.plays (w ω) lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {S : Fin R → ℕ → Set (Draw H R)} {G : Fin R → ℕ → Draw H R → ℝ}
    (hS : ∀ r k, MeasurableSet (S r k)) (hG : ∀ r k, Measurable (G r k))
    (hdesc : ∀ r ∈ 𝒮, ∀ j k, ∀ᵐ ω ∂P, ∀ x : ℝ,
      σ.plays (wOut r j ω) lookahead r k = some x ↔
        frameOutside m d₁ (D ω) r ℓ j ∈ S r k ∧ G r k (frameOutside m d₁ (D ω) r ℓ j) = x)
    {q : CellChoices R} (hq : q.Valid m f d₁ w₁ c 𝒮 s ℓ) :
    q.value m f d₁ w₁ lookahead c 𝒮 s ℓ ≤ ∫⁻ ω, σ.cost (w ω) lookahead c ∂P := by
  obtain ⟨M, hM, hbound⟩ := hq.bounded
  exact hD.limsup_cells_le_cost hm hB₁ hpos₁ hhost₁ σ hstar lookahead c 𝒮 h𝒮 hs hs1 hℓ
    hq.longestPause_le hw hOut hslow hS hG hdesc (δ := leastDelayTo m f d₁) (fun _ => rfl)
    (count := pauseCount m f ℓ) (fun _ => rfl) hq.latencyCap_nonneg
    hq.referencePeriod_nonneg hq.capturePeriod_nonneg hq.capturePeriod_le hq.out_sub_le
    hq.le_capture_sub q.pauseWeight hq.missed_ge hq.discontinuities_ge hq.horizon_tendsto
    hq.horizon_pos q.blocks q.cells hq.out_lt_horizon hq.cells_spec hM
    (fun n ω => le_trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun r hr =>
      cellsCost_le_cellsCap m f d₁ w₁ lookahead r hs.le ℓ (leastDelayTo m f d₁ r)
        (hq.capturePeriod_nonneg r hr) (q.outputPeriod r) hq.latencyCap_nonneg
        (c.latency : ℝ≥0∞) q.longestPause q.windowBlocks q.pauseWeight q.clearCells
        (q.cells n r) (D ω) (w ω) (σ.plays (w ω) lookahead r))) (hbound n))

/-- **A lower bound on the expected cost, in every member of the generative
model.** Take a random world of a member, with the draw `D ω` and the world
`world ω` of each outcome. Take a solution of the compared class
(`StarSolutions`): its hosts exchange messages only with the sender, its
cost is a measurable function of what is drawn, and almost surely its
position advances by one frame per output sample within `u`, with
`0 ≤ u < 1`, in every step of continuous playback. Let what it plays at each
output sample of each speaker be a measurable function of what is drawn
(`measurablePlays`). Let `𝒮` be a set of speakers whose hosts are not the
sender's, and `ℓ > 0` a length of cells.

Then the expected cost of the solution is at least the mean, over the
outcomes, of the lower bound for the clocks of the outcome
(`fixedClockBound` with the least advance `1 - u`). The mean is a lower
integral: nothing is assumed or proved about the measurability of that
bound. -/
theorem lintegral_fixedClockBound_le [Countable H] {Msg : Type} {σ : Solution H R Msg}
    {lookahead : ℕ+} {c : Weights} {u : ℝ} (hσ : m.StarSolutions f lookahead c u Msg σ)
    (hplays : m.measurablePlays f lookahead Msg σ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hD : m.Prior f P D) {world : Ω → World H R} (hB : ∀ ω, m.Builds f (D ω) (world ω))
    (𝒮 : Finset (Fin R)) (h𝒮 : ∀ r ∈ 𝒮, m.host r ≠ m.sender) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫⁻ ω, fixedClockBound m f (D ω) (world ω) lookahead c 𝒮 (1 - u) ℓ ∂P
      ≤ σ.expectedCost P world lookahead c := by
  classical
  have := hD.prob
  have hm := hD.aemeasurable
  have hD₂ : m.Prior f (P.prod P) (resampleLinks D) := hD.prior_resampleLinks
  -- A world for every pair of outcomes: the clocks of the first, the pauses of the second.
  choose world₂ hB₂ using fun ω : Ω × Ω => hD.exists_resampleLinks hB ω
  -- The worlds without the pauses of each cell.
  have hexOut : ∀ (r : Fin R) (j : ℕ) (ω : Ω × Ω), ∃ w' : World H R,
      m.Builds f ((resampleLinks D ω).linkOutside m.sender (m.host r) ((j : ℝ) * ℓ)
        (((j : ℝ) + 1) * ℓ)) w' := fun r j ω =>
    (hB₂ ω).exists_linkOutside (fun i j' => hD₂.leastDelay_pos ω i j')
      (fun i j' => hD₂.linkPaused_monotone ω i j') _ _ _ _
  choose wOut₂ hOut₂ using hexOut
  rw [expectedCost_resampleLinks hσ.measurable hD hB hB₂]
  choose S G hS hG hSG using hplays
  -- The step bound, for almost every pair of outcomes.
  have hstep : ∀ᵐ ω₁ ∂P, ∀ᵐ ω₂ ∂P, σ.WithinStep (world₂ (ω₁, ω₂)) lookahead u :=
    Measure.ae_ae_of_ae_prod
      (hσ.withinStep (Ω × Ω) (P.prod P) (resampleLinks D) world₂ hD₂ hB₂)
  -- The descriptions of the playback in the worlds without the pauses of each cell.
  have hdesc : ∀ᵐ ω₁ ∂P, ∀ (r : Fin R) (j k : ℕ), ∀ᵐ ω₂ ∂P, ∀ x : ℝ,
      σ.plays (wOut₂ r j (ω₁, ω₂)) lookahead r k = some x ↔
        frameOutside m (D ω₁) (D ω₂) r ℓ j ∈ S r k
          ∧ G r k (frameOutside m (D ω₁) (D ω₂) r ℓ j) = x := by
    refine ae_all_iff.mpr fun r => ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ?_
    have hj : (0 : ℝ) ≤ (j : ℝ) * ℓ := mul_nonneg (Nat.cast_nonneg j) hℓ.le
    have hjle : (j : ℝ) * ℓ ≤ ((j : ℝ) + 1) * ℓ := by nlinarith
    have h1 := ae_plays_linkOutside_of (hSG r k) hD₂ hB₂ m.sender (m.host r) hj hjle
      (hOut₂ r j)
    exact Measure.ae_ae_of_ae_prod h1
  refine lintegral_mono_ae ?_
  filter_upwards [hstep, hdesc] with ω₁ hω₁ hdω₁
  refine iSup₂_le fun q hq => ?_
  exact hD.value_le_lintegral_cost hm (hB ω₁) (fun i j => (hD.leastDelay_pos ω₁ i j).le)
    (fun h => hD.hostPaused_monotone ω₁ h) σ
    hσ.star lookahead c 𝒮 h𝒮 (by linarith) (by linarith) hℓ
    (w := fun ω => world₂ (ω₁, ω)) (wOut := fun r j ω => wOut₂ r j (ω₁, ω))
    (fun ω => hB₂ (ω₁, ω)) (fun r j ω => hOut₂ r j (ω₁, ω))
    (fun r _ => by
      filter_upwards [hω₁] with ω hω k x y hx hy hxy hy2
      have h1 := (abs_le.mp (hω r k x y hx hy hxy hy2)).1
      linarith)
    hS hG (fun r _ j k => hdω₁ r j k) hq

end Unisono.Spec.GenerativeWorld
