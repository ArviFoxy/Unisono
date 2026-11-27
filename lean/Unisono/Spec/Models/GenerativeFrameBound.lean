/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeLimit

/-!
# A lower bound on the mean cost over the pauses, with fixed clocks

With the clocks of a fixed outcome and the pauses of a random world, every
solution through the sender that keeps the step bound, and whose playback
in the worlds without the pauses of each cell is described by measurable
sets and functions of the draw, has a mean cost of at least the long-run
average of the level programs of the cells, minus terms that depend only on
the clocks.

* `cellFloor_le_cellValue`: the level program of a cell is at least its
  least latency term.
* `Prior.limsup_cells_le_cost`: the statement. The horizons, the numbers of
  playback blocks, the sets of cells and the bounds for the audio devices
  are given; the bound holds for every choice that satisfies the
  conditions.

The mean is over the pauses only. The mean over the clocks, and the
conditions for almost every outcome of the clocks, are not done here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {Ω : Type} [MeasurableSpace Ω]
  {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R}

omit [DecidableEq H] in
/-- The level program of a cell is at least its least latency term. -/
theorem cellFloor_le_cellValue (m : GenerativeWorld H R) (f : Member H R) (d₁ : Draw H R)
    (w₁ : World H R) (lookahead : ℕ+) (r : Fin R) (s ℓ δ : ℝ) (pc pr : ℕ → ℝ) (Gcap : ℝ)
    (cl : ℝ≥0∞) (Xmax : ℝ) (Nbar : ℕ) (count : ℝ≥0) (w' : ℝ≥0∞) (j : ℕ) :
    cellFloor m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl j
      ≤ cellValue m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl Xmax Nbar count w' j :=
  iInf_mono fun _ => le_self_add

/-- **A lower bound on the mean cost over the pauses, with the clocks of a
fixed outcome.** Fix a draw `d₁` with its world `w₁`, which give the clocks,
the audio devices and the least delays, and take the pauses from a random
world of the member: `w ω` is the world built from `d₁` with the pauses of
the outcome `ω`. Consider a solution whose hosts exchange messages only
with the sender and a set `𝒮` of speakers whose hosts are not the sender's.
For each of them: its position advances by at least `s`, with `0 < s ≤ 1`,
in every step of continuous playback, in almost every world `w ω`; and its
playback in the worlds without the pauses of each cell is described by
measurable sets and functions of the draw.

Let the horizons `T n` be positive and grow without bound. For each `n` and
each speaker of `𝒮` let its first `N n r` playback blocks end before `T n`,
and let `J n r` be a set of cells in which none of its playback blocks is
requested, whose windows start after its first block and end by block
`N n r`. Let `pc r`, `pr r`, `Gcap` and `p₀` bound the audio devices near
the blocks as in `Builds.sum_blocks_le_latency`, let the weight of missed
samples cover the weight of latency times `p₀ * C` plus `w'`, where `C` is
the constant of that theorem, and the weight of discontinuities `w' * s`.
Let what the cells cost at least (`cellsCost`), averaged over the speakers,
be at most a finite number times `T n` in every outcome.

Then the mean cost over the pauses is at least the limit superior, as `n`
grows, of the following divided by `T n`: the average over the speakers of
the sum over the cells of `J n r` of `exp (-count)` times `q` times the
level program of the cell plus `1 - q` times its least latency term, minus
the weight of latency times the average of `Gcap` times `captureDeficit`
and of `p₀ * (1 + s) * Gcap` for each block. Here `count` pauses of the
link to the speaker's host begin in a cell on average, and
`q = exp (-rate * m₀ * ℓ)`. -/
theorem Prior.limsup_cells_le_cost {Msg : Type} (hD : m.Prior f P D) (hm : AEMeasurable D P)
    {d₁ : Draw H R} {w₁ : World H R} (hB₁ : m.Builds f d₁ w₁)
    (hpos₁ : ∀ i j, 0 ≤ d₁.split i j * f.roundTrip i j)
    (hhost₁ : ∀ h, Monotone (d₁.hostPaused h)) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) (c : Weights) (𝒮 : Finset (Fin R))
    (h𝒮 : ∀ r ∈ 𝒮, m.host r ≠ m.sender) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {Xmax : ℝ} {Nbar m₀ : ℕ} (hX : Xmax ≤ ((m₀ : ℝ) + 1) * ℓ)
    {w : Ω → World H R} {wOut : Fin R → ℕ → Ω → World H R}
    (hw : ∀ ω, m.Builds f (d₁.withLinks (D ω)) (w ω))
    (hOut : ∀ r j ω, m.Builds f (frameOutside m d₁ (D ω) r ℓ j) (wOut r j ω))
    (hslow : ∀ r ∈ 𝒮, ∀ᵐ ω ∂P, ∀ k x y, σ.plays (w ω) lookahead r k = some x →
      σ.plays (w ω) lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {S : Fin R → ℕ → Set (Draw H R)} {G : Fin R → ℕ → Draw H R → ℝ}
    (hS : ∀ r k, MeasurableSet (S r k)) (hG : ∀ r k, Measurable (G r k))
    (hdesc : ∀ r ∈ 𝒮, ∀ j k, ∀ᵐ ω ∂P, ∀ x : ℝ,
      σ.plays (wOut r j ω) lookahead r k = some x ↔
        frameOutside m d₁ (D ω) r ℓ j ∈ S r k ∧ G r k (frameOutside m d₁ (D ω) r ℓ j) = x)
    {δ : Fin R → ℝ}
    (hδ : ∀ r, δ r = d₁.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    {count : Fin R → ℝ≥0}
    (hcount : ∀ r, count r = Real.toNNReal (f.linkPauseRate m.sender (m.host r) * ℓ))
    {pc pr : Fin R → ℕ → ℝ} {Gcap p₀ : ℝ} (hcap : 0 ≤ Gcap) (hp₀ : 0 ≤ p₀)
    (hpc0 : ∀ r ∈ 𝒮, ∀ b, 0 ≤ pc r b) (hpcle : ∀ r ∈ 𝒮, ∀ b, pc r b ≤ p₀)
    (hpr : ∀ r ∈ 𝒮, ∀ b k, b * m.blockSize ≤ k → k < (b + 1) * m.blockSize →
      (w₁.speaker r).out (k + 1) - (w₁.speaker r).out k ≤ pr r b)
    (hpc : ∀ r ∈ 𝒮, ∀ b i, (w₁.speaker r).out (b * m.blockSize) - Gcap < w₁.source.capture i →
      w₁.source.capture (i + 1) ≤ (w₁.speaker r).asked (b + 1) →
      pc r b ≤ w₁.source.capture (i + 1) - w₁.source.capture i)
    (w' : ℝ≥0∞)
    (hw1 : (c.latency : ℝ≥0∞) * ENNReal.ofReal (p₀ * ((1 + 2 * s) * (2 + 1 / s) * Gcap
        + s * ((m.blockSize : ℝ) - 1) * p₀ * (2 * s + 1))) + w' ≤ c.missed)
    (hw2 : w' * ENNReal.ofReal s ≤ c.discontinuities)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) (hTpos : ∀ n, 0 < T n) (N : ℕ → Fin R → ℕ)
    (J : ℕ → Fin R → Finset ℕ)
    (hout : ∀ n, ∀ r ∈ 𝒮, (w₁.speaker r).out (N n r * m.blockSize) < T n)
    (hJ : ∀ n, ∀ r ∈ 𝒮, ∀ j ∈ J n r, 1 ≤ cellBlock w₁ r ℓ (δ r) j
      ∧ cellBlock w₁ r ℓ (δ r) j + Nbar ≤ N n r
      ∧ ∀ b' < cellBlock w₁ r ℓ (δ r) j, (w₁.speaker r).asked b' < (j : ℝ) * ℓ + δ r)
    {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbound : ∀ n ω, (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
        cellsCost m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap (c.latency : ℝ≥0∞) Xmax
          Nbar w' m₀ (J n r) (D ω) (w ω) (σ.plays (w ω) lookahead r)
      ≤ M * ENNReal.ofReal (T n)) :
    limsup (fun n =>
        ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ∑ j ∈ J n r,
            ENNReal.ofReal (Real.exp (-(count r : ℝ)))
              * (ENNReal.ofReal
                    (Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ))))
                  * cellValue m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
                    (c.latency : ℝ≥0∞) Xmax Nbar (count r) w' j
                + ENNReal.ofReal
                    (1 - Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ))))
                  * cellFloor m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
                    (c.latency : ℝ≥0∞) j)
          - (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
              (ENNReal.ofReal Gcap * w₁.captureDeficit p₀ (T n)
                + ENNReal.ofReal (p₀ * ((N n r : ℝ) * ((1 + s) * Gcap))))))
          / ENNReal.ofReal (T n)) atTop
      ≤ ∫⁻ ω, σ.cost (w ω) lookahead c ∂P := by
  classical
  have := hD.prob
  have hB1 : (0 : ℝ) ≤ (m.blockSize : ℝ) - 1 := by
    have h1 : 1 ≤ m.blockSize := m.blockSize_pos
    have h2 : (1 : ℝ) ≤ (m.blockSize : ℝ) := by exact_mod_cast h1
    linarith
  have hC : 0 ≤ (1 + 2 * s) * (2 + 1 / s) * Gcap
      + s * ((m.blockSize : ℝ) - 1) * p₀ * (2 * s + 1) := by
    have h1 : 0 ≤ 1 / s := (one_div_pos.mpr hs).le
    have h2 : 0 ≤ (1 + 2 * s) * (2 + 1 / s) * Gcap :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hcap
    have h3 : 0 ≤ s * ((m.blockSize : ℝ) - 1) * p₀ * (2 * s + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hs.le hB1) hp₀) (by linarith)
    linarith
  refine limsup_le_lintegral_cost w (fun ω => σ.plays (w ω) lookahead) c hT hTpos hM hbound
    (fun n => ?_) ?_
  · -- The mean over the pauses.
    have hcell : ∀ r ∈ 𝒮, ∑ j ∈ J n r, ENNReal.ofReal (Real.exp (-(count r : ℝ)))
          * (ENNReal.ofReal (Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ))))
              * cellValue m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
                (c.latency : ℝ≥0∞) Xmax Nbar (count r) w' j
            + ENNReal.ofReal
                (1 - Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ))))
              * cellFloor m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
                (c.latency : ℝ≥0∞) j)
        ≤ ∫⁻ ω, cellsCost m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
            (c.latency : ℝ≥0∞) Xmax Nbar w' m₀ (J n r) (D ω) (w ω)
            (σ.plays (w ω) lookahead r) ∂P := by
      intro r hr
      refine le_trans (Finset.sum_le_sum fun j _ => ?_)
        (hD.sum_cellValue_le hm hB₁ hpos₁ hhost₁ σ hstar lookahead (h𝒮 r hr) hs.le hs1 hℓ.le m₀ hw
          (hOut r) (hslow r hr) (hS r) (hG r) (hdesc r hr) (hδ r) (hcount r) (pc r) (pr r)
          Gcap (J n r) (fun j hj => (hJ n r hr j hj).2.2) (c.latency : ℝ≥0∞) w')
      refine le_trans (mul_le_mul' le_rfl (hD.lintegral_clear_ge d₁ r hℓ.le m₀ j
        (cellFloor_le_cellValue m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
          (c.latency : ℝ≥0∞) Xmax Nbar (count r) w' j))) ?_
      exact lintegral_const_mul_le _ _
    calc (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ∑ j ∈ J n r, ENNReal.ofReal (Real.exp (-(count r : ℝ)))
            * (ENNReal.ofReal
                  (Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ))))
                * cellValue m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
                  (c.latency : ℝ≥0∞) Xmax Nbar (count r) w' j
              + ENNReal.ofReal
                  (1 - Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ))))
                * cellFloor m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
                  (c.latency : ℝ≥0∞) j)
        ≤ (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ∫⁻ ω, cellsCost m f d₁ w₁ lookahead r s ℓ (δ r) (pc r)
            (pr r) Gcap (c.latency : ℝ≥0∞) Xmax Nbar w' m₀ (J n r) (D ω) (w ω)
            (σ.plays (w ω) lookahead r) ∂P := mul_le_mul' le_rfl (Finset.sum_le_sum hcell)
      _ ≤ (R : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ r ∈ 𝒮, cellsCost m f d₁ w₁ lookahead r s ℓ (δ r) (pc r)
            (pr r) Gcap (c.latency : ℝ≥0∞) Xmax Nbar w' m₀ (J n r) (D ω) (w ω)
            (σ.plays (w ω) lookahead r) ∂P := mul_le_mul' le_rfl (sum_lintegral_le 𝒮 _)
      _ ≤ _ := lintegral_const_mul_le _ _
  · -- In almost every outcome, at every horizon.
    have hslowAll : ∀ᵐ ω ∂P, ∀ r, r ∈ 𝒮 → ∀ k x y, σ.plays (w ω) lookahead r k = some x →
        σ.plays (w ω) lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y := by
      refine ae_all_iff.mpr fun r => ?_
      by_cases hr : r ∈ 𝒮
      · filter_upwards [hslow r hr] with ω hω _
        exact hω
      · exact Eventually.of_forall fun ω h => absurd h hr
    filter_upwards [hslowAll] with ω hω n
    obtain ⟨-, -, -, hsrc, hspk, -⟩ := hB₁.same_devices (hw ω) rfl rfl rfl rfl rfl rfl rfl
    have hdefc : (w ω).captureDeficit p₀ (T n) = w₁.captureDeficit p₀ (T n) := by
      unfold World.captureDeficit
      rw [hsrc]
    have hQ := (w ω).sum_le_accrued_add_loss (σ.plays (w ω) lookahead) c (T := T n) 𝒮 (N n)
      m.blockSize hs.le hcap hp₀ hC w' hw1 hw2
      (fun r hr => by
        rw [hspk]
        exact hout n r hr)
      (fun r hr k hk => lt_trans
        ((hw ω).capture_lt_out hpos₁ (fun i j' => hD.linkPaused_monotone ω i j')
          hhost₁ σ hstar lookahead (h𝒮 r hr) hk) (by
          rw [hspk]
          exact hout n r hr))
      (fun r => cellsCost m f d₁ w₁ lookahead r s ℓ (δ r) (pc r) (pr r) Gcap
        (c.latency : ℝ≥0∞) Xmax Nbar w' m₀ (J n r) (D ω) (w ω) (σ.plays (w ω) lookahead r))
      (fun r hr => hB₁.cellsCost_le (hw ω) hpos₁ (fun i j' => hD.linkPaused_monotone ω i j')
        hhost₁ σ hstar lookahead (h𝒮 r hr) hs hℓ hX (hω r hr)
        (δ r) hcap hp₀ (N n r) (fun b _ => hpc0 r hr b) (fun b _ => hpcle r hr b)
        (fun b _ => hpr r hr b) (fun b _ => hpc r hr b) (J n r)
        (fun j hj => ⟨(hJ n r hr j hj).1, (hJ n r hr j hj).2.1,
          (hJ n r hr j hj).2.2 _ (by
            have := (hJ n r hr j hj).1
            omega)⟩) (c.latency : ℝ≥0∞) w')
    rw [hdefc] at hQ
    exact hQ

end Unisono.Spec.GenerativeWorld
