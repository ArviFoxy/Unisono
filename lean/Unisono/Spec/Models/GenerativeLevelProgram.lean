/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeClockMean
public import Unisono.Spec.CellCount

/-!
# The level program per second

The lower bound for fixed clocks (`fixedClockBound`) sums, over cells of
true time, the level program of each cell (`cellValue`): the least, over the
room that a solution keeps, of what the room costs in latency plus the mean
of what one pause costs with that room. The level program of a cell depends
on the cell through the times at which the speaker requests its playback
blocks near the cell.

This file defines a level program that depends on a few numbers only, and
shows that the level program of a cell of length `ℓ` is at least `ℓ` times
it when the requests near the cell are at most `A` apart.

* `levelLatency`: the latency term per second, as a function of the room.
* `levelValue`: the level program per second: the least, over the rooms, of
  the latency term plus the rate of the pauses times the mean, over the
  length of one pause, of what it costs with that room.
* `levelFloor`: the least latency term.
* `mul_levelLatency_le_cell`, `mul_levelFloor_le_cellFloor`,
  `mul_levelValue_le_cellValue`: the comparisons with a cell.
* `levelFloor_le_levelValue`, `levelValue_ne_top`: the level program is at
  least its least latency term, and it is finite for finite weights.

The numbers are: the least advance `s` of the position in a step of
continuous playback; the least delay `δ` from the sender; the time `lead`
from the request of a playback block to its first output sample; the
longest time `A` between two requests; a lower bound `pc` for the time
between two captured frames and an upper bound `pr` for the time between
two output samples; the cap `Gcap` on a latency; the longest pause `Xmax`
and the largest number `Nbar` of playback blocks that are counted for one
pause. Nothing here is random, and no cost is bounded here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-- **The latency term of the level program, per second**, for the room `ρ`
in frames. The weight `cl` times `pc * s * (blockSize - 1) / A`, the time
of source that the steps of a playback block cover at least, per second,
times the latency that the room implies, counted from zero up to `Gcap`:
`δ + lead + pc * (ρ + lookahead - 1) - 2 * pr
  - blockSize * max (pr - s * pc) 0`. -/
def levelLatency (m : GenerativeWorld H R) (lookahead : ℕ+) (s δ lead A pc pr Gcap : ℝ)
    (cl : ℝ≥0∞) (ρ : ℝ) : ℝ≥0∞ :=
  cl * ENNReal.ofReal (pc * (s * ((m.blockSize : ℝ) - 1)) / A
    * min (max (δ + lead + pc * (ρ + ((lookahead : ℕ) : ℝ) - 1) - 2 * pr
      - (m.blockSize : ℝ) * max (pr - s * pc) 0) 0) Gcap)

/-- **The level program per second**, for speaker `r`: the least, over the
rooms `ρ ≥ 0`, of the latency term for the room plus the rate of the pauses
of the link from the sender to the speaker's host times the mean, over the
length `x` of one pause, of `w'` times what the pause costs at least with
that room: `s` for each output sample of the `min Nbar ⌊min x Xmax / A⌋`
playback blocks that it stalls, minus the room, minus `s`. -/
def levelValue (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+) (r : Fin R)
    (s δ lead A pc pr Gcap : ℝ) (cl : ℝ≥0∞) (Xmax : ℝ) (Nbar : ℕ) (w' : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ ρ : {ρ : ℝ // 0 ≤ ρ}, levelLatency m lookahead s δ lead A pc pr Gcap cl ρ
    + ENNReal.ofReal (f.linkPauseRate m.sender (m.host r))
      * ∫⁻ x in {x : ℝ | x ≠ 0}, w' * ENNReal.ofReal
          (s * (((min Nbar ⌊min x Xmax / A⌋₊ : ℕ) : ℝ) * m.blockSize) - ρ - s)
        ∂(f.linkPauseLength m.sender (m.host r))

/-- The least of the latency term of the level program over the rooms
`ρ ≥ 0`. -/
def levelFloor (m : GenerativeWorld H R) (lookahead : ℕ+) (s δ lead A pc pr Gcap : ℝ)
    (cl : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ ρ : {ρ : ℝ // 0 ≤ ρ}, levelLatency m lookahead s δ lead A pc pr Gcap cl ρ

/-- The level program is at least its least latency term. -/
theorem levelFloor_le_levelValue (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+)
    (r : Fin R) (s δ lead A pc pr Gcap : ℝ) (cl : ℝ≥0∞) (Xmax : ℝ) (Nbar : ℕ) (w' : ℝ≥0∞) :
    levelFloor m lookahead s δ lead A pc pr Gcap cl
      ≤ levelValue m f lookahead r s δ lead A pc pr Gcap cl Xmax Nbar w' :=
  iInf_mono fun _ => le_self_add

/-- **The level program per second is finite** when the weights `cl` and
`w'` are finite and `s ≥ 0`. -/
theorem levelValue_ne_top (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+)
    (r : Fin R) {s : ℝ} (hs : 0 ≤ s) (δ lead A pc pr Gcap : ℝ) {cl : ℝ≥0∞} (hcl : cl ≠ ⊤)
    (Xmax : ℝ) (Nbar : ℕ) {w' : ℝ≥0∞} (hw' : w' ≠ ⊤) :
    levelValue m f lookahead r s δ lead A pc pr Gcap cl Xmax Nbar w' ≠ ⊤ := by
  have := f.linkPauseLength_prob m.sender (m.host r)
  refine ne_top_of_le_ne_top ?_ (iInf_le _ (⟨0, le_rfl⟩ : {ρ : ℝ // 0 ≤ ρ}))
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hcl ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
  have hle : ∫⁻ x in {x : ℝ | x ≠ 0}, w' * ENNReal.ofReal
        (s * (((min Nbar ⌊min x Xmax / A⌋₊ : ℕ) : ℝ) * m.blockSize) - (0 : ℝ) - s)
      ∂(f.linkPauseLength m.sender (m.host r))
      ≤ ∫⁻ _ in {x : ℝ | x ≠ 0}, w' * ENNReal.ofReal (s * ((Nbar : ℝ) * m.blockSize))
        ∂(f.linkPauseLength m.sender (m.host r)) := by
    refine lintegral_mono fun x => mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    have h1 : ((min Nbar ⌊min x Xmax / A⌋₊ : ℕ) : ℝ) ≤ (Nbar : ℝ) := by
      exact_mod_cast min_le_left Nbar ⌊min x Xmax / A⌋₊
    have h2 : (0 : ℝ) ≤ (m.blockSize : ℝ) := Nat.cast_nonneg _
    have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) hs
    linarith
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_const]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hw' ENNReal.ofReal_ne_top) (measure_ne_top _ _)

/-- **The latency term of a cell is at least the length of the cell times
the latency term per second.** For the cell `j` of length `ℓ ≥ 0` and its
first block `b ≥ 1`: let the bounds `pc` and `pr` for the block before it be
`pc₀ ≥ 0` and `pr₀`, let block `b` be requested at most `A` after block
`b - 1`, and at least `lead` before its first output sample. -/
theorem mul_levelLatency_le_cell (m : GenerativeWorld H R) (f : Member H R)
    (d₁ : Draw H R) (w₁ : World H R) (lookahead : ℕ+) (r : Fin R)
    {s ℓ A pc₀ pr₀ lead Gcap : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hA : 0 < A) (hpc₀ : 0 ≤ pc₀)
    (hcap : 0 ≤ Gcap) {pc pr : ℕ → ℝ} (cl : ℝ≥0∞) {j b : ℕ}
    (hbdef : cellBlock w₁ r ℓ (leastDelayTo m f d₁ r) j = b) (hb : 1 ≤ b)
    (hpc : pc (b - 1) = pc₀) (hpr : pr (b - 1) = pr₀)
    (hgap0 : 0 < (w₁.speaker r).asked b - (w₁.speaker r).asked (b - 1))
    (hgap : (w₁.speaker r).asked b - (w₁.speaker r).asked (b - 1) ≤ A)
    (hlead : lead ≤ (w₁.speaker r).out (b * m.blockSize) - (w₁.speaker r).asked b) (ρ : ℝ) :
    ENNReal.ofReal ℓ
        * levelLatency m lookahead s (leastDelayTo m f d₁ r) lead A pc₀ pr₀ Gcap cl ρ
      ≤ cellLatency m f d₁ w₁ lookahead r s ℓ (leastDelayTo m f d₁ r) pc pr Gcap cl j ρ := by
  have hB1 : (0 : ℝ) ≤ (m.blockSize : ℝ) - 1 := by
    have h1 : 1 ≤ m.blockSize := m.blockSize_pos
    have h2 : (1 : ℝ) ≤ (m.blockSize : ℝ) := by exact_mod_cast h1
    linarith
  unfold levelLatency cellLatency
  rw [hbdef, hpc, hpr]
  have hidx : b - 1 + 1 = b := Nat.sub_add_cancel hb
  have hrl : leastDelayTo m f d₁ r + lead + pc₀ * (ρ + ((lookahead : ℕ) : ℝ) - 1) - 2 * pr₀
      - (m.blockSize : ℝ) * max (pr₀ - s * pc₀) 0
      ≤ roomLatency m f d₁ w₁ lookahead r s pc₀ pr₀ (b - 1) ρ := by
    unfold roomLatency leastDelayTo
    rw [hidx]
    linarith
  have hM := min_le_min (max_le_max hrl (le_refl (0 : ℝ))) (le_refl Gcap)
  have hM0 : 0 ≤ min (max (leastDelayTo m f d₁ r + lead
      + pc₀ * (ρ + ((lookahead : ℕ) : ℝ) - 1) - 2 * pr₀
      - (m.blockSize : ℝ) * max (pr₀ - s * pc₀) 0) 0) Gcap := le_min (le_max_right _ _) hcap
  have hc : 0 ≤ ℓ * (pc₀ * (s * ((m.blockSize : ℝ) - 1))) :=
    mul_nonneg hℓ (mul_nonneg hpc₀ (mul_nonneg hs hB1))
  generalize min (max (leastDelayTo m f d₁ r + lead
      + pc₀ * (ρ + ((lookahead : ℕ) : ℝ) - 1) - 2 * pr₀
      - (m.blockSize : ℝ) * max (pr₀ - s * pc₀) 0) 0) Gcap = M₁ at hM hM0 ⊢
  generalize min (max (roomLatency m f d₁ w₁ lookahead r s pc₀ pr₀ (b - 1) ρ) 0) Gcap = M₂
    at hM ⊢
  generalize (w₁.speaker r).asked b - (w₁.speaker r).asked (b - 1) = gap at hgap0 hgap ⊢
  have hcomm : ENNReal.ofReal ℓ
        * (cl * ENNReal.ofReal (pc₀ * (s * ((m.blockSize : ℝ) - 1)) / A * M₁))
      = cl * ENNReal.ofReal (ℓ * (pc₀ * (s * ((m.blockSize : ℝ) - 1)) / A * M₁)) := by
    rw [ENNReal.ofReal_mul hℓ]
    ring
  rw [hcomm]
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have e1 : ℓ * (pc₀ * (s * ((m.blockSize : ℝ) - 1)) / A * M₁)
      = ℓ * (pc₀ * (s * ((m.blockSize : ℝ) - 1))) * M₁ / A := by ring
  have e2 : ℓ / gap * (pc₀ * (s * ((m.blockSize : ℝ) - 1) * M₂))
      = ℓ * (pc₀ * (s * ((m.blockSize : ℝ) - 1))) * M₂ / gap := by ring
  rw [e1, e2, div_le_div_iff₀ hA hgap0]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hM hc) hgap hgap0.le
    (mul_nonneg hc (hM0.trans hM))

/-- **The least latency term of a cell is at least the length of the cell
times the least latency term per second**, under the conditions of
`mul_levelLatency_le_cell`. -/
theorem mul_levelFloor_le_cellFloor (m : GenerativeWorld H R) (f : Member H R)
    (d₁ : Draw H R) (w₁ : World H R) (lookahead : ℕ+) (r : Fin R)
    {s ℓ A pc₀ pr₀ lead Gcap : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hA : 0 < A) (hpc₀ : 0 ≤ pc₀)
    (hcap : 0 ≤ Gcap) {pc pr : ℕ → ℝ} (cl : ℝ≥0∞) {j b : ℕ}
    (hbdef : cellBlock w₁ r ℓ (leastDelayTo m f d₁ r) j = b) (hb : 1 ≤ b)
    (hpc : pc (b - 1) = pc₀) (hpr : pr (b - 1) = pr₀)
    (hgap0 : 0 < (w₁.speaker r).asked b - (w₁.speaker r).asked (b - 1))
    (hgap : (w₁.speaker r).asked b - (w₁.speaker r).asked (b - 1) ≤ A)
    (hlead : lead ≤ (w₁.speaker r).out (b * m.blockSize) - (w₁.speaker r).asked b) :
    ENNReal.ofReal ℓ
        * levelFloor m lookahead s (leastDelayTo m f d₁ r) lead A pc₀ pr₀ Gcap cl
      ≤ cellFloor m f d₁ w₁ lookahead r s ℓ (leastDelayTo m f d₁ r) pc pr Gcap cl j :=
  le_iInf fun ρ => (mul_le_mul' le_rfl (iInf_le _ ρ)).trans
    (mul_levelLatency_le_cell m f d₁ w₁ lookahead r hs hℓ hA hpc₀ hcap cl hbdef hb
      hpc hpr hgap0 hgap hlead ρ)

/-- **The level program of a cell is at least the length of the cell times
the level program per second.** Under the conditions of
`mul_levelLatency_le_cell`, let also the first block `b` of the
window of the cell be requested no later than `j * ℓ + δ + A`, for the
least delay `δ`, and the `i`-th block after it at most `i * A` later, for
`i < Nbar`. -/
theorem mul_levelValue_le_cellValue (m : GenerativeWorld H R) (f : Member H R)
    (d₁ : Draw H R) (w₁ : World H R) (lookahead : ℕ+) (r : Fin R)
    {s ℓ A pc₀ pr₀ lead Gcap : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hA : 0 < A) (hpc₀ : 0 ≤ pc₀)
    (hcap : 0 ≤ Gcap) {pc pr : ℕ → ℝ} (cl : ℝ≥0∞) (Xmax : ℝ) (Nbar : ℕ) (w' : ℝ≥0∞)
    {j b : ℕ} (hbdef : cellBlock w₁ r ℓ (leastDelayTo m f d₁ r) j = b) (hb : 1 ≤ b)
    (hpc : pc (b - 1) = pc₀) (hpr : pr (b - 1) = pr₀)
    (hgap0 : 0 < (w₁.speaker r).asked b - (w₁.speaker r).asked (b - 1))
    (hgap : (w₁.speaker r).asked b - (w₁.speaker r).asked (b - 1) ≤ A)
    (hlead : lead ≤ (w₁.speaker r).out (b * m.blockSize) - (w₁.speaker r).asked b)
    (hfirst : (w₁.speaker r).asked b ≤ (j : ℝ) * ℓ + leastDelayTo m f d₁ r + A)
    (hspace : ∀ i, i < Nbar →
      (w₁.speaker r).asked (b + i) ≤ (w₁.speaker r).asked b + (i : ℝ) * A) :
    ENNReal.ofReal ℓ * levelValue m f lookahead r s (leastDelayTo m f d₁ r) lead A pc₀ pr₀
        Gcap cl Xmax Nbar w'
      ≤ cellValue m f d₁ w₁ lookahead r s ℓ (leastDelayTo m f d₁ r) pc pr Gcap cl Xmax Nbar
        (pauseCount m f ℓ r) w' j := by
  have hrate := f.linkPauseRate_nonneg m.sender (m.host r)
  have hcount : ENNReal.ofReal ((pauseCount m f ℓ r : ℝ≥0) : ℝ)
      = ENNReal.ofReal ℓ * ENNReal.ofReal (f.linkPauseRate m.sender (m.host r)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    show ENNReal.ofReal (f.linkPauseRate m.sender (m.host r) * ℓ) = _
    rw [ENNReal.ofReal_mul hrate, mul_comm]
  have hBnn : (0 : ℝ) ≤ (m.blockSize : ℝ) := Nat.cast_nonneg _
  unfold levelValue cellValue
  refine le_iInf fun ρ => (mul_le_mul' le_rfl (iInf_le _ ρ)).trans ?_
  rw [mul_add]
  refine add_le_add (mul_levelLatency_le_cell m f d₁ w₁ lookahead r hs hℓ hA hpc₀ hcap
    cl hbdef hb hpc hpr hgap0 hgap hlead ρ) ?_
  rw [hcount, ← mul_assoc]
  refine mul_le_mul' le_rfl (lintegral_mono fun x => mul_le_mul' le_rfl
    (ENNReal.ofReal_le_ofReal ?_))
  have hwin : min Nbar ⌊min x Xmax / A⌋₊
      ≤ windowCount (w₁.speaker r).asked ℓ (leastDelayTo m f d₁ r) Xmax Nbar j x := by
    refine le_windowCount hA ?_ ?_
    · have hb' : firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + leastDelayTo m f d₁ r)
          = b := hbdef
      rw [hb']
      exact hfirst
    · intro i hi
      have hb' : firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + leastDelayTo m f d₁ r)
          = b := hbdef
      rw [hb']
      exact hspace i hi
  have hwinR : ((min Nbar ⌊min x Xmax / A⌋₊ : ℕ) : ℝ)
      ≤ (windowCount (w₁.speaker r).asked ℓ (leastDelayTo m f d₁ r) Xmax Nbar j x : ℝ) := by
    exact_mod_cast hwin
  have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwinR hBnn) hs
  linarith

end Unisono.Spec.GenerativeWorld
