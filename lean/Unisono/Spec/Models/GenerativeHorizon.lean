/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeCellPause
public import Unisono.Spec.Models.GenerativeBlockSum

/-!
# The cells of one speaker up to a horizon

`Prior.cell_mean_ge` bounds the mean cost of one cell by the level program
of the cell. This file sums over the cells of one speaker whose windows end
by playback block `N`, with the clocks of a fixed outcome.

* `sum_ite_cellSamples_le`: the missed samples and discontinuities of the
  windows of the cells that count are at most those of all output samples
  before `N * B`. A cell counts when no paused time begins in the `m` cells
  before it; such windows do not overlap.
* `sum_share_le`: each cell takes the share `ℓ / (asked b - asked (b - 1))`
  of a quantity of playback block `b - 1`, where `b` is the first block of
  its window; the shares of one block add up to at most one.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal

/-- **The windows of the cells that count, against all output samples.** Let
`J` be a finite set of cells whose windows end by playback block `N`, and
`C j` a condition under which no paused time begins in the cells before
cell `j` that are within `m` cells of it, with `Xmax ≤ (m + 1) * ℓ`. For
`g ≥ 0`: the sum over the cells of `J` that satisfy `C` of the sum of `g`
over the output samples of the window is at most the sum of `g` over the
output samples before `N * B`. -/
theorem sum_ite_cellSamples_le {asked : ℕ → ℝ} (hmono : StrictMono asked) {ℓ δ Xmax : ℝ}
    (hℓ : 0 < ℓ) {m : ℕ} (hX : Xmax ≤ ((m : ℝ) + 1) * ℓ) {Nbar B : ℕ} (hB : 0 < B)
    (hex : ∀ T, ∃ b, T ≤ asked b) {I : ℕ → ℝ} (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (J : Finset ℕ)
    {N : ℕ} (C : ℕ → Prop) [DecidablePred C]
    (hclear : ∀ j ∈ J, C j → ∀ i, i < j → j ≤ i + m → I i ≤ 0)
    (hN : ∀ j ∈ J, firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + Nbar ≤ N) :
    ∑ j ∈ J, (if C j then
        ENNReal.ofReal (∑ k ∈ cellSamples asked ℓ δ Xmax Nbar B j (I j), g k) else 0)
      ≤ ∑ k ∈ Finset.range (N * B), ENNReal.ofReal (g k) := by
  rw [← Finset.sum_filter]
  have h := sum_cellSamples_le hmono hℓ hX hB hex (I := I) (fun k => ENNReal.ofReal (g k))
    (J.filter C) (N := N)
    (fun j hj => hclear j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2)
    (fun j hj => hN j (Finset.mem_filter.mp hj).1)
  refine le_trans (le_of_eq ?_) h
  exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_sum_of_nonneg fun k _ => hg k

/-- **The shares of the cells of one playback block add up to at most
one.** Let `J` be a finite set of cells; write `b` for the first playback
block requested at or after `(j + 1) * ℓ + δ`, and suppose that `1 ≤ b ≤ N`
and that block `b - 1` is requested before `j * ℓ + δ`. Let `X b ≥ 0` be a
quantity of playback block `b`, for `b < N`. Then the sum over the cells of
`ℓ / (asked b - asked (b - 1))` times `X (b - 1)` is at most the sum of `X`
over the first `N` blocks. -/
theorem sum_share_le {asked : ℕ → ℝ} (hmono : StrictMono asked)
    (hex : ∀ T, ∃ b, T ≤ asked b) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (X : ℕ → ℝ) {N : ℕ}
    (hX0 : ∀ b < N, 0 ≤ X b) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
      ∧ firstFrom asked (((j : ℝ) + 1) * ℓ + δ) ≤ N
      ∧ asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1) < (j : ℝ) * ℓ + δ) :
    ∑ j ∈ J, ENNReal.ofReal
        (ℓ / (asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ))
            - asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1))
          * X (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1))
      ≤ ∑ b ∈ Finset.range N, ENNReal.ofReal (X b) := by
  classical
  have hmaps : ∀ j ∈ J, firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1 ∈ Finset.range N :=
    fun j hj => Finset.mem_range.mpr (by
      have h1 := (hJ j hj).1
      have h2 := (hJ j hj).2.1
      omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun b hb => ?_
  have hbN := Finset.mem_range.mp hb
  have hfib : ∀ j ∈ J.filter (fun j : ℕ => firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1 = b),
      firstFrom asked (((j : ℝ) + 1) * ℓ + δ) = b + 1 := fun j hj => by
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := (hJ j (Finset.mem_filter.mp hj).1).1
    omega
  have hcard := card_mul_le_of_firstFrom hmono hex hℓ (δ := δ) (b := b + 1)
    (J.filter (fun j : ℕ => firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1 = b)) (fun j hj => by
      have h3 := (hJ j (Finset.mem_filter.mp hj).1).2.2
      rw [hfib j hj] at h3
      exact ⟨hfib j hj, h3⟩)
  rw [Nat.add_sub_cancel] at hcard
  have hden : 0 < asked (b + 1) - asked b := sub_pos.mpr (hmono (Nat.lt_succ_self b))
  have hterm : ∀ j ∈ J.filter (fun j : ℕ => firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1 = b),
      ENNReal.ofReal
          (ℓ / (asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ))
              - asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1))
            * X (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1))
        = ENNReal.ofReal (ℓ / (asked (b + 1) - asked b) * X b) := fun j hj => by
    rw [hfib j hj, Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ((J.filter (fun j : ℕ => firstFrom asked (((j : ℝ) + 1) * ℓ + δ) - 1 = b)).card : ℝ)
      * (ℓ / (asked (b + 1) - asked b)) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one hden).mpr hcard
  have h2 := mul_le_mul_of_nonneg_right h1 (hX0 b hbN)
  linarith

/-- The sum of the means of finitely many functions is at most the mean of
their sum. No measurability is needed. -/
theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (J : Finset ι) (F : ι → α → ℝ≥0∞) :
    ∑ j ∈ J, ∫⁻ a, F j a ∂μ ≤ ∫⁻ a, ∑ j ∈ J, F j a ∂μ := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    rw [Finset.sum_insert hj]
    calc ∫⁻ a, F j a ∂μ + ∑ i ∈ J, ∫⁻ a, F i a ∂μ
        ≤ ∫⁻ a, F j a ∂μ + ∫⁻ a, ∑ i ∈ J, F i a ∂μ := add_le_add le_rfl ih
      _ ≤ ∫⁻ a, (F j a + ∑ i ∈ J, F i a) ∂μ := MeasureTheory.le_lintegral_add _ _
      _ = ∫⁻ a, ∑ i ∈ insert j J, F i a ∂μ := by simp only [Finset.sum_insert hj]

end Unisono.Spec

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {Ω : Type} [MeasurableSpace Ω]
  {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R}

/-- The first playback block of the window of cell `j`: the first block of
speaker `r` that is requested at or after `(j + 1) * ℓ + δ`. -/
def cellBlock (w₁ : World H R) (r : Fin R) (ℓ δ : ℝ) (j : ℕ) : ℕ :=
  firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ)

/-- The latency term of the level program of cell `j`, as a function of the
room `ρ` before the first block `b` of the window of the cell: the weight
`cl` times the share `ℓ / (asked b - asked (b - 1))` of what the room implies
for the latency of the frames of playback block `b - 1`, which is `pc`
times `s * (blockSize - 1)` times the smaller of `roomLatency` (zero if
negative) and `Gcap`. -/
def cellLatency (m : GenerativeWorld H R) (f : Member H R) (d₁ : Draw H R) (w₁ : World H R)
    (lookahead : ℕ+) (r : Fin R) (s ℓ δ : ℝ) (pc pr : ℕ → ℝ) (Gcap : ℝ) (cl : ℝ≥0∞) (j : ℕ)
    (ρ : ℝ) : ℝ≥0∞ :=
  cl * ENNReal.ofReal
    (ℓ / ((w₁.speaker r).asked (cellBlock w₁ r ℓ δ j)
        - (w₁.speaker r).asked (cellBlock w₁ r ℓ δ j - 1))
      * (pc (cellBlock w₁ r ℓ δ j - 1) * (s * ((m.blockSize : ℝ) - 1)
        * min (max (roomLatency m f d₁ w₁ lookahead r s (pc (cellBlock w₁ r ℓ δ j - 1))
          (pr (cellBlock w₁ r ℓ δ j - 1)) (cellBlock w₁ r ℓ δ j - 1) ρ) 0) Gcap)))

/-- **The level program of cell `j`**: the least, over the rooms `ρ ≥ 0`,
of the latency term for the room plus `count` times the mean, over the
length `x` of one pause, of `w'` times what such a pause costs at least with
that room: `s` for each output sample of the window, minus the room, minus
`s`. -/
def cellValue (m : GenerativeWorld H R) (f : Member H R) (d₁ : Draw H R) (w₁ : World H R)
    (lookahead : ℕ+) (r : Fin R) (s ℓ δ : ℝ) (pc pr : ℕ → ℝ) (Gcap : ℝ) (cl : ℝ≥0∞)
    (Xmax : ℝ) (Nbar : ℕ) (count : ℝ≥0) (w' : ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ⨅ ρ : {ρ : ℝ // 0 ≤ ρ}, cellLatency m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl j ρ
    + ENNReal.ofReal count * ∫⁻ x in {x : ℝ | x ≠ 0}, w' * ENNReal.ofReal
        (s * ((windowCount (w₁.speaker r).asked ℓ δ Xmax Nbar j x : ℝ) * m.blockSize) - ρ - s)
      ∂(f.linkPauseLength m.sender (m.host r))

/-- The least of the latency term of cell `j` over the rooms `ρ ≥ 0`. -/
def cellFloor (m : GenerativeWorld H R) (f : Member H R) (d₁ : Draw H R) (w₁ : World H R)
    (lookahead : ℕ+) (r : Fin R) (s ℓ δ : ℝ) (pc pr : ℕ → ℝ) (Gcap : ℝ) (cl : ℝ≥0∞) (j : ℕ) :
    ℝ≥0∞ :=
  ⨅ ρ : {ρ : ℝ // 0 ≤ ρ}, cellLatency m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl j ρ

/-- The draws in which the link from the sender to the host of speaker `r`
pauses nothing from cell `j - m₀` to the beginning of cell `j`. -/
def clearSet (m : GenerativeWorld H R) (r : Fin R) (ℓ : ℝ) (m₀ j : ℕ) : Set (Draw H R) :=
  {e | e.linkPaused m.sender (m.host r) ((j : ℝ) * ℓ)
    - e.linkPaused m.sender (m.host r) (((j - m₀ : ℕ) : ℝ) * ℓ) ≤ 0}

open Classical in
/-- **The cells of one speaker up to a horizon, in the mean over the
pauses.** Fix a draw `d₁` with its world `w₁`, which give the clocks, the
audio devices and the least delays, and take the pauses from a random world
of the member, as in `Prior.cell_mean_ge`. Let `J` be a finite set of cells
in which no playback block is requested, whose windows start at a block
after the first one and end by playback block `N`. Let `pc`, `pr`, `Gcap`
and `p₀` bound the audio devices near the first `N` playback blocks as in
`Builds.sum_blocks_le_latency`.

Then the sum over the cells of `J` of `exp (-count)` times the mean of the
level program of the cell (`cellValue`) where no paused time begins in the
`m₀` cells before it (`clearSet`), and of the least latency term
(`cellFloor`) elsewhere, is at most the mean of: `cl` times the weighted
latency of the frames that the steps before output sample `N * blockSize`
pass on new ground, with the terms of `Builds.sum_blocks_le_latency`, plus
`w'` times the missed samples and `s` times the discontinuities of the
output samples before `N * blockSize`. -/
theorem Prior.sum_cells_le {Msg : Type} (hD : m.Prior f P D) (hm : AEMeasurable D P)
    {d₁ : Draw H R} {w₁ : World H R} (hB₁ : m.Builds f d₁ w₁)
    (hpos₁ : ∀ i j, 0 ≤ d₁.split i j * f.roundTrip i j) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R} (hr : m.host r ≠ m.sender)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {Xmax : ℝ} {Nbar m₀ : ℕ}
    (hX : Xmax ≤ ((m₀ : ℝ) + 1) * ℓ) {w : Ω → World H R} {wOut : ℕ → Ω → World H R}
    (hw : ∀ ω, m.Builds f (d₁.withPaused (D ω)) (w ω))
    (hOut : ∀ j ω, m.Builds f (frameOutside m d₁ (D ω) r ℓ j) (wOut j ω))
    (hslow : ∀ᵐ ω ∂P, ∀ k x y, σ.plays (w ω) lookahead r k = some x →
      σ.plays (w ω) lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {S : ℕ → Set (Draw H R)} {G : ℕ → Draw H R → ℝ} (hS : ∀ k, MeasurableSet (S k))
    (hG : ∀ k, Measurable (G k))
    (hdesc : ∀ j k, ∀ᵐ ω ∂P, ∀ x : ℝ, σ.plays (wOut j ω) lookahead r k = some x ↔
      frameOutside m d₁ (D ω) r ℓ j ∈ S k ∧ G k (frameOutside m d₁ (D ω) r ℓ j) = x)
    {δ : ℝ} (hδ : δ = d₁.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    {count : ℝ≥0}
    (hcount : count = Real.toNNReal (f.linkPauseRate m.sender (m.host r) * ℓ))
    {pc pr : ℕ → ℝ} {Gcap p₀ : ℝ} (hcap : 0 ≤ Gcap) (hp₀ : 0 ≤ p₀) (N : ℕ)
    (hpc0 : ∀ b < N, 0 ≤ pc b) (hpcle : ∀ b < N, pc b ≤ p₀)
    (hpr : ∀ b < N, ∀ k, b * m.blockSize ≤ k → k < (b + 1) * m.blockSize →
      (w₁.speaker r).out (k + 1) - (w₁.speaker r).out k ≤ pr b)
    (hpc : ∀ b < N, ∀ i, (w₁.speaker r).out (b * m.blockSize) - Gcap < w₁.source.capture i →
      w₁.source.capture (i + 1) ≤ (w₁.speaker r).asked (b + 1) →
      pc b ≤ w₁.source.capture (i + 1) - w₁.source.capture i)
    (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ cellBlock w₁ r ℓ δ j ∧ cellBlock w₁ r ℓ δ j + Nbar ≤ N
      ∧ ∀ b' < cellBlock w₁ r ℓ δ j, (w₁.speaker r).asked b' < (j : ℝ) * ℓ + δ)
    (cl w' : ℝ≥0∞) :
    ∑ j ∈ J, ∫⁻ ω, ENNReal.ofReal (Real.exp (-(count : ℝ)))
        * (if frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j then
            cellValue m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl Xmax Nbar count w' j
          else cellFloor m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl j) ∂P
      ≤ ∫⁻ ω, (cl * (∑ n ∈ newFrames (σ.plays (w ω) lookahead r) 0 (N * m.blockSize),
              ((w ω).latencyAt (σ.plays (w ω) lookahead) r n
                  * ENNReal.ofReal ((w ω).source.capture (n + 1) - (w ω).source.capture n)
                + ENNReal.ofReal Gcap
                  * ENNReal.ofReal
                    (p₀ - ((w ω).source.capture (n + 1) - (w ω).source.capture n)))
            + ENNReal.ofReal (p₀ * ((N : ℝ) * ((1 + s) * Gcap)
                + ((1 + 2 * s) * (2 + 1 / s) * Gcap
                    + s * ((m.blockSize : ℝ) - 1) * p₀ * (2 * s + 1))
                  * missedBefore (σ.plays (w ω) lookahead r) (N * m.blockSize + 1))))
          + w' * ∑ k ∈ Finset.range (N * m.blockSize),
              ENNReal.ofReal ((missedAt (σ.plays (w ω) lookahead r) k : ℝ)
                + s * (discontinuityAt (σ.plays (w ω) lookahead r) k : ℝ))) ∂P := by
  have := hD.prob
  have hmonoA : StrictMono (w₁.speaker r).asked := (w₁.speaker r).asked_strictMono
  have hexA : ∀ T, ∃ b, T ≤ (w₁.speaker r).asked b := fun T => hB₁.exists_le_asked r T
  have hB1 : (0 : ℝ) ≤ (m.blockSize : ℝ) - 1 := by
    have h1 : 1 ≤ m.blockSize := m.blockSize_pos
    have h2 : (1 : ℝ) ≤ (m.blockSize : ℝ) := by exact_mod_cast h1
    linarith
  have hφ : ∀ j, Measurable (cellLatency m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl j) :=
    fun j => by
      unfold cellLatency roomLatency
      refine measurable_const.mul (ENNReal.measurable_ofReal.comp ?_)
      refine measurable_const.mul (measurable_const.mul (measurable_const.mul ?_))
      refine Measurable.min (Measurable.max ?_ measurable_const) measurable_const
      exact ((measurable_const.add (measurable_const.mul
        ((measurable_id.add measurable_const).sub measurable_const))).sub
          measurable_const).sub measurable_const
  have hSC : ∀ j, MeasurableSet (clearSet m r ℓ m₀ j) := fun j => by
    have h1 : ∀ t, Measurable fun e : Draw H R => e.linkPaused m.sender (m.host r) t :=
      fun t => (measurable_pi_apply t).comp ((measurable_pi_apply (m.host r)).comp
        ((measurable_pi_apply m.sender).comp measurable_draw_linkPaused))
    exact measurableSet_le ((h1 _).sub (h1 _)) measurable_const
  have hcountj : ∀ j : ℕ, count = Real.toNNReal
      (f.linkPauseRate m.sender (m.host r) * (((j : ℝ) + 1) * ℓ - (j : ℝ) * ℓ)) := fun j => by
    rw [hcount]
    congr 2
    ring
  -- One cell.
  have hcell : ∀ j ∈ J, ∫⁻ ω, ENNReal.ofReal (Real.exp (-(count : ℝ)))
        * (if frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j then
            cellValue m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl Xmax Nbar count w' j
          else cellFloor m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl j) ∂P
      ≤ ∫⁻ ω, (cellLatency m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl j
            (max (room m f (d₁.withPaused (D ω)) (w ω) lookahead
              (σ.plays (w ω) lookahead r) r (cellBlock w₁ r ℓ δ j)) 0)
          + (if frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j then
              w' * ENNReal.ofReal
                (∑ k ∈ cellSamples (w₁.speaker r).asked ℓ δ Xmax Nbar m.blockSize j
                    (cellIncrement m (D ω) r ℓ j),
                  ((missedAt (σ.plays (w ω) lookahead r) k : ℝ)
                    + s * (discontinuityAt (σ.plays (w ω) lookahead r) k : ℝ)))
            else 0)) ∂P := fun j hj =>
    hD.cell_mean_ge hm hB₁ hpos₁ σ hstar lookahead hr hs.le hs1 hℓ.le j hw (hOut j) hslow hS
      hG (hdesc j) hδ (β₀ := cellBlock w₁ r ℓ δ j) rfl (hJ j hj).2.2 rfl (hcountj j) (hφ j) w'
      (hSC j)
  refine le_trans (Finset.sum_le_sum hcell) ?_
  refine le_trans (sum_lintegral_le J _) ?_
  refine lintegral_mono_ae ?_
  filter_upwards [hslow] with ω hslowω
  obtain ⟨-, -, -, hsrc, hspk, -⟩ := hB₁.same_devices (hw ω) rfl rfl rfl rfl rfl rfl
  have hsum := (hw ω).sum_blocks_le_latency hpos₁
    (fun i j' => hD.linkPaused_monotone ω i j') (fun x => hD.hostPaused_monotone ω x) σ hstar
    lookahead hr hs (fun k x h => ((hw ω).arrival_lt_of_plays hpos₁ (fun i j' => hD.linkPaused_monotone ω i j')
      (fun y => hD.hostPaused_monotone ω y) σ hstar lookahead hr h).1) hslowω hcap hp₀ N hpc0
    hpcle (by
      rw [hspk]
      exact hpr) (by
      rw [hspk, hsrc]
      exact hpc)
  have hRL : ∀ (b : ℕ) (ρ : ℝ), roomLatency m f (d₁.withPaused (D ω)) (w ω) lookahead r s
      (pc b) (pr b) b ρ = roomLatency m f d₁ w₁ lookahead r s (pc b) (pr b) b ρ :=
    fun b ρ => by
      unfold roomLatency
      rw [hspk]
      rfl
  simp only [hRL] at hsum
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · -- The latency terms of the cells are shares of the terms of the blocks.
    obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ, X = fun b => pc b * (s * ((m.blockSize : ℝ) - 1)
        * min (max (roomLatency m f d₁ w₁ lookahead r s (pc b) (pr b) b
          (max (room m f (d₁.withPaused (D ω)) (w ω) lookahead (σ.plays (w ω) lookahead r) r
            (b + 1)) 0)) 0) Gcap) := ⟨_, rfl⟩
    have hX0 : ∀ b < N, 0 ≤ X b := fun b hb => by
      rw [hXdef]
      exact mul_nonneg (hpc0 b hb) (mul_nonneg (mul_nonneg hs.le hB1)
        (le_min (le_max_right _ _) hcap))
    have hterm : ∀ j ∈ J, cellLatency m f d₁ w₁ lookahead r s ℓ δ pc pr Gcap cl j
          (max (room m f (d₁.withPaused (D ω)) (w ω) lookahead
            (σ.plays (w ω) lookahead r) r (cellBlock w₁ r ℓ δ j)) 0)
        = cl * ENNReal.ofReal
          (ℓ / ((w₁.speaker r).asked (firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ))
              - (w₁.speaker r).asked
                (firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ) - 1))
            * X (firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ) - 1)) :=
      fun j hj => by
        have h1 : cellBlock w₁ r ℓ δ j - 1 + 1 = cellBlock w₁ r ℓ δ j :=
          Nat.sub_add_cancel (hJ j hj).1
        unfold cellBlock at h1
        rw [hXdef]
        unfold cellLatency cellBlock
        simp only
        rw [h1]
    have hJ' : ∀ j ∈ J, 1 ≤ firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ)
        ∧ firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ) ≤ N
        ∧ (w₁.speaker r).asked
            (firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ) - 1)
          < (j : ℝ) * ℓ + δ := fun j hj => by
      obtain ⟨h1, h2, h3⟩ := hJ j hj
      unfold cellBlock at h1 h2 h3
      exact ⟨h1, by omega, h3 _ (by omega)⟩
    have hshare := sum_share_le hmonoA hexA hℓ (δ := δ) X hX0 J hJ'
    have hsum' : ∑ b ∈ Finset.range N, ENNReal.ofReal (X b)
        ≤ ∑ n ∈ newFrames (σ.plays (w ω) lookahead r) 0 (N * m.blockSize),
            ((w ω).latencyAt (σ.plays (w ω) lookahead) r n
                * ENNReal.ofReal ((w ω).source.capture (n + 1) - (w ω).source.capture n)
              + ENNReal.ofReal Gcap
                * ENNReal.ofReal
                  (p₀ - ((w ω).source.capture (n + 1) - (w ω).source.capture n)))
          + ENNReal.ofReal (p₀ * ((N : ℝ) * ((1 + s) * Gcap)
              + ((1 + 2 * s) * (2 + 1 / s) * Gcap
                  + s * ((m.blockSize : ℝ) - 1) * p₀ * (2 * s + 1))
                * missedBefore (σ.plays (w ω) lookahead r) (N * m.blockSize + 1))) := by
      rw [hXdef]
      exact hsum
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    exact mul_le_mul' le_rfl (hshare.trans hsum')
  · -- The windows of the cells that count do not overlap.
    have hg : ∀ k, 0 ≤ (missedAt (σ.plays (w ω) lookahead r) k : ℝ)
        + s * (discontinuityAt (σ.plays (w ω) lookahead r) k : ℝ) := fun k =>
      add_nonneg (Nat.cast_nonneg _) (mul_nonneg hs.le (Nat.cast_nonneg _))
    have hclear : ∀ j ∈ J, frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j →
        ∀ i, i < j → j ≤ i + m₀ → cellIncrement m (D ω) r ℓ i ≤ 0 := by
      intro j _ hC i hij hjm
      have hab : (j : ℝ) * ℓ ≤ ((j : ℝ) + 1) * ℓ := by nlinarith
      have hlp : (frameOutside m d₁ (D ω) r ℓ j).linkPaused m.sender (m.host r)
          = pathOutside ((j : ℝ) * ℓ) (((j : ℝ) + 1) * ℓ)
            ((D ω).linkPaused m.sender (m.host r)) :=
        (D ω).linkOutside_self m.sender (m.host r) _ _
      have hjm' : (((j - m₀ : ℕ) : ℝ)) * ℓ ≤ (i : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j - m₀ ≤ i)) hℓ.le
      have hij' : ((i : ℝ) + 1) * ℓ ≤ (j : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hℓ.le
      have hjle : (((j - m₀ : ℕ) : ℝ)) * ℓ ≤ (j : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le j m₀) hℓ.le
      have hC' : (frameOutside m d₁ (D ω) r ℓ j).linkPaused m.sender (m.host r) ((j : ℝ) * ℓ)
          - (frameOutside m d₁ (D ω) r ℓ j).linkPaused m.sender (m.host r)
            (((j - m₀ : ℕ) : ℝ) * ℓ) ≤ 0 := hC
      rw [hlp, pathOutside_of_le hab _ le_rfl, pathOutside_of_le hab _ hjle] at hC'
      have hmonoX := hD.linkPaused_monotone ω m.sender (m.host r)
      have h1 := hmonoX hij'
      have h2 := hmonoX hjm'
      unfold cellIncrement
      linarith
    have hN : ∀ j ∈ J, firstFrom (w₁.speaker r).asked (((j : ℝ) + 1) * ℓ + δ) + Nbar ≤ N :=
      fun j hj => (hJ j hj).2.1
    have hwin := sum_ite_cellSamples_le hmonoA hℓ hX m.blockSize_pos hexA (δ := δ)
      (Nbar := Nbar) (Xmax := Xmax) (I := fun i => cellIncrement m (D ω) r ℓ i)
      (fun k => (missedAt (σ.plays (w ω) lookahead r) k : ℝ)
        + s * (discontinuityAt (σ.plays (w ω) lookahead r) k : ℝ)) hg J
      (fun j => frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j) hclear hN
    have hmul : ∀ j ∈ J, (if frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j then
          w' * ENNReal.ofReal
            (∑ k ∈ cellSamples (w₁.speaker r).asked ℓ δ Xmax Nbar m.blockSize j
                (cellIncrement m (D ω) r ℓ j),
              ((missedAt (σ.plays (w ω) lookahead r) k : ℝ)
                + s * (discontinuityAt (σ.plays (w ω) lookahead r) k : ℝ)))
        else 0)
        = w' * (if frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j then
          ENNReal.ofReal
            (∑ k ∈ cellSamples (w₁.speaker r).asked ℓ δ Xmax Nbar m.blockSize j
                (cellIncrement m (D ω) r ℓ j),
              ((missedAt (σ.plays (w ω) lookahead r) k : ℝ)
                + s * (discontinuityAt (σ.plays (w ω) lookahead r) k : ℝ)))
          else 0) := fun j _ => by
      split_ifs
      · rfl
      · rw [mul_zero]
    rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum]
    exact mul_le_mul' le_rfl hwin

end Unisono.Spec.GenerativeWorld
