/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.CellWindows

/-!
# Counting the blocks of a window and the cells that can be counted

True time is cut into cells of length `ℓ`, and `asked b` is the true time at
which a speaker requests its playback block `b`. `Unisono.Spec.CellWindows`
defines the window of a cell: the playback blocks that paused time which
begins in the cell can stall. This file counts, for requests that are at
most `A` apart, how many blocks a window holds at least, and how many cells
satisfy the conditions under which a lower bound on a cost may count them.
Nothing here is random.

* `le_windowCount`: a window holds at least `min Nbar ⌊min x Xmax / A⌋`
  playback blocks, for paused time `x`, when the first block of the window
  is requested at most `A` after the cell begins (shifted by `δ`) and the
  following requests are at most `A` apart.
* `countedCells`: among the first `K` cells, those in which no playback
  block is requested, shifted by `δ`, whose window starts after the first
  playback block and ends by block `N`.
* `le_card_countedCells`: how many such cells there are at least. A cell in
  which a block is requested holds a request of its own, so there are at
  most as many of them as requests.
* `mul_le_card_countedCells_mul`: for requests that are exactly `A` apart,
  the counted cells cover the horizon but for a fraction `ℓ / A` and a
  constant.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- **A window holds at least `min Nbar ⌊min x Xmax / A⌋` playback blocks.**
Let the first block of the window of cell `j` be requested no later than
`j * ℓ + δ + A`, and let the request of the `i`-th block after it come at
most `i * A` later, for `i < Nbar`, with `A > 0`. Then paused time `x`
stalls at least `min Nbar ⌊min x Xmax / A⌋` blocks, where the floor of a
negative number counts as zero. -/
theorem le_windowCount {asked : ℕ → ℝ} {ℓ δ Xmax A : ℝ} (hA : 0 < A) {Nbar j : ℕ} {x : ℝ}
    (hfirst : asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ)) ≤ (j : ℝ) * ℓ + δ + A)
    (hspace : ∀ i, i < Nbar → asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + i)
      ≤ asked (firstFrom asked (((j : ℝ) + 1) * ℓ + δ)) + (i : ℝ) * A) :
    min Nbar ⌊min x Xmax / A⌋₊ ≤ windowCount asked ℓ δ Xmax Nbar j x := by
  classical
  by_cases hx : 0 ≤ min x Xmax
  swap
  · have h0 : ⌊min x Xmax / A⌋₊ = 0 :=
      Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg (not_le.mp hx).le hA.le)
    rw [h0, Nat.min_zero]
    exact Nat.zero_le _
  unfold windowCount
  refine Nat.le_findGreatest (min_le_left _ _) ?_
  by_cases h0 : min Nbar ⌊min x Xmax / A⌋₊ = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    have hpos : 1 ≤ min Nbar ⌊min x Xmax / A⌋₊ := Nat.one_le_iff_ne_zero.mpr h0
    have hlt : min Nbar ⌊min x Xmax / A⌋₊ - 1 < Nbar :=
      lt_of_lt_of_le (Nat.sub_lt hpos Nat.one_pos) (min_le_left _ _)
    have h1 := hspace _ hlt
    have hidx : firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + min Nbar ⌊min x Xmax / A⌋₊ - 1
        = firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + (min Nbar ⌊min x Xmax / A⌋₊ - 1) := by
      omega
    rw [hidx]
    have hfl : ((min Nbar ⌊min x Xmax / A⌋₊ : ℕ) : ℝ) ≤ min x Xmax / A :=
      le_trans (by exact_mod_cast min_le_right Nbar ⌊min x Xmax / A⌋₊)
        (Nat.floor_le (div_nonneg hx hA.le))
    have hmul : ((min Nbar ⌊min x Xmax / A⌋₊ : ℕ) : ℝ) * A ≤ min x Xmax :=
      (le_div_iff₀ hA).mp hfl
    have hcast : ((min Nbar ⌊min x Xmax / A⌋₊ - 1 : ℕ) : ℝ)
        = ((min Nbar ⌊min x Xmax / A⌋₊ : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub hpos, Nat.cast_one]
    rw [hcast] at h1
    nlinarith

/-- **The cells that can be counted for one speaker**: among the first `K`
cells, those whose window starts after the first playback block and ends by
block `N`, when windows hold at most `Nbar` blocks, and in which no playback
block is requested, shifted by `δ`: every block before the first block of
the window is requested before `j * ℓ + δ`. -/
def countedCells (asked : ℕ → ℝ) (ℓ δ : ℝ) (Nbar N K : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range K).filter fun j =>
    1 ≤ firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
      ∧ firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + Nbar ≤ N
      ∧ ∀ b', b' < firstFrom asked (((j : ℝ) + 1) * ℓ + δ) → asked b' < (j : ℝ) * ℓ + δ

theorem mem_countedCells {asked : ℕ → ℝ} {ℓ δ : ℝ} {Nbar N K j : ℕ} :
    j ∈ countedCells asked ℓ δ Nbar N K ↔ j < K
      ∧ 1 ≤ firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
      ∧ firstFrom asked (((j : ℝ) + 1) * ℓ + δ) + Nbar ≤ N
      ∧ ∀ b', b' < firstFrom asked (((j : ℝ) + 1) * ℓ + δ) → asked b' < (j : ℝ) * ℓ + δ := by
  classical
  unfold countedCells
  rw [Finset.mem_filter, Finset.mem_range]

/-- There are at most `K` counted cells. -/
theorem card_countedCells_le (asked : ℕ → ℝ) (ℓ δ : ℝ) (Nbar N K : ℕ) :
    (countedCells asked ℓ δ Nbar N K).card ≤ K := by
  classical
  unfold countedCells
  exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range K))

/-- **How many cells can be counted at least.** Let the requests `asked` be
without bound, and let the first `K` cells reach the request of block
`N - Nbar`, shifted by `δ`. Then the counted cells number at least the cells
between the request of block `0` and the request of block `N - Nbar`, minus
two, minus one for each of the `N - Nbar` requests before that block. -/
theorem le_card_countedCells {asked : ℕ → ℝ} (hex : ∀ T, ∃ b, T ≤ asked b) {ℓ δ : ℝ}
    (hℓ : 0 < ℓ) {Nbar N K : ℕ}
    (hK : (asked (N - Nbar) - δ) / ℓ ≤ K) :
    (asked (N - Nbar) - δ) / ℓ - 1 - (max ((asked 0 - δ) / ℓ) 0 + 1) - ((N - Nbar : ℕ) : ℝ)
      ≤ ((countedCells asked ℓ δ Nbar N K).card : ℝ) := by
  classical
  -- The cells from `j₀` to `K₁`: after the first request and before the last one.
  set j₀ : ℕ := ⌈(asked 0 - δ) / ℓ⌉₊ with hj₀
  set K₁ : ℕ := ⌊(asked (N - Nbar) - δ) / ℓ⌋₊ with hK₁
  have hK₁K : K₁ ≤ K := Nat.floor_le_of_le hK
  have hj₀le : (asked 0 - δ) / ℓ ≤ (j₀ : ℝ) := Nat.le_ceil _
  have hj₀lt : (j₀ : ℝ) < max ((asked 0 - δ) / ℓ) 0 + 1 :=
    lt_of_le_of_lt (by exact_mod_cast Nat.ceil_mono (le_max_left ((asked 0 - δ) / ℓ) 0))
      (Nat.ceil_lt_add_one (le_max_right _ _))
  have hK₁gt : (asked (N - Nbar) - δ) / ℓ - 1 < (K₁ : ℝ) := Nat.sub_one_lt_floor _
  -- Facts about a cell between the two.
  have hfacts : ∀ j, j₀ ≤ j → j < K₁ → 1 ≤ firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
      ∧ firstFrom asked (((j : ℝ) + 1) * ℓ + δ) ≤ N - Nbar := by
    intro j hj hjK
    have hjr : (j₀ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hstart : asked 0 ≤ (j : ℝ) * ℓ + δ := by
      have h1 : (asked 0 - δ) / ℓ ≤ (j : ℝ) := le_trans hj₀le hjr
      have h2 := (div_le_iff₀ hℓ).mp h1
      linarith
    have hK₁pos : 0 < K₁ := lt_of_le_of_lt (Nat.zero_le j) hjK
    have hxpos : 0 < (asked (N - Nbar) - δ) / ℓ := Nat.pos_of_floor_pos hK₁pos
    have hend : ((j : ℝ) + 1) * ℓ + δ ≤ asked (N - Nbar) := by
      have h1 : ((j : ℝ) + 1) ≤ (K₁ : ℝ) := by exact_mod_cast hjK
      have h2 : (K₁ : ℝ) ≤ (asked (N - Nbar) - δ) / ℓ := Nat.floor_le hxpos.le
      have h3 := (le_div_iff₀ hℓ).mp (le_trans h1 h2)
      linarith
    refine ⟨?_, ?_⟩
    · by_contra hcon
      have h0 : firstFrom asked (((j : ℝ) + 1) * ℓ + δ) = 0 := by omega
      have h1 := le_asked_firstFrom (hex (((j : ℝ) + 1) * ℓ + δ))
      rw [h0] at h1
      nlinarith
    · by_contra hcon
      have h1 := asked_lt_of_lt_firstFrom (hex (((j : ℝ) + 1) * ℓ + δ)) (not_le.mp hcon)
      linarith
  -- The cells in which a block is requested.
  set usable : ℕ → Prop := fun j =>
    ∀ b', b' < firstFrom asked (((j : ℝ) + 1) * ℓ + δ) → asked b' < (j : ℝ) * ℓ + δ with husable
  have hgood : (Finset.Ico j₀ K₁).filter usable ⊆ countedCells asked ℓ δ Nbar N K := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨⟨hj1, hj2⟩, hu⟩ := hj
    obtain ⟨h1, h2⟩ := hfacts j hj1 hj2
    refine mem_countedCells.mpr ⟨lt_of_lt_of_le hj2 hK₁K, h1, ?_, hu⟩
    by_cases hN : Nbar ≤ N
    · omega
    · have h3 : N - Nbar = 0 := by omega
      omega
  have hex' : ∀ j, ¬ usable j → ∃ b', b' < firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
      ∧ (j : ℝ) * ℓ + δ ≤ asked b' := by
    intro j hj
    rw [husable] at hj
    push Not at hj
    exact hj
  set g : ℕ → ℕ := fun j => if h : ¬ usable j then Classical.choose (hex' j h) else 0 with hg
  have hgspec : ∀ j, ¬ usable j → g j < firstFrom asked (((j : ℝ) + 1) * ℓ + δ)
      ∧ (j : ℝ) * ℓ + δ ≤ asked (g j) := by
    intro j hj
    have hgj : g j = Classical.choose (hex' j hj) :=
      show (if h : ¬ usable j then Classical.choose (hex' j h) else 0) = _ from
        dite_eq_left hj
    rw [hgj]
    exact Classical.choose_spec (hex' j hj)
  have hbad : ((Finset.Ico j₀ K₁).filter fun j => ¬ usable j).card ≤ N - Nbar := by
    have hmaps : ∀ j ∈ (Finset.Ico j₀ K₁).filter (fun j => ¬ usable j),
        g j ∈ Finset.range (N - Nbar) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Ico] at hj
      obtain ⟨⟨hj1, hj2⟩, hu⟩ := hj
      have h1 := (hgspec j hu).1
      have h2 := (hfacts j hj1 hj2).2
      exact Finset.mem_range.mpr (lt_of_lt_of_le h1 h2)
    have hinj : Set.InjOn g ((Finset.Ico j₀ K₁).filter (fun j => ¬ usable j) : Set ℕ) := by
      intro j hj j' hj' hgg
      have hu : ¬ usable j := (Finset.mem_filter.mp hj).2
      have hu' : ¬ usable j' := (Finset.mem_filter.mp hj').2
      have hlt : ∀ a c : ℕ, ¬ usable a → ¬ usable c → g a = g c → ¬ a < c := by
        intro a c ha hc hac hlt
        have h1 := asked_lt_of_lt_firstFrom (hex (((a : ℝ) + 1) * ℓ + δ)) (hgspec a ha).1
        have h2 := (hgspec c hc).2
        rw [← hac] at h2
        have h3 : (a : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast hlt
        nlinarith
      rcases Nat.lt_trichotomy j j' with h | h | h
      · exact absurd h (hlt j j' hu hu' hgg)
      · exact h
      · exact absurd h (hlt j' j hu' hu hgg.symm)
    exact le_trans (Finset.card_le_card_of_injOn g hmaps hinj)
      (le_of_eq (Finset.card_range _))
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Ico j₀ K₁) usable
  rw [Nat.card_Ico] at hsplit
  have hcard := Finset.card_le_card hgood
  have hnat : K₁ - j₀ ≤ (countedCells asked ℓ δ Nbar N K).card + (N - Nbar) := by omega
  have hreal : (K₁ : ℝ) - (j₀ : ℝ)
      ≤ ((countedCells asked ℓ δ Nbar N K).card : ℝ) + ((N - Nbar : ℕ) : ℝ) := by
    have h1 : (K₁ : ℝ) ≤ ((K₁ - j₀ : ℕ) : ℝ) + (j₀ : ℝ) := by
      exact_mod_cast (by omega : K₁ ≤ K₁ - j₀ + j₀)
    have h2 : ((K₁ - j₀ : ℕ) : ℝ)
        ≤ (((countedCells asked ℓ δ Nbar N K).card + (N - Nbar) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at h2
    linarith
  linarith

/-- **With evenly spaced requests, the counted cells cover the horizon but
for a fraction `ℓ / A` and a constant.** Let block `b` be requested at
`a₀ + b * A`, with cells of length `0 < ℓ ≤ A`. Let the first `K` cells
reach the request of block `N - Nbar`, shifted by `δ`, and let
`T ≤ o + (N + 1) * A`. Then `T * (1 - ℓ / A)` is at most the number of
counted cells times `ℓ`, plus
`|o| + (Nbar + 1) * A + max (δ - a₀) 0 + 2 * ℓ`. -/
theorem mul_le_card_countedCells_mul {asked : ℕ → ℝ} {a₀ A : ℝ} (hA : 0 < A)
    (hasked : ∀ b, asked b = a₀ + (b : ℝ) * A) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hℓA : ℓ ≤ A)
    {Nbar N K : ℕ} (hK : (asked (N - Nbar) - δ) / ℓ ≤ K) {T o : ℝ}
    (hT : T ≤ o + ((N : ℝ) + 1) * A) :
    T * (1 - ℓ / A)
      ≤ ((countedCells asked ℓ δ Nbar N K).card : ℝ) * ℓ
        + (|o| + ((Nbar : ℝ) + 1) * A + max (δ - a₀) 0 + 2 * ℓ) := by
  have hex : ∀ T', ∃ b, T' ≤ asked b := fun T' => by
    obtain ⟨b, hb⟩ := exists_nat_ge ((T' - a₀) / A)
    refine ⟨b, ?_⟩
    rw [hasked]
    have h1 := (div_le_iff₀ hA).mp hb
    linarith
  have h := le_card_countedCells hex hℓ hK
  have hn'ge : (N : ℝ) - Nbar ≤ ((N - Nbar : ℕ) : ℝ) := by
    by_cases hle : Nbar ≤ N
    · rw [Nat.cast_sub hle]
    · have h0 : N - Nbar = 0 := by omega
      have h1 : (N : ℝ) < (Nbar : ℝ) := by exact_mod_cast not_le.mp hle
      rw [h0, Nat.cast_zero]
      linarith
  have hn'0 : (0 : ℝ) ≤ ((N - Nbar : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha0 : asked 0 = a₀ := by
    rw [hasked, Nat.cast_zero, zero_mul, add_zero]
  rw [hasked (N - Nbar), ha0] at h
  generalize ((N - Nbar : ℕ) : ℝ) = n' at h hn'ge hn'0
  generalize ((countedCells asked ℓ δ Nbar N K).card : ℝ) = card at h ⊢
  have hmax : max ((a₀ - δ) / ℓ) 0 * ℓ = max (a₀ - δ) 0 := by
    rcases le_total 0 (a₀ - δ) with h0 | h0
    · rw [max_eq_left (div_nonneg h0 hℓ.le), max_eq_left h0, div_mul_cancel₀ _ hℓ.ne']
    · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg h0 hℓ.le), max_eq_right h0, zero_mul]
  have h1 : a₀ + n' * A - δ - ℓ - (max (a₀ - δ) 0 + ℓ) - n' * ℓ ≤ card * ℓ := by
    have h2 := mul_le_mul_of_nonneg_right h hℓ.le
    have e : ((a₀ + n' * A - δ) / ℓ - 1 - (max ((a₀ - δ) / ℓ) 0 + 1) - n') * ℓ
        = (a₀ + n' * A - δ) / ℓ * ℓ - ℓ - (max ((a₀ - δ) / ℓ) 0 * ℓ + ℓ) - n' * ℓ := by ring
    rw [e, div_mul_cancel₀ _ hℓ.ne', hmax] at h2
    exact h2
  have ht0 : 0 ≤ 1 - ℓ / A := by
    rw [sub_nonneg, div_le_one hA]
    exact hℓA
  have ht1 : 1 - ℓ / A ≤ 1 := by
    have h2 := div_nonneg hℓ.le hA.le
    linarith
  have hAt : A * (1 - ℓ / A) = A - ℓ := by
    field_simp
  have hTt := mul_le_mul_of_nonneg_right hT ht0
  have hot : o * (1 - ℓ / A) ≤ |o| :=
    calc o * (1 - ℓ / A) ≤ |o| * (1 - ℓ / A) := mul_le_mul_of_nonneg_right (le_abs_self o) ht0
      _ ≤ |o| * 1 := mul_le_mul_of_nonneg_left ht1 (abs_nonneg o)
      _ = |o| := mul_one _
  have hmaxid : a₀ - δ - max (a₀ - δ) 0 = -max (δ - a₀) 0 := by
    rcases le_total 0 (a₀ - δ) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h0, max_eq_left (by linarith)]
      ring
  have hAℓ : 0 ≤ A - ℓ := sub_nonneg.mpr hℓA
  have hN : ((N : ℝ) + 1) * (A - ℓ) ≤ (n' + (Nbar : ℝ) + 1) * (A - ℓ) :=
    mul_le_mul_of_nonneg_right (by linarith) hAℓ
  have hNb : ((Nbar : ℝ) + 1) * (A - ℓ) ≤ ((Nbar : ℝ) + 1) * A :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : (o + ((N : ℝ) + 1) * A) * (1 - ℓ / A)
      = o * (1 - ℓ / A) + ((N : ℝ) + 1) * (A - ℓ) := by
    rw [← hAt]
    ring
  have e3 : (n' + (Nbar : ℝ) + 1) * (A - ℓ)
      = n' * A - n' * ℓ + ((Nbar : ℝ) + 1) * (A - ℓ) := by ring
  rw [e2] at hTt
  rw [e3] at hN
  linarith

end Unisono.Spec
