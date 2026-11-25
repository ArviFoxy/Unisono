/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeEarliest
public import Unisono.Spec.Stall

/-!
# What every solution through the sender pays while a block is on its way

In the generative model, consider a solution whose hosts exchange messages
only with the sender, and a speaker whose host is not the sender's. While
the message of capture block `c` has not arrived, the speaker can play only
positions that need earlier blocks.

* `Builds.le_of_plays_before`: if the message that the sender sends at the
  handover of capture block `c` has not arrived before the request of
  playback block `β`, every position played at an output sample of a
  playback block up to `β` is at most `c * blockSize - lookahead`.
* `Builds.stall_le`: so the output samples from `k₀` to `K`, all in playback
  blocks up to `β`, cost missed samples and discontinuities
  (`Unisono.Spec.stall_le_of_le`): `s` for each of them is at most the room
  from the position played last before `k₀` to `c * blockSize - lookahead`,
  plus the missed samples counted from `k₀` to `K`, plus `s` times the
  discontinuities counted from `k₀` to `K - 1` and one more. Here `s` is the
  least advance of the position in a step of continuous playback.

Both hold in one outcome, for any draw whose least delays are not negative
and whose paused times never decrease, so in every outcome of every random
world of every member. They are not yet combined into a bound on expected
cost.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] {m : GenerativeWorld H R}
  {f : Member H R} {d : Draw H R} {w : World H R}

/-- **While a block is on its way, only earlier positions can be played.**
Consider a world built from a draw whose least delays are not negative and
whose paused times never decrease, a solution whose hosts exchange messages
only with the sender, and a speaker whose host is not the sender's. If the
message that the sender sends at the handover of capture block `c` has not
arrived before the request of playback block `β`, then every position played
at an output sample of a playback block up to `β` is at most
`c * blockSize - lookahead`. -/
theorem Builds.le_of_plays_before (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {c β k : ℕ} {x : ℝ}
    (hc : (w.speaker r).asked β
      ≤ d.arrival f m.sender (m.host r) (w.source.handed c))
    (hk : k / m.blockSize ≤ β) (hplay : σ.plays w lookahead r k = some x) :
    x ≤ (c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ) := by
  obtain ⟨-, hlt⟩ := hB.arrival_lt_of_plays hpos hlink hhost σ hstar lookahead hr hplay
  have hasked : (w.speaker r).asked (k / m.blockSize) ≤ (w.speaker r).asked β :=
    (w.speaker r).asked_mono hk
  have hA := hB.arrival_mono (hlink m.sender (m.host r)) (hhost m.sender) (hhost (m.host r))
  have hnb : (⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1) / m.blockSize < c := by
    by_contra hge
    have h1 : w.source.handed c
        ≤ w.source.handed ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1) / m.blockSize) :=
      w.source.handed_mono (not_lt.mp hge)
    have h2 := hA h1
    linarith
  have h3 : ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 < c * m.blockSize :=
    (Nat.div_lt_iff_lt_mul m.blockSize_pos).mp hnb
  have h4 : ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ ≤ c * m.blockSize := by
    generalize c * m.blockSize = q at h3 ⊢
    omega
  have h5 := Nat.le_ceil (x + ((lookahead : ℕ) : ℝ))
  have h6 : ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ ((c * m.blockSize : ℕ) : ℝ) := by
    exact_mod_cast h4
  push_cast at h6
  linarith

/-- **What every solution through the sender pays while a block is on its
way.** Consider a world built from a draw whose least delays are not
negative and whose paused times never decrease, a solution whose hosts
exchange messages only with the sender, and a speaker whose host is not the
sender's, whose position advances by at least `s` in every step of
continuous playback, with `0 ≤ s ≤ 1`. Suppose that the message that the
sender sends at the handover of capture block `c` has not arrived before the
request of playback block `β`. Then for output samples `k₀ ≤ K` with `K` in
a playback block up to `β`: `s` for each output sample from `k₀` to `K` is at
most the room from the position played last before `k₀` to
`c * blockSize - lookahead`, plus the missed samples counted from `k₀` to
`K`, plus `s` times the discontinuities counted from `k₀` to `K - 1` and one
more. -/
theorem Builds.stall_le (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {c β k₀ K : ℕ} (hK : k₀ ≤ K) (hKβ : K / m.blockSize ≤ β)
    (hc : (w.speaker r).asked β
      ≤ d.arrival f m.sender (m.host r) (w.source.handed c)) :
    s * ((K : ℝ) + 1 - k₀)
      ≤ max ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
        + ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt (σ.plays w lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt (σ.plays w lookahead r) k : ℝ)
          + 1) := by
  have hnn : ∀ k x, σ.plays w lookahead r k = some x → 0 ≤ x := fun k x hx =>
    (hB.arrival_lt_of_plays hpos hlink hhost σ hstar lookahead hr hx).1
  have hle : ∀ k, k ≤ K → ∀ x, σ.plays w lookahead r k = some x →
      x ≤ (c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ) := fun k hk x hx =>
    hB.le_of_plays_before hpos hlink hhost σ hstar lookahead hr hc
      ((Nat.div_le_div_right hk).trans hKβ) hx
  have hD0 : (0 : ℝ) ≤ ∑ k ∈ Finset.Ico k₀ K,
      (discontinuityAt (σ.plays w lookahead r) k : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (K : ℝ) + 1 - k₀ := by
    have : (k₀ : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  by_cases hP : 0 ≤ (c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
  · -- The position played last before `k₀` is at most the bound.
    have hx₀ : (lastPlayed (σ.plays w lookahead r) k₀).getD 0
        ≤ (c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ) := by
      cases hl : lastPlayed (σ.plays w lookahead r) k₀ with
      | none => simpa using hP
      | some x =>
        obtain ⟨ht, hx⟩ := lastPlayed_some hl
        simp only [Option.getD_some]
        exact hle _ (by omega) x hx
    have h1 := stall_le_of_le hs0 hs1 hnn hslow hK hx₀ fun k _ hkK x hx => hle k hkK x hx
    have h2 := le_max_left ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
      - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
    linarith
  · -- Nothing can be played: every output sample of the stretch is missed.
    have hnone : ∀ k, k ≤ K → σ.plays w lookahead r k = none := by
      intro k hk
      by_contra hne
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
      have h1 := hle k hk x hx
      have h2 := hnn k x hx
      exact hP (h2.trans h1)
    have hM : ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt (σ.plays w lookahead r) k : ℝ)
        = (K : ℝ) + 1 - k₀ := by
      have hone : ∀ k ∈ Finset.Ico k₀ (K + 1),
          (missedAt (σ.plays w lookahead r) k : ℝ) = 1 := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        rw [missedAt_of_none (hnone k (Nat.lt_succ_iff.mp hk.2))]
        norm_num
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
        Nat.cast_sub (Nat.le_succ_of_le hK)]
      push_cast
      ring
    have h2 := le_max_right ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
      - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
    have h3 := mul_le_mul_of_nonneg_right hs1 hn0
    have h4 : (0 : ℝ) ≤ s * (∑ k ∈ Finset.Ico k₀ K,
        (discontinuityAt (σ.plays w lookahead r) k : ℝ) + 1) :=
      mul_nonneg hs0 (by linarith)
    rw [hM]
    linarith

/-- **What every solution through the sender pays while a block is on its
way**, in every outcome of every random world of every member. The statement
of `Builds.stall_le` for the world of the outcome `ω`. -/
theorem Prior.stall_le {Ω : Type} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) (ω : Ω) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays (world ω) lookahead r k = some x →
      σ.plays (world ω) lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {c β k₀ K : ℕ} (hK : k₀ ≤ K) (hKβ : K / m.blockSize ≤ β)
    (hc : ((world ω).speaker r).asked β
      ≤ (D ω).arrival f m.sender (m.host r) ((world ω).source.handed c)) :
    s * ((K : ℝ) + 1 - k₀)
      ≤ max ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays (world ω) lookahead r) k₀).getD 0) 0
        + ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt (σ.plays (world ω) lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico k₀ K,
            (discontinuityAt (σ.plays (world ω) lookahead r) k : ℝ) + 1) :=
  (hB ω).stall_le (fun i j => (hD.leastDelay_pos ω i j).le)
    (fun i j => hD.linkPaused_monotone ω i j) (fun h => hD.hostPaused_monotone ω h) σ hstar
    lookahead hr hs0 hs1 hslow hK hKβ hc

end Unisono.Spec.GenerativeWorld
