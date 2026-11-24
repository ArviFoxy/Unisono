/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Skips
public import Unisono.Spec.StarShift

/-!
# One playback in two worlds that differ by a shift

A star solution plays the same in two worlds that differ by a shift of the
hosts' timelines along the links to and from the sender, while every
speaker's play times move with the timeline of its host. This file bounds
the two costs from below without assuming that every frame is played.

* **One frame** (`World.frame_add_ge`). A speaker that plays the frame pays,
  in the two worlds together, a tracking error of at least half the square
  of its shift, and two speakers that both play it pay a synchronization
  error of at least half the square of the difference of their shifts. So
  the frame costs at least twice `shiftCost` of half the shifts, minus
  `speakerShiftCost / R` for each speaker that does not play it.
* **Until a time** (`World.weighted_frames_add_ge`,
  `World.weighted_missed_eq`). What the frames captured so far have cost in
  the two worlds, and what the missed samples counted so far have paid.
* **One playback** (`World.cost_add_ge_of_shift`). When the position
  advances by at least `s` in every step of continuous playback, and the
  weight of missed samples is at least six times `speakerShiftCost` over
  `s` times the rate, the costs in the two worlds add up to at least twice
  the cost of half the shifts. A frame that a speaker never plays is paid
  for by missed samples, which are counted when the playback passes the
  frame, possibly long after its capture
  (`Unisono.Spec.Skips`).
* **A playback that stops** (`World.cost_ge_of_eventually_none`) costs the
  weight of missed samples at every output sample.
* **A star solution** (`Solution.cost_shiftStar_add_ge_of_step`). A star
  solution whose position advances by one frame per output sample within
  `u < 1`, in every step of continuous playback, pays, in a world and in
  the same world with the links to and from the sender shifted, at least
  twice the cost of half the shift. Nothing is assumed about which frames it
  plays, or about its run: a run that stops decides nothing more
  (`Solution.plays_eq_none_of_stalled`), so the speakers play nothing from
  then on.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal NNReal
open Filter Topology

variable {H : Type} {R : ℕ}

/-! ## Frames that a speaker does not play -/

/-- One if the playback never plays frame `n`, zero if it plays it. -/
def unplayedAt (plays : ℕ → Option ℝ) (n : ℕ) : ℕ := by
  classical
  exact if PlaysFrame plays n then 0 else 1

theorem unplayedAt_of {plays : ℕ → Option ℝ} {n : ℕ} (h : PlaysFrame plays n) :
    unplayedAt plays n = 0 := by
  classical
  unfold unplayedAt
  rw [ite_eq_left h]

theorem unplayedAt_of_not {plays : ℕ → Option ℝ} {n : ℕ} (h : ¬ PlaysFrame plays n) :
    unplayedAt plays n = 1 := by
  classical
  unfold unplayedAt
  rw [ite_eq_right h]

/-- The frames among the first `N` that are never played, counted one by
one. -/
theorem neverPlayed_eq_sum (plays : ℕ → Option ℝ) (N : ℕ) :
    neverPlayed plays N = ∑ n ∈ Finset.range N, unplayedAt plays n := by
  classical
  unfold neverPlayed
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : PlaysFrame plays n
  · rw [unplayedAt_of h]
    simp [h]
  · rw [unplayedAt_of_not h]
    simp [h]

/-- A speaker plays a frame at some time exactly when a step of continuous
playback passes the frame. -/
theorem playTime_isSome_iff (out : ℕ → Time) (plays : ℕ → Option ℝ) (n : ℕ) :
    (playTime out plays n).isSome ↔ PlaysFrame plays n := by
  classical
  unfold playTime
  split_ifs with h
  · obtain ⟨x, y, hx, hy, -⟩ := Nat.find_spec h
    rw [hx, hy]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun hs => absurd hs (by simp), fun hp => absurd hp h⟩

/-- The positive part of a sum is at most the sum of the positive parts. -/
theorem ofReal_sum_le {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-! ## One frame in the two worlds -/

/-- What a shift `x` of the speakers' play times costs at one frame through
speaker `r`, for weights `c`: `c.tracking` times the square of the speaker's
shift, plus `c.sync` times the mean, over the speakers, of the square of the
difference between its shift and theirs. It is what the frame's cost can
fall by, times the number of speakers, when speaker `r` does not play the
frame. -/
def speakerShiftCost (c : Weights) (x : Fin R → ℝ) (r : Fin R) : ℝ :=
  (c.tracking : ℝ) * x r ^ 2 + (c.sync : ℝ) * ((∑ r', (x r - x r') ^ 2) / R)

theorem speakerShiftCost_nonneg (c : Weights) (x : Fin R → ℝ) (r : Fin R) :
    0 ≤ speakerShiftCost c x r := by
  unfold speakerShiftCost
  have h1 : 0 ≤ (∑ r', (x r - x r') ^ 2) / (R : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg R)
  have hs : (0 : ℝ) ≤ c.sync := c.sync.coe_nonneg
  have ht : (0 : ℝ) ≤ c.tracking := c.tracking.coe_nonneg
  positivity

/-- **Two speakers in the two worlds.** If both play the frame, the squares
of the differences of their play times in the two worlds add up to at least
twice the square of the difference of their half shifts. -/
theorem World.pairCost_add_ge (w w' : World H R) (plays : Fin R → ℕ → Option ℝ)
    (x : Fin R → ℝ) (n : ℕ)
    (hshift : ∀ r, w'.playTime plays r n = (w.playTime plays r n).map (· + 2 * x r))
    (a b : Fin R) :
    ENNReal.ofReal (2 * (x a - x b) ^ 2
        - 2 * ((unplayedAt (plays a) n : ℝ) + unplayedAt (plays b) n) * (x a - x b) ^ 2)
      ≤ w.pairCost plays a b n + w'.pairCost plays a b n := by
  have hsq : 0 ≤ (x a - x b) ^ 2 := sq_nonneg _
  by_cases ha : PlaysFrame (plays a) n
  · by_cases hb : PlaysFrame (plays b) n
    · have hsa : (w.playTime plays a n).isSome :=
        (playTime_isSome_iff (w.speaker a).out (plays a) n).mpr ha
      have hsb : (w.playTime plays b n).isSome :=
        (playTime_isSome_iff (w.speaker b).out (plays b) n).mpr hb
      obtain ⟨ta, hta⟩ := Option.isSome_iff_exists.mp hsa
      obtain ⟨tb, htb⟩ := Option.isSome_iff_exists.mp hsb
      have e1 : w.pairCost plays a b n = ENNReal.ofReal ((ta - tb) ^ 2) := by
        simp only [World.pairCost, hta, htb]
      have e2 : w'.pairCost plays a b n
          = ENNReal.ofReal ((ta + 2 * x a - (tb + 2 * x b)) ^ 2) := by
        simp only [World.pairCost, hshift, hta, htb, Option.map_some]
      rw [e1, e2, unplayedAt_of ha, unplayedAt_of hb,
        ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      nlinarith [sq_nonneg (ta - tb + (x a - x b))]
    · rw [unplayedAt_of ha, unplayedAt_of_not hb]
      have hle : 2 * (x a - x b) ^ 2
          - 2 * (((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) * (x a - x b) ^ 2 ≤ 0 := by
        push_cast
        linarith
      rw [ENNReal.ofReal_of_nonpos hle]
      exact zero_le
  · rw [unplayedAt_of_not ha]
    have hub : (0 : ℝ) ≤ unplayedAt (plays b) n := Nat.cast_nonneg _
    have hle : 2 * (x a - x b) ^ 2
        - 2 * (((1 : ℕ) : ℝ) + unplayedAt (plays b) n) * (x a - x b) ^ 2 ≤ 0 := by
      push_cast
      nlinarith
    rw [ENNReal.ofReal_of_nonpos hle]
    exact zero_le

/-- **One speaker in the two worlds.** If it plays the frame, the squares of
its tracking errors in the two worlds add up to at least twice the square of
its half shift. -/
theorem World.trackingAt_add_ge (w w' : World H R) (plays : Fin R → ℕ → Option ℝ)
    (x : Fin R → ℝ) (n : ℕ) (hsrc : w'.source = w.source) (htgt : w'.target = w.target)
    (hshift : ∀ r, w'.playTime plays r n = (w.playTime plays r n).map (· + 2 * x r))
    (r : Fin R) :
    ENNReal.ofReal (2 * x r ^ 2 - 2 * (unplayedAt (plays r) n : ℝ) * x r ^ 2)
      ≤ w.trackingAt plays r n + w'.trackingAt plays r n := by
  by_cases hr : PlaysFrame (plays r) n
  · have hs : (w.playTime plays r n).isSome :=
      (playTime_isSome_iff (w.speaker r).out (plays r) n).mpr hr
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
    have e1 : w.trackingAt plays r n
        = ENNReal.ofReal ((t - w.source.capture n - w.target n) ^ 2) := by
      simp [World.trackingAt, World.latency, ht]
    have e2 : w'.trackingAt plays r n
        = ENNReal.ofReal ((t + 2 * x r - w.source.capture n - w.target n) ^ 2) := by
      simp [World.trackingAt, World.latency, hshift, ht, hsrc, htgt]
    rw [e1, e2, unplayedAt_of hr, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    nlinarith [sq_nonneg (t - w.source.capture n - w.target n + x r)]
  · rw [unplayedAt_of_not hr]
    have hle : 2 * x r ^ 2 - 2 * ((1 : ℕ) : ℝ) * x r ^ 2 ≤ 0 := by
      push_cast
      linarith
    rw [ENNReal.ofReal_of_nonpos hle]
    exact zero_le

/-- **One frame in the two worlds.** Let the same playback run in two worlds
with the same source and targets, in the second of which every speaker `r`
plays each frame `2 * x r` later. The weighted synchronization and tracking
of a frame in the two worlds add up to at least twice the cost of the shift
`x`, minus twice `speakerShiftCost c x r / R` for each speaker `r` that does
not play the frame. -/
theorem World.frame_add_ge (w w' : World H R) (plays : Fin R → ℕ → Option ℝ) (c : Weights)
    (hR : 0 < R) (x : Fin R → ℝ) (n : ℕ) (hsrc : w'.source = w.source)
    (htgt : w'.target = w.target)
    (hshift : ∀ r, w'.playTime plays r n = (w.playTime plays r n).map (· + 2 * x r)) :
    ENNReal.ofReal (2 * shiftCost c x
        - 2 * ∑ r, (unplayedAt (plays r) n : ℝ) * (speakerShiftCost c x r / R))
      ≤ (c.sync : ℝ≥0∞) * (w.syncCost plays n + w'.syncCost plays n)
        + (c.tracking : ℝ≥0∞) * (w.trackingCost plays n + w'.trackingCost plays n) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hR0 : (R : ℝ) ≠ 0 := hRpos.ne'
  let u : Fin R → ℝ := fun r => unplayedAt (plays r) n
  -- The sums of the real lower bounds.
  have hD := sum_pairs_sq_eq_var hR x
  have hU : ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
        (u p.1 + u p.2) * (x p.1 - x p.2) ^ 2
      = ∑ a, u a * ∑ b, (x a - x b) ^ 2 := by
    have h2 := two_mul_sum_pairs (fun a b => (u a + u b) * (x a - x b) ^ 2)
      (fun a b => by ring) (fun a => by ring)
    have hsplit : ∑ a, ∑ b, (u a + u b) * (x a - x b) ^ 2
        = (∑ a, u a * ∑ b, (x a - x b) ^ 2) + ∑ a, u a * ∑ b, (x a - x b) ^ 2 := by
      have h3 : ∑ a, ∑ b, u b * (x a - x b) ^ 2 = ∑ a, u a * ∑ b, (x a - x b) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      have h4 : ∑ a, ∑ b, u a * (x a - x b) ^ 2 = ∑ a, u a * ∑ b, (x a - x b) ^ 2 :=
        Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      have h5 : ∑ a, ∑ b, (u a + u b) * (x a - x b) ^ 2
          = (∑ a, ∑ b, u a * (x a - x b) ^ 2) + ∑ a, ∑ b, u b * (x a - x b) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [h5, h4, h3]
    linarith
  have hS₁ : ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
        (2 * (x p.1 - x p.2) ^ 2 - 2 * (u p.1 + u p.2) * (x p.1 - x p.2) ^ 2)
      = 2 * ((R : ℝ) ^ 2 * varFin x) - 2 * ∑ a, u a * ∑ b, (x a - x b) ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hD, ← hU, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  have hS₂ : ∑ r, (2 * x r ^ 2 - 2 * u r * x r ^ 2)
      = 2 * ∑ r, x r ^ 2 - 2 * ∑ r, u r * x r ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun r _ => by ring
  have hshare : ∑ r, u r * (speakerShiftCost c x r / R)
      = ((c.tracking : ℝ) * ∑ r, u r * x r ^ 2
          + (c.sync : ℝ) * (∑ a, u a * ∑ b, (x a - x b) ^ 2) / R) / R := by
    unfold speakerShiftCost
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  -- The bounds for the pairs and for the speakers, in the two worlds.
  have h1 : ENNReal.ofReal (2 * ((R : ℝ) ^ 2 * varFin x) - 2 * ∑ a, u a * ∑ b, (x a - x b) ^ 2)
      ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
          (w.pairCost plays p.1 p.2 n + w'.pairCost plays p.1 p.2 n) := by
    rw [← hS₁]
    exact (ofReal_sum_le _ _).trans
      (Finset.sum_le_sum fun p _ => w.pairCost_add_ge w' plays x n hshift p.1 p.2)
  have h2 : ENNReal.ofReal (2 * ∑ r, x r ^ 2 - 2 * ∑ r, u r * x r ^ 2)
      ≤ ∑ r, (w.trackingAt plays r n + w'.trackingAt plays r n) := by
    rw [← hS₂]
    exact (ofReal_sum_le _ _).trans
      (Finset.sum_le_sum fun r _ => w.trackingAt_add_ge w' plays x n hsrc htgt hshift r)
  -- The weights and the averages.
  have hcs : (c.sync : ℝ≥0∞) = ENNReal.ofReal (c.sync : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  have hct : (c.tracking : ℝ≥0∞) = ENNReal.ofReal (c.tracking : ℝ) :=
    (ENNReal.ofReal_coe_nnreal).symm
  have hinv2 : ((R : ℝ≥0∞) ^ 2)⁻¹ = ENNReal.ofReal (((R : ℝ) ^ 2)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hRpos.le,
      ENNReal.ofReal_natCast]
  have hinv1 : (R : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((R : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hRpos, ENNReal.ofReal_natCast]
  have hsync : ENNReal.ofReal ((c.sync : ℝ) * (((R : ℝ) ^ 2)⁻¹
        * (2 * ((R : ℝ) ^ 2 * varFin x) - 2 * ∑ a, u a * ∑ b, (x a - x b) ^ 2)))
      ≤ (c.sync : ℝ≥0∞) * (w.syncCost plays n + w'.syncCost plays n) := by
    rw [ENNReal.ofReal_mul c.sync.coe_nonneg, ENNReal.ofReal_mul (by positivity), ← hcs, ← hinv2]
    unfold World.syncCost
    rw [← mul_add, ← Finset.sum_add_distrib]
    exact mul_le_mul_right (mul_le_mul_right h1 _) _
  have htrack : ENNReal.ofReal ((c.tracking : ℝ) * ((R : ℝ)⁻¹
        * (2 * ∑ r, x r ^ 2 - 2 * ∑ r, u r * x r ^ 2)))
      ≤ (c.tracking : ℝ≥0∞) * (w.trackingCost plays n + w'.trackingCost plays n) := by
    rw [ENNReal.ofReal_mul c.tracking.coe_nonneg, ENNReal.ofReal_mul (by positivity), ← hct,
      ← hinv1]
    unfold World.trackingCost
    rw [← mul_add, ← Finset.sum_add_distrib]
    exact mul_le_mul_right (mul_le_mul_right h2 _) _
  have hreal : 2 * shiftCost c x - 2 * ∑ r, u r * (speakerShiftCost c x r / R)
      = (c.sync : ℝ) * (((R : ℝ) ^ 2)⁻¹
          * (2 * ((R : ℝ) ^ 2 * varFin x) - 2 * ∑ a, u a * ∑ b, (x a - x b) ^ 2))
        + (c.tracking : ℝ) * ((R : ℝ)⁻¹
          * (2 * ∑ r, x r ^ 2 - 2 * ∑ r, u r * x r ^ 2)) := by
    rw [hshare]
    unfold shiftCost
    field_simp
    ring
  show ENNReal.ofReal (2 * shiftCost c x - 2 * ∑ r, u r * (speakerShiftCost c x r / R)) ≤ _
  rw [hreal]
  exact ENNReal.ofReal_add_le.trans (add_le_add hsync htrack)

/-! ## What accrues until a time -/

/-- Among instants at `ρ` per second from `o` on, the number before a time
`T` is at least `ρ * (T - o)`, and for `T ≥ 0` at most
`ρ * T + ρ * |o| + 1`. -/
theorem find_of_linear {t : ℕ → ℝ} {o ρ : ℝ} (hρ : 0 < ρ) (ht : ∀ k, t k = o + (k : ℝ) / ρ)
    {T : ℝ} (h : ∃ k, T ≤ t k) :
    ρ * (T - o) ≤ (Nat.find h : ℝ) ∧ (0 ≤ T → (Nat.find h : ℝ) ≤ ρ * T + (ρ * |o| + 1)) := by
  constructor
  · have hspec := Nat.find_spec h
    rw [ht, ← sub_le_iff_le_add', le_div_iff₀ hρ] at hspec
    linarith
  · intro hT
    have habs : -o ≤ |o| := neg_le_abs o
    have h1 : 0 ≤ ρ * (|o| + o) := mul_nonneg hρ.le (by linarith)
    cases hN : Nat.find h with
    | zero =>
      have : 0 ≤ ρ * T := mul_nonneg hρ.le hT
      have h2 : 0 ≤ ρ * |o| := mul_nonneg hρ.le (abs_nonneg o)
      simp only [Nat.cast_zero]
      linarith
    | succ M =>
      have hmin : ¬ T ≤ t M := Nat.find_min h (by omega)
      rw [ht, not_le] at hmin
      have h3 : (M : ℝ) / ρ < T - o := by linarith
      rw [div_lt_iff₀ hρ] at h3
      push_cast
      nlinarith

/-- Instants at `ρ` per second come after every time. -/
theorem exists_of_linear {t : ℕ → ℝ} {o ρ : ℝ} (hρ : 0 < ρ) (ht : ∀ k, t k = o + (k : ℝ) / ρ)
    (T : ℝ) : ∃ k, T ≤ t k := by
  obtain ⟨k, hk⟩ := exists_nat_ge (ρ * (T - o))
  refine ⟨k, ?_⟩
  rw [ht, ← sub_le_iff_le_add', le_div_iff₀ hρ]
  linarith

/-- A cost of the frames accrued until `T`, as a finite sum, when frames are
captured without end. -/
theorem World.accruedFrames_eq_sum (w : World H R) (cost : ℕ → ℝ≥0∞) {T : Time}
    (hex : ∃ n, T ≤ w.source.capture n) :
    w.accruedFrames cost T = ∑ n ∈ Finset.range (Nat.find hex),
      cost n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) := by
  unfold World.accruedFrames
  rw [tsum_eq_sum (s := Finset.range (Nat.find hex))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hlt : w.source.capture n < T := not_le.mp (Nat.find_min hex (Finset.mem_range.mp hn))
    simp [hlt]
  · intro n hn
    have hge : Nat.find hex ≤ n := by simpa using hn
    have hT : T ≤ w.source.capture n :=
      (Nat.find_spec hex).trans (w.source.capture_strictMono.monotone hge)
    simp [not_lt.mpr hT]

/-- Two worlds with the same capture device accrue the same cost of the
frames. -/
theorem World.accruedFrames_congr_source {w w' : World H R} (h : w'.source = w.source)
    (cost : ℕ → ℝ≥0∞) (T : Time) : w'.accruedFrames cost T = w.accruedFrames cost T := by
  unfold World.accruedFrames
  rw [h]

/-- **What the missed samples have paid until a time**, as the number of
missed samples counted at the output samples that left before it. -/
theorem World.weighted_missed_eq (v : World H R) (plays : Fin R → ℕ → Option ℝ) (c : Weights)
    (hR : 0 < R) {T : Time} (hex : ∀ r, ∃ k, T ≤ (v.speaker r).out k) :
    (c.missed : ℝ≥0∞) * v.accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) T
      = ENNReal.ofReal ((c.missed : ℝ) / R
          * ∑ r, (missedBefore (plays r) (Nat.find (hex r)) : ℝ)) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  rw [v.accruedOutputs_eq_sum _ hex]
  have hinner : ∀ r, ∑ k ∈ Finset.range (Nat.find (hex r)), ((missedAt (plays r) k : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal (missedBefore (plays r) (Nat.find (hex r)) : ℝ) := by
    intro r
    rw [ENNReal.ofReal_natCast]
    unfold missedBefore
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun r _ => hinner r,
    ← ENNReal.ofReal_sum_of_nonneg (fun r _ => Nat.cast_nonneg _)]
  have hinv : (R : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((R : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hRpos, ENNReal.ofReal_natCast]
  have hcm : (c.missed : ℝ≥0∞) = ENNReal.ofReal (c.missed : ℝ) :=
    (ENNReal.ofReal_coe_nnreal).symm
  rw [hinv, hcm, ← ENNReal.ofReal_mul (inv_nonneg.mpr hRpos.le),
    ← ENNReal.ofReal_mul c.missed.coe_nonneg]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- **What the frames have cost until a time, in the two worlds.** Let the
same playback run in two worlds with the same source and targets, in the
second of which every speaker `r` plays each frame `2 * x r` later, and let
frames be captured at `ρ` per second. Until any time, the weighted
synchronization and tracking accrued in the two worlds are at least
`2 * shiftCost c x / ρ` for each frame captured, minus
`2 * (speakerShiftCost c x r / R) / ρ` for each of these frames that speaker
`r` never plays. -/
theorem World.weighted_frames_add_ge (w w' : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) (hR : 0 < R) (x : Fin R → ℝ) (hsrc : w'.source = w.source)
    (htgt : w'.target = w.target)
    (hshift : ∀ r n, w'.playTime plays r n = (w.playTime plays r n).map (· + 2 * x r))
    {ρ t₀ : ℝ} (hρ : 0 < ρ) (hcap : ∀ n, w.source.capture n = t₀ + (n : ℝ) / ρ) {T : Time}
    (hex : ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (2 * shiftCost c x / ρ * (Nat.find hex : ℝ)
        - 2 / ρ * ∑ r, speakerShiftCost c x r / R * (neverPlayed (plays r) (Nat.find hex) : ℝ))
      ≤ (c.sync : ℝ≥0∞) * w.accruedFrames (w.syncCost plays) T
        + (c.tracking : ℝ≥0∞) * w.accruedFrames (w.trackingCost plays) T
        + ((c.sync : ℝ≥0∞) * w'.accruedFrames (w'.syncCost plays) T
          + (c.tracking : ℝ≥0∞) * w'.accruedFrames (w'.trackingCost plays) T) := by
  -- The cost of each frame, in real numbers.
  let g : ℕ → ℝ := fun n => 2 * shiftCost c x
    - 2 * ∑ r, (unplayedAt (plays r) n : ℝ) * (speakerShiftCost c x r / R)
  have hdur : ∀ n, w.source.capture (n + 1) - w.source.capture n = 1 / ρ := by
    intro n
    rw [hcap, hcap]
    push_cast
    ring
  have hsum : 2 * shiftCost c x / ρ * (Nat.find hex : ℝ)
        - 2 / ρ * ∑ r, speakerShiftCost c x r / R * (neverPlayed (plays r) (Nat.find hex) : ℝ)
      = ∑ n ∈ Finset.range (Nat.find hex), g n * (1 / ρ) := by
    have h1 : ∑ n ∈ Finset.range (Nat.find hex),
          ∑ r, (unplayedAt (plays r) n : ℝ) * (speakerShiftCost c x r / R)
        = ∑ r, speakerShiftCost c x r / R * (neverPlayed (plays r) (Nat.find hex) : ℝ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [neverPlayed_eq_sum, Nat.cast_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [← Finset.sum_mul]
    show _ = (∑ n ∈ Finset.range (Nat.find hex), (2 * shiftCost c x
      - 2 * ∑ r, (unplayedAt (plays r) n : ℝ) * (speakerShiftCost c x r / R))) * (1 / ρ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, h1]
    field_simp
  rw [hsum]
  -- Frame by frame.
  have hframe : ∀ n, ENNReal.ofReal (g n)
      ≤ (c.sync : ℝ≥0∞) * w.syncCost plays n + (c.tracking : ℝ≥0∞) * w.trackingCost plays n
        + ((c.sync : ℝ≥0∞) * w'.syncCost plays n
          + (c.tracking : ℝ≥0∞) * w'.trackingCost plays n) := by
    intro n
    refine (w.frame_add_ge w' plays c hR x n hsrc htgt (fun r => hshift r n)).trans_eq ?_
    ring
  have hacc : w.accruedFrames (fun n => ENNReal.ofReal (g n)) T
      ≤ (c.sync : ℝ≥0∞) * w.accruedFrames (w.syncCost plays) T
        + (c.tracking : ℝ≥0∞) * w.accruedFrames (w.trackingCost plays) T
        + ((c.sync : ℝ≥0∞) * w'.accruedFrames (w'.syncCost plays) T
          + (c.tracking : ℝ≥0∞) * w'.accruedFrames (w'.trackingCost plays) T) := by
    rw [World.accruedFrames_congr_source hsrc, World.accruedFrames_congr_source hsrc,
      w.accruedFrames_weighted, w.accruedFrames_weighted]
    have hone : ∀ A B : ℝ≥0∞, A + B = 1 * A + 1 * B := fun A B => by rw [one_mul, one_mul]
    rw [hone, w.accruedFrames_weighted]
    refine w.accruedFrames_mono (fun n => ?_) T
    rw [one_mul, one_mul]
    exact hframe n
  refine le_trans ?_ hacc
  rw [w.accruedFrames_eq_sum _ hex]
  refine (ofReal_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [hdur n, ENNReal.ofReal_mul' (by positivity)]

/-! ## The two costs -/

/-- **The costs of one playback in two worlds that differ by a shift.** Let
the same playback run in two worlds with the same source and targets, in the
second of which every speaker `r` plays each frame `2 * x r` later. Let
frames be captured and output samples leave at `ρ` per second. Let every
position be at least zero, and let the position advance by at least `s`,
with `0 < s ≤ 1`, in every step of continuous playback. If the weight of
missed samples is large enough, `6 * speakerShiftCost c x r ≤ c.missed * s *
ρ` for every speaker `r`, then the costs in the two worlds add up to at least
twice the cost of the shift `x`. The playback need not play every frame, in
either world. -/
theorem World.cost_add_ge_of_shift (w w' : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) (hR : 0 < R) (x : Fin R → ℝ) (hsrc : w'.source = w.source)
    (htgt : w'.target = w.target)
    (hshift : ∀ r n, w'.playTime plays r n = (w.playTime plays r n).map (· + 2 * x r))
    {ρ t₀ : ℝ} (hρ : 0 < ρ) (hcap : ∀ n, w.source.capture n = t₀ + (n : ℝ) / ρ)
    (o o' : Fin R → ℝ) (hout : ∀ r k, (w.speaker r).out k = o r + (k : ℝ) / ρ)
    (hout' : ∀ r k, (w'.speaker r).out k = o' r + (k : ℝ) / ρ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hpos : ∀ r k y, plays r k = some y → 0 ≤ y)
    (hslow : ∀ r k y z, plays r k = some y → plays r (k + 1) = some z → y < z → z < y + 2 →
      y + s ≤ z)
    (hthr : ∀ r, 6 * speakerShiftCost c x r ≤ (c.missed : ℝ) * s * ρ) :
    ENNReal.ofReal (2 * shiftCost c x) ≤ w.cost plays c + w'.cost plays c := by
  classical
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hsc0 : 0 ≤ shiftCost c x := shiftCost_nonneg c x
  -- Frames and output samples come without end.
  have hcapex : ∀ T : Time, ∃ n, T ≤ w.source.capture n := fun T =>
    exists_of_linear hρ hcap T
  have houtex : ∀ (T : Time) (r : Fin R), ∃ k, T ≤ (w.speaker r).out k := fun T r =>
    exists_of_linear hρ (hout r) T
  have houtex' : ∀ (T : Time) (r : Fin R), ∃ k, T ≤ (w'.speaker r).out k := fun T r =>
    exists_of_linear hρ (hout' r) T
  let F : ℝ → ℕ := fun T => Nat.find (hcapex T)
  let K₁ : Fin R → ℝ → ℕ := fun r T => Nat.find (houtex T r)
  let K₂ : Fin R → ℝ → ℕ := fun r T => Nat.find (houtex' T r)
  -- Their numbers before a time `T` are within a constant of `ρ * T`.
  let b : ℝ := |t₀| + ∑ r, (|o r| + |o' r|)
  let a : ℝ := ρ * b + 1
  have hsum0 : 0 ≤ ∑ r, (|o r| + |o' r|) :=
    Finset.sum_nonneg fun r _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb0 : 0 ≤ b := add_nonneg (abs_nonneg _) hsum0
  have ha : 0 ≤ a := add_nonneg (mul_nonneg hρ.le hb0) zero_le_one
  have ht₀b : |t₀| ≤ b := le_add_of_nonneg_right hsum0
  have hob : ∀ r, |o r| ≤ b ∧ |o' r| ≤ b := fun r => by
    have h1 : |o r| + |o' r| ≤ ∑ r, (|o r| + |o' r|) :=
      Finset.single_le_sum (f := fun r => |o r| + |o' r|)
        (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ r)
    have h2 := abs_nonneg (o r)
    have h3 := abs_nonneg (o' r)
    have h4 := abs_nonneg t₀
    constructor <;> show _ ≤ |t₀| + ∑ r, (|o r| + |o' r|) <;> linarith
  have hFup : ∀ T, 0 ≤ T → (F T : ℝ) ≤ ρ * T + a := fun T hT => by
    have h := (find_of_linear hρ hcap (hcapex T)).2 hT
    have h1 : ρ * |t₀| ≤ ρ * b := mul_le_mul_of_nonneg_left ht₀b hρ.le
    show (Nat.find (hcapex T) : ℝ) ≤ ρ * T + (ρ * b + 1)
    linarith
  have hFlow : ∀ T, ρ * T - a ≤ F T := fun T => by
    have h := (find_of_linear hρ hcap (hcapex T)).1
    have h1 : ρ * t₀ ≤ ρ * b := mul_le_mul_of_nonneg_left ((le_abs_self t₀).trans ht₀b) hρ.le
    show ρ * T - (ρ * b + 1) ≤ (Nat.find (hcapex T) : ℝ)
    linarith
  have hK₁ : ∀ r T, 0 ≤ T → ρ * T - a ≤ K₁ r T := fun r T _ => by
    have h := (find_of_linear hρ (hout r) (houtex T r)).1
    have h1 : ρ * o r ≤ ρ * b :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hob r).1) hρ.le
    show ρ * T - (ρ * b + 1) ≤ (Nat.find (houtex T r) : ℝ)
    linarith
  have hK₂ : ∀ r T, 0 ≤ T → ρ * T - a ≤ K₂ r T := fun r T _ => by
    have h := (find_of_linear hρ (hout' r) (houtex' T r)).1
    have h1 : ρ * o' r ≤ ρ * b :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hob r).2) hρ.le
    show ρ * T - (ρ * b + 1) ≤ (Nat.find (houtex' T r) : ℝ)
    linarith
  -- What the weighted sum of the six objectives has accrued by `T`.
  let I : World H R → Time → ℝ≥0∞ := fun v T =>
    c.sync * v.accruedFrames (v.syncCost plays) T
      + c.latency * v.accruedFrames (v.latencyCost plays) T
      + c.tracking * v.accruedFrames (v.trackingCost plays) T
      + c.roughness * v.accruedOutputs (v.roughnessCost plays) T
      + c.missed * v.accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) T
      + c.discontinuities * v.accruedOutputs (fun r k => (discontinuityAt (plays r) k : ℝ≥0∞)) T
  have hthree : ∀ a b c d e f : ℝ≥0∞, a + c + e ≤ a + b + c + d + e + f := by
    intro a b c d e f
    calc a + c + e ≤ (a + b) + c + (d + e) :=
          add_le_add (add_le_add le_self_add le_rfl) le_add_self
      _ = a + b + c + d + e := by ring
      _ ≤ a + b + c + d + e + f := le_self_add
  have hI : ∀ (v : World H R) (T : Time),
      c.sync * v.accruedFrames (v.syncCost plays) T
        + c.tracking * v.accruedFrames (v.trackingCost plays) T
        + c.missed * v.accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) T
        ≤ I v T := fun v T => hthree _ _ _ _ _ _
  -- The frames cost, and the missed samples pay.
  have hacc : ∀ T : Time, ENNReal.ofReal
      (2 * shiftCost c x / ρ * (F T : ℝ)
        - 2 / ρ * ∑ r, speakerShiftCost c x r / R * (neverPlayed (plays r) (F T) : ℝ)
        + ((c.missed : ℝ) / R * ∑ r, (missedBefore (plays r) (K₁ r T) : ℝ)
          + (c.missed : ℝ) / R * ∑ r, (missedBefore (plays r) (K₂ r T) : ℝ)))
      ≤ I w T + I w' T := by
    intro T
    have h1 := w.weighted_frames_add_ge w' plays c hR x hsrc htgt hshift hρ hcap (hcapex T)
    have h2 := w.weighted_missed_eq plays c hR (houtex T)
    have h3 := w'.weighted_missed_eq plays c hR (houtex' T)
    refine ENNReal.ofReal_add_le.trans ?_
    refine (add_le_add h1 (ENNReal.ofReal_add_le.trans (add_le_add h2.ge h3.ge))).trans ?_
    refine le_trans (le_of_eq ?_) (add_le_add (hI w T) (hI w' T))
    ring
  -- At some arbitrarily late times the payments have covered the frames.
  have hpaid : ∀ ε : ℝ, 0 < ε → ∀ T₀ : ℝ, ∃ T, T₀ ≤ T ∧
      2 / ρ * ∑ r, speakerShiftCost c x r / R * (neverPlayed (plays r) (F T) : ℝ)
        - (c.missed : ℝ) / R * ∑ r, ((missedBefore (plays r) (K₁ r T) : ℝ)
            + missedBefore (plays r) (K₂ r T))
        ≤ ε * T := by
    intro ε hε T₀
    exact exists_time_paid hρ hs0 hs1 ha (div_nonneg c.missed.coe_nonneg hRpos.le)
      (fun r N => neverPlayed (plays r) N) (fun r K => missedBefore (plays r) K)
      (fun r => firstFrames (plays r))
      (fun r N => neverPlayed_le (plays r) N)
      (fun r => fun K K' h => missedBefore_mono (plays r) h)
      (fun r K N hN => neverPlayed_le_of_missed hs0.le hs1 (hpos r) (hslow r) hN)
      (fun r => speakerShiftCost c x r / R)
      (fun r => div_nonneg (speakerShiftCost_nonneg c x r) hRpos.le)
      (fun r => by
        have h := div_le_div_of_nonneg_right (hthr r) hRpos.le
        have e1 : (6 : ℝ) * (speakerShiftCost c x r / R) = 6 * speakerShiftCost c x r / R := by
          ring
        have e2 : (c.missed : ℝ) / R * s * ρ = (c.missed : ℝ) * s * ρ / R := by ring
        rw [e1, e2]
        exact h)
      F K₁ K₂ hFup hK₁ hK₂ hε T₀
  have hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ T : Time in atTop,
      ENNReal.ofReal (2 * shiftCost c x - ε) ≤ (I w T + I w' T) / ENNReal.ofReal T := by
    intro ε hε
    rw [Filter.frequently_atTop]
    intro T₀
    obtain ⟨T, hT, hle⟩ := hpaid (ε / 2) (by positivity)
      (max T₀ (max 1 (4 * shiftCost c x * a / (ρ * ε))))
    have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
    have hT1 : 1 ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have hTa : 4 * shiftCost c x * a / (ρ * ε) ≤ T :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hTpos : 0 < T := by linarith
    refine ⟨T, hT₀, ?_⟩
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hTpos).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul' hTpos.le]
    refine (ENNReal.ofReal_le_ofReal ?_).trans (hacc T)
    have hFl := hFlow T
    have h4 : 2 * shiftCost c x * a / ρ ≤ ε / 2 * T := by
      rw [div_le_iff₀ (by positivity)] at hTa
      rw [div_le_iff₀ hρ]
      nlinarith
    have h5 : 2 * shiftCost c x * T - 2 * shiftCost c x * a / ρ
        ≤ 2 * shiftCost c x / ρ * (F T : ℝ) := by
      have h7 : 2 * shiftCost c x / ρ * (ρ * T - a) ≤ 2 * shiftCost c x / ρ * (F T : ℝ) :=
        mul_le_mul_of_nonneg_left hFl (by positivity)
      have e : 2 * shiftCost c x / ρ * (ρ * T - a)
          = 2 * shiftCost c x * T - 2 * shiftCost c x * a / ρ := by
        field_simp
      linarith
    have h6 : (c.missed : ℝ) / R * ∑ r, ((missedBefore (plays r) (K₁ r T) : ℝ)
          + missedBefore (plays r) (K₂ r T))
        = (c.missed : ℝ) / R * ∑ r, (missedBefore (plays r) (K₁ r T) : ℝ)
          + (c.missed : ℝ) / R * ∑ r, (missedBefore (plays r) (K₂ r T) : ℝ) := by
      rw [Finset.sum_add_distrib, mul_add]
    linarith
  -- So the long-run average of the two accrued costs is at least the bound.
  have hlim : ∀ ε : ℝ, 0 < ε →
      ENNReal.ofReal (2 * shiftCost c x - ε) ≤ w.cost plays c + w'.cost plays c := by
    intro ε hε
    refine (Filter.le_limsup_of_frequently_le (hfreq ε hε)).trans ?_
    have h3 : (fun T : Time => (I w T + I w' T) / ENNReal.ofReal T)
        = fun T => I w T / ENNReal.ofReal T + I w' T / ENNReal.ofReal T := by
      funext T
      exact ENNReal.add_div
    rw [h3]
    exact ennreal_limsup_add_le (fun T => I w T / ENNReal.ofReal T)
      (fun T => I w' T / ENNReal.ofReal T)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
  calc ENNReal.ofReal (2 * shiftCost c x)
      = ENNReal.ofReal ((2 * shiftCost c x - ε) + ε) := by rw [sub_add_cancel]
    _ ≤ ENNReal.ofReal (2 * shiftCost c x - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ ≤ w.cost plays c + w'.cost plays c + ε := by
        rw [ENNReal.ofReal_coe_nnreal]
        exact add_le_add (hlim ε hεpos) le_rfl

/-! ## A playback that stops -/

/-- A cost that accrues at least `B` per second, up to a constant, has a
long-run average of at least `B`. -/
theorem le_longRun_of_linear {A : Time → ℝ≥0∞} {B C : ℝ}
    (h : ∀ T, ENNReal.ofReal (B * T - C) ≤ A T) : ENNReal.ofReal B ≤ longRun A := by
  unfold longRun
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
  have hev : ∀ᶠ T : Time in atTop, ENNReal.ofReal (B - ε) ≤ A T / ENNReal.ofReal T := by
    filter_upwards [eventually_ge_atTop (max 1 (C / ε))] with T hT
    have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
    have hTC : C / ε ≤ T := (le_max_right _ _).trans hT
    have hTpos : 0 < T := by linarith
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hTpos).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul' hTpos.le]
    refine (ENNReal.ofReal_le_ofReal ?_).trans (h T)
    rw [div_le_iff₀ hεpos] at hTC
    nlinarith
  have hle := Filter.le_limsup_of_frequently_le hev.frequently
  calc ENNReal.ofReal B = ENNReal.ofReal ((B - ε) + ε) := by rw [sub_add_cancel]
    _ ≤ ENNReal.ofReal (B - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ ≤ limsup (fun T => A T / ENNReal.ofReal T) atTop + ε := by
        rw [ENNReal.ofReal_coe_nnreal]
        exact add_le_add hle le_rfl

/-- From the output sample on from which a playback plays nothing, every
output sample counts one missed sample. -/
theorem missedBefore_ge_of_none {plays : ℕ → Option ℝ} {k₀ : ℕ}
    (h : ∀ k, k₀ ≤ k → plays k = none) : ∀ K, K - k₀ ≤ missedBefore plays K
  | 0 => by simp
  | K + 1 => by
      have ih := missedBefore_ge_of_none h K
      rw [missedBefore_succ]
      by_cases hK : k₀ ≤ K
      · rw [missedAt_of_none (h K hK)]
        omega
      · omega

/-- **A playback that stops costs the weight of missed samples at every
output sample.** If every speaker plays nothing from some output sample on,
and output samples leave at `ρ` per second, the cost is at least
`c.missed * ρ`. -/
theorem World.cost_ge_of_eventually_none (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) (hR : 0 < R) {ρ : ℝ} (hρ : 0 < ρ) (o : Fin R → ℝ)
    (hout : ∀ r k, (w.speaker r).out k = o r + (k : ℝ) / ρ)
    (hnone : ∀ r, ∃ k₀, ∀ k, k₀ ≤ k → plays r k = none) :
    ENNReal.ofReal ((c.missed : ℝ) * ρ) ≤ w.cost plays c := by
  classical
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  choose k₀ hk₀ using hnone
  have houtex : ∀ (T : Time) (r : Fin R), ∃ k, T ≤ (w.speaker r).out k := fun T r =>
    exists_of_linear hρ (hout r) T
  refine le_longRun_of_linear (C := (c.missed : ℝ) / R * ∑ r, (ρ * o r + (k₀ r : ℝ)))
    fun T => ?_
  refine le_trans ?_ (le_add_self.trans le_self_add)
  rw [w.weighted_missed_eq plays c hR (houtex T)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hterm : ∀ r, ρ * (T - o r) - (k₀ r : ℝ)
      ≤ (missedBefore (plays r) (Nat.find (houtex T r)) : ℝ) := by
    intro r
    have h1 := (find_of_linear hρ (hout r) (houtex T r)).1
    have h2 := missedBefore_ge_of_none (hk₀ r) (Nat.find (houtex T r))
    have h3 : (Nat.find (houtex T r) : ℝ) ≤ missedBefore (plays r) (Nat.find (houtex T r))
        + (k₀ r : ℝ) := by
      have : Nat.find (houtex T r) ≤ missedBefore (plays r) (Nat.find (houtex T r)) + k₀ r := by
        omega
      exact_mod_cast this
    linarith
  have hsum : ∑ r, (ρ * (T - o r) - (k₀ r : ℝ))
      = (R : ℝ) * (ρ * T) - ∑ r, (ρ * o r + (k₀ r : ℝ)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hle := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) fun r _ => hterm r)
    (show (0 : ℝ) ≤ (c.missed : ℝ) / R from div_nonneg c.missed.coe_nonneg hRpos.le)
  rw [hsum] at hle
  have e : (c.missed : ℝ) / R * ((R : ℝ) * (ρ * T) - ∑ r, (ρ * o r + (k₀ r : ℝ)))
      = (c.missed : ℝ) * ρ * T - (c.missed : ℝ) / R * ∑ r, (ρ * o r + (k₀ r : ℝ)) := by
    field_simp
  linarith

/-! ## A solution in the two worlds -/

/-- When frames are captured at `ρ` per second, the sound at position `x`
was captured `x / ρ` after frame zero. -/
theorem World.captured_of_linear (w : World H R) {ρ t₀ : ℝ}
    (hcap : ∀ n, w.source.capture n = t₀ + (n : ℝ) / ρ) (x : ℝ) :
    w.captured x = t₀ + x / ρ := by
  unfold World.captured
  rw [hcap, hcap]
  push_cast
  ring

/-- **A bound on the speed bounds the advance of the position.** When frames
are captured and output samples leave at the same rate, a step of continuous
playback at a speed within `u` of one advances the position by at least
`1 - u`. -/
theorem World.advance_of_speed (w : World H R) (plays : Fin R → ℕ → Option ℝ) {ρ t₀ : ℝ}
    (hρ : 0 < ρ) (hcap : ∀ n, w.source.capture n = t₀ + (n : ℝ) / ρ) (o : Fin R → ℝ)
    (hout : ∀ r k, (w.speaker r).out k = o r + (k : ℝ) / ρ) {u : ℝ}
    (hspeed : ∀ r k v, w.speed plays r k = some v → |v - 1| ≤ u)
    (r : Fin R) (k : ℕ) (y z : ℝ) (hy : plays r k = some y) (hz : plays r (k + 1) = some z)
    (h1 : y < z) (h2 : z < y + 2) : y + (1 - u) ≤ z := by
  classical
  have hsp : w.speed plays r k = some (z - y) := by
    unfold World.speed
    simp only [hy, hz]
    rw [ite_eq_left ⟨h1, h2⟩, w.captured_of_linear hcap, w.captured_of_linear hcap, hout, hout]
    congr 1
    push_cast
    field_simp
    ring
  have h3 := (abs_le.mp (hspeed r k _ hsp)).1
  linarith

variable [DecidableEq H] {Msg : Type}

/-- A solution plays the source only at positions that are at least zero. -/
theorem Solution.nonneg_of_plays (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {r : Fin R} {k : ℕ} {x : ℝ} (h : σ.plays w lookahead r k = some x) : 0 ≤ x := by
  obtain ⟨b, n, hkb, hnb, hearly, hact⟩ := exists_asked_of_plays_some σ w lookahead h
  have hp := σ.plays_of_asked_step w lookahead hnb hearly hkb
  rw [h, hact] at hp
  simp only [playable] at hp
  split_ifs at hp with hc
  exact hc.1

/-- **A run that stops decides nothing more.** If no event of the run comes
after the true time `T`, a speaker plays nothing at the output samples of the
blocks that its device requests after `T`. -/
theorem Solution.plays_eq_none_of_stalled (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) {T : Time} (hT : ∀ n, σ.eventTime w lookahead n ≤ T) (r : Fin R)
    {b₀ : ℕ} (hb₀ : T < (w.speaker r).asked b₀) {k : ℕ} (hk : (w.speaker r).first b₀ ≤ k) :
    σ.plays w lookahead r k = none := by
  by_contra hne
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨b, n, hkb, -, hearly, -⟩ := exists_asked_of_plays_some σ w lookahead hx
  have hev : σ.eventTime w lookahead n = (w.speaker r).asked b := by
    unfold Solution.eventTime
    rw [hearly]
    rfl
  have hlt : (w.speaker r).asked b < (w.speaker r).asked b₀ :=
    lt_of_le_of_lt (hev ▸ hT n) hb₀
  have hbb : b < b₀ := (w.speaker r).asked_strictMono.lt_iff_lt.mp hlt
  have hfirst : (w.speaker r).first (b + 1) ≤ (w.speaker r).first b₀ :=
    (w.speaker r).first_strictMono.monotone hbb
  unfold PlaybackDevice.block at hkb
  rw [List.mem_range'_1] at hkb
  have := (w.speaker r).first_strictMono (Nat.lt_succ_self b)
  omega

/-- The cost of a shift is at most the mean of what it costs through each
speaker. -/
theorem mul_shiftCost_le_sum (c : Weights) (hR : 0 < R) (x : Fin R → ℝ) :
    (R : ℝ) * shiftCost c x ≤ ∑ r, speakerShiftCost c x r := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hvar0 : 0 ≤ varFin x :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hRpos.le
  have hpairs := two_mul_sum_pairs (fun a b => (x a - x b) ^ 2) (fun a b => by ring)
    (fun a => by ring)
  rw [sum_pairs_sq_eq_var hR x] at hpairs
  have hsum : ∑ r, speakerShiftCost c x r
      = (c.tracking : ℝ) * ∑ r, x r ^ 2 + (c.sync : ℝ) * ((∑ a, ∑ b, (x a - x b) ^ 2) / R) := by
    unfold speakerShiftCost
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_div]
  rw [hsum, ← hpairs]
  unfold shiftCost
  have hs : (0 : ℝ) ≤ c.sync := c.sync.coe_nonneg
  have e : (c.sync : ℝ) * (2 * ((R : ℝ) ^ 2 * varFin x) / R)
      = 2 * ((c.sync : ℝ) * (R * varFin x)) := by
    field_simp
  have e2 : (R : ℝ) * ((c.sync : ℝ) * varFin x + (c.tracking : ℝ) * ((∑ r, x r ^ 2) / R))
      = (c.sync : ℝ) * (R * varFin x) + (c.tracking : ℝ) * ∑ r, x r ^ 2 := by
    field_simp
  rw [e, e2]
  have h0 : 0 ≤ (c.sync : ℝ) * (R * varFin x) := by positivity
  linarith

/-- **A star solution within a speed bound pays in one of two worlds that it
cannot tell apart, whatever it plays.** Let frames be captured and output
samples leave at `ρ` per second in the world `w`, and let every playback
device request blocks without end. Let `X` be a shift of the hosts'
timelines along the links to and from the sender, which leaves the sender's
timeline in place. Let `σ` be a star solution whose position in `w`
advances, in every step of continuous playback, by one frame per output
sample within `u < 1`. If the weight of missed samples is large enough,
`6 * speakerShiftCost c (X / 2) r ≤ c.missed * (1 - u) * ρ` for every speaker
`r`, then the costs of `σ` in `w` and in the shifted world add up to at
least twice `shiftCost c` of half the speakers' shifts.

Nothing is assumed about which frames `σ` plays, or about its run: if the
run stops in one of the worlds, the speakers play nothing from then on, and
the missed samples alone cost more than the bound. -/
theorem Solution.cost_shiftStar_add_ge_of_step (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (c : Weights) (hstar : σ.IsStar w.sender) (X : H → ℝ)
    (hXs : X w.sender = 0)
    (hstar₁ : ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + X i < a + X j)
    (hR : 0 < R) {ρ t₀ : ℝ} (hρ : 0 < ρ)
    (hcap : ∀ n, w.source.capture n = t₀ + (n : ℝ) / ρ) (o : Fin R → ℝ)
    (hout : ∀ r k, (w.speaker r).out k = o r + (k : ℝ) / ρ)
    (hasked : ∀ r (T : Time), ∃ b, T < (w.speaker r).asked b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hstep : σ.WithinStep w lookahead u)
    (hthr : ∀ r, 6 * speakerShiftCost c (fun r => X (w.host r) / 2) r
      ≤ (c.missed : ℝ) * (1 - u) * ρ) :
    ENNReal.ofReal (2 * shiftCost c fun r => X (w.host r) / 2)
      ≤ σ.cost w lookahead c + σ.cost (shiftStarKeepPeers w X hstar₁) lookahead c := by
  classical
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  set w' := shiftStarKeepPeers w X hstar₁ with hw'
  have hout' : ∀ r k, (w'.speaker r).out k = (o r + X (w.host r)) + (k : ℝ) / ρ := by
    intro r k
    show (w.speaker r).out k + X (w.host r) = _
    rw [hout]
    ring
  have hasked' : ∀ r (T : Time), ∃ b, T < (w'.speaker r).asked b := by
    intro r T
    obtain ⟨b, hb⟩ := hasked r (T - X (w.host r))
    refine ⟨b, ?_⟩
    show T < (w.speaker r).asked b + X (w.host r)
    linarith
  -- The bound is less than what a playback that stops costs.
  have hcm : (0 : ℝ) ≤ c.missed := c.missed.coe_nonneg
  have hbound : 2 * shiftCost c (fun r => X (w.host r) / 2) ≤ (c.missed : ℝ) * ρ := by
    have h1 := mul_shiftCost_le_sum c hR fun r => X (w.host r) / 2
    have h2 : ∑ r, speakerShiftCost c (fun r => X (w.host r) / 2) r
        ≤ ∑ _r : Fin R, (c.missed : ℝ) * (1 - u) * ρ / 6 :=
      Finset.sum_le_sum fun r _ => by linarith [hthr r]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : shiftCost c (fun r => X (w.host r) / 2) ≤ (c.missed : ℝ) * (1 - u) * ρ / 6 :=
      le_of_mul_le_mul_left (h1.trans h2) hRpos
    have h4 : (c.missed : ℝ) * (1 - u) * ρ ≤ (c.missed : ℝ) * ρ := by
      have : (c.missed : ℝ) * (1 - u) ≤ (c.missed : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hcm
      nlinarith
    have h5 : 0 ≤ (c.missed : ℝ) * ρ := mul_nonneg hcm hρ.le
    linarith
  have hstall : ∀ (v : World H R) (ov : Fin R → ℝ),
      (∀ r k, (v.speaker r).out k = ov r + (k : ℝ) / ρ) →
      (∀ r (T : Time), ∃ b, T < (v.speaker r).asked b) →
      (¬ ∀ T : Time, ∃ n, T < σ.eventTime v lookahead n) →
      ENNReal.ofReal (2 * shiftCost c fun r => X (w.host r) / 2) ≤ σ.cost v lookahead c := by
    intro v ov hov hav hno
    push Not at hno
    obtain ⟨T, hT⟩ := hno
    refine (ENNReal.ofReal_le_ofReal hbound).trans ?_
    refine v.cost_ge_of_eventually_none (σ.plays v lookahead) c hR hρ ov hov fun r => ?_
    obtain ⟨b₀, hb₀⟩ := hav r T
    exact ⟨(v.speaker r).first b₀, fun k hk => σ.plays_eq_none_of_stalled v lookahead hT r hb₀ hk⟩
  by_cases hp : ∀ T : Time, ∃ n, T < σ.eventTime w lookahead n
  · by_cases hp' : ∀ T : Time, ∃ n, T < σ.eventTime w' lookahead n
    · have hplays : σ.plays w' lookahead = σ.plays w lookahead :=
        σ.plays_shiftStarKeepPeers w lookahead hstar X hXs hstar₁ hp hp'
      have hshift : ∀ r n, w'.playTime (σ.plays w lookahead) r n
          = (w.playTime (σ.plays w lookahead) r n).map (· + 2 * (X (w.host r) / 2)) := by
        intro r n
        rw [hw', playTime_shiftStarKeepPeers]
        congr 1
        funext t
        ring
      have hmain := w.cost_add_ge_of_shift w' (σ.plays w lookahead) c hR
        (fun r => X (w.host r) / 2) rfl rfl hshift hρ hcap o (fun r => o r + X (w.host r)) hout
        hout' (s := 1 - u) (by linarith) (by linarith)
        (fun r k y hy => σ.nonneg_of_plays w lookahead hy)
        (fun r k y z hy hz h1 h2 => by
          have h3 := (abs_le.mp (hstep r k y z hy hz h1 h2)).1
          linarith) hthr
      unfold Solution.cost
      rw [hplays]
      exact hmain
    · exact (hstall w' (fun r => o r + X (w.host r)) hout' hasked' hp').trans le_add_self
  · exact (hstall w o hout hasked hp).trans le_self_add

end Unisono.Spec
