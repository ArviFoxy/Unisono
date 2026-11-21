/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Objectives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Checks of the definitions

Statements that say, about small cases, what the definitions of the
objectives say in words. They are not results about the problem; they are
there so that a definition that does not mean what its description says
fails here.

* The speed is one less how fast the latency changes (`speed_eq`).
* Missed samples: an output sample that plays anything but the source
  counts one (`missedAt_none`); playback that goes on counts nothing
  (`missedAt_continues`); a jump forward over `J` frames counts `J`
  (`missedAt_skip`); playing `J` frames again counts `J`
  (`missedAt_repeat`); after `g` output samples that played something
  else, which count `g`, content that goes on as if they had played counts
  nothing more (`missedAt_after_gap`), and content that resumes where it
  stopped counts nothing more either (`missedAt_resume`).
* The synchronisation cost of a frame, when every speaker plays it, is the
  variance of the times at which they play it (`sum_pairs_eq`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal

variable {H : Type} {R : ℕ}

/-! ## Speed -/

/-- **The speed is one less how fast the latency changes.** Over a step of
the playback that goes on, the speed is one less the change of the latency,
the time an output sample leaves less the time its content was captured,
divided by the time between the two output samples. -/
theorem speed_eq (w : World H R) (plays : Fin R → ℕ → Option ℝ) (r : Fin R) (k : ℕ)
    {x y : ℝ} (hx : plays r k = some x) (hy : plays r (k + 1) = some y) (hxy : x < y)
    (hyx : y < x + 2) :
    w.speed plays r k = some (1 - (((w.speaker r).out (k + 1) - w.captured y)
      - ((w.speaker r).out k - w.captured x))
      / ((w.speaker r).out (k + 1) - (w.speaker r).out k)) := by
  have hpos : (w.speaker r).out k < (w.speaker r).out (k + 1) :=
    (w.speaker r).out_strictMono (Nat.lt_succ_self k)
  have hne : (w.speaker r).out (k + 1) - (w.speaker r).out k ≠ 0 := by linarith
  simp only [World.speed, hx, hy, hxy, hyx, and_self, ite_true, Option.some.injEq]
  field_simp
  ring

/-! ## Missed samples -/

/-- An output sample that plays anything but the source counts one missed
sample. -/
theorem missedAt_none (plays : ℕ → Option ℝ) {k : ℕ} (h : plays k = none) :
    missedAt plays k = 1 := by
  simp [missedAt, h]

/-- The missed samples counted at output sample `k`, which plays content `y`,
when the last output sample before it that played the source is `j`, which
played content `x`. -/
theorem missedAt_after (plays : ℕ → Option ℝ) {j k : ℕ} {x y : ℝ} (hjk : j < k)
    (hj : plays j = some x) (hk : plays k = some y)
    (hnone : ∀ i, j < i → i < k → plays i = none) :
    missedAt plays k = (⌊y - x - 1⌋ - ((k - 1 - j : ℕ) : ℤ)).toNat + ⌊1 - (y - x)⌋.toNat := by
  classical
  have hlast : Nat.findGreatest (fun i => (plays i).isSome = true) (k - 1) = j := by
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, fun _ => by simp [hj], fun i hji hik => ?_⟩
    simp [hnone i hji (by omega)]
  have hsome : ∃ i < k, (plays i).isSome = true := ⟨j, hjk, by simp [hj]⟩
  simp only [missedAt, hk, hsome, ite_true]
  rw [hlast, hj]

/-- Playback that goes on from one output sample to the next counts no missed
sample. -/
theorem missedAt_continues (plays : ℕ → Option ℝ) {k : ℕ} {x y : ℝ} (hx : plays k = some x)
    (hy : plays (k + 1) = some y) (hxy : x < y) (hyx : y < x + 2) :
    missedAt plays (k + 1) = 0 := by
  rw [missedAt_after plays (Nat.lt_succ_self k) hx hy (fun i h1 h2 => by omega)]
  have h1 : ⌊y - x - 1⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    linarith
  have h2 : ⌊1 - (y - x)⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    linarith
  rw [show k + 1 - 1 - k = 0 by omega, Nat.cast_zero, sub_zero]
  rw [Int.toNat_eq_zero.mpr h1, Int.toNat_eq_zero.mpr h2]

/-- A jump forward over `J` frames counts `J` missed samples. -/
theorem missedAt_skip (plays : ℕ → Option ℝ) {k : ℕ} {x : ℝ} (J : ℕ) (hx : plays k = some x)
    (hy : plays (k + 1) = some (x + 1 + J)) :
    missedAt plays (k + 1) = J := by
  rw [missedAt_after plays (Nat.lt_succ_self k) hx hy (fun i h1 h2 => by omega)]
  have h1 : ⌊x + 1 + (J : ℝ) - x - 1⌋ = J := by
    rw [show x + 1 + (J : ℝ) - x - 1 = (J : ℤ) by push_cast; ring, Int.floor_intCast]
  have h2 : ⌊1 - (x + 1 + (J : ℝ) - x)⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith
  rw [show k + 1 - 1 - k = 0 by omega, Nat.cast_zero, sub_zero]
  rw [h1, Int.toNat_eq_zero.mpr h2]
  simp

/-- Playing `J` frames again counts `J` missed samples. -/
theorem missedAt_repeat (plays : ℕ → Option ℝ) {k : ℕ} {x : ℝ} (J : ℕ) (hx : plays k = some x)
    (hy : plays (k + 1) = some (x + 1 - J)) :
    missedAt plays (k + 1) = J := by
  rw [missedAt_after plays (Nat.lt_succ_self k) hx hy (fun i h1 h2 => by omega)]
  have h1 : ⌊x + 1 - (J : ℝ) - x - 1⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith
  have h2 : ⌊1 - (x + 1 - (J : ℝ) - x)⌋ = J := by
    rw [show 1 - (x + 1 - (J : ℝ) - x) = (J : ℤ) by push_cast; ring, Int.floor_intCast]
  rw [show k + 1 - 1 - k = 0 by omega, Nat.cast_zero, sub_zero]
  have h1' : (⌊x + 1 - (J : ℝ) - x - 1⌋).toNat = 0 := Int.toNat_eq_zero.mpr h1
  rw [h1', h2]
  simp

/-- After `g` output samples that played something else, which count `g`
missed samples, content that goes on as if they had played the source
counts no more. -/
theorem missedAt_after_gap (plays : ℕ → Option ℝ) {k g : ℕ} {x : ℝ} (hx : plays k = some x)
    (hgap : ∀ i, k < i → i < k + 1 + g → plays i = none)
    (hy : plays (k + 1 + g) = some (x + 1 + g)) :
    missedAt plays (k + 1 + g) = 0 := by
  rw [missedAt_after plays (by omega) hx hy hgap]
  have h1 : ⌊x + 1 + (g : ℝ) - x - 1⌋ = g := by
    rw [show x + 1 + (g : ℝ) - x - 1 = (g : ℤ) by push_cast; ring, Int.floor_intCast]
  have h2 : ⌊1 - (x + 1 + (g : ℝ) - x)⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    have : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    linarith
  rw [h1, Int.toNat_eq_zero.mpr h2, show k + 1 + g - 1 - k = g by omega]
  simp

/-- After `g` output samples that played something else, which count `g`
missed samples, content that resumes where it stopped counts no more. -/
theorem missedAt_resume (plays : ℕ → Option ℝ) {k g : ℕ} {x : ℝ} (hx : plays k = some x)
    (hgap : ∀ i, k < i → i < k + 1 + g → plays i = none)
    (hy : plays (k + 1 + g) = some (x + 1)) :
    missedAt plays (k + 1 + g) = 0 := by
  rw [missedAt_after plays (by omega) hx hy hgap]
  have h1 : ⌊x + 1 - x - 1⌋ - ((k + 1 + g - 1 - k : ℕ) : ℤ) ≤ 0 := by
    rw [show x + 1 - x - 1 = (0 : ℤ) by push_cast; ring, Int.floor_intCast]
    omega
  have h2 : ⌊1 - (x + 1 - x)⌋ ≤ 0 := by
    rw [show 1 - (x + 1 - x) = (0 : ℤ) by push_cast; ring, Int.floor_intCast]
  rw [Int.toNat_eq_zero.mpr h1, Int.toNat_eq_zero.mpr h2]

/-! ## Synchronisation -/

/-- **The pairs and the variance.** The squares of the differences between the
times `t r` of `R` speakers, over all pairs, add up to `R` times the sum of
the squares of their distances from the mean: divided by `R ^ 2`, the
variance. -/
theorem sum_pairs_eq (t : Fin R → ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (t p.1 - t p.2) ^ 2
      = R * ∑ r, (t r - (∑ r', t r') / R) ^ 2 := by
  -- Every unordered pair of different speakers appears once among the
  -- ordered pairs with the first before the second, and twice among all
  -- ordered pairs; a pair of a speaker with itself adds nothing.
  have hall : ∑ p : Fin R × Fin R, (t p.1 - t p.2) ^ 2
      = 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (t p.1 - t p.2) ^ 2 := by
    have hsplit : ∑ p : Fin R × Fin R, (t p.1 - t p.2) ^ 2
        = ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (t p.1 - t p.2) ^ 2
          + ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2), (t p.1 - t p.2) ^ 2 :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hgt : ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2), (t p.1 - t p.2) ^ 2
        = ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (t p.1 - t p.2) ^ 2 := by
      -- swapping the two speakers of a pair keeps the square
      have hle : ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2),
            (t p.1 - t p.2) ^ 2
          = ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.2 < p.1), (t p.1 - t p.2) ^ 2 := by
        rw [← Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2)) (fun p => p.2 < p.1)]
        have hdiag : ∑ p ∈ (Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2)).filter
              (fun p => ¬ p.2 < p.1), (t p.1 - t p.2) ^ 2 = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp
          have : p.1 = p.2 := le_antisymm hp.2 hp.1
          rw [this, sub_self]
          ring
        rw [hdiag, add_zero, Finset.filter_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨h.le, h⟩
      rw [hle]
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simpa using hp
      · intro p hp
        simpa using hp
      · intro p _
        simp
      · intro p _
        simp
      · intro p _
        simp only [Prod.fst_swap, Prod.snd_swap]
        ring
    rw [hsplit, hgt]
    ring
  -- The sum over all ordered pairs, worked out.
  have hexpand : ∑ p : Fin R × Fin R, (t p.1 - t p.2) ^ 2
      = 2 * (R * ∑ r, t r ^ 2 - (∑ r, t r) ^ 2) := by
    rw [Fintype.sum_prod_type]
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp
  · have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    have hmean : R * ∑ r, (t r - (∑ r', t r') / R) ^ 2 = R * ∑ r, t r ^ 2 - (∑ r, t r) ^ 2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      field_simp
      ring
    rw [hmean]
    linarith [hall, hexpand]

end Unisono.Spec
