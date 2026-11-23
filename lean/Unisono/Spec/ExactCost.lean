/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.StarShift

/-!
# The cost of playback at exact latencies

`Unisono.Spec.ExactLatency` bounds the cost of playback at exact latencies
from above. This file bounds it from below, so that the cost is known
exactly.

Let every output sample of each speaker `r`, from some output sample on,
play the sound captured exactly `L r` seconds before the sample leaves
(`World.PlaysAtLatencies`), in a world whose capture times are linear in the
position and whose output samples leave after every true time.

* From some frame on, some step of every speaker's playback passes each frame
  (`World.PlaysAtLatencies.exists_covers`), and speaker `r` plays the frame
  exactly `L r` after its capture
  (`World.PlaysAtLatencies.exists_playTime`).
* The cost is at least `frameCost c L target` when the target latency is
  constant (`World.frameCost_le_cost_of_exact`).

The file also relates the two costs of one frame: with latencies `t + a r`
and target `t`, the frame cost is the shift cost of `a`
(`frameCost_const_add`), which is the weighted sum that the upper bounds
state (`ofReal_shiftCost`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-! ## The cost of one frame -/

theorem meanFin_const_add (hR : 0 < R) (t : ℝ) (a : Fin R → ℝ) :
    meanFin (fun r => t + a r) = t + meanFin a := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold meanFin
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Adding the same number to every entry does not change the variance. -/
theorem varFin_const_add (hR : 0 < R) (t : ℝ) (a : Fin R → ℝ) :
    varFin (fun r => t + a r) = varFin a := by
  unfold varFin
  rw [meanFin_const_add hR]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **The cost of a frame that every speaker plays late by its own amount.**
When the speakers play a frame with latencies `t + a r` and its target
latency is `t`, the frame's weighted synchronization and tracking cost is the
shift cost of `a`. -/
theorem frameCost_const_add (c : Weights) (hR : 0 < R) (t : ℝ) (a : Fin R → ℝ) :
    frameCost c (fun r => t + a r) t = shiftCost c a := by
  unfold frameCost shiftCost
  rw [varFin_const_add hR, meanFin_const_add hR, modal_sq_split hR a]
  ring

/-- A shift and its opposite cost the same. -/
theorem shiftCost_neg (c : Weights) (x : Fin R → ℝ) :
    shiftCost c (fun r => -x r) = shiftCost c x := by
  have hm : meanFin (fun r => -x r) = -meanFin x := by
    unfold meanFin
    rw [Finset.sum_neg_distrib, neg_div]
  have h1 : ∀ r, (-x r - -meanFin x) ^ 2 = (x r - meanFin x) ^ 2 := fun r => by ring
  have h2 : ∀ r, (-x r) ^ 2 = x r ^ 2 := fun r => by ring
  unfold shiftCost varFin
  rw [hm]
  simp only [h1, h2]

/-- A shift of at most `B` at every speaker costs at most the sum of the
weights of synchronization and of tracking times `B ^ 2`. -/
theorem shiftCost_le (c : Weights) (hR : 0 < R) {x : Fin R → ℝ} {B : ℝ}
    (hx : ∀ r, |x r| ≤ B) : shiftCost c x ≤ ((c.sync : ℝ) + (c.tracking : ℝ)) * B ^ 2 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hsq : (∑ r : Fin R, x r ^ 2) / R ≤ B ^ 2 := by
    rw [div_le_iff₀ hRpos]
    calc ∑ r : Fin R, x r ^ 2 ≤ ∑ _r : Fin R, B ^ 2 := Finset.sum_le_sum fun r _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx r) 2
      _ = B ^ 2 * R := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hvar : varFin x ≤ (∑ r : Fin R, x r ^ 2) / R := by
    rw [modal_sq_split hR x]
    nlinarith [sq_nonneg (meanFin x)]
  have h1 := mul_le_mul_of_nonneg_left (hvar.trans hsq) c.sync.coe_nonneg
  have h2 := mul_le_mul_of_nonneg_left hsq c.tracking.coe_nonneg
  unfold shiftCost
  linarith

/-- The shift cost as the weighted sum of the squared differences of the
pairs of speakers and of the squares. -/
theorem ofReal_shiftCost (c : Weights) (hR : 0 < R) (a : Fin R → ℝ) :
    ENNReal.ofReal (shiftCost c a)
      = (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
              ENNReal.ofReal ((a q.1 - a q.2) ^ 2))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (a r ^ 2)) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hvar0 : 0 ≤ varFin a :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hRpos.le
  have hsq0 : 0 ≤ (∑ r : Fin R, a r ^ 2) / R :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hRpos.le
  have h1 : ((R : ℝ≥0∞) ^ 2)⁻¹
      * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
          ENNReal.ofReal ((a q.1 - a q.2) ^ 2) = ENNReal.ofReal (varFin a) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), sum_pairs_sq_eq_var hR a,
      ENNReal.ofReal_mul (sq_nonneg _)]
    have hsq : ENNReal.ofReal ((R : ℝ) ^ 2) = (R : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.ofReal_pow hRpos.le, ENNReal.ofReal_natCast]
    rw [hsq, ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by simp), one_mul]
  have h2 : (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (a r ^ 2)
      = ENNReal.ofReal ((∑ r : Fin R, a r ^ 2) / R) := by
    have hinv : (R : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((R : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos hRpos, ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), hinv,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hRpos.le), inv_mul_eq_div]
  have hcs : (c.sync : ℝ≥0∞) = ENNReal.ofReal (c.sync : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  have hct : (c.tracking : ℝ≥0∞) = ENNReal.ofReal (c.tracking : ℝ) :=
    (ENNReal.ofReal_coe_nnreal).symm
  rw [h1, h2, hcs, hct, ← ENNReal.ofReal_mul c.sync.coe_nonneg,
    ← ENNReal.ofReal_mul c.tracking.coe_nonneg,
    ← ENNReal.ofReal_add (mul_nonneg c.sync.coe_nonneg hvar0)
      (mul_nonneg c.tracking.coe_nonneg hsq0)]
  rfl

/-! ## Every frame is played -/

/-- **From some frame on, playback at exact latencies passes every frame.**
Each such frame is passed by a step of every speaker's playback that begins
at output sample `K` or later. -/
theorem World.PlaysAtLatencies.exists_covers {w : World H R} {plays : Fin R → ℕ → Option ℝ}
    {L : Fin R → ℝ} {K : ℕ} (h : w.PlaysAtLatencies plays L K) {ρ t₀ : ℝ} (hρ : 0 < ρ)
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ)
    (hout : ∀ r (T : Time), ∃ k, T ≤ (w.speaker r).out k) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ r, ∃ k, K ≤ k ∧ Covers (plays r) k n := by
  classical
  -- The position that each output sample from `K` on plays.
  have hpos : ∀ r k, K ≤ k → plays r k = some (ρ * ((w.speaker r).out k - L r - t₀)) := by
    intro r k hk
    obtain ⟨-, x, hx, hE⟩ := h r k hk
    rw [hcap] at hE
    have h1 : x / ρ = (w.speaker r).out k - L r - t₀ := by linarith
    rw [div_eq_iff hρ.ne'] at h1
    rw [hx, h1]
    ring_nf
  refine ⟨∑ r, ⌈ρ * ((w.speaker r).out K - L r - t₀)⌉₊, fun n hn r => ?_⟩
  have hK : ρ * ((w.speaker r).out K - L r - t₀) ≤ n := by
    have h1 : ρ * ((w.speaker r).out K - L r - t₀)
        ≤ ⌈ρ * ((w.speaker r).out K - L r - t₀)⌉₊ := Nat.le_ceil _
    have h2 : ⌈ρ * ((w.speaker r).out K - L r - t₀)⌉₊ ≤ n :=
      (Finset.single_le_sum (f := fun r => ⌈ρ * ((w.speaker r).out K - L r - t₀)⌉₊)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)).trans hn
    exact h1.trans (by exact_mod_cast h2)
  have hex : ∃ k, K ≤ k ∧ (n : ℝ) < ρ * ((w.speaker r).out k - L r - t₀) := by
    obtain ⟨k₀, hk₀⟩ := hout r (((n : ℝ) + 1) / ρ + L r + t₀)
    refine ⟨max k₀ K, le_max_right _ _, ?_⟩
    have hmono : (w.speaker r).out k₀ ≤ (w.speaker r).out (max k₀ K) :=
      (w.speaker r).out_strictMono.monotone (le_max_left _ _)
    have h1 : ((n : ℝ) + 1) / ρ ≤ (w.speaker r).out (max k₀ K) - L r - t₀ := by linarith
    have h2 := (div_le_iff₀' hρ).mp h1
    linarith
  obtain ⟨hk₁K, hk₁⟩ := Nat.find_spec hex
  have hne : Nat.find hex ≠ K := by
    intro e
    rw [e] at hk₁
    linarith
  have hkK : K ≤ Nat.find hex - 1 := by omega
  have hmin : ¬(K ≤ Nat.find hex - 1
      ∧ (n : ℝ) < ρ * ((w.speaker r).out (Nat.find hex - 1) - L r - t₀)) :=
    Nat.find_min hex (by omega)
  have hle : ρ * ((w.speaker r).out (Nat.find hex - 1) - L r - t₀) ≤ n := by
    by_contra hc
    exact hmin ⟨hkK, not_le.mp hc⟩
  have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  obtain ⟨x, y, hx, hy, hxy, hyx⟩ := (h r (Nat.find hex - 1) hkK).1
  rw [hpos r _ hkK, Option.some.injEq] at hx
  rw [hsucc, hpos r _ hk₁K, Option.some.injEq] at hy
  refine ⟨Nat.find hex - 1, hkK, x, y, ?_, ?_, hxy, hyx, ?_, ?_⟩
  · rw [hpos r _ hkK, hx]
  · rw [hsucc, hpos r _ hk₁K, hy]
  · rw [← hx]
    exact hle
  · rw [← hy]
    exact hk₁.le

/-- **From some frame on, playback at exact latencies plays every frame at a
known time**: speaker `r` plays the frame exactly `L r` after its capture. -/
theorem World.PlaysAtLatencies.exists_playTime {w : World H R}
    {plays : Fin R → ℕ → Option ℝ} {L : Fin R → ℝ} {K : ℕ} (h : w.PlaysAtLatencies plays L K)
    {ρ t₀ : ℝ} (hρ : 0 < ρ) (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ)
    (hout : ∀ r (T : Time), ∃ k, T ≤ (w.speaker r).out k) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ r, w.playTime plays r n = some (w.source.capture n + L r) := by
  classical
  obtain ⟨N₁, hN₁⟩ := h.exists_covers hρ hcap hout
  obtain ⟨N₂, hN₂⟩ := exists_frame_beyond plays K
  refine ⟨max N₁ N₂, fun n hn r => ?_⟩
  have hsome : ∃ t, w.playTime plays r n = some t := by
    obtain ⟨k, -, hcov⟩ := hN₁ n (le_trans (le_max_left _ _) hn) r
    unfold World.playTime Spec.playTime
    split_ifs with h'
    · obtain ⟨x, y, hx, hy, -⟩ := Nat.find_spec h'
      rw [hx, hy]
      exact ⟨_, rfl⟩
    · exact absurd ⟨k, hcov⟩ h'
  obtain ⟨t, ht⟩ := hsome
  have hl : w.latency plays r n = some (t - w.source.capture n) := by
    simp [World.latency, ht]
  have he := w.latency_eq_of_exact plays h hcap
    (fun k hk => hN₂ r k n hk (le_trans (le_max_right _ _) hn)) hl
  rw [ht]
  congr 1
  linarith

/-! ## The cost from below -/

/-- **The cost of playback at exact latencies is at least the frame cost.**
Let every speaker `r` play at the exact latency `L r` from some output sample
on, in a world whose capture times are linear in the position, whose output
samples leave after every true time, whose frames are captured after every
true time, and whose target latency is constant. Then the cost is at least
`frameCost c L target`. -/
theorem World.frameCost_le_cost_of_exact (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) {L : Fin R → ℝ} {ρ t₀ target : ℝ} {K : ℕ} (h : w.PlaysAtLatencies plays L K)
    (hρ : 0 < ρ) (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ)
    (htarget : ∀ n, w.target n = target) (hout : ∀ r (T : Time), ∃ k, T ≤ (w.speaker r).out k)
    (hR : 0 < R) (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (frameCost c L target) ≤ w.cost plays c := by
  obtain ⟨N, hN⟩ := h.exists_playTime hρ hcap hout
  let g : ℕ → ℝ≥0∞ := fun n => if N ≤ n then ENNReal.ofReal (frameCost c L target) else 0
  have h1 : longRun (w.accruedFrames g) ≤ w.cost plays c := by
    refine w.longRun_frames_le_cost plays c g fun n => ?_
    by_cases hn : N ≤ n
    · have hfun : (fun r => w.source.capture n + L r - w.source.capture n) = L := by
        funext r
        ring
      rw [w.weighted_frame_modal_split plays c hR n (hN n hn), hfun, htarget]
      simp only [g, hn, ↓reduceIte, frameCost]
      exact le_rfl
    · simp [g, hn]
  have h2 : ENNReal.ofReal (frameCost c L target) + ENNReal.ofReal (frameCost c L target)
      ≤ longRun (w.accruedFrames g) + longRun (w.accruedFrames g) :=
    w.longRun_accruedFrames_add_ge g g N
      (fun n hn => by simp only [g, hn, ↓reduceIte]; exact le_rfl) hunb
  rw [← two_mul, ← two_mul] at h2
  exact ((ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp h2).trans h1

end Unisono.Spec
