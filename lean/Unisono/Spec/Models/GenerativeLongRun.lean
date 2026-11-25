/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeHorizon
public import Unisono.Spec.AccruedLower

/-!
# From the cells to the cost accrued until a horizon

Two steps from the sum over the cells of one speaker (`Prior.sum_cells_le`)
towards the long-run average cost.

* `Prior.lintegral_clear_ge`: a cell counts with probability at least
  `exp (-rate * m₀ * ℓ)`, the probability that the link pauses nothing in
  the `m₀` cells before it. So the mean of the level program of the cell
  where it counts, and of the least latency term elsewhere, is at least that
  probability times the level program plus the rest times the least latency
  term.
* `World.accrued_ge_of_blocks`: the cost accrued until a true time `T` is at
  least the average over any set of speakers of: the weighted latency of the
  frames that the speaker passes on new ground in its first playback blocks,
  and the missed samples and discontinuities of the output samples of those
  blocks, when the blocks end before `T` and the frames are captured before
  `T`.

No bound on expected cost is proved here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal

variable {H : Type} {R : ℕ}

/-- **The cost accrued until a horizon is at least what the first playback
blocks of some speakers cost.** Let `𝒮` be a set of speakers. For each of
them let its first `N r` playback blocks, of `B` output samples, end before
true time `T`, and let the frames that its steps before output sample
`N r * B` pass on new ground be captured before `T`. Then the average over
all speakers of the sum, over the speakers of `𝒮`, of: the weight of latency
times the latency of each of those frames times the time until the next
frame is captured, the weight of missed samples times the missed samples
counted at the output samples up to `N r * B`, and the weight of
discontinuities times the discontinuities counted at the output samples
before `N r * B`, is at most the three weighted costs accrued until `T`. -/
theorem World.accrued_ge_of_blocks (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) {T : Time} (𝒮 : Finset (Fin R)) (N : Fin R → ℕ) (B : ℕ)
    (hout : ∀ r ∈ 𝒮, (w.speaker r).out (N r * B) < T)
    (hcap : ∀ r ∈ 𝒮, ∀ n ∈ newFrames (plays r) 0 (N r * B), w.source.capture n < T) :
    (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ((c.latency : ℝ≥0∞)
          * ∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
            * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
        + (c.missed : ℝ≥0∞) * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)
        + (c.discontinuities : ℝ≥0∞)
          * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞))
      ≤ (c.latency : ℝ≥0∞) * w.accruedFrames (w.latencyCost plays) T
        + (c.missed : ℝ≥0∞)
          * w.accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) T
        + (c.discontinuities : ℝ≥0∞)
          * w.accruedOutputs (fun r k => (discontinuityAt (plays r) k : ℝ≥0∞)) T := by
  classical
  have hmono : ∀ r, Monotone (w.speaker r).out := fun r => (w.speaker r).out_strictMono.monotone
  have h1 := w.sum_le_accruedFrames_latency plays (T := T)
    (fun r => if r ∈ 𝒮 then newFrames (plays r) 0 (N r * B) else ∅) (fun r n hn => by
      by_cases hr : r ∈ 𝒮
      · rw [ite_eq_left hr] at hn
        exact hcap r hr n hn
      · rw [ite_eq_right hr] at hn
        exact absurd hn (Finset.notMem_empty n))
  have h2 := w.sum_le_accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) (T := T)
    (fun r => if r ∈ 𝒮 then Finset.range (N r * B + 1) else ∅) (fun r k hk => by
      by_cases hr : r ∈ 𝒮
      · rw [ite_eq_left hr] at hk
        exact lt_of_le_of_lt (hmono r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
          (hout r hr)
      · rw [ite_eq_right hr] at hk
        exact absurd hk (Finset.notMem_empty k))
  have h3 := w.sum_le_accruedOutputs (fun r k => (discontinuityAt (plays r) k : ℝ≥0∞))
    (T := T) (fun r => if r ∈ 𝒮 then Finset.range (N r * B) else ∅) (fun r k hk => by
      by_cases hr : r ∈ 𝒮
      · rw [ite_eq_left hr] at hk
        exact lt_of_le_of_lt (hmono r (Finset.mem_range.mp hk).le) (hout r hr)
      · rw [ite_eq_right hr] at hk
        exact absurd hk (Finset.notMem_empty k))
  -- The sums over all speakers are the sums over the speakers of `𝒮`.
  have e : ∀ (F : Fin R → Finset ℕ) (g : Fin R → ℕ → ℝ≥0∞),
      ∑ r, ∑ n ∈ (if r ∈ 𝒮 then F r else ∅), g r n = ∑ r ∈ 𝒮, ∑ n ∈ F r, g r n := by
    intro F g
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => r ∈ 𝒮)]
    have hz : ∑ r ∈ Finset.univ.filter (fun r => ¬r ∈ 𝒮),
        ∑ n ∈ (if r ∈ 𝒮 then F r else ∅), g r n = 0 :=
      Finset.sum_eq_zero fun r hr => by
        rw [ite_eq_right (Finset.mem_filter.mp hr).2, Finset.sum_empty]
    rw [hz, add_zero]
    have hfilter : Finset.univ.filter (fun r => r ∈ 𝒮) = 𝒮 := by
      ext r
      simp
    rw [hfilter]
    exact Finset.sum_congr rfl fun r hr => by rw [ite_eq_left hr]
  rw [e] at h1 h2 h3
  calc (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ((c.latency : ℝ≥0∞)
            * ∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
              * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
          + (c.missed : ℝ≥0∞)
            * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)
          + (c.discontinuities : ℝ≥0∞)
            * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞))
      = (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
            ∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
              * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n))
          + (c.missed : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
            ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞))
          + (c.discontinuities : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
            ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul' le_rfl h1) (mul_le_mul' le_rfl h2))
        (mul_le_mul' le_rfl h3)

/-- By how much the frames captured before true time `T` are followed by the
next frame sooner than the reference period `p₀`, added up. With a capture
device that runs at a constant rate and `p₀` its period, this is zero. -/
def World.captureDeficit (w : World H R) (p₀ : ℝ) (T : Time) : ℝ≥0∞ :=
  ∑' n, if w.source.capture n < T then
    ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n)) else 0

theorem World.sum_le_captureDeficit (w : World H R) (p₀ : ℝ) {T : Time} (F : Finset ℕ)
    (hF : ∀ n ∈ F, w.source.capture n < T) :
    ∑ n ∈ F, ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n))
      ≤ w.captureDeficit p₀ T := by
  unfold World.captureDeficit
  calc ∑ n ∈ F, ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n))
      = ∑ n ∈ F, if w.source.capture n < T then
          ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n)) else 0 :=
        Finset.sum_congr rfl fun n hn => by rw [ite_eq_left (hF n hn)]
    _ ≤ _ := sum_le_tsum F

/-- **The cost accrued until a horizon, against bounds for some speakers.**
Let `𝒮` be a set of speakers whose first `N r` playback blocks end before
true time `T`, with the frames passed on new ground in them captured before
`T`. For each of them let `Q r` be at most the right-hand side of
`Builds.cellsCost_le`: the weight of latency times the weighted latency of
those frames with the terms for shorter periods, for the blocks and for the
missed samples (with the constant `C`), plus `w'` times the missed samples
and `s` times the discontinuities of the output samples of the blocks. Let
the weight of missed samples be at least the weight of latency times
`p₀ * C`, plus `w'`, and the weight of discontinuities at least `w' * s`.
Then the average of `Q` over all speakers is at most the weighted latency,
missed samples and discontinuities accrued until `T`, plus the weight of
latency times the average of: `Gcap` times `captureDeficit`, plus
`p₀ * (1 + s) * Gcap` for each block. The last two terms do not depend on
the solution. -/
theorem World.sum_le_accrued_add_loss (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) {T : Time} (𝒮 : Finset (Fin R)) (N : Fin R → ℕ) (B : ℕ) {s Gcap p₀ C : ℝ}
    (hs : 0 ≤ s) (hcap : 0 ≤ Gcap) (hp₀ : 0 ≤ p₀) (hC : 0 ≤ C) (w' : ℝ≥0∞)
    (hw1 : (c.latency : ℝ≥0∞) * ENNReal.ofReal (p₀ * C) + w' ≤ c.missed)
    (hw2 : w' * ENNReal.ofReal s ≤ c.discontinuities)
    (hout : ∀ r ∈ 𝒮, (w.speaker r).out (N r * B) < T)
    (hcapt : ∀ r ∈ 𝒮, ∀ n ∈ newFrames (plays r) 0 (N r * B), w.source.capture n < T)
    (Q : Fin R → ℝ≥0∞)
    (hQ : ∀ r ∈ 𝒮, Q r ≤ (c.latency : ℝ≥0∞)
        * (∑ n ∈ newFrames (plays r) 0 (N r * B),
            (w.latencyAt plays r n
                * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
              + ENNReal.ofReal Gcap
                * ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n)))
          + ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap)
              + C * missedBefore (plays r) (N r * B + 1))))
        + w' * ∑ k ∈ Finset.range (N r * B),
            ENNReal.ofReal ((missedAt (plays r) k : ℝ)
              + s * (discontinuityAt (plays r) k : ℝ))) :
    (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, Q r
      ≤ (c.latency : ℝ≥0∞) * w.accruedFrames (w.latencyCost plays) T
        + (c.missed : ℝ≥0∞)
          * w.accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) T
        + (c.discontinuities : ℝ≥0∞)
          * w.accruedOutputs (fun r k => (discontinuityAt (plays r) k : ℝ≥0∞)) T
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
            (ENNReal.ofReal Gcap * w.captureDeficit p₀ T
              + ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap))))) := by
  have hper : ∀ r ∈ 𝒮, Q r
      ≤ ((c.latency : ℝ≥0∞)
            * ∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
              * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
          + (c.missed : ℝ≥0∞)
            * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)
          + (c.discontinuities : ℝ≥0∞)
            * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞))
        + (c.latency : ℝ≥0∞) * (ENNReal.ofReal Gcap * w.captureDeficit p₀ T
            + ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap)))) := by
    intro r hr
    refine (hQ r hr).trans ?_
    have hdef : ∑ n ∈ newFrames (plays r) 0 (N r * B), ENNReal.ofReal Gcap
          * ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n))
        ≤ ENNReal.ofReal Gcap * w.captureDeficit p₀ T := by
      rw [← Finset.mul_sum]
      exact mul_le_mul' le_rfl (w.sum_le_captureDeficit p₀ _ (hcapt r hr))
    have hM : ((missedBefore (plays r) (N r * B + 1) : ℕ) : ℝ≥0∞)
        = ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞) := by
      unfold missedBefore
      push_cast
      rfl
    have hN0 : (0 : ℝ) ≤ (N r : ℝ) * ((1 + s) * Gcap) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) hcap)
    have e1 : ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap)
          + C * missedBefore (plays r) (N r * B + 1)))
        = ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap)))
          + ENNReal.ofReal (p₀ * C)
            * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞) := by
      have hsplit : p₀ * ((N r : ℝ) * ((1 + s) * Gcap)
            + C * (missedBefore (plays r) (N r * B + 1) : ℝ))
          = p₀ * ((N r : ℝ) * ((1 + s) * Gcap))
            + p₀ * C * (missedBefore (plays r) (N r * B + 1) : ℝ) := by ring
      rw [← hM, hsplit, ENNReal.ofReal_add (mul_nonneg hp₀ hN0)
        (mul_nonneg (mul_nonneg hp₀ hC) (Nat.cast_nonneg _)),
        ENNReal.ofReal_mul (mul_nonneg hp₀ hC), ENNReal.ofReal_natCast]
    have e2 : ∑ k ∈ Finset.range (N r * B), ENNReal.ofReal ((missedAt (plays r) k : ℝ)
          + s * (discontinuityAt (plays r) k : ℝ))
        = ∑ k ∈ Finset.range (N r * B), (missedAt (plays r) k : ℝ≥0∞)
          + ENNReal.ofReal s
            * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg hs (Nat.cast_nonneg _)),
        ENNReal.ofReal_mul hs, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hmle : ∑ k ∈ Finset.range (N r * B), (missedAt (plays r) k : ℝ≥0∞)
        ≤ ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞) :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ _))
    rw [Finset.sum_add_distrib, e1, e2]
    calc (c.latency : ℝ≥0∞)
            * (∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
                  * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
                + ∑ n ∈ newFrames (plays r) 0 (N r * B), ENNReal.ofReal Gcap
                  * ENNReal.ofReal (p₀ - (w.source.capture (n + 1) - w.source.capture n))
              + (ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap)))
                + ENNReal.ofReal (p₀ * C)
                  * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)))
          + w' * (∑ k ∈ Finset.range (N r * B), (missedAt (plays r) k : ℝ≥0∞)
            + ENNReal.ofReal s
              * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞))
        ≤ (c.latency : ℝ≥0∞)
            * (∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
                  * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
                + ENNReal.ofReal Gcap * w.captureDeficit p₀ T
              + (ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap)))
                + ENNReal.ofReal (p₀ * C)
                  * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)))
          + w' * (∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)
            + ENNReal.ofReal s
              * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞)) := by
          gcongr
      _ = ((c.latency : ℝ≥0∞)
              * ∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
                * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
            + ((c.latency : ℝ≥0∞) * ENNReal.ofReal (p₀ * C) + w')
              * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)
            + (w' * ENNReal.ofReal s)
              * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞))
          + (c.latency : ℝ≥0∞) * (ENNReal.ofReal Gcap * w.captureDeficit p₀ T
              + ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap)))) := by ring
      _ ≤ _ := by gcongr
  have hblocks := w.accrued_ge_of_blocks plays c 𝒮 N B hout hcapt
  calc (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, Q r
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, (((c.latency : ℝ≥0∞)
              * ∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
                * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
            + (c.missed : ℝ≥0∞)
              * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)
            + (c.discontinuities : ℝ≥0∞)
              * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞))
          + (c.latency : ℝ≥0∞) * (ENNReal.ofReal Gcap * w.captureDeficit p₀ T
              + ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap))))) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum hper)
    _ = (R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮, ((c.latency : ℝ≥0∞)
              * ∑ n ∈ newFrames (plays r) 0 (N r * B), w.latencyAt plays r n
                * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
            + (c.missed : ℝ≥0∞)
              * ∑ k ∈ Finset.range (N r * B + 1), (missedAt (plays r) k : ℝ≥0∞)
            + (c.discontinuities : ℝ≥0∞)
              * ∑ k ∈ Finset.range (N r * B), (discontinuityAt (plays r) k : ℝ≥0∞))
          + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r ∈ 𝒮,
              (ENNReal.ofReal Gcap * w.captureDeficit p₀ T
                + ENNReal.ofReal (p₀ * ((N r : ℝ) * ((1 + s) * Gcap))))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    _ ≤ _ := add_le_add hblocks le_rfl

end Unisono.Spec

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {Ω : Type} [MeasurableSpace Ω]
  {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R}

open Classical in
/-- **A cell counts with probability at least `exp (-rate * m₀ * ℓ)`.** In a
random world of any member: let `v` and `fl ≤ v` be two numbers. The mean of
`v` on the outcomes in which the link from the sender to the host of speaker
`r` pauses nothing in the `m₀` cells before cell `j` (`clearSet`), and of
`fl` on the others, is at least `q * v + (1 - q) * fl`, where
`q = exp (-rate * m₀ * ℓ)` and `rate` pauses of the link begin per second on
average. -/
theorem Prior.lintegral_clear_ge (hD : m.Prior f P D) (d₁ : Draw H R) (r : Fin R) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (m₀ j : ℕ) {v fl : ℝ≥0∞} (hfl : fl ≤ v) :
    ENNReal.ofReal (Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ)))) * v
        + ENNReal.ofReal (1 - Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ))))
          * fl
      ≤ ∫⁻ ω, (if frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j then v else fl) ∂P := by
  have := hD.prob
  have hrate := f.linkPauseRate_nonneg m.sender (m.host r)
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-(f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ))) :=
    ⟨_, rfl⟩
  rw [← hq]
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact (Real.exp_pos _).le
  have hq1 : q ≤ 1 := by
    rw [hq]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hrate
      (mul_nonneg (Nat.cast_nonneg _) hℓ)))
  have hab : (j : ℝ) * ℓ ≤ ((j : ℝ) + 1) * ℓ := by nlinarith
  have hjle : (((j - m₀ : ℕ) : ℝ)) * ℓ ≤ (j : ℝ) * ℓ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le j m₀) hℓ
  -- The cell counts exactly when the link pauses nothing in the cells before it.
  have hmem : ∀ ω, frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j
      ↔ (D ω).linkPaused m.sender (m.host r) ((j : ℝ) * ℓ)
        - (D ω).linkPaused m.sender (m.host r) (((j - m₀ : ℕ) : ℝ) * ℓ) ≤ 0 := fun ω => by
    have hlp : (frameOutside m d₁ (D ω) r ℓ j).linkPaused m.sender (m.host r)
        = pathOutside ((j : ℝ) * ℓ) (((j : ℝ) + 1) * ℓ)
          ((D ω).linkPaused m.sender (m.host r)) :=
      (D ω).linkOutside_self m.sender (m.host r) _ _
    show (frameOutside m d₁ (D ω) r ℓ j).linkPaused m.sender (m.host r) ((j : ℝ) * ℓ)
      - (frameOutside m d₁ (D ω) r ℓ j).linkPaused m.sender (m.host r)
        (((j - m₀ : ℕ) : ℝ) * ℓ) ≤ 0 ↔ _
    rw [hlp, pathOutside_of_le hab _ le_rfl, pathOutside_of_le hab _ hjle]
  have hlaw := hD.linkPaused_law m.sender (m.host r) (((j - m₀ : ℕ) : ℝ) * ℓ) ((j : ℝ) * ℓ) hjle
  obtain ⟨C, hCdef⟩ : ∃ C : Set Ω, C = {ω | (D ω).linkPaused m.sender (m.host r) ((j : ℝ) * ℓ)
      - (D ω).linkPaused m.sender (m.host r) (((j - m₀ : ℕ) : ℝ) * ℓ) ≤ 0} := ⟨_, rfl⟩
  have hCnull : NullMeasurableSet C P := by
    rw [hCdef]
    exact hlaw.aemeasurable.nullMeasurable measurableSet_Iic
  have hPC : ENNReal.ofReal q ≤ P C := by
    have h1 : P C = pauseLaw (Real.toNNReal (f.linkPauseRate m.sender (m.host r)
        * ((j : ℝ) * ℓ - ((j - m₀ : ℕ) : ℝ) * ℓ))) (f.linkPauseLength m.sender (m.host r))
        (Set.Iic 0) := by
      rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable measurableSet_Iic,
        hCdef]
      rfl
    have h2 := pauseLaw_ge_dirac (Real.toNNReal (f.linkPauseRate m.sender (m.host r)
        * ((j : ℝ) * ℓ - ((j - m₀ : ℕ) : ℝ) * ℓ))) (f.linkPauseLength m.sender (m.host r))
      (Set.Iic 0)
    have h3 : (ENNReal.ofReal (Real.exp (-((Real.toNNReal (f.linkPauseRate m.sender (m.host r)
        * ((j : ℝ) * ℓ - ((j - m₀ : ℕ) : ℝ) * ℓ)) : ℝ≥0) : ℝ)))
          • Measure.dirac (0 : ℝ)) (Set.Iic 0)
        = ENNReal.ofReal (Real.exp (-((Real.toNNReal (f.linkPauseRate m.sender (m.host r)
          * ((j : ℝ) * ℓ - ((j - m₀ : ℕ) : ℝ) * ℓ)) : ℝ≥0) : ℝ))) := by
      simp
    rw [h3] at h2
    have hsub : (j : ℝ) - ((j - m₀ : ℕ) : ℝ) ≤ (m₀ : ℝ) := by
      have h4 : j ≤ (j - m₀) + m₀ := by omega
      have h5 : (j : ℝ) ≤ ((j - m₀ : ℕ) : ℝ) + (m₀ : ℝ) := by exact_mod_cast h4
      linarith
    have hc0 : 0 ≤ f.linkPauseRate m.sender (m.host r)
        * ((j : ℝ) * ℓ - ((j - m₀ : ℕ) : ℝ) * ℓ) := mul_nonneg hrate (by linarith)
    have hcle : f.linkPauseRate m.sender (m.host r)
          * ((j : ℝ) * ℓ - ((j - m₀ : ℕ) : ℝ) * ℓ)
        ≤ f.linkPauseRate m.sender (m.host r) * (m₀ * ℓ) := by
      refine mul_le_mul_of_nonneg_left ?_ hrate
      have h6 := mul_le_mul_of_nonneg_right hsub hℓ
      linarith
    rw [h1]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h2
    rw [hq, Real.coe_toNNReal _ hc0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsplit : ENNReal.ofReal q * v + ENNReal.ofReal (1 - q) * fl
      = fl + ENNReal.ofReal q * (v - fl) := by
    have hone : ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1 := by
      rw [← ENNReal.ofReal_add hq0 (by linarith)]
      simp
    calc ENNReal.ofReal q * v + ENNReal.ofReal (1 - q) * fl
        = ENNReal.ofReal q * (fl + (v - fl)) + ENNReal.ofReal (1 - q) * fl := by
          rw [add_tsub_cancel_of_le hfl]
      _ = (ENNReal.ofReal q + ENNReal.ofReal (1 - q)) * fl + ENNReal.ofReal q * (v - fl) := by
          ring
      _ = fl + ENNReal.ofReal q * (v - fl) := by rw [hone, one_mul]
  rw [hsplit]
  calc fl + ENNReal.ofReal q * (v - fl)
      ≤ fl + P C * (v - fl) := add_le_add le_rfl (mul_le_mul' hPC le_rfl)
    _ = ∫⁻ ω, (fl + C.indicator (fun _ => v - fl) ω) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_const₀ hCnull, mul_comm]
    _ = ∫⁻ ω, (if frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j then v else fl) ∂P := by
        refine lintegral_congr fun ω => ?_
        by_cases hω : frameOutside m d₁ (D ω) r ℓ j ∈ clearSet m r ℓ m₀ j
        · have hωC : ω ∈ C := by
            rw [hCdef]
            exact (hmem ω).mp hω
          rw [ite_eq_left hω, Set.indicator_of_mem hωC, add_tsub_cancel_of_le hfl]
        · have hωC : ω ∉ C := by
            rw [hCdef]
            exact fun h => hω ((hmem ω).mpr h)
          rw [ite_eq_right hω, Set.indicator_of_notMem hωC, add_zero]

end Unisono.Spec.GenerativeWorld
