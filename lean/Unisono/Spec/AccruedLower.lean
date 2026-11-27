/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Objectives

/-!
# Lower bounds on what a playback accrues

A lower bound on the cost of a playback is put together from frames and
output samples that are known to be charged. This file has the three steps
that do not depend on which they are.

* `World.sum_le_accruedFrames_latency`: the latency accrued until true time
  `T` is at least the latencies of any finite set of frames of each speaker
  that are captured before `T`, each times the time until the next frame is
  captured, averaged over the speakers.
* `World.sum_le_accruedOutputs`: a cost of the output samples accrued until
  `T` is at least its sum over any finite set of output samples of each
  speaker that leave before `T`, averaged over the speakers.
* `World.longRun_le_cost_of_latency_missed`: the cost of a playback is at
  least the long-run average of any quantity that, from some true time on,
  is at most the weighted latency, missed samples and discontinuities
  accrued. The other three objectives are left out, which only lowers the
  bound.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal

variable {H : Type} {R : ℕ}

/-- **The latency accrued is at least that of any frames captured so far.**
For each speaker `r` let `S r` be a finite set of frames that are captured
before true time `T`. The latency accrued until `T` is at least the average
over the speakers of the latencies of those frames at the speaker, each
times the time until the next frame is captured. -/
theorem World.sum_le_accruedFrames_latency (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {T : Time} (S : Fin R → Finset ℕ) (hS : ∀ r, ∀ n ∈ S r, w.source.capture n < T) :
    (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ n ∈ S r, w.latencyAt plays r n
        * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
      ≤ w.accruedFrames (w.latencyCost plays) T := by
  classical
  obtain ⟨U, hU⟩ : ∃ U : Finset ℕ, U = Finset.univ.biUnion S := ⟨_, rfl⟩
  have hUT : ∀ n ∈ U, w.source.capture n < T := by
    intro n hn
    rw [hU, Finset.mem_biUnion] at hn
    obtain ⟨r, -, hr⟩ := hn
    exact hS r n hr
  have hsub : ∀ r, S r ⊆ U := fun r => by
    rw [hU]
    exact Finset.subset_biUnion_of_mem S (Finset.mem_univ r)
  unfold World.accruedFrames World.latencyCost
  calc (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ n ∈ S r, w.latencyAt plays r n
          * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ n ∈ U, w.latencyAt plays r n
          * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum_of_subset (hsub r))
    _ = ∑ n ∈ U, (R : ℝ≥0∞)⁻¹ * (∑ r, w.latencyAt plays r n)
          * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_mul, mul_assoc]
    _ = ∑ n ∈ U, if w.source.capture n < T then
          (R : ℝ≥0∞)⁻¹ * (∑ r, w.latencyAt plays r n)
            * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0 :=
        Finset.sum_congr rfl fun n hn => by rw [ite_eq_left (hUT n hn)]
    _ ≤ ∑' n, if w.source.capture n < T then
          (R : ℝ≥0∞)⁻¹ * (∑ r, w.latencyAt plays r n)
            * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0 :=
        sum_le_tsum U

/-- **A cost of the output samples accrued is at least its sum over any
output samples that have left.** For each speaker `r` let `S r` be a finite
set of output samples that leave before true time `T`. A cost of the output
samples accrued until `T` is at least the average over the speakers of its
sum over those output samples. -/
theorem World.sum_le_accruedOutputs (w : World H R) (cost : Fin R → ℕ → ℝ≥0∞) {T : Time}
    (S : Fin R → Finset ℕ) (hS : ∀ r, ∀ k ∈ S r, (w.speaker r).out k < T) :
    (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ S r, cost r k ≤ w.accruedOutputs cost T := by
  unfold World.accruedOutputs
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun r _ => ?_)
  calc ∑ k ∈ S r, cost r k
      = ∑ k ∈ S r, if (w.speaker r).out k < T then cost r k else 0 :=
        Finset.sum_congr rfl fun k hk => by rw [ite_eq_left (hS r k hk)]
    _ ≤ ∑' k, if (w.speaker r).out k < T then cost r k else 0 := sum_le_tsum (S r)

/-- **The cost is at least the long-run average of any lower bound on the
weighted latency, missed samples and discontinuities accrued.** If, from
some true time on, `G T` is at most the weight of latency times the latency
accrued until `T`, plus the weight of missed samples times the missed
samples accrued, plus the weight of discontinuities times the
discontinuities accrued, then the long-run average of `G` is at most the
cost of the playback. -/
theorem World.longRun_le_cost_of_latency_missed (w : World H R)
    (plays : Fin R → ℕ → Option ℝ) (c : Weights) {G : Time → ℝ≥0∞} {T₀ : Time}
    (hG : ∀ T, T₀ ≤ T →
      G T ≤ (c.latency : ℝ≥0∞) * w.accruedFrames (w.latencyCost plays) T
        + (c.missed : ℝ≥0∞)
          * w.accruedOutputs (fun r k => (missedAt (plays r) k : ℝ≥0∞)) T
        + (c.discontinuities : ℝ≥0∞)
          * w.accruedOutputs (fun r k => (discontinuityAt (plays r) k : ℝ≥0∞)) T) :
    longRun G ≤ w.cost plays c := by
  unfold World.cost longRun
  refine Filter.limsup_le_limsup ?_
  filter_upwards [Filter.eventually_ge_atTop T₀] with T hT
  refine ENNReal.div_le_div_right ((hG T hT).trans ?_) _
  have h1 : (c.latency : ℝ≥0∞) * w.accruedFrames (w.latencyCost plays) T
      ≤ (c.sync : ℝ≥0∞) * w.accruedFrames (w.syncCost plays) T
        + (c.latency : ℝ≥0∞) * w.accruedFrames (w.latencyCost plays) T
        + (c.tracking : ℝ≥0∞) * w.accruedFrames (w.trackingCost plays) T
        + (c.roughness : ℝ≥0∞) * w.accruedOutputs (w.roughnessCost plays) T :=
    le_add_right (le_add_right le_add_self)
  exact add_le_add (add_le_add h1 le_rfl) le_rfl

end Unisono.Spec
