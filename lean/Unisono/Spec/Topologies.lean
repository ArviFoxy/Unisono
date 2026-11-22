/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Objectives
public import Unisono.Spec.Run
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Communication topologies, modal objective decomposition, and shift lower bounds

This file defines communication topologies, proves per-frame modal identities
and per-cycle ramp roughness formulas directly on `Unisono.Spec.World` and
`Unisono.Spec.Objectives`, and proves host-time shift indistinguishability and
synchronization/tracking lower bounds directly on `Unisono.Spec.Solution`.

* **Topologies (`Solution.UsesGraph`, `Solution.IsStar`).** A solution uses a
  directed communication graph `adj` when every message `(h → dst)` it ever
  sends satisfies `adj h dst`. A *star* solution restricts all communication to
  links incident on the sender (`h = sender ∨ dst = sender`). Peer solutions
  additionally allow direct receiver-to-receiver messages.
* **Modal decomposition of `World` frame objectives.** For any frame played by
  all `R > 0` speakers, the speaker latencies `ℓ_r = T_r(n) - capture(n)` split
  into their group mean (common mode `meanFin ℓ`) and zero-mean deviations
  (differential mode `ℓ_r - meanFin ℓ`):
  - `World.syncCost` equals the variance of the speaker latencies
    (`World.syncCost_eq_var`).
  - `World.trackingCost` splits orthogonally into `syncCost` plus the squared
    common-mode tracking error `(meanFin ℓ - target n)²`
    (`World.trackingCost_eq_sync_add_mean`).
  - Consequently, `c.sync * syncCost + c.tracking * trackingCost` weights the
    differential mode by `c.sync + c.tracking` and the common mode by
    `c.tracking` alone (`World.weighted_frame_modal_split`).
  - `modal_sq_split` is the algebraic vector identity
    `(∑ r, x r ^ 2) / R = meanFin x ^ 2 + varFin x`, used on per-cycle pace
    changes in `ModalControl.lean` (it is not a decomposition of sample-by-sample
    `World.roughness` across asynchronous devices).
* **Per-cycle ramp roughness and weight conversion.** Over `M` uniformly spaced
  output samples of duration `Δt = M / ρ`, ramping speed linearly across the
  cycle by a pace change of `w_cyc` frames per cycle costs
  `w_cyc² / (ρ² Δt³)` of `World.roughnessCost` (`World.roughness_linear_ramp`),
  whereas stepping speed at the cycle boundary costs `M = ρ Δt` times as much
  (`World.roughness_boundary_step`). Comparing a cycle's squared timing error
  against ramp roughness gives the normalized per-cycle position weight
  `(c_pos / c_rough) * Δt⁴` (`cyclePositionWeight_eq`).
* **Host-time shift invariance and lower bounds.** Shifting each host `h`'s
  timeline by `Δ h` (with `Δ sender = 0`) changes the one-way delay on link
  `(i, j)` by `Δ j - Δ i` (and on the reverse link `(j, i)` by `Δ i - Δ j`),
  leaving every round-trip time unchanged (`World.shiftHosts_rtt_eq`). Under
  non-Zeno progress and no simultaneous arrivals from distinct origins at the
  same host, every host observes the identical sequence of local events in the
  shifted world—even with drifting clocks and changed cross-host interleavings—so
  the solution produces identical playback decisions (`Solution.plays_shiftHosts`),
  yielding long-run lower bounds directly on `World.sync` and `World.tracking`
  (`Solution.sync_shiftHosts_lower_bound`,
  `Solution.tracking_shiftHosts_lower_bound`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open Filter
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} {Msg : Type}

/-! ## Communication topologies -/

/-- A solution respects the communication graph `adj` when every message sent
by host `h` to host `dst` satisfies `adj h dst`. -/
def Solution.UsesGraph (σ : Solution H R Msg) (adj : H → H → Prop) : Prop :=
  ∀ h view dst msg frames, (dst, msg, frames) ∈ (σ h view).sends → adj h dst

/-- A solution is a *star* solution when every message goes either from the
sender or to the sender (no receiver-to-receiver messages). -/
def Solution.IsStar (σ : Solution H R Msg) (sender : H) : Prop :=
  σ.UsesGraph fun h dst => h = sender ∨ dst = sender

/-! ## Exact modal decomposition of the specification objectives -/

/-- Sample mean of a real vector indexed by `Fin R`. -/
def meanFin (x : Fin R → ℝ) : ℝ :=
  (∑ r : Fin R, x r) / R

/-- Sample variance of a real vector indexed by `Fin R`. -/
def varFin (x : Fin R → ℝ) : ℝ :=
  (∑ r : Fin R, (x r - meanFin x) ^ 2) / R

/-- Sum of squared deviations equals `R` times the sample variance. -/
theorem sum_sq_sub_mean (hR : 0 < R) (x : Fin R → ℝ) :
    ∑ r : Fin R, (x r - meanFin x) ^ 2 = R * varFin x := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold varFin
  field_simp

/-- **Pythagorean modal split for any real vector.** The average square of
`x : Fin R → ℝ` equals the square of its mean (common mode) plus its sample
variance (differential mode). -/
theorem modal_sq_split (hR : 0 < R) (x : Fin R → ℝ) :
    (∑ r : Fin R, x r ^ 2) / R = meanFin x ^ 2 + varFin x := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hsum : ∑ r : Fin R, (x r - meanFin x) ^ 2
      = (∑ r : Fin R, x r ^ 2) - R * meanFin x ^ 2 := by
    have hexp : ∀ r : Fin R, (x r - meanFin x) ^ 2
        = x r ^ 2 - 2 * meanFin x * x r + meanFin x ^ 2 := fun r => by ring
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm : ∑ r : Fin R, x r = R * meanFin x := by
      unfold meanFin
      field_simp
    rw [hm]
    ring
  unfold varFin
  rw [hsum]
  field_simp
  ring

/-- Shifted Pythagorean modal split around an arbitrary target `t`:
`mean_r (x_r - t)² = var(x) + (mean(x) - t)²`. -/
theorem modal_sq_sub_target (hR : 0 < R) (x : Fin R → ℝ) (t : ℝ) :
    (∑ r : Fin R, (x r - t) ^ 2) / R = varFin x + (meanFin x - t) ^ 2 := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hm : meanFin (fun r => x r - t) = meanFin x - t := by
    unfold meanFin
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hv : varFin (fun r => x r - t) = varFin x := by
    unfold varFin
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hm]
    ring
  rw [modal_sq_split hR (fun r => x r - t), hm, hv, add_comm]

/-- Sum of squared pairwise differences over ordered pairs `r < r'` equals
`R²` times the sample variance. -/
theorem sum_pairs_sq_eq_var (hR : 0 < R) (x : Fin R → ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (x p.1 - x p.2) ^ 2
      = (R : ℝ) ^ 2 * varFin x := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hlt_gt :
      ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (x p.1 - x p.2) ^ 2
        = ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.2 < p.1), (x p.1 - x p.2) ^ 2 := by
    refine Finset.sum_nbij Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p₁ _ p₂ _ h
      exact Prod.swap_injective h
    · intro p hp
      refine ⟨p.swap, ?_, Prod.swap_swap p⟩
      simpa using hp
    · intro p _
      dsimp only [Prod.swap]
      ring
  have hall :
      ∑ p : Fin R × Fin R, (x p.1 - x p.2) ^ 2
        = 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
            (x p.1 - x p.2) ^ 2 := by
    have hsplit : (Finset.univ : Finset (Fin R × Fin R))
        = (Finset.univ.filter fun p : Fin R × Fin R => p.1 < p.2)
          ∪ (Finset.univ.filter fun p : Fin R × Fin R => p.2 < p.1)
          ∪ (Finset.univ.filter fun p : Fin R × Fin R => p.1 = p.2) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
      rcases lt_trichotomy a b with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
    have hd1 : Disjoint
        (Finset.univ.filter fun p : Fin R × Fin R => p.1 < p.2)
        (Finset.univ.filter fun p : Fin R × Fin R => p.2 < p.1) := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      exact lt_asymm h1 h2
    have hd2 : Disjoint
        ((Finset.univ.filter fun p : Fin R × Fin R => p.1 < p.2)
          ∪ (Finset.univ.filter fun p : Fin R × Fin R => p.2 < p.1))
        (Finset.univ.filter fun p : Fin R × Fin R => p.1 = p.2) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      rcases hp1 with h | h <;> rw [hp2] at h <;> exact lt_irrefl _ h
    have hdiag :
        ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 = p.2), (x p.1 - x p.2) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [hp]
      ring
    conv_lhs => rw [hsplit]
    rw [Finset.sum_union hd2, Finset.sum_union hd1, hdiag, add_zero, ← hlt_gt]
    ring
  have hexp :
      ∑ p : Fin R × Fin R, (x p.1 - x p.2) ^ 2
        = 2 * (R : ℝ) * ∑ r : Fin R, (x r - meanFin x) ^ 2 := by
    rw [Fintype.sum_prod_type]
    have h1 : ∀ a b : Fin R, (x a - x b) ^ 2 = x a ^ 2 - 2 * x a * x b + x b ^ 2 := fun _ _ => by
      ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 : ∑ a : Fin R, 2 * x a * ∑ b : Fin R, x b
        = 2 * (∑ a : Fin R, x a) ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sq]
      ring
    rw [h2]
    have hm : ∑ r : Fin R, x r = R * meanFin x := by
      unfold meanFin
      field_simp
    have hvar := modal_sq_split hR x
    have hsumsq : ∑ r : Fin R, x r ^ 2 = R * meanFin x ^ 2 + R * varFin x := by
      have := congrArg (fun u => (R : ℝ) * u) hvar
      field_simp at this
      linarith
    rw [sum_sq_sub_mean hR x, hsumsq, hm]
    ring
  rw [sum_sq_sub_mean hR x] at hexp
  linarith

/-- **Synchronization cost is purely differential mode.** When every speaker
plays frame `n` with latencies `ℓ r = T r - c(n)`, `w.syncCost plays n` equals
`ENNReal.ofReal (varFin ℓ)`. -/
theorem World.syncCost_eq_var (w : World H R) (plays : Fin R → ℕ → Option ℝ) (hR : 0 < R)
    (n : ℕ) {T : Fin R → Time} (hT : ∀ r, w.playTime plays r n = some (T r)) :
    w.syncCost plays n = ENNReal.ofReal (varFin fun r => T r - w.source.capture n) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hpair : ∀ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
      w.pairCost plays p.1 p.2 n
        = ENNReal.ofReal (((T p.1 - w.source.capture n) - (T p.2 - w.source.capture n)) ^ 2) := by
    intro p _
    simp only [World.pairCost, hT]
    congr 1
    ring
  unfold World.syncCost
  rw [Finset.sum_congr rfl hpair, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    sum_pairs_sq_eq_var hR (fun r => T r - w.source.capture n)]
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  have hsq : ENNReal.ofReal ((R : ℝ) ^ 2) = (R : ℝ≥0∞) ^ 2 := by
    rw [ENNReal.ofReal_pow hRpos.le, ENNReal.ofReal_natCast]
  rw [hsq, ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by simp), one_mul]

/-- **Tracking cost splits orthogonally into synchronization plus common-mode
tracking.** When every speaker plays frame `n` with latencies
`ℓ r = T r - c(n)`, `w.trackingCost plays n` equals
`w.syncCost plays n + ENNReal.ofReal ((meanFin ℓ - w.target n) ^ 2)`. -/
theorem World.trackingCost_eq_sync_add_mean (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (hR : 0 < R) (n : ℕ) {T : Fin R → Time} (hT : ∀ r, w.playTime plays r n = some (T r)) :
    w.trackingCost plays n = w.syncCost plays n
      + ENNReal.ofReal ((meanFin (fun r => T r - w.source.capture n) - w.target n) ^ 2) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hlat : ∀ r, w.latency plays r n = some (T r - w.source.capture n) := fun r => by
    simp [World.latency, hT r]
  have htrk : ∀ r : Fin R, w.trackingAt plays r n
      = ENNReal.ofReal (((T r - w.source.capture n) - w.target n) ^ 2) := fun r => by
    simp [World.trackingAt, hlat r]
  have hvar0 : 0 ≤ varFin (fun r => T r - w.source.capture n) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hRpos.le
  unfold World.trackingCost
  rw [Finset.sum_congr rfl fun r _ => htrk r,
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  have hinv : (R : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((R : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hRpos, ENNReal.ofReal_natCast]
  rw [hinv, ← ENNReal.ofReal_mul (inv_nonneg.mpr hRpos.le), inv_mul_eq_div,
    modal_sq_sub_target hR (fun r => T r - w.source.capture n) (w.target n),
    ENNReal.ofReal_add hvar0 (sq_nonneg _), w.syncCost_eq_var plays hR n hT]

/-- **Exact modal split of the specification's quadratic frame objectives.**
For any `Weights` `c`, the weighted synchronization and tracking cost at frame
`n` splits into differential-mode variance weighted by `c.sync + c.tracking`,
plus squared common-mode tracking error weighted by `c.tracking` alone. In
low-latency mode (`c.tracking = 0`), the common mode carries zero quadratic
position weight. -/
theorem World.weighted_frame_modal_split (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) (hR : 0 < R) (n : ℕ) {T : Fin R → Time}
    (hT : ∀ r, w.playTime plays r n = some (T r)) :
    (c.sync : ℝ≥0∞) * w.syncCost plays n + (c.tracking : ℝ≥0∞) * w.trackingCost plays n
      = ENNReal.ofReal (((c.sync : ℝ) + (c.tracking : ℝ))
            * varFin (fun r => T r - w.source.capture n)
          + (c.tracking : ℝ)
            * (meanFin (fun r => T r - w.source.capture n) - w.target n) ^ 2) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hvar0 : 0 ≤ varFin (fun r => T r - w.source.capture n) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hRpos.le
  rw [w.trackingCost_eq_sync_add_mean plays hR n hT, w.syncCost_eq_var plays hR n hT, mul_add]
  have hcs : (c.sync : ℝ≥0∞) = ENNReal.ofReal (c.sync : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  have hct : (c.tracking : ℝ≥0∞) = ENNReal.ofReal (c.tracking : ℝ) :=
    (ENNReal.ofReal_coe_nnreal).symm
  rw [hcs, hct, ← ENNReal.ofReal_mul c.sync.coe_nonneg,
    ← ENNReal.ofReal_mul c.tracking.coe_nonneg,
    ← ENNReal.ofReal_mul c.tracking.coe_nonneg,
    ← add_assoc,
    ← ENNReal.ofReal_add (mul_nonneg c.sync.coe_nonneg hvar0)
      (mul_nonneg c.tracking.coe_nonneg hvar0),
    ← ENNReal.ofReal_add
      (add_nonneg (mul_nonneg c.sync.coe_nonneg hvar0) (mul_nonneg c.tracking.coe_nonneg hvar0))
      (mul_nonneg c.tracking.coe_nonneg (sq_nonneg _))]
  congr 1
  ring

/-! ## Per-cycle ramp roughness and weight conversion -/

/-- When playback is continuous at output sample `k + 1`, the next continuous
step after `k` is `k + 1`. -/
theorem nextContinuous_succ (p : ℕ → Option ℝ) (k : ℕ) (hc : PlaysContinuously p (k + 1)) :
    nextContinuous p k = some (k + 1) := by
  classical
  unfold nextContinuous
  have hex : ∃ j, k < j ∧ PlaysContinuously p j := ⟨k + 1, Nat.lt_succ_self k, hc⟩
  rw [dite_eq_left hex, Option.some.injEq]
  exact le_antisymm (Nat.find_min' hex ⟨Nat.lt_succ_self k, hc⟩)
    (Nat.succ_le_of_lt (Nat.find_spec hex).1)

/-- **Linear-ramp roughness over a cycle of `M` uniformly spaced samples.**
When speaker `r`'s output samples leave uniformly at nominal rate `ρ > 0`
(`out (k₀ + j) = t₀ + j / ρ`) and playback speed ramps linearly by `Δv` across
`M > 0` continuous sample steps, the sum of `World.roughnessCost` over the `M`
steps equals `ρ * Δv² / M`. Writing `Δt = M / ρ` for the cycle duration and
`Δv = w_cyc / M` for a pace change of `w_cyc` frames per cycle, this equals
`w_cyc² / (ρ² * Δt³)`. -/
theorem World.roughness_linear_ramp (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (r : Fin R) (k₀ M : ℕ) (hM : 0 < M) {ρ : ℝ} (hρ : 0 < ρ) (t₀ v₀ Δv : ℝ)
    (hout : ∀ j ≤ M + 1, (w.speaker r).out (k₀ + j) = t₀ + (j : ℝ) / ρ)
    (hcont : ∀ j ≤ M, PlaysContinuously (plays r) (k₀ + j))
    (hspd : ∀ j ≤ M, w.speed plays r (k₀ + j) = some (v₀ + (j : ℝ) / (M : ℝ) * Δv)) :
    ∑ j ∈ Finset.range M, w.roughnessCost plays r (k₀ + j)
      = ENNReal.ofReal (ρ * Δv ^ 2 / (M : ℝ)) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hterm : ∀ j ∈ Finset.range M,
      w.roughnessCost plays r (k₀ + j) = ENNReal.ofReal (ρ * Δv ^ 2 / (M : ℝ) ^ 2) := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    unfold World.roughnessCost
    rw [hspd j hjM.le, nextContinuous_succ (plays r) (k₀ + j)
      (by simpa [Nat.add_assoc] using hcont (j + 1) hjM)]
    dsimp only
    have hspd' : w.speed plays r (k₀ + j + 1)
        = some (v₀ + ((j + 1 : ℕ) : ℝ) / (M : ℝ) * Δv) := by
      simpa [Nat.add_assoc] using hspd (j + 1) hjM
    rw [hspd']
    dsimp only
    have ho0 : (w.speaker r).out (k₀ + j) = t₀ + (j : ℝ) / ρ := hout j (by omega)
    have ho1 : (w.speaker r).out (k₀ + j + 1) = t₀ + ((j + 1 : ℕ) : ℝ) / ρ := by
      simpa [Nat.add_assoc] using hout (j + 1) (by omega)
    have ho2 : (w.speaker r).out (k₀ + j + 1 + 1) = t₀ + ((j + 2 : ℕ) : ℝ) / ρ := by
      simpa [Nat.add_assoc] using hout (j + 2) (by omega)
    rw [ho0, ho1, ho2]
    congr 1
    push_cast
    have hρne : ρ ≠ 0 := hρ.ne'
    have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
  congr 1
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  field_simp

/-- **Boundary-step roughness over a cycle of `M` uniformly spaced samples.**
Holding playback speed constant at `v₀` across `M` samples and stepping by `Δv`
at the cycle boundary incurs `World.roughnessCost` equal to `ρ * Δv²` —
`M = ρ * Δt` times larger than a linear speed ramp across the cycle. -/
theorem World.roughness_boundary_step (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (r : Fin R) (k₀ M : ℕ) (hM : 0 < M) {ρ : ℝ} (hρ : 0 < ρ) (t₀ v₀ Δv : ℝ)
    (hout : ∀ j ≤ M + 1, (w.speaker r).out (k₀ + j) = t₀ + (j : ℝ) / ρ)
    (hcont : ∀ j ≤ M, PlaysContinuously (plays r) (k₀ + j))
    (hspd_pre : ∀ j < M, w.speed plays r (k₀ + j) = some v₀)
    (hspd_end : w.speed plays r (k₀ + M) = some (v₀ + Δv)) :
    ∑ j ∈ Finset.range M, w.roughnessCost plays r (k₀ + j)
      = ENNReal.ofReal (ρ * Δv ^ 2) := by
  have hsplit : Finset.range M = insert (M - 1) (Finset.range (M - 1)) := by
    have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel hM
    conv_lhs => rw [← hM1, Finset.range_add_one]
  rw [hsplit, Finset.sum_insert (Finset.notMem_range_self)]
  have hzero : ∑ j ∈ Finset.range (M - 1), w.roughnessCost plays r (k₀ + j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj1 : j + 1 < M := by
      have := Finset.mem_range.mp hj
      omega
    unfold World.roughnessCost
    rw [hspd_pre j (by omega),
      nextContinuous_succ (plays r) (k₀ + j)
        (by simpa [Nat.add_assoc] using hcont (j + 1) (by omega))]
    dsimp only
    rw [show w.speed plays r (k₀ + j + 1) = some v₀ by
        simpa [Nat.add_assoc] using hspd_pre (j + 1) hj1]
    simp
  rw [hzero, add_zero]
  unfold World.roughnessCost
  have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel hM
  rw [hspd_pre (M - 1) (by omega),
    nextContinuous_succ (plays r) (k₀ + (M - 1))
      (by simpa [Nat.add_assoc, hM1] using hcont M le_rfl)]
  dsimp only
  rw [show w.speed plays r (k₀ + (M - 1) + 1) = some (v₀ + Δv) by
      simpa [Nat.add_assoc, hM1] using hspd_end]
  dsimp only
  have ho0 : (w.speaker r).out (k₀ + (M - 1)) = t₀ + ((M - 1 : ℕ) : ℝ) / ρ := hout (M - 1) (by omega)
  have ho1 : (w.speaker r).out (k₀ + (M - 1) + 1) = t₀ + (M : ℝ) / ρ := by
    simpa [Nat.add_assoc, hM1] using hout M (by omega)
  have ho2 : (w.speaker r).out (k₀ + (M - 1) + 1 + 1) = t₀ + ((M + 1 : ℕ) : ℝ) / ρ := by
    simpa [Nat.add_assoc, hM1] using hout (M + 1) le_rfl
  rw [ho0, ho1, ho2]
  congr 1
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub hM, Nat.cast_one]
  rw [hcast]
  push_cast
  have hρne : ρ ≠ 0 := hρ.ne'
  field_simp
  ring

/-- **Exact conversion between specification weights and per-cycle weights.**
Under a linear speed ramp over a cycle of duration `Δt = M / ρ` (at nominal
rate `ρ > 0`), a position error of `e` frames (`e / ρ` seconds) held for `Δt`
seconds plus a pace change of `w_cyc` frames per cycle has weighted cost
proportional to `((c_pos / c_rough) * Δt⁴) * e² + w_cyc²`. Thus the per-cycle
position weight is `(c_pos / c_rough) * Δt⁴`, not `c_pos / c_rough`. -/
theorem cyclePositionWeight_eq {c_pos c_rough ρ Δt : ℝ}
    (hcR : c_rough ≠ 0) (hρ : ρ ≠ 0) (hΔt : Δt ≠ 0) (e w_cyc : ℝ) :
    c_pos * (e / ρ) ^ 2 * Δt + c_rough * (w_cyc ^ 2 / (ρ ^ 2 * Δt ^ 3))
      = c_rough / (ρ ^ 2 * Δt ^ 3) * (((c_pos / c_rough) * Δt ^ 4) * e ^ 2 + w_cyc ^ 2) := by
  field_simp

/-! ## Host-time shift transformation -/

/-- Shifting every host `h`'s true timeline by `Δ h` (with `Δ w.sender = 0`):
host `h`'s clock reads `(w.clock h).read (t - Δ h)`, speaker `r`'s device
events shift by `+ Δ (w.host r)`, and a message sent from `i` to `j` at true
time `t` arrives shifted by `+ Δ j` relative to `t - Δ i`, preserving all
round-trip times while shifting link `(i, j)`'s one-way delay by `Δ j - Δ i`. -/
def World.shiftHosts (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j) : World H R where
  rate := w.rate
  rate_pos := w.rate_pos
  sender := w.sender
  host := w.host
  hosts := w.hosts
  clock h :=
    { read := fun t => (w.clock h).read (t - Δ h)
      strictMono := fun _ _ hlt => (w.clock h).strictMono (by linarith)
      continuous := (w.clock h).continuous.comp (continuous_id.sub continuous_const) }
  source := w.source
  speaker r :=
    { out := fun k => (w.speaker r).out k + Δ (w.host r)
      out_strictMono := fun _ _ hlt => by linarith [(w.speaker r).out_strictMono hlt]
      first := (w.speaker r).first
      first_zero := (w.speaker r).first_zero
      first_strictMono := (w.speaker r).first_strictMono
      asked := fun b => (w.speaker r).asked b + Δ (w.host r)
      asked_strictMono := fun _ _ hlt => by linarith [(w.speaker r).asked_strictMono hlt]
      asked_before := fun b => by linarith [(w.speaker r).asked_before b]
      reported := (w.speaker r).reported }
  network :=
    { deliver := fun i j t q => (w.network.deliver i j (t - Δ i) q).map (· + Δ j)
      after := fun i j t q a h => by
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨a₀, ha₀, rfl⟩ := h
        have := hnet i j (t - Δ i) q a₀ ha₀
        linarith }
  target := w.target

/-- Shifting hosts leaves every round-trip time unchanged: if a query leaves `i`
at `t₁`, reaches `j` at `t₂`, and its reply reaches `i` at `t₄`, the shifted
round-trip time equals the original round-trip time. -/
theorem World.shiftHosts_rtt_eq (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    {i j : H} {s₁ s₂ s₄ : Time} {q₁ q₂ : ℕ}
    (h1 : w.network.deliver i j s₁ q₁ = some s₂)
    (h2 : w.network.deliver j i s₂ q₂ = some s₄) :
    (w.shiftHosts Δ hnet).network.deliver i j (s₁ + Δ i) q₁ = some (s₂ + Δ j)
      ∧ (w.shiftHosts Δ hnet).network.deliver j i (s₂ + Δ j) q₂ = some (s₄ + Δ i)
      ∧ (s₄ + Δ i) - (s₁ + Δ i) = s₄ - s₁ := by
  refine ⟨?_, ?_, by ring⟩
  · simp [World.shiftHosts, h1]
  · simp [World.shiftHosts, h2]

/-- Under a host shift `Δ`, an identical play sequence `plays` shifts speaker
`r`'s true play time of frame `n` by `+ Δ (w.host r)`. -/
theorem World.playTime_shiftHosts (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (plays : Fin R → ℕ → Option ℝ) (r : Fin R) (n : ℕ) :
    (w.shiftHosts Δ hnet).playTime plays r n
      = (w.playTime plays r n).map (· + Δ (w.host r)) := by
  classical
  unfold World.playTime Unisono.Spec.playTime
  split_ifs with h
  · cases hx : plays r (Nat.find h) <;> cases hy : plays r (Nat.find h + 1) <;> simp
    simp only [World.shiftHosts]
    ring
  · simp

/-- Under a host shift `Δ`, an identical play sequence `plays` shifts speaker
`r`'s latency of frame `n` by `+ Δ (w.host r)`. -/
theorem World.latency_shiftHosts (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (plays : Fin R → ℕ → Option ℝ) (r : Fin R) (n : ℕ) :
    (w.shiftHosts Δ hnet).latency plays r n
      = (w.latency plays r n).map (· + Δ (w.host r)) := by
  rw [World.latency, World.latency, w.playTime_shiftHosts Δ hnet plays r n]
  have hsrc : (w.shiftHosts Δ hnet).source = w.source := rfl
  rw [hsrc]
  cases w.playTime plays r n with
  | none => rfl
  | some t =>
      simp only [Option.map_some, Option.some.injEq]
      ring

/-- **Parallelogram lower bound on synchronization under opposite shifts.**
If the same playback `plays` runs in `w⁺ = w.shiftHosts Δ` and
`w⁻ = w.shiftHosts (-Δ)` and every speaker plays frame `n`, then the sum of
their synchronization costs at frame `n` is at least
`2 * varFin (fun r => Δ (w.host r))`. -/
theorem World.syncCost_shiftHosts_add_ge (w : World H R) (Δ : H → ℝ)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (plays : Fin R → ℕ → Option ℝ) (hR : 0 < R) (n : ℕ)
    (hplay : ∀ r, (w.playTime plays r n).isSome) :
    ENNReal.ofReal (2 * varFin (fun r => Δ (w.host r)))
      ≤ (w.shiftHosts Δ hnet₁).syncCost plays n
        + (w.shiftHosts (-Δ) hnet₂).syncCost plays n := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  choose T hT using fun r => Option.isSome_iff_exists.mp (hplay r)
  have hT₁ : ∀ r, (w.shiftHosts Δ hnet₁).playTime plays r n = some (T r + Δ (w.host r)) :=
    fun r => by rw [w.playTime_shiftHosts Δ hnet₁ plays r n, hT r]; rfl
  have hT₂ : ∀ r, (w.shiftHosts (-Δ) hnet₂).playTime plays r n = some (T r - Δ (w.host r)) :=
    fun r => by
      rw [w.playTime_shiftHosts (-Δ) hnet₂ plays r n, hT r]
      simp [sub_eq_add_neg]
  rw [World.syncCost_eq_var _ plays hR n hT₁, World.syncCost_eq_var _ plays hR n hT₂]
  have hnonneg : ∀ f : Fin R → ℝ, 0 ≤ varFin f := fun f =>
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hRpos.le
  rw [← ENNReal.ofReal_add (hnonneg _) (hnonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hsrc₁ : (w.shiftHosts Δ hnet₁).source = w.source := rfl
  have hsrc₂ : (w.shiftHosts (-Δ) hnet₂).source = w.source := rfl
  rw [hsrc₁, hsrc₂]
  set a : Fin R → ℝ := fun r => T r - w.source.capture n
  set b : Fin R → ℝ := fun r => Δ (w.host r)
  have hm₁ : meanFin (fun r => T r + Δ (w.host r) - w.source.capture n)
      = meanFin a + meanFin b := by
    unfold meanFin
    have : ∀ r, T r + Δ (w.host r) - w.source.capture n = a r + b r := fun r => by ring
    simp only [this, Finset.sum_add_distrib, add_div]
  have hm₂ : meanFin (fun r => T r - Δ (w.host r) - w.source.capture n)
      = meanFin a - meanFin b := by
    unfold meanFin
    have : ∀ r, T r - Δ (w.host r) - w.source.capture n = a r - b r := fun r => by ring
    simp only [this, Finset.sum_sub_distrib, sub_div]
  have hpara :
      varFin (fun r => T r + Δ (w.host r) - w.source.capture n)
        + varFin (fun r => T r - Δ (w.host r) - w.source.capture n)
      = 2 * varFin a + 2 * varFin b := by
    unfold varFin
    rw [hm₁, hm₂, ← add_div, ← Finset.sum_add_distrib]
    have hpt : ∀ r : Fin R,
        (T r + Δ (w.host r) - w.source.capture n - (meanFin a + meanFin b)) ^ 2
          + (T r - Δ (w.host r) - w.source.capture n - (meanFin a - meanFin b)) ^ 2
        = 2 * (a r - meanFin a) ^ 2 + 2 * (b r - meanFin b) ^ 2 := fun r => by
      simp only [a, b]; ring
    simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpara]
  linarith [hnonneg a]

/-- **Parallelogram lower bound on tracking under opposite uniform shifts.**
If the same playback `plays` runs in `w⁺` and `w⁻` with shift `± A` on every
speaker host and every speaker plays frame `n`, then the sum of their tracking
costs at frame `n` is at least `2 * A ^ 2`. -/
theorem World.trackingCost_shiftHosts_add_ge (w : World H R) (Δ : H → ℝ) (A : ℝ)
    (hΔ : ∀ r, Δ (w.host r) = A)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (plays : Fin R → ℕ → Option ℝ) (hR : 0 < R) (n : ℕ)
    (hplay : ∀ r, (w.playTime plays r n).isSome) :
    ENNReal.ofReal (2 * A ^ 2)
      ≤ (w.shiftHosts Δ hnet₁).trackingCost plays n
        + (w.shiftHosts (-Δ) hnet₂).trackingCost plays n := by
  choose T hT using fun r => Option.isSome_iff_exists.mp (hplay r)
  have hT₁ : ∀ r, (w.shiftHosts Δ hnet₁).playTime plays r n = some (T r + A) := fun r => by
    rw [w.playTime_shiftHosts Δ hnet₁ plays r n, hT r, hΔ r]; rfl
  have hT₂ : ∀ r, (w.shiftHosts (-Δ) hnet₂).playTime plays r n = some (T r - A) := fun r => by
    rw [w.playTime_shiftHosts (-Δ) hnet₂ plays r n, hT r]
    simp [hΔ r, sub_eq_add_neg]
  rw [World.trackingCost_eq_sync_add_mean _ plays hR n hT₁,
    World.trackingCost_eq_sync_add_mean _ plays hR n hT₂]
  have hsrc₁ : (w.shiftHosts Δ hnet₁).source = w.source := rfl
  have hsrc₂ : (w.shiftHosts (-Δ) hnet₂).source = w.source := rfl
  have htgt₁ : (w.shiftHosts Δ hnet₁).target = w.target := rfl
  have htgt₂ : (w.shiftHosts (-Δ) hnet₂).target = w.target := rfl
  rw [hsrc₁, hsrc₂, htgt₁, htgt₂]
  have hm₁ : meanFin (fun r => T r + A - w.source.capture n)
      = meanFin (fun r => T r - w.source.capture n) + A := by
    unfold meanFin
    have : ∀ r, T r + A - w.source.capture n = (T r - w.source.capture n) + A := fun r => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  have hm₂ : meanFin (fun r => T r - A - w.source.capture n)
      = meanFin (fun r => T r - w.source.capture n) - A := by
    unfold meanFin
    have : ∀ r, T r - A - w.source.capture n = (T r - w.source.capture n) - A := fun r => by ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  rw [hm₁, hm₂]
  have hpara :
      ENNReal.ofReal (2 * A ^ 2)
        ≤ ENNReal.ofReal ((meanFin (fun r => T r - w.source.capture n) + A - w.target n) ^ 2)
          + ENNReal.ofReal ((meanFin (fun r => T r - w.source.capture n) - A - w.target n) ^ 2) := by
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (meanFin (fun r => T r - w.source.capture n) - w.target n)]
  calc ENNReal.ofReal (2 * A ^ 2)
      ≤ ENNReal.ofReal ((meanFin (fun r => T r - w.source.capture n) + A - w.target n) ^ 2)
          + ENNReal.ofReal ((meanFin (fun r => T r - w.source.capture n) - A - w.target n) ^ 2) :=
        hpara
    _ ≤ _ := by
      gcongr <;> exact le_add_self

/-- Subadditivity of `Filter.limsup` in `ℝ≥0∞` along `atTop`. -/
theorem ennreal_limsup_add_le (u v : Time → ℝ≥0∞) :
    Filter.limsup (fun T => u T + v T) atTop
      ≤ Filter.limsup u atTop + Filter.limsup v atTop := by
  by_cases hu : Filter.limsup u atTop = ⊤
  · simp [hu]
  by_cases hv : Filter.limsup v atTop = ⊤
  · simp [hv]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hhalf : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by simp)
  have hu' : Filter.limsup u atTop < Filter.limsup u atTop + (ε : ℝ≥0∞) / 2 :=
    ENNReal.lt_add_right hu hhalf.ne'
  have hv' : Filter.limsup v atTop < Filter.limsup v atTop + (ε : ℝ≥0∞) / 2 :=
    ENNReal.lt_add_right hv hhalf.ne'
  have hev_u : ∀ᶠ T in atTop, u T < Filter.limsup u atTop + (ε : ℝ≥0∞) / 2 :=
    eventually_lt_of_limsup_lt hu'
  have hev_v : ∀ᶠ T in atTop, v T < Filter.limsup v atTop + (ε : ℝ≥0∞) / 2 :=
    eventually_lt_of_limsup_lt hv'
  have hle : Filter.limsup (fun T => u T + v T) atTop
      ≤ (Filter.limsup u atTop + (ε : ℝ≥0∞) / 2)
        + (Filter.limsup v atTop + (ε : ℝ≥0∞) / 2) := by
    apply Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop (x := 0) (fun _ => zero_le))
    filter_upwards [hev_u, hev_v] with T h1 h2
    exact add_le_add h1.le h2.le
  have hsum : (Filter.limsup u atTop + (ε : ℝ≥0∞) / 2)
      + (Filter.limsup v atTop + (ε : ℝ≥0∞) / 2)
      = Filter.limsup u atTop + Filter.limsup v atTop + (ε : ℝ≥0∞) := by
    calc (Filter.limsup u atTop + (ε : ℝ≥0∞) / 2) + (Filter.limsup v atTop + (ε : ℝ≥0∞) / 2)
        = Filter.limsup u atTop + Filter.limsup v atTop
          + ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) := by ring
      _ = Filter.limsup u atTop + Filter.limsup v atTop + (ε : ℝ≥0∞) := by
          rw [ENNReal.add_halves]
  rwa [hsum] at hle

/-- **Long-run lower bound from a per-frame lower bound.** If `f₁ n + f₂ n ≥ B`
for every frame `n ≥ N`, and frame capture times grow without bound, then
`longRun (accruedFrames f₁) + longRun (accruedFrames f₂) ≥ B`. -/
theorem World.longRun_accruedFrames_add_ge (w : World H R) (f₁ f₂ : ℕ → ℝ≥0∞) {B : ℝ≥0∞}
    (N : ℕ) (hB : ∀ n, N ≤ n → B ≤ f₁ n + f₂ n)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    B ≤ longRun (w.accruedFrames f₁) + longRun (w.accruedFrames f₂) := by
  by_cases hB0 : B = 0
  · simp [hB0]
  have hsum_acc : ∀ T : Time,
      B * ENNReal.ofReal (T - w.source.capture N)
        ≤ w.accruedFrames f₁ T + w.accruedFrames f₂ T := by
    intro T
    by_cases hTN : T ≤ w.source.capture N
    · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr hTN), mul_zero]
      exact zero_le
    · push Not at hTN
      classical
      let m := Nat.find (hunb T)
      have hm_ge : T ≤ w.source.capture m := Nat.find_spec (hunb T)
      have hNm : N ≤ m := by
        by_contra hlt
        push Not at hlt
        linarith [w.source.capture_strictMono hlt]
      have hlt_T : ∀ n ∈ Finset.Ico N m, w.source.capture n < T := by
        intro n hn
        rw [Finset.mem_Ico] at hn
        by_contra hge
        push Not at hge
        exact absurd (Nat.find_min' (hunb T) hge) (not_le.mpr hn.2)
      have htele_real : ∀ k, N ≤ k →
          ∑ n ∈ Finset.Ico N k, (w.source.capture (n + 1) - w.source.capture n)
            = w.source.capture k - w.source.capture N := by
        intro k hNk
        induction k, hNk using Nat.le_induction with
        | base => simp
        | succ k hNk ih =>
          rw [Finset.sum_Ico_succ_top hNk, ih]
          ring
      have htele : ∑ n ∈ Finset.Ico N m,
          ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
          = ENNReal.ofReal (w.source.capture m - w.source.capture N) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ =>
          sub_nonneg.mpr (w.source.capture_strictMono (Nat.lt_succ_self n)).le),
          htele_real m hNm]
      have hstep : ∀ n ∈ Finset.Ico N m,
          B * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n)
            ≤ (if w.source.capture n < T then
                f₁ n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
              + (if w.source.capture n < T then
                f₂ n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0) := by
        intro n hn
        rw [ite_eq_left (hlt_T n hn), ite_eq_left (hlt_T n hn), ← add_mul]
        exact mul_le_mul_left (hB n (Finset.mem_Ico.mp hn).1) _
      calc B * ENNReal.ofReal (T - w.source.capture N)
          ≤ B * ENNReal.ofReal (w.source.capture m - w.source.capture N) := by
            gcongr
        _ = B * ∑ n ∈ Finset.Ico N m,
              ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) := by
            rw [htele]
        _ = ∑ n ∈ Finset.Ico N m,
              B * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ n ∈ Finset.Ico N m,
              ((if w.source.capture n < T then
                f₁ n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
              + (if w.source.capture n < T then
                f₂ n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)) :=
            Finset.sum_le_sum hstep
        _ = (∑ n ∈ Finset.Ico N m, if w.source.capture n < T then
              f₁ n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0)
            + (∑ n ∈ Finset.Ico N m, if w.source.capture n < T then
              f₂ n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n) else 0) :=
            Finset.sum_add_distrib
        _ ≤ w.accruedFrames f₁ T + w.accruedFrames f₂ T :=
            add_le_add (sum_le_tsum _) (sum_le_tsum _)
  have hlim_ratio :
      Tendsto (fun T : Time => B * ENNReal.ofReal (T - w.source.capture N) / ENNReal.ofReal T)
        atTop (nhds B) := by
    by_cases hBtop : B = ⊤
    · subst hBtop
      refine ENNReal.tendsto_nhds_top_iff_nnreal.mpr fun r => ?_
      filter_upwards [eventually_gt_atTop (max 1 (2 * w.source.capture N))] with T hT
      have hsub : 0 < T - w.source.capture N := by
        have h1 : (1 : ℝ) < T := lt_of_le_of_lt (le_max_left _ _) hT
        have h2 : 2 * w.source.capture N < T := lt_of_le_of_lt (le_max_right _ _) hT
        linarith
      have hpos : ENNReal.ofReal (T - w.source.capture N) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hsub).ne'
      rw [ENNReal.top_mul hpos, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
      exact ENNReal.coe_lt_top
    · have hreal : Tendsto (fun T : Time => (T - w.source.capture N) / T) atTop (nhds 1) := by
        have heq : ∀ᶠ T : Time in atTop,
            (T - w.source.capture N) / T = 1 - w.source.capture N / T := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
          field_simp
        rw [tendsto_congr' heq]
        have hzero : Tendsto (fun T : Time => w.source.capture N / T) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        simpa using tendsto_const_nhds.sub hzero
      have henn : Tendsto
          (fun T : Time => ENNReal.ofReal (T - w.source.capture N) / ENNReal.ofReal T)
          atTop (nhds 1) := by
        have heq : ∀ᶠ T : Time in atTop,
            ENNReal.ofReal (T - w.source.capture N) / ENNReal.ofReal T
              = ENNReal.ofReal ((T - w.source.capture N) / T) := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
          rw [ENNReal.ofReal_div_of_pos hT]
        rw [tendsto_congr' heq]
        have hcomp : Tendsto (fun T : Time => ENNReal.ofReal ((T - w.source.capture N) / T))
            atTop (nhds (ENNReal.ofReal 1)) :=
          (ENNReal.continuous_ofReal.tendsto 1).comp hreal
        simpa using hcomp
      have hmul : Tendsto
          (fun T : Time => B * (ENNReal.ofReal (T - w.source.capture N) / ENNReal.ofReal T))
          atTop (nhds B) := by
        simpa using ENNReal.Tendsto.const_mul henn (Or.inr hBtop)
      refine hmul.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T _
      rw [mul_div_assoc]
  have hle_lim :
      Filter.limsup (fun T : Time =>
          B * ENNReal.ofReal (T - w.source.capture N) / ENNReal.ofReal T) atTop
        ≤ Filter.limsup (fun T : Time =>
            w.accruedFrames f₁ T / ENNReal.ofReal T
              + w.accruedFrames f₂ T / ENNReal.ofReal T) atTop := by
    apply Filter.limsup_le_limsup
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T _
      rw [← ENNReal.add_div]
      exact ENNReal.div_le_div_right (hsum_acc T) _
    · exact isCoboundedUnder_le_of_le atTop (x := 0) (fun _ => zero_le)
    · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
  rw [hlim_ratio.limsup_eq] at hle_lim
  exact hle_lim.trans (ennreal_limsup_add_le _ _)

/-- **Long-run synchronization lower bound for identical playbacks under
opposite host shifts.** If `plays` runs identically in `w⁺ = w.shiftHosts Δ`
and `w⁻ = w.shiftHosts (-Δ)` and plays every frame from some `N` on (with
unbounded capture times), then at least one of the two worlds suffers
long-run synchronization cost at least `varFin (fun r => Δ (w.host r))`. -/
theorem World.sync_shiftHosts_max_ge (w : World H R) (Δ : H → ℝ)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (plays : Fin R → ℕ → Option ℝ) (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime plays r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (varFin fun r => Δ (w.host r))
      ≤ max ((w.shiftHosts Δ hnet₁).sync plays) ((w.shiftHosts (-Δ) hnet₂).sync plays) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hvar0 : 0 ≤ varFin (fun r => Δ (w.host r)) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hRpos.le
  have hadd : ENNReal.ofReal (2 * varFin fun r => Δ (w.host r))
      ≤ (w.shiftHosts Δ hnet₁).sync plays + (w.shiftHosts (-Δ) hnet₂).sync plays := by
    unfold World.sync
    have heq₁ : (w.shiftHosts Δ hnet₁).accruedFrames ((w.shiftHosts Δ hnet₁).syncCost plays)
        = w.accruedFrames ((w.shiftHosts Δ hnet₁).syncCost plays) := rfl
    have heq₂ : (w.shiftHosts (-Δ) hnet₂).accruedFrames ((w.shiftHosts (-Δ) hnet₂).syncCost plays)
        = w.accruedFrames ((w.shiftHosts (-Δ) hnet₂).syncCost plays) := rfl
    rw [heq₁, heq₂]
    exact w.longRun_accruedFrames_add_ge _ _ N
      (fun n hn => w.syncCost_shiftHosts_add_ge Δ hnet₁ hnet₂ plays hR n (hplay n hn)) hunb
  have htwo : ENNReal.ofReal (2 * varFin fun r => Δ (w.host r))
      = ENNReal.ofReal (varFin fun r => Δ (w.host r))
        + ENNReal.ofReal (varFin fun r => Δ (w.host r)) := by
    rw [two_mul, ENNReal.ofReal_add hvar0 hvar0]
  rw [htwo] at hadd
  set M := max ((w.shiftHosts Δ hnet₁).sync plays) ((w.shiftHosts (-Δ) hnet₂).sync plays)
  have hM : (w.shiftHosts Δ hnet₁).sync plays + (w.shiftHosts (-Δ) hnet₂).sync plays ≤ M + M :=
    add_le_add (le_max_left _ _) (le_max_right _ _)
  have hle : ENNReal.ofReal (varFin fun r => Δ (w.host r))
      + ENNReal.ofReal (varFin fun r => Δ (w.host r)) ≤ M + M := hadd.trans hM
  by_contra hlt
  push Not at hlt
  have hstrict : M + M < ENNReal.ofReal (varFin fun r => Δ (w.host r))
      + ENNReal.ofReal (varFin fun r => Δ (w.host r)) :=
    ENNReal.add_lt_add hlt hlt
  exact not_lt_of_ge hle hstrict

/-- **Long-run tracking lower bound under opposite uniform shifts.** -/
theorem World.tracking_shiftHosts_max_ge (w : World H R) (Δ : H → ℝ) (A : ℝ)
    (hΔ : ∀ r, Δ (w.host r) = A)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (plays : Fin R → ℕ → Option ℝ) (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime plays r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (A ^ 2)
      ≤ max ((w.shiftHosts Δ hnet₁).tracking plays) ((w.shiftHosts (-Δ) hnet₂).tracking plays) := by
  have hadd : ENNReal.ofReal (2 * A ^ 2)
      ≤ (w.shiftHosts Δ hnet₁).tracking plays + (w.shiftHosts (-Δ) hnet₂).tracking plays := by
    unfold World.tracking
    have heq₁ : (w.shiftHosts Δ hnet₁).accruedFrames ((w.shiftHosts Δ hnet₁).trackingCost plays)
        = w.accruedFrames ((w.shiftHosts Δ hnet₁).trackingCost plays) := rfl
    have heq₂ : (w.shiftHosts (-Δ) hnet₂).accruedFrames ((w.shiftHosts (-Δ) hnet₂).trackingCost plays)
        = w.accruedFrames ((w.shiftHosts (-Δ) hnet₂).trackingCost plays) := rfl
    rw [heq₁, heq₂]
    exact w.longRun_accruedFrames_add_ge _ _ N
      (fun n hn => w.trackingCost_shiftHosts_add_ge Δ A hΔ hnet₁ hnet₂ plays hR n (hplay n hn)) hunb
  have htwo : ENNReal.ofReal (2 * A ^ 2) = ENNReal.ofReal (A ^ 2) + ENNReal.ofReal (A ^ 2) := by
    rw [two_mul, ENNReal.ofReal_add (sq_nonneg A) (sq_nonneg A)]
  rw [htwo] at hadd
  set M := max ((w.shiftHosts Δ hnet₁).tracking plays) ((w.shiftHosts (-Δ) hnet₂).tracking plays)
  have hM : (w.shiftHosts Δ hnet₁).tracking plays + (w.shiftHosts (-Δ) hnet₂).tracking plays
      ≤ M + M := add_le_add (le_max_left _ _) (le_max_right _ _)
  have hle : ENNReal.ofReal (A ^ 2) + ENNReal.ofReal (A ^ 2) ≤ M + M := hadd.trans hM
  by_contra hlt
  push Not at hlt
  have hstrict : M + M < ENNReal.ofReal (A ^ 2) + ENNReal.ofReal (A ^ 2) :=
    ENNReal.add_lt_add hlt hlt
  exact not_lt_of_ge hle hstrict

/-! ## Step-by-step indistinguishability under host shifts -/

/-- A clock shift `t ↦ C(t - d)` shifts `Clock.timeAt c` by `+ d`. -/
theorem Clock.timeAt_shift (C : Clock) (d c : ℝ) :
    ({ read := fun t => C.read (t - d)
       strictMono := fun _ _ h => C.strictMono (by linarith)
       continuous := C.continuous.comp (continuous_id.sub continuous_const) } : Clock).timeAt c
      = (C.timeAt c).map (· + d) := by
  classical
  unfold Clock.timeAt
  by_cases h1 : ∃ t, C.read (t - d) = c
  · have h2 : ∃ t, C.read t = c := by obtain ⟨t, ht⟩ := h1; exact ⟨t - d, ht⟩
    rw [dite_eq_left h1, dite_eq_left h2, Option.map_some, Option.some.injEq]
    have hc1 : C.read (Classical.choose h1 - d) = c := Classical.choose_spec h1
    have hc2 : C.read (Classical.choose h2) = c := Classical.choose_spec h2
    have heq := C.strictMono.injective (hc1.trans hc2.symm)
    linarith
  · have h2 : ¬ ∃ t, C.read t = c := by
      rintro ⟨t, ht⟩
      exact h1 ⟨t + d, by simpa using ht⟩
    rw [dite_eq_right h1, dite_eq_right h2, Option.map_none]

/-! ## Host-local causal invariance under host shifts (independent of cross-host interleavings) -/

/-- `earliest` selects an element of `l` whose `(time, rank)` key is
lexicographically least in `l`. -/
theorem earliest_spec_lex {α : Type} (key : α → Time × ℕ) :
    ∀ (l : List α) (a : α), earliest key l = some a →
      a ∈ l ∧ ∀ b ∈ l, (key a).1 < (key b).1 ∨ ((key a).1 = (key b).1 ∧ (key a).2 ≤ (key b).2)
  | [], a, h => by simp [earliest] at h
  | c :: l, a, h => by
      simp only [earliest] at h
      cases hl : earliest key l with
      | none =>
          simp only [hl, Option.some.injEq] at h
          subst h
          cases l with
          | nil => simp
          | cons d l' => exact absurd hl (earliest_ne_none key d l')
      | some b =>
          simp only [hl] at h
          obtain ⟨hb, hmin⟩ := earliest_spec_lex key l b hl
          split_ifs at h with hc
          · simp only [Option.some.injEq] at h
            subst h
            refine ⟨by simp, fun d hd => ?_⟩
            rcases List.mem_cons.mp hd with rfl | hd
            · exact Or.inr ⟨rfl, le_rfl⟩
            · rcases hc with hc1 | ⟨hc1, hc2⟩
              · rcases hmin d hd with hd1 | ⟨hd1, _⟩
                · exact Or.inl (lt_trans hc1 hd1)
                · exact Or.inl (hd1 ▸ hc1)
              · rcases hmin d hd with hd1 | ⟨hd1, hd2⟩
                · exact Or.inl (hc1.symm ▸ hd1)
                · exact Or.inr ⟨hc1.trans hd1, le_trans hc2 hd2⟩
          · simp only [Option.some.injEq] at h
            subst h
            have hbc : (key b).1 < (key c).1 ∨ ((key b).1 = (key c).1 ∧ (key b).2 ≤ (key c).2) := by
              rcases lt_trichotomy (key b).1 (key c).1 with hlt | heq | hgt
              · exact Or.inl hlt
              · refine Or.inr ⟨heq, ?_⟩
                by_contra hlt2
                exact hc (Or.inr ⟨heq.symm, Nat.le_of_lt (not_le.mp hlt2)⟩)
              · exact absurd (Or.inl hgt) hc
            refine ⟨List.mem_cons_of_mem _ hb, fun d hd => ?_⟩
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hbc
            · exact hmin d hd

/-- Frames held by a host determined solely from its local view. -/
def heldOfView (view : List (Event H R Msg)) : Finset ℕ :=
  view.foldl (fun acc e => acc ∪ e.observation.frames) ∅

theorem heldOfView_concat (l : List (Event H R Msg)) (e : Event H R Msg) :
    heldOfView (l ++ [e]) = heldOfView l ∪ e.observation.frames := by
  simp [heldOfView]

/-- Every host's held-frame set equals `heldOfView` of its current view. -/
theorem Solution.held_eq_heldOfView [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (lookahead : ℕ+) (n : ℕ) (h : H) :
    (σ.states v lookahead n).held h = heldOfView ((σ.states v lookahead n).views h) := by
  induction n with
  | zero => simp [Solution.states, State.start, heldOfView]
  | succ n ih =>
    have hstep : ∀ (st : State H R Msg) (h₀ : H) (t : Time) (obs : Observation H R Msg),
        st.held h = heldOfView (st.views h) →
        (st.handle σ v lookahead h₀ t obs).held h
          = heldOfView ((st.handle σ v lookahead h₀ t obs).views h) := by
      intro st h₀ t obs hinv
      rw [State.handle_held v st σ lookahead h₀ t obs h]
      have hv : (st.handle σ v lookahead h₀ t obs).views h
          = if h = h₀ then st.views h₀ ++ [⟨(v.clock h₀).read t, obs⟩] else st.views h := by
        simp only [State.handle, State.sendAll_views]
        split_ifs with hh
        · subst hh; simp
        · simp [hh]
      rw [hv]
      split_ifs with hh
      · subst hh; rw [heldOfView_concat, hinv]
      · exact hinv
    show ((σ.states v lookahead n).step σ v lookahead).held h
      = heldOfView (((σ.states v lookahead n).step σ v lookahead).views h)
    unfold State.step
    split
    · exact hstep _ _ _ _ ih
    · exact hstep _ _ _ _ ih
    · split
      · exact hstep _ _ _ _ ih
      · exact ih
    · split
      · exact hstep _ _ _ _ ih
      · exact ih
    · exact ih

/-- Process one send list at event time `s` on link `(i, h)` and collect all
messages delivered at arrival time `t`. -/
def sendListArrivals [DecidableEq H] (v : World H R) (i h : H) (t s : Time)
    (held : Finset ℕ) (q0 : ℕ) (sends : List (H × Msg × Finset ℕ)) :
    ℕ × List (Event H R Msg) :=
  sends.foldl
    (fun acc m =>
      if m.1 = h then
        let evs := match v.network.deliver i h s acc.1 with
          | some a =>
              if a = t then
                acc.2 ++ [⟨(v.clock h).read t, .received i m.2.1 (m.2.2.filter (· ∈ held))⟩]
              else acc.2
          | none => acc.2
        (acc.1 + 1, evs)
      else acc)
    (q0, [])

/-- Collect `(sentCount i h, arrivals at (h, t) from i)` purely from host `i`'s
local view. -/
def sentArrivalsAux [DecidableEq H] (σ : Solution H R Msg) (v : World H R) (i h : H) (t : Time) :
    List (Event H R Msg) → List (Event H R Msg) → ℕ → List (Event H R Msg) →
      ℕ × List (Event H R Msg)
  | _, [], q, evs => (q, evs)
  | pfx, e :: rest, q, evs =>
      let pfx' := pfx ++ [e]
      match (v.clock i).timeAt e.reading with
      | some s =>
          let res := sendListArrivals v i h t s (heldOfView pfx') q (σ i pfx').sends
          sentArrivalsAux σ v i h t pfx' rest res.1 (evs ++ res.2)
      | none =>
          sentArrivalsAux σ v i h t pfx' rest q evs

def sentArrivalsFromView [DecidableEq H] (σ : Solution H R Msg) (v : World H R) (i h : H) (t : Time)
    (view : List (Event H R Msg)) : ℕ × List (Event H R Msg) :=
  sentArrivalsAux σ v i h t [] view 0 []

private theorem sendListArrivals_nil_of_no_deliver [DecidableEq H] (v : World H R)
    (i h : H) (t s : Time) (held : Finset ℕ) (q0 : ℕ) (sends : List (H × Msg × Finset ℕ))
    (hno : ∀ q, v.network.deliver i h s q ≠ some t) :
    (sendListArrivals v i h t s held q0 sends).2 = [] := by
  unfold sendListArrivals
  suffices hgen : ∀ (q : ℕ) (evs : List (Event H R Msg)),
      (sends.foldl
        (fun acc m =>
          if m.1 = h then
            let evs := match v.network.deliver i h s acc.1 with
              | some a =>
                  if a = t then
                    acc.2 ++ [⟨(v.clock h).read t, .received i m.2.1 (m.2.2.filter (· ∈ held))⟩]
                  else acc.2
              | none => acc.2
            (acc.1 + 1, evs)
          else acc) (q, evs)).2 = evs from hgen q0 []
  induction sends with
  | nil => intro q evs; rfl
  | cons m rest ih =>
    intro q evs
    simp only [List.foldl_cons]
    split_ifs with hm
    · cases hd : v.network.deliver i h s q with
      | none => exact ih (q + 1) evs
      | some a =>
        have hne : a ≠ t := fun h => hno q (h ▸ hd)
        simp only [hne, ite_false]
        exact ih (q + 1) evs
    · exact ih q evs

private theorem sendListArrivals_shift [DecidableEq H] (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (i h : H) (t s : Time) (held : Finset ℕ) (q0 : ℕ) (sends : List (H × Msg × Finset ℕ)) :
    sendListArrivals (w.shiftHosts Δ hnet) i h (t + Δ h) (s + Δ i) held q0 sends
      = sendListArrivals w i h t s held q0 sends := by
  unfold sendListArrivals
  suffices hgen : ∀ (acc : ℕ × List (Event H R Msg)),
      sends.foldl
        (fun acc m =>
          if m.1 = h then
            let evs := match (w.shiftHosts Δ hnet).network.deliver i h (s + Δ i) acc.1 with
              | some a =>
                  if a = t + Δ h then
                    acc.2 ++ [⟨((w.shiftHosts Δ hnet).clock h).read (t + Δ h),
                      .received i m.2.1 (m.2.2.filter (· ∈ held))⟩]
                  else acc.2
              | none => acc.2
            (acc.1 + 1, evs)
          else acc) acc
      = sends.foldl
        (fun acc m =>
          if m.1 = h then
            let evs := match w.network.deliver i h s acc.1 with
              | some a =>
                  if a = t then
                    acc.2 ++ [⟨(w.clock h).read t,
                      .received i m.2.1 (m.2.2.filter (· ∈ held))⟩]
                  else acc.2
              | none => acc.2
            (acc.1 + 1, evs)
          else acc) acc by
    exact hgen (q0, [])
  induction sends with
  | nil => intro acc; rfl
  | cons m rest ih =>
    intro acc
    simp only [List.foldl_cons]
    have hstep :
        (if m.1 = h then
          let evs := match (w.shiftHosts Δ hnet).network.deliver i h (s + Δ i) acc.1 with
            | some a =>
                if a = t + Δ h then
                  acc.2 ++ [⟨((w.shiftHosts Δ hnet).clock h).read (t + Δ h),
                    .received i m.2.1 (m.2.2.filter (· ∈ held))⟩]
                else acc.2
            | none => acc.2
          (acc.1 + 1, evs)
        else acc)
        = (if m.1 = h then
          let evs := match w.network.deliver i h s acc.1 with
            | some a =>
                if a = t then
                  acc.2 ++ [⟨(w.clock h).read t,
                    .received i m.2.1 (m.2.2.filter (· ∈ held))⟩]
                else acc.2
            | none => acc.2
          (acc.1 + 1, evs)
        else acc) := by
      split_ifs with hm
      · simp only [World.shiftHosts, add_sub_cancel_right]
        cases hd : w.network.deliver i h s acc.1 with
        | none => rfl
        | some a =>
          simp only [Option.map_some]
          have hiff : (a + Δ h = t + Δ h) ↔ (a = t) := add_right_cancel_iff
          simp only [hiff]
      · rfl
    rw [hstep]
    exact ih _

private theorem sentArrivalsAux_concat [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (i h : H) (t : Time) (pfx l : List (Event H R Msg)) (e : Event H R Msg)
    (q : ℕ) (evs : List (Event H R Msg)) :
    sentArrivalsAux σ v i h t pfx (l ++ [e]) q evs
      = let r := sentArrivalsAux σ v i h t pfx l q evs
        match (v.clock i).timeAt e.reading with
        | some s =>
            let step := sendListArrivals v i h t s (heldOfView (pfx ++ l ++ [e])) r.1
              (σ i (pfx ++ l ++ [e])).sends
            (step.1, r.2 ++ step.2)
        | none => r := by
  induction l generalizing pfx q evs with
  | nil =>
    simp only [List.nil_append, sentArrivalsAux, List.append_nil]
  | cons a rest ih =>
    simp only [List.cons_append, sentArrivalsAux]
    cases (v.clock i).timeAt a.reading with
    | none =>
      simpa [List.append_assoc] using ih (pfx ++ [a]) q evs
    | some s =>
      simpa [List.append_assoc] using ih (pfx ++ [a])
        (sendListArrivals v i h t s (heldOfView (pfx ++ [a])) q (σ i (pfx ++ [a])).sends).1
        (evs ++ (sendListArrivals v i h t s (heldOfView (pfx ++ [a])) q (σ i (pfx ++ [a])).sends).2)

private theorem sentArrivalsFromView_concat [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (i h : H) (t s : Time) (view : List (Event H R Msg)) (obs : Observation H R Msg) :
    sentArrivalsFromView σ v i h t (view ++ [⟨(v.clock i).read s, obs⟩])
      = let r := sentArrivalsFromView σ v i h t view
        let step := sendListArrivals v i h t s
          (heldOfView (view ++ [⟨(v.clock i).read s, obs⟩])) r.1
          (σ i (view ++ [⟨(v.clock i).read s, obs⟩])).sends
        (step.1, r.2 ++ step.2) := by
  unfold sentArrivalsFromView
  rw [sentArrivalsAux_concat]
  have hta : (v.clock i).timeAt ((v.clock i).read s) = some s := by
    classical
    unfold Clock.timeAt
    have hex : ∃ u, (v.clock i).read u = (v.clock i).read s := ⟨s, rfl⟩
    rw [dite_eq_left hex, Option.some.injEq]
    exact (v.clock i).strictMono.injective (Classical.choose_spec hex)
  simp [hta]

private theorem sentArrivalsFromView_append_no_deliver [DecidableEq H] (σ : Solution H R Msg)
    (v : World H R) (i h : H) (t : Time) (view extra : List (Event H R Msg))
    (hno : ∀ e ∈ extra, ∀ s, (v.clock i).timeAt e.reading = some s →
      ∀ q, v.network.deliver i h s q ≠ some t) :
    (sentArrivalsFromView σ v i h t (view ++ extra)).2
      = (sentArrivalsFromView σ v i h t view).2 := by
  induction extra using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    rw [← List.append_assoc]
    have hl : (sentArrivalsFromView σ v i h t (view ++ l)).2
        = (sentArrivalsFromView σ v i h t view).2 :=
      ih (fun x hx => hno x (List.mem_append_left _ hx))
    unfold sentArrivalsFromView
    rw [sentArrivalsAux_concat]
    dsimp only
    cases hta : (v.clock i).timeAt e.reading with
    | none => exact hl
    | some s =>
      dsimp only
      rw [sendListArrivals_nil_of_no_deliver v i h t s _ _ _
        (hno e (List.mem_append_right _ (List.mem_singleton_self e)) s hta),
        List.append_nil]
      exact hl

theorem sentArrivalsFromView_shiftHosts [DecidableEq H] (σ : Solution H R Msg) (w : World H R)
    (Δ : H → ℝ) (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (i h : H) (t : Time) (view : List (Event H R Msg)) :
    sentArrivalsFromView σ (w.shiftHosts Δ hnet) i h (t + Δ h) view
      = sentArrivalsFromView σ w i h t view := by
  unfold sentArrivalsFromView
  suffices hgen : ∀ pfx rest q evs,
      sentArrivalsAux σ (w.shiftHosts Δ hnet) i h (t + Δ h) pfx rest q evs
        = sentArrivalsAux σ w i h t pfx rest q evs from hgen [] view 0 []
  intro pfx rest
  induction rest generalizing pfx with
  | nil => intro q evs; rfl
  | cons e rest ih =>
    intro q evs
    simp only [sentArrivalsAux]
    have hta : ((w.shiftHosts Δ hnet).clock i).timeAt e.reading
        = ((w.clock i).timeAt e.reading).map (· + Δ i) :=
      Clock.timeAt_shift (w.clock i) (Δ i) e.reading
    rw [hta]
    cases (w.clock i).timeAt e.reading with
    | none => exact ih (pfx ++ [e]) q evs
    | some s =>
      simp only [Option.map_some]
      rw [sendListArrivals_shift w Δ hnet i h t s]
      exact ih (pfx ++ [e]) _ _

/-- Count timers set by host `h` to fire at clock reading `cTarget`, computed
purely from host `h`'s local view. -/
def timersFromViewAux (σ : Solution H R Msg) (h : H) (cTarget : ℝ) :
    List (Event H R Msg) → List (Event H R Msg) → ℕ → ℕ
  | _, [], acc => acc
  | pfx, e :: rest, acc =>
      let pfx' := pfx ++ [e]
      let add := (σ h pfx').timers.countP (fun c => decide (e.reading < c ∧ c = cTarget))
      timersFromViewAux σ h cTarget pfx' rest (acc + add)

def timersFromView (σ : Solution H R Msg) (h : H) (cTarget : ℝ)
    (view : List (Event H R Msg)) : ℕ :=
  timersFromViewAux σ h cTarget [] view 0

private theorem timersFromViewAux_concat (σ : Solution H R Msg) (h : H) (cTarget : ℝ)
    (pfx l : List (Event H R Msg)) (e : Event H R Msg) (acc : ℕ) :
    timersFromViewAux σ h cTarget pfx (l ++ [e]) acc
      = timersFromViewAux σ h cTarget pfx l acc
        + (σ h (pfx ++ l ++ [e])).timers.countP (fun c => decide (e.reading < c ∧ c = cTarget)) := by
  induction l generalizing pfx acc with
  | nil => simp [timersFromViewAux]
  | cons a rest ih =>
    simp only [List.cons_append, timersFromViewAux]
    simpa [List.append_assoc] using ih (pfx ++ [a]) _

private theorem timersFromView_concat (σ : Solution H R Msg) (h : H) (cTarget : ℝ)
    (view : List (Event H R Msg)) (e : Event H R Msg) :
    timersFromView σ h cTarget (view ++ [e])
      = timersFromView σ h cTarget view
        + (σ h (view ++ [e])).timers.countP (fun c => decide (e.reading < c ∧ c = cTarget)) := by
  unfold timersFromView
  simpa using timersFromViewAux_concat σ h cTarget [] view e 0

/-- Filter `inFlight` to arrivals from origin `i` to destination `h` at time `t`. -/
def filterOriginArrivals [DecidableEq H] (v : World H R) (i h : H) (t : Time)
    (inFlight : List (InFlight H Msg)) : List (Event H R Msg) :=
  inFlight.filterMap fun m =>
    if m.origin = i ∧ m.destination = h ∧ m.arrival = t then
      some ⟨(v.clock h).read t, .received m.origin m.contents m.frames⟩
    else none

private theorem sendAll_filterOriginArrivals [DecidableEq H] (v : World H R)
    (st : State H R Msg) (h₀ : H) (s : Time) (held : Finset ℕ)
    (sends : List (H × Msg × Finset ℕ)) (i h : H) (t : Time) :
    (st.sendAll v h₀ s held sends).sentCount i h
      = (if h₀ = i then (sendListArrivals v i h t s held (st.sentCount i h) sends).1
          else st.sentCount i h)
    ∧ filterOriginArrivals v i h t (st.sendAll v h₀ s held sends).inFlight
      = filterOriginArrivals v i h t st.inFlight
        ++ (if h₀ = i then (sendListArrivals v i h t s held (st.sentCount i h) sends).2 else []) := by
  have hfold_append : ∀ (l : List (H × Msg × Finset ℕ)) (q : ℕ) (base extra : List (Event H R Msg)),
      (l.foldl
        (fun acc x =>
          if x.1 = h then
            let evs := match v.network.deliver i h s acc.1 with
              | some a =>
                  if a = t then
                    acc.2 ++ [⟨(v.clock h).read t, .received i x.2.1 (x.2.2.filter (· ∈ held))⟩]
                  else acc.2
              | none => acc.2
            (acc.1 + 1, evs)
          else acc) (q, base ++ extra)).2
      = base ++ (l.foldl
        (fun acc x =>
          if x.1 = h then
            let evs := match v.network.deliver i h s acc.1 with
              | some a =>
                  if a = t then
                    acc.2 ++ [⟨(v.clock h).read t, .received i x.2.1 (x.2.2.filter (· ∈ held))⟩]
                  else acc.2
              | none => acc.2
            (acc.1 + 1, evs)
          else acc) (q, extra)).2 := by
    intro l
    induction l with
    | nil => intro q base extra; rfl
    | cons x xs ihx =>
      intro q base extra
      simp only [List.foldl_cons]
      by_cases hx : x.1 = h
      · simp only [hx, ite_true]
        cases v.network.deliver i h s q with
        | none => exact ihx (q + 1) base extra
        | some a =>
          dsimp only
          split_ifs
          · rw [List.append_assoc]; exact ihx (q + 1) base _
          · exact ihx (q + 1) base extra
      · simp only [hx, ite_false]
        exact ihx q base extra
  have hfold_fst : ∀ (l : List (H × Msg × Finset ℕ)) (q : ℕ) (a b : List (Event H R Msg)),
      (l.foldl
        (fun acc x =>
          if x.1 = h then
            let evs := match v.network.deliver i h s acc.1 with
              | some a =>
                  if a = t then
                    acc.2 ++ [⟨(v.clock h).read t, .received i x.2.1 (x.2.2.filter (· ∈ held))⟩]
                  else acc.2
              | none => acc.2
            (acc.1 + 1, evs)
          else acc) (q, a)).1
      = (l.foldl
        (fun acc x =>
          if x.1 = h then
            let evs := match v.network.deliver i h s acc.1 with
              | some a =>
                  if a = t then
                    acc.2 ++ [⟨(v.clock h).read t, .received i x.2.1 (x.2.2.filter (· ∈ held))⟩]
                  else acc.2
              | none => acc.2
            (acc.1 + 1, evs)
          else acc) (q, b)).1 := by
    intro l
    induction l with
    | nil => intro q a b; rfl
    | cons x xs ihx =>
      intro q a b
      simp only [List.foldl_cons]
      split_ifs
      · exact ihx (q + 1) _ _
      · exact ihx q _ _
  induction sends generalizing st with
  | nil => simp [State.sendAll, sendListArrivals]
  | cons m rest ih =>
    set st1 := st.send v h₀ s m.1 m.2.1 (m.2.2.filter (· ∈ held)) with hst1
    have hstep_sa : st.sendAll v h₀ s held (m :: rest) = st1.sendAll v h₀ s held rest := rfl
    rw [hstep_sa]
    obtain ⟨ih1, ih2⟩ := ih st1
    by_cases hhi : h₀ = i
    · subst hhi
      have hsc1 : st1.sentCount h₀ h = if m.1 = h then st.sentCount h₀ h + 1 else st.sentCount h₀ h := by
        simp only [hst1, State.send]
        by_cases hmh : m.1 = h
        · subst hmh; simp
        · simp [hmh, Function.update_of_ne (Ne.symm hmh)]
      have hflt1 : filterOriginArrivals v h₀ h t st1.inFlight
          = filterOriginArrivals v h₀ h t st.inFlight
            ++ (if m.1 = h then
                  match v.network.deliver h₀ h s (st.sentCount h₀ h) with
                  | some a =>
                      if a = t then
                        [⟨(v.clock h).read t, .received h₀ m.2.1 (m.2.2.filter (· ∈ held))⟩]
                      else []
                  | none => []
                else []) := by
        simp only [hst1, State.send, filterOriginArrivals]
        cases hd : v.network.deliver h₀ m.1 s (st.sentCount h₀ m.1) with
        | none =>
          split_ifs with hmh
          · subst hmh; simp [hd]
          · simp
        | some a =>
          rw [List.filterMap_append]
          simp only [List.filterMap_cons, List.filterMap_nil, true_and]
          by_cases hmh : m.1 = h
          · subst hmh
            simp only [hd, ite_true, true_and]
            split_ifs <;> simp
          · simp [hmh]
      simp only [ite_true] at ih1 ih2 ⊢
      refine ⟨?_, ?_⟩
      · rw [ih1, sendListArrivals, sendListArrivals, List.foldl_cons]
        by_cases hmh : m.1 = h
        · simp only [hmh, ite_true] at hsc1 ⊢
          rw [hsc1]
          exact hfold_fst rest (st.sentCount h₀ h + 1) [] _
        · simp only [hmh, ite_false] at hsc1 ⊢
          rw [hsc1]
      · rw [ih2, hflt1, List.append_assoc, sendListArrivals, sendListArrivals, List.foldl_cons]
        congr 1
        by_cases hmh : m.1 = h
        · simp only [hmh, ite_true] at hsc1 ⊢
          rw [hsc1]
          cases hd : v.network.deliver h₀ h s (st.sentCount h₀ h) with
          | none => simp
          | some a =>
            dsimp only
            split_ifs with hat
            · simpa using (hfold_append rest (st.sentCount h₀ h + 1)
                [⟨(v.clock h).read t, .received h₀ m.2.1 (m.2.2.filter (· ∈ held))⟩] []).symm
            · simp
        · simp only [hmh, ite_false] at hsc1 ⊢
          rw [hsc1, List.nil_append]
    · have hsc1 : st1.sentCount i h = st.sentCount i h := by
        simp [hst1, State.send, Function.update_of_ne (Ne.symm hhi)]
      have hflt1 : filterOriginArrivals v i h t st1.inFlight
          = filterOriginArrivals v i h t st.inFlight := by
        simp only [hst1, State.send, filterOriginArrivals]
        cases v.network.deliver h₀ m.1 s (st.sentCount h₀ m.1) with
        | none => rfl
        | some a =>
          rw [List.filterMap_append]
          simp [hhi]
      simp only [hhi, ite_false, List.append_nil] at ih1 ih2 ⊢
      exact ⟨ih1.trans hsc1, ih2.trans hflt1⟩

/-- Before any event at or after time `t` has been processed, both `sentCount i h`
and the in-flight messages on link `(i, h)` arriving at time `t` are determined
purely by host `i`'s current view. -/
theorem Solution.inFlight_origin_at_eq [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (lookahead : ℕ+) (i h : H) (t : Time) {n : ℕ}
    (hlt : ∀ k < n, σ.eventTime v lookahead k < t) :
    (σ.states v lookahead n).sentCount i h
      = (sentArrivalsFromView σ v i h t ((σ.states v lookahead n).views i)).1
    ∧ filterOriginArrivals v i h t (σ.states v lookahead n).inFlight
      = (sentArrivalsFromView σ v i h t ((σ.states v lookahead n).views i)).2 := by
  induction n with
  | zero =>
    simp [Solution.states, State.start, filterOriginArrivals, sentArrivalsFromView, sentArrivalsAux]
  | succ n ih =>
    obtain ⟨ihc, ihf⟩ := ih (fun k hk => hlt k (Nat.lt_succ_of_lt hk))
    have hn_lt : σ.eventTime v lookahead n < t := hlt n (Nat.lt_succ_self n)
    set st := σ.states v lookahead n with hst
    have hheld_eq : ∀ h₀, st.held h₀ = heldOfView (st.views h₀) :=
      fun h₀ => σ.held_eq_heldOfView v lookahead n h₀
    have hhandle : ∀ (st₀ : State H R Msg) (h₀ : H) (s : Time) (obs : Observation H R Msg),
        st₀.views i = st.views i →
        st₀.held h₀ = heldOfView (st₀.views h₀) →
        st₀.sentCount i h = (sentArrivalsFromView σ v i h t (st.views i)).1 →
        filterOriginArrivals v i h t st₀.inFlight = (sentArrivalsFromView σ v i h t (st.views i)).2 →
        (st₀.handle σ v lookahead h₀ s obs).sentCount i h
          = (sentArrivalsFromView σ v i h t ((st₀.handle σ v lookahead h₀ s obs).views i)).1
        ∧ filterOriginArrivals v i h t (st₀.handle σ v lookahead h₀ s obs).inFlight
          = (sentArrivalsFromView σ v i h t ((st₀.handle σ v lookahead h₀ s obs).views i)).2 := by
      intro st₀ h₀ s obs hvi hhh hsc hfl
      dsimp only [State.handle]
      have hviews : (({ st₀ with
          views := Function.update st₀.views h₀ (st₀.views h₀ ++ [⟨(v.clock h₀).read s, obs⟩])
          held := Function.update st₀.held h₀ (st₀.held h₀ ∪ obs.frames) } : State H R Msg).sendAll
            v h₀ s (st₀.held h₀ ∪ obs.frames)
            (σ h₀ (st₀.views h₀ ++ [⟨(v.clock h₀).read s, obs⟩])).sends).views i
          = if i = h₀ then st.views i ++ [⟨(v.clock i).read s, obs⟩] else st.views i := by
        rw [State.sendAll_views]
        split_ifs with hh
        · subst hh; simp [hvi]
        · simp [Function.update_of_ne hh, hvi]
      have hsa := sendAll_filterOriginArrivals v
        { st₀ with
          views := Function.update st₀.views h₀ (st₀.views h₀ ++ [⟨(v.clock h₀).read s, obs⟩])
          held := Function.update st₀.held h₀ (st₀.held h₀ ∪ obs.frames) }
        h₀ s (st₀.held h₀ ∪ obs.frames)
        (σ h₀ (st₀.views h₀ ++ [⟨(v.clock h₀).read s, obs⟩])).sends i h t
      rw [hviews]
      by_cases hhi : h₀ = i
      · subst hhi
        simp only [ite_true] at hsa ⊢
        rw [sentArrivalsFromView_concat]
        have hh' : st₀.held h₀ ∪ obs.frames = heldOfView (st.views h₀ ++ [⟨(v.clock h₀).read s, obs⟩]) := by
          rw [heldOfView_concat, ← hvi, hhh]
        refine ⟨?_, ?_⟩
        · simpa only [hvi, hh', hsc] using hsa.1
        · simpa only [hvi, hh', hsc, hfl] using hsa.2
      · have hih : i ≠ h₀ := Ne.symm hhi
        simp only [hhi, hih, ite_false, List.append_nil] at hsa ⊢
        exact ⟨hsa.1.trans hsc, hsa.2.trans hfl⟩
    show ((st.step σ v lookahead).sentCount i h
        = (sentArrivalsFromView σ v i h t ((st.step σ v lookahead).views i)).1)
      ∧ (filterOriginArrivals v i h t (st.step σ v lookahead).inFlight
        = (sentArrivalsFromView σ v i h t ((st.step σ v lookahead).views i)).2)
    unfold State.step
    cases he : earliest (st.key v) st.due with
    | none => exact ⟨ihc, ihf⟩
    | some d =>
      dsimp only
      cases d with
      | handed b =>
        exact hhandle st v.sender (v.source.handed b) _ rfl (hheld_eq _) ihc ihf
      | asked r b =>
        exact hhandle st (v.host r) ((v.speaker r).asked b) _ rfl (hheld_eq _) ihc ihf
      | arrival p =>
        dsimp only
        cases hm : st.inFlight[p]? with
        | none => dsimp only; exact ⟨ihc, ihf⟩
        | some m =>
          dsimp only
          have hma : m.arrival < t := by
            have ht : σ.eventTime v lookahead n = m.arrival := by
              simp only [Solution.eventTime, ← hst, he, State.key, hm, Option.map_some,
                Option.getD_some]
            linarith
          have hp : p < st.inFlight.length := by
            by_contra hge
            rw [List.getElem?_eq_none (not_lt.mp hge)] at hm
            simp at hm
          have hfl_erase : filterOriginArrivals v i h t (st.inFlight.eraseIdx p)
              = filterOriginArrivals v i h t st.inFlight := by
            unfold filterOriginArrivals
            conv_rhs => rw [← List.take_append_drop p st.inFlight]
            rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons hp,
              List.filterMap_append, List.filterMap_append, List.filterMap_cons]
            have hget : st.inFlight[p] = m := by
              rw [List.getElem?_eq_getElem hp, Option.some.injEq] at hm; exact hm
            rw [hget]
            have hne : m.arrival ≠ t := ne_of_lt hma
            simp [hne]
          exact hhandle { st with inFlight := st.inFlight.eraseIdx p } m.destination m.arrival _
            rfl (hheld_eq _) ihc (hfl_erase.trans ihf)
      | timer p =>
        dsimp only
        cases hu : st.timers[p]? with
        | none => dsimp only; exact ⟨ihc, ihf⟩
        | some u =>
          dsimp only
          exact hhandle { st with timers := st.timers.eraseIdx p } u.host u.time .timer
            rfl (hheld_eq _) ihc ihf

/-- Before any event at or after time `t` has been processed, the number of
pending timers at host `h` scheduled for time `t` equals `timersFromView` of
host `h`'s current view. -/
theorem Solution.timers_countP_at_eq [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (lookahead : ℕ+) (h : H) (t : Time) {n : ℕ}
    (hlt : ∀ k < n, σ.eventTime v lookahead k < t) :
    (σ.states v lookahead n).timers.countP (fun u => decide (u.host = h ∧ u.time = t))
      = timersFromView σ h ((v.clock h).read t) ((σ.states v lookahead n).views h) := by
  induction n with
  | zero =>
    simp [Solution.states, State.start, timersFromView, timersFromViewAux]
  | succ n ih =>
    have ih' := ih (fun k hk => hlt k (Nat.lt_succ_of_lt hk))
    have hn_lt : σ.eventTime v lookahead n < t := hlt n (Nat.lt_succ_self n)
    set st := σ.states v lookahead n with hst
    have hhandle : ∀ (st₀ : State H R Msg) (h₀ : H) (s : Time) (obs : Observation H R Msg),
        st₀.views h = st.views h →
        st₀.timers.countP (fun u => decide (u.host = h ∧ u.time = t))
          = timersFromView σ h ((v.clock h).read t) (st.views h) →
        (st₀.handle σ v lookahead h₀ s obs).timers.countP (fun u => decide (u.host = h ∧ u.time = t))
          = timersFromView σ h ((v.clock h).read t) ((st₀.handle σ v lookahead h₀ s obs).views h) := by
      intro st₀ h₀ s obs hvh htc
      dsimp only [State.handle]
      rw [State.sendAll_timers, State.sendAll_views, List.countP_append]
      by_cases hh : h₀ = h
      · subst hh
        simp only [Function.update_self, hvh, htc, timersFromView_concat]
        congr 1
        set ts := (σ h₀ (st.views h₀ ++ [⟨(v.clock h₀).read s, obs⟩])).timers
        induction ts with
        | nil => simp
        | cons c cs ihc =>
          simp only [List.filterMap_cons, List.countP_cons]
          by_cases hltc : (v.clock h₀).read s < c
          · simp only [hltc, ite_true]
            cases hta : (v.clock h₀).timeAt c with
            | none =>
              have hne : c ≠ (v.clock h₀).read t := by
                intro heq
                subst heq
                have hsome : (v.clock h₀).timeAt ((v.clock h₀).read t) = some t := by
                  classical
                  unfold Clock.timeAt
                  have hex : ∃ u, (v.clock h₀).read u = (v.clock h₀).read t := ⟨t, rfl⟩
                  rw [dite_eq_left hex, Option.some.injEq]
                  exact (v.clock h₀).strictMono.injective (Classical.choose_spec hex)
                rw [hsome] at hta
                simp at hta
              simp only [Option.map_none, hne, and_false, decide_false, Bool.false_eq_true,
                ite_false, add_zero]
              exact ihc
            | some u =>
              have hru : (v.clock h₀).read u = c := Clock.read_timeAt hta
              have hiff : (u = t) ↔ (c = (v.clock h₀).read t) := by
                constructor
                · rintro rfl; exact hru.symm
                · intro heq; exact (v.clock h₀).strictMono.injective (hru.trans heq)
              simp only [Option.map_some, List.countP_cons, true_and, hiff]
              omega
          · simp only [hltc, ite_false, false_and, decide_false, Bool.false_eq_true, add_zero]
            exact ihc
      · have hne : h ≠ h₀ := Ne.symm hh
        simp only [Function.update_of_ne hne, hvh, htc]
        have hzero : (List.filterMap
            (fun c => if (v.clock h₀).read s < c then
              Option.map (fun u => (⟨u, h₀⟩ : Timer H)) ((v.clock h₀).timeAt c) else none)
            (σ h₀ (st₀.views h₀ ++ [⟨(v.clock h₀).read s, obs⟩])).timers).countP
              (fun u => decide (u.host = h ∧ u.time = t)) = 0 := by
          rw [List.countP_eq_zero]
          intro u hu
          simp only [List.mem_filterMap] at hu
          rcases hu with ⟨c, _, hc⟩
          split_ifs at hc with hltc
          · rw [Option.map_eq_some_iff] at hc
            rcases hc with ⟨t', _, rfl⟩
            simp [hh]
        omega
    show ((st.step σ v lookahead).timers.countP (fun u => decide (u.host = h ∧ u.time = t)))
      = timersFromView σ h ((v.clock h).read t) ((st.step σ v lookahead).views h)
    unfold State.step
    cases he : earliest (st.key v) st.due with
    | none => exact ih'
    | some d =>
      dsimp only
      cases d with
      | handed b => exact hhandle st v.sender (v.source.handed b) _ rfl ih'
      | asked r b => exact hhandle st (v.host r) ((v.speaker r).asked b) _ rfl ih'
      | arrival p =>
        dsimp only
        cases hm : st.inFlight[p]? with
        | none => dsimp only; exact ih'
        | some m =>
          dsimp only
          exact hhandle { st with inFlight := st.inFlight.eraseIdx p } m.destination m.arrival _ rfl ih'
      | timer p =>
        dsimp only
        cases hu : st.timers[p]? with
        | none => dsimp only; exact ih'
        | some u =>
          dsimp only
          have hut : u.time < t := by
            have ht : σ.eventTime v lookahead n = u.time := by
              simp only [Solution.eventTime, ← hst, he, State.key, hu, Option.map_some,
                Option.getD_some]
            linarith
          have hp : p < st.timers.length := by
            by_contra hge
            rw [List.getElem?_eq_none (not_lt.mp hge)] at hu
            simp at hu
          have htc_erase : (st.timers.eraseIdx p).countP (fun u => decide (u.host = h ∧ u.time = t))
              = st.timers.countP (fun u => decide (u.host = h ∧ u.time = t)) := by
            conv_rhs => rw [← List.take_append_drop p st.timers]
            rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons hp,
              List.countP_append, List.countP_append, List.countP_cons]
            have hget : st.timers[p] = u := by
              rw [List.getElem?_eq_getElem hp, Option.some.injEq] at hu; exact hu
            rw [hget]
            have hne : u.time ≠ t := ne_of_lt hut
            simp [hne]
          exact hhandle { st with timers := st.timers.eraseIdx p } u.host u.time .timer rfl
            (htc_erase.trans ih')

/-- Remaining events scheduled for host `h` at exact true time `t` in state `st`,
ordered by the specification's tie-breaking rank. -/
def remHanded [DecidableEq H] (v : World H R) (h : H) (t : Time) (st : State H R Msg) :
    List (Event H R Msg) :=
  if h = v.sender ∧ v.source.handed st.handedNext = t then
    [⟨(v.clock h).read t,
      .handed ((v.source.block st.handedNext).map fun n => (n, v.target n))
        (v.source.reported st.handedNext)⟩]
  else []

def remAsked [DecidableEq H] (v : World H R) (h : H) (t : Time) (st : State H R Msg) :
    List (Event H R Msg) :=
  (List.finRange R).filterMap fun r =>
    if v.host r = h ∧ (v.speaker r).asked (st.askedNext r) = t then
      some ⟨(v.clock h).read t,
        .asked r ((v.speaker r).block (st.askedNext r)) ((v.speaker r).reported (st.askedNext r))⟩
    else none

def remArrivals [DecidableEq H] (v : World H R) (h : H) (t : Time) (st : State H R Msg) :
    List (Event H R Msg) :=
  st.inFlight.filterMap fun m =>
    if m.destination = h ∧ m.arrival = t then
      some ⟨(v.clock h).read t, .received m.origin m.contents m.frames⟩
    else none

def remTimers [DecidableEq H] (v : World H R) (h : H) (t : Time) (st : State H R Msg) :
    List (Event H R Msg) :=
  List.replicate (st.timers.countP fun u => decide (u.host = h ∧ u.time = t))
    ⟨(v.clock h).read t, .timer⟩

def remAll [DecidableEq H] (v : World H R) (h : H) (t : Time) (st : State H R Msg) :
    List (Event H R Msg) :=
  remHanded v h t st ++ remAsked v h t st ++ remArrivals v h t st ++ remTimers v h t st

private theorem sendAll_remArrivals_gt [DecidableEq H] (v : World H R) (st : State H R Msg)
    (h₀ h : H) (t : Time) (held : Finset ℕ) (sends : List (H × Msg × Finset ℕ)) :
    remArrivals v h t (st.sendAll v h₀ t held sends) = remArrivals v h t st := by
  induction sends generalizing st with
  | nil => rfl
  | cons m rest ih =>
    have hstep_sa : st.sendAll v h₀ t held (m :: rest)
        = (st.send v h₀ t m.1 m.2.1 (m.2.2.filter (· ∈ held))).sendAll v h₀ t held rest := rfl
    rw [hstep_sa, ih]
    unfold remArrivals State.send
    cases hd : v.network.deliver h₀ m.1 t (st.sentCount h₀ m.1) with
    | none => rfl
    | some a =>
      have hne : a ≠ t := ne_of_gt (v.network.after h₀ m.1 t (st.sentCount h₀ m.1) a hd)
      rw [List.filterMap_append]
      simp [hne]

private theorem handle_remTimers_gt [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (lookahead : ℕ+) (st : State H R Msg) (h₀ h : H) (t : Time) (obs : Observation H R Msg) :
    remTimers v h t (st.handle σ v lookahead h₀ t obs) = remTimers v h t st := by
  unfold remTimers State.handle
  dsimp only
  rw [State.sendAll_timers, List.countP_append]
  have hzero : (List.filterMap
      (fun c => if (v.clock h₀).read t < c then
        Option.map (fun u => (⟨u, h₀⟩ : Timer H)) ((v.clock h₀).timeAt c) else none)
      (σ h₀ (st.views h₀ ++ [⟨(v.clock h₀).read t, obs⟩])).timers).countP
        (fun u => decide (u.host = h ∧ u.time = t)) = 0 := by
    rw [List.countP_eq_zero]
    intro u hu
    simp only [List.mem_filterMap] at hu
    rcases hu with ⟨c, _, hc⟩
    split_ifs at hc with hlt
    · rw [Option.map_eq_some_iff] at hc
      rcases hc with ⟨t', ht', rfl⟩
      have hrt' : (v.clock h₀).read t' = c := Clock.read_timeAt ht'
      have hne : t' ≠ t := by
        intro heq; subst heq; linarith
      simp [hne]
  rw [hzero, add_zero]

/-- **Per-instant conservation law.** At any step whose event occurs at exact
true time `t`, the concatenation `views h ++ remAll v h t` is invariant for
every host `h`. -/
theorem Solution.views_append_remAll_step [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (lookahead : ℕ+) (h : H) (t : Time) {k : ℕ} (hk : σ.eventTime v lookahead k = t) :
    (σ.states v lookahead (k + 1)).views h ++ remAll v h t (σ.states v lookahead (k + 1))
      = (σ.states v lookahead k).views h ++ remAll v h t (σ.states v lookahead k) := by
  set st := σ.states v lookahead k with hst
  have hdue := σ.eventTime_dueFrom v lookahead k
  rw [← hst, hk] at hdue
  obtain ⟨e₀, he₀⟩ := earliest_exists (st.key v) st.due_ne_nil
  obtain ⟨hmem, hlex⟩ := earliest_spec_lex (st.key v) st.due e₀ he₀
  have ht0 : (st.key v e₀).1 = t := by
    simpa only [Solution.eventTime, ← hst, he₀] using hk
  have hstep : σ.states v lookahead (k + 1) = st.step σ v lookahead := rfl
  rw [hstep]
  unfold State.step
  rw [he₀]
  rcases st.mem_due hmem with rfl | ⟨r, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · dsimp only
    have hht : v.source.handed st.handedNext = t := ht0
    have hgt : v.source.handed (st.handedNext + 1) ≠ t :=
      ne_of_gt (hht ▸ v.source.handed_strictMono (Nat.lt_succ_self _))
    set obs : Observation H R Msg :=
      .handed ((v.source.block st.handedNext).map fun n => (n, v.target n))
        (v.source.reported st.handedNext)
    have hremA : remArrivals v h t (st.handle σ v lookahead v.sender t obs) = remArrivals v h t st := by
      dsimp only [State.handle]; exact sendAll_remArrivals_gt v _ v.sender h t _ _
    have hremT : remTimers v h t (st.handle σ v lookahead v.sender t obs) = remTimers v h t st :=
      handle_remTimers_gt σ v lookahead st v.sender h t obs
    have hremQ : remAsked v h t (st.handle σ v lookahead v.sender t obs) = remAsked v h t st := by
      unfold remAsked; rw [State.handle_askedNext]
    have hremH_new : remHanded v h t
        { st.handle σ v lookahead v.sender t obs with handedNext := st.handedNext + 1 } = [] := by
      simp [remHanded, hgt]
    unfold remAll
    have hremA' : remArrivals v h t
        { st.handle σ v lookahead v.sender t obs with handedNext := st.handedNext + 1 }
        = remArrivals v h t st := hremA
    have hremT' : remTimers v h t
        { st.handle σ v lookahead v.sender t obs with handedNext := st.handedNext + 1 }
        = remTimers v h t st := hremT
    have hremQ' : remAsked v h t
        { st.handle σ v lookahead v.sender t obs with handedNext := st.handedNext + 1 }
        = remAsked v h t st := hremQ
    rw [hht, hremH_new, hremQ', hremA', hremT']
    by_cases hs : h = v.sender
    · subst hs
      have hv : ({ st.handle σ v lookahead v.sender t obs with handedNext := st.handedNext + 1 }).views v.sender
          = st.views v.sender ++ [⟨(v.clock v.sender).read t, obs⟩] := by
        simp [State.handle, State.sendAll_views]
      rw [hv]
      simp [remHanded, hht, obs, List.append_assoc]
    · have hv : ({ st.handle σ v lookahead v.sender t obs with handedNext := st.handedNext + 1 }).views h
          = st.views h := by
        simp [State.handle, State.sendAll_views, Function.update_of_ne hs]
      rw [hv]
      simp [remHanded, hs]
  · dsimp only
    have hat : (v.speaker r).asked (st.askedNext r) = t := ht0
    have hgt : (v.speaker r).asked (st.askedNext r + 1) ≠ t :=
      ne_of_gt (hat ▸ (v.speaker r).asked_strictMono (Nat.lt_succ_self _))
    have hnoH : v.source.handed st.handedNext ≠ t := by
      intro heq
      rcases hlex (.handed st.handedNext) st.handed_mem_due with h1 | ⟨_, h2⟩
      · simp [State.key, hat, heq] at h1
      · simp [State.key] at h2
    have hnoLt : ∀ r' : Fin R, r' < r → (v.speaker r').asked (st.askedNext r') ≠ t := by
      intro r' hr' heq
      rcases hlex (.asked r' (st.askedNext r')) (st.asked_mem_due r') with h1 | ⟨_, h2⟩
      · simp [State.key, hat, heq] at h1
      · simp only [State.key] at h2
        have : (r' : ℕ) < (r : ℕ) := hr'
        omega
    set obs : Observation H R Msg :=
      .asked r ((v.speaker r).block (st.askedNext r)) ((v.speaker r).reported (st.askedNext r))
    set st1 := { st.handle σ v lookahead (v.host r) t obs with
      askedNext := Function.update st.askedNext r (st.askedNext r + 1) }
    have hremH1 : remHanded v h t st1 = [] := by
      simp [remHanded, st1, State.handle_handedNext, hnoH]
    have hremH0 : remHanded v h t st = [] := by
      simp [remHanded, hnoH]
    have hremA1 : remArrivals v h t st1 = remArrivals v h t st := by
      dsimp only [st1, State.handle]; exact sendAll_remArrivals_gt v _ (v.host r) h t _ _
    have hremT1 : remTimers v h t st1 = remTimers v h t st :=
      handle_remTimers_gt σ v lookahead st (v.host r) h t obs
    unfold remAll
    rw [hat]
    change st1.views h ++ (remHanded v h t st1 ++ remAsked v h t st1 ++ remArrivals v h t st1 ++ remTimers v h t st1)
      = st.views h ++ (remHanded v h t st ++ remAsked v h t st ++ remArrivals v h t st ++ remTimers v h t st)
    rw [hremH1, hremH0, hremA1, hremT1, List.nil_append, List.nil_append]
    by_cases hr : v.host r = h
    · have hv1 : st1.views h = st.views h ++ [⟨(v.clock h).read t, obs⟩] := by
        simp [st1, State.handle, State.sendAll_views, hr]
      have hremQ : remAsked v h t st = ⟨(v.clock h).read t, obs⟩ :: remAsked v h t st1 := by
        unfold remAsked
        have hsplit : List.finRange R
            = (List.finRange R).take r.1 ++ r :: (List.finRange R).drop (r.1 + 1) := by
          have hlen : r.1 < (List.finRange R).length := by simp
          have hget : (List.finRange R)[r.1]'hlen = r := by simp
          conv_lhs => rw [← List.take_append_drop r.1 (List.finRange R)]
          rw [List.drop_eq_getElem_cons hlen, hget]
        have htake_none : ∀ (f : Fin R → Option (Event H R Msg)),
            (∀ r' : Fin R, r' < r → f r' = none) →
            ((List.finRange R).take r.1).filterMap f = [] := by
          intro f hf
          rw [List.filterMap_eq_nil_iff]
          intro r' hr'
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr'
          have hi' : i < r.1 := by
            have := List.length_take_le r.1 (List.finRange R)
            omega
          have hlt' : ((List.finRange R).take r.1)[i] < r := by
            simp [List.getElem_take, Fin.lt_def, hi']
          exact hf _ hlt'
        have hdrop_eq : (((List.finRange R).drop (r.1 + 1)).filterMap
              (fun r' => if v.host r' = h ∧ (v.speaker r').asked (st.askedNext r') = t then
                some (⟨(v.clock h).read t,
                  .asked r' ((v.speaker r').block (st.askedNext r'))
                    ((v.speaker r').reported (st.askedNext r'))⟩ : Event H R Msg)
              else none) : List (Event H R Msg))
            = ((List.finRange R).drop (r.1 + 1)).filterMap
              (fun r' => if v.host r' = h ∧ (v.speaker r').asked (st1.askedNext r') = t then
                some (⟨(v.clock h).read t,
                  .asked r' ((v.speaker r').block (st1.askedNext r'))
                    ((v.speaker r').reported (st1.askedNext r'))⟩ : Event H R Msg)
              else none) := by
          refine List.filterMap_congr fun r' hr' => ?_
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr'
          have hne : ((List.finRange R).drop (r.1 + 1))[i] ≠ r := by
            intro h
            have hv := congrArg Fin.val h
            simp only [List.getElem_drop, List.getElem_finRange, Fin.val_cast] at hv
            omega
          simp only [st1, Function.update_of_ne hne]
        conv_lhs => rw [hsplit]
        conv_rhs => rw [hsplit]
        rw [List.filterMap_append, List.filterMap_append, List.filterMap_cons, List.filterMap_cons]
        rw [htake_none _ (fun r' hr' => by simp [hnoLt r' hr']),
          htake_none _ (fun r' hr' => by
            have hne : r' ≠ r := ne_of_lt hr'
            simp [st1, Function.update_of_ne hne, hnoLt r' hr'])]
        simp only [List.nil_append, hr, hat, and_self, ite_true, st1, Function.update_self, hgt,
          and_false, ite_false, hdrop_eq, obs]
      rw [hv1, hremQ]
      simp [List.append_assoc]
    · have hv1 : st1.views h = st.views h := by
        simp [st1, State.handle, State.sendAll_views, Function.update_of_ne (Ne.symm hr)]
      have hremQ : remAsked v h t st1 = remAsked v h t st := by
        unfold remAsked
        refine List.filterMap_congr fun r' _ => ?_
        by_cases hrr' : r' = r
        · subst hrr'; simp [hr]
        · simp [st1, Function.update_of_ne hrr']
      rw [hv1, hremQ]
  · dsimp only
    set m := st.inFlight[p]'hp
    have hget : st.inFlight[p]? = some m := List.getElem?_eq_getElem hp
    have hmt : m.arrival = t := by
      simpa [State.key, hget] using ht0
    have hnoH : v.source.handed st.handedNext ≠ t := by
      intro heq
      rcases hlex (.handed st.handedNext) st.handed_mem_due with h1 | ⟨_, h2⟩
      · simp [State.key, hget, hmt, heq] at h1
      · simp [State.key] at h2
    have hnoQ : ∀ r : Fin R, (v.speaker r).asked (st.askedNext r) ≠ t := by
      intro r heq
      rcases hlex (.asked r (st.askedNext r)) (st.asked_mem_due r) with h1 | ⟨_, h2⟩
      · simp [State.key, hget, hmt, heq] at h1
      · simp only [State.key] at h2
        have := r.isLt
        omega
    have hnoEarlier : ∀ (q : ℕ) (hqp : q < p), (st.inFlight[q]'(lt_trans hqp hp)).arrival ≠ t := by
      intro q hqp heq
      have hqlen : q < st.inFlight.length := lt_trans hqp hp
      rcases hlex (.arrival q) (st.arrival_mem_due hqlen) with h1 | ⟨_, h2⟩
      · simp [State.key, hget, hmt, List.getElem?_eq_getElem hqlen, heq] at h1
      · simp only [State.key] at h2
        omega
    rw [hget]
    dsimp only
    set st₀ : State H R Msg := { st with inFlight := st.inFlight.eraseIdx p }
    set obs : Observation H R Msg := .received m.origin m.contents m.frames
    set st1 := st₀.handle σ v lookahead m.destination t obs
    have hremH0 : remHanded v h t st = [] := by simp [remHanded, hnoH]
    have hremH1 : remHanded v h t st1 = [] := by
      simp [remHanded, st1, State.handle_handedNext, st₀, hnoH]
    have hremQ0 : remAsked v h t st = [] := by
      unfold remAsked
      rw [List.filterMap_eq_nil_iff]
      intro r _; simp [hnoQ r]
    have hremQ1 : remAsked v h t st1 = [] := by
      unfold remAsked
      rw [State.handle_askedNext]
      rw [List.filterMap_eq_nil_iff]
      intro r _; simp [st₀, hnoQ r]
    have hremT1 : remTimers v h t st1 = remTimers v h t st :=
      handle_remTimers_gt σ v lookahead st₀ m.destination h t obs
    have hremA1 : remArrivals v h t st1 = remArrivals v h t st₀ := by
      dsimp only [st1, State.handle]
      exact sendAll_remArrivals_gt v _ m.destination h t _ _
    have htake_nil : ((st.inFlight.take p).filterMap
        (fun x => if x.destination = h ∧ x.arrival = t then
          some (⟨(v.clock h).read t, .received x.origin x.contents x.frames⟩ : Event H R Msg)
        else none) : List (Event H R Msg)) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx
      have hqp : q < p := by
        have := List.length_take_le p st.inFlight
        omega
      simp only [List.getElem_take]
      simp [hnoEarlier q hqp]
    have hsplit_arr : remArrivals v h t st
        = (if m.destination = h then [⟨(v.clock h).read t, obs⟩] else [])
          ++ remArrivals v h t st₀ := by
      unfold remArrivals
      simp only [st₀]
      conv_lhs => rw [← List.take_append_drop p st.inFlight]
      rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons hp,
        List.filterMap_append, List.filterMap_append, List.filterMap_cons, htake_nil]
      simp only [List.nil_append, m, hmt, and_true, obs]
      split_ifs <;> simp
    unfold remAll
    rw [hmt]
    change st1.views h ++ (remHanded v h t st1 ++ remAsked v h t st1 ++ remArrivals v h t st1 ++ remTimers v h t st1)
      = st.views h ++ (remHanded v h t st ++ remAsked v h t st ++ remArrivals v h t st ++ remTimers v h t st)
    rw [hremH1, hremH0, hremQ1, hremQ0, hremA1, hremT1, hsplit_arr]
    by_cases hd : m.destination = h
    · have hv1 : st1.views h = st.views h ++ [⟨(v.clock h).read t, obs⟩] := by
        simp [st1, st₀, State.handle, State.sendAll_views, hd]
      rw [hv1]
      simp [hd, List.append_assoc]
    · have hv1 : st1.views h = st.views h := by
        simp [st1, st₀, State.handle, State.sendAll_views, Function.update_of_ne (Ne.symm hd)]
      rw [hv1]
      simp [hd]
  · dsimp only
    set u := st.timers[p]'hp
    have hget : st.timers[p]? = some u := List.getElem?_eq_getElem hp
    have hut : u.time = t := by
      simpa [State.key, hget] using ht0
    have hnoH : v.source.handed st.handedNext ≠ t := by
      intro heq
      rcases hlex (.handed st.handedNext) st.handed_mem_due with h1 | ⟨_, h2⟩
      · simp [State.key, hget, hut, heq] at h1
      · simp [State.key] at h2
    have hnoQ : ∀ r : Fin R, (v.speaker r).asked (st.askedNext r) ≠ t := by
      intro r heq
      rcases hlex (.asked r (st.askedNext r)) (st.asked_mem_due r) with h1 | ⟨_, h2⟩
      · simp [State.key, hget, hut, heq] at h1
      · simp only [State.key] at h2
        have := r.isLt
        omega
    have hnoA : ∀ m ∈ st.inFlight, m.arrival ≠ t := by
      intro m hm heq
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hm
      rcases hlex (.arrival q) (st.arrival_mem_due hq) with h1 | ⟨_, h2⟩
      · simp [State.key, hget, hut, List.getElem?_eq_getElem hq, heq] at h1
      · simp only [State.key] at h2
        omega
    rw [hget]
    dsimp only
    set st₀ : State H R Msg := { st with timers := st.timers.eraseIdx p }
    set st1 := st₀.handle σ v lookahead u.host t .timer
    have hremH0 : remHanded v h t st = [] := by simp [remHanded, hnoH]
    have hremH1 : remHanded v h t st1 = [] := by
      simp [remHanded, st1, State.handle_handedNext, st₀, hnoH]
    have hremQ0 : remAsked v h t st = [] := by
      unfold remAsked
      rw [List.filterMap_eq_nil_iff]
      intro r _; simp [hnoQ r]
    have hremQ1 : remAsked v h t st1 = [] := by
      unfold remAsked
      rw [State.handle_askedNext]
      rw [List.filterMap_eq_nil_iff]
      intro r _; simp [st₀, hnoQ r]
    have hremA0 : remArrivals v h t st = [] := by
      unfold remArrivals
      rw [List.filterMap_eq_nil_iff]
      intro m hm; simp [hnoA m hm]
    have hremA1 : remArrivals v h t st1 = [] := by
      have : remArrivals v h t st1 = remArrivals v h t st₀ := by
        dsimp only [st1, State.handle]
        exact sendAll_remArrivals_gt v _ u.host h t _ _
      rw [this]
      exact hremA0
    have hremT1 : remTimers v h t st1 = remTimers v h t st₀ :=
      handle_remTimers_gt σ v lookahead st₀ u.host h t .timer
    have hcnt : st.timers.countP (fun x => decide (x.host = h ∧ x.time = t))
        = (if u.host = h then 1 else 0)
          + (st.timers.eraseIdx p).countP (fun x => decide (x.host = h ∧ x.time = t)) := by
      conv_lhs => rw [← List.take_append_drop p st.timers]
      rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons hp,
        List.countP_append, List.countP_append, List.countP_cons]
      have : st.timers[p] = u := rfl
      rw [this, hut]
      by_cases huh : u.host = h
      · simp only [huh, and_self, decide_true, ite_true]; omega
      · simp only [huh, false_and, decide_false, Bool.false_eq_true, ite_false]; omega
    unfold remAll
    rw [hut]
    change st1.views h ++ (remHanded v h t st1 ++ remAsked v h t st1 ++ remArrivals v h t st1 ++ remTimers v h t st1)
      = st.views h ++ (remHanded v h t st ++ remAsked v h t st ++ remArrivals v h t st ++ remTimers v h t st)
    rw [hremH1, hremH0, hremQ1, hremQ0, hremA1, hremA0, hremT1]
    simp only [List.nil_append]
    by_cases huh : u.host = h
    · have hv1 : st1.views h = st.views h ++ [⟨(v.clock h).read t, .timer⟩] := by
        simp [st1, st₀, State.handle, State.sendAll_views, huh]
      rw [hv1]
      unfold remTimers
      simp only [st₀, hcnt, huh, ite_true, add_comm 1, List.replicate_succ]
      rw [List.append_assoc, List.singleton_append]
    · have hv1 : st1.views h = st.views h := by
        simp [st1, st₀, State.handle, State.sendAll_views, Function.update_of_ne (Ne.symm huh)]
      rw [hv1]
      unfold remTimers
      simp only [st₀, hcnt, huh, ite_false, zero_add]

/-- At any step whose event time is strictly greater than `t`, no pending events
remain at time `t`. -/
theorem Solution.remAll_eq_nil_of_lt_eventTime [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (lookahead : ℕ+) (h : H) (t : Time) {n : ℕ} (hn : t < σ.eventTime v lookahead n) :
    remAll v h t (σ.states v lookahead n) = [] := by
  have hdue := σ.eventTime_dueFrom v lookahead n
  unfold remAll
  have h1 : remHanded v h t (σ.states v lookahead n) = [] := by
    have : t < v.source.handed (σ.states v lookahead n).handedNext := lt_of_lt_of_le hn hdue.1
    simp [remHanded, ne_of_gt this]
  have h2 : remAsked v h t (σ.states v lookahead n) = [] := by
    unfold remAsked
    rw [List.filterMap_eq_nil_iff]
    intro r _
    have : t < (v.speaker r).asked ((σ.states v lookahead n).askedNext r) :=
      lt_of_lt_of_le hn (hdue.2.1 r)
    simp [ne_of_gt this]
  have h3 : remArrivals v h t (σ.states v lookahead n) = [] := by
    unfold remArrivals
    rw [List.filterMap_eq_nil_iff]
    intro m hm
    have : t < m.arrival := lt_of_lt_of_le hn (hdue.2.2.1 m hm)
    simp [ne_of_gt this]
  have h4 : remTimers v h t (σ.states v lookahead n) = [] := by
    unfold remTimers
    have hzero : (σ.states v lookahead n).timers.countP (fun u => decide (u.host = h ∧ u.time = t)) = 0 := by
      rw [List.countP_eq_zero]
      intro u hu
      have : t < u.time := lt_of_lt_of_le hn (hdue.2.2.2 u hu)
      simp [ne_of_gt this]
    rw [hzero]
    rfl
  simp [h1, h2, h3, h4]

/-- **View-update formula at a single instant `t`.** Between `n₀` (first step
with `eventTime ≥ t`) and `n₁` (first step with `eventTime > t`), every host's
view advances by exactly `remAll v h t (states n₀)`. -/
theorem Solution.views_eq_append_remAll [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (lookahead : ℕ+) (h : H) (t : Time) {n₀ n₁ : ℕ}
    (hle : n₀ ≤ n₁)
    (hge : t ≤ σ.eventTime v lookahead n₀)
    (hgt : t < σ.eventTime v lookahead n₁)
    (hbefore : ∀ k < n₁, σ.eventTime v lookahead k ≤ t) :
    (σ.states v lookahead n₁).views h
      = (σ.states v lookahead n₀).views h ++ remAll v h t (σ.states v lookahead n₀) := by
  have hcons : ∀ k, n₀ ≤ k → k ≤ n₁ →
      (σ.states v lookahead k).views h ++ remAll v h t (σ.states v lookahead k)
        = (σ.states v lookahead n₀).views h ++ remAll v h t (σ.states v lookahead n₀) := by
    intro k hk0 hk1
    induction k, hk0 using Nat.le_induction with
    | base => rfl
    | succ k hk0 ih =>
      have hk_eq : σ.eventTime v lookahead k = t :=
        le_antisymm (hbefore k (Nat.lt_of_succ_le hk1))
          (le_trans hge (σ.eventTime_mono v lookahead hk0))
      rw [σ.views_append_remAll_step v lookahead h t hk_eq, ih (Nat.le_of_succ_le hk1)]
  have h1 := hcons n₁ hle le_rfl
  rw [σ.remAll_eq_nil_of_lt_eventTime v lookahead h t hgt, List.append_nil] at h1
  exact h1

/-- Every in-flight message at step `n` was delivered by `v.network.deliver`. -/
theorem Solution.inFlight_delivered [DecidableEq H] (σ : Solution H R Msg) (v : World H R)
    (lookahead : ℕ+) (n : ℕ) {m : InFlight H Msg} (hm : m ∈ (σ.states v lookahead n).inFlight) :
    ∃ s q, v.network.deliver m.origin m.destination s q = some m.arrival := by
  induction n generalizing m with
  | zero => simp [Solution.states, State.start] at hm
  | succ n ih =>
    have hsend : ∀ (st : State H R Msg) (h₀ : H) (s : Time) (j : H) (c : Msg) (F : Finset ℕ)
        {m : InFlight H Msg},
        m ∈ (st.send v h₀ s j c F).inFlight →
        m ∈ st.inFlight ∨ ∃ s' q', v.network.deliver m.origin m.destination s' q' = some m.arrival := by
      intro st h₀ s j c F m' hm'
      simp only [State.send] at hm'
      cases hd : v.network.deliver h₀ j s (st.sentCount h₀ j) with
      | none => simp [hd] at hm'; exact Or.inl hm'
      | some a =>
        simp only [hd, List.mem_append, List.mem_singleton] at hm'
        rcases hm' with hm' | rfl
        · exact Or.inl hm'
        · exact Or.inr ⟨s, st.sentCount h₀ j, hd⟩
    have hsendAll : ∀ (sends : List (H × Msg × Finset ℕ)) (st : State H R Msg)
        (h₀ : H) (s : Time) (held : Finset ℕ) {m : InFlight H Msg},
        m ∈ (st.sendAll v h₀ s held sends).inFlight →
        m ∈ st.inFlight ∨ ∃ s' q', v.network.deliver m.origin m.destination s' q' = some m.arrival := by
      intro sends
      induction sends with
      | nil => intro st _ _ _ _ hm'; exact Or.inl hm'
      | cons x xs ihs =>
        intro st h₀ s held m' hm'
        simp only [State.sendAll, List.foldl_cons] at hm'
        rcases ihs _ h₀ s held hm' with hm1 | hex
        · exact hsend st h₀ s x.1 x.2.1 _ hm1
        · exact Or.inr hex
    have hstep_m : m ∈ (σ.states v lookahead n).inFlight
        ∨ ∃ s' q', v.network.deliver m.origin m.destination s' q' = some m.arrival := by
      have hhandle_m : ∀ (st₀ : State H R Msg) (h₀ : H) (s : Time) (obs : Observation H R Msg),
          m ∈ (st₀.handle σ v lookahead h₀ s obs).inFlight →
          m ∈ st₀.inFlight ∨ ∃ s' q', v.network.deliver m.origin m.destination s' q' = some m.arrival := by
        intro st₀ h₀ s obs hm'
        have := hsendAll _
          { st₀ with
            views := Function.update st₀.views h₀ (st₀.views h₀ ++ [⟨(v.clock h₀).read s, obs⟩])
            held := Function.update st₀.held h₀ (st₀.held h₀ ∪ obs.frames) }
          h₀ s (st₀.held h₀ ∪ obs.frames) hm'
        simpa using this
      change m ∈ ((σ.states v lookahead n).step σ v lookahead).inFlight at hm
      unfold State.step at hm
      split at hm
      · exact hhandle_m _ _ _ _ hm
      · exact hhandle_m _ _ _ _ hm
      · split at hm
        · rcases hhandle_m _ _ _ _ hm with hm1 | hex
          · exact Or.inl (List.mem_of_mem_eraseIdx hm1)
          · exact Or.inr hex
        · exact Or.inl hm
      · split at hm
        · exact hhandle_m { σ.states v lookahead n with
            timers := (σ.states v lookahead n).timers.eraseIdx _ } _ _ _ hm
        · exact Or.inl hm
      · exact Or.inl hm
    rcases hstep_m with hm1 | hex
    · exact ih hm1
    · exact hex

private theorem list_prefix_eq_of_not_mem {α : Type} {l₁ l₂ l₁' l₂' : List α} {e : α}
    (h1 : e ∉ l₁) (h1' : e ∉ l₁') (heq : l₁ ++ e :: l₂ = l₁' ++ e :: l₂') : l₁ = l₁' := by
  induction l₁ generalizing l₁' with
  | nil =>
    cases l₁' with
    | nil => rfl
    | cons a rest =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      exact absurd (heq.1 ▸ List.mem_cons_self) h1'
  | cons a rest ih =>
    cases l₁' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      exact absurd (heq.1.symm ▸ List.mem_cons_self) h1
    | cons b rest' =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, hrest⟩ := heq
      congr 1
      exact ih (fun hm => h1 (List.mem_cons_of_mem _ hm))
        (fun hm => h1' (List.mem_cons_of_mem _ hm)) hrest

/-- No two in-flight messages from distinct origins in `σ`'s run on `w` arrive at
the same host at the exact same true time. This prevents arrival-tie reordering
when host timelines are shifted; it holds almost surely under any continuous
delay distribution. -/
def Solution.NoCrossOriginCollision [DecidableEq H] (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) : Prop :=
  ∀ n (m₁ m₂ : InFlight H Msg),
    m₁ ∈ (σ.states w lookahead n).inFlight →
    m₂ ∈ (σ.states w lookahead n).inFlight →
    m₁.destination = m₂.destination →
    m₁.arrival = m₂.arrival →
    m₁.origin = m₂.origin

/-- **Host-local view invariance under host shifts (no `horder` assumption).**
Assume non-Zeno progress in both `w` and `w' = w.shiftHosts Δ hnet` (with
`Δ w.sender = 0`), and that no two in-flight messages from distinct origins in
`w` arrive at the same host at the exact same instant
(`σ.NoCrossOriginCollision w lookahead`). Then every host observes the
identical sequence of local events up to `w`-time `t` in `w` and up to
`w'`-time `t + Δ h` in `w'` — even with drifting clocks and changed cross-host
interleavings — and `σ` produces identical playback decisions
`σ.plays w' lookahead = σ.plays w lookahead`. -/
theorem Solution.plays_shiftHosts [DecidableEq H] (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (Δ : H → ℝ) (hΔs : Δ w.sender = 0)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hprog₁ : ∀ T : Time, ∃ n, T < σ.eventTime w lookahead n)
    (hprog₂ : ∀ T : Time, ∃ n, T < σ.eventTime (w.shiftHosts Δ hnet) lookahead n)
    (harr : σ.NoCrossOriginCollision w lookahead) :
    σ.plays (w.shiftHosts Δ hnet) lookahead = σ.plays w lookahead := by
  classical
  set w' := w.shiftHosts Δ hnet with hw'
  let firstGe (v : World H R) (hp : ∀ T, ∃ n, T < σ.eventTime v lookahead n) (t : Time) : ℕ :=
    Nat.find (let ⟨n, hn⟩ := hp t; ⟨n, hn.le⟩)
  let firstGt (v : World H R) (hp : ∀ T, ∃ n, T < σ.eventTime v lookahead n) (t : Time) : ℕ :=
    Nat.find (hp t)
  have hGe_spec : ∀ v hp t, t ≤ σ.eventTime v lookahead (firstGe v hp t) :=
    fun v hp t => Nat.find_spec (let ⟨n, hn⟩ := hp t; ⟨n, hn.le⟩)
  have hGe_lt : ∀ v hp t k, k < firstGe v hp t → σ.eventTime v lookahead k < t :=
    fun v hp t k hk => not_le.mp (Nat.find_min (let ⟨n, hn⟩ := hp t; ⟨n, hn.le⟩) hk)
  have hGt_spec : ∀ v hp t, t < σ.eventTime v lookahead (firstGt v hp t) :=
    fun v hp t => Nat.find_spec (hp t)
  have hGt_le : ∀ v hp t k, k < firstGt v hp t → σ.eventTime v lookahead k ≤ t :=
    fun v hp t k hk => not_lt.mp (Nat.find_min (hp t) hk)
  have hGe_le_Gt : ∀ v hp t, firstGe v hp t ≤ firstGt v hp t := fun v hp t =>
    Nat.find_min' (let ⟨n, hn⟩ := hp t; ⟨n, hn.le⟩) (hGt_spec v hp t).le
  -- Uniform upper bound on `Δ h` across all hosts `h : H`.
  let Δmax : ℝ := ((List.finRange R).map (fun r => Δ (w.host r))).foldl max 0
  have hΔ_le : ∀ h : H, Δ h ≤ Δmax := by
    have hfold_ge : ∀ (l : List ℝ) (init : ℝ), init ≤ l.foldl max init
        ∧ ∀ x ∈ l, x ≤ l.foldl max init := by
      intro l
      induction l with
      | nil => intro init; exact ⟨le_rfl, by simp⟩
      | cons a rest ih =>
        intro init
        simp only [List.foldl_cons]
        obtain ⟨h1, h2⟩ := ih (max init a)
        refine ⟨le_trans (le_max_left init a) h1, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_trans (le_max_right init x) h1
        · exact h2 x hx
    intro h
    rcases w.hosts h with rfl | ⟨r, rfl⟩
    · rw [hΔs]; exact (hfold_ge _ 0).1
    · exact (hfold_ge _ 0).2 _ (List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩)
  -- Key step: if `views h` match strictly before `t` for every `h`, then `views h` match through `t`.
  have hstep_at : ∀ t : Time,
      (∀ h, (σ.states w' lookahead (firstGe w' hprog₂ (t + Δ h))).views h
          = (σ.states w lookahead (firstGe w hprog₁ t)).views h) →
      ∀ h, (σ.states w' lookahead (firstGt w' hprog₂ (t + Δ h))).views h
          = (σ.states w lookahead (firstGt w hprog₁ t)).views h := by
    intro t hbefore_eq h
    rw [σ.views_eq_append_remAll w' lookahead h (t + Δ h) (hGe_le_Gt w' hprog₂ _)
          (hGe_spec w' hprog₂ _) (hGt_spec w' hprog₂ _) (hGt_le w' hprog₂ _),
        σ.views_eq_append_remAll w lookahead h t (hGe_le_Gt w hprog₁ _)
          (hGe_spec w hprog₁ _) (hGt_spec w hprog₁ _) (hGt_le w hprog₁ _),
        hbefore_eq h]
    congr 1
    set n₁ := firstGe w hprog₁ t
    set n₂ := firstGe w' hprog₂ (t + Δ h)
    have hH_eq : remHanded w' h (t + Δ h) (σ.states w' lookahead n₂)
        = remHanded w h t (σ.states w lookahead n₁) := by
      unfold remHanded
      by_cases hs : h = w.sender
      · subst hs
        have hw's : w'.sender = w.sender := rfl
        have hw'src : w'.source = w.source := rfl
        have hw'tgt : w'.target = w.target := rfl
        have hclk : (w'.clock w.sender).read t = (w.clock w.sender).read t := by
          simp [w', World.shiftHosts, hΔs]
        simp only [hw's, hw'src, hw'tgt, hΔs, add_zero, true_and, hclk]
        have hiff : ∀ (v : World H R) (hp : ∀ T, ∃ n, T < σ.eventTime v lookahead n),
            v.source = w.source →
            (w.source.handed (σ.states v lookahead (firstGe v hp t)).handedNext = t
              ↔ ∃ b, w.source.handed b = t) := by
          intro v hp hsrc
          constructor
          · intro hb; exact ⟨_, hb⟩
          · rintro ⟨b, hb⟩
            have hge_b : b ≤ (σ.states v lookahead (firstGe v hp t)).handedNext := by
              by_contra hlt
              have hdue := (σ.eventTime_dueFrom v lookahead (firstGe v hp t)).1
              rw [hsrc] at hdue
              linarith [w.source.handed_strictMono (not_le.mp hlt), hGe_spec v hp t]
            have hle_b : (σ.states v lookahead (firstGe v hp t)).handedNext ≤ b := by
              by_contra hgt
              obtain ⟨k, hk, _, hearly⟩ := σ.exists_handed_step v lookahead (not_le.mp hgt)
              have hkt : σ.eventTime v lookahead k = t := by
                simp only [Solution.eventTime, hearly, State.key, hsrc, hb]
              linarith [hGe_lt v hp t k hk]
            rw [le_antisymm hle_b hge_b, hb]
        by_cases hex : ∃ b, w.source.handed b = t
        · have hb1 : w.source.handed (σ.states w lookahead n₁).handedNext = t :=
            (hiff w hprog₁ rfl).mpr hex
          have hb2 : w.source.handed (σ.states w' lookahead n₂).handedNext = t := by
            have hn2 : n₂ = firstGe w' hprog₂ t := by simp [n₂, hΔs]
            rw [hn2]; exact (hiff w' hprog₂ rfl).mpr hex
          have heq_b := w.source.handed_strictMono.injective (hb2.trans hb1.symm)
          simp [hb1, heq_b]
        · have hb1 : w.source.handed (σ.states w lookahead n₁).handedNext ≠ t :=
            fun h' => hex ⟨_, h'⟩
          have hb2 : w.source.handed (σ.states w' lookahead n₂).handedNext ≠ t :=
            fun h' => hex ⟨_, h'⟩
          simp [hb1, hb2]
      · have hw's : h ≠ w'.sender := hs
        simp [hs, hw's]
    have hQ_eq : remAsked w' h (t + Δ h) (σ.states w' lookahead n₂)
        = remAsked w h t (σ.states w lookahead n₁) := by
      unfold remAsked
      refine List.filterMap_congr fun r _ => ?_
      by_cases hr : w.host r = h
      · have hw'hr : w'.host r = h := hr
        have hclk : (w'.clock h).read (t + Δ h) = (w.clock h).read t := by simp [w', World.shiftHosts]
        have hspk_asked : ∀ b, (w'.speaker r).asked b = (w.speaker r).asked b + Δ h := fun b => by
          simp [w', World.shiftHosts, hr]
        have hspk_block : (w'.speaker r).block = (w.speaker r).block := rfl
        have hspk_rep : (w'.speaker r).reported = (w.speaker r).reported := rfl
        simp only [hr, hw'hr, hclk, hspk_asked, add_right_cancel_iff, hspk_block, hspk_rep, true_and]
        have hiff1 : (w.speaker r).asked ((σ.states w lookahead n₁).askedNext r) = t
            ↔ ∃ b, (w.speaker r).asked b = t := by
          constructor
          · intro hb; exact ⟨_, hb⟩
          · rintro ⟨b, hb⟩
            have hge_b : b ≤ (σ.states w lookahead n₁).askedNext r := by
              by_contra hlt
              have hdue := (σ.eventTime_dueFrom w lookahead n₁).2.1 r
              linarith [(w.speaker r).asked_strictMono (not_le.mp hlt), hGe_spec w hprog₁ t]
            have hle_b : (σ.states w lookahead n₁).askedNext r ≤ b := by
              by_contra hgt
              obtain ⟨k, hk, _, hearly⟩ := σ.exists_asked_step w lookahead (not_le.mp hgt)
              have hkt : σ.eventTime w lookahead k = t := by
                simp only [Solution.eventTime, hearly, State.key, hb]
              linarith [hGe_lt w hprog₁ t k hk]
            rw [le_antisymm hle_b hge_b, hb]
        have hiff2 : (w.speaker r).asked ((σ.states w' lookahead n₂).askedNext r) = t
            ↔ ∃ b, (w.speaker r).asked b = t := by
          constructor
          · intro hb; exact ⟨_, hb⟩
          · rintro ⟨b, hb⟩
            have hge_b : b ≤ (σ.states w' lookahead n₂).askedNext r := by
              by_contra hlt
              have hdue := (σ.eventTime_dueFrom w' lookahead n₂).2.1 r
              rw [hspk_asked] at hdue
              linarith [(w.speaker r).asked_strictMono (not_le.mp hlt), hGe_spec w' hprog₂ (t + Δ h)]
            have hle_b : (σ.states w' lookahead n₂).askedNext r ≤ b := by
              by_contra hgt
              obtain ⟨k, hk, _, hearly⟩ := σ.exists_asked_step w' lookahead (not_le.mp hgt)
              have hkt : σ.eventTime w' lookahead k = t + Δ h := by
                simp only [Solution.eventTime, hearly, State.key, hspk_asked, hb]
              linarith [hGe_lt w' hprog₂ (t + Δ h) k hk]
            rw [le_antisymm hle_b hge_b, hb]
        by_cases hex : ∃ b, (w.speaker r).asked b = t
        · have hb1 := hiff1.mpr hex
          have hb2 := hiff2.mpr hex
          have heq_b := (w.speaker r).asked_strictMono.injective (hb2.trans hb1.symm)
          simp [hb1, heq_b]
        · have hb1 : (w.speaker r).asked ((σ.states w lookahead n₁).askedNext r) ≠ t :=
            fun h' => hex ⟨_, h'⟩
          have hb2 : (w.speaker r).asked ((σ.states w' lookahead n₂).askedNext r) ≠ t :=
            fun h' => hex ⟨_, h'⟩
          simp [hb1, hb2]
      · have hw'hr : w'.host r ≠ h := hr
        simp [hr, hw'hr]
    have hA_eq : remArrivals w' h (t + Δ h) (σ.states w' lookahead n₂)
        = remArrivals w h t (σ.states w lookahead n₁) := by
      have hOriginEq : ∀ i : H,
          filterOriginArrivals w' i h (t + Δ h) (σ.states w' lookahead n₂).inFlight
            = filterOriginArrivals w i h t (σ.states w lookahead n₁).inFlight := by
        intro i
        rw [(σ.inFlight_origin_at_eq w lookahead i h t (hGe_lt w hprog₁ t)).2,
          (σ.inFlight_origin_at_eq w' lookahead i h (t + Δ h) (hGe_lt w' hprog₂ (t + Δ h))).2]
        set n₂' := firstGe w' hprog₂ (t + Δ i)
        have halign : (sentArrivalsFromView σ w' i h (t + Δ h) ((σ.states w' lookahead n₂).views i)).2
            = (sentArrivalsFromView σ w' i h (t + Δ h) ((σ.states w' lookahead n₂').views i)).2 := by
          rcases le_total n₂' n₂ with hle | hle
          · obtain ⟨extra, hextra, hev⟩ := σ.views_append w' lookahead hle i
            rw [hextra]
            refine sentArrivalsFromView_append_no_deliver σ w' i h (t + Δ h) _ extra fun e he s hta q hdel => ?_
            obtain ⟨k, hk1, _, s', obs, hhk, rfl⟩ := hev e he
            have hse : s = s' := (w'.clock i).strictMono.injective (Clock.read_timeAt hta)
            subst hse
            have hs_ge : t + Δ i ≤ s := le_trans (hGe_spec w' hprog₂ (t + Δ i))
              ((σ.handled_time w' lookahead hhk) ▸ σ.eventTime_mono w' lookahead hk1)
            simp only [w', World.shiftHosts, Option.map_eq_some_iff] at hdel
            rcases hdel with ⟨a, ha, haeq⟩
            have hat : a = t := add_right_cancel haeq
            rw [hat] at ha
            have := w.network.after i h (s - Δ i) q t ha
            linarith
          · obtain ⟨extra, hextra, hev⟩ := σ.views_append w' lookahead hle i
            rw [hextra]
            symm
            refine sentArrivalsFromView_append_no_deliver σ w' i h (t + Δ h) _ extra fun e he s hta q hdel => ?_
            obtain ⟨k, hk1, _, s', obs, hhk, rfl⟩ := hev e he
            have hse : s = s' := (w'.clock i).strictMono.injective (Clock.read_timeAt hta)
            subst hse
            have hs_ge : t + Δ h ≤ s := le_trans (hGe_spec w' hprog₂ (t + Δ h))
              ((σ.handled_time w' lookahead hhk) ▸ σ.eventTime_mono w' lookahead hk1)
            have := w'.network.after i h s q (t + Δ h) hdel
            linarith
        rw [halign, hbefore_eq i, sentArrivalsFromView_shiftHosts]
      have hExistsInW : ∀ m ∈ (σ.states w' lookahead n₂).inFlight,
          m.destination = h → m.arrival = t + Δ h →
          ∃ m₁ ∈ (σ.states w lookahead n₁).inFlight,
            m₁.origin = m.origin ∧ m₁.destination = h ∧ m₁.arrival = t := by
        intro m hm hd ha
        have hne' : filterOriginArrivals w' m.origin h (t + Δ h)
            (σ.states w' lookahead n₂).inFlight ≠ [] := by
          intro hnil
          have hnone := List.filterMap_eq_nil_iff.mp hnil m hm
          simp [hd, ha] at hnone
        rw [hOriginEq m.origin] at hne'
        cases hlst : filterOriginArrivals w m.origin h t (σ.states w lookahead n₁).inFlight with
        | nil => exact absurd hlst hne'
        | cons e _ =>
          have hmem : e ∈ filterOriginArrivals w m.origin h t (σ.states w lookahead n₁).inFlight := by
            rw [hlst]; simp
          unfold filterOriginArrivals at hmem
          rw [List.mem_filterMap] at hmem
          obtain ⟨m₁, hm₁, hsome⟩ := hmem
          split_ifs at hsome with hcond
          exact ⟨m₁, hm₁, hcond.1, hcond.2.1, hcond.2.2⟩
      by_cases hex : ∃ m₀ ∈ (σ.states w lookahead n₁).inFlight,
          m₀.destination = h ∧ m₀.arrival = t
      · obtain ⟨m₀, hm₀, hd₀, ha₀⟩ := hex
        have huniq1 : remArrivals w h t (σ.states w lookahead n₁)
            = filterOriginArrivals w m₀.origin h t (σ.states w lookahead n₁).inFlight := by
          unfold remArrivals filterOriginArrivals
          refine List.filterMap_congr fun m hm => ?_
          by_cases hcond : m.destination = h ∧ m.arrival = t
          · obtain ⟨hmd, hma⟩ := hcond
            have hi_eq : m.origin = m₀.origin :=
              harr n₁ m m₀ hm hm₀ (hmd.trans hd₀.symm) (hma.trans ha₀.symm)
            simp [hi_eq, hmd, hma]
          · simp [hcond]
        have huniq2 : remArrivals w' h (t + Δ h) (σ.states w' lookahead n₂)
            = filterOriginArrivals w' m₀.origin h (t + Δ h) (σ.states w' lookahead n₂).inFlight := by
          unfold remArrivals filterOriginArrivals
          refine List.filterMap_congr fun m hm => ?_
          by_cases hcond : m.destination = h ∧ m.arrival = t + Δ h
          · obtain ⟨hmd, hma⟩ := hcond
            obtain ⟨m₁, hm₁, ho₁, hd₁, ha₁⟩ := hExistsInW m hm hmd hma
            have hi_eq : m.origin = m₀.origin :=
              ho₁.symm.trans (harr n₁ m₁ m₀ hm₁ hm₀ (hd₁.trans hd₀.symm) (ha₁.trans ha₀.symm))
            simp [hi_eq, hmd, hma]
          · simp [hcond]
        rw [huniq1, huniq2, hOriginEq m₀.origin]
      · have hnil1 : remArrivals w h t (σ.states w lookahead n₁) = [] := by
          unfold remArrivals
          rw [List.filterMap_eq_nil_iff]
          intro m hm
          by_cases hcond : m.destination = h ∧ m.arrival = t
          · exact absurd ⟨m, hm, hcond.1, hcond.2⟩ hex
          · simp [hcond]
        have hnil2 : remArrivals w' h (t + Δ h) (σ.states w' lookahead n₂) = [] := by
          unfold remArrivals
          rw [List.filterMap_eq_nil_iff]
          intro m hm
          by_cases hcond : m.destination = h ∧ m.arrival = t + Δ h
          · obtain ⟨m₁, hm₁, _, hd₁, ha₁⟩ := hExistsInW m hm hcond.1 hcond.2
            exact absurd ⟨m₁, hm₁, hd₁, ha₁⟩ hex
          · simp [hcond]
        rw [hnil1, hnil2]
    have hT_eq : remTimers w' h (t + Δ h) (σ.states w' lookahead n₂)
        = remTimers w h t (σ.states w lookahead n₁) := by
      unfold remTimers
      rw [σ.timers_countP_at_eq w' lookahead h (t + Δ h) (hGe_lt w' hprog₂ (t + Δ h)),
        σ.timers_countP_at_eq w lookahead h t (hGe_lt w hprog₁ t)]
      have hclk : (w'.clock h).read (t + Δ h) = (w.clock h).read t := by simp [w', World.shiftHosts]
      rw [hclk, hbefore_eq h]
    unfold remAll
    rw [hH_eq, hQ_eq, hA_eq, hT_eq]
  -- Core theorem: for any horizon `T`, local views up to `t` match for every `t ≤ T`.
  have hviews_eq : ∀ (T t : Time), t ≤ T →
      ∀ h, (σ.states w' lookahead (firstGt w' hprog₂ (t + Δ h))).views h
        = (σ.states w lookahead (firstGt w hprog₁ t)).views h := by
    intro T
    let M₁ := firstGt w hprog₁ T
    let M₂ := firstGt w' hprog₂ (T + Δmax)
    let S₁ : Finset ℝ := ((Finset.range M₁).image (fun k => σ.eventTime w lookahead k)).filter (· ≤ T)
    let S₂ : Finset ℝ :=
      ((Finset.range M₂).image fun k =>
        match σ.handled w' lookahead k with
        | some (h, s', _) => s' - Δ h
        | none => T + 1).filter (· ≤ T)
    let S : Finset ℝ := S₁ ∪ S₂
    have hgap_w : ∀ a b h, a < b → b ≤ T → (∀ s ∈ S, ¬ (a < s ∧ s < b)) →
        (σ.states w lookahead (firstGe w hprog₁ b)).views h
          = (σ.states w lookahead (firstGt w hprog₁ a)).views h := by
      intro a b h hab hbT hnone
      have hle_step : firstGt w hprog₁ a ≤ firstGe w hprog₁ b := by
        by_contra hlt
        linarith [hGe_spec w hprog₁ b, hGt_le w hprog₁ a _ (not_le.mp hlt)]
      obtain ⟨l, hl, hev⟩ := σ.views_append w lookahead hle_step h
      have hl_nil : l = [] := by
        cases l with
        | nil => rfl
        | cons e _ =>
          exfalso
          obtain ⟨i, hi1, hi2, s, obs, hhi, _⟩ := hev e (by simp)
          have hsi : σ.eventTime w lookahead i = s := σ.handled_time w lookahead hhi
          have hsa : a < s := lt_of_lt_of_le (hGt_spec w hprog₁ a) (hsi ▸ σ.eventTime_mono w lookahead hi1)
          have hsb : s < b := hsi ▸ hGe_lt w hprog₁ b i hi2
          have hiM₁ : i < M₁ := by
            by_contra hge
            have := lt_of_lt_of_le (hGt_spec w hprog₁ T) (hsi ▸ σ.eventTime_mono w lookahead (not_lt.mp hge))
            linarith
          have hsS : s ∈ S := by
            apply Finset.mem_union_left
            rw [Finset.mem_filter, Finset.mem_image]
            exact ⟨⟨i, Finset.mem_range.mpr hiM₁, hsi⟩, le_trans hsb.le hbT⟩
          exact hnone s hsS ⟨hsa, hsb⟩
      rw [hl, hl_nil, List.append_nil]
    have hgap_w' : ∀ a b h, a < b → b ≤ T → (∀ s ∈ S, ¬ (a < s ∧ s < b)) →
        (σ.states w' lookahead (firstGe w' hprog₂ (b + Δ h))).views h
          = (σ.states w' lookahead (firstGt w' hprog₂ (a + Δ h))).views h := by
      intro a b h hab hbT hnone
      have hle_step : firstGt w' hprog₂ (a + Δ h) ≤ firstGe w' hprog₂ (b + Δ h) := by
        by_contra hlt
        linarith [hGe_spec w' hprog₂ (b + Δ h), hGt_le w' hprog₂ (a + Δ h) _ (not_le.mp hlt)]
      obtain ⟨l, hl, hev⟩ := σ.views_append w' lookahead hle_step h
      have hl_nil : l = [] := by
        cases l with
        | nil => rfl
        | cons e _ =>
          exfalso
          obtain ⟨i, hi1, hi2, s', obs, hhi, _⟩ := hev e (by simp)
          have hsi : σ.eventTime w' lookahead i = s' := σ.handled_time w' lookahead hhi
          have hsa : a < s' - Δ h := by
            have := lt_of_lt_of_le (hGt_spec w' hprog₂ (a + Δ h)) (hsi ▸ σ.eventTime_mono w' lookahead hi1)
            linarith
          have hsb : s' - Δ h < b := by
            have := hsi ▸ hGe_lt w' hprog₂ (b + Δ h) i hi2
            linarith
          have hiM₂ : i < M₂ := by
            by_contra hge
            have := lt_of_lt_of_le (hGt_spec w' hprog₂ (T + Δmax))
              (hsi ▸ σ.eventTime_mono w' lookahead (not_lt.mp hge))
            linarith [hΔ_le h]
          have hsS : s' - Δ h ∈ S := by
            apply Finset.mem_union_right
            rw [Finset.mem_filter, Finset.mem_image]
            exact ⟨⟨i, Finset.mem_range.mpr hiM₂, by simp [hhi]⟩, le_trans hsb.le hbT⟩
          exact hnone (s' - Δ h) hsS ⟨hsa, hsb⟩
      rw [hl, hl_nil, List.append_nil]
    have hzero_w : ∀ t h, t ≤ T → S.filter (· < t) = ∅ →
        (σ.states w lookahead (firstGe w hprog₁ t)).views h = [] := by
      intro t h htT hempty
      obtain ⟨l, hl, hev⟩ := σ.views_append w lookahead (Nat.zero_le (firstGe w hprog₁ t)) h
      simp only [Solution.states, State.start, List.nil_append] at hl
      cases l with
      | nil => exact hl
      | cons e _ =>
        exfalso
        obtain ⟨i, _, hi2, s, obs, hhi, _⟩ := hev e (by simp)
        have hsi : σ.eventTime w lookahead i = s := σ.handled_time w lookahead hhi
        have hst : s < t := hsi ▸ hGe_lt w hprog₁ t i hi2
        have hiM₁ : i < M₁ := by
          by_contra hge
          have := lt_of_lt_of_le (hGt_spec w hprog₁ T) (hsi ▸ σ.eventTime_mono w lookahead (not_lt.mp hge))
          linarith
        have hsS : s ∈ S.filter (· < t) := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_union_left _ ?_, hst⟩
          rw [Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨i, Finset.mem_range.mpr hiM₁, hsi⟩, le_trans hst.le htT⟩
        rw [hempty] at hsS
        exact Finset.notMem_empty s hsS
    have hzero_w' : ∀ t h, t ≤ T → S.filter (· < t) = ∅ →
        (σ.states w' lookahead (firstGe w' hprog₂ (t + Δ h))).views h = [] := by
      intro t h htT hempty
      obtain ⟨l, hl, hev⟩ := σ.views_append w' lookahead (Nat.zero_le (firstGe w' hprog₂ (t + Δ h))) h
      simp only [Solution.states, State.start, List.nil_append] at hl
      cases l with
      | nil => exact hl
      | cons e _ =>
        exfalso
        obtain ⟨i, _, hi2, s', obs, hhi, _⟩ := hev e (by simp)
        have hsi : σ.eventTime w' lookahead i = s' := σ.handled_time w' lookahead hhi
        have hst : s' - Δ h < t := by
          have := hsi ▸ hGe_lt w' hprog₂ (t + Δ h) i hi2
          linarith
        have hiM₂ : i < M₂ := by
          by_contra hge
          have := lt_of_lt_of_le (hGt_spec w' hprog₂ (T + Δmax))
            (hsi ▸ σ.eventTime_mono w' lookahead (not_lt.mp hge))
          linarith [hΔ_le h]
        have hsS : s' - Δ h ∈ S.filter (· < t) := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_union_right _ ?_, hst⟩
          rw [Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨i, Finset.mem_range.mpr hiM₂, by simp [hhi]⟩, le_trans hst.le htT⟩
        rw [hempty] at hsS
        exact Finset.notMem_empty _ hsS
    suffices hind : ∀ m : ℕ, ∀ t ≤ T, (S.filter (· < t)).card ≤ m →
        ∀ h, (σ.states w' lookahead (firstGt w' hprog₂ (t + Δ h))).views h
          = (σ.states w lookahead (firstGt w hprog₁ t)).views h by
      intro t htT
      exact hind (S.filter (· < t)).card t htT le_rfl
    intro m
    induction m with
    | zero =>
      intro t htT hcard
      have hempty : S.filter (· < t) = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      exact hstep_at t fun h => by rw [hzero_w t h htT hempty, hzero_w' t h htT hempty]
    | succ m ih =>
      intro t htT hcard
      by_cases hne : (S.filter (· < t)).Nonempty
      · let t₀ := (S.filter (· < t)).max' hne
        have ht₀_mem : t₀ ∈ S.filter (· < t) := Finset.max'_mem _ hne
        have ht₀_lt : t₀ < t := (Finset.mem_filter.mp ht₀_mem).2
        have hsub : S.filter (· < t₀) ⊂ S.filter (· < t) := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro s hs
            rw [Finset.mem_filter] at hs ⊢
            exact ⟨hs.1, lt_trans hs.2 ht₀_lt⟩
          · intro heq
            have : t₀ ∈ S.filter (· < t₀) := heq ▸ ht₀_mem
            exact lt_irrefl t₀ (Finset.mem_filter.mp this).2
        have hcard₀ : (S.filter (· < t₀)).card ≤ m := by
          have := Finset.card_lt_card hsub
          omega
        have hih := ih t₀ (le_trans ht₀_lt.le htT) hcard₀
        have hno_between : ∀ s ∈ S, ¬ (t₀ < s ∧ s < t) := fun s hs ⟨h1, h2⟩ =>
          not_le.mpr h1 (Finset.le_max' (S.filter (· < t)) s (Finset.mem_filter.mpr ⟨hs, h2⟩))
        exact hstep_at t fun h => by
          rw [hgap_w t₀ t h ht₀_lt htT hno_between, hgap_w' t₀ t h ht₀_lt htT hno_between, hih h]
      · have hempty : S.filter (· < t) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        exact hstep_at t fun h => by rw [hzero_w t h htT hempty, hzero_w' t h htT hempty]
  -- Deduce `σ.plays w' lookahead r k = σ.plays w lookahead r k` for every speaker `r` and sample `k`.
  funext r k
  have hex_b : ∃ b, k < (w.speaker r).first (b + 1) := by
    refine ⟨k, ?_⟩
    have hle : k + 1 ≤ (w.speaker r).first (k + 1) := (w.speaker r).first_strictMono.id_le (k + 1)
    omega
  let b := Nat.find hex_b
  have hb_hi : k < (w.speaker r).first (b + 1) := Nat.find_spec hex_b
  have hb_lo : (w.speaker r).first b ≤ k := by
    cases hb0 : b with
    | zero => rw [(w.speaker r).first_zero]; exact Nat.zero_le k
    | succ b' =>
      have := Nat.find_min hex_b (show b' < b by omega)
      omega
  have hk_mem : k ∈ (w.speaker r).block b := by
    unfold PlaybackDevice.block
    rw [List.mem_range'_1]
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self b)
    omega
  let t := (w.speaker r).asked b
  let h := w.host r
  have hlt1 : b < (σ.states w lookahead (firstGt w hprog₁ t)).askedNext r :=
    σ.lt_askedNext w lookahead (hGt_spec w hprog₁ t)
  obtain ⟨na, hna_lt, hna_b, hna_early⟩ := σ.exists_asked_step w lookahead hlt1
  have hlt2 : b < (σ.states w' lookahead (firstGt w' hprog₂ (t + Δ h))).askedNext r := by
    apply σ.lt_askedNext w' lookahead
    have hsp : (w'.speaker r).asked b = t + Δ h := rfl
    rw [hsp]
    exact hGt_spec w' hprog₂ (t + Δ h)
  obtain ⟨na', hna'_lt, hna'_b, hna'_early⟩ := σ.exists_asked_step w' lookahead hlt2
  set ev : Event H R Msg :=
    ⟨(w.clock h).read t, .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩
  have hclk_eq : (w'.clock h).read ((w'.speaker r).asked b) = (w.clock h).read t := by
    simp [w', World.shiftHosts, t, h]
  have hsplit1 : ∃ l₂, (σ.states w lookahead (firstGt w hprog₁ t)).views h
      = (σ.states w lookahead na).views h ++ ev :: l₂ := by
    obtain ⟨l₂, hl₂, _⟩ := σ.views_append w lookahead (Nat.succ_le_of_lt hna_lt) h
    refine ⟨l₂, ?_⟩
    rw [hl₂, σ.views_succ w lookahead na h, σ.handled_of_asked w lookahead hna_early]
    simp [ev, h, t]
  have hsplit2 : ∃ l₂', (σ.states w' lookahead (firstGt w' hprog₂ (t + Δ h))).views h
      = (σ.states w' lookahead na').views h ++ ev :: l₂' := by
    obtain ⟨l₂', hl₂', _⟩ := σ.views_append w' lookahead (Nat.succ_le_of_lt hna'_lt) h
    refine ⟨l₂', ?_⟩
    rw [hl₂', σ.views_succ w' lookahead na' h, σ.handled_of_asked w' lookahead hna'_early]
    have hw'h : w'.host r = h := rfl
    have hw'blk : (w'.speaker r).block b = (w.speaker r).block b := rfl
    have hw'rep : (w'.speaker r).reported b = (w.speaker r).reported b := rfl
    simp [ev, hw'h, hw'blk, hw'rep, hclk_eq]
  have hnot1 : ev ∉ (σ.states w lookahead na).views h := by
    intro hmem
    obtain ⟨i, hi, s, obs, hhi, heq⟩ := σ.handled_of_mem_views w lookahead hmem
    simp only [ev, Event.mk.injEq] at heq
    obtain ⟨hread, rfl⟩ := heq
    have hs_eq : s = t := (w.clock h).strictMono.injective hread.symm
    have hearly_i := σ.handled_asked w lookahead hhi
    have hsi : (w.speaker r).asked ((σ.states w lookahead i).askedNext r) = t := by
      have ht_i := σ.handled_time w lookahead hhi
      simp only [Solution.eventTime, hearly_i, State.key] at ht_i
      linarith
    have hb_eq : (σ.states w lookahead i).askedNext r = b :=
      (w.speaker r).asked_strictMono.injective hsi
    have hsucc := σ.askedNext_succ w lookahead hearly_i
    have hmono := σ.askedNext_mono w lookahead r (Nat.lt_iff_add_one_le.mp hi)
    simp only at hmono
    omega
  have hnot2 : ev ∉ (σ.states w' lookahead na').views h := by
    intro hmem
    obtain ⟨i, hi, s', obs, hhi, heq⟩ := σ.handled_of_mem_views w' lookahead hmem
    simp only [ev, Event.mk.injEq] at heq
    obtain ⟨hread, rfl⟩ := heq
    have hs_eq : s' = t + Δ h := (w'.clock h).strictMono.injective (hread.symm.trans hclk_eq.symm)
    have hearly_i := σ.handled_asked w' lookahead hhi
    have hsi : (w'.speaker r).asked ((σ.states w' lookahead i).askedNext r) = (w'.speaker r).asked b := by
      have ht_i := σ.handled_time w' lookahead hhi
      simp only [Solution.eventTime, hearly_i, State.key] at ht_i
      exact ht_i.trans hs_eq
    have hb_eq : (σ.states w' lookahead i).askedNext r = b :=
      (w'.speaker r).asked_strictMono.injective hsi
    have hsucc := σ.askedNext_succ w' lookahead hearly_i
    have hmono := σ.askedNext_mono w' lookahead r (Nat.lt_iff_add_one_le.mp hi)
    simp only at hmono
    omega
  obtain ⟨l₂, hl₂⟩ := hsplit1
  obtain ⟨l₂', hl₂'⟩ := hsplit2
  have hveq : (σ.states w' lookahead na').views h = (σ.states w lookahead na).views h := by
    have hall := hviews_eq t t le_rfl h
    rw [hl₂, hl₂'] at hall
    exact list_prefix_eq_of_not_mem hnot2 hnot1 hall
  have hheq : (σ.states w' lookahead na').held h = (σ.states w lookahead na).held h := by
    rw [σ.held_eq_heldOfView w' lookahead na' h, σ.held_eq_heldOfView w lookahead na h, hveq]
  have hp1 := σ.plays_of_asked_step w lookahead hna_b hna_early hk_mem
  have hp2 := σ.plays_of_asked_step w' lookahead hna'_b hna'_early hk_mem
  rw [hp1, hp2]
  have hw'h : w'.host r = h := rfl
  have hw'blk : (w'.speaker r).block b = (w.speaker r).block b := rfl
  have hw'rep : (w'.speaker r).reported b = (w.speaker r).reported b := rfl
  simp only [hw'h, hw'blk, hw'rep, hclk_eq, hveq, hheq, h, t]

/-- **Synchronization lower bound under opposite host shifts (all topologies).**
For any solution `σ` (star or peer) that is non-Zeno in `w`, `w⁺ = w.shiftHosts Δ`,
and `w⁻ = w.shiftHosts (-Δ)` (with `Δ w.sender = 0`), when every link satisfies
`hnet₁`/`hnet₂`, no two messages from distinct origins arrive simultaneously at
the same host (`harr`), and every speaker plays all frames from `N` onward in `w`,
at least one of `w⁺` and `w⁻` suffers long-run synchronization cost at least
`varFin (fun r => Δ (w.host r))`. -/
theorem Solution.sync_shiftHosts_lower_bound [DecidableEq H] (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (Δ : H → ℝ) (hΔs : Δ w.sender = 0)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (hprog : ∀ T : Time, ∃ n, T < σ.eventTime w lookahead n)
    (hprog₁ : ∀ T : Time, ∃ n, T < σ.eventTime (w.shiftHosts Δ hnet₁) lookahead n)
    (hprog₂ : ∀ T : Time, ∃ n, T < σ.eventTime (w.shiftHosts (-Δ) hnet₂) lookahead n)
    (harr : σ.NoCrossOriginCollision w lookahead)
    (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime (σ.plays w lookahead) r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (varFin fun r => Δ (w.host r))
      ≤ max ((w.shiftHosts Δ hnet₁).sync (σ.plays (w.shiftHosts Δ hnet₁) lookahead))
            ((w.shiftHosts (-Δ) hnet₂).sync (σ.plays (w.shiftHosts (-Δ) hnet₂) lookahead)) := by
  have hp₁ := σ.plays_shiftHosts w lookahead Δ hΔs hnet₁ hprog hprog₁ harr
  have hp₂ := σ.plays_shiftHosts w lookahead (-Δ) (by simp [hΔs]) hnet₂ hprog hprog₂ harr
  rw [hp₁, hp₂]
  exact w.sync_shiftHosts_max_ge Δ hnet₁ hnet₂ (σ.plays w lookahead) hR N hplay hunb

/-- **Tracking lower bound under opposite uniform host shifts (all topologies).**
Under opposite uniform non-sender shifts `±A`, non-Zeno progress, and distinct
cross-origin arrival times, at least one of `w⁺` and `w⁻` suffers long-run
tracking cost at least `A²`. -/
theorem Solution.tracking_shiftHosts_lower_bound [DecidableEq H] (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (Δ : H → ℝ) (A : ℝ) (hΔs : Δ w.sender = 0)
    (hΔ : ∀ r, Δ (w.host r) = A)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (hprog : ∀ T : Time, ∃ n, T < σ.eventTime w lookahead n)
    (hprog₁ : ∀ T : Time, ∃ n, T < σ.eventTime (w.shiftHosts Δ hnet₁) lookahead n)
    (hprog₂ : ∀ T : Time, ∃ n, T < σ.eventTime (w.shiftHosts (-Δ) hnet₂) lookahead n)
    (harr : σ.NoCrossOriginCollision w lookahead)
    (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime (σ.plays w lookahead) r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (A ^ 2)
      ≤ max ((w.shiftHosts Δ hnet₁).tracking (σ.plays (w.shiftHosts Δ hnet₁) lookahead))
            ((w.shiftHosts (-Δ) hnet₂).tracking (σ.plays (w.shiftHosts (-Δ) hnet₂) lookahead)) := by
  have hp₁ := σ.plays_shiftHosts w lookahead Δ hΔs hnet₁ hprog hprog₁ harr
  have hp₂ := σ.plays_shiftHosts w lookahead (-Δ) (by simp [hΔs]) hnet₂ hprog hprog₂ harr
  rw [hp₁, hp₂]
  exact w.tracking_shiftHosts_max_ge Δ A hΔ hnet₁ hnet₂ (σ.plays w lookahead) hR N hplay hunb

end Unisono.Spec
