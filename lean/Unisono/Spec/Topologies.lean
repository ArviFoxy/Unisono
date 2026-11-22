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
# Communication topologies, modal objective decomposition, and star lower bounds

This file connects multi-speaker control and topology analysis directly to the
specification (`Unisono.Spec.World`, `Unisono.Spec.Solution`,
`Unisono.Spec.Objectives`).

* **Topologies (`Solution.UsesGraph`, `Solution.IsStar`).** A solution uses a
  directed communication graph `adj` when every message `(h → dst)` it ever
  sends satisfies `adj h dst`. A *star* solution restricts all communication to
  links incident on the sender (`h = sender ∨ dst = sender`). Peer (mesh)
  solutions additionally allow direct receiver-to-receiver messages.
* **Exact modal decomposition of `World` objectives.** For any frame played by
  all `R > 0` speakers, the speaker latencies `ℓ_r = T_r(n) - c(n)` split into
  their group mean (common mode `lbar`) and zero-mean deviations (differential
  mode `ℓ_r - lbar`):
  - `World.syncCost` depends purely on the differential mode
    (`World.syncCost_eq_var`).
  - `World.trackingCost` splits orthogonally into `syncCost` plus the squared
    common-mode tracking error `(lbar - target n)²`
    (`World.trackingCost_eq_sync_add_mean`).
  - Consequently, `c.sync * syncCost + c.tracking * trackingCost` weights the
    differential mode by `c.sync + c.tracking` and the common mode by
    `c.tracking` alone (`World.weighted_frame_modal_split`). In low-latency
    mode (`c.tracking = 0`), the common mode carries zero quadratic position
    penalty.
  - Per-speaker squared speed changes split identically into common-mode and
    differential-mode roughness (`modal_sq_split`).
* **Host-time shift invariance and the star asymmetry lower bound.** Shifting
  each host `h`'s timeline by `Δ h` (with `Δ sender = 0`) shifts outbound and
  inbound delays on link `(i, j)` by `Δ j - Δ i`, preserving every round-trip
  time while changing one-way delay asymmetries (`World.shiftHosts`). When a
  shift preserves the event selection order along the run, every host observes
  the exact same sequence of clock readings and messages, so the solution
  produces identical playback decisions (`Solution.plays_shiftHosts_of_earliest_eq`).
  Yet each speaker's true play time shifts by `Δ (host r)`
  (`World.playTime_shiftHosts`), forcing an unavoidable worst-case
  synchronization lower bound (`World.sync_shiftHosts_max_ge`) and tracking
  lower bound (`World.tracking_shiftHosts_max_ge`) directly on `World.sync`
  and `World.tracking`.
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
variance (differential mode). Applied to speed changes, this decomposes
speaker-averaged roughness orthogonally into common-mode and differential-mode
roughness. -/
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

/-! ## Host-time shift gauge transformation -/

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

/-- Two run states match under host shift `Δ` when all per-host views, device
counters, send counts, held frames, and playback decisions coincide, and every
in-flight message and timer is shifted by `Δ` of its destination/host. -/
def State.ShiftedEq (Δ : H → ℝ) (st st' : State H R Msg) : Prop :=
  st'.views = st.views
    ∧ st'.handedNext = st.handedNext
    ∧ st'.askedNext = st.askedNext
    ∧ st'.sentCount = st.sentCount
    ∧ st'.held = st.held
    ∧ st'.plays = st.plays
    ∧ st'.inFlight = st.inFlight.map (fun m => { m with arrival := m.arrival + Δ m.destination })
    ∧ st'.timers = st.timers.map (fun u => { u with time := u.time + Δ u.host })

theorem State.shiftedEq_start (Δ : H → ℝ) :
    State.ShiftedEq Δ (State.start : State H R Msg) State.start := by
  simp [State.ShiftedEq, State.start]

theorem State.shiftedEq_send [DecidableEq H] (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    {st st' : State H R Msg} (hs : State.ShiftedEq Δ st st')
    (h : H) (t : Time) (j : H) (contents : Msg) (frames : Finset ℕ) :
    State.ShiftedEq Δ (st.send w h t j contents frames)
      (st'.send (w.shiftHosts Δ hnet) h (t + Δ h) j contents frames) := by
  obtain ⟨hv, hhd, ha, hsc, hhe, hpl, hif, htm⟩ := hs
  refine ⟨hv, hhd, ha, ?_, hhe, hpl, ?_, htm⟩
  · simp [State.send, hsc]
  · simp only [State.send, World.shiftHosts, add_sub_cancel_right, hsc, hif]
    cases hd : w.network.deliver h j t (st.sentCount h j) with
    | none => simp
    | some a => simp

theorem State.shiftedEq_sendAll [DecidableEq H] (w : World H R) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    {st st' : State H R Msg} (hs : State.ShiftedEq Δ st st')
    (h : H) (t : Time) (held : Finset ℕ) (sends : List (H × Msg × Finset ℕ)) :
    State.ShiftedEq Δ (st.sendAll w h t held sends)
      (st'.sendAll (w.shiftHosts Δ hnet) h (t + Δ h) held sends) := by
  induction sends generalizing st st' with
  | nil => exact hs
  | cons m rest ih =>
    simp only [State.sendAll, List.foldl_cons]
    exact ih (State.shiftedEq_send w Δ hnet hs h t m.1 m.2.1 (m.2.2.filter (· ∈ held)))

theorem State.shiftedEq_handle [DecidableEq H] (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) (Δ : H → ℝ)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    {st st' : State H R Msg} (hs : State.ShiftedEq Δ st st')
    (h : H) (t : Time) (obs : Observation H R Msg) :
    State.ShiftedEq Δ (st.handle σ w lookahead h t obs)
      (st'.handle σ (w.shiftHosts Δ hnet) lookahead h (t + Δ h) obs) := by
  obtain ⟨hv, hhd, ha, hsc, hhe, hpl, hif, htm⟩ := hs
  have hread : ((w.shiftHosts Δ hnet).clock h).read (t + Δ h) = (w.clock h).read t := by
    simp [World.shiftHosts]
  have hbase : State.ShiftedEq Δ
      { st with
        views := Function.update st.views h (st.views h ++ [⟨(w.clock h).read t, obs⟩])
        held := Function.update st.held h (st.held h ∪ obs.frames) }
      { st' with
        views := Function.update st'.views h (st'.views h ++ [⟨(w.clock h).read t, obs⟩])
        held := Function.update st'.held h (st.held h ∪ obs.frames) } :=
    ⟨by rw [hv], hhd, ha, hsc, by rw [hhe], hpl, hif, htm⟩
  have hsend := State.shiftedEq_sendAll w Δ hnet hbase h t (st.held h ∪ obs.frames)
    (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).sends
  obtain ⟨hv', hhd', ha', hsc', hhe', hpl', hif', htm'⟩ := hsend
  have hview_eq : st'.views h ++ [⟨((w.shiftHosts Δ hnet).clock h).read (t + Δ h), obs⟩]
      = st'.views h ++ [⟨(w.clock h).read t, obs⟩] := by rw [hread]
  have hact_eq : σ h (st'.views h ++ [⟨(w.clock h).read t, obs⟩])
      = σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩]) := by rw [hv]
  have hheld_eq : st'.held h ∪ obs.frames = st.held h ∪ obs.frames := by rw [hhe]
  dsimp only [State.handle]
  rw [hview_eq, hact_eq, hheld_eq]
  refine ⟨hv', hhd', ha', hsc', hhe', ?_, hif', ?_⟩
  · cases obs with
    | handed _ _ => exact hpl'
    | asked r outputs reported =>
      funext r' k
      dsimp only
      split_ifs
      · rfl
      · exact congrFun (congrFun hpl' r') k
    | received _ _ _ => exact hpl'
    | timer => exact hpl'
  · rw [htm', hread, List.map_append]
    have htimers :
        List.filterMap
            (fun c => if (w.clock h).read t < c then
              Option.map (fun u => (⟨u, h⟩ : Timer H))
                (((w.shiftHosts Δ hnet).clock h).timeAt c)
              else none)
            (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).timers
          = List.map (fun u : Timer H => { u with time := u.time + Δ u.host })
            (List.filterMap
              (fun c => if (w.clock h).read t < c then
                Option.map (fun u => (⟨u, h⟩ : Timer H)) ((w.clock h).timeAt c)
                else none)
              (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).timers) := by
      induction (σ h (st.views h ++ [⟨(w.clock h).read t, obs⟩])).timers with
      | nil => simp
      | cons c cs ih =>
        simp only [List.filterMap_cons]
        split_ifs with hc
        · have hta : ((w.shiftHosts Δ hnet).clock h).timeAt c
              = ((w.clock h).timeAt c).map (· + Δ h) :=
            Clock.timeAt_shift (w.clock h) (Δ h) c
          rw [hta]
          cases (w.clock h).timeAt c with
          | none => simpa using ih
          | some u => simpa using ih
        · exact ih
    rw [htimers]

/-- If `w.shiftHosts Δ` preserves the `earliest` selection at every step of the
run, then every step maintains `State.ShiftedEq Δ` and the solution produces
**identical playback decisions** (`σ.plays (w.shiftHosts Δ) = σ.plays w`). -/
theorem Solution.plays_shiftHosts_of_earliest_eq [DecidableEq H] (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (Δ : H → ℝ) (hΔs : Δ w.sender = 0)
    (hnet : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (horder : ∀ n,
      earliest ((σ.states (w.shiftHosts Δ hnet) lookahead n).key (w.shiftHosts Δ hnet))
          (σ.states (w.shiftHosts Δ hnet) lookahead n).due
        = earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due) :
    (∀ n, State.ShiftedEq Δ (σ.states w lookahead n)
        (σ.states (w.shiftHosts Δ hnet) lookahead n))
      ∧ σ.plays (w.shiftHosts Δ hnet) lookahead = σ.plays w lookahead := by
  set w' := w.shiftHosts Δ hnet with hw'
  have hstates : ∀ n, State.ShiftedEq Δ (σ.states w lookahead n)
      (σ.states w' lookahead n) := by
    intro n
    induction n with
    | zero => exact State.shiftedEq_start Δ
    | succ n ih =>
      simp only [Solution.states, State.step]
      rw [horder n]
      cases he : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due with
      | none => exact ih
      | some d =>
        cases d with
        | handed b =>
          have hh := State.shiftedEq_handle σ w lookahead Δ hnet ih w.sender (w.source.handed b)
            (.handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))
          rw [hΔs, add_zero] at hh
          obtain ⟨hv, -, ha, hsc, hhe, hpl, hif, htm⟩ := hh
          exact ⟨hv, rfl, ha, hsc, hhe, hpl, hif, htm⟩
        | asked r b =>
          have hh := State.shiftedEq_handle σ w lookahead Δ hnet ih (w.host r)
            ((w.speaker r).asked b) (.asked r ((w.speaker r).block b) ((w.speaker r).reported b))
          obtain ⟨hv, hhd, -, hsc, hhe, hpl, hif, htm⟩ := hh
          refine ⟨hv, hhd, ?_, hsc, hhe, hpl, hif, htm⟩
          have ha' : (σ.states w' lookahead n).askedNext = (σ.states w lookahead n).askedNext :=
            ih.2.2.1
          simp [ha']
        | arrival p =>
          obtain ⟨hv, hhd, ha, hsc, hhe, hpl, hif, htm⟩ := ih
          have hget : (σ.states w' lookahead n).inFlight[p]?
              = ((σ.states w lookahead n).inFlight[p]?).map
                  (fun m => { m with arrival := m.arrival + Δ m.destination }) := by
            rw [hif, List.getElem?_map]
          dsimp only
          rw [hget]
          cases hm : (σ.states w lookahead n).inFlight[p]? with
          | none => exact ⟨hv, hhd, ha, hsc, hhe, hpl, hif, htm⟩
          | some m =>
            simp only [Option.map_some]
            have hbase : State.ShiftedEq Δ
                { σ.states w lookahead n with
                  inFlight := (σ.states w lookahead n).inFlight.eraseIdx p }
                { σ.states w' lookahead n with
                  inFlight := (σ.states w' lookahead n).inFlight.eraseIdx p } :=
              ⟨hv, hhd, ha, hsc, hhe, hpl, by rw [hif, List.eraseIdx_map], htm⟩
            exact State.shiftedEq_handle σ w lookahead Δ hnet hbase
              m.destination m.arrival (.received m.origin m.contents m.frames)
        | timer p =>
          obtain ⟨hv, hhd, ha, hsc, hhe, hpl, hif, htm⟩ := ih
          have hget : (σ.states w' lookahead n).timers[p]?
              = ((σ.states w lookahead n).timers[p]?).map
                  (fun u => { u with time := u.time + Δ u.host }) := by
            rw [htm, List.getElem?_map]
          dsimp only
          rw [hget]
          cases hu : (σ.states w lookahead n).timers[p]? with
          | none => exact ⟨hv, hhd, ha, hsc, hhe, hpl, hif, htm⟩
          | some u =>
            simp only [Option.map_some]
            have hbase : State.ShiftedEq Δ
                { σ.states w lookahead n with
                  timers := (σ.states w lookahead n).timers.eraseIdx p }
                { σ.states w' lookahead n with
                  timers := (σ.states w' lookahead n).timers.eraseIdx p } :=
              ⟨hv, hhd, ha, hsc, hhe, hpl, hif, by rw [htm, List.eraseIdx_map]⟩
            exact State.shiftedEq_handle σ w lookahead Δ hnet hbase u.host u.time .timer
  refine ⟨hstates, ?_⟩
  funext r k
  classical
  unfold Solution.plays
  have hfirst : (w'.speaker r).first = (w.speaker r).first := rfl
  have hcond : ∀ n, (k < (w'.speaker r).first ((σ.states w' lookahead n).askedNext r))
      ↔ (k < (w.speaker r).first ((σ.states w lookahead n).askedNext r)) := by
    intro n
    rw [hfirst, (hstates n).2.2.1]
  by_cases h2 : ∃ n, k < (w.speaker r).first ((σ.states w lookahead n).askedNext r)
  · have h1 : ∃ n, k < (w'.speaker r).first ((σ.states w' lookahead n).askedNext r) :=
      let ⟨n, hn⟩ := h2; ⟨n, (hcond n).mpr hn⟩
    rw [dite_eq_left h1, dite_eq_left h2]
    have hfind : Nat.find h1 = Nat.find h2 := by
      congr 1
      funext n
      exact propext (hcond n)
    rw [hfind, (hstates (Nat.find h2)).2.2.2.2.2.1]
  · have h1 : ¬ ∃ n, k < (w'.speaker r).first ((σ.states w' lookahead n).askedNext r) :=
      fun ⟨n, hn⟩ => h2 ⟨n, (hcond n).mp hn⟩
    rw [dite_eq_right h1, dite_eq_right h2]

/-- **Irreducible synchronization lower bound under indistinguishable host
shifts.** For any solution `σ` whose event-selection order is preserved by
opposite asymmetry shifts `±Δ` (with `Δ w.sender = 0`), `σ` produces the exact
same playback decisions in `w⁺ = w.shiftHosts Δ` and `w⁻ = w.shiftHosts (-Δ)`.
If every speaker plays all frames from some `N` onward, at least one of the
two worlds suffers long-run synchronization cost at least
`varFin (fun r => Δ (w.host r))`. -/
theorem Solution.sync_shiftHosts_lower_bound [DecidableEq H] (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (Δ : H → ℝ) (hΔs : Δ w.sender = 0)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (horder₁ : ∀ n,
      earliest ((σ.states (w.shiftHosts Δ hnet₁) lookahead n).key (w.shiftHosts Δ hnet₁))
          (σ.states (w.shiftHosts Δ hnet₁) lookahead n).due
        = earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due)
    (horder₂ : ∀ n,
      earliest ((σ.states (w.shiftHosts (-Δ) hnet₂) lookahead n).key (w.shiftHosts (-Δ) hnet₂))
          (σ.states (w.shiftHosts (-Δ) hnet₂) lookahead n).due
        = earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due)
    (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime (σ.plays w lookahead) r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (varFin fun r => Δ (w.host r))
      ≤ max ((w.shiftHosts Δ hnet₁).sync (σ.plays (w.shiftHosts Δ hnet₁) lookahead))
            ((w.shiftHosts (-Δ) hnet₂).sync (σ.plays (w.shiftHosts (-Δ) hnet₂) lookahead)) := by
  have hp₁ := (σ.plays_shiftHosts_of_earliest_eq w lookahead Δ hΔs hnet₁ horder₁).2
  have hp₂ := (σ.plays_shiftHosts_of_earliest_eq w lookahead (-Δ) (by simp [hΔs]) hnet₂ horder₂).2
  rw [hp₁, hp₂]
  exact w.sync_shiftHosts_max_ge Δ hnet₁ hnet₂ (σ.plays w lookahead) hR N hplay hunb

/-- **Irreducible tracking lower bound under indistinguishable uniform shifts.**
Under opposite uniform non-sender shifts `±A` preserving event order, at least
one of the two worlds suffers long-run tracking cost at least `A²`. -/
theorem Solution.tracking_shiftHosts_lower_bound [DecidableEq H] (σ : Solution H R Msg)
    (w : World H R) (lookahead : ℕ+) (Δ : H → ℝ) (A : ℝ) (hΔs : Δ w.sender = 0)
    (hΔ : ∀ r, Δ (w.host r) = A)
    (hnet₁ : ∀ i j s q a, w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (hnet₂ : ∀ i j s q a, w.network.deliver i j s q = some a → s + (-Δ i) < a + (-Δ j))
    (horder₁ : ∀ n,
      earliest ((σ.states (w.shiftHosts Δ hnet₁) lookahead n).key (w.shiftHosts Δ hnet₁))
          (σ.states (w.shiftHosts Δ hnet₁) lookahead n).due
        = earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due)
    (horder₂ : ∀ n,
      earliest ((σ.states (w.shiftHosts (-Δ) hnet₂) lookahead n).key (w.shiftHosts (-Δ) hnet₂))
          (σ.states (w.shiftHosts (-Δ) hnet₂) lookahead n).due
        = earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due)
    (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime (σ.plays w lookahead) r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (A ^ 2)
      ≤ max ((w.shiftHosts Δ hnet₁).tracking (σ.plays (w.shiftHosts Δ hnet₁) lookahead))
            ((w.shiftHosts (-Δ) hnet₂).tracking (σ.plays (w.shiftHosts (-Δ) hnet₂) lookahead)) := by
  have hp₁ := (σ.plays_shiftHosts_of_earliest_eq w lookahead Δ hΔs hnet₁ horder₁).2
  have hp₂ := (σ.plays_shiftHosts_of_earliest_eq w lookahead (-Δ) (by simp [hΔs]) hnet₂ horder₂).2
  rw [hp₁, hp₂]
  exact w.tracking_shiftHosts_max_ge Δ A hΔ hnet₁ hnet₂ (σ.plays w lookahead) hR N hplay hunb

end Unisono.Spec
