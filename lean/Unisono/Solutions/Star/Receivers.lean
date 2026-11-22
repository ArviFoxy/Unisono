/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Several receivers: what the receivers share cancels

Each receiver `r` must follow `θ r = c + i r`, the difference of the
sender's clock and its own clock. The part `c` is common to all receivers:
the sender's clock, and the delays on the sender's side. The part `i r`
belongs to the receiver: its clock and its link. The receiver measures
`θ r + n r`, where `n r` is the error of its measurements. A linear way of
playing maps the measurements to a correction through a linear map `F r`,
such as a causal filter acting on sequences of random variables, and the
receiver's error is the correction minus `θ r`.

Synchronization depends only on the differences of the errors of the
receivers. This file proves three identities about them, in any real vector
space, so they hold for every realization and therefore also in the mean:

* When all receivers apply the same map, the common part cancels from every
  difference (`error_sub_error_same`), and the synchronization cost does not
  depend on it (`syncCost_same_filter`).
* When two receivers apply different maps, the common part enters their
  difference through the difference of the maps (`error_sub_error`).
* When the sender broadcasts an estimate `c + η` of the common part, and each
  receiver applies a map `G`, the same for all, to the broadcast and its own
  map `F r` to its measurements minus the broadcast, the common part cancels
  again, whatever the maps `F r` are (`broadcastError_sub`,
  `syncCost_broadcast`). What remains of the broadcast's error `η` enters
  through the receivers' own maps.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Star

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The error of a receiver that applies the linear map `F` to its
measurements `c + i + n` and must follow `c + i`. -/
def error (F : M →ₗ[ℝ] M) (c i n : M) : M := F (c + i + n) - (c + i)

/-- **The common part cancels when the maps are the same.** -/
theorem error_sub_error_same (F : M →ₗ[ℝ] M) (c i₁ n₁ i₂ n₂ : M) :
    error F c i₁ n₁ - error F c i₂ n₂ = F (i₁ + n₁ - (i₂ + n₂)) - (i₁ - i₂) := by
  simp only [error, map_add, map_sub]
  abel

/-- **The common part leaks through different maps.** The difference of the
errors of two receivers is the difference of the maps applied to the common
part, plus what their own parts contribute. -/
theorem error_sub_error (F₁ F₂ : M →ₗ[ℝ] M) (c i₁ n₁ i₂ n₂ : M) :
    error F₁ c i₁ n₁ - error F₂ c i₂ n₂
      = (F₁ - F₂) c + (F₁ (i₁ + n₁) - F₂ (i₂ + n₂)) - (i₁ - i₂) := by
  simp only [error, map_add, LinearMap.sub_apply]
  abel

/-- The error of a receiver that applies `G` to the broadcast `c + η` and its
own map `F` to its measurements `c + i + n` minus the broadcast. -/
def broadcastError (G F : M →ₗ[ℝ] M) (c η i n : M) : M :=
  G (c + η) + F (c + i + n - (c + η)) - (c + i)

/-- **The broadcast cancels the common part, whatever the receivers' own maps
are.** -/
theorem broadcastError_sub (G F₁ F₂ : M →ₗ[ℝ] M) (c η i₁ n₁ i₂ n₂ : M) :
    broadcastError G F₁ c η i₁ n₁ - broadcastError G F₂ c η i₂ n₂
      = F₁ (i₁ + n₁ - η) - F₂ (i₂ + n₂ - η) - (i₁ - i₂) := by
  have h₁ : c + i₁ + n₁ - (c + η) = i₁ + n₁ - η := by abel
  have h₂ : c + i₂ + n₂ - (c + η) = i₂ + n₂ - η := by abel
  simp only [broadcastError, h₁, h₂]
  abel

section Cost

variable {E : Type*} [NormedAddCommGroup E] {R : ℕ}

/-- The synchronization cost of the errors `e` of `R` receivers: the sum of
the squared norms of the differences over the pairs of distinct receivers.
For errors that are random sequences, with the norm of mean squares, it is
`R²` times the mean variance of the errors across the receivers. -/
def syncCost (e : Fin R → E) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), ‖e p.1 - e p.2‖ ^ 2

/-- Two families of errors whose differences agree have the same
synchronization cost. -/
theorem syncCost_congr {e e' : Fin R → E} (h : ∀ r s, e r - e s = e' r - e' s) :
    syncCost e = syncCost e' := by
  simp only [syncCost]
  exact Finset.sum_congr rfl fun p _ => by rw [h]

variable [Module ℝ E]

/-- **With the same map at every receiver, the synchronization cost does not
depend on the common part.** -/
theorem syncCost_same_filter (F : E →ₗ[ℝ] E) (c c' : E) (i n : Fin R → E) :
    syncCost (fun r => error F c (i r) (n r)) = syncCost (fun r => error F c' (i r) (n r)) :=
  syncCost_congr fun r s => by rw [error_sub_error_same, error_sub_error_same]

/-- **With the broadcast, the synchronization cost does not depend on the
common part, whatever the receivers' own maps are.** -/
theorem syncCost_broadcast (G : E →ₗ[ℝ] E) (F : Fin R → E →ₗ[ℝ] E) (c c' η : E)
    (i n : Fin R → E) :
    syncCost (fun r => broadcastError G (F r) c η (i r) (n r))
      = syncCost (fun r => broadcastError G (F r) c' η (i r) (n r)) :=
  syncCost_congr fun r s => by rw [broadcastError_sub, broadcastError_sub]

end Cost

end Unisono.Solutions.Star
