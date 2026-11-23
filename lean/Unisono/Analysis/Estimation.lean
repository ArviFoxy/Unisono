/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Clock-offset estimation for star and peer (receiver–receiver) topologies

> **Status (supplementary component / oracle analysis):** This module proves
> algebraic and stochastic properties in a simplified component or oracle
> setting as a supplement to `Unisono.Spec`. Per `PRINCIPLES.md`, results
> here do **not** replace end-to-end proofs on `Unisono.Spec.Solution` and
> `Unisono.Spec.Objectives` under a named model class in `Unisono.Spec.Models`.


This module records algebraic and `L²` identities for linear clock-offset
estimation in both communication topologies:

1. **Star topology (sender–receiver communication only).**
   * Each receiver `r` estimates its clock offset `θ r = φ_s - φ_r` relative to
     the sender from noisy star measurements `θ r + m r`, where `φ_s` is the
     sender's clock/capture phase, `φ_r` is receiver `r`'s clock/playback phase,
     and `m r` is the network/timestamp measurement error.
   * When two receivers apply the same linear filter (`star_pair_error_same`),
     sender-clock wander `φ_s` cancels in their relative timing error.
   * When two receivers apply different linear filters (for instance, on
     heterogeneous wired and wireless links), `star_pair_error_heterogeneous`
     exhibits the leakage `(F₁ - F₂) φ_s`.
   * Under an index-aligned common schedule correction `sRef` subtracted by
     both receivers (`disciplined_schedule_error`), heterogeneous filters see
     `δ_S = φ_s - sRef` instead of `φ_s`. This is an aligned algebraic
     identity (it does not model broadcast delay or jitter); when `sRef`
     estimates `φ_s` relative to the receivers' mean, `δ_S` contains both
     estimation noise and the precision-weighted receiver-clock mean.
   * Under inverse-variance weighting across `R` pairwise-uncorrelated `L²`
     receiver errors with second moments `σ_r²` and combined parameter
     `V_bc = (∑ σ_r⁻²)⁻¹`, the residual `m_r - m̄` has second moment
     `σ_r² - V_bc` (`residual_variance_sub`, `residual_variance_L2`), strictly
     less than `σ_r²` (equal to the variance when the errors are zero-mean;
     biased errors such as static asymmetry or queueing bias violate the
     orthogonality hypothesis).

2. **Peer / receiver–receiver topology (Graph-Laplacian BLUE & Thomson's
   Principle).**
   * On any finite directed measurement graph `G = (V, E)` with edge weights
     `var e > 0`, a linear estimator `∑ e, f e * y e` recovers `φ t - φ s` on
     every noiseless clock vector `φ` if and only if `f` is a unit `s → t` flow
     (`linear_unbiased_iff_unitFlow`).
   * **Exact linear bias under edge asymmetries (`graph_estimator_bias`).**
     When edge `e` carries static bias `α e` (such as a one-way delay
     asymmetry), any unit `s → t` flow `f` has exact estimation bias
     `∑ e, f e * α e`. Zero bias for arbitrary unknown sender-link asymmetries
     holds only for estimators that assign zero flow to those biased edges,
     not in general for the minimum-variance graph BLUE.
   * **Thomson's Principle (`thomson_blue_optimal`).** The algebraic quadratic
     form `flowVariance G f = ∑ e, G.var e * f e ^ 2` (which equals estimation
     variance when edge measurement errors are zero-mean and mutually
     uncorrelated with variances `G.var e`; links sharing one wireless medium
     can violate uncorrelatedness) is uniquely minimized over unit `s → t`
     flows by the electrical flow `f*_e = (ψ (dst e) - ψ (src e)) / var e`,
     achieving effective resistance `ψ t - ψ s`.
   * **Topology corollaries:**
     - **Star graph (`star_effective_resistance`):** effective resistance
       between receivers `r₁ ≠ r₂` is `v r₁ + v r₂`.
     - **Complete peer graph `K_N` (`complete_graph_effective_resistance`,
       `complete_graph_equal_budget`):** with equal edge variance `v` per link
       (`N (N - 1) / 2` links vs `N - 1` spokes), effective resistance is
       `2 v / N` (`N×` smaller than `2 v`); at the *same total probe budget*
       across all links (`v_K = (N / 2) * v`), effective resistance is `v`
       (a `2×` reduction for every `N ≥ 2`).
     - **Wi-Fi sender with wired peer link (`wifi_sender_wired_peers_resistance`,
       `triangle_blue_bias`):** two speakers with Wi-Fi sender variance `vW`
       and wired peer variance `vP` achieve parallel effective resistance
       `2 vW vP / (2 vW + vP)`, while the graph BLUE retains bias
       `(vP / (2 vW + vP)) * (α₁ - α₀) + (2 vW / (2 vW + vP)) * αP` under
       edge biases `(α₀, α₁, αP)` (whereas the peer-only estimator has bias
       `αP`, zero when the peer link is symmetric).
-/

@[expose] public noncomputable section

namespace Unisono.Analysis

open MeasureTheory Finset

/-! ## Part 1: Star-topology linear filters and inverse-variance residuals -/

section StarEstimation

/-- Causal finite-impulse-response linear filter with taps `w : ℕ → ℝ` applied
to a signal `x : ℕ → ℝ` at cycle `k`. -/
def linFilter (w x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), w j * x (k - j)

theorem linFilter_add (w x y : ℕ → ℝ) (k : ℕ) :
    linFilter w (fun t => x t + y t) k = linFilter w x k + linFilter w y k := by
  simp only [linFilter, mul_add, Finset.sum_add_distrib]

theorem linFilter_sub (w x y : ℕ → ℝ) (k : ℕ) :
    linFilter w (fun t => x t - y t) k = linFilter w x k - linFilter w y k := by
  simp only [linFilter, mul_sub, Finset.sum_sub_distrib]

/-- **Sender-clock cancellation under identical filters.** When two receivers
observe `θ_i = φ_s - φ_i` with measurement errors `m_i` and apply the same
linear filter `w`, their relative estimation error
`(F(θ₁ + m₁) - θ₁) - (F(θ₂ + m₂) - θ₂)` does not depend on `φ_s`. -/
theorem star_pair_error_same (w φs φ₁ φ₂ m₁ m₂ : ℕ → ℝ) (k : ℕ) :
    (linFilter w (fun t => (φs t - φ₁ t) + m₁ t) k - (φs k - φ₁ k))
      - (linFilter w (fun t => (φs t - φ₂ t) + m₂ t) k - (φs k - φ₂ k))
    = (linFilter w m₁ k - linFilter w m₂ k)
      + ((φ₁ k - linFilter w φ₁ k) - (φ₂ k - linFilter w φ₂ k)) := by
  rw [linFilter_add, linFilter_sub, linFilter_add, linFilter_sub]
  ring

/-- **Sender-clock leakage under heterogeneous filters.** When two receivers
apply different linear filters `w₁` and `w₂` (for instance, because one link is
wired and the other is Wi-Fi), the sender clock `φ_s` no longer cancels: it
leaks into their relative synchronization error through
`linFilter w₁ φ_s k - linFilter w₂ φ_s k`. -/
theorem star_pair_error_heterogeneous (w₁ w₂ φs φ₁ φ₂ m₁ m₂ : ℕ → ℝ) (k : ℕ) :
    (linFilter w₁ (fun t => (φs t - φ₁ t) + m₁ t) k - (φs k - φ₁ k))
      - (linFilter w₂ (fun t => (φs t - φ₂ t) + m₂ t) k - (φs k - φ₂ k))
    = (linFilter w₁ φs k - linFilter w₂ φs k)
      + (linFilter w₁ m₁ k - linFilter w₂ m₂ k)
      + ((φ₁ k - linFilter w₁ φ₁ k) - (φ₂ k - linFilter w₂ φ₂ k)) := by
  rw [linFilter_add, linFilter_sub, linFilter_add, linFilter_sub]
  ring

/-- **Aligned schedule-subtraction identity.** Substituting the residual
`δS t = φs t - sRef t` for `φs t` in `star_pair_error_heterogeneous` replaces
the raw sender-phase leakage `(F₁ - F₂) φ_s` with `(F₁ - F₂) δS`. This assumes
both receivers subtract the same correction `sRef` at the same cycle index `t`
(it does not model broadcast delay, broadcast jitter, or extrapolation error);
moreover, if `sRef` estimates `φ_s` relative to the receivers' mean, `δS`
includes both estimation error and that receiver-clock mean. -/
theorem disciplined_schedule_error (w₁ w₂ φs sRef φ₁ φ₂ m₁ m₂ : ℕ → ℝ) (k : ℕ) :
    let δS : ℕ → ℝ := fun t => φs t - sRef t
    (linFilter w₁ (fun t => (δS t - φ₁ t) + m₁ t) k - (δS k - φ₁ k))
      - (linFilter w₂ (fun t => (δS t - φ₂ t) + m₂ t) k - (δS k - φ₂ k))
    = (linFilter w₁ δS k - linFilter w₂ δS k)
      + (linFilter w₁ m₁ k - linFilter w₂ m₂ k)
      + ((φ₁ k - linFilter w₁ φ₁ k) - (φ₂ k - linFilter w₂ φ₂ k)) := by
  intro δS
  exact star_pair_error_heterogeneous w₁ w₂ δS φ₁ φ₂ m₁ m₂ k

/-- Inverse-variance combined variance `V_bc = (∑ r, (σ2 r)⁻¹)⁻¹` of the
precision-weighted consensus average of `R` independent observations with
variances `σ2 r > 0`. -/
def consensusVar {R : ℕ} (σ2 : Fin R → ℝ) : ℝ :=
  (∑ r : Fin R, (σ2 r)⁻¹)⁻¹

/-- Inverse-variance weight `α r = consensusVar σ2 / σ2 r`. -/
def invVarWeight {R : ℕ} (σ2 : Fin R → ℝ) (r : Fin R) : ℝ :=
  consensusVar σ2 / σ2 r

theorem sum_inv_pos {R : ℕ} (hR : 0 < R) {σ2 : Fin R → ℝ} (hσ : ∀ r, 0 < σ2 r) :
    0 < ∑ r : Fin R, (σ2 r)⁻¹ := by
  have : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  exact Finset.sum_pos (fun r _ => inv_pos.mpr (hσ r)) Finset.univ_nonempty

theorem consensusVar_pos {R : ℕ} (hR : 0 < R) {σ2 : Fin R → ℝ} (hσ : ∀ r, 0 < σ2 r) :
    0 < consensusVar σ2 :=
  inv_pos.mpr (sum_inv_pos hR hσ)

theorem sum_invVarWeight {R : ℕ} (hR : 0 < R) {σ2 : Fin R → ℝ} (hσ : ∀ r, 0 < σ2 r) :
    ∑ r : Fin R, invVarWeight σ2 r = 1 := by
  have hS : ∑ r : Fin R, (σ2 r)⁻¹ ≠ 0 := (sum_inv_pos hR hσ).ne'
  simp only [invVarWeight, consensusVar, div_eq_mul_inv, ← Finset.mul_sum]
  exact inv_mul_cancel₀ hS

/-- **Algebraic residual-variance identity.** For weights
`α i = V_bc / σ2 i` with `σ2 i > 0` and `V_bc = (∑ i, (σ2 i)⁻¹)⁻¹`,
`(1 - α r)² σ2 r + ∑_{i ≠ r} (α i)² σ2 i = σ2 r - V_bc`, strictly less than
`σ2 r` because `m r` enters `m̄` with positive weight. -/
theorem residual_variance_sub {R : ℕ} (hR : 0 < R) {σ2 : Fin R → ℝ} (hσ : ∀ r, 0 < σ2 r)
    (r : Fin R) :
    ∑ i : Fin R, ((if i = r then (1 : ℝ) else 0) - invVarWeight σ2 i) ^ 2 * σ2 i
      = σ2 r - consensusVar σ2 := by
  have hS_pos : 0 < ∑ i : Fin R, (σ2 i)⁻¹ := sum_inv_pos hR hσ
  have hS_ne : ∑ i : Fin R, (σ2 i)⁻¹ ≠ 0 := hS_pos.ne'
  have hσ_ne : ∀ i, σ2 i ≠ 0 := fun i => (hσ i).ne'
  have hexpand : ∀ i : Fin R,
      ((if i = r then (1 : ℝ) else 0) - invVarWeight σ2 i) ^ 2 * σ2 i
        = (if i = r then σ2 r - 2 * consensusVar σ2 else 0)
          + consensusVar σ2 ^ 2 * (σ2 i)⁻¹ := by
    intro i
    simp only [invVarWeight]
    have hi := hσ_ne i
    split_ifs with h
    · subst h
      field_simp
      ring
    · field_simp
      ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ r, ite_eq_left (Finset.mem_univ r),
    ← Finset.mul_sum]
  have hV : consensusVar σ2 ^ 2 * (∑ i : Fin R, (σ2 i)⁻¹) = consensusVar σ2 := by
    unfold consensusVar
    field_simp
  rw [hV]
  ring

/-- **`L²` second moment of `m r - m̄` under pairwise orthogonal errors.**
For any `L²` random variables `m : Fin R → Ω → ℝ` with second moments
`∫ (m i)² = σ2 i > 0` and pairwise orthogonality `∫ m i * m j = 0` for `i ≠ j`
(which equals uncorrelatedness with variance `σ2 i` when each `m i` has zero
mean, and fails when errors share a nonzero bias such as queueing bias or
asymmetry), the precision-weighted average `m̄ = ∑ i, invVarWeight σ2 i * m i`
has second moment `consensusVar σ2` and each residual `m r - m̄` has second
moment `σ2 r - consensusVar σ2`. -/
theorem residual_variance_L2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {R : ℕ} (hR : 0 < R) {σ2 : Fin R → ℝ} (hσ : ∀ r, 0 < σ2 r)
    {m : Fin R → Ω → ℝ} (hm : ∀ i, MemLp (m i) 2 μ)
    (hvar : ∀ i, ∫ ω, m i ω ^ 2 ∂μ = σ2 i)
    (hunc : ∀ i j, i ≠ j → ∫ ω, m i ω * m j ω ∂μ = 0) (r : Fin R) :
    let mBar : Ω → ℝ := fun ω => ∑ i : Fin R, invVarWeight σ2 i * m i ω
    (∫ ω, mBar ω ^ 2 ∂μ = consensusVar σ2)
      ∧ (∫ ω, (m r ω - mBar ω) ^ 2 ∂μ = σ2 r - consensusVar σ2) := by
  intro mBar
  have hquad : ∀ c : Fin R → ℝ,
      ∫ ω, (∑ i : Fin R, c i * m i ω) ^ 2 ∂μ = ∑ i : Fin R, c i ^ 2 * σ2 i := by
    intro c
    have hi_prod : ∀ i j, Integrable (fun ω => (c i * m i ω) * (c j * m j ω)) μ :=
      fun i j => ((hm i).const_mul (c i)).integrable_mul ((hm j).const_mul (c j))
    have hexp : ∀ ω, (∑ i : Fin R, c i * m i ω) ^ 2
        = ∑ i : Fin R, ∑ j : Fin R, (c i * m i ω) * (c j * m j ω) := by
      intro ω; rw [sq, Finset.sum_mul_sum]
    simp_rw [hexp]
    rw [integral_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hi_prod i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum Finset.univ fun j _ => hi_prod i j]
    rw [Finset.sum_eq_single i]
    · have hrew : (fun ω => (c i * m i ω) * (c i * m i ω))
          = fun ω => c i ^ 2 * m i ω ^ 2 := by funext ω; ring
      rw [hrew, integral_const_mul, hvar i]
    · intro j _ hne
      have hrew : (fun ω => (c i * m i ω) * (c j * m j ω))
          = fun ω => (c i * c j) * (m i ω * m j ω) := by funext ω; ring
      rw [hrew, integral_const_mul, hunc i j hne.symm, mul_zero]
    · simp
  constructor
  · rw [hquad (invVarWeight σ2)]
    have hS_ne : ∑ i : Fin R, (σ2 i)⁻¹ ≠ 0 := (sum_inv_pos hR hσ).ne'
    have hterm : ∀ i : Fin R, invVarWeight σ2 i ^ 2 * σ2 i = consensusVar σ2 ^ 2 * (σ2 i)⁻¹ := by
      intro i
      have hi : σ2 i ≠ 0 := (hσ i).ne'
      unfold invVarWeight
      field_simp
    simp_rw [hterm, ← Finset.mul_sum]
    unfold consensusVar
    field_simp
  · have hrew : ∀ ω, m r ω - mBar ω
        = ∑ i : Fin R, ((if i = r then (1 : ℝ) else 0) - invVarWeight σ2 i) * m i ω := by
      intro ω
      simp only [mBar, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ r, Finset.mem_univ, ↓reduceIte]
    simp_rw [hrew]
    rw [hquad (fun i => (if i = r then (1 : ℝ) else 0) - invVarWeight σ2 i)]
    exact residual_variance_sub hR hσ r

end StarEstimation

/-! ## Part 2: Peer / receiver–receiver Graph-Laplacian BLUE (Thomson's Principle) -/

section GraphBlue

/-- A finite directed measurement graph on vertices `V` with edges `E` and
positive edge weights `var e > 0`. In the statistical interpretation, edge `e`
observes `y e = φ (dst e) - φ (src e) + α e + η e`, where `α e` is static bias
and `η e` is zero-mean noise with variance `var e`. -/
structure EdgeGraph (V E : Type*) [Fintype V] [DecidableEq V] [Fintype E] where
  src : E → V
  dst : E → V
  var : E → ℝ
  var_pos : ∀ e, 0 < var e

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

/-- Net divergence (inflow minus outflow) of an edge flow `f : E → ℝ` at vertex
`u`. -/
def flowDiv (G : EdgeGraph V E) (f : E → ℝ) (u : V) : ℝ :=
  ∑ e : E, ((if G.dst e = u then f e else 0) - (if G.src e = u then f e else 0))

/-- Discrete summation by parts (adjointness of discrete gradient and
divergence): for any flow `f : E → ℝ` and any vertex potential `φ : V → ℝ`,
`∑ e, f e * (φ (dst e) - φ (src e)) = ∑ u, φ u * flowDiv G f u`. -/
theorem sum_flow_grad (G : EdgeGraph V E) (f : E → ℝ) (φ : V → ℝ) :
    ∑ e : E, f e * (φ (G.dst e) - φ (G.src e)) = ∑ u : V, φ u * flowDiv G f u := by
  have h1 : ∀ e : E, f e * (φ (G.dst e) - φ (G.src e))
      = ∑ u : V, φ u * ((if G.dst e = u then f e else 0) - (if G.src e = u then f e else 0)) := by
    intro e
    simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq Finset.univ, Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [flowDiv, Finset.mul_sum]

/-- A unit `s → t` flow satisfies Kirchhoff's current law with net sink `+1` at
`t`, net source `-1` at `s`, and `0` everywhere else. -/
def IsUnitFlow (G : EdgeGraph V E) (s t : V) (f : E → ℝ) : Prop :=
  ∀ u : V, flowDiv G f u = (if u = t then (1 : ℝ) else 0) - (if u = s then 1 else 0)

/-- **Unbiasedness equivalence (zero-bias edges).** A linear estimator
`y ↦ ∑ e, f e * y e` recovers `φ t - φ s` for every noiseless, unbiased clock
vector `φ : V → ℝ` if and only if `f` is a unit `s → t` flow. -/
theorem linear_unbiased_iff_unitFlow (G : EdgeGraph V E) (s t : V) (f : E → ℝ) :
    (∀ φ : V → ℝ, ∑ e : E, f e * (φ (G.dst e) - φ (G.src e)) = φ t - φ s)
      ↔ IsUnitFlow G s t f := by
  constructor
  · intro hunb u
    have h := hunb (fun v => if v = u then 1 else 0)
    have hlhs : ∑ e : E, f e * ((if G.dst e = u then (1 : ℝ) else 0)
        - (if G.src e = u then 1 else 0)) = flowDiv G f u := by
      unfold flowDiv
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [mul_sub]
    rw [hlhs] at h
    have h1 : (if t = u then (1 : ℝ) else 0) = if u = t then 1 else 0 := by
      by_cases htu : u = t <;> simp [htu, Ne.symm]
    have h2 : (if s = u then (1 : ℝ) else 0) = if u = s then 1 else 0 := by
      by_cases hsu : u = s <;> simp [hsu, Ne.symm]
    rw [h1, h2] at h
    exact h
  · intro hf φ
    rw [sum_flow_grad]
    have hcongr : ∑ u : V, φ u * flowDiv G f u
        = ∑ u : V, φ u * ((if u = t then (1 : ℝ) else 0) - (if u = s then 1 else 0)) :=
      Finset.sum_congr rfl fun u _ => by rw [hf u]
    rw [hcongr]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, ↓reduceIte]

/-- **Exact bias of a graph linear estimator under static edge biases.**
When each edge measurement carries static bias `α e` (such as a one-way delay
asymmetry), `y e = φ (dst e) - φ (src e) + α e`, any unit `s → t` flow `f`
incurs estimation bias `∑ e, f e * α e` relative to `φ t - φ s`. In
particular, bias vanishes for arbitrary unknown sender-link asymmetries only
if `f` puts zero weight on those links (not in general for the minimum-variance
graph BLUE). -/
theorem graph_estimator_bias (G : EdgeGraph V E) {s t : V} {f : E → ℝ}
    (hf : IsUnitFlow G s t f) (φ : V → ℝ) (α : E → ℝ) :
    (∑ e : E, f e * ((φ (G.dst e) - φ (G.src e)) + α e)) - (φ t - φ s)
      = ∑ e : E, f e * α e := by
  have hunb := (linear_unbiased_iff_unitFlow G s t f).mpr hf φ
  simp only [mul_add, Finset.sum_add_distrib, hunb]
  ring

/-- Algebraic quadratic form `∑ e, G.var e * (f e)²` associated with edge
weights `f`. When edge measurement errors are zero-mean and mutually
uncorrelated with variances `G.var e`, this equals the estimator's variance
(note that links sharing one wireless medium need not be uncorrelated). -/
def flowVariance (G : EdgeGraph V E) (f : E → ℝ) : ℝ :=
  ∑ e : E, G.var e * f e ^ 2

/-- Electrical current `f*_e = (ψ (dst e) - ψ (src e)) / var e` induced by a
vertex potential `ψ : V → ℝ` (Ohm's law with resistance `R_e = var e`). -/
def electricalFlow (G : EdgeGraph V E) (ψ : V → ℝ) (e : E) : ℝ :=
  (ψ (G.dst e) - ψ (G.src e)) / G.var e

/-- **Thomson's Principle (algebraic Graph-Laplacian BLUE optimality).**
Suppose vertex potential `ψ : V → ℝ` solves the weighted graph Laplacian for
unit injection from `s` to `t`, i.e., `IsUnitFlow G s t (electricalFlow G ψ)`.
Then:
1. For every unit `s → t` flow `f`,
   `flowVariance G f = flowVariance G f* + flowVariance G (f - f*)`.
2. The electrical flow achieves `flowVariance G f* = ψ t - ψ s` (the effective
   resistance between `s` and `t`).
3. Every unit `s → t` flow has `flowVariance` at least `ψ t - ψ s`, with
   equality if and only if `f = electricalFlow G ψ`. -/
theorem thomson_blue_optimal (G : EdgeGraph V E) {s t : V} {ψ : V → ℝ}
    (hψ : IsUnitFlow G s t (electricalFlow G ψ)) :
    let fStar := electricalFlow G ψ
    (flowVariance G fStar = ψ t - ψ s)
    ∧ (∀ f : E → ℝ, IsUnitFlow G s t f →
        flowVariance G f = (ψ t - ψ s) + flowVariance G (fun e => f e - fStar e))
    ∧ (∀ f : E → ℝ, IsUnitFlow G s t f → ψ t - ψ s ≤ flowVariance G f)
    ∧ (∀ f : E → ℝ, IsUnitFlow G s t f → (flowVariance G f = ψ t - ψ s ↔ f = fStar)) := by
  intro fStar
  have hcross : ∀ g : E → ℝ, (∀ u : V, flowDiv G g u = 0) →
      ∑ e : E, G.var e * g e * fStar e = 0 := by
    intro g hg
    have hrew : ∀ e : E, G.var e * g e * fStar e = g e * (ψ (G.dst e) - ψ (G.src e)) := by
      intro e
      have hv : G.var e ≠ 0 := (G.var_pos e).ne'
      simp only [fStar, electricalFlow]
      field_simp
    simp_rw [hrew]
    rw [sum_flow_grad]
    simp [hg]
  have hvarStar : flowVariance G fStar = ψ t - ψ s := by
    have hrew : ∀ e : E, G.var e * fStar e ^ 2 = fStar e * (ψ (G.dst e) - ψ (G.src e)) := by
      intro e
      have hv : G.var e ≠ 0 := (G.var_pos e).ne'
      simp only [fStar, electricalFlow]
      field_simp
    unfold flowVariance
    simp_rw [hrew]
    exact (linear_unbiased_iff_unitFlow G s t fStar).mpr hψ ψ
  have hpyth : ∀ f : E → ℝ, IsUnitFlow G s t f →
      flowVariance G f = (ψ t - ψ s) + flowVariance G (fun e => f e - fStar e) := by
    intro f hf
    let g : E → ℝ := fun e => f e - fStar e
    have hg_div : ∀ u : V, flowDiv G g u = 0 := by
      intro u
      have hsub : flowDiv G g u = flowDiv G f u - flowDiv G fStar u := by
        simp only [flowDiv, g, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> ring
      rw [hsub, hf u, hψ u, sub_self]
    have hsplit : flowVariance G f
        = flowVariance G fStar + 2 * (∑ e : E, G.var e * g e * fStar e)
          + flowVariance G g := by
      simp only [flowVariance, g, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [hsplit, hvarStar, hcross g hg_div, mul_zero, add_zero]
  have hnonneg : ∀ g : E → ℝ, 0 ≤ flowVariance G g := fun g =>
    Finset.sum_nonneg fun e _ => mul_nonneg (G.var_pos e).le (sq_nonneg _)
  refine ⟨hvarStar, hpyth, fun f hf => ?_, fun f hf => ?_⟩
  · linarith [hpyth f hf, hnonneg (fun e => f e - fStar e)]
  · constructor
    · intro heq
      have hzero : flowVariance G (fun e => f e - fStar e) = 0 := by
        linarith [hpyth f hf]
      funext e
      have hterm : G.var e * (f e - fStar e) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
          mul_nonneg (G.var_pos i).le (sq_nonneg _)).mp hzero e (Finset.mem_univ e)
      have hsq : (f e - fStar e) ^ 2 = 0 :=
        (mul_eq_zero.mp hterm).resolve_left (G.var_pos e).ne'
      linarith [sq_eq_zero_iff.mp hsq]
    · intro heq
      rw [heq, hvarStar]

/-! ### Topology corollaries -/

/-- **Star topology effective resistance.** On a star graph with hub `0 : Fin (R + 1)`
and `R` spokes `r : Fin R` connecting `0 → r.succ` with probe variance `v r > 0`,
the minimum `flowVariance` for `φ r₂.succ - φ r₁.succ` (`r₁ ≠ r₂`) is
`v r₁ + v r₂`. -/
def starGraph {R : ℕ} (v : Fin R → ℝ) (hv : ∀ r, 0 < v r) :
    EdgeGraph (Fin (R + 1)) (Fin R) where
  src := fun _ => 0
  dst := fun r => r.succ
  var := v
  var_pos := hv

theorem star_effective_resistance {R : ℕ} (v : Fin R → ℝ) (hv : ∀ r, 0 < v r)
    {r₁ r₂ : Fin R} (hne : r₁ ≠ r₂) :
    let G := starGraph v hv
    let ψ : Fin (R + 1) → ℝ := fun u =>
      if u = r₂.succ then v r₂ else if u = r₁.succ then -(v r₁) else 0
    IsUnitFlow G r₁.succ r₂.succ (electricalFlow G ψ)
      ∧ flowVariance G (electricalFlow G ψ) = v r₁ + v r₂
      ∧ (∀ f : Fin R → ℝ, IsUnitFlow G r₁.succ r₂.succ f → v r₁ + v r₂ ≤ flowVariance G f) := by
  intro G ψ
  have h10 : r₁.succ ≠ (0 : Fin (R + 1)) := Fin.succ_ne_zero r₁
  have h20 : r₂.succ ≠ (0 : Fin (R + 1)) := Fin.succ_ne_zero r₂
  have h12 : r₁.succ ≠ r₂.succ := fun h => hne (Fin.succ_injective _ h)
  have hf : ∀ r : Fin R, electricalFlow G ψ r
      = (if r = r₂ then (1 : ℝ) else 0) - (if r = r₁ then 1 else 0) := by
    intro r
    have hvr : v r ≠ 0 := (hv r).ne'
    simp only [electricalFlow, G, starGraph, ψ, h20.symm, h10.symm, ↓reduceIte, sub_zero]
    by_cases h2 : r = r₂
    · subst h2
      simp only [↓reduceIte, hne.symm, sub_zero]
      field_simp
    · by_cases h1 : r = r₁
      · subst h1
        simp only [h12, ↓reduceIte, hne, zero_sub]
        field_simp
      · have h2' : r.succ ≠ r₂.succ := fun h => h2 (Fin.succ_injective _ h)
        have h1' : r.succ ≠ r₁.succ := fun h => h1 (Fin.succ_injective _ h)
        simp [h2', h1', h2, h1]
  have hunit : IsUnitFlow G r₁.succ r₂.succ (electricalFlow G ψ) := by
    intro u
    unfold flowDiv
    simp_rw [hf]
    simp only [G, starGraph]
    refine Fin.cases ?_ (fun r => ?_) u
    · simp [Fin.succ_ne_zero, h20.symm, h10.symm]
    · simp [Fin.succ_inj, (Fin.succ_ne_zero r).symm]
  have hth := thomson_blue_optimal G hunit
  have hdiff : ψ r₂.succ - ψ r₁.succ = v r₁ + v r₂ := by
    simp only [ψ, ↓reduceIte, h12]
    ring
  rw [hdiff] at hth
  exact ⟨hunit, hth.1, hth.2.2.1⟩

/-- **Complete peer graph `K_N` effective resistance.** When all `N = R + 1`
hosts exchange pairwise probes of equal variance `v > 0` across all
`N (N - 1) / 2` edges `(i, j)` with `i < j`, the minimum `flowVariance` for
estimating `φ t - φ s` (`s ≠ t`) is `2 v / N`. Note that `K_N` uses `N / 2`
times as many links as a star on `N` vertices (`N - 1` spokes); see
`complete_graph_equal_budget` for the equal-total-probe-budget comparison. -/
def completeGraph (N : ℕ) (v : ℝ) (hv : 0 < v) :
    EdgeGraph (Fin N) { p : Fin N × Fin N // p.1 < p.2 } where
  src := fun e => e.1.1
  dst := fun e => e.1.2
  var := fun _ => v
  var_pos := fun _ => hv

theorem complete_graph_effective_resistance {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : 0 < v)
    {s t : Fin N} (hne : s ≠ t) :
    let G := completeGraph N v hv
    let ψ : Fin N → ℝ := fun u =>
      (v / N) * ((if u = t then (1 : ℝ) else 0) - (if u = s then 1 else 0))
    IsUnitFlow G s t (electricalFlow G ψ)
      ∧ flowVariance G (electricalFlow G ψ) = 2 * v / N
      ∧ (∀ f, IsUnitFlow G s t f → 2 * v / N ≤ flowVariance G f) := by
  intro G ψ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hvne : v ≠ 0 := hv.ne'
  have hunit : IsUnitFlow G s t (electricalFlow G ψ) := by
    intro u
    have hdiv_all : flowDiv G (electricalFlow G ψ) u
        = ∑ w : Fin N, (ψ u - ψ w) / v := by
      unfold flowDiv electricalFlow G completeGraph
      have hterm : ∀ e : { p : Fin N × Fin N // p.1 < p.2 },
          (if e.1.2 = u then (ψ e.1.2 - ψ e.1.1) / v else 0)
            - (if e.1.1 = u then (ψ e.1.2 - ψ e.1.1) / v else 0)
          = (if e.1.2 = u then (ψ u - ψ e.1.1) / v else 0)
            + (if e.1.1 = u then (ψ u - ψ e.1.2) / v else 0) := by
        intro ⟨⟨a, b⟩, hab⟩
        by_cases hbu : b = u
        · subst hbu
          have hau : a ≠ b := hab.ne
          simp [hau]
        · by_cases hau : a = u
          · subst hau
            simp [hbu]
            ring
          · simp [hbu, hau]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib]
      have hlt_sum : (∑ e : { p : Fin N × Fin N // p.1 < p.2 },
          if e.1.2 = u then (ψ u - ψ e.1.1) / v else 0)
          = ∑ w ∈ Finset.univ.filter (fun w : Fin N => w < u), (ψ u - ψ w) / v := by
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun e _ => e.1.1) ?_ ?_ ?_ ?_
        · intro ⟨⟨a, b⟩, hab⟩ he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
          exact he ▸ hab
        · intro ⟨⟨a₁, b₁⟩, _⟩ h1 ⟨⟨a₂, b₂⟩, _⟩ h2 ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          exact Subtype.ext (Prod.ext ha (h1.trans h2.symm))
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          exact ⟨⟨(w, u), hw⟩, by simp, rfl⟩
        · intro _ _; rfl
      have hgt_sum : (∑ e : { p : Fin N × Fin N // p.1 < p.2 },
          if e.1.1 = u then (ψ u - ψ e.1.2) / v else 0)
          = ∑ w ∈ Finset.univ.filter (fun w : Fin N => u < w), (ψ u - ψ w) / v := by
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun e _ => e.1.2) ?_ ?_ ?_ ?_
        · intro ⟨⟨a, b⟩, hab⟩ he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
          exact he ▸ hab
        · intro ⟨⟨a₁, b₁⟩, _⟩ h1 ⟨⟨a₂, b₂⟩, _⟩ h2 hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          exact Subtype.ext (Prod.ext (h1.trans h2.symm) hb)
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          exact ⟨⟨(u, w), hw⟩, by simp, rfl⟩
        · intro _ _; rfl
      rw [hlt_sum, hgt_sum]
      have hdisj : Disjoint (Finset.univ.filter (fun w : Fin N => w < u))
          (Finset.univ.filter (fun w : Fin N => u < w)) := by
        rw [Finset.disjoint_filter]
        intro w _ h1 h2
        exact lt_asymm h1 h2
      rw [← Finset.sum_union hdisj]
      have heq_zero : (ψ u - ψ u) / v = 0 := by ring
      have hpart : (Finset.univ.filter (fun w : Fin N => w < u)
            ∪ Finset.univ.filter (fun w : Fin N => u < w))
          = Finset.univ.erase u := by
        ext w
        simp
      rw [hpart, ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ u), heq_zero, add_zero]
    rw [hdiv_all]
    have hsum_ψ : ∑ w : Fin N, ψ w = 0 := by
      simp only [ψ, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, ↓reduceIte, sub_self, mul_zero]
    simp only [sub_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, hsum_ψ, zero_div, sub_zero]
    simp only [ψ]
    field_simp
  have hth := thomson_blue_optimal G hunit
  have hdiff : ψ t - ψ s = 2 * v / N := by
    simp only [ψ, ↓reduceIte, hne, hne.symm]
    ring
  rw [hdiff] at hth
  exact ⟨hunit, hth.1, hth.2.2.1⟩

/-- **Equal-probe-budget comparison for `K_N` versus the star.** Splitting the
star's total probe budget (`N - 1` spokes at variance `v`) uniformly across all
`N (N - 1) / 2` edges of `K_N` scales each edge's variance to `vK = (N / 2) * v`.
The complete graph's effective resistance between any two vertices is then
`2 * vK / N = v`, a `2×` reduction relative to the star's `2 v` for every
`N ≥ 2` (rather than `N×`). -/
theorem complete_graph_equal_budget {N : ℕ} (hN : 2 ≤ N) {v : ℝ} (hv : 0 < v)
    {s t : Fin N} (hne : s ≠ t) :
    let hvK : 0 < (N : ℝ) / 2 * v := by
      have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      positivity
    let G := completeGraph N ((N : ℝ) / 2 * v) hvK
    let ψ : Fin N → ℝ := fun u =>
      (((N : ℝ) / 2 * v) / N) * ((if u = t then (1 : ℝ) else 0) - (if u = s then 1 else 0))
    flowVariance G (electricalFlow G ψ) = v := by
  intro hvK G ψ
  have h := (complete_graph_effective_resistance hN hvK hne).2.1
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [h]
  field_simp

/-- **Wi-Fi sender + wired peers (parallel effective resistance).**
Consider 3 hosts (`Fin 3`): sender `0` on Wi-Fi with probe variance `vW > 0`
to speakers `1` and `2`, plus a direct wired peer link `(1, 2)` with probe
variance `vP > 0`. The minimum `flowVariance` for `φ 2 - φ 1` is the parallel
combination `2 vW vP / (2 vW + vP)`, smaller than both `2 vW` and `vP`. -/
def triangleGraph (vW vP : ℝ) (hvW : 0 < vW) (hvP : 0 < vP) :
    EdgeGraph (Fin 3) (Fin 3) where
  -- Edge 0: (0 -> 1) Wi-Fi, Edge 1: (0 -> 2) Wi-Fi, Edge 2: (1 -> 2) wired peer
  src := ![0, 0, 1]
  dst := ![1, 2, 2]
  var := ![vW, vW, vP]
  var_pos := fun e => by fin_cases e <;> assumption

theorem wifi_sender_wired_peers_resistance {vW vP : ℝ} (hvW : 0 < vW) (hvP : 0 < vP) :
    let G := triangleGraph vW vP hvW hvP
    let reff := (2 * vW * vP) / (2 * vW + vP)
    let ψ : Fin 3 → ℝ := ![0, -(reff / 2), reff / 2]
    IsUnitFlow G 1 2 (electricalFlow G ψ)
      ∧ flowVariance G (electricalFlow G ψ) = reff
      ∧ reff < vP
      ∧ reff < 2 * vW
      ∧ (∀ f : Fin 3 → ℝ, IsUnitFlow G 1 2 f → reff ≤ flowVariance G f) := by
  intro G reff ψ
  have hden : 0 < 2 * vW + vP := by linarith
  have hden_ne : 2 * vW + vP ≠ 0 := hden.ne'
  have hvW_ne : vW ≠ 0 := hvW.ne'
  have hvP_ne : vP ≠ 0 := hvP.ne'
  have hunit : IsUnitFlow G 1 2 (electricalFlow G ψ) := by
    intro u
    fin_cases u <;>
    · simp only [flowDiv, Fin.sum_univ_three, electricalFlow, G, triangleGraph, ψ, reff,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      norm_num
      field_simp
      ring
  have hth := thomson_blue_optimal G hunit
  have hdiff : ψ 2 - ψ 1 = reff := by
    simp only [ψ, Matrix.cons_val]
    ring
  rw [hdiff] at hth
  have hltP : reff < vP := by
    change (2 * vW * vP) / (2 * vW + vP) < vP
    rw [div_lt_iff₀ hden]
    nlinarith
  have hltW : reff < 2 * vW := by
    change (2 * vW * vP) / (2 * vW + vP) < 2 * vW
    rw [div_lt_iff₀ hden]
    nlinarith
  exact ⟨hunit, hth.1, hltP, hltW, hth.2.2.1⟩

/-- **Exact bias of the triangle BLUE versus the peer-only estimator.**
On `triangleGraph vW vP` with edge biases `α = ![α₀, α₁, αP]` (where `α₀` and
`α₁` are the one-way asymmetries on sender links `(0, 1)` and `(0, 2)` and `αP`
is the bias on the direct peer link `(1, 2)`):
1. The Graph-Laplacian BLUE `electricalFlow` routes fraction `vP / (2 vW + vP)`
   through the sender path and `2 vW / (2 vW + vP)` through the peer link, so
   its estimation bias for `φ 2 - φ 1` is
   `(vP / (2 vW + vP)) * (α₁ - α₀) + (2 vW / (2 vW + vP)) * αP`
   (nonzero whenever `α₁ ≠ α₀`, even if `αP = 0`).
2. The peer-only unit flow `fPeer = ![0, 0, 1]` has bias `αP`, which vanishes
   whenever the direct peer link is symmetric (`αP = 0`). -/
theorem triangle_blue_bias {vW vP : ℝ} (hvW : 0 < vW) (hvP : 0 < vP)
    (φ : Fin 3 → ℝ) (α₀ α₁ αP : ℝ) :
    let G := triangleGraph vW vP hvW hvP
    let reff := (2 * vW * vP) / (2 * vW + vP)
    let ψ : Fin 3 → ℝ := ![0, -(reff / 2), reff / 2]
    let α : Fin 3 → ℝ := ![α₀, α₁, αP]
    let fPeer : Fin 3 → ℝ := ![0, 0, 1]
    IsUnitFlow G 1 2 fPeer
      ∧ ((∑ e : Fin 3, electricalFlow G ψ e * ((φ (G.dst e) - φ (G.src e)) + α e))
            - (φ 2 - φ 1)
          = (vP / (2 * vW + vP)) * (α₁ - α₀) + (2 * vW / (2 * vW + vP)) * αP)
      ∧ ((∑ e : Fin 3, fPeer e * ((φ (G.dst e) - φ (G.src e)) + α e))
            - (φ 2 - φ 1)
          = αP) := by
  intro G reff ψ α fPeer
  have hden : (2 * vW + vP) ≠ 0 := by linarith
  have hvW_ne : vW ≠ 0 := hvW.ne'
  have hvP_ne : vP ≠ 0 := hvP.ne'
  have hunit_blue : IsUnitFlow G 1 2 (electricalFlow G ψ) :=
    (wifi_sender_wired_peers_resistance hvW hvP).1
  have hunit_peer : IsUnitFlow G 1 2 fPeer := by
    intro u
    fin_cases u <;>
    · simp [flowDiv, Fin.sum_univ_three, G, triangleGraph, fPeer]
  refine ⟨hunit_peer, ?_, ?_⟩
  · rw [graph_estimator_bias G hunit_blue φ α]
    simp only [Fin.sum_univ_three, electricalFlow, G, triangleGraph, ψ, reff, α,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    ring
  · rw [graph_estimator_bias G hunit_peer φ α]
    simp [Fin.sum_univ_three, fPeer, α]

end GraphBlue

end Unisono.Analysis
