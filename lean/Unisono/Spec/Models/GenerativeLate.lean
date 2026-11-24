/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.MeasurableDelay

/-!
# How often a message is late, in every random world

In every random world of a member of the generative model, the long-run
fraction of late messages among messages sent at equally spaced true times is
a number of the member: the probability that one message is late.

* `pathLaw`: the law of the paused times of all links and hosts of a member,
  as functions of true time. It is their law in every random world of the
  member (`Prior.map_paused_eq_pathLaw`).
* `lateProbability`: the probability, under that law, that a message from
  one host to another takes longer than a given time. It does not depend on
  the true time at which the message is sent
  (`measureReal_late_cells`), because the paused times moved in time have the
  same law (`map_cellPaused_shift`).
* `lateFraction`: the fraction of the first `n` messages, sent at the true
  times `h₀`, `h₀ + ℓ`, `h₀ + 2 ℓ`, ..., that take longer than a given time.
* `Prior.ae_tendsto_lateFraction`: in almost every outcome of every random
  world of the member, that fraction converges to `lateProbability`.

The true times of sending are fixed numbers here. In a random world the
capture device hands over its blocks at true times that depend on the clocks,
which are drawn; the statement for those times is not derived here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-- The fraction of the first `n` messages from host `i` to host `j`, sent at
the true times `h₀`, `h₀ + ℓ`, `h₀ + 2 ℓ` and so on over a link with least
delay `δ`, that take longer than `μ` seconds, for the paused times `x`. -/
def lateFraction (x : PauseIndex H → Time → ℝ) (i j : H) (δ μ h₀ ℓ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ c ∈ Finset.range n,
    if μ < arrivalM x i j δ (h₀ + c * ℓ) - (h₀ + c * ℓ) then (1 : ℝ) else 0

theorem measurableSet_late (i j : H) (δ μ s : ℝ) :
    MeasurableSet {x : PauseIndex H → Time → ℝ | μ < arrivalM x i j δ s - s} := by
  have hp : Measurable fun x : PauseIndex H → Time → ℝ => (x, δ, s) :=
    measurable_id.prodMk measurable_const
  have h : Measurable fun x : PauseIndex H → Time → ℝ => arrivalM x i j δ s :=
    Measurable.comp
      (g := fun p : (PauseIndex H → Time → ℝ) × ℝ × ℝ => arrivalM p.1 i j p.2.1 p.2.2)
      (f := fun x => (x, δ, s)) (measurable_arrivalM i j) hp
  exact measurableSet_lt measurable_const (h.sub_const s)

theorem measurable_lateFraction (i j : H) (δ μ h₀ ℓ : ℝ) (n : ℕ) :
    Measurable fun x : PauseIndex H → Time → ℝ => lateFraction x i j δ μ h₀ ℓ n := by
  unfold lateFraction
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ fun c _ =>
    Measurable.ite (measurableSet_late i j δ μ (h₀ + c * ℓ)) measurable_const measurable_const

section Law

variable [Fintype H]

/-- The law of the paused times of all links and hosts of a member, as
functions of true time: the law of the paused times that independent cells of
one second give. -/
def pathLaw (f : Member H R) : Measure (PauseIndex H → Time → ℝ) :=
  (pauseCellsLaw f 1).map (cellPaused 1)

instance (f : Member H R) : IsProbabilityMeasure (pathLaw f) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_cellPaused 1).aemeasurable).mpr inferInstance

/-- **The paused times of every random world of a member have the law
`pathLaw`.** -/
theorem Prior.map_paused_eq_pathLaw {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R}
    {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) :
    P.map (fun ω => (D ω).paused) = pathLaw f :=
  hD.map_paused one_pos

/-- The probability that a message from host `i` to host `j`, over a link
with least delay `δ`, takes longer than `μ` seconds, in the member `f`. -/
def lateProbability (f : Member H R) (i j : H) (δ μ : ℝ) : ℝ :=
  (pathLaw f).real {x | μ < arrivalM x i j δ 0 - 0}

/-- **The paused times moved in time have the same law.** The paused times
that the cells give, moved by `h₀` seconds and counted from their values
then, have the law `pathLaw`, whatever the length `ℓ` of a cell is. -/
theorem map_cellPaused_shift (f : Member H R) {ℓ : ℝ} (hℓ : 0 < ℓ) (h₀ : ℝ) :
    (pauseCellsLaw f ℓ).map
        (fun ω (x : PauseIndex H) t => cellPaused ℓ ω x (t + h₀) - cellPaused ℓ ω x h₀)
      = pathLaw f := by
  refine map_paths_eq (L := fun x => f.pauseIncrementLaw x)
    (X := fun x t ω => cellPaused ℓ ω x (t + h₀) - cellPaused ℓ ω x h₀)
    (X' := fun x t ω => cellPaused 1 ω x t) (fun x => ?_)
    (fun x => hasIncrementLaws_cellPaused f one_pos x) (fun x => ?_)
    (fun x => (measurable_pi_iff.mp (measurable_cellPaused 1) x).aemeasurable) ?_
    (iIndepFun_cellPaused f 1)
  · have base := hasIncrementLaws_cellPaused f hℓ x
    refine ⟨fun ω => by simp, ?_, ?_⟩
    · intro n τ hτ
      have h := base.indep n (fun i => τ i + h₀) fun a b hab => by
        have := hτ hab
        linarith
      have e : (fun (i : Fin n) ω => (cellPaused ℓ ω x (τ i.succ + h₀) - cellPaused ℓ ω x h₀)
            - (cellPaused ℓ ω x (τ i.castSucc + h₀) - cellPaused ℓ ω x h₀))
          = fun (i : Fin n) ω =>
            cellPaused ℓ ω x (τ i.succ + h₀) - cellPaused ℓ ω x (τ i.castSucc + h₀) := by
        funext i ω
        ring
      rw [e]
      exact h
    · intro s t hst
      have h := base.law (s + h₀) (t + h₀) (by linarith)
      have e : (fun ω => (cellPaused ℓ ω x (t + h₀) - cellPaused ℓ ω x h₀)
            - (cellPaused ℓ ω x (s + h₀) - cellPaused ℓ ω x h₀))
          = fun ω => cellPaused ℓ ω x (t + h₀) - cellPaused ℓ ω x (s + h₀) := by
        funext ω
        ring
      rw [e]
      have el : f.pauseIncrementLaw x (s + h₀) (t + h₀) = f.pauseIncrementLaw x s t := by
        unfold Member.pauseIncrementLaw
        rw [add_sub_add_right_eq_sub]
      rw [el] at h
      exact h
  · exact (measurable_pi_iff.mpr fun t =>
      ((measurable_pi_iff.mp (measurable_pi_iff.mp (measurable_cellPaused ℓ) x) (t + h₀)).sub
        (measurable_pi_iff.mp (measurable_pi_iff.mp (measurable_cellPaused ℓ) x) h₀))).aemeasurable
  · exact (iIndepFun_cellPaused f ℓ).comp (fun _ (X : Time → ℝ) t => X (t + h₀) - X h₀)
      fun _ => measurable_pi_iff.mpr fun t =>
        (measurable_pi_apply (t + h₀)).sub (measurable_pi_apply h₀)

/-- **The probability that a message is late does not depend on when it is
sent.** For cells that last `ℓ` seconds, the probability that a message sent
at the true time `h₀` takes longer than `μ` seconds is `lateProbability`. -/
theorem measureReal_late_cells (f : Member H R) {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : H) (δ μ h₀ : ℝ) :
    (pauseCellsLaw f ℓ).real {ω | μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀}
      = lateProbability f i j δ μ := by
  have hshift : ∀ ω : ℤ → PauseIndex H → Cell,
      arrivalM (fun x t => cellPaused ℓ ω x (t + h₀) - cellPaused ℓ ω x h₀) i j δ 0
        = arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀ := by
    intro ω
    have h := arrivalM_shift (x := cellPaused ℓ ω)
      (y := fun x t => cellPaused ℓ ω x (t + h₀) - cellPaused ℓ ω x h₀) (a := h₀)
      (c := fun x => cellPaused ℓ ω x h₀) (fun p t => cellPaused_rightContinuous hℓ ω p t)
      (fun p t => by
        have h1 := cellPaused_rightContinuous hℓ ω p (t + h₀)
        have h2 : ContinuousWithinAt (fun u : ℝ => u + h₀) (Set.Ici t) t :=
          (continuous_id.add continuous_const).continuousWithinAt
        exact (ContinuousWithinAt.comp (g := cellPaused ℓ ω p) (f := fun u : ℝ => u + h₀) h1 h2
          fun u hu => by
            show t + h₀ ≤ u + h₀
            linarith [show t ≤ u from hu]).sub continuousWithinAt_const)
      (fun p t => rfl) i j δ 0
    rw [zero_add] at h
    exact h
  have hm : Measurable fun (ω : ℤ → PauseIndex H → Cell) (x : PauseIndex H) (t : Time) =>
      cellPaused ℓ ω x (t + h₀) - cellPaused ℓ ω x h₀ :=
    measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun t =>
      (measurable_pi_iff.mp (measurable_pi_iff.mp (measurable_cellPaused ℓ) x) (t + h₀)).sub
        (measurable_pi_iff.mp (measurable_pi_iff.mp (measurable_cellPaused ℓ) x) h₀)
  unfold lateProbability
  rw [← map_cellPaused_shift f hℓ h₀, measureReal_def, measureReal_def,
    Measure.map_apply hm (measurableSet_late i j δ μ 0)]
  congr 2
  ext ω
  show μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀
    ↔ μ < arrivalM (fun x t => cellPaused ℓ ω x (t + h₀) - cellPaused ℓ ω x h₀) i j δ 0 - 0
  rw [hshift, sub_zero]

/-- **The long-run fraction of late messages is the probability that a
message is late, for the cells.** -/
theorem ae_tendsto_lateFraction_cells (f : Member H R) {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : H)
    (δ μ h₀ : ℝ) :
    ∀ᵐ ω ∂pauseCellsLaw f ℓ,
      Tendsto (fun n => lateFraction (cellPaused ℓ ω) i j δ μ h₀ ℓ n) atTop
        (𝓝 (lateProbability f i j δ μ)) := by
  classical
  filter_upwards [ae_tendsto_lateFrequency f hℓ i j δ μ h₀] with ω hω
  rw [measureReal_late_cells f hℓ] at hω
  refine hω.congr fun n => ?_
  unfold lateFraction
  rw [Finset.card_filter, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/-- **The long-run fraction of late messages is the probability that a
message is late, in every random world.** In every random world of a member,
consider messages from host `i` to host `j` sent at the true times `h₀`,
`h₀ + ℓ`, `h₀ + 2 ℓ` and so on, over a link with least delay `δ`. In almost
every outcome, the fraction of the first `n` messages that take longer than
`μ` seconds converges to `lateProbability`, a number of the member. -/
theorem Prior.ae_tendsto_lateFraction {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R}
    {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (i j : H) (δ μ h₀ : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => lateFraction (D ω).paused i j δ μ h₀ ℓ n) atTop
      (𝓝 (lateProbability f i j δ μ)) :=
  hD.ae_paused_mem hℓ
    (measurableSet_tendsto (𝓝 (lateProbability f i j δ μ))
      fun n => measurable_lateFraction i j δ μ h₀ ℓ n)
    (ae_tendsto_lateFraction_cells f hℓ i j δ μ h₀)

end Law

end Unisono.Spec.GenerativeWorld
