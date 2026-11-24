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

* `Prior.indepFun_scalars_paused`: the numbers of a draw (the splits, the
  offsets and the mean rates of the clocks, `Draw.scalars`) are independent
  of its paused times.
* `Prior.ae_lateFraction_scalars`: so the statement holds when the least
  delay, the time, the first true time of sending and the time between two
  messages are measurable functions of those numbers, as they are for the
  blocks that a capture device hands over. For each value of the numbers the
  statement holds for almost every value of the paused times, and the set of
  pairs for which the fraction converges is measurable
  (`ae_mem_of_indepFun`).
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

/-! ## True times of sending that depend on what is drawn -/

/-- The paused times that the cells give have the law `pathLaw`, whatever
the length of a cell is. -/
theorem map_cellPaused_eq_pathLaw (f : Member H R) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (pauseCellsLaw f ℓ).map (cellPaused ℓ) = pathLaw f :=
  map_paths_eq (X := fun x t ω => cellPaused ℓ ω x t) (X' := fun x t ω => cellPaused 1 ω x t)
    (fun x => hasIncrementLaws_cellPaused f hℓ x)
    (fun x => hasIncrementLaws_cellPaused f one_pos x)
    (fun x => (measurable_pi_iff.mp (measurable_cellPaused ℓ) x).aemeasurable)
    (fun x => (measurable_pi_iff.mp (measurable_cellPaused 1) x).aemeasurable)
    (iIndepFun_cellPaused f ℓ) (iIndepFun_cellPaused f 1)

omit [Fintype H] in
/-- **A property of an independent pair.** Let two random variables be
independent. If, for each value of the first, a measurable property of the
pair holds for almost every value of the second, then it holds for the pair
in almost every outcome. -/
theorem ae_mem_of_indepFun {Ω E 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]
    [MeasurableSpace 𝒳] {P : Measure Ω} [IsProbabilityMeasure P] {Θ : Ω → E} {X : Ω → 𝒳}
    (hΘ : AEMeasurable Θ P) (hX : AEMeasurable X P) (hind : IndepFun Θ X P)
    {G : Set (E × 𝒳)} (hG : MeasurableSet G) (h : ∀ θ, ∀ᵐ x ∂P.map X, (θ, x) ∈ G) :
    ∀ᵐ ω ∂P, (Θ ω, X ω) ∈ G := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hΘ hX).mp hind
  have hprod : ∀ᵐ p ∂(P.map Θ).prod (P.map X), p ∈ G :=
    (Measure.ae_prod_mem_iff_ae_ae_mem hG).mpr (Filter.Eventually.of_forall h)
  rw [← hmap] at hprod
  exact (ae_map_iff (hΘ.prodMk hX) hG).mp hprod

omit [Fintype H] in
/-- The fraction of late messages is measurable in the least delay, the
time, the first true time of sending, the time between two messages and the
paused times together. -/
theorem measurable_lateFraction_prod (i j : H) (n : ℕ) :
    Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) =>
      lateFraction p.2 i j p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 n := by
  unfold lateFraction
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun c _ => ?_
  have hδ : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hμ : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) => p.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hh : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) => p.1.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hl : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) => p.1.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hs : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) =>
      p.1.2.2.1 + (c : ℝ) * p.1.2.2.2 := hh.add (hl.const_mul _)
  have hq : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) =>
      (p.2, p.1.1, p.1.2.2.1 + (c : ℝ) * p.1.2.2.2) := measurable_snd.prodMk (hδ.prodMk hs)
  have ha : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) =>
      arrivalM p.2 i j p.1.1 (p.1.2.2.1 + (c : ℝ) * p.1.2.2.2) :=
    Measurable.comp
      (g := fun q : (PauseIndex H → Time → ℝ) × ℝ × ℝ => arrivalM q.1 i j q.2.1 q.2.2)
      (f := fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) =>
        (p.2, p.1.1, p.1.2.2.1 + (c : ℝ) * p.1.2.2.2)) (measurable_arrivalM i j) hq
  exact Measurable.ite (measurableSet_lt hμ (ha.sub hs)) measurable_const measurable_const

/-- The probability that a message is late is measurable in the least delay
and the time. -/
theorem measurable_lateProbability (f : Member H R) (i j : H) :
    Measurable fun q : ℝ × ℝ => lateProbability f i j q.1 q.2 := by
  have hq : Measurable fun p : (ℝ × ℝ) × (PauseIndex H → Time → ℝ) => (p.2, p.1.1, (0 : ℝ)) :=
    measurable_snd.prodMk ((measurable_fst.comp measurable_fst).prodMk measurable_const)
  have ha : Measurable fun p : (ℝ × ℝ) × (PauseIndex H → Time → ℝ) =>
      arrivalM p.2 i j p.1.1 0 :=
    Measurable.comp
      (g := fun q : (PauseIndex H → Time → ℝ) × ℝ × ℝ => arrivalM q.1 i j q.2.1 q.2.2)
      (f := fun p : (ℝ × ℝ) × (PauseIndex H → Time → ℝ) => (p.2, p.1.1, (0 : ℝ)))
      (measurable_arrivalM i j) hq
  have hS : MeasurableSet {p : (ℝ × ℝ) × (PauseIndex H → Time → ℝ) |
      p.1.2 < arrivalM p.2 i j p.1.1 0 - 0} :=
    measurableSet_lt (measurable_snd.comp measurable_fst) (ha.sub_const 0)
  exact (measurable_measure_prodMk_left (ν := pathLaw f) hS).ennreal_toReal

/-- **The long-run fraction of late messages when the times of sending are
drawn.** In a random world of a member, let the least delay `δ`, the time
`μ`, the first true time of sending `h₀` and the time `ℓ` between two
messages be random, and independent of the paused times of the links and
hosts. In almost every outcome in which `ℓ` is positive, the fraction of the
first `n` messages that take longer than `μ` converges to `lateProbability`
for the `δ` and `μ` of the outcome. -/
theorem Prior.ae_lateFraction_indep {Ω : Type} [MeasurableSpace Ω]
    {m : GenerativeWorld H R} {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R}
    (hD : m.Prior f P D) (i j : H) {Θ : Ω → ℝ × ℝ × ℝ × ℝ} (hΘ : AEMeasurable Θ P)
    (hind : IndepFun Θ (fun ω => (D ω).paused) P) :
    ∀ᵐ ω ∂P, 0 < (Θ ω).2.2.2 →
      Tendsto (fun n => lateFraction (D ω).paused i j (Θ ω).1 (Θ ω).2.1 (Θ ω).2.2.1
        (Θ ω).2.2.2 n) atTop (𝓝 (lateProbability f i j (Θ ω).1 (Θ ω).2.1)) := by
  have := hD.prob
  have hX : AEMeasurable (fun ω => (D ω).paused) P :=
    AEMeasurable.of_eval fun x => hD.aemeasurable_paused x
  have hL : Measurable fun p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) =>
      lateProbability f i j p.1.1 p.1.2.1 :=
    (measurable_lateProbability f i j).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hG : MeasurableSet
      ({p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) | p.1.2.2.2 ≤ 0}
        ∪ {p | Tendsto (fun n => lateFraction p.2 i j p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 n
            - lateProbability f i j p.1.1 p.1.2.1) atTop (𝓝 0)}) :=
    (measurableSet_le (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp measurable_fst))) measurable_const).union
      (measurableSet_tendsto (𝓝 0) fun n => (measurable_lateFraction_prod i j n).sub hL)
  have h : ∀ θ : ℝ × ℝ × ℝ × ℝ, ∀ᵐ x ∂P.map (fun ω => (D ω).paused),
      (θ, x) ∈ ({p : (ℝ × ℝ × ℝ × ℝ) × (PauseIndex H → Time → ℝ) | p.1.2.2.2 ≤ 0}
        ∪ {p | Tendsto (fun n => lateFraction p.2 i j p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 n
            - lateProbability f i j p.1.1 p.1.2.1) atTop (𝓝 0)}) := by
    intro θ
    rw [hD.map_paused_eq_pathLaw]
    rcases le_or_gt θ.2.2.2 0 with hℓ | hℓ
    · exact Filter.Eventually.of_forall fun x => Or.inl hℓ
    · rw [← map_cellPaused_eq_pathLaw f hℓ]
      refine (ae_map_iff (measurable_cellPaused θ.2.2.2).aemeasurable
        (hG.preimage measurable_prodMk_left)).mpr ?_
      filter_upwards [ae_tendsto_lateFraction_cells f hℓ i j θ.1 θ.2.1 θ.2.2.1] with ω hω
      exact Or.inr (tendsto_sub_nhds_zero_iff.mpr hω)
  filter_upwards [ae_mem_of_indepFun hΘ hX hind hG h] with ω hω hℓ
  rcases hω with hle | htend
  · exact absurd hℓ (not_lt.mpr hle)
  · exact tendsto_sub_nhds_zero_iff.mp htend

end Law

/-! ## The numbers of a draw are independent of its paused times -/

/-- The components of a draw that are numbers: the split of each pair of
hosts, the offset and the mean rate of each host's clock, and the mean rate
of the clock of each audio device. -/
abbrev ScalarIndex (H : Type) (R : ℕ) : Type :=
  {z : Sym2 H // ¬ z.IsDiag} ⊕ H ⊕ H ⊕ Option (Fin R)

/-- The component of a draw that holds each of its numbers. -/
def scalarComponent : ScalarIndex H R → Component H R
  | .inl z => .split z
  | .inr (.inl h) => .offset h
  | .inr (.inr (.inl h)) => .logRate h
  | .inr (.inr (.inr x)) => .deviceLogRate x

/-- The numbers of a draw, with each pair of hosts taken in the order `o`. -/
def Draw.scalars (d : Draw H R) (o : Orientation H) : ScalarIndex H R → ℝ
  | .inl z => d.split (o z).1.1 (o z).1.2
  | .inr (.inl h) => d.offset h
  | .inr (.inr (.inl h)) => d.logRate h
  | .inr (.inr (.inr x)) => d.deviceLogRate x

/-- The value of a component that is a number, as a number. -/
def scalarCast : (s : ScalarIndex H R) → (scalarComponent s).Val → ℝ
  | .inl _ => id
  | .inr (.inl _) => id
  | .inr (.inr (.inl _)) => id
  | .inr (.inr (.inr _)) => id

/-- The value of a component that is a paused time, as a function of true
time. -/
def pauseCast : (p : PauseIndex H) → (pauseComponent (R := R) p).Val → (Time → ℝ)
  | .inl _ => id
  | .inr _ => id

theorem measurable_scalarCast (s : ScalarIndex H R) : Measurable (scalarCast s) := by
  rcases s with z | h | h | x <;> exact measurable_id

theorem measurable_pauseCast (p : PauseIndex H) : Measurable (pauseCast (R := R) p) := by
  rcases p with ij | h <;> exact measurable_id

theorem scalarComponent_injective :
    Function.Injective (scalarComponent (H := H) (R := R)) := by
  rintro (z | h | h | x) (z' | h' | h' | x') hh <;> simp [scalarComponent] at hh <;> simp [hh]

theorem scalarComponent_ne_pause (s : ScalarIndex H R) (p : PauseIndex H) :
    scalarComponent s ≠ pauseComponent p := by
  rcases s with z | h | h | x <;> rcases p with ij | h' <;> simp [scalarComponent, pauseComponent]

section Scalars

variable {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R} {f : Member H R}
  {P : Measure Ω} {D : Ω → Draw H R}

/-- In a random world, each number of the draw is measurable up to a set of
probability zero. -/
theorem Prior.aemeasurable_scalar (hD : m.Prior f P D) (o : Orientation H)
    (s : ScalarIndex H R) : AEMeasurable (fun ω => (D ω).component o (scalarComponent s)) P := by
  rcases s with z | h | h | x
  · have hz : s((o z).1.1, (o z).1.2) = z.1 := (o z).2
    have hne : (o z).1.1 ≠ (o z).1.2 := by
      intro h
      apply z.2
      rw [← hz]
      exact Sym2.mk_isDiag_iff.mpr h
    exact (hD.split_law _ _ hne).aemeasurable
  · exact (hD.offset_law h).aemeasurable
  · exact (hD.logRate_law h).aemeasurable
  · exact (hD.deviceLogRate_law x).aemeasurable

/-- **The numbers of a draw are independent of its paused times.** In a
random world, the splits, the offsets and the mean rates of the clocks,
taken together, are independent of the paused times of the links and hosts,
taken together. -/
theorem Prior.indepFun_scalars_paused [Fintype H] (hD : m.Prior f P D) (o : Orientation H) :
    IndepFun (fun ω => (D ω).scalars o) (fun ω => (D ω).paused) P := by
  classical
  have hinj : Function.Injective
      (Sum.elim (scalarComponent (H := H) (R := R)) pauseComponent) := by
    rintro (s | p) (s' | p') hh
    · exact congrArg Sum.inl (scalarComponent_injective hh)
    · exact absurd hh (scalarComponent_ne_pause s p')
    · exact absurd hh.symm (scalarComponent_ne_pause s' p)
    · exact congrArg Sum.inr (pauseComponent_injective hh)
  have hfam := (hD.independent o).precomp hinj
  have hae : ∀ k : ScalarIndex H R ⊕ PauseIndex H, AEMeasurable (fun ω =>
      (D ω).component o (Sum.elim (scalarComponent (H := H) (R := R)) pauseComponent k)) P := by
    rintro (s | p)
    · exact hD.aemeasurable_scalar o s
    · rcases p with ij | h
      · exact hD.aemeasurable_paused (.inl ij)
      · exact hD.aemeasurable_paused (.inr h)
  obtain ⟨S, hS⟩ : ∃ S : Finset (ScalarIndex H R ⊕ PauseIndex H), ∀ k, k ∈ S ↔ ∃ s, Sum.inl s = k :=
    ⟨Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩, fun k => by simp⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (ScalarIndex H R ⊕ PauseIndex H), ∀ k, k ∈ T ↔ ∃ p, Sum.inr p = k :=
    ⟨Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩, fun k => by simp⟩
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    obtain ⟨s, rfl⟩ := (hS k).mp hkS
    obtain ⟨p, hp⟩ := (hT _).mp hkT
    exact Sum.inr_ne_inl hp
  have hST := hfam.indepFun_finset₀ S T hdisj hae
  have hφ : Measurable fun (u : (k : ↥S) →
        (Sum.elim (scalarComponent (H := H) (R := R)) pauseComponent k).Val)
      (s : ScalarIndex H R) => scalarCast s (u ⟨Sum.inl s, (hS _).mpr ⟨s, rfl⟩⟩) :=
    measurable_pi_iff.mpr fun s => (measurable_scalarCast s).comp
      (measurable_pi_apply (⟨Sum.inl s, (hS _).mpr ⟨s, rfl⟩⟩ : ↥S))
  have hψ : Measurable fun (u : (k : ↥T) →
        (Sum.elim (scalarComponent (H := H) (R := R)) pauseComponent k).Val)
      (p : PauseIndex H) => pauseCast p (u ⟨Sum.inr p, (hT _).mpr ⟨p, rfl⟩⟩) :=
    measurable_pi_iff.mpr fun p => (measurable_pauseCast p).comp
      (measurable_pi_apply (⟨Sum.inr p, (hT _).mpr ⟨p, rfl⟩⟩ : ↥T))
  have hcomp := hST.comp hφ hψ
  have e1 : (fun ω => (D ω).scalars o)
      = (fun (u : (k : ↥S) →
            (Sum.elim (scalarComponent (H := H) (R := R)) pauseComponent k).Val)
          (s : ScalarIndex H R) => scalarCast s (u ⟨Sum.inl s, (hS _).mpr ⟨s, rfl⟩⟩))
        ∘ fun ω (k : ↥S) => (D ω).component o
            (Sum.elim (scalarComponent (H := H) (R := R)) pauseComponent k) := by
    funext ω s
    rcases s with z | h | h | x <;> rfl
  have e2 : (fun ω => (D ω).paused)
      = (fun (u : (k : ↥T) →
            (Sum.elim (scalarComponent (H := H) (R := R)) pauseComponent k).Val)
          (p : PauseIndex H) => pauseCast p (u ⟨Sum.inr p, (hT _).mpr ⟨p, rfl⟩⟩))
        ∘ fun ω (k : ↥T) => (D ω).component o
            (Sum.elim (scalarComponent (H := H) (R := R)) pauseComponent k) := by
    funext ω p
    rcases p with ij | h <;> rfl
  rw [e1, e2]
  exact hcomp

/-- In a random world, the numbers of the draw, taken together, are
measurable up to a set of probability zero. -/
theorem Prior.aemeasurable_scalars [Finite H] (hD : m.Prior f P D) (o : Orientation H) :
    AEMeasurable (fun ω => (D ω).scalars o) P := by
  refine AEMeasurable.of_eval fun s => ?_
  have h := (measurable_scalarCast s).comp_aemeasurable (hD.aemeasurable_scalar o s)
  have e : (fun ω => (D ω).scalars o s)
      = scalarCast s ∘ fun ω => (D ω).component o (scalarComponent s) := by
    funext ω
    rcases s with z | h | h | x <;> rfl
  rw [e]
  exact h

/-- **The long-run fraction of late messages when the times of sending depend
on the clocks.** In a random world of a member, let the least delay `δ`, the
time `μ`, the first true time of sending `h₀` and the time `ℓ` between two
messages be any measurable functions of the numbers of the draw: the splits,
the offsets and the mean rates of the clocks. In almost every outcome in
which `ℓ` is positive, the fraction of the first `n` messages that take
longer than `μ` converges to `lateProbability` for the `δ` and `μ` of the
outcome. -/
theorem Prior.ae_lateFraction_scalars [Fintype H] (hD : m.Prior f P D) (o : Orientation H)
    (i j : H) {Φ : (ScalarIndex H R → ℝ) → ℝ × ℝ × ℝ × ℝ} (hΦ : Measurable Φ) :
    ∀ᵐ ω ∂P, 0 < (Φ ((D ω).scalars o)).2.2.2 →
      Filter.Tendsto (fun n => lateFraction (D ω).paused i j (Φ ((D ω).scalars o)).1
        (Φ ((D ω).scalars o)).2.1 (Φ ((D ω).scalars o)).2.2.1 (Φ ((D ω).scalars o)).2.2.2 n)
        Filter.atTop (nhds (lateProbability f i j (Φ ((D ω).scalars o)).1
          (Φ ((D ω).scalars o)).2.1)) :=
  hD.ae_lateFraction_indep i j (hΦ.comp_aemeasurable (hD.aemeasurable_scalars o))
    ((hD.indepFun_scalars_paused o).comp hΦ measurable_id)

end Scalars

end Unisono.Spec.GenerativeWorld
