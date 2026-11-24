/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ErgodicCells
public import Unisono.Spec.Models.GenerativePauses
public import Unisono.Spec.Models.IncrementLaw

/-!
# The pauses of a member have one law

A member of the generative model has many random worlds. This file shows
that the paused times of all its links and hosts, taken together as functions
of true time, have the same law in every one of them, and that this law is
the one of independent cells.

* `Draw.paused`: the paused time of each link and of each host of a draw.
* `pauseCellsLaw`, `cellPaused`: independent cells that each last `ℓ`
  seconds, and the paused times that they give. In each cell the number of
  pauses of a link or of a host has the Poisson law, with the mean number of
  pauses that begin in `ℓ` seconds.
* `Prior.map_paused`: in every random world of a member, the paused times of
  the links and of the hosts have the law of `cellPaused`, whatever `ℓ` is.
* `Prior.ae_paused_mem`: so a measurable property of the paused times that
  holds in almost every outcome of the cells holds in almost every outcome
  of every random world of the member.

The length `ℓ` of a cell is free because moving the cells by one cell moves
true time by `ℓ` seconds: a quantity that is read at times `ℓ` seconds apart
becomes a quantity along the orbit of that move, to which the ergodic theorem
of `Unisono.Spec.Models.ErgodicCells` applies.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Independent cells whose parts are independent -/

section Rows

variable {J S : Type*} [Fintype J] [MeasurableSpace S] (ν : J → Measure S)
  [∀ x, IsProbabilityMeasure (ν x)]

/-- When the cells are independent and each cell has one part for each index
`x`, the parts `x` of all cells have the law of independent cells. -/
theorem map_row (x : J) :
    (Measure.infinitePi fun _ : ℤ => Measure.pi ν).map (fun (ω : ℤ → J → S) c => ω c x)
      = Measure.infinitePi fun _ : ℤ => ν x := by
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℤ => Measure.pi ν)
    (f := fun (_ : ℤ) (s : J → S) => s x) (fun _ => measurable_pi_apply x)
  refine h.trans ?_
  congr 1
  funext c
  exact (measurePreserving_eval ν x).map_eq

/-- When the cells are independent and the parts of each cell are
independent, the families of the parts, one family for each index, have the
law of independent families of independent cells. -/
theorem map_rows :
    (Measure.infinitePi fun _ : ℤ => Measure.pi ν).map (fun (ω : ℤ → J → S) x c => ω c x)
      = Measure.pi fun x => Measure.infinitePi fun _ : ℤ => ν x := by
  have e0 : (Measure.infinitePi fun _ : ℤ => Measure.pi ν)
      = Measure.infinitePi fun _ : ℤ => Measure.infinitePi fun x : J => ν x := by
    congr 1
    funext c
    exact (Measure.infinitePi_eq_pi _).symm
  have e1 := Measure.infinitePi_map_curry_symm (fun (_ : ℤ) (x : J) => ν x)
  have e2 := Measure.infinitePi_map_curry (fun (x : J) (_ : ℤ) => ν x)
  have e3 := Measure.infinitePi_map_piCongrLeft (μ := fun q : J × ℤ => ν q.1)
    (Equiv.prodComm ℤ J)
  have hfun : (fun (ω : ℤ → J → S) x c => ω c x)
      = (MeasurableEquiv.curry J ℤ S) ∘ ((MeasurableEquiv.piCongrLeft (fun _ : J × ℤ => S)
          (Equiv.prodComm ℤ J)) ∘ (MeasurableEquiv.curry ℤ J S).symm) := by
    funext ω x c
    exact (MeasurableEquiv.piCongrLeft_apply_apply (Equiv.prodComm ℤ J)
      (β := fun _ : J × ℤ => S) (Function.uncurry ω) (c, x)).symm
  calc (Measure.infinitePi fun _ : ℤ => Measure.pi ν).map (fun (ω : ℤ → J → S) x c => ω c x)
      = (((Measure.infinitePi fun _ : ℤ => Measure.infinitePi fun x : J => ν x).map
            (MeasurableEquiv.curry ℤ J S).symm).map
          (MeasurableEquiv.piCongrLeft (fun _ : J × ℤ => S) (Equiv.prodComm ℤ J))).map
        (MeasurableEquiv.curry J ℤ S) := by
        rw [hfun, e0, Measure.map_map (MeasurableEquiv.measurable _)
            (MeasurableEquiv.measurable _),
          Measure.map_map ((MeasurableEquiv.measurable _).comp (MeasurableEquiv.measurable _))
            (MeasurableEquiv.measurable _)]
        rfl
    _ = ((Measure.infinitePi fun p : ℤ × J => ν p.2).map
          (MeasurableEquiv.piCongrLeft (fun _ : J × ℤ => S) (Equiv.prodComm ℤ J))).map
        (MeasurableEquiv.curry J ℤ S) := by rw [e1]
    _ = (Measure.infinitePi fun q : J × ℤ => ν q.1).map (MeasurableEquiv.curry J ℤ S) := by
        congr 1
    _ = Measure.infinitePi fun x : J => Measure.infinitePi fun _ : ℤ => ν x := e2
    _ = Measure.pi fun x => Measure.infinitePi fun _ : ℤ => ν x := Measure.infinitePi_eq_pi _

/-- When the cells are independent and the parts of each cell are
independent, the families of the parts, one family for each index, are
independent. -/
theorem iIndepFun_rows :
    iIndepFun (fun (x : J) (ω : ℤ → J → S) (c : ℤ) => ω c x)
      (Measure.infinitePi fun _ : ℤ => Measure.pi ν) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map fun x => (measurable_pi_iff.mpr fun c =>
    (measurable_pi_apply x).comp (measurable_pi_apply c)).aemeasurable).mpr ?_
  refine (map_rows ν).trans ?_
  congr 1
  funext x
  exact (map_row ν x).symm

end Rows

namespace GenerativeWorld

variable {H : Type} {R : ℕ}

/-! ## The links and the hosts of a member -/

/-- Everything that pauses: the links, each a pair of hosts in one direction,
and the hosts. -/
abbrev PauseIndex (H : Type) : Type := (H × H) ⊕ H

/-- How many pauses of a link or of a host begin per second, on average. -/
def Member.pauseRate (f : Member H R) : PauseIndex H → ℝ
  | .inl ij => f.linkPauseRate ij.1 ij.2
  | .inr h => f.hostPauseRate h

/-- The law of the length of a pause of a link or of a host. -/
def Member.pauseLength (f : Member H R) : PauseIndex H → Measure ℝ
  | .inl ij => f.linkPauseLength ij.1 ij.2
  | .inr h => f.hostPauseLength h

theorem Member.pauseRate_nonneg (f : Member H R) (x : PauseIndex H) : 0 ≤ f.pauseRate x := by
  cases x with
  | inl ij => exact f.linkPauseRate_nonneg _ _
  | inr h => exact f.hostPauseRate_nonneg h

instance Member.pauseLength_prob (f : Member H R) (x : PauseIndex H) :
    IsProbabilityMeasure (f.pauseLength x) := by
  cases x with
  | inl ij => exact f.linkPauseLength_prob _ _
  | inr h => exact f.hostPauseLength_prob h

theorem Member.pauseLength_pos (f : Member H R) (x : PauseIndex H) :
    f.pauseLength x (Set.Iic 0) = 0 := by
  cases x with
  | inl ij => exact f.linkPauseLength_pos _ _
  | inr h => exact f.hostPauseLength_pos h

theorem Member.pauseLength_mean (f : Member H R) (x : PauseIndex H) :
    Integrable (fun y : ℝ => y) (f.pauseLength x) := by
  cases x with
  | inl ij => exact f.linkPauseLength_mean _ _
  | inr h => exact f.hostPauseLength_mean h

theorem Member.pauseLoad_lt_one (f : Member H R) (x : PauseIndex H) :
    f.pauseRate x * ∫ y, y ∂f.pauseLength x < 1 := by
  cases x with
  | inl ij => exact f.linkLoad_lt_one _ _
  | inr h => exact f.hostLoad_lt_one h

/-- The law of the paused time of a link or of a host that begins between
the true times `s` and `t`. -/
def Member.pauseIncrementLaw (f : Member H R) (x : PauseIndex H) (s t : ℝ) : Measure ℝ :=
  pauseLaw (Real.toNNReal (f.pauseRate x * (t - s))) (f.pauseLength x)

/-- The paused time of each link and of each host of a draw. -/
def Draw.paused (d : Draw H R) : PauseIndex H → Time → ℝ
  | .inl ij => d.linkPaused ij.1 ij.2
  | .inr h => d.hostPaused h

/-! ## The paused times of a random world -/

section Prior

variable {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R} {f : Member H R}
  {P : Measure Ω} {D : Ω → Draw H R}

/-- In a random world, the paused time of each link and of each host starts
at zero and has independent increments with the laws of the member. -/
theorem Prior.hasIncrementLaws_paused (hD : m.Prior f P D) (x : PauseIndex H) :
    HasIncrementLaws (f.pauseIncrementLaw x) (fun t ω => (D ω).paused x t) P := by
  cases x with
  | inl ij =>
    exact ⟨fun ω => hD.linkPaused_zero ω _ _, hD.linkPaused_increments _ _,
      fun s t hst => hD.linkPaused_law _ _ s t hst⟩
  | inr h =>
    exact ⟨fun ω => hD.hostPaused_zero ω h, hD.hostPaused_increments h,
      fun s t hst => hD.hostPaused_law h s t hst⟩

/-- In a random world, the paused time of each link and of each host, as a
function of true time, is measurable up to a set of probability zero. -/
theorem Prior.aemeasurable_paused (hD : m.Prior f P D) (x : PauseIndex H) :
    AEMeasurable (fun ω t => (D ω).paused x t) P := by
  refine aemeasurable_path (fun t => (hD.hasIncrementLaws_paused x).aemeasurable t)
    fun ω t => ?_
  cases x with
  | inl ij => exact hD.linkPaused_rightContinuous ω _ _ t
  | inr h => exact hD.hostPaused_rightContinuous ω h t

/-- The component of a draw that holds the paused time of a link or of a
host. -/
def pauseComponent : PauseIndex H → Component H R
  | .inl ij => .linkPaused ij.1 ij.2
  | .inr h => .hostPaused h

theorem pauseComponent_injective : Function.Injective (pauseComponent (H := H) (R := R)) := by
  rintro (⟨i, j⟩ | h) (⟨i', j'⟩ | h') hxy
  · simp only [pauseComponent, Component.linkPaused.injEq] at hxy
    rw [hxy.1, hxy.2]
  · simp [pauseComponent] at hxy
  · simp [pauseComponent] at hxy
  · simp only [pauseComponent, Component.hostPaused.injEq] at hxy
    rw [hxy]

/-- In a random world, the paused times of the links and of the hosts are
independent. -/
theorem Prior.iIndepFun_paused (hD : m.Prior f P D) :
    iIndepFun (fun (x : PauseIndex H) ω t => (D ω).paused x t) P := by
  have h1 := (hD.independent (refOrientation H)).precomp
    (pauseComponent_injective (H := H) (R := R))
  have h2 := h1.comp
    (fun x : PauseIndex H => (Sum.casesOn x (fun _ => id) (fun _ => id) :
      (pauseComponent (R := R) x).Val → (Time → ℝ)))
    (fun x => by cases x <;> exact measurable_id)
  have e : (fun (x : PauseIndex H) ω t => (D ω).paused x t)
      = fun x : PauseIndex H => (Sum.casesOn x (fun _ => id) (fun _ => id) :
          (pauseComponent (R := R) x).Val → (Time → ℝ))
        ∘ fun ω => (D ω).component (refOrientation H) (pauseComponent x) := by
    funext x
    cases x <;> rfl
  rw [e]
  exact h2

end Prior

/-! ## The paused times of independent cells -/

section Cells

variable [Fintype H]

/-- The law of the cells of all links and hosts, when one cell lasts `ℓ`
seconds: the cells are independent, and in each cell the links and the hosts
are independent, each with the law of a cell for the number of its pauses
that begin in `ℓ` seconds on average. -/
def pauseCellsLaw (f : Member H R) (ℓ : ℝ) : Measure (ℤ → PauseIndex H → Cell) :=
  Measure.infinitePi fun _ : ℤ =>
    Measure.pi fun x => cellLaw (Real.toNNReal (f.pauseRate x * ℓ)) (f.pauseLength x)

instance (f : Member H R) (ℓ : ℝ) : IsProbabilityMeasure (pauseCellsLaw f ℓ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℤ =>
    Measure.pi fun x => cellLaw (Real.toNNReal (f.pauseRate x * ℓ)) (f.pauseLength x)))

/-- The paused time of each link and of each host that the cells give, when
one cell lasts `ℓ` seconds. -/
def cellPaused (ℓ : ℝ) (ω : ℤ → PauseIndex H → Cell) (x : PauseIndex H) (t : Time) : ℝ :=
  pausedPath (fun c => ω c x) (t / ℓ)

omit [Fintype H] in
theorem measurable_cellPaused (ℓ : ℝ) : Measurable (cellPaused (H := H) ℓ) :=
  measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun t =>
    (measurable_pausedPath (t / ℓ)).comp (measurable_pi_iff.mpr fun c =>
      (measurable_pi_apply x).comp (measurable_pi_apply c))

/-- The cells of one link or host have the law of its independent cells. -/
theorem measurePreserving_row (f : Member H R) (ℓ : ℝ) (x : PauseIndex H) :
    MeasurePreserving (fun (ω : ℤ → PauseIndex H → Cell) c => ω c x) (pauseCellsLaw f ℓ)
      (cellsLaw (Real.toNNReal (f.pauseRate x * ℓ)) (f.pauseLength x)) :=
  ⟨measurable_pi_iff.mpr fun c => (measurable_pi_apply x).comp (measurable_pi_apply c),
    map_row (fun x => cellLaw (Real.toNNReal (f.pauseRate x * ℓ)) (f.pauseLength x)) x⟩

/-- The paused time that the cells give starts at zero and has independent
increments with the laws of the member. -/
theorem hasIncrementLaws_cellPaused (f : Member H R) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : PauseIndex H) :
    HasIncrementLaws (f.pauseIncrementLaw x) (fun t ω => cellPaused ℓ ω x t)
      (pauseCellsLaw f ℓ) where
  zero := fun ω => by
    show pausedPath _ (0 / ℓ) = 0
    rw [zero_div]
    exact pausedPath_zero _
  indep := by
    intro n τ hτ
    have hτ' : Monotone fun i => τ i / ℓ := fun a b hab =>
      div_le_div_of_nonneg_right (hτ hab) hℓ.le
    exact iIndepFun_of_measurePreserving (measurePreserving_row f ℓ x)
      (fun i : Fin n => (measurable_pausedPath _).sub (measurable_pausedPath _))
      (hasIndepIncrements_pausedPath _ _ (f.pauseLength_pos x) n (fun i => τ i / ℓ) hτ')
  law := by
    intro s t hst
    have hst' : s / ℓ ≤ t / ℓ := div_le_div_of_nonneg_right hst hℓ.le
    have h := (hasLaw_pausedPath_sub (Real.toNNReal (f.pauseRate x * ℓ)) (f.pauseLength x)
      (f.pauseLength_pos x) hst').fun_comp (measurePreserving_row f ℓ x).hasLaw
    have e : ((Real.toNNReal (f.pauseRate x * ℓ) : ℝ≥0) : ℝ) * (t / ℓ - s / ℓ)
        = f.pauseRate x * (t - s) := by
      rw [Real.coe_toNNReal _ (mul_nonneg (f.pauseRate_nonneg x) hℓ.le)]
      field_simp
    rw [e] at h
    exact h

/-- The paused times that the cells give for the links and for the hosts are
independent. -/
theorem iIndepFun_cellPaused (f : Member H R) (ℓ : ℝ) :
    iIndepFun (fun (x : PauseIndex H) ω t => cellPaused ℓ ω x t) (pauseCellsLaw f ℓ) :=
  (iIndepFun_rows fun x => cellLaw (Real.toNNReal (f.pauseRate x * ℓ)) (f.pauseLength x)).comp
    (fun _ (ω' : Cells) t => pausedPath ω' (t / ℓ))
    fun _ => measurable_pi_iff.mpr fun t => measurable_pausedPath (t / ℓ)

/-- **The pauses of a member have one law.** In every random world of a
member, the paused times of all links and hosts, as functions of true time,
have the law of the paused times that independent cells give, whatever the
length `ℓ` of a cell is. -/
theorem Prior.map_paused {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R}
    {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    P.map (fun ω => (D ω).paused) = (pauseCellsLaw f ℓ).map (cellPaused ℓ) := by
  have := hD.prob
  exact map_paths_eq (fun x => hD.hasIncrementLaws_paused x)
    (fun x => hasIncrementLaws_cellPaused f hℓ x) (fun x => hD.aemeasurable_paused x)
    (fun x => (measurable_pi_iff.mp (measurable_cellPaused ℓ) x).aemeasurable)
    hD.iIndepFun_paused (iIndepFun_cellPaused f ℓ)

/-- **A property of the pauses that holds for the cells holds in every
random world.** If a measurable set of paused times holds the paused times of
almost every outcome of the cells, for one length of a cell, then it holds
the paused times of almost every outcome of every random world of the
member. -/
theorem Prior.ae_paused_mem {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R}
    {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {𝒮 : Set (PauseIndex H → Time → ℝ)} (h𝒮 : MeasurableSet 𝒮)
    (h : ∀ᵐ ω ∂pauseCellsLaw f ℓ, cellPaused ℓ ω ∈ 𝒮) :
    ∀ᵐ ω ∂P, (D ω).paused ∈ 𝒮 := by
  have hm : AEMeasurable (fun ω => (D ω).paused) P :=
    AEMeasurable.of_eval fun x => hD.aemeasurable_paused x
  have h1 : ∀ᵐ y ∂(pauseCellsLaw f ℓ).map (cellPaused ℓ), y ∈ 𝒮 :=
    (ae_map_iff (measurable_cellPaused ℓ).aemeasurable h𝒮).mpr h
  rw [← hD.map_paused hℓ] at h1
  exact (ae_map_iff hm h𝒮).mp h1

end Cells

end GenerativeWorld

end Unisono.Spec
