/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeNoiseless
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# A random world for every noiseless member

Every noiseless member of the generative model, with any number of hosts and
speakers, has a random world (`exists_holds_of_noiseless`).

The random world is built on a concrete probability space. An outcome is one
real number for each component of a draw (`Component H → ℝ`), and the numbers
are independent: each has the law of its component (`canonicalLaw`). The draw
of an outcome takes its splits and offsets from these numbers
(`canonicalDraw`), and its world is the ideal constant world with those
offsets and with the least delays that the splits give (`canonicalWorld`).

The same construction serves the proofs about noiseless members: a statement
about the expected cost of a solution can be checked on this one probability
space, where an outcome can be changed coordinate by coordinate.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Random variables that are constant are independent. -/
theorem iIndepFun_of_const {Ω : Type} [MeasurableSpace Ω] {ι : Type} {β : ι → Type}
    [∀ i, MeasurableSpace (β i)] (P : Measure Ω) [IsProbabilityMeasure P] (c : ∀ i, β i) :
    iIndepFun (fun i (_ : Ω) => c i) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, c i ∈ sets i
  · have h1 : (⋂ i ∈ S, (fun _ : Ω => c i) ⁻¹' sets i) = Set.univ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
      exact h
    rw [h1, measure_univ]
    symm
    refine Finset.prod_eq_one fun i hi => ?_
    have h2 : (fun _ : Ω => c i) ⁻¹' sets i = Set.univ := by
      ext ω
      simp [h i hi]
    rw [h2, measure_univ]
  · push Not at h
    obtain ⟨i, hi, hci⟩ := h
    have h0 : (fun _ : Ω => c i) ⁻¹' sets i = ∅ := by
      ext ω
      simp [hci]
    have h1 : (⋂ i ∈ S, (fun _ : Ω => c i) ⁻¹' sets i) = ∅ := by
      refine Set.eq_empty_of_subset_empty ?_
      rw [← h0]
      exact Set.biInter_subset_of_mem hi
    rw [h1, measure_empty]
    symm
    exact Finset.prod_eq_zero hi (by rw [h0, measure_empty])

/-- The process that is zero at all times is a Gaussian process. -/
theorem isGaussianProcess_zero {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] : IsGaussianProcess (fun (_ : Time) (_ : Ω) => (0 : ℝ)) P where
  hasGaussianLaw I :=
    { aemeasurable := aemeasurable_const
      isGaussian_map := by
        rw [Measure.map_const, measure_univ, one_smul]
        infer_instance }

namespace GenerativeWorld

variable {H : Type} {R : ℕ}

/-! ## The components of a draw as coordinates -/

/-- The components of a draw, listed by kind. -/
def componentEquiv (H : Type) :
    Component H ≃ ({z : Sym2 H // ¬ z.IsDiag} ⊕ H) ⊕ (H ⊕ H) ⊕ (H × H) where
  toFun
    | .split z => .inl (.inl z)
    | .offset h => .inl (.inr h)
    | .logRate h => .inr (.inl (.inl h))
    | .wander h => .inr (.inl (.inr h))
    | .traffic i j => .inr (.inr (i, j))
  invFun
    | .inl (.inl z) => .split z
    | .inl (.inr h) => .offset h
    | .inr (.inl (.inl h)) => .logRate h
    | .inr (.inl (.inr h)) => .wander h
    | .inr (.inr (i, j)) => .traffic i j
  left_inv := by rintro (_ | _ | _ | _ | _) <;> rfl
  right_inv := by rintro ((_ | _) | (_ | _) | ⟨_, _⟩) <;> rfl

/-- The components of a draw are finitely many when the hosts are. -/
instance [Fintype H] [DecidableEq H] : Fintype (Component H) :=
  Fintype.ofEquiv _ (componentEquiv H).symm

/-- A number moved into the open interval from zero to one: itself if it lies
there, one half otherwise. -/
def splitOf (u : ℝ) : ℝ := if 0 < u ∧ u < 1 then u else 1 / 2

theorem splitOf_mem (u : ℝ) : splitOf u ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold splitOf
  split_ifs with h
  · exact h
  · constructor <;> norm_num

theorem measurable_splitOf : Measurable splitOf :=
  Measurable.ite (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) measurable_id measurable_const

/-- A split with a Beta law lies between zero and one, so moving it into that
interval changes nothing. -/
theorem splitOf_ae_eq (a b : ℝ) : splitOf =ᵐ[betaMeasure a b] id := by
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun u hu => ?_) (betaMeasure_compl_Ioo a b)
  intro hmem
  exact hu (by simp [splitOf, hmem.1, hmem.2])

/-- Moving into the interval commutes with taking the other direction's
share. -/
theorem splitOf_one_sub (u : ℝ) : splitOf (1 - u) = 1 - splitOf u := by
  unfold splitOf
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨by linarith [h1.2], by linarith [h1.1]⟩ h2
  · exact absurd ⟨by linarith [h2.2], by linarith [h2.1]⟩ h1
  · norm_num

/-- The pair of two distinct hosts. -/
def pairOf (i j : H) (h : i ≠ j) : {z : Sym2 H // ¬ z.IsDiag} :=
  ⟨s(i, j), by simpa using h⟩

theorem pairOf_swap {i j : H} (h : i ≠ j) : pairOf j i h.symm = pairOf i j h :=
  Subtype.ext Sym2.eq_swap

/-- A fixed order of every pair of distinct hosts, chosen once. -/
def refOrientation (H : Type) : Orientation H := fun z =>
  ⟨Quot.out z.1, Quot.out_eq z.1⟩

/-- The fixed order of the pair of `i` and `j` is `(i, j)` or `(j, i)`. -/
theorem refOrientation_pairOf (i j : H) (h : i ≠ j) :
    (refOrientation H (pairOf i j h)).1 = (i, j)
      ∨ (refOrientation H (pairOf i j h)).1 = (j, i) := by
  have hp := (refOrientation H (pairOf i j h)).2
  rcases Sym2.eq_iff.mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

/-- The law of each coordinate: the Beta law for the split of a pair, the
uniform law for the offset of a clock, and zero for the mean rate, the wander
and the traffic, which a noiseless member does not have. -/
def canonicalLaw (m : GenerativeWorld H R) (f : Member H R) : Component H → Measure ℝ
  | .split _ => betaMeasure m.shape m.shape
  | .offset _ => ProbabilityTheory.cond volume (Set.Icc (-f.offsetRange) f.offsetRange)
  | .logRate _ => Measure.dirac 0
  | .wander _ => Measure.dirac 0
  | .traffic _ _ => Measure.dirac 0

instance (m : GenerativeWorld H R) (f : Member H R) (p : Component H) :
    IsProbabilityMeasure (canonicalLaw m f p) := by
  cases p
  · exact isProbabilityMeasureBeta m.shape_pos m.shape_pos
  · have hpos : 0 < f.offsetRange - -f.offsetRange := by linarith [f.offsetRange_pos]
    exact cond_isProbabilityMeasure_of_finite
      (by rw [Real.volume_Icc]; exact (ENNReal.ofReal_pos.mpr hpos).ne')
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))

section Draw

variable [DecidableEq H]

/-- The draw of an outcome: the split of a pair, in its fixed order, and the
offsets are coordinates of the outcome; the mean rates are one, and there is
no wander and no other traffic. -/
def canonicalDraw (y : Component H → ℝ) : Draw H where
  split := fun i j =>
    if h : i = j then 1 / 2
    else if (refOrientation H (pairOf i j h)).1 = (i, j) then
      splitOf (y (.split (pairOf i j h)))
    else 1 - splitOf (y (.split (pairOf i j h)))
  offset := fun h => y (.offset h)
  logRate := fun _ => 0
  wander := fun _ _ => 0
  traffic := fun _ _ _ => 0

theorem canonicalDraw_split_mem (y : Component H → ℝ) (i j : H) :
    (canonicalDraw y).split i j ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [canonicalDraw]
  split_ifs with h h'
  · constructor <;> norm_num
  · exact splitOf_mem _
  · have := splitOf_mem (y (.split (pairOf i j h)))
    exact ⟨by linarith [this.2], by linarith [this.1]⟩

theorem canonicalDraw_split_swap (y : Component H → ℝ) (i j : H) :
    (canonicalDraw y).split i j + (canonicalDraw y).split j i = 1 := by
  by_cases h : i = j
  · subst h
    simp only [canonicalDraw]
    norm_num
  · have hji : j ≠ i := Ne.symm h
    simp only [canonicalDraw, dite_eq_right h, dite_eq_right hji]
    have hsw : pairOf j i hji = pairOf i j h := pairOf_swap h
    rw [hsw]
    rcases refOrientation_pairOf i j h with hp | hp
    · have hne : (refOrientation H (pairOf i j h)).1 ≠ (j, i) := by
        rw [hp]
        intro he
        exact h (Prod.ext_iff.mp he).1
      rw [ite_eq_left hp, ite_eq_right hne]
      ring
    · have hne : (refOrientation H (pairOf i j h)).1 ≠ (i, j) := by
        rw [hp]
        intro he
        exact h (Prod.ext_iff.mp he).2
      rw [ite_eq_right hne, ite_eq_left hp]
      ring

/-- How each component of the draw of an outcome depends on its coordinate,
when the pairs are taken in the order `o`. -/
def canonicalMap (o : Orientation H) : (p : Component H) → ℝ → p.Val
  | .split z => fun u => if (refOrientation H z).1 = (o z).1 then splitOf u else 1 - splitOf u
  | .offset _ => fun u => u
  | .logRate _ => fun _ => (0 : ℝ)
  | .wander _ => fun _ _ => 0
  | .traffic _ _ => fun _ _ => 0

theorem measurable_canonicalMap (o : Orientation H) (p : Component H) :
    Measurable (canonicalMap o p) := by
  cases p with
  | split z =>
    exact Measurable.ite (MeasurableSet.const _) measurable_splitOf
      (measurable_splitOf.const_sub 1)
  | offset h => exact measurable_id
  | logRate h => exact measurable_const
  | wander h => exact measurable_const
  | traffic i j => exact measurable_const

theorem canonicalDraw_component (o : Orientation H) (p : Component H)
    (y : Component H → ℝ) :
    (canonicalDraw y).component o p = canonicalMap o p (y p) := by
  cases p with
  | split z =>
    have hz : s((o z).1.1, (o z).1.2) = z.1 := (o z).2
    have hne : (o z).1.1 ≠ (o z).1.2 := by
      intro h
      apply z.2
      rw [← hz]
      exact Sym2.mk_isDiag_iff.mpr h
    have hpair : pairOf (o z).1.1 (o z).1.2 hne = z := Subtype.ext hz
    have hsplit : (canonicalDraw y).split (o z).1.1 (o z).1.2
        = if (refOrientation H (pairOf (o z).1.1 (o z).1.2 hne)).1 = ((o z).1.1, (o z).1.2) then
            splitOf (y (.split (pairOf (o z).1.1 (o z).1.2 hne)))
          else 1 - splitOf (y (.split (pairOf (o z).1.1 (o z).1.2 hne))) := by
      simp only [canonicalDraw, dite_eq_right hne]
    rw [hpair] at hsplit
    change (canonicalDraw y).split (o z).1.1 (o z).1.2 = _
    rw [hsplit]
    rfl
  | offset h => rfl
  | logRate h => rfl
  | wander h => rfl
  | traffic i j => rfl

variable [Fintype H]

/-- The split of two distinct hosts has the Beta law on the concrete
probability space. -/
theorem canonicalDraw_split_law (m : GenerativeWorld H R) (f : Member H R) {i j : H}
    (hij : i ≠ j) :
    HasLaw (fun y : Component H → ℝ => (canonicalDraw y).split i j)
      (betaMeasure m.shape m.shape) (Measure.pi (canonicalLaw m f)) := by
  have hcoord : HasLaw (fun y : Component H → ℝ => y (.split (pairOf i j hij)))
      (betaMeasure m.shape m.shape) (Measure.pi (canonicalLaw m f)) :=
    (measurePreserving_eval (canonicalLaw m f) (.split (pairOf i j hij))).hasLaw
  have hto : HasLaw splitOf (betaMeasure m.shape m.shape) (betaMeasure m.shape m.shape) :=
    HasLaw.id.congr (splitOf_ae_eq m.shape m.shape)
  by_cases hp : (refOrientation H (pairOf i j hij)).1 = (i, j)
  · have heq : (fun y : Component H → ℝ => (canonicalDraw y).split i j)
        = fun y => splitOf (y (.split (pairOf i j hij))) := by
      funext y
      simp only [canonicalDraw, dite_eq_right hij, ite_eq_left hp]
    rw [heq]
    exact hto.fun_comp hcoord
  · have heq : (fun y : Component H → ℝ => (canonicalDraw y).split i j)
        = fun y => 1 - splitOf (y (.split (pairOf i j hij))) := by
      funext y
      simp only [canonicalDraw, dite_eq_right hij, ite_eq_right hp]
    rw [heq]
    have hsub : HasLaw (fun x : ℝ => 1 - x) (betaMeasure m.shape m.shape)
        (betaMeasure m.shape m.shape) :=
      ⟨by fun_prop, betaMeasure_map_one_sub m.shape⟩
    exact hsub.fun_comp (hto.fun_comp hcoord)

/-- **The draw of an outcome has the law of a noiseless member.** -/
theorem canonicalDraw_prior (m : GenerativeWorld H R) (f : Member H R) (hf : f.Noiseless) :
    m.Prior f (Measure.pi (canonicalLaw m f)) (canonicalDraw (H := H)) where
  prob := inferInstance
  split_swap := canonicalDraw_split_swap
  split_mem := canonicalDraw_split_mem
  split_law := fun i j hij => canonicalDraw_split_law m f hij
  offset_law := fun h => (measurePreserving_eval (canonicalLaw m f) (.offset h)).hasLaw
  logRate_law := fun h => by
    have h0 : Real.toNNReal (f.rateSpread ^ 2) = 0 := by simp [hf.no_spread]
    rw [h0, gaussianReal_zero_var]
    change HasLaw (fun _ => (0 : ℝ)) (Measure.dirac 0) _
    exact ⟨aemeasurable_const, by simp [Measure.map_const]⟩
  wander_gaussian := fun _ => isGaussianProcess_zero _
  wander_mean := fun _ _ => by simp [canonicalDraw]
  wander_covariance := fun h _ _ => by
    simp only [canonicalDraw]
    rw [covariance_const_left, hf.no_wander h]
    simp
  wander_continuous := fun _ _ => continuous_const
  traffic_monotone := fun _ _ _ => monotone_const
  traffic_zero := fun _ _ _ => rfl
  traffic_rightContinuous := fun _ _ _ _ => continuousWithinAt_const
  traffic_increments := fun _ _ _ _ _ => iIndepFun_of_const _ fun _ => (0 : ℝ) - 0
  traffic_law := fun i j s t _ => by
    have h0 : Real.toNNReal (f.trafficRate i j * (t - s)) = 0 := by
      simp [hf.no_traffic i j]
    rw [h0, trafficLaw_zero]
    change HasLaw (fun _ => (0 : ℝ) - 0) (Measure.dirac 0) _
    exact ⟨aemeasurable_const, by simp [Measure.map_const]⟩
  independent := fun o => by
    have h : (fun p (y : Component H → ℝ) => (canonicalDraw y).component o p)
        = fun p (y : Component H → ℝ) => canonicalMap o p (y p) := by
      funext p y
      exact canonicalDraw_component o p y
    rw [h]
    exact iIndepFun_pi fun p => (measurable_canonicalMap o p).aemeasurable

end Draw

/-! ## The ideal constant world of a noiseless draw -/

/-- The ideal constant world with the settings of the model `m`, the starts
of the member `f`, the clock offsets `offset` and the constant delays
`delay`. Every clock reads true time plus its offset, and every device runs
on the clock of its host at the nominal rate. -/
def idealWorld (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (offset : H → ℝ) (delay : H → H → ℝ)
    (hdelay : ∀ i j, 0 < delay i j) : World H R where
  rate := m.rate
  rate_pos := m.rate_pos
  sender := m.sender
  host := m.host
  hosts := hex
  clock := fun h =>
    { read := fun t => t + offset h
      strictMono := fun _ _ hab => by linarith
      continuous := by fun_prop }
  source :=
    { capture := fun n => f.captureStart - offset m.sender + (n : ℝ) / m.rate
      capture_strictMono := fun a b hab => by
        have h := mul_lt_mul_of_pos_right (Nat.cast_lt (α := ℝ).mpr hab) (inv_pos.mpr m.rate_pos)
        simp only [div_eq_mul_inv]
        linarith
      first := fun b => b * m.blockSize
      first_zero := Nat.zero_mul _
      first_strictMono := fun _ _ hab => Nat.mul_lt_mul_of_pos_right hab m.blockSize_pos
      handed := fun b =>
        f.captureStart - offset m.sender + (((b + 1) * m.blockSize - 1 : ℕ) : ℝ) / m.rate
      handed_strictMono := fun a b hab => by
        have hlt : (a + 1) * m.blockSize - 1 < (b + 1) * m.blockSize - 1 := by
          have h1 : (a + 1) * m.blockSize < (b + 1) * m.blockSize :=
            Nat.mul_lt_mul_of_pos_right (by omega) m.blockSize_pos
          have h2 : 0 < (a + 1) * m.blockSize := Nat.mul_pos (by omega) m.blockSize_pos
          omega
        have h := mul_lt_mul_of_pos_right (Nat.cast_lt (α := ℝ).mpr hlt) (inv_pos.mpr m.rate_pos)
        simp only [div_eq_mul_inv]
        linarith
      handed_after := fun _ => le_rfl
      reported := fun b => f.captureStart + ((b * m.blockSize : ℕ) : ℝ) / m.rate }
  speaker := fun r =>
    { out := fun k => f.speakerStart r - offset (m.host r) + (k : ℝ) / m.rate
      out_strictMono := fun a b hab => by
        have h := mul_lt_mul_of_pos_right (Nat.cast_lt (α := ℝ).mpr hab) (inv_pos.mpr m.rate_pos)
        simp only [div_eq_mul_inv]
        linarith
      first := fun b => b * m.blockSize
      first_zero := Nat.zero_mul _
      first_strictMono := fun _ _ hab => Nat.mul_lt_mul_of_pos_right hab m.blockSize_pos
      asked := fun b =>
        f.speakerStart r - offset (m.host r) + ((b * m.blockSize : ℕ) : ℝ) / m.rate - m.lead
      asked_strictMono := fun a b hab => by
        have hlt : a * m.blockSize < b * m.blockSize :=
          Nat.mul_lt_mul_of_pos_right hab m.blockSize_pos
        have h := mul_lt_mul_of_pos_right (Nat.cast_lt (α := ℝ).mpr hlt) (inv_pos.mpr m.rate_pos)
        simp only [div_eq_mul_inv]
        linarith
      asked_before := fun _ => by linarith [m.lead_pos]
      reported := fun b => f.speakerStart r + ((b * m.blockSize : ℕ) : ℝ) / m.rate }
  network :=
    { deliver := fun i j t _ => some (t + delay i j)
      after := fun i j t _ a h => by
        simp only [Option.some.injEq] at h
        linarith [hdelay i j] }
  target := fun _ => m.targetLatency

/-- **The ideal constant world of a noiseless draw is the world built from
it.** -/
theorem idealWorld_builds (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (d : Draw H)
    (hsplit : ∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1) (hlog : ∀ h, d.logRate h = 0)
    (hwander : ∀ h t, d.wander h t = 0) (htraffic : ∀ i j t, d.traffic i j t = 0) :
    m.Builds f d (idealWorld m f hex d.offset (fun i j => d.split i j * f.roundTrip i j)
      (fun i j => mul_pos (hsplit i j).1 (f.roundTrip_pos i j))) where
  rate_eq := rfl
  sender_eq := rfl
  host_eq := rfl
  clock := fun h t => by
    rw [Draw.reading_of_noiseless (hlog h) (hwander h) t]
    simp only [idealWorld]
    ring
  network := fun i j s q =>
    ⟨0, Draw.isBacklog_zero_of_const (fun s t => by rw [htraffic, htraffic]) s, by
      simp [idealWorld]⟩
  capture := fun n => by
    simp only [idealWorld]
    ring
  capture_first := fun _ => rfl
  capture_handed := fun _ => rfl
  capture_reported := fun b => by
    simp only [idealWorld]
    ring
  speaker_out := fun r k => by
    simp only [idealWorld]
    ring
  speaker_first := fun _ _ => rfl
  speaker_asked := fun r b => by
    simp only [idealWorld]
    ring
  speaker_reported := fun r b => by
    simp only [idealWorld]
    ring
  target_eq := fun _ => rfl

section World

variable [DecidableEq H]

/-- The world of an outcome: the ideal constant world of its draw. -/
def canonicalWorld (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : Component H → ℝ) : World H R :=
  idealWorld m f hex (canonicalDraw y).offset
    (fun i j => (canonicalDraw y).split i j * f.roundTrip i j)
    (fun i j => mul_pos (canonicalDraw_split_mem y i j).1 (f.roundTrip_pos i j))

theorem canonicalWorld_builds (m : GenerativeWorld H R) (f : Member H R)
    (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) (y : Component H → ℝ) :
    m.Builds f (canonicalDraw y) (canonicalWorld m f hex y) :=
  idealWorld_builds m f hex (canonicalDraw y) (canonicalDraw_split_mem y) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- **Every noiseless member has a random world.** For any hosts and
speakers, a noiseless member of the generative model has a random world: the
outcomes are the coordinates of the components, drawn independently, and the
world of an outcome is the ideal constant world of its draw. -/
theorem exists_holds_of_noiseless [Fintype H] (m : GenerativeWorld H R) (f : Member H R)
    (hf : f.Noiseless) (hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (world : Ω → World H R),
      m.Holds f P world :=
  ⟨Component H → ℝ, inferInstance, Measure.pi (canonicalLaw m f), canonicalWorld m f hex,
    canonicalDraw, canonicalDraw_prior m f hf, canonicalWorld_builds m f hex⟩

end World

end GenerativeWorld

end Unisono.Spec
