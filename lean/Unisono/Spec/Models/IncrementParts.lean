/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.IncrementLaw
public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The increments of a path within a period and outside it

The paused time of a link, as a function of true time, is a path with
independent increments. This file splits a path at a period from `a` to `b`
into two paths whose sum is the path:

* `pathWithin a b x` has the increments of `x` within the period and no
  others: it is zero up to `a`, follows the changes of `x` from `a` to `b`,
  and is constant from `b` on.
* `pathOutside a b x` has the increments of `x` outside the period: it
  follows `x` up to `a`, is constant from `a` to `b`, and follows the changes
  of `x` from `b` on.

The results:

* `indepFun_pathWithin_pathOutside`: for a process with
  independent increments that is zero at time zero, and a period that begins
  at or after time zero, the two paths are independent.
* `indepFun_comp_prodMk`: if a random variable `V` is independent of `U`,
  and two functions of `V` are independent of each other, then the first
  function of `V` is independent of the pair of `U` and the second function
  of `V`.

Together they say that what a link pauses within a period is independent of
everything else that is drawn, including what the same link pauses outside
the period.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## The two paths -/

/-- The time `t` moved into the period from `a` to `b`: `a` for a time
before the period, `b` for a time after it, and `t` itself for a time of the
period. -/
def clampTime (a b t : ℝ) : ℝ := min (max t a) b

theorem clampTime_of_le {a b t : ℝ} (hab : a ≤ b) (ht : t ≤ a) : clampTime a b t = a := by
  unfold clampTime
  rw [max_eq_right ht, min_eq_left hab]

theorem clampTime_of_ge {a b t : ℝ} (hab : a ≤ b) (ht : b ≤ t) : clampTime a b t = b := by
  unfold clampTime
  rw [max_eq_left (hab.trans ht), min_eq_right ht]

theorem clampTime_of_mem {a b t : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) : clampTime a b t = t := by
  unfold clampTime
  rw [max_eq_left h1, min_eq_left h2]

theorem clampTime_monotone (a b : ℝ) : Monotone (clampTime a b) := fun _ _ hst =>
  min_le_min_right b (max_le_max_right a hst)

theorem le_clampTime {a b : ℝ} (hab : a ≤ b) (t : ℝ) : a ≤ clampTime a b t :=
  le_min (le_max_right t a) hab

theorem clampTime_le (a b t : ℝ) : clampTime a b t ≤ b := min_le_right _ _

theorem continuous_clampTime (a b : ℝ) : Continuous (clampTime a b) :=
  (continuous_id.max continuous_const).min continuous_const

/-- The path that has the increments of the path `x` within the period from
`a` to `b`, and no others. -/
def pathWithin (a b : ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ := x (clampTime a b t) - x a

/-- The path that has the increments of the path `x` outside the period from
`a` to `b`: the path `x` minus its increments within the period. -/
def pathOutside (a b : ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ := x t - pathWithin a b x t

/-- **The two paths add up to the path.** -/
theorem pathOutside_add_pathWithin (a b : ℝ) (x : ℝ → ℝ) (t : ℝ) :
    pathOutside a b x t + pathWithin a b x t = x t := by
  unfold pathOutside
  ring

theorem pathWithin_of_le {a b t : ℝ} (hab : a ≤ b) (x : ℝ → ℝ) (ht : t ≤ a) :
    pathWithin a b x t = 0 := by
  unfold pathWithin
  rw [clampTime_of_le hab ht, sub_self]

theorem pathWithin_of_ge {a b t : ℝ} (hab : a ≤ b) (x : ℝ → ℝ) (ht : b ≤ t) :
    pathWithin a b x t = x b - x a := by
  unfold pathWithin
  rw [clampTime_of_ge hab ht]

theorem pathWithin_of_mem {a b t : ℝ} (x : ℝ → ℝ) (h1 : a ≤ t) (h2 : t ≤ b) :
    pathWithin a b x t = x t - x a := by
  unfold pathWithin
  rw [clampTime_of_mem h1 h2]

/-- Up to the beginning of the period, the path of the increments outside
the period is the path itself. -/
theorem pathOutside_of_le {a b t : ℝ} (hab : a ≤ b) (x : ℝ → ℝ) (ht : t ≤ a) :
    pathOutside a b x t = x t := by
  unfold pathOutside
  rw [pathWithin_of_le hab x ht, sub_zero]

/-- The path of the increments outside the period, from the values of the
path before the period and after it. -/
theorem pathOutside_eq {a b : ℝ} (hab : a ≤ b) (x : ℝ → ℝ) (t : ℝ) :
    pathOutside a b x t = x (min t a) + x (max t b) - x b := by
  unfold pathOutside
  rcases le_total t a with ht | ht
  · rw [pathWithin_of_le hab x ht, min_eq_left ht, max_eq_right (ht.trans hab)]
    ring
  · rcases le_total t b with htb | htb
    · rw [pathWithin_of_mem x ht htb, min_eq_right ht, max_eq_right htb]
      ring
    · rw [pathWithin_of_ge hab x htb, min_eq_right ht, max_eq_left htb]
      ring

theorem pathWithin_monotone (a b : ℝ) {x : ℝ → ℝ} (hx : Monotone x) :
    Monotone (pathWithin a b x) := fun _ _ hst =>
  sub_le_sub_right (hx (clampTime_monotone a b hst)) _

theorem pathOutside_monotone {a b : ℝ} (hab : a ≤ b) {x : ℝ → ℝ} (hx : Monotone x) :
    Monotone (pathOutside a b x) := by
  intro s t hst
  rw [pathOutside_eq hab, pathOutside_eq hab]
  have h1 := hx (min_le_min_right a hst)
  have h2 := hx (max_le_max_right b hst)
  linarith

theorem pathWithin_nonneg {a b : ℝ} (hab : a ≤ b) {x : ℝ → ℝ} (hx : Monotone x) (t : ℝ) :
    0 ≤ pathWithin a b x t :=
  sub_nonneg.mpr (hx (le_clampTime hab t))

/-- The increments within the period add up to at most the change of the
path over the period. -/
theorem pathWithin_le (a b : ℝ) {x : ℝ → ℝ} (hx : Monotone x) (t : ℝ) :
    pathWithin a b x t ≤ x b - x a :=
  sub_le_sub_right (hx (clampTime_le a b t)) _

/-- A path that does not change over the period has no increments within
it. -/
theorem pathWithin_eq_zero {a b : ℝ} (hab : a ≤ b) {x : ℝ → ℝ} (hx : Monotone x)
    (h : x b = x a) (t : ℝ) : pathWithin a b x t = 0 := by
  have h1 := pathWithin_nonneg hab hx t
  have h2 := pathWithin_le a b hx t
  rw [h, sub_self] at h2
  exact le_antisymm h2 h1

/-- Over any period, the increments outside the period from `a` to `b` add
up to at most the change of the path. -/
theorem pathOutside_sub_le (a b : ℝ) {x : ℝ → ℝ} (hx : Monotone x) {s t : ℝ} (hst : s ≤ t) :
    pathOutside a b x t - pathOutside a b x s ≤ x t - x s := by
  unfold pathOutside
  have := pathWithin_monotone a b hx hst
  linarith

theorem pathWithin_rightContinuous (a b : ℝ) {x : ℝ → ℝ}
    (hx : ∀ t, ContinuousWithinAt x (Set.Ici t) t) (t : ℝ) :
    ContinuousWithinAt (pathWithin a b x) (Set.Ici t) t := by
  have hmaps : Set.MapsTo (clampTime a b) (Set.Ici t) (Set.Ici (clampTime a b t)) :=
    fun _ hs => clampTime_monotone a b hs
  have h1 : ContinuousWithinAt (fun s => x (clampTime a b s)) (Set.Ici t) t :=
    (hx (clampTime a b t)).comp (continuous_clampTime a b).continuousWithinAt hmaps
  exact h1.sub continuousWithinAt_const

theorem pathOutside_rightContinuous (a b : ℝ) {x : ℝ → ℝ}
    (hx : ∀ t, ContinuousWithinAt x (Set.Ici t) t) (t : ℝ) :
    ContinuousWithinAt (pathOutside a b x) (Set.Ici t) t :=
  (hx t).sub (pathWithin_rightContinuous a b hx t)

theorem measurable_pathWithin (a b : ℝ) : Measurable (pathWithin a b) :=
  measurable_pi_iff.mpr fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _)

theorem measurable_pathOutside (a b : ℝ) : Measurable (pathOutside a b) :=
  measurable_pi_iff.mpr fun t =>
    (measurable_pi_apply t).sub ((measurable_pi_apply _).sub (measurable_pi_apply _))

/-! ## The two paths of a process with independent increments -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

open Classical in
/-- Among the sorted times, an earlier time has an earlier place. -/
theorem timeIndex_le {K : Finset ℝ} {u v : ℝ} (hu : u ∈ insert 0 K) (hv : v ∈ insert 0 K)
    (huv : u ≤ v) : timeIndex K u ≤ timeIndex K v := by
  by_contra hcon
  have hlt : timeIndex K v < timeIndex K u := not_le.mp hcon
  have h1 := sortedTimes_monotone K hlt.le
  rw [sortedTimes_timeIndex hu, sortedTimes_timeIndex hv] at h1
  have he : u = v := le_antisymm huv h1
  rw [he] at hlt
  exact lt_irrefl _ hlt

/-- Numbers given at the places of a finite set, extended by zero to every
place. -/
def extendZero (S : Finset ℕ) (v : S → ℝ) (l : ℕ) : ℝ := if h : l ∈ S then v ⟨l, h⟩ else 0

theorem measurable_extendZero (S : Finset ℕ) (l : ℕ) :
    Measurable fun v : S → ℝ => extendZero S v l := by
  unfold extendZero
  by_cases h : l ∈ S
  · simp only [dite_eq_left h]
    exact measurable_pi_apply _
  · simp only [dite_eq_right h]
    exact measurable_const

theorem extendZero_restrict {S : Finset ℕ} (Δ : ℕ → ℝ) {l : ℕ} (h : l ∈ S) :
    extendZero S (fun i : S => Δ i) l = Δ l := by
  unfold extendZero
  rw [dite_eq_left h]

open Classical in
/-- **At finitely many times, the two paths are independent.** For a process
with independent increments that is zero at time zero, and a period from `a`
to `b` that begins at or after time zero: the values of the path of the
increments within the period at the times of `I` are independent of the
values of the path of the increments outside the period at the times of
`J`. All the values are sums of increments between neighbours of one sorted
list of times, and no increment is used on both sides. -/
theorem indepFun_restrict_pathWithin_pathOutside {X : ℝ → Ω → ℝ}
    (hX : HasIndepIncrements X P) (hm : ∀ t, AEMeasurable (X t) P) (h0 : ∀ ω, X 0 ω = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (I J : Finset ℝ) :
    IndepFun (fun ω (t : I) => pathWithin a b (fun s => X s ω) t)
      (fun ω (t : J) => pathOutside a b (fun s => X s ω) t) P := by
  obtain ⟨K, hK⟩ : ∃ K : Finset ℝ, K = insert a (insert b (I.image (clampTime a b) ∪
      (J.image (fun t => min t a) ∪ J.image (fun t => max t b)))) := ⟨_, rfl⟩
  have mem0 : (0 : ℝ) ∈ insert 0 K := Finset.mem_insert_self 0 K
  have mema : a ∈ insert 0 K := by
    rw [hK]
    simp
  have memb : b ∈ insert 0 K := by
    rw [hK]
    simp
  have memI : ∀ t ∈ I, clampTime a b t ∈ insert 0 K := fun t ht => by
    rw [hK]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, rfl⟩)))
  have memJ1 : ∀ t ∈ J, min t a ∈ insert 0 K := fun t ht => by
    rw [hK]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, rfl⟩))))
  have memJ2 : ∀ t ∈ J, max t b ∈ insert 0 K := fun t ht => by
    rw [hK]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, ht, rfl⟩))))
  -- The increments between neighbours among the sorted times are independent.
  have hind : iIndepFun (fun (l : ℕ) ω =>
      X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω) P := hX.nat (sortedTimes_monotone K)
  have hΔm : ∀ l : ℕ, AEMeasurable (fun ω =>
      X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω) P := fun l => (hm _).sub (hm _)
  have hiab : timeIndex K a ≤ timeIndex K b := timeIndex_le mema memb hab
  have hdisj : Disjoint (Finset.Ico (timeIndex K a) (timeIndex K b))
      (Finset.range (timeIndex K a) ∪ Finset.Ico (timeIndex K b) (insert 0 K).card) := by
    refine Finset.disjoint_left.mpr fun l h1 h2 => ?_
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_range] at h1 h2
    omega
  have hST := hind.indepFun_finset₀ (Finset.Ico (timeIndex K a) (timeIndex K b))
    (Finset.range (timeIndex K a) ∪ Finset.Ico (timeIndex K b) (insert 0 K).card) hdisj hΔm
  -- The values of the two paths, from the increments of each side.
  have hφ : Measurable fun (v : Finset.Ico (timeIndex K a) (timeIndex K b) → ℝ) (t : I) =>
      ∑ l ∈ Finset.Ico (timeIndex K a) (timeIndex K (clampTime a b t)),
        extendZero (Finset.Ico (timeIndex K a) (timeIndex K b)) v l :=
    measurable_pi_iff.mpr fun t => Finset.measurable_sum _ fun l _ => measurable_extendZero _ l
  have hψ : Measurable fun (v : (Finset.range (timeIndex K a)
        ∪ Finset.Ico (timeIndex K b) (insert 0 K).card : Finset ℕ) → ℝ) (t : J) =>
      (∑ l ∈ Finset.Ico (timeIndex K 0) (timeIndex K (min t a)), extendZero _ v l)
        - (∑ l ∈ Finset.Ico (timeIndex K (min t a)) (timeIndex K 0), extendZero _ v l)
        + ∑ l ∈ Finset.Ico (timeIndex K b) (timeIndex K (max t b)), extendZero _ v l :=
    measurable_pi_iff.mpr fun t =>
      ((Finset.measurable_sum _ fun l _ => measurable_extendZero _ l).sub
        (Finset.measurable_sum _ fun l _ => measurable_extendZero _ l)).add
        (Finset.measurable_sum _ fun l _ => measurable_extendZero _ l)
  have hcomp := hST.comp hφ hψ
  have e1 : (fun ω (t : I) => pathWithin a b (fun s => X s ω) t)
      = (fun (v : Finset.Ico (timeIndex K a) (timeIndex K b) → ℝ) (t : I) =>
          ∑ l ∈ Finset.Ico (timeIndex K a) (timeIndex K (clampTime a b t)),
            extendZero (Finset.Ico (timeIndex K a) (timeIndex K b)) v l)
        ∘ fun ω (l : Finset.Ico (timeIndex K a) (timeIndex K b)) =>
            X (sortedTimes K ((l : ℕ) + 1)) ω - X (sortedTimes K l) ω := by
    funext ω t
    have hc := memI t t.2
    have hle : timeIndex K a ≤ timeIndex K (clampTime a b t) :=
      timeIndex_le mema hc (le_clampTime hab t)
    have hle' : timeIndex K (clampTime a b t) ≤ timeIndex K b :=
      timeIndex_le hc memb (clampTime_le a b t)
    have hsum : ∑ l ∈ Finset.Ico (timeIndex K a) (timeIndex K (clampTime a b t)),
          extendZero (Finset.Ico (timeIndex K a) (timeIndex K b))
            (fun l : Finset.Ico (timeIndex K a) (timeIndex K b) =>
              X (sortedTimes K ((l : ℕ) + 1)) ω - X (sortedTimes K l) ω) l
        = ∑ l ∈ Finset.Ico (timeIndex K a) (timeIndex K (clampTime a b t)),
            (X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω) :=
      Finset.sum_congr rfl fun l hl =>
        extendZero_restrict (fun l => X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω)
          (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hl).1,
            lt_of_lt_of_le (Finset.mem_Ico.mp hl).2 hle'⟩)
    simp only [Function.comp_apply]
    rw [hsum, Finset.sum_Ico_sub (fun l => X (sortedTimes K l) ω) hle,
      sortedTimes_timeIndex hc, sortedTimes_timeIndex mema]
    rfl
  have e2 : (fun ω (t : J) => pathOutside a b (fun s => X s ω) t)
      = (fun (v : (Finset.range (timeIndex K a)
            ∪ Finset.Ico (timeIndex K b) (insert 0 K).card : Finset ℕ) → ℝ) (t : J) =>
          (∑ l ∈ Finset.Ico (timeIndex K 0) (timeIndex K (min t a)), extendZero _ v l)
            - (∑ l ∈ Finset.Ico (timeIndex K (min t a)) (timeIndex K 0), extendZero _ v l)
            + ∑ l ∈ Finset.Ico (timeIndex K b) (timeIndex K (max t b)), extendZero _ v l)
        ∘ fun ω (l : (Finset.range (timeIndex K a)
              ∪ Finset.Ico (timeIndex K b) (insert 0 K).card : Finset ℕ)) =>
            X (sortedTimes K ((l : ℕ) + 1)) ω - X (sortedTimes K l) ω := by
    funext ω t
    have hu := memJ1 t t.2
    have hv := memJ2 t t.2
    have hua : timeIndex K (min (t : ℝ) a) ≤ timeIndex K a :=
      timeIndex_le hu mema (min_le_right _ _)
    have h0a : timeIndex K 0 ≤ timeIndex K a := timeIndex_le mem0 mema ha
    have hbv : timeIndex K b ≤ timeIndex K (max (t : ℝ) b) :=
      timeIndex_le memb hv (le_max_right _ _)
    have hvN : timeIndex K (max (t : ℝ) b) < (insert 0 K).card := timeIndex_lt hv
    have hrestr : ∀ l : ℕ, l ∈ Finset.range (timeIndex K a)
          ∪ Finset.Ico (timeIndex K b) (insert 0 K).card →
        extendZero (Finset.range (timeIndex K a) ∪ Finset.Ico (timeIndex K b) (insert 0 K).card)
            (fun l : (Finset.range (timeIndex K a)
                ∪ Finset.Ico (timeIndex K b) (insert 0 K).card : Finset ℕ) =>
              X (sortedTimes K ((l : ℕ) + 1)) ω - X (sortedTimes K l) ω) l
          = X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω := fun l hl =>
      extendZero_restrict (fun l => X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω) hl
    have hs1 : ∑ l ∈ Finset.Ico (timeIndex K 0) (timeIndex K (min (t : ℝ) a)),
          extendZero (Finset.range (timeIndex K a)
              ∪ Finset.Ico (timeIndex K b) (insert 0 K).card)
            (fun l : (Finset.range (timeIndex K a)
                ∪ Finset.Ico (timeIndex K b) (insert 0 K).card : Finset ℕ) =>
              X (sortedTimes K ((l : ℕ) + 1)) ω - X (sortedTimes K l) ω) l
        = ∑ l ∈ Finset.Ico (timeIndex K 0) (timeIndex K (min (t : ℝ) a)),
            (X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω) :=
      Finset.sum_congr rfl fun l hl => hrestr l (Finset.mem_union_left _
        (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hl).2 hua)))
    have hs2 : ∑ l ∈ Finset.Ico (timeIndex K (min (t : ℝ) a)) (timeIndex K 0),
          extendZero (Finset.range (timeIndex K a)
              ∪ Finset.Ico (timeIndex K b) (insert 0 K).card)
            (fun l : (Finset.range (timeIndex K a)
                ∪ Finset.Ico (timeIndex K b) (insert 0 K).card : Finset ℕ) =>
              X (sortedTimes K ((l : ℕ) + 1)) ω - X (sortedTimes K l) ω) l
        = ∑ l ∈ Finset.Ico (timeIndex K (min (t : ℝ) a)) (timeIndex K 0),
            (X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω) :=
      Finset.sum_congr rfl fun l hl => hrestr l (Finset.mem_union_left _
        (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hl).2 h0a)))
    have hs3 : ∑ l ∈ Finset.Ico (timeIndex K b) (timeIndex K (max (t : ℝ) b)),
          extendZero (Finset.range (timeIndex K a)
              ∪ Finset.Ico (timeIndex K b) (insert 0 K).card)
            (fun l : (Finset.range (timeIndex K a)
                ∪ Finset.Ico (timeIndex K b) (insert 0 K).card : Finset ℕ) =>
              X (sortedTimes K ((l : ℕ) + 1)) ω - X (sortedTimes K l) ω) l
        = ∑ l ∈ Finset.Ico (timeIndex K b) (timeIndex K (max (t : ℝ) b)),
            (X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω) :=
      Finset.sum_congr rfl fun l hl => hrestr l (Finset.mem_union_right _
        (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hl).1,
          lt_trans (Finset.mem_Ico.mp hl).2 hvN⟩))
    have hdiff : (∑ l ∈ Finset.Ico (timeIndex K 0) (timeIndex K (min (t : ℝ) a)),
          (X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω))
        - ∑ l ∈ Finset.Ico (timeIndex K (min (t : ℝ) a)) (timeIndex K 0),
          (X (sortedTimes K (l + 1)) ω - X (sortedTimes K l) ω)
        = X (min (t : ℝ) a) ω := by
      rcases le_total (timeIndex K 0) (timeIndex K (min (t : ℝ) a)) with hle | hle
      · rw [Finset.sum_Ico_sub (fun l => X (sortedTimes K l) ω) hle,
          Finset.Ico_eq_empty_of_le hle, Finset.sum_empty, sortedTimes_timeIndex hu,
          sortedTimes_timeIndex mem0, h0 ω]
        ring
      · rw [Finset.sum_Ico_sub (fun l => X (sortedTimes K l) ω) hle,
          Finset.Ico_eq_empty_of_le hle, Finset.sum_empty, sortedTimes_timeIndex hu,
          sortedTimes_timeIndex mem0, h0 ω]
        ring
    simp only [Function.comp_apply]
    rw [hs1, hs2, hs3, hdiff, Finset.sum_Ico_sub (fun l => X (sortedTimes K l) ω) hbv,
      sortedTimes_timeIndex hv, sortedTimes_timeIndex memb, pathOutside_eq hab]
    ring
  rw [e1, e2]
  exact hcomp

/-- **The increments of a process within a period are independent of its
increments outside the period.** For a process with independent increments
that is zero at time zero, and a period from `a` to `b` that begins at or
after time zero: the path of the increments within the period and the path
of the increments outside it are independent. -/
theorem indepFun_pathWithin_pathOutside [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ}
    (hX : HasIndepIncrements X P) (hm : ∀ t, AEMeasurable (X t) P) (h0 : ∀ ω, X 0 ω = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IndepFun (fun ω => pathWithin a b (fun s => X s ω))
      (fun ω => pathOutside a b (fun s => X s ω)) P :=
  IndepFun.process_indepFun_process₀
    (X := fun t ω => pathWithin a b (fun s => X s ω) t)
    (Y := fun t ω => pathOutside a b (fun s => X s ω) t)
    (fun t => show AEMeasurable (fun ω => X (clampTime a b t) ω - X a ω) P from
      (hm _).sub (hm a))
    (fun t => show AEMeasurable (fun ω => X t ω - (X (clampTime a b t) ω - X a ω)) P from
      (hm t).sub ((hm _).sub (hm a)))
    fun I J => indepFun_restrict_pathWithin_pathOutside hX hm h0 ha hab I J

/-! ## Two independent functions of one of two independent variables -/

/-- For two probability laws `μ` and `ν`: if two functions `φ` and `ψ` are
independent under `ν`, then under the product of `μ` and `ν` the value of
`φ` is independent of the pair of the first coordinate and the value of
`ψ`. The statement is about the laws. -/
theorem map_prod_comp_eq_prod {𝒰 𝒱 ℳ 𝒪 : Type*} [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [MeasurableSpace ℳ] [MeasurableSpace 𝒪] (μ : Measure 𝒰) (ν : Measure 𝒱)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ : 𝒱 → ℳ} {ψ : 𝒱 → 𝒪}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (h : ν.map (fun v => (φ v, ψ v)) = (ν.map φ).prod (ν.map ψ)) :
    (μ.prod ν).map (fun p : 𝒰 × 𝒱 => (φ p.2, (p.1, ψ p.2)))
      = (ν.map φ).prod (μ.prod (ν.map ψ)) := by
  have hΘ : Measurable fun p : 𝒰 × 𝒱 => (φ p.2, (p.1, ψ p.2)) :=
    (hφ.comp measurable_snd).prodMk (measurable_fst.prodMk (hψ.comp measurable_snd))
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [Measure.map_apply hΘ (hs.prod ht), Measure.prod_apply (hΘ (hs.prod ht)),
    Measure.prod_apply ht, ← lintegral_const_mul _ (measurable_measure_prodMk_left ht)]
  refine lintegral_congr fun u => ?_
  have hset : Prod.mk u ⁻¹' ((fun p : 𝒰 × 𝒱 => (φ p.2, (p.1, ψ p.2))) ⁻¹' s ×ˢ t)
      = (fun v => (φ v, ψ v)) ⁻¹' s ×ˢ (Prod.mk u ⁻¹' t) := by
    ext v
    simp only [Set.mem_preimage, Set.mem_prod]
  rw [hset, ← Measure.map_apply (hφ.prodMk hψ) (hs.prod (measurable_prodMk_left ht)), h,
    Measure.prod_prod]

/-- **A function of one variable is independent of the other variable
together with an independent function of the first.** If the random
variables `U` and `V` are independent, and the functions `φ` and `ψ` of `V`
are independent of each other, then `φ` of `V` is independent of the pair of
`U` and `ψ` of `V`. -/
theorem indepFun_comp_prodMk {𝒰 𝒱 ℳ 𝒪 : Type*} [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [MeasurableSpace ℳ] [MeasurableSpace 𝒪] [IsProbabilityMeasure P] {U : Ω → 𝒰} {V : Ω → 𝒱}
    {φ : 𝒱 → ℳ} {ψ : 𝒱 → 𝒪} (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hφ : Measurable φ) (hψ : Measurable ψ) (hUV : IndepFun U V P)
    (hφψ : IndepFun (fun ω => φ (V ω)) (fun ω => ψ (V ω)) P) :
    IndepFun (fun ω => φ (V ω)) (fun ω => (U ω, ψ (V ω))) P := by
  have hφV : AEMeasurable (fun ω => φ (V ω)) P := hφ.comp_aemeasurable hV
  have hψV : AEMeasurable (fun ω => ψ (V ω)) P := hψ.comp_aemeasurable hV
  have hUψ : AEMeasurable (fun ω => (U ω, ψ (V ω))) P := hU.prodMk hψV
  have : IsProbabilityMeasure (P.map U) := (Measure.isProbabilityMeasure_map_iff hU).mpr inferInstance
  have : IsProbabilityMeasure (P.map V) := (Measure.isProbabilityMeasure_map_iff hV).mpr inferInstance
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hU hV).mp hUV
  have h2 := (indepFun_iff_map_prod_eq_prod_map_map hφV hψV).mp hφψ
  have eφ : P.map (fun ω => φ (V ω)) = (P.map V).map φ :=
    (AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable hV).symm
  have eψ : P.map (fun ω => ψ (V ω)) = (P.map V).map ψ :=
    (AEMeasurable.map_map_of_aemeasurable hψ.aemeasurable hV).symm
  have eφψ : P.map (fun ω => (φ (V ω), ψ (V ω))) = (P.map V).map (fun v => (φ v, ψ v)) :=
    (AEMeasurable.map_map_of_aemeasurable (hφ.prodMk hψ).aemeasurable hV).symm
  have eUψ : P.map (fun ω => (U ω, ψ (V ω))) = (P.map U).prod ((P.map V).map ψ) := by
    have hpm : Measurable (Prod.map (id : 𝒰 → 𝒰) ψ) := measurable_id.prodMap hψ
    have e : (fun ω => (U ω, ψ (V ω))) = Prod.map id ψ ∘ fun ω => (U ω, V ω) := rfl
    rw [e, ← AEMeasurable.map_map_of_aemeasurable hpm.aemeasurable (hU.prodMk hV), h1,
      ← Measure.map_prod_map (P.map U) (P.map V) measurable_id hψ, Measure.map_id]
  have hΘ : Measurable fun p : 𝒰 × 𝒱 => (φ p.2, (p.1, ψ p.2)) :=
    (hφ.comp measurable_snd).prodMk (measurable_fst.prodMk (hψ.comp measurable_snd))
  have eL : P.map (fun ω => (φ (V ω), (U ω, ψ (V ω))))
      = ((P.map U).prod (P.map V)).map (fun p : 𝒰 × 𝒱 => (φ p.2, (p.1, ψ p.2))) := by
    rw [← h1, AEMeasurable.map_map_of_aemeasurable hΘ.aemeasurable (hU.prodMk hV)]
    rfl
  rw [eφ, eψ, eφψ] at h2
  refine (indepFun_iff_map_prod_eq_prod_map_map hφV hUψ).mpr ?_
  rw [eL, eφ, eUψ]
  exact map_prod_comp_eq_prod (P.map U) (P.map V) hφ hψ h2

end Unisono.Spec
