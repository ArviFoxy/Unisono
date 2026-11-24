/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeIdle
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The delay of a message as a measurable function of the paused times

The true time at which a message arrives is defined from backlogs, and a
backlog is a least upper bound over all earlier true times, taken at a true
time that itself depends on another backlog. Written that way it is not
visibly a measurable function of the paused times. This file gives a form
that is, and that agrees with the definition for paused times that never
decrease and are continuous from the right.

* `valueAfter`: the value of a function of time just after a time, as the
  upper limit of its values at rational times that decrease to the time. It
  is measurable in the function and the time together
  (`measurable_valueAfter`), and it is the value of the function where the
  function is continuous from the right (`valueAfter_eq`).
* `backlogM`: the backlog from `valueAfter` and the earlier times at rational
  distances. It is measurable (`measurable_backlogM`) and it is the backlog
  (`backlogM_eq`).
* `arrivalM`: when a message arrives, from `backlogM`. It is measurable in
  the paused times, the least delay and the true time of sending together
  (`measurable_arrivalM`), and in a world built from a draw it is when the
  message arrives (`Builds.arrival_eq_arrivalM`).

For independent cells that last `ℓ` seconds:

* `arrivalM_cellPaused_shiftCells`: moving the cells by `n` cells moves the
  arrivals by `n * ℓ` seconds.
* `ae_tendsto_lateFrequency`: among the messages sent at the true times
  `h₀`, `h₀ + ℓ`, `h₀ + 2 ℓ`, ..., the fraction that take longer than a given
  time converges, in almost every outcome, to the probability that the first
  one does. This is the ergodic theorem for moving the cells by one cell.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-! ## The value of a function of time just after a time -/

/-- A rational time after `t`, at most `1 / (n + 1)` later. -/
def ratAfter (n : ℕ) (t : ℝ) : ℚ := ((⌊t * ((n : ℝ) + 1)⌋ : ℚ) + 1) / ((n : ℚ) + 1)

theorem measurable_ratAfter (n : ℕ) : Measurable (ratAfter n) :=
  (Measurable.of_discrete (f := fun k : ℤ => ((k : ℚ) + 1) / ((n : ℚ) + 1))).comp
    (Int.measurable_floor.comp (measurable_id.mul_const _))

theorem lt_ratAfter (n : ℕ) (t : ℝ) : t < (ratAfter n t : ℝ) := by
  unfold ratAfter
  push_cast
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [lt_div_iff₀ hn]
  exact Int.lt_floor_add_one _

theorem ratAfter_le (n : ℕ) (t : ℝ) : (ratAfter n t : ℝ) ≤ t + 1 / ((n : ℝ) + 1) := by
  unfold ratAfter
  push_cast
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hn, add_mul, one_div, inv_mul_cancel₀ hn.ne']
  linarith [Int.floor_le (t * ((n : ℝ) + 1))]

theorem tendsto_ratAfter (t : ℝ) :
    Tendsto (fun n : ℕ => (ratAfter n t : ℝ)) atTop (𝓝[Set.Ici t] t) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => (lt_ratAfter n t).le⟩
  have hlim : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (lt_ratAfter n t).le) (fun n => ratAfter_le n t)

/-- The value of a function of time just after the time `t`: the upper limit
of its values at rational times that decrease to `t`. -/
def valueAfter (X : Time → ℝ) (t : ℝ) : ℝ :=
  limsup (fun n : ℕ => X (ratAfter n t)) atTop

/-- Where a function of time is continuous from the right, its value just
after a time is its value at the time. -/
theorem valueAfter_eq {X : Time → ℝ} {t : ℝ} (h : ContinuousWithinAt X (Set.Ici t) t) :
    valueAfter X t = X t :=
  (h.tendsto.comp (tendsto_ratAfter t)).limsup_eq

theorem measurable_valueAfter : Measurable fun p : (Time → ℝ) × ℝ => valueAfter p.1 p.2 := by
  refine Measurable.limsup fun n => ?_
  have h : Measurable fun p : (Time → ℝ) × ℚ => p.1 (p.2 : ℝ) :=
    measurable_from_prod_countable_left fun q => measurable_pi_apply (q : ℝ)
  exact h.comp (measurable_fst.prodMk ((measurable_ratAfter n).comp measurable_snd))

/-! ## The backlog -/

/-- The backlog at true time `t` of a link or a host whose paused time is
`X`, from the values of `X` just after `t` and just after the earlier times
at rational distances from `t`. -/
def backlogM (X : Time → ℝ) (t : ℝ) : ℝ :=
  ⨆ q : {q : ℚ // 0 ≤ q}, valueAfter X t - valueAfter X (t - (q : ℚ)) - (q : ℚ)

theorem measurable_backlogM : Measurable fun p : (Time → ℝ) × ℝ => backlogM p.1 p.2 :=
  Measurable.iSup fun _ => (measurable_valueAfter.sub (measurable_valueAfter.comp
    (measurable_fst.prodMk (measurable_snd.sub_const _)))).sub_const _

/-- For a paused time that is continuous from the right, the backlog from
its values at the earlier times at rational distances. -/
theorem backlogM_eq_iSup {X : Time → ℝ} (hright : ∀ t, ContinuousWithinAt X (Set.Ici t) t)
    (t : ℝ) : backlogM X t = ⨆ q : {q : ℚ // 0 ≤ q}, X t - X (t - (q : ℚ)) - (q : ℚ) := by
  unfold backlogM
  simp only [valueAfter_eq (hright _)]

/-- **`backlogM` is the backlog**, for a paused time that never decreases
and is continuous from the right. -/
theorem backlogM_eq {X : Time → ℝ} (hmono : Monotone X)
    (hright : ∀ t, ContinuousWithinAt X (Set.Ici t) t) {t v : ℝ} (h : IsBacklog X t v) :
    backlogM X t = v := by
  have : Nonempty {q : ℚ // 0 ≤ q} := ⟨⟨0, le_rfl⟩⟩
  rw [backlogM_eq_iSup hright]
  refine IsLUB.ciSup_eq ⟨?_, ?_⟩
  · rintro x ⟨q, rfl⟩
    have hq : (0 : ℝ) ≤ ((q : ℚ) : ℝ) := by exact_mod_cast q.2
    exact h.1 ⟨t - (q : ℚ), by linarith, by ring⟩
  · intro y hy
    refine h.2 ?_
    rintro x ⟨s, hs, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - s < t - s + ε by linarith)
    have hq0 : (0 : ℚ) ≤ q := by
      have : (0 : ℝ) ≤ (q : ℝ) := (sub_nonneg.mpr hs).trans hq1.le
      exact_mod_cast this
    have h1 : X t - X (t - (q : ℝ)) - (q : ℝ) ≤ y := hy ⟨⟨q, hq0⟩, rfl⟩
    have h2 := hmono (show t - (q : ℝ) ≤ s by linarith)
    linarith

/-- The backlog of a paused time moved in time, and changed by a constant,
is the backlog moved in time. -/
theorem backlogM_shift {X Y : Time → ℝ} {a c : ℝ}
    (hX : ∀ t, ContinuousWithinAt X (Set.Ici t) t)
    (hY : ∀ t, ContinuousWithinAt Y (Set.Ici t) t) (hXY : ∀ t, Y t = X (t + a) - c) (t : ℝ) :
    backlogM Y t = backlogM X (t + a) := by
  rw [backlogM_eq_iSup hY, backlogM_eq_iSup hX]
  congr 1
  funext q
  rw [hXY, hXY, show t - ((q : ℚ) : ℝ) + a = t + a - ((q : ℚ) : ℝ) by ring]
  ring

/-! ## The arrival of a message -/

/-- When host `j` observes a message that host `i` sends at true time `s`,
from the paused times `x` of the links and hosts and the least delay `δ` of
the direction: after the backlog of host `i`, the least delay and the backlog
of the link, and the backlog of host `j`, each taken with `backlogM`. -/
def arrivalM (x : PauseIndex H → Time → ℝ) (i j : H) (δ : ℝ) (s : Time) : Time :=
  s + backlogM (x (.inr i)) s + δ
    + backlogM (x (.inl (i, j))) (s + backlogM (x (.inr i)) s)
    + backlogM (x (.inr j))
        (s + backlogM (x (.inr i)) s + δ
          + backlogM (x (.inl (i, j))) (s + backlogM (x (.inr i)) s))

theorem measurable_backlogM_comp {α : Type*} [MeasurableSpace α] {X : α → Time → ℝ} {τ : α → ℝ}
    (hX : Measurable X) (hτ : Measurable τ) : Measurable fun a => backlogM (X a) (τ a) := by
  have hp : Measurable fun a => (X a, τ a) := hX.prodMk hτ
  exact Measurable.comp (g := fun p : (Time → ℝ) × ℝ => backlogM p.1 p.2)
    (f := fun a => (X a, τ a)) measurable_backlogM hp

theorem measurable_arrivalM (i j : H) :
    Measurable fun p : (PauseIndex H → Time → ℝ) × ℝ × ℝ => arrivalM p.1 i j p.2.1 p.2.2 := by
  have hx : ∀ y : PauseIndex H,
      Measurable fun p : (PauseIndex H → Time → ℝ) × ℝ × ℝ => p.1 y := fun y =>
    (measurable_pi_apply y).comp measurable_fst
  have hs : Measurable fun p : (PauseIndex H → Time → ℝ) × ℝ × ℝ => p.2.2 :=
    measurable_snd.comp measurable_snd
  have hδ : Measurable fun p : (PauseIndex H → Time → ℝ) × ℝ × ℝ => p.2.1 :=
    measurable_fst.comp measurable_snd
  have h1 : Measurable fun p : (PauseIndex H → Time → ℝ) × ℝ × ℝ =>
      backlogM (p.1 (.inr i)) p.2.2 := measurable_backlogM_comp (hx _) hs
  have h2 : Measurable fun p : (PauseIndex H → Time → ℝ) × ℝ × ℝ =>
      backlogM (p.1 (.inl (i, j))) (p.2.2 + backlogM (p.1 (.inr i)) p.2.2) :=
    measurable_backlogM_comp (hx _) (hs.add h1)
  have h3 : Measurable fun p : (PauseIndex H → Time → ℝ) × ℝ × ℝ =>
      backlogM (p.1 (.inr j)) (p.2.2 + backlogM (p.1 (.inr i)) p.2.2 + p.2.1
        + backlogM (p.1 (.inl (i, j))) (p.2.2 + backlogM (p.1 (.inr i)) p.2.2)) :=
    measurable_backlogM_comp (hx _) (((hs.add h1).add hδ).add h2)
  exact (((hs.add h1).add hδ).add h2).add h3

/-- **`arrivalM` is when a message arrives**, in a world built from a draw
whose paused times never decrease and are continuous from the right. -/
theorem Builds.arrival_eq_arrivalM {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
    {w : World H R} (hB : m.Builds f d w) (hmono : ∀ x, Monotone (d.paused x))
    (hright : ∀ x t, ContinuousWithinAt (d.paused x) (Set.Ici t) t) (i j : H) (s : Time) :
    d.arrival f i j s = arrivalM d.paused i j (d.split i j * f.roundTrip i j) s := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, he⟩ := hB.arrival_eq i j s
  have e₁ : backlogM (d.paused (.inr i)) s = v₁ :=
    backlogM_eq (hmono (.inr i)) (hright (.inr i)) hv₁
  have e₂ : backlogM (d.paused (.inl (i, j))) (s + v₁) = v₂ :=
    backlogM_eq (hmono (.inl (i, j))) (hright (.inl (i, j))) hv₂
  have e₃ : backlogM (d.paused (.inr j)) (s + v₁ + d.split i j * f.roundTrip i j + v₂) = v₃ :=
    backlogM_eq (hmono (.inr j)) (hright (.inr j)) hv₃
  rw [he]
  unfold arrivalM
  rw [e₁, e₂, e₃]

/-- The arrivals for paused times moved in time, and changed by constants,
are the arrivals moved in time. -/
theorem arrivalM_shift {x y : PauseIndex H → Time → ℝ} {a : ℝ} {c : PauseIndex H → ℝ}
    (hx : ∀ p t, ContinuousWithinAt (x p) (Set.Ici t) t)
    (hy : ∀ p t, ContinuousWithinAt (y p) (Set.Ici t) t)
    (hxy : ∀ p t, y p t = x p (t + a) - c p) (i j : H) (δ s : ℝ) :
    arrivalM y i j δ s = arrivalM x i j δ (s + a) - a := by
  have e₁ : backlogM (y (.inr i)) s = backlogM (x (.inr i)) (s + a) :=
    backlogM_shift (hx _) (hy _) (hxy _) s
  have e₂ : backlogM (y (.inl (i, j))) (s + backlogM (x (.inr i)) (s + a))
      = backlogM (x (.inl (i, j))) (s + a + backlogM (x (.inr i)) (s + a)) := by
    rw [backlogM_shift (hx _) (hy _) (hxy _)]
    congr 1
    ring
  have e₃ : backlogM (y (.inr j)) (s + backlogM (x (.inr i)) (s + a) + δ
        + backlogM (x (.inl (i, j))) (s + a + backlogM (x (.inr i)) (s + a)))
      = backlogM (x (.inr j)) (s + a + backlogM (x (.inr i)) (s + a) + δ
        + backlogM (x (.inl (i, j))) (s + a + backlogM (x (.inr i)) (s + a))) := by
    rw [backlogM_shift (hx _) (hy _) (hxy _)]
    congr 1
    ring
  unfold arrivalM
  rw [e₁, e₂, e₃]
  ring

/-! ## The paused times of independent cells -/

/-- The paused time for the cells moved by `n` cells is the paused time moved
by `n` seconds, counted from its value at `n` seconds. -/
theorem pausedPath_shiftCells (n : ℤ) (ω : Cells) (u : ℝ) :
    pausedPath (shiftCells n ω) u = pausedPath ω (u + n) - pausedPath ω n := by
  rcases le_total 0 u with hu | hu
  · have h1 := pausedPath_sub hu (shiftCells n ω)
    have h2 := pausedPath_sub (show (0 : ℝ) + n ≤ u + n by linarith) ω
    rw [pausedPath_zero] at h1
    rw [zero_add] at h2
    rw [pausedBetween_shiftCells, zero_add] at h1
    linarith
  · have h1 := pausedPath_sub hu (shiftCells n ω)
    have h2 := pausedPath_sub (show u + (n : ℝ) ≤ 0 + n by linarith) ω
    rw [pausedPath_zero] at h1
    rw [pausedBetween_shiftCells, zero_add] at h1
    rw [zero_add] at h2
    linarith

theorem cellPaused_monotone {ℓ : ℝ} (hℓ : 0 < ℓ) (ω : ℤ → PauseIndex H → Cell)
    (x : PauseIndex H) : Monotone (cellPaused ℓ ω x) := fun _ _ hab =>
  pausedPath_monotone _ (div_le_div_of_nonneg_right hab hℓ.le)

theorem cellPaused_rightContinuous {ℓ : ℝ} (hℓ : 0 < ℓ) (ω : ℤ → PauseIndex H → Cell)
    (x : PauseIndex H) (t : ℝ) : ContinuousWithinAt (cellPaused ℓ ω x) (Set.Ici t) t := by
  have h := pausedPath_rightContinuous (fun c => ω c x) (t / ℓ)
  have hdiv : ContinuousWithinAt (fun u : ℝ => u / ℓ) (Set.Ici t) t :=
    (continuous_id.div_const ℓ).continuousWithinAt
  exact ContinuousWithinAt.comp (g := pausedPath fun c => ω c x) (f := fun u : ℝ => u / ℓ) h hdiv
    fun u hu => div_le_div_of_nonneg_right hu hℓ.le

/-- The paused times for the cells moved by `n` cells that last `ℓ` seconds
are the paused times moved by `n * ℓ` seconds, counted from their values
then. -/
theorem cellPaused_shiftCells {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℤ) (ω : ℤ → PauseIndex H → Cell)
    (x : PauseIndex H) (t : ℝ) :
    cellPaused ℓ (shiftCells n ω) x t
      = cellPaused ℓ ω x (t + n * ℓ) - cellPaused ℓ ω x (n * ℓ) := by
  unfold cellPaused
  have h := pausedPath_shiftCells n (fun c => ω c x) (t / ℓ)
  have e1 : (t + n * ℓ) / ℓ = t / ℓ + n := by field_simp
  have e2 : (n : ℝ) * ℓ / ℓ = n := by field_simp
  rw [e1, e2]
  exact h

/-- **Moving the cells moves the arrivals.** For cells that last `ℓ`
seconds, the arrival of a message sent at `s`, for the cells moved by `n`
cells, is the arrival of a message sent at `s + n * ℓ`, minus `n * ℓ`. -/
theorem arrivalM_cellPaused_shiftCells {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℤ)
    (ω : ℤ → PauseIndex H → Cell) (i j : H) (δ s : ℝ) :
    arrivalM (cellPaused ℓ (shiftCells n ω)) i j δ s
      = arrivalM (cellPaused ℓ ω) i j δ (s + n * ℓ) - n * ℓ :=
  arrivalM_shift (c := fun p => cellPaused ℓ ω p (n * ℓ))
    (fun p t => cellPaused_rightContinuous hℓ ω p t)
    (fun p t => cellPaused_rightContinuous hℓ (shiftCells n ω) p t)
    (fun p t => cellPaused_shiftCells hℓ n ω p t) i j δ s

/-! ## How often a message is late -/

section Frequency

variable [Fintype H]

/-- **The long-run fraction of late messages is a probability.** Consider
independent cells that last `ℓ` seconds, and messages from host `i` to host
`j` sent at the true times `h₀`, `h₀ + ℓ`, `h₀ + 2 ℓ` and so on, over a link
with least delay `δ`. In almost every outcome, the fraction of the first `n`
messages that take longer than `μ` seconds converges, as `n` grows, to the
probability that the first message takes longer than `μ` seconds. -/
theorem ae_tendsto_lateFrequency (f : Member H R) {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : H)
    (δ μ h₀ : ℝ) :
    ∀ᵐ ω ∂pauseCellsLaw f ℓ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (((Finset.range n).filter fun c : ℕ =>
          μ < arrivalM (cellPaused ℓ ω) i j δ (h₀ + c * ℓ) - (h₀ + c * ℓ)).card : ℝ)) atTop
        (𝓝 ((pauseCellsLaw f ℓ).real
          {ω | μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀})) := by
  classical
  have hmeas : MeasurableSet {ω : ℤ → PauseIndex H → Cell |
      μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀} := by
    have h : Measurable fun ω : ℤ → PauseIndex H → Cell =>
        arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀ :=
      ((measurable_arrivalM i j).comp ((measurable_cellPaused ℓ).prodMk
        (measurable_const (a := ((δ, h₀) : ℝ × ℝ))))).sub_const _
    exact measurableSet_lt measurable_const h
  have hT : Ergodic (shiftCells 1) (pauseCellsLaw f ℓ) := ergodic_shiftCells _ one_ne_zero
  have hg : Measurable ({ω : ℤ → PauseIndex H → Cell |
      μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀}.indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator hmeas
  have hbound : ∀ ω, |{ω : ℤ → PauseIndex H → Cell |
      μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀}.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
    intro ω
    by_cases h : ω ∈ {ω : ℤ → PauseIndex H → Cell |
        μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀}
    · rw [Set.indicator_of_mem h]
      norm_num
    · rw [Set.indicator_of_notMem h]
      norm_num
  have hint : ∫ ω, {ω : ℤ → PauseIndex H → Cell |
        μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀}.indicator (fun _ => (1 : ℝ)) ω
        ∂pauseCellsLaw f ℓ
      = (pauseCellsLaw f ℓ).real {ω | μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀} := by
    rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
  filter_upwards [tendsto_birkhoffAverage_ae hT hg hbound] with ω hω
  rw [hint] at hω
  refine hω.congr fun n => ?_
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hshift := arrivalM_cellPaused_shiftCells hℓ (c : ℤ) ω i j δ h₀
  rw [iterate_shiftCells, mul_one]
  have hiff : (shiftCells (c : ℤ) ω ∈ {ω : ℤ → PauseIndex H → Cell |
        μ < arrivalM (cellPaused ℓ ω) i j δ h₀ - h₀})
      ↔ μ < arrivalM (cellPaused ℓ ω) i j δ (h₀ + c * ℓ) - (h₀ + c * ℓ) := by
    show μ < arrivalM (cellPaused ℓ (shiftCells (c : ℤ) ω)) i j δ h₀ - h₀ ↔ _
    rw [hshift]
    push_cast
    constructor <;> intro h <;> linarith
  by_cases h : μ < arrivalM (cellPaused ℓ ω) i j δ (h₀ + c * ℓ) - (h₀ + c * ℓ)
  · rw [Set.indicator_of_mem (hiff.mpr h), ite_eq_left h]
    simp
  · rw [Set.indicator_of_notMem (fun hmem => h (hiff.mp hmem)), ite_eq_right h]
    simp

end Frequency

end Unisono.Spec.GenerativeWorld
