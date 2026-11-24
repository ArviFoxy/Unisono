/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativePauseLaw

/-!
# All links and hosts are idle together, again and again

A link or a host is idle at a true time when it has no backlog: every pause
that began earlier is over. This file proves that, in every random world of
every member of the generative model, in almost every outcome, all links and
all hosts are idle together during periods of any length, again and again.

**Theorem** (`Prior.ae_idle`). In every random world of a member, in almost
every outcome: for every number of seconds `M` and every true time `N` there
is a later true time `a` such that no link and no host has a backlog at any
true time from `a` to `a + M`.

The proof is on the independent cells of
`Unisono.Spec.Models.GenerativePauseLaw`, with cells of one second.

* The outcomes in which, at true time zero, the pauses that began earlier
  leave every link and every host a backlog of at most `K` seconds have
  positive probability for some `K`, because the backlogs are finite in
  almost every outcome (`exists_boundedBefore_ne_zero`).
* The outcomes in which no pause begins in the `K + M + 1` seconds from true
  time zero have positive probability (`measure_emptyUpTo_ne_zero`).
* The two sets depend on different cells, so they are independent, and in an
  outcome of both every link and every host is idle from true time `K` to
  `K + M` (`idleOn_of_bounded_empty`).
* Moving the cells is ergodic, so almost every outcome, moved by some number
  of cells, lies in both sets, again and again
  (`ae_cellPaused_mem_idleOften`).

The property is stated with the values of the paused times at countably many
times (`idleOften`), so that it is a measurable set of paused times and
carries over to every random world of the member (`Prior.ae_paused_mem`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ}

/-! ## Idle periods of a paused time -/

/-- The link or the host whose paused time is `X` has no backlog at true time
`t`, as far as the earlier rational times show: the paused time that began
since each of them is at most the time since then. -/
def IdleAt (X : Time → ℝ) (t : Time) : Prop :=
  ∀ q : ℚ, (q : ℝ) ≤ t → X t - X q ≤ t - q

/-- The link or the host whose paused time is `X` has no backlog at true time
`a`, and no pause of it begins from then until `b`. -/
def IdleOn (X : Time → ℝ) (a b : Time) : Prop :=
  IdleAt X a ∧ X b = X a

/-- For a paused time that never decreases, no backlog as far as the rational
times show is no backlog at all. -/
theorem IdleAt.sub_le {X : Time → ℝ} (hmono : Monotone X) {t : Time} (h : IdleAt X t)
    {s : Time} (hs : s ≤ t) : X t - X s ≤ t - s := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s - ε < s by linarith)
  have h1 := h q (hq2.le.trans hs)
  have h2 := hmono hq2.le
  linarith

/-- **An idle link or host has no backlog.** If the paused time never
decreases, there is no backlog at `a`, and no pause begins until `b`, then
the backlog is zero at every true time from `a` to `b`. -/
theorem IdleOn.isBacklog {X : Time → ℝ} (hmono : Monotone X) {a b t : Time} (h : IdleOn X a b)
    (hat : a ≤ t) (htb : t ≤ b) : IsBacklog X t 0 := by
  have h1 : X t ≤ X b := hmono htb
  rw [h.2] at h1
  have hXt : X t = X a := le_antisymm h1 (hmono hat)
  refine ⟨?_, fun y hy => hy ⟨t, le_rfl, by ring⟩⟩
  rintro x ⟨s, hs, rfl⟩
  rcases le_total a s with has | hsa
  · have := hmono has
    linarith
  · have := h.1.sub_le hmono hsa
    linarith

/-- The families of paused times in which, for every number of seconds `M`
and every true time `N`, there is a later whole true time `a` from which all
members of the family are idle for `M` seconds. -/
def idleOften (J : Type) : Set (J → Time → ℝ) :=
  {x | ∀ M N : ℕ, ∃ a : ℕ, N ≤ a ∧ ∀ p, IdleOn (x p) a (a + M)}

theorem measurableSet_idleOften (J : Type) [Countable J] : MeasurableSet (idleOften J) := by
  have hev : ∀ (p : J) (t : ℝ), Measurable fun x : J → Time → ℝ => x p t := fun p t =>
    (measurable_pi_apply t).comp (measurable_pi_apply p)
  have hidle : ∀ (p : J) (a : ℝ), MeasurableSet {x : J → Time → ℝ | IdleAt (x p) a} := by
    intro p a
    have h : {x : J → Time → ℝ | IdleAt (x p) a}
        = ⋂ q : ℚ, ⋂ _ : (q : ℝ) ≤ a, {x | x p a - x p q ≤ a - q} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [h]
    exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
      measurableSet_le ((hev p a).sub (hev p q)) measurable_const
  have h : idleOften J = ⋂ M : ℕ, ⋂ N : ℕ, ⋃ a : ℕ, ⋃ _ : N ≤ a, ⋂ p : J,
      ({x | IdleAt (x p) a} ∩ {x | x p ((a : ℝ) + M) = x p a}) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx M N
      obtain ⟨a, ha, h⟩ := hx M N
      exact ⟨a, ha, fun p => h p⟩
    · intro hx M N
      obtain ⟨a, ha, h⟩ := hx M N
      exact ⟨a, ha, fun p => h p⟩
  rw [h]
  exact MeasurableSet.iInter fun M => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun a =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun p =>
      (hidle p a).inter (measurableSet_eq_fun (hev p _) (hev p _))

/-! ## Cells without pauses -/

/-- The outcome of the cells with every cell from cell `a` on made empty. -/
def clearFrom (a : ℤ) (ω : Cells) : Cells :=
  fun c => if a ≤ c then (0, fun _ => (0, 0)) else ω c

theorem measurable_clearFrom (a : ℤ) : Measurable (clearFrom a) :=
  measurable_pi_iff.mpr fun c => by
    by_cases h : a ≤ c
    · simp only [clearFrom, ite_eq_left h]
      exact measurable_const
    · simp only [clearFrom, ite_eq_right h]
      exact measurable_pi_apply c

theorem cellSum_of_empty (g : ℝ × ℝ → ℝ) {cell : Cell} (h : cell.1 = 0) : cellSum g cell = 0 := by
  unfold cellSum
  rw [h, Finset.range_zero, Finset.sum_empty]

/-- No paused time begins in a period whose cells are empty. -/
theorem pausedBetween_eq_zero_of_empty {s t : ℝ} {ω : Cells}
    (h : ∀ c ∈ Finset.Icc ⌊s⌋ ⌊t⌋, (ω c).1 = 0) : pausedBetween s t ω = 0 :=
  Finset.sum_eq_zero fun c hc => cellSum_of_empty _ (h c hc)

/-- Emptying cells does not add paused time. -/
theorem pausedBetween_clearFrom_le (a : ℤ) (s t : ℝ) (ω : Cells) :
    pausedBetween s t (clearFrom a ω) ≤ pausedBetween s t ω :=
  Finset.sum_le_sum fun c _ => by
    by_cases h : a ≤ c
    · rw [cellSum_of_empty _ (show (clearFrom a ω c).1 = 0 by simp only [clearFrom, ite_eq_left h])]
      exact cellSum_nonneg (markIn_nonneg c s t) _
    · rw [show clearFrom a ω c = ω c by simp only [clearFrom, ite_eq_right h]]

/-- Emptying the cells from cell `a` on does not change the paused time that
begins up to a true time in cell `a` or earlier, when cell `a` is empty. -/
theorem pausedBetween_clearFrom_eq {a : ℤ} {s t : ℝ} {ω : Cells} (ht : ⌊t⌋ ≤ a)
    (h : (ω a).1 = 0) : pausedBetween s t (clearFrom a ω) = pausedBetween s t ω :=
  Finset.sum_congr rfl fun c hc => by
    have hca : c ≤ a := (Finset.mem_Icc.mp hc).2.trans ht
    rcases lt_or_eq_of_le hca with hlt | rfl
    · rw [show clearFrom a ω c = ω c by simp only [clearFrom, ite_eq_right (not_le.mpr hlt)]]
    · rw [cellSum_of_empty _ (show (clearFrom c ω c).1 = 0 by
        simp only [clearFrom, ite_eq_left le_rfl]), cellSum_of_empty _ h]

/-- The paused time that begins in a period, for the cells moved by `k`
cells, is the paused time that begins in the period moved by `k` seconds. -/
theorem pausedBetween_shiftCells (k : ℤ) (s t : ℝ) (ω : Cells) :
    pausedBetween s t (shiftCells k ω) = pausedBetween (s + k) (t + k) ω := by
  unfold pausedBetween
  rw [Int.floor_add_intCast, Int.floor_add_intCast]
  refine Finset.sum_nbij' (fun c => c + k) (fun c => c - k) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_Icc] at hc ⊢
    omega
  · intro c hc
    rw [Finset.mem_Icc] at hc ⊢
    omega
  · intro c _
    omega
  · intro c _
    omega
  · intro c _
    have hmark : markIn (c + k) (s + k) (t + k) = markIn c s t := by
      funext z
      have hp : pauseStart (c + k) z.1 = pauseStart c z.1 + k := by
        unfold pauseStart
        push_cast
        ring
      unfold markIn
      rw [hp]
      have h1 : (s + (k : ℝ) < pauseStart c z.1 + k) ↔ (s < pauseStart c z.1) := by
        constructor <;> intro h <;> linarith
      have h2 : (pauseStart c z.1 + k ≤ t + k) ↔ (pauseStart c z.1 ≤ t) := by
        constructor <;> intro h <;> linarith
      simp only [h1, h2]
    rw [hmark]
    rfl

section Cells

variable [Fintype H]

/-- The outcomes of the cells in which the pauses that begin before true time
zero leave every link and every host a backlog of at most `K` seconds at true
time zero, as far as the earlier rational times show. -/
def boundedBefore (K : ℕ) : Set (ℤ → PauseIndex H → Cell) :=
  {ω | ∀ (p : PauseIndex H) (q : ℚ), (q : ℝ) ≤ 0 →
    pausedBetween q 0 (clearFrom 0 fun c => ω c p) ≤ -q + K}

/-- The outcomes of the cells in which no pause of any link or host begins in
the cells from `0` to `n`. -/
def emptyUpTo (n : ℕ) : Set (ℤ → PauseIndex H → Cell) :=
  Set.pi (↑(Finset.Icc (0 : ℤ) n)) fun _ => Set.pi Set.univ fun _ => {cell : Cell | cell.1 = 0}

omit [Fintype H] in
theorem mem_emptyUpTo {n : ℕ} {ω : ℤ → PauseIndex H → Cell} :
    ω ∈ emptyUpTo n ↔ ∀ (c : ℤ), 0 ≤ c → c ≤ n → ∀ p, (ω c p).1 = 0 := by
  constructor
  · intro h c h0 hn p
    exact h c (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨h0, hn⟩)) p (Set.mem_univ p)
  · intro h c hc p _
    have hc' := Finset.mem_Icc.mp (Finset.mem_coe.mp hc)
    exact h c hc'.1 hc'.2 p

theorem measurableSet_boundedBefore (K : ℕ) : MeasurableSet (boundedBefore (H := H) K) := by
  have h : boundedBefore (H := H) K = ⋂ p : PauseIndex H, ⋂ q : ℚ, ⋂ _ : (q : ℝ) ≤ 0,
      {ω | pausedBetween q 0 (clearFrom 0 fun c => ω c p) ≤ -q + K} := by
    ext ω
    simp only [Set.mem_iInter]
    rfl
  rw [h]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
    measurableSet_le ((measurable_pausedBetween q 0).comp ((measurable_clearFrom 0).comp
      (measurable_pi_iff.mpr fun c => (measurable_pi_apply p).comp (measurable_pi_apply c))))
      measurable_const

omit [Fintype H] in
theorem measurableSet_emptyUpTo [Countable H] (n : ℕ) : MeasurableSet (emptyUpTo (H := H) n) :=
  MeasurableSet.pi (Finset.countable_toSet _) fun _ _ =>
    MeasurableSet.pi Set.countable_univ fun _ _ => measurable_fst (measurableSet_singleton 0)

/-- **No pause begins in the first cells with positive probability.** -/
theorem measure_emptyUpTo_ne_zero (f : Member H R) (ℓ : ℝ) (n : ℕ) :
    pauseCellsLaw f ℓ (emptyUpTo n) ≠ 0 := by
  have hE : MeasurableSet (Set.pi Set.univ fun _ : PauseIndex H => {cell : Cell | cell.1 = 0}) :=
    MeasurableSet.pi Set.countable_univ fun _ _ => measurable_fst (measurableSet_singleton 0)
  unfold pauseCellsLaw emptyUpTo
  rw [Measure.infinitePi_pi _ fun _ _ => hE]
  refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
  rw [Measure.pi_pi]
  refine Finset.prod_ne_zero_iff.mpr fun p _ => ?_
  have hset : {cell : Cell | cell.1 = 0} = ({0} : Set ℕ) ×ˢ (Set.univ : Set (ℕ → ℝ × ℝ)) := by
    ext cell
    simp
  rw [hset, cellLaw, Measure.prod_prod, measure_univ, mul_one, poissonMeasure_singleton]
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

omit [Fintype H] in
/-- In an outcome of the cells in which the earlier pauses leave a backlog of
at most `K` seconds at true time zero, and no pause begins in the next
`K + M + 1` seconds, every link and every host is idle from true time `K` to
`K + M`. -/
theorem idleOn_of_bounded_empty {K M : ℕ} {ω : ℤ → PauseIndex H → Cell}
    (hb : ω ∈ boundedBefore K) (he : ω ∈ emptyUpTo (K + M)) (p : PauseIndex H) :
    IdleOn (cellPaused 1 ω p) K ((K : ℝ) + M) := by
  have hempty : ∀ c : ℤ, 0 ≤ c → c ≤ ((K + M : ℕ) : ℤ) → (ω c p).1 = 0 := fun c h0 hn =>
    mem_emptyUpTo.mp he c h0 hn p
  have hKM : ((K : ℝ) + M) = ((K + M : ℕ) : ℝ) := by push_cast; ring
  constructor
  · intro q hq
    have hsub : cellPaused 1 ω p K - cellPaused 1 ω p q = pausedBetween q K fun c => ω c p := by
      unfold cellPaused
      simp only [div_one]
      exact pausedPath_sub hq _
    rw [hsub]
    rcases le_or_gt 0 (q : ℝ) with hq0 | hq0
    · rw [pausedBetween_eq_zero_of_empty fun c hc => by
        rw [Finset.mem_Icc, Int.floor_natCast] at hc
        exact hempty c ((Int.floor_nonneg.mpr hq0).trans hc.1) (by push_cast; omega)]
      linarith
    · have hzero : pausedBetween 0 K (fun c => ω c p) = 0 :=
        pausedBetween_eq_zero_of_empty fun c hc => by
          rw [Finset.mem_Icc, Int.floor_natCast, Int.floor_zero] at hc
          exact hempty c hc.1 (by push_cast; omega)
      have hadd := pausedBetween_add hq0.le (Nat.cast_nonneg K) fun c => ω c p
      have hclear := pausedBetween_clearFrom_eq (s := q) (t := 0) (a := 0)
        (ω := fun c => ω c p) (by simp) (hempty 0 le_rfl (by positivity))
      have hbound := hb p q hq0.le
      linarith
  · have hsub : cellPaused 1 ω p ((K : ℝ) + M) - cellPaused 1 ω p K
        = pausedBetween K ((K : ℝ) + M) fun c => ω c p := by
      unfold cellPaused
      simp only [div_one]
      exact pausedPath_sub (by linarith [Nat.cast_nonneg (α := ℝ) M]) _
    have hzero : pausedBetween K ((K : ℝ) + M) (fun c => ω c p) = 0 :=
      pausedBetween_eq_zero_of_empty fun c hc => by
        rw [hKM, Finset.mem_Icc, Int.floor_natCast, Int.floor_natCast] at hc
        exact hempty c (by omega) hc.2
    linarith

omit [Fintype H] in
/-- The change of the paused time over a period, for the cells moved by `n`
cells of one second, is its change over the period moved by `n` seconds. -/
theorem cellPaused_shiftCells_sub (n : ℤ) (ω : ℤ → PauseIndex H → Cell) (p : PauseIndex H)
    {s t : ℝ} (hst : s ≤ t) :
    cellPaused 1 (shiftCells n ω) p t - cellPaused 1 (shiftCells n ω) p s
      = cellPaused 1 ω p (t + n) - cellPaused 1 ω p (s + n) := by
  unfold cellPaused
  simp only [div_one]
  rw [pausedPath_sub hst, pausedPath_sub (by linarith : s + (n : ℝ) ≤ t + n)]
  exact pausedBetween_shiftCells n s t fun c => ω c p

omit [Fintype H] in
/-- A link or a host that is idle from `a` to `b` for the cells moved by `n`
cells of one second is idle from `a + n` to `b + n`. -/
theorem idleOn_of_shiftCells {n : ℕ} {ω : ℤ → PauseIndex H → Cell} {p : PauseIndex H}
    {a b : ℝ} (hab : a ≤ b) (h : IdleOn (cellPaused 1 (shiftCells (n : ℤ) ω) p) a b) :
    IdleOn (cellPaused 1 ω p) (a + n) (b + n) := by
  constructor
  · intro q hq
    have hq' : (((q - n : ℚ)) : ℝ) ≤ a := by
      push_cast
      linarith
    have h1 := h.1 (q - n) hq'
    have h2 := cellPaused_shiftCells_sub (n : ℤ) ω p hq'
    have e : (((q - n : ℚ)) : ℝ) + ((n : ℤ) : ℝ) = q := by
      push_cast
      ring
    rw [e] at h2
    have e2 : a + ((n : ℤ) : ℝ) = a + (n : ℝ) := by push_cast; ring
    rw [e2] at h2
    have hc : (((q - n : ℚ)) : ℝ) = (q : ℝ) - n := by
      push_cast
      ring
    linarith
  · have h2 := cellPaused_shiftCells_sub (n : ℤ) ω p hab
    have e1 : a + ((n : ℤ) : ℝ) = a + (n : ℝ) := by push_cast; ring
    have e2 : b + ((n : ℤ) : ℝ) = b + (n : ℝ) := by push_cast; ring
    rw [e1, e2, h.2, sub_self] at h2
    linarith

/-- **The backlogs before true time zero are bounded with positive
probability.** For some number of seconds `K`, the outcomes of the cells in
which the earlier pauses leave every link and every host a backlog of at
most `K` seconds at true time zero have positive probability. -/
theorem exists_boundedBefore_ne_zero (f : Member H R) :
    ∃ K : ℕ, pauseCellsLaw f 1 (boundedBefore K) ≠ 0 := by
  -- In almost every outcome the paused time of every link and host is tame.
  have htame : ∀ᵐ ω ∂pauseCellsLaw f 1, ∀ p : PauseIndex H,
      Tame (pausedPath fun c => ω c p) := by
    refine ae_all_iff.mpr fun p => ?_
    have hπ := measurePreserving_row f 1 p
    have hload : ((Real.toNNReal (f.pauseRate p * 1) : ℝ≥0) : ℝ) * ∫ y, y ∂f.pauseLength p
        < 1 := by
      rw [Real.coe_toNNReal _ (by have := f.pauseRate_nonneg p; linarith), mul_one]
      exact f.pauseLoad_lt_one p
    have h := ae_tame_pausedPath (Real.toNNReal (f.pauseRate p * 1)) (f.pauseLength p)
      (f.pauseLength_pos p) (f.pauseLength_mean p) hload
    rw [← hπ.map_eq] at h
    exact (ae_map_iff hπ.aemeasurable measurableSet_tame_pausedPath).mp h
  have hex : ∀ᵐ ω ∂pauseCellsLaw f 1, ∃ K : ℕ, ω ∈ boundedBefore K := by
    filter_upwards [htame] with ω hω
    choose B hB using hω
    refine ⟨Finset.univ.sup B + 1, fun p q hq => ?_⟩
    have h1 := pausedBetween_clearFrom_le 0 q 0 fun c => ω c p
    have h2 := pausedPath_sub hq fun c => ω c p
    have hn := Nat.le_ceil (-(q : ℝ))
    have hn' := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ -(q : ℝ) by linarith)
    have h3 := pausedPath_monotone (fun c => ω c p)
      (show -((⌈-(q : ℝ)⌉₊ : ℕ) : ℝ) ≤ q by linarith)
    have h4 := hB p ⌈-(q : ℝ)⌉₊
    have h5 : ((B p : ℕ) : ℝ) ≤ ((Finset.univ.sup B : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Finset.le_sup (Finset.mem_univ p))
    push_cast
    linarith
  by_contra hcon
  push Not at hcon
  have hnull : pauseCellsLaw f 1 (⋃ K : ℕ, boundedBefore (H := H) K) = 0 :=
    measure_iUnion_null_iff.mpr hcon
  have hall : pauseCellsLaw f 1 Set.univ = 0 :=
    measure_mono_null (fun ω _ => by
      by_cases h : ∃ K : ℕ, ω ∈ boundedBefore K
      · exact Or.inl (Set.mem_iUnion.mpr h)
      · exact Or.inr h) (measure_union_null hnull (ae_iff.mp hex))
  rw [measure_univ] at hall
  exact one_ne_zero hall

/-- **All links and hosts are idle together, again and again, for the
cells.** In almost every outcome of the cells of one second, the paused times
are in `idleOften`. -/
theorem ae_cellPaused_mem_idleOften (f : Member H R) :
    ∀ᵐ ω ∂pauseCellsLaw f 1, cellPaused 1 ω ∈ idleOften (PauseIndex H) := by
  obtain ⟨K, hK⟩ := exists_boundedBefore_ne_zero f
  have hT : Ergodic (shiftCells 1) (pauseCellsLaw f 1) :=
    ergodic_shiftCells _ one_ne_zero
  have hvisit : ∀ M : ℕ, ∀ᵐ ω ∂pauseCellsLaw f 1, ∃ᶠ n in atTop,
      (shiftCells 1)^[n] ω ∈ boundedBefore K ∩ emptyUpTo (K + M) := by
    intro M
    refine ae_frequently_mem_of_ergodic hT
      ((measurableSet_boundedBefore K).inter (measurableSet_emptyUpTo _)) ?_
    have hind : pauseCellsLaw f 1 (boundedBefore K ∩ emptyUpTo (K + M))
        = pauseCellsLaw f 1 (boundedBefore K) * pauseCellsLaw f 1 (emptyUpTo (K + M)) := by
      refine measure_inter_of_disjoint_cells _ (I₁ := {c : ℤ | c < 0})
        (I₂ := {c : ℤ | 0 ≤ c}) ?_ (measurableSet_boundedBefore K) (measurableSet_emptyUpTo _)
        ?_ ?_
      · exact Set.disjoint_left.mpr fun c (h1 : c < 0) (h2 : 0 ≤ c) => absurd h2 (not_le.mpr h1)
      · intro ω ω' hsame hω p q hq
        have e : (clearFrom 0 fun c => ω' c p) = clearFrom 0 fun c => ω c p := by
          funext c
          by_cases h : (0 : ℤ) ≤ c
          · simp only [clearFrom, ite_eq_left h]
          · simp only [clearFrom, ite_eq_right h]
            rw [hsame c (not_le.mp h)]
        rw [e]
        exact hω p q hq
      · intro ω ω' hsame hω
        rw [mem_emptyUpTo] at hω ⊢
        intro c h0 hn p
        rw [← hsame c h0]
        exact hω c h0 hn p
    rw [hind]
    exact mul_ne_zero hK (measure_emptyUpTo_ne_zero f 1 _)
  filter_upwards [ae_all_iff.mpr hvisit] with ω hω M N
  obtain ⟨n, hn, hmem⟩ := (frequently_atTop.mp (hω M)) N
  rw [iterate_shiftCells, mul_one] at hmem
  refine ⟨K + n, by omega, fun p => ?_⟩
  have h := idleOn_of_shiftCells (by linarith [Nat.cast_nonneg (α := ℝ) M])
    (idleOn_of_bounded_empty hmem.1 hmem.2 p)
  have e1 : ((K + n : ℕ) : ℝ) = (K : ℝ) + n := by push_cast; ring
  have e2 : (K : ℝ) + n + M = (K : ℝ) + M + n := by ring
  rw [e1, e2]
  exact h

end Cells

/-- **All links and hosts are idle together, again and again.** In every
random world of a member of the generative model, in almost every outcome:
for every number of seconds `M` and every true time `N` there is a later
true time `a` such that no link and no host has a backlog at any true time
from `a` to `a + M`. -/
theorem Prior.ae_idle [Fintype H] {Ω : Type} [MeasurableSpace Ω] {m : GenerativeWorld H R}
    {f : Member H R} {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) :
    ∀ᵐ ω ∂P, ∀ M N : ℕ, ∃ a : ℕ, N ≤ a ∧ ∀ (p : PauseIndex H) (t : ℝ),
      (a : ℝ) ≤ t → t ≤ a + M → IsBacklog ((D ω).paused p) t 0 := by
  have h := hD.ae_paused_mem one_pos (measurableSet_idleOften _) (ae_cellPaused_mem_idleOften f)
  filter_upwards [h] with ω hω M N
  obtain ⟨a, ha, hidle⟩ := hω M N
  refine ⟨a, ha, fun p t hat htb => (hidle p).isBacklog ?_ hat htb⟩
  cases p with
  | inl ij => exact hD.linkPaused_monotone ω _ _
  | inr h => exact hD.hostPaused_monotone ω h

end Unisono.Spec.GenerativeWorld
