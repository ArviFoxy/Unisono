/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Objectives
public import Unisono.Spec.Models.Bounded
public import Unisono.Spec.Models.Delays
public import Unisono.Spec.Models.GenerativeCanonical
public import Unisono.Spec.Models.GenerativeWorld
public import Unisono.Spec.Models.Ideal
public import Unisono.Spec.Models.SecondOrder
public import Unisono.Spec.Models.StochasticWorld
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Checks of the definitions

Statements that say, about small cases, what the definitions of the
objectives say in words. They are not results about the problem; they exist
so that a definition that does not mean what its description says fails to
build.

* The speed equals one minus the rate of change of the latency
  (`speed_eq`).
* Missed samples: an output sample that plays anything but the source
  counts one (`missedAt_none`); continuous playback counts nothing
  (`missedAt_continues`); a jump forward over `J` frames counts `J`
  (`missedAt_skip`); playing `J` frames again counts `J`
  (`missedAt_repeat`); after `g` output samples that played something
  else, which count `g`, a position that continues as if they had played
  counts nothing more (`missedAt_after_gap`), and a position that resumes
  where it stopped counts nothing more either (`missedAt_resume`).
* Discontinuities: a gap counts one, however long it is
  (`discontinuities_gap`), and so does a jump (`discontinuityAt_jump`).
* Roughness across a break: a change of speed `Δv` between two continuous
  steps whose midpoints are `Δt` apart costs `Δv² / Δt`, whatever lies
  between them (`roughnessCost_across`).
* The synchronization cost of a frame, when every speaker plays it, is the
  variance of the times at which they play it (`sum_pairs_eq`); one speaker
  off by `Δ` from all others adds `(R - 1) Δ² / R²` (`syncCost_one_off`).
* Not playing a frame at one speaker lowers the frame's latency cost by that
  speaker's latency divided by the number of speakers
  (`latencyCost_unplayed`).
* The run processes events in chronological order
  (`Solution.eventTime_le_succ`), and a run that advances past every true
  time decides what every output sample plays (`Solution.decided`).
* No model of the world is empty (`Bounds.example_within`,
  `IdealConstantWorld.example_holds`,
  `StationaryNetworkDisturbances.example_holds`,
  `SecondOrderMoments.example_holds`, `StochasticWorld.example_holds`,
  `GenerativeWorld.example_holds`). The example of the generative model has
  no pauses and no wander.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal

variable {H : Type} {R : ℕ}

/-! ## Speed -/

/-- **The speed equals one minus the rate of change of the latency.** Over a
step of continuous playback, the speed is one minus the change of the
latency divided by the time between the two output samples. The latency of
an output sample is the time it leaves minus the time its sound was
captured. -/
theorem speed_eq (w : World H R) (plays : Fin R → ℕ → Option ℝ) (r : Fin R) (k : ℕ)
    {x y : ℝ} (hx : plays r k = some x) (hy : plays r (k + 1) = some y) (hxy : x < y)
    (hyx : y < x + 2) :
    w.speed plays r k = some (1 - (((w.speaker r).out (k + 1) - w.captured y)
      - ((w.speaker r).out k - w.captured x))
      / ((w.speaker r).out (k + 1) - (w.speaker r).out k)) := by
  have hpos : (w.speaker r).out k < (w.speaker r).out (k + 1) :=
    (w.speaker r).out_strictMono (Nat.lt_succ_self k)
  have hne : (w.speaker r).out (k + 1) - (w.speaker r).out k ≠ 0 := by linarith
  simp only [World.speed, hx, hy, hxy, hyx, and_self, ite_true, Option.some.injEq]
  field_simp
  ring

/-! ## Missed samples -/

/-- An output sample that plays anything but the source counts one missed
sample. -/
theorem missedAt_none (plays : ℕ → Option ℝ) {k : ℕ} (h : plays k = none) :
    missedAt plays k = 1 := by
  simp [missedAt, h]

/-- The missed samples counted at output sample `k`, which plays position
`y`. Here `j` is the last earlier output sample that played the source, at
position `x`. -/
theorem missedAt_after (plays : ℕ → Option ℝ) {j k : ℕ} {x y : ℝ} (hjk : j < k)
    (hj : plays j = some x) (hk : plays k = some y)
    (hnone : ∀ i, j < i → i < k → plays i = none) :
    missedAt plays k = (⌊y - x - 1⌋ - ((k - 1 - j : ℕ) : ℤ)).toNat + ⌊1 - (y - x)⌋.toNat := by
  classical
  have hlast : Nat.findGreatest (fun i => (plays i).isSome = true) (k - 1) = j := by
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, fun _ => by simp [hj], fun i hji hik => ?_⟩
    simp [hnone i hji (by omega)]
  have hsome : ∃ i < k, (plays i).isSome = true := ⟨j, hjk, by simp [hj]⟩
  simp only [missedAt, hk, hsome, ite_true]
  rw [hlast, hj]

/-- Continuous playback counts no missed sample. -/
theorem missedAt_continues (plays : ℕ → Option ℝ) {k : ℕ} {x y : ℝ} (hx : plays k = some x)
    (hy : plays (k + 1) = some y) (hxy : x < y) (hyx : y < x + 2) :
    missedAt plays (k + 1) = 0 := by
  rw [missedAt_after plays (Nat.lt_succ_self k) hx hy (fun i h1 h2 => by omega)]
  have h1 : ⌊y - x - 1⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    linarith
  have h2 : ⌊1 - (y - x)⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    linarith
  rw [show k + 1 - 1 - k = 0 by omega, Nat.cast_zero, sub_zero]
  rw [Int.toNat_eq_zero.mpr h1, Int.toNat_eq_zero.mpr h2]

/-- A jump forward over `J` frames counts `J` missed samples. -/
theorem missedAt_skip (plays : ℕ → Option ℝ) {k : ℕ} {x : ℝ} (J : ℕ) (hx : plays k = some x)
    (hy : plays (k + 1) = some (x + 1 + J)) :
    missedAt plays (k + 1) = J := by
  rw [missedAt_after plays (Nat.lt_succ_self k) hx hy (fun i h1 h2 => by omega)]
  have h1 : ⌊x + 1 + (J : ℝ) - x - 1⌋ = J := by
    rw [show x + 1 + (J : ℝ) - x - 1 = (J : ℤ) by push_cast; ring, Int.floor_intCast]
  have h2 : ⌊1 - (x + 1 + (J : ℝ) - x)⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith
  rw [show k + 1 - 1 - k = 0 by omega, Nat.cast_zero, sub_zero]
  rw [h1, Int.toNat_eq_zero.mpr h2]
  simp

/-- Playing `J` frames again counts `J` missed samples. -/
theorem missedAt_repeat (plays : ℕ → Option ℝ) {k : ℕ} {x : ℝ} (J : ℕ) (hx : plays k = some x)
    (hy : plays (k + 1) = some (x + 1 - J)) :
    missedAt plays (k + 1) = J := by
  rw [missedAt_after plays (Nat.lt_succ_self k) hx hy (fun i h1 h2 => by omega)]
  have h1 : ⌊x + 1 - (J : ℝ) - x - 1⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith
  have h2 : ⌊1 - (x + 1 - (J : ℝ) - x)⌋ = J := by
    rw [show 1 - (x + 1 - (J : ℝ) - x) = (J : ℤ) by push_cast; ring, Int.floor_intCast]
  rw [show k + 1 - 1 - k = 0 by omega, Nat.cast_zero, sub_zero]
  have h1' : (⌊x + 1 - (J : ℝ) - x - 1⌋).toNat = 0 := Int.toNat_eq_zero.mpr h1
  rw [h1', h2]
  simp

/-- After `g` non-source outputs, which count `g` missed samples, a position
that continues as if those outputs had played the source counts no further
missed samples. -/
theorem missedAt_after_gap (plays : ℕ → Option ℝ) {k g : ℕ} {x : ℝ} (hx : plays k = some x)
    (hgap : ∀ i, k < i → i < k + 1 + g → plays i = none)
    (hy : plays (k + 1 + g) = some (x + 1 + g)) :
    missedAt plays (k + 1 + g) = 0 := by
  rw [missedAt_after plays (by omega) hx hy hgap]
  have h1 : ⌊x + 1 + (g : ℝ) - x - 1⌋ = g := by
    rw [show x + 1 + (g : ℝ) - x - 1 = (g : ℤ) by push_cast; ring, Int.floor_intCast]
  have h2 : ⌊1 - (x + 1 + (g : ℝ) - x)⌋ ≤ 0 := by
    rw [← Int.lt_add_one_iff, zero_add, Int.floor_lt]
    push_cast
    have : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    linarith
  rw [h1, Int.toNat_eq_zero.mpr h2, show k + 1 + g - 1 - k = g by omega]
  simp

/-- After `g` non-source outputs, which count `g` missed samples, a position
that resumes where playback stopped counts no further missed samples. -/
theorem missedAt_resume (plays : ℕ → Option ℝ) {k g : ℕ} {x : ℝ} (hx : plays k = some x)
    (hgap : ∀ i, k < i → i < k + 1 + g → plays i = none)
    (hy : plays (k + 1 + g) = some (x + 1)) :
    missedAt plays (k + 1 + g) = 0 := by
  rw [missedAt_after plays (by omega) hx hy hgap]
  have h1 : ⌊x + 1 - x - 1⌋ - ((k + 1 + g - 1 - k : ℕ) : ℤ) ≤ 0 := by
    rw [show x + 1 - x - 1 = (0 : ℤ) by push_cast; ring, Int.floor_intCast]
    omega
  have h2 : ⌊1 - (x + 1 - x)⌋ ≤ 0 := by
    rw [show 1 - (x + 1 - x) = (0 : ℤ) by push_cast; ring, Int.floor_intCast]
  rw [Int.toNat_eq_zero.mpr h1, Int.toNat_eq_zero.mpr h2]

/-! ## Synchronization -/

/-- **The pairs and the variance.** For the times `t r` of `R` speakers, the
sum over all pairs of the squared differences equals `R` times the sum of
the squared distances from the mean. Divided by `R ^ 2`, it is the
variance. -/
theorem sum_pairs_eq (t : Fin R → ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (t p.1 - t p.2) ^ 2
      = R * ∑ r, (t r - (∑ r', t r') / R) ^ 2 := by
  -- Every unordered pair of different speakers appears once among the
  -- ordered pairs with the first before the second, and twice among all
  -- ordered pairs; a pair of a speaker with itself adds nothing.
  have hall : ∑ p : Fin R × Fin R, (t p.1 - t p.2) ^ 2
      = 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (t p.1 - t p.2) ^ 2 := by
    have hsplit : ∑ p : Fin R × Fin R, (t p.1 - t p.2) ^ 2
        = ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (t p.1 - t p.2) ^ 2
          + ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2), (t p.1 - t p.2) ^ 2 :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hgt : ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2), (t p.1 - t p.2) ^ 2
        = ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (t p.1 - t p.2) ^ 2 := by
      -- swapping the two speakers of a pair keeps the square
      have hle : ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2),
            (t p.1 - t p.2) ^ 2
          = ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.2 < p.1), (t p.1 - t p.2) ^ 2 := by
        rw [← Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2)) (fun p => p.2 < p.1)]
        have hdiag : ∑ p ∈ (Finset.univ.filter (fun p : Fin R × Fin R => ¬ p.1 < p.2)).filter
              (fun p => ¬ p.2 < p.1), (t p.1 - t p.2) ^ 2 = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp
          have : p.1 = p.2 := le_antisymm hp.2 hp.1
          rw [this, sub_self]
          ring
        rw [hdiag, add_zero, Finset.filter_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨h.le, h⟩
      rw [hle]
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simpa using hp
      · intro p hp
        simpa using hp
      · intro p _
        simp
      · intro p _
        simp
      · intro p _
        simp only [Prod.fst_swap, Prod.snd_swap]
        ring
    rw [hsplit, hgt]
    ring
  -- The sum over all ordered pairs, worked out.
  have hexpand : ∑ p : Fin R × Fin R, (t p.1 - t p.2) ^ 2
      = 2 * (R * ∑ r, t r ^ 2 - (∑ r, t r) ^ 2) := by
    rw [Fintype.sum_prod_type]
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp
  · have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    have hmean : R * ∑ r, (t r - (∑ r', t r') / R) ^ 2 = R * ∑ r, t r ^ 2 - (∑ r, t r) ^ 2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      field_simp
      ring
    rw [hmean]
    linarith [hall, hexpand]


/-! ## The run -/

section Run

variable {Msg : Type}

theorem earliest_ne_none {α : Type} (key : α → Time × ℕ) (a : α) (l : List α) :
    earliest key (a :: l) ≠ none := by
  simp only [earliest]
  cases earliest key l with
  | none => simp
  | some b => dsimp only; split_ifs <;> simp

/-- The element that `earliest` selects from a list belongs to the list, and
its key is at most the key of every element. -/
theorem earliest_spec {α : Type} (key : α → Time × ℕ) :
    ∀ (l : List α) (a : α), earliest key l = some a → a ∈ l ∧ ∀ b ∈ l, (key a).1 ≤ (key b).1
  | [], a, h => by simp [earliest] at h
  | c :: l, a, h => by
      simp only [earliest] at h
      cases hl : earliest key l with
      | none =>
          simp only [hl, Option.some.injEq] at h
          subst h
          cases l with
          | nil => simp
          | cons d l' => exact absurd hl (earliest_ne_none key d l')
      | some b =>
          simp only [hl] at h
          obtain ⟨hb, hmin⟩ := earliest_spec key l b hl
          split_ifs at h with hc
          · simp only [Option.some.injEq] at h
            subst h
            have hcb : (key c).1 ≤ (key b).1 := by
              rcases hc with hc | ⟨hc, _⟩
              · exact hc.le
              · exact hc.le
            refine ⟨by simp, fun d hd => ?_⟩
            rcases List.mem_cons.mp hd with rfl | hd
            · exact le_rfl
            · exact hcb.trans (hmin d hd)
          · simp only [Option.some.injEq] at h
            subst h
            have hbc : (key b).1 ≤ (key c).1 := by
              by_contra hlt
              exact hc (Or.inl (not_le.mp hlt))
            refine ⟨List.mem_cons_of_mem _ hb, fun d hd => ?_⟩
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hbc
            · exact hmin d hd

theorem earliest_exists {α : Type} (key : α → Time × ℕ) {l : List α} (hl : l ≠ []) :
    ∃ a, earliest key l = some a := by
  cases l with
  | nil => exact absurd rfl hl
  | cons c l => exact Option.ne_none_iff_exists'.mp (earliest_ne_none key c l)

/-- **Among the earliest elements of least rank, `earliest` selects the first
of the list.** Every element before the selected one has a strictly larger
key: a later time, or the same time and a higher rank. -/
theorem earliest_spec_first {α : Type} (key : α → Time × ℕ) :
    ∀ (l : List α) (a : α), earliest key l = some a →
      ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ ∀ b ∈ l₁,
        (key a).1 < (key b).1 ∨ ((key a).1 = (key b).1 ∧ (key a).2 < (key b).2)
  | [], a, h => by simp [earliest] at h
  | c :: l, a, h => by
      simp only [earliest] at h
      cases hl : earliest key l with
      | none =>
          simp only [hl, Option.some.injEq] at h
          subst h
          exact ⟨[], l, rfl, by simp⟩
      | some b =>
          simp only [hl] at h
          split_ifs at h with hc
          · simp only [Option.some.injEq] at h
            subst h
            exact ⟨[], l, rfl, by simp⟩
          · simp only [Option.some.injEq] at h
            subst h
            obtain ⟨l₁, l₂, hsplit, hbefore⟩ := earliest_spec_first key l b hl
            refine ⟨c :: l₁, l₂, by rw [hsplit]; rfl, fun x hx => ?_⟩
            rcases List.mem_cons.mp hx with rfl | hx
            · rw [not_or, not_lt, not_and, not_le] at hc
              rcases hc.1.lt_or_eq with hlt | heq
              · exact Or.inl hlt
              · exact Or.inr ⟨heq, hc.2 heq.symm⟩
            · exact hbefore x hx

/-- The number of a host is at most one more than the number of speakers. -/
theorem World.hostIndex_le [DecidableEq H] (w : World H R) (h : H) : w.hostIndex h ≤ R + 1 := by
  unfold World.hostIndex
  split_ifs
  · exact Nat.zero_le _
  · cases hf : (List.finRange R).find? fun r => decide (w.host r = h) with
    | none => simp
    | some r =>
      simp only [Option.elim]
      have := r.isLt
      omega

/-- **Different hosts have different numbers.** -/
theorem World.hostIndex_injective [DecidableEq H] (w : World H R) :
    Function.Injective w.hostIndex := by
  intro a b hab
  have hfind : ∀ h, h ≠ w.sender →
      ∃ r, (List.finRange R).find? (fun r => decide (w.host r = h)) = some r ∧ w.host r = h := by
    intro h hs
    rcases w.hosts h with rfl | ⟨r₀, hr₀⟩
    · exact absurd rfl hs
    · cases hf : (List.finRange R).find? (fun r => decide (w.host r = h)) with
      | none =>
        have hnone := List.find?_eq_none.mp hf r₀ (List.mem_finRange r₀)
        simp [hr₀] at hnone
      | some r =>
        have hsome := List.find?_some hf
        exact ⟨r, rfl, by simpa using hsome⟩
  unfold World.hostIndex at hab
  by_cases ha : a = w.sender <;> by_cases hb : b = w.sender
  · rw [ha, hb]
  · obtain ⟨r, hr, -⟩ := hfind b hb
    rw [ite_eq_left ha, ite_eq_right hb, hr] at hab
    simp only [Option.elim] at hab
    omega
  · obtain ⟨r, hr, -⟩ := hfind a ha
    rw [ite_eq_right ha, ite_eq_left hb, hr] at hab
    simp only [Option.elim] at hab
    omega
  · obtain ⟨ra, hra, ha'⟩ := hfind a ha
    obtain ⟨rb, hrb, hb'⟩ := hfind b hb
    rw [ite_eq_right ha, ite_eq_right hb, hra, hrb] at hab
    simp only [Option.elim] at hab
    have hr : ra = rb := Fin.ext (by omega)
    rw [← ha', ← hb', hr]

theorem Clock.read_timeAt {clock : Clock} {c : ℝ} {u : Time} (h : clock.timeAt c = some u) :
    clock.read u = c := by
  unfold Clock.timeAt at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  exact Classical.choose_spec hc

namespace State

variable (w : World H R) (st : State H R Msg)

theorem due_ne_nil : st.due ≠ [] := by
  simp [due]

theorem handed_mem_due : Due.handed st.handedNext ∈ st.due := by
  simp [due]

theorem asked_mem_due (r : Fin R) : Due.asked r (st.askedNext r) ∈ st.due := by
  simp [due]

theorem arrival_mem_due {p : ℕ} (hp : p < st.inFlight.length) : Due.arrival p ∈ st.due := by
  simp [due, hp]

theorem timer_mem_due {p : ℕ} (hp : p < st.timers.length) : Due.timer p ∈ st.due := by
  simp [due, hp]

theorem mem_due {e : Due R} (he : e ∈ st.due) :
    e = .handed st.handedNext ∨ (∃ r, e = .asked r (st.askedNext r))
      ∨ (∃ p < st.inFlight.length, e = .arrival p) ∨ (∃ p < st.timers.length, e = .timer p) := by
  simp [due] at he
  rcases he with rfl | ⟨r, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨r, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, hp, rfl⟩))

/-- The index of a pending arrival among the messages in transit. -/
def arrivalIndex : Due R → Option ℕ
  | .arrival p => some p
  | _ => none

/-- The pending arrivals are listed in the order of the messages in
transit. -/
theorem due_filterMap_arrivalIndex :
    st.due.filterMap arrivalIndex = List.range st.inFlight.length := by
  have h1 : ((List.finRange R).map fun r => Due.asked r (st.askedNext r)).filterMap
      arrivalIndex = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro d hd
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hd
    rfl
  have h2 : ((List.range st.inFlight.length).map Due.arrival).filterMap (arrivalIndex (R := R))
      = List.range st.inFlight.length := by
    rw [List.filterMap_map]
    exact List.filterMap_some
  have h3 : ((List.range st.timers.length).map Due.timer).filterMap (arrivalIndex (R := R))
      = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro d hd
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
    rfl
  unfold due
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_cons, h2, h3]
  simp only [arrivalIndex, h1, List.append_nil, List.nil_append]

/-- In the list of pending events, an arrival of a lower index comes before
an arrival of a higher index. -/
theorem arrival_mem_of_lt {l₁ l₂ : List (Due R)} {p q : ℕ}
    (hsplit : st.due = l₁ ++ Due.arrival p :: l₂) (hqp : q < p) : Due.arrival q ∈ l₁ := by
  have hrange := st.due_filterMap_arrivalIndex
  rw [hsplit, List.filterMap_append, List.filterMap_cons] at hrange
  simp only [arrivalIndex] at hrange
  have hpw : List.Pairwise (· < ·)
      (l₁.filterMap arrivalIndex ++ p :: l₂.filterMap arrivalIndex) := by
    rw [hrange]
    exact List.pairwise_lt_range
  have hp_mem : p ∈ List.range st.inFlight.length := by
    rw [← hrange]
    simp
  have hq_mem : q ∈ l₁.filterMap arrivalIndex ++ p :: l₂.filterMap arrivalIndex := by
    rw [hrange, List.mem_range]
    exact lt_trans hqp (List.mem_range.mp hp_mem)
  rw [List.pairwise_append] at hpw
  obtain ⟨-, hpw₂, -⟩ := hpw
  rcases List.mem_append.mp hq_mem with h | h
  · obtain ⟨d, hd, hdq⟩ := List.mem_filterMap.mp h
    cases d with
    | arrival x =>
      simp only [arrivalIndex, Option.some.injEq] at hdq
      subst hdq
      exact hd
    | handed b => simp [arrivalIndex] at hdq
    | asked r b => simp [arrivalIndex] at hdq
    | timer x => simp [arrivalIndex] at hdq
  · rcases List.mem_cons.mp h with rfl | h
    · exact absurd hqp (lt_irrefl _)
    · have hlt := (List.pairwise_cons.mp hpw₂).1 q h
      omega

/-- Every pending event of a state occurs at true time `t` or later. -/
def DueFrom (t : Time) : Prop :=
  t ≤ w.source.handed st.handedNext ∧ (∀ r, t ≤ (w.speaker r).asked (st.askedNext r))
    ∧ (∀ m ∈ st.inFlight, t ≤ m.arrival) ∧ (∀ u ∈ st.timers, t ≤ u.time)

theorem DueFrom.le_key [DecidableEq H] {st : State H R Msg} {t : Time} (h : st.DueFrom w t)
    {e : Due R}
    (he : e ∈ st.due) : t ≤ (st.key w e).1 := by
  rcases st.mem_due he with rfl | ⟨r, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact h.1
  · exact h.2.1 r
  · simp only [key, List.getElem?_eq_getElem hp, Option.map_some, Option.getD_some]
    exact h.2.2.1 _ (List.getElem_mem hp)
  · simp only [key, List.getElem?_eq_getElem hp, Option.map_some, Option.getD_some]
    exact h.2.2.2 _ (List.getElem_mem hp)

theorem dueFrom_of_le_key [DecidableEq H] {t : Time} (h : ∀ e ∈ st.due, t ≤ (st.key w e).1) :
    st.DueFrom w t := by
  refine ⟨h _ st.handed_mem_due, fun r => h _ (st.asked_mem_due r), ?_, ?_⟩
  · intro m hm
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hm
    simpa [key, List.getElem?_eq_getElem hp] using h _ (st.arrival_mem_due hp)
  · intro u hu
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hu
    simpa [key, List.getElem?_eq_getElem hp] using h _ (st.timer_mem_due hp)

variable [DecidableEq H]

theorem sendAll_handedNext (h : H) (t : Time) (held : Finset ℕ)
    (sends : List (H × Msg × Finset ℕ)) :
    (st.sendAll w h t held sends).handedNext = st.handedNext := by
  induction sends generalizing st with
  | nil => rfl
  | cons m l ih => exact ih (st.send w h t m.1 m.2.1 (m.2.2.filter (· ∈ held)))

theorem sendAll_askedNext (h : H) (t : Time) (held : Finset ℕ)
    (sends : List (H × Msg × Finset ℕ)) :
    (st.sendAll w h t held sends).askedNext = st.askedNext := by
  induction sends generalizing st with
  | nil => rfl
  | cons m l ih => exact ih (st.send w h t m.1 m.2.1 (m.2.2.filter (· ∈ held)))

theorem sendAll_timers (h : H) (t : Time) (held : Finset ℕ)
    (sends : List (H × Msg × Finset ℕ)) :
    (st.sendAll w h t held sends).timers = st.timers := by
  induction sends generalizing st with
  | nil => rfl
  | cons m l ih => exact ih (st.send w h t m.1 m.2.1 (m.2.2.filter (· ∈ held)))

/-- The messages a host sends at true time `t` arrive after `t`. -/
theorem sendAll_inFlight {h : H} {t t₀ : Time} (ht : t₀ ≤ t) (held : Finset ℕ)
    (sends : List (H × Msg × Finset ℕ)) (hst : ∀ m ∈ st.inFlight, t₀ ≤ m.arrival) :
    ∀ m ∈ (st.sendAll w h t held sends).inFlight, t₀ ≤ m.arrival := by
  induction sends generalizing st with
  | nil => exact hst
  | cons m l ih =>
    refine ih (st.send w h t m.1 m.2.1 (m.2.2.filter (· ∈ held))) ?_
    intro f hf
    simp only [send] at hf
    split at hf
    · rename_i a ha
      rcases List.mem_append.mp hf with hf | hf
      · exact hst f hf
      · simp only [List.mem_singleton] at hf
        subst hf
        exact ht.trans (w.network.after h m.1 t _ a ha).le
    · exact hst f hf

/-- A host that handles an event at true time `t` adds only events after
`t`: the messages it sends arrive after `t`, and the timers it sets fire
after `t`. -/
theorem handle_dueFrom (σ : Solution H R Msg) (lookahead : ℕ+) {h : H} {t : Time}
    {obs : Observation H R Msg} (hst : st.DueFrom w t) :
    (st.handle σ w lookahead h t obs).DueFrom w t := by
  obtain ⟨h1, h2, h3, h4⟩ := hst
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [handle, sendAll_handedNext]
    exact h1
  · intro r
    simp only [handle, sendAll_askedNext]
    exact h2 r
  · intro m hm
    simp only [handle] at hm
    exact sendAll_inFlight w _ le_rfl _ _ (by exact h3) m hm
  · intro u hu
    simp only [handle, sendAll_timers, List.mem_append, List.mem_filterMap] at hu
    rcases hu with hu | ⟨c, _, hc⟩
    · exact h4 u hu
    · split_ifs at hc with hlt
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hc
      have hread := Clock.read_timeAt hv
      exact ((w.clock h).strictMono.lt_iff_lt.mp (hread ▸ hlt)).le

/-- After the earliest pending event is handled, every pending event occurs
no earlier than it. -/
theorem step_dueFrom (σ : Solution H R Msg) (lookahead : ℕ+) {e : Due R}
    (he : earliest (st.key w) st.due = some e) (hst : st.DueFrom w (st.key w e).1) :
    (st.step σ w lookahead).DueFrom w (st.key w e).1 := by
  have hmem := (earliest_spec _ _ _ he).1
  unfold State.step
  rw [he]
  rcases st.mem_due hmem with rfl | ⟨r, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · have hm := st.handle_dueFrom w σ lookahead (h := w.sender)
      (obs := .handed ((w.source.block st.handedNext).map fun n => (n, w.target n))
        (w.source.reported st.handedNext)) hst
    exact ⟨(w.source.handed_strictMono (Nat.lt_succ_self _)).le, hm.2.1, hm.2.2.1, hm.2.2.2⟩
  · have hm := st.handle_dueFrom w σ lookahead (h := w.host r)
      (obs := .asked r ((w.speaker r).block (st.askedNext r))
        ((w.speaker r).reported (st.askedNext r))) hst
    refine ⟨hm.1, fun r' => ?_, hm.2.2.1, hm.2.2.2⟩
    by_cases hr : r' = r
    · subst hr
      simp only [Function.update_self]
      exact ((w.speaker r').asked_strictMono (Nat.lt_succ_self _)).le
    · simp only [Function.update_of_ne hr]
      exact hst.2.1 r'
  · simp only [List.getElem?_eq_getElem hp]
    have hkey : (st.key w (.arrival p)).1 = st.inFlight[p].arrival := by
      simp [key, List.getElem?_eq_getElem hp]
    rw [hkey] at hst ⊢
    apply handle_dueFrom
    exact ⟨hst.1, hst.2.1, fun m hm => hst.2.2.1 m (List.mem_of_mem_eraseIdx hm), hst.2.2.2⟩
  · simp only [List.getElem?_eq_getElem hp]
    have hkey : (st.key w (.timer p)).1 = st.timers[p].time := by
      simp [key, List.getElem?_eq_getElem hp]
    rw [hkey] at hst ⊢
    apply handle_dueFrom
    exact ⟨hst.1, hst.2.1, hst.2.2.1, fun u hu => hst.2.2.2 u (List.mem_of_mem_eraseIdx hu)⟩

end State

variable [DecidableEq H]

theorem Solution.eventTime_dueFrom (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    (n : ℕ) : (σ.states w lookahead n).DueFrom w (σ.eventTime w lookahead n) := by
  apply State.dueFrom_of_le_key
  intro e he
  obtain ⟨e₀, he₀⟩ := earliest_exists ((σ.states w lookahead n).key w)
    (σ.states w lookahead n).due_ne_nil
  simp only [Solution.eventTime, he₀]
  exact (earliest_spec _ _ _ he₀).2 e he

/-- **The run processes events in chronological order.** -/
theorem Solution.eventTime_le_succ (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    (n : ℕ) : σ.eventTime w lookahead n ≤ σ.eventTime w lookahead (n + 1) := by
  set st := σ.states w lookahead n with hst
  obtain ⟨e₀, he₀⟩ := earliest_exists (st.key w) st.due_ne_nil
  have ht : σ.eventTime w lookahead n = (st.key w e₀).1 := by
    simp only [Solution.eventTime, ← hst, he₀]
  have hA := σ.eventTime_dueFrom w lookahead n
  rw [← hst, ht] at hA
  have hB := st.step_dueFrom w σ lookahead he₀ hA
  have hstep : σ.states w lookahead (n + 1) = st.step σ w lookahead := rfl
  obtain ⟨e₁, he₁⟩ := earliest_exists ((σ.states w lookahead (n + 1)).key w)
    (σ.states w lookahead (n + 1)).due_ne_nil
  have ht₁ : σ.eventTime w lookahead (n + 1) = ((σ.states w lookahead (n + 1)).key w e₁).1 := by
    simp only [Solution.eventTime, he₁]
  rw [ht, ht₁]
  rw [← hstep] at hB
  exact hB.le_key w (earliest_spec _ _ _ he₁).1

theorem Solution.eventTime_le_asked (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    (n : ℕ) (r : Fin R) :
    σ.eventTime w lookahead n ≤ (w.speaker r).asked ((σ.states w lookahead n).askedNext r) :=
  (σ.eventTime_dueFrom w lookahead n).2.1 r

/-- A device request that occurs before the event of step `n` has been
handled by step `n`. -/
theorem Solution.lt_askedNext (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {n : ℕ} {r : Fin R} {b : ℕ} (h : (w.speaker r).asked b < σ.eventTime w lookahead n) :
    b < (σ.states w lookahead n).askedNext r := by
  by_contra hle
  have h1 := (w.speaker r).asked_strictMono.monotone (not_lt.mp hle)
  have h2 := σ.eventTime_le_asked w lookahead n r
  linarith

/-- **A run that advances past every true time decides every output
sample.** If, for every true time, the run has a later event, then every
request of every device is handled. Each output sample then plays what the
solution decided at its request (`Solution.plays`). -/
theorem Solution.decided (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    (hgo : ∀ T, ∃ n, T < σ.eventTime w lookahead n) (r : Fin R) (k : ℕ) :
    ∃ n, k < (w.speaker r).first ((σ.states w lookahead n).askedNext r) := by
  obtain ⟨n, hn⟩ := hgo ((w.speaker r).asked k)
  exact ⟨n, (σ.lt_askedNext w lookahead hn).trans_le
    ((w.speaker r).first_strictMono.id_le _)⟩

end Run


section Further

open MeasureTheory Filter Topology

/-! ## Discontinuities -/

/-- A non-source output counts no discontinuity: a gap counts only at its
start. -/
theorem discontinuityAt_none (plays : ℕ → Option ℝ) {k : ℕ} (h : plays k = none) :
    discontinuityAt plays k = 0 := by
  simp [discontinuityAt, h]

/-- The start of a gap counts one discontinuity. -/
theorem discontinuityAt_gap_start (plays : ℕ → Option ℝ) {k : ℕ} {x : ℝ}
    (hx : plays k = some x) (hnext : plays (k + 1) = none) : discontinuityAt plays k = 1 := by
  have : ¬ PlaysContinuously plays k := by
    rintro ⟨a, b, -, hb, -⟩
    simp [hnext] at hb
  simp [discontinuityAt, hx, this]

/-- **A gap counts one discontinuity, however long it is.** -/
theorem discontinuities_gap (plays : ℕ → Option ℝ) {k g : ℕ} {x : ℝ} (hx : plays k = some x)
    (hg : 0 < g) (hgap : ∀ i, k < i → i ≤ k + g → plays i = none) :
    ∑ i ∈ Finset.range (g + 1), discontinuityAt plays (k + i) = 1 := by
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun i hi =>
    discontinuityAt_none plays (hgap _ (by omega) (by simp at hi; omega))]
  simpa using discontinuityAt_gap_start plays hx (hgap (k + 1) (by omega) (by omega))

/-- **A jump counts one discontinuity**: a jump forward by two frames or
more, or any jump back. -/
theorem discontinuityAt_jump (plays : ℕ → Option ℝ) {k : ℕ} {x y : ℝ} (hx : plays k = some x)
    (hy : plays (k + 1) = some y) (hjump : y ≤ x ∨ x + 2 ≤ y) :
    discontinuityAt plays k = 1 := by
  have : ¬ PlaysContinuously plays k := by
    rintro ⟨a, b, ha, hb, hab, hba⟩
    rw [hx, Option.some.injEq] at ha
    rw [hy, Option.some.injEq] at hb
    subst ha
    subst hb
    rcases hjump with h | h <;> linarith
  simp [discontinuityAt, hx, this]

/-- Continuous playback counts no discontinuity. -/
theorem discontinuityAt_continues (plays : ℕ → Option ℝ) {k : ℕ}
    (h : PlaysContinuously plays k) : discontinuityAt plays k = 0 := by
  simp [discontinuityAt, h]

/-! ## Roughness across a break -/

/-- **Roughness across a break.** When the step from output sample `k` has
speed `v`, and the next continuous step is `j`, with speed `v'`, the
roughness between them is `(v' - v)² / Δt`, where `Δt` is the time between
the two steps' midpoints, whatever the output samples between them play. -/
theorem roughnessCost_across (w : World H R) (plays : Fin R → ℕ → Option ℝ) (r : Fin R)
    {k j : ℕ} {v v' : ℝ} (hv : w.speed plays r k = some v) (hkj : k < j)
    (hj : PlaysContinuously (plays r) j)
    (hbetween : ∀ i, k < i → i < j → ¬ PlaysContinuously (plays r) i)
    (hv' : w.speed plays r j = some v') :
    w.roughnessCost plays r k = ENNReal.ofReal ((v' - v) ^ 2 / (((w.speaker r).out j
      + (w.speaker r).out (j + 1) - (w.speaker r).out k - (w.speaker r).out (k + 1)) / 2)) := by
  have hnext : nextContinuous (plays r) k = some j := by
    classical
    unfold nextContinuous
    split
    · rw [Option.some.injEq, Nat.find_eq_iff]
      exact ⟨⟨hkj, hj⟩, fun i hij ⟨hki, hi⟩ => hbetween i hki hij hi⟩
    · rename_i hno
      exact absurd ⟨j, hkj, hj⟩ hno
  simp only [World.roughnessCost, hv, hnext, hv']

/-! ## Muting a speaker -/

/-- **Not playing a frame at one speaker** lowers the frame's latency cost by
that speaker's latency divided by the number of speakers. -/
theorem latencyCost_unplayed (w : World H R) (plays plays' : Fin R → ℕ → Option ℝ) (r : Fin R)
    (n : ℕ) {l : ℝ} (hl : w.latency plays r n = some l) (hl' : w.latency plays' r n = none)
    (hothers : ∀ r', r' ≠ r → w.latency plays' r' n = w.latency plays r' n) :
    w.latencyCost plays n = w.latencyCost plays' n + (R : ℝ≥0∞)⁻¹ * ENNReal.ofReal l := by
  have h1 : w.latencyAt plays r n = ENNReal.ofReal l := by simp [World.latencyAt, hl]
  have h2 : w.latencyAt plays' r n = 0 := by simp [World.latencyAt, hl']
  have h3 : ∀ x ∈ Finset.univ.erase r, w.latencyAt plays' x n = w.latencyAt plays x n :=
    fun x hx => by simp only [World.latencyAt, hothers x (Finset.ne_of_mem_erase hx)]
  unfold World.latencyCost
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), ← Finset.add_sum_erase _ _ (Finset.mem_univ r),
    h1, h2, Finset.sum_congr rfl h3]
  ring

/-- **One speaker off by `Δ`.** When every speaker but `r` plays frame `n` at
the same time `t`, and speaker `r` plays it at `t + Δ`, the frame's
synchronization cost is `(R - 1) Δ² / R²`, about `Δ² / R`. The variance
therefore weighs a single outlying speaker less as the number of speakers
grows. -/
theorem syncCost_one_off (w : World H R) (plays : Fin R → ℕ → Option ℝ) (r : Fin R) (n : ℕ)
    {t Δ : ℝ} (hr : w.playTime plays r n = some (t + Δ))
    (hothers : ∀ r', r' ≠ r → w.playTime plays r' n = some t) :
    w.syncCost plays n = ((R : ℝ≥0∞) ^ 2)⁻¹ * (((R - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Δ ^ 2)) := by
  have hpair : ∀ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
      w.pairCost plays p.1 p.2 n = if p.1 = r ∨ p.2 = r then ENNReal.ofReal (Δ ^ 2) else 0 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h1 : p.1 = r
    · have h2 : p.2 ≠ r := fun h => by rw [h1, h] at hp; exact lt_irrefl _ hp
      simp [World.pairCost, h1, hr, hothers p.2 h2]
    · by_cases h2 : p.2 = r
      · simp [World.pairCost, h2, hr, hothers p.1 h1]
      · simp [World.pairCost, hothers p.1 h1, hothers p.2 h2, h1, h2]
  have hcard : ((Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2)).filter
      (fun p => p.1 = r ∨ p.2 = r)).card = R - 1 := by
    have ht : (Finset.univ.erase r).card = R - 1 := by simp [Finset.card_erase_of_mem]
    rw [← ht]
    refine Finset.card_bij (fun p _ => if p.1 = r then p.2 else p.1) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      obtain ⟨hlt, h | h⟩ := hp
      · rw [ite_eq_left h]
        intro he
        rw [h, he] at hlt
        exact lt_irrefl _ hlt
      · have h1 : p.1 ≠ r := fun he => by rw [he, h] at hlt; exact lt_irrefl _ hlt
        rw [ite_eq_right h1]
        exact h1
    · intro p hp p' hp' heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
      obtain ⟨hlt, h⟩ := hp
      obtain ⟨hlt', h'⟩ := hp'
      by_cases h1 : p.1 = r <;> by_cases h1' : p'.1 = r
      · rw [ite_eq_left h1, ite_eq_left h1'] at heq
        exact Prod.ext (h1.trans h1'.symm) heq
      · rw [ite_eq_left h1, ite_eq_right h1'] at heq
        have h2' : p'.2 = r := h'.resolve_left h1'
        rw [h1] at hlt
        rw [h2'] at hlt'
        rw [heq] at hlt
        exact absurd hlt' (lt_asymm hlt)
      · rw [ite_eq_right h1, ite_eq_left h1'] at heq
        have h2 : p.2 = r := h.resolve_left h1
        rw [h1'] at hlt'
        rw [h2] at hlt
        rw [← heq] at hlt'
        exact absurd hlt (lt_asymm hlt')
      · rw [ite_eq_right h1, ite_eq_right h1'] at heq
        have h2 : p.2 = r := h.resolve_left h1
        have h2' : p'.2 = r := h'.resolve_left h1'
        exact Prod.ext heq (h2.trans h2'.symm)
    · intro r' hr'
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hr'
      rcases lt_or_gt_of_ne hr' with h | h
      · refine ⟨(r', r), by simp [h], ?_⟩
        simp only
        rw [ite_eq_right hr']
      · refine ⟨(r, r'), by simp [h], ?_⟩
        simp
  unfold World.syncCost
  rw [Finset.sum_congr rfl hpair, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, hcard]

/-! ## No model is empty -/

/-- **The bounded model is not empty.** A world with one speaker on the
sender's host, exact clocks and devices, blocks of one frame, and a network
that delivers every message after one second satisfies the bounds. -/
theorem Bounds.example_within : ∃ (w : World Unit 1) (B : Bounds Unit), w.WithinBounds B := by
  refine ⟨
    { rate := 1
      rate_pos := one_pos
      sender := ()
      host := fun _ => ()
      hosts := fun _ => Or.inl rfl
      clock := fun _ => ⟨id, strictMono_id, continuous_id⟩
      source :=
        { capture := fun n => n
          capture_strictMono := Nat.strictMono_cast
          first := id
          first_zero := rfl
          first_strictMono := strictMono_id
          handed := fun b => b
          handed_strictMono := Nat.strictMono_cast
          handed_after := fun b => by simp
          reported := fun b => b }
      speaker := fun _ =>
        { out := fun k => k + 1
          out_strictMono := fun a b h => by simpa using h
          first := id
          first_zero := rfl
          first_strictMono := strictMono_id
          asked := fun b => b + 1 / 2
          asked_strictMono := fun a b h => by simpa using h
          asked_before := fun b => by norm_num
          reported := fun b => b + 1 }
      network := ⟨fun _ _ s _ => some (s + 1), fun _ _ s _ a h => by
        simp only [Option.some.injEq] at h; linarith⟩
      target := fun _ => 0 },
    { clockRate := 0
      clockRate_nonneg := le_rfl
      clockRate_lt_one := one_pos
      deviceRate := 0
      deviceRate_nonneg := le_rfl
      deviceRate_lt_one := one_pos
      report := 0
      report_nonneg := le_rfl
      handoff := 0
      handoff_nonneg := le_rfl
      leadLeast := 1 / 2
      leadMost := 1 / 2
      leadLeast_pos := by norm_num
      leadLeast_le := le_rfl
      blockLeast := 1
      blockMost := 1
      blockLeast_pos := one_pos
      blockLeast_le := le_rfl
      delayLeast := fun _ _ => 1
      delayMost := fun _ _ => 1
      delayLeast_pos := fun _ _ => one_pos
      delayLeast_le := fun _ _ => le_rfl
      lossRun := 0 }, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h s t _
    simp
  · intro n
    simp
  · intro r k
    simp
  · intro b
    simp
  · intro r b
    simp
  · intro b
    simp
  · intro r b
    norm_num
  · intro b
    simp
  · intro r b
    simp
  · intro i j s q a h
    simp only [Option.some.injEq] at h
    constructor <;> linarith
  · intro i j q send
    exact ⟨0, le_rfl, rfl⟩

/-- **The ideal constant world model is not empty** (including both symmetric
and asymmetric instances, and every instance satisfies `WithinBounds`). -/
theorem IdealConstantWorld.example_holds :
    (∃ (m : IdealConstantWorld (Fin 2) 1) (w : World (Fin 2) 1), m.Holds w ∧ m.Symmetric)
    ∧ (∃ (m : IdealConstantWorld (Fin 2) 1) (w : World (Fin 2) 1), m.Holds w ∧ m.Asymmetric) := by
  let mkWorld (d : Fin 2 → Fin 2 → ℝ) (hd : ∀ i j, 0 < d i j) : World (Fin 2) 1 :=
      { rate := 1
        rate_pos := one_pos
        sender := 0
        host := fun _ => 1
        hosts := fun h => by
          fin_cases h
          · exact Or.inl rfl
          · exact Or.inr ⟨0, rfl⟩
        clock := fun h => ⟨fun t => t + (h : ℕ), fun _ _ hlt => by linarith,
          continuous_id.add continuous_const⟩
        source :=
          { capture := fun n => n
            capture_strictMono := Nat.strictMono_cast
            first := id
            first_zero := rfl
            first_strictMono := strictMono_id
            handed := fun b => b
            handed_strictMono := Nat.strictMono_cast
            handed_after := fun b => by simp
            reported := fun b => b }
        speaker := fun _ =>
          { out := fun k => k + 1
            out_strictMono := fun a b h => by simpa using h
            first := id
            first_zero := rfl
            first_strictMono := strictMono_id
            asked := fun b => b + 1 / 2
            asked_strictMono := fun a b h => by simpa using h
            asked_before := fun b => by norm_num
            reported := fun b => (b + 1 : ℝ) + 1 }
        network := ⟨fun i j s _ => some (s + d i j), fun i j s _ a h => by
          simp only [Option.some.injEq] at h; linarith [hd i j]⟩
        target := fun _ => 1 }
  have mkHolds : ∀ (d : Fin 2 → Fin 2 → ℝ) (hd : ∀ i j, 0 < d i j),
      IdealConstantWorld.Holds
        { rate := 1, rate_pos := one_pos, sender := 0, host := fun _ => 1,
          delay := d, delay_pos := hd, blockSize := 1, blockSize_pos := one_pos,
          lead := 1 / 2, lead_pos := by norm_num, targetLatency := 1, targetLatency_nonneg := zero_le_one }
        (mkWorld d hd) := by
    intro d hd
    refine
      { rate_eq := rfl
        sender_eq := rfl
        host_eq := rfl
        clocks := fun h => ⟨(h : ℕ), fun _ => rfl⟩
        capture := ⟨0, fun n => by simp [mkWorld]⟩
        capture_first := fun b => by simp [mkWorld]
        capture_handed := fun b => by simp [mkWorld]
        capture_reported := fun b => by simp [mkWorld]
        speaker_out := fun _ => ⟨1, fun k => by simp [mkWorld]; ring⟩
        speaker_first := fun _ b => by simp [mkWorld]
        speaker_asked := fun _ b => by simp [mkWorld]; ring
        speaker_reported := fun _ b => by simp [mkWorld]
        network := fun _ _ _ _ => rfl
        target_eq := fun _ => rfl }
  constructor
  · refine ⟨_, mkWorld (fun _ _ => 1) (fun _ _ => one_pos),
      mkHolds (fun _ _ => 1) (fun _ _ => one_pos), fun _ _ => rfl⟩
  · let dAsym : Fin 2 → Fin 2 → ℝ := fun i j => if i = 0 ∧ j = 1 then 2 else 1
    have hdAsym : ∀ i j, 0 < dAsym i j := fun i j => by
      simp only [dAsym]; split_ifs <;> norm_num
    refine ⟨_, mkWorld dAsym hdAsym, mkHolds dAsym hdAsym, 0, 1, ?_⟩
    simp [dAsym]

/-- **The stationary network disturbances model class is not empty**: a network
of one host whose link to itself has a constant baseline of one second, no
jitter, no pauses and no losses belongs to the model class with zero rates. -/
theorem StationaryNetworkDisturbances.example_holds :
    ∃ (m : StationaryNetworkDisturbances Unit) (P : Measure Unit)
      (d : Unit → Unit → Unit → Link), IsProbabilityMeasure P ∧ m.Holds P d := by
  let link : Link := ⟨fun _ => 1, fun _ _ => 0, ∅, ∅⟩
  let d : Unit → Unit → Unit → Link := fun _ _ _ => link
  have hstate : ∀ u q, link.state u q = (0, false, false) := by
    intro u q
    simp [Link.state, Link.Holds, Link.Loses, link]
  have hshift : ∀ τ ω, shiftTime τ (linkStates d ω) = linkStates d ω := by
    intro τ ω
    funext i j u q
    simp [shiftTime, linkStates, d, hstate]
  have hdrop : ∀ m ω, shiftCount m (droppedMessages d ω) = droppedMessages d ω := by
    intro m ω
    funext i j q
    simp [shiftCount, droppedMessages, d, link]
  have hmix : ∀ {β : Type} [MeasurableSpace β] (X : Unit → β) (A B : Set β),
      (Measure.dirac ()) {ω | X ω ∈ A ∧ X ω ∈ B}
        = (Measure.dirac ()) {ω | X ω ∈ A} * (Measure.dirac ()) {ω | X ω ∈ B} := by
    intro β _ X A B
    simp only [Measure.dirac_apply, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    by_cases hA : X () ∈ A <;> by_cases hB : X () ∈ B <;> simp [hA, hB]
  refine ⟨
    { slope := fun _ _ => 0
      slope_nonneg := fun _ _ => le_rfl
      tailFactor := fun _ _ => 1
      tailFactor_pos := fun _ _ => one_pos
      tailScale := fun _ _ => 1
      tailScale_pos := fun _ _ => one_pos
      pauseRate := fun _ _ _ => 0
      pauseRate_nonneg := fun _ _ _ => le_rfl
      pauseLength := fun _ _ _ => Measure.dirac 1
      pauseLength_probability := fun _ _ _ => inferInstance
      pauseLength_pos := fun _ _ _ => by simp [Measure.dirac_apply']
      pauseLength_mean := fun _ _ _ => by
        rw [lintegral_dirac]
        exact ENNReal.ofReal_lt_top
      lossProbability := fun _ _ => 0
      lossProbability_nonneg := fun _ _ => le_rfl
      lossProbability_lt_one := fun _ _ => zero_lt_one },
    Measure.dirac (), d, inferInstance, ?_⟩
  refine
    { baseline_pos := fun _ _ _ _ => one_pos
      baseline_slow := fun _ _ _ _ _ => by simp [d, link]
      jitter_nonneg := fun _ _ _ _ _ => le_rfl
      jitter_near_zero := fun _ _ _ _ δ hδ => by simp [d, link, hδ]
      jitter_tail := fun _ _ _ _ x hx => by simp [d, link, not_lt.mpr hx]
      pause_length_pos := fun _ _ _ p hp => by simp [d, link] at hp
      paused_lt_one := fun _ _ _ => by simp [d, link, Link.Holds]
      outage_lt_one := fun _ _ _ => by simp [d, link, Link.Loses]
      pauses := fun _ _ _ _ _ _ _ _ => by simp [d, link]
      lost := fun _ _ _ => by simp [d, link]
      state_measurable := fun _ _ _ _ => measurable_const' fun _ _ => rfl
      lost_measurable := fun _ _ _ => by simp [d, link]
      states_stationary := fun τ => by simp only [hshift]
      states_mixing := fun A B _ _ => by
        simp only [hshift]
        rw [hmix]
        exact tendsto_const_nhds
      dropped_stationary := fun m => by simp only [hdrop]
      dropped_mixing := fun A B _ _ => by
        simp only [hdrop]
        rw [hmix]
        exact tendsto_const_nhds }

/-- **The second-order moments model class is not empty**: a 3-host star
(sender `0`, speakers on hosts `1` and `2`) over a uniform probability space on
`Bool × Bool`, with nonzero uncorrelated per-packet link jitter of variance `1`
on links `(0, 1)` and `(0, 2)` and zero clock, device, and timestamp noise,
satisfies `SecondOrderMoments.Holds`. Band-limiting `ClockNoise` to
`[lowFreq, highFreq]` resolves the rate-bound incompatibility
(`secondDifferenceCovariance_diag_le`), while constructing a witness with
nonzero `ClockNoise` whose clock paths remain strictly increasing remains open. -/
theorem SecondOrderMoments.example_holds : ∃ (m : SecondOrderMoments (Fin 3) 2)
    (P : Measure (Bool × Bool)) (world : Bool × Bool → World (Fin 3) 2)
    (d : Bool × Bool → Fin 3 → Fin 3 → Link),
    m.Holds P world d ∧
      m.ownJitter 0 1 = ⟨1, fun _ _ => 1⟩ ∧ m.ownJitter 0 2 = ⟨1, fun _ _ => 1⟩ := by
  let P : Measure (Bool × Bool) :=
    (4 : ℝ≥0∞)⁻¹ • (Measure.dirac (false, false) + Measure.dirac (false, true)
      + Measure.dirac (true, false) + Measure.dirac (true, true))
  have hP : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    simp only [P, smul_apply, add_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.indicator_univ, Pi.one_apply, smul_eq_mul]
    have h4 : (1 : ℝ≥0∞) + 1 + 1 + 1 = 4 := by norm_num
    rw [h4, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  have hmemLp : ∀ f : Bool × Bool → ℝ, MemLp f 2 P := by
    intro f
    have : IsProbabilityMeasure P := hP
    refine MemLp.of_bound (Measurable.aestronglyMeasurable (measurable_of_countable f))
      (max (max |f (false, false)| |f (false, true)|)
        (max |f (true, false)| |f (true, true)|)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    rcases ω with ⟨b₁, b₂⟩
    cases b₁ <;> cases b₂
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hint : ∀ f : Bool × Bool → ℝ,
      ∫ ω, f ω ∂P = (f (false, false) + f (false, true) + f (true, false) + f (true, true)) / 4 := by
    intro f
    have hfin : ∀ a : Bool × Bool, Integrable f (Measure.dirac a) :=
      fun a => integrable_dirac eNorm_lt_top
    have hadd1 : Integrable f (Measure.dirac (false, false) + Measure.dirac (false, true)) :=
      (hfin _).add_measure (hfin _)
    have hadd2 : Integrable f
        (Measure.dirac (false, false) + Measure.dirac (false, true) + Measure.dirac (true, false)) :=
      hadd1.add_measure (hfin _)
    simp only [P, integral_smul_measure, integral_add_measure hadd2 (hfin _),
      integral_add_measure hadd1 (hfin _), integral_add_measure (hfin _) (hfin _),
      integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
    ring
  let s1 : Bool × Bool → ℝ := fun ω => if ω.1 then 1 else -1
  let s2 : Bool × Bool → ℝ := fun ω => if ω.2 then 1 else -1
  let own : Bool × Bool → Fin 3 → Fin 3 → Time → ℕ → ℝ := fun ω i j _ _ =>
    if i = 0 ∧ j = 1 then 1 + s1 ω else if i = 0 ∧ j = 2 then 1 + s2 ω else 0
  have hown_nonneg : ∀ ω i j u q, 0 ≤ own ω i j u q := by
    intro ω i j u q
    simp only [own, s1, s2]
    split_ifs <;> norm_num
  let d : Bool × Bool → Fin 3 → Fin 3 → Link := fun ω i j =>
    ⟨fun _ => 1, own ω i j, ∅, ∅⟩
  let world : Bool × Bool → World (Fin 3) 2 := fun ω =>
    { rate := 1
      rate_pos := one_pos
      sender := 0
      host := fun r => if r = 0 then 1 else 2
      hosts := fun h => by
        fin_cases h
        · exact Or.inl rfl
        · exact Or.inr ⟨0, by decide⟩
        · exact Or.inr ⟨1, by decide⟩
      clock := fun _ => ⟨id, strictMono_id, continuous_id⟩
      source :=
        { capture := fun n => n
          capture_strictMono := Nat.strictMono_cast
          first := id
          first_zero := rfl
          first_strictMono := strictMono_id
          handed := fun b => b
          handed_strictMono := Nat.strictMono_cast
          handed_after := fun b => by simp
          reported := fun b => b }
      speaker := fun _ =>
        { out := fun k => k + 1
          out_strictMono := fun a b h => by simpa using h
          first := id
          first_zero := rfl
          first_strictMono := strictMono_id
          asked := fun b => b + 1 / 2
          asked_strictMono := fun a b h => by simpa using h
          asked_before := fun b => by norm_num
          reported := fun b => b + 1 }
      network := ⟨fun i j s q => (d ω i j).deliver s q,
        fun i j _ _ _ h => Link.deliver_after (d ω i j) (fun _ => one_pos) (hown_nonneg ω i j) h⟩
      target := fun _ => 0 }
  let ownJ : Fin 3 → Fin 3 → PacketJitterNoise := fun i j =>
    if i = 0 ∧ j = 1 then ⟨1, fun _ _ => 1⟩
    else if i = 0 ∧ j = 2 then ⟨1, fun _ _ => 1⟩
    else ⟨0, fun _ _ => 0⟩
  let m : SecondOrderMoments (Fin 3) 2 :=
    { rate := 1
      rate_pos := one_pos
      sender := 0
      host := fun r => if r = 0 then 1 else 2
      clock := fun _ => ClockNoise.zero
      txJitter := fun _ => ⟨0, fun _ => 0⟩
      rxJitter := fun _ => ⟨0, fun _ => 0⟩
      ownJitter := ownJ
      capture := ClockNoise.zero
      playback := fun _ => ClockNoise.zero
      captureTimestampVariance := 0
      captureTimestampVariance_nonneg := le_rfl
      playbackTimestampVariance := fun _ => 0
      playbackTimestampVariance_nonneg := fun _ => le_rfl }
  have hclk_zero : ∀ ω i t τ, secondDifference (fun t => ((world ω).clock i).read t - t) t τ = 0 := by
    intro ω i t τ
    simp [world, secondDifference]
  have hdev_cap : ∀ ω k j, gridDifference (devicePhase (world ω).source.capture m.rate) k j = 0 := by
    intro ω k j
    simp [m, world, devicePhase, gridDifference]
  have hdev_spk : ∀ ω r k j,
      gridDifference (devicePhase ((world ω).speaker r).out m.rate) k j = 0 := by
    intro ω r k j
    simp only [m, world, devicePhase, gridDifference]
    push_cast
    simp only [div_one]
    ring
  refine ⟨m, P, world, d, ?_, by simp [m, ownJ], by simp [m, ownJ]⟩
  refine
    { prob := hP
      network := fun _ _ _ _ _ => rfl
      rate_eq := fun _ => rfl
      sender_eq := fun _ => rfl
      host_eq := fun _ _ => rfl
      clocks := fun i => ⟨fun _ _ => hmemLp _, fun t τ => by simp [hclk_zero],
        fun t₁ τ₁ t₂ τ₂ => by simp [m, hclk_zero, secondDifferenceCovariance_zero]⟩
      clocks_uncorrelated := fun i j _ t₁ τ₁ t₂ τ₂ => by simp [hclk_zero]
      jitter := ⟨fun _ _ _ => 0, fun _ _ _ => 0, own,
        fun ω i j u q => by simp [d],
        fun _ => ⟨fun _ => hmemLp _, fun _ => by simp [m], fun _ _ => by simp [m]⟩,
        fun _ => ⟨fun _ => hmemLp _, fun _ => by simp [m], fun _ _ => by simp [m]⟩,
        fun i j => ⟨fun _ _ => hmemLp _, fun s q => by
            rw [hint]
            by_cases h1 : i = 0 ∧ j = 1
            · simp [m, ownJ, own, s1, h1]; norm_num
            · by_cases h2 : i = 0 ∧ j = 2
              · simp [m, ownJ, own, s2, h2]; norm_num
              · simp [m, ownJ, own, h1, h2],
          fun s q u q' => by
            rw [hint]
            by_cases h1 : i = 0 ∧ j = 1
            · simp [m, ownJ, own, s1, h1]; norm_num
            · by_cases h2 : i = 0 ∧ j = 2
              · simp [m, ownJ, own, s2, h2]; norm_num
              · simp [m, ownJ, own, h1, h2]⟩,
        fun _ _ _ _ _ _ => by simp,
        fun _ _ _ _ _ _ => by simp,
        fun i j i' j' hne s q u q' => by
          have hzero_left : ∀ a b : Fin 3, ¬(a = 0 ∧ b = 1) → ¬(a = 0 ∧ b = 2) →
              ∀ ω t k, own ω a b t k = 0 := fun a b h1 h2 ω t k => by simp [own, h1, h2]
          by_cases h1 : i = 0 ∧ j = 1
          · by_cases h2' : i' = 0 ∧ j' = 2
            · simp only [hint, own, s1, s2, h1, h2', and_true, true_and, ite_true]
              norm_num
            · have h1' : ¬(i' = 0 ∧ j' = 1) := by
                intro h; exact hne (Prod.ext (h1.1.trans h.1.symm) (h1.2.trans h.2.symm))
              simp [hzero_left i' j' h1' h2']
          · by_cases h2 : i = 0 ∧ j = 2
            · by_cases h1' : i' = 0 ∧ j' = 1
              · simp only [hint, own, s1, s2, h2, h1', and_true, true_and, ite_true]
                norm_num
              · have h2' : ¬(i' = 0 ∧ j' = 2) := by
                  intro h; exact hne (Prod.ext (h2.1.trans h.1.symm) (h2.2.trans h.2.symm))
                simp [hzero_left i' j' h1' h2']
            · simp [hzero_left i j h1 h2],
        fun _ _ _ _ _ => by simp [hclk_zero],
        fun _ _ _ _ _ => by simp [hclk_zero],
        fun _ _ _ _ _ _ _ => by simp [hclk_zero],
        fun _ _ _ _ => by simp [hdev_cap],
        fun _ _ _ _ => by simp [hdev_cap],
        fun _ _ _ _ _ _ => by simp [hdev_cap],
        fun _ _ _ _ _ => by simp [hdev_spk],
        fun _ _ _ _ _ => by simp [hdev_spk],
        fun _ _ _ _ _ _ _ => by simp [hdev_spk],
        fun _ _ _ => by simp [world, captureError],
        fun _ _ _ => by simp [world, captureError],
        fun _ _ _ _ _ => by simp [world, captureError],
        fun _ _ _ _ => by simp [world, playbackError],
        fun _ _ _ _ => by simp [world, playbackError],
        fun _ _ _ _ _ _ => by simp [world, playbackError]⟩
      capture := ⟨fun _ _ => hmemLp _, fun k j => by simp [hdev_cap],
        fun k₁ j₁ k₂ j₂ => by simp [m, hdev_cap, secondDifferenceCovariance_zero]⟩
      playback := fun r => ⟨fun _ _ => hmemLp _, fun k j => by simp [hdev_spk],
        fun k₁ j₁ k₂ j₂ => by simp [m, hdev_spk, secondDifferenceCovariance_zero]⟩
      capture_clock_uncorrelated := fun i _ t τ k j => by simp [hclk_zero]
      playback_clock_uncorrelated := fun i r _ t τ k j => by simp [hclk_zero]
      capture_playback_uncorrelated := fun r _ k₁ j₁ k₂ j₂ => by simp [hdev_cap]
      playback_uncorrelated := fun r r' _ k₁ j₁ k₂ j₂ => by simp [hdev_spk]
      capture_timestamps := ⟨fun _ => hmemLp _, fun b => by simp [world, captureError],
        fun b b' => by simp [m, world, captureError]⟩
      playback_timestamps := fun r => ⟨fun _ => hmemLp _, fun b => by simp [world, playbackError],
        fun b b' => by simp [m, world, playbackError]⟩
      capture_playback_timestamps_uncorrelated := fun r b₁ b₂ => by simp [world, captureError]
      playback_timestamps_uncorrelated := fun r r' _ b₁ b₂ => by simp [world, playbackError]
      clock_capture_timestamps_uncorrelated := fun i t τ b => by simp [hclk_zero]
      clock_playback_timestamps_uncorrelated := fun i r t τ b => by simp [hclk_zero]
      capture_device_capture_timestamps_uncorrelated := fun k j b => by simp [hdev_cap]
      capture_device_playback_timestamps_uncorrelated := fun r k j b => by simp [hdev_cap]
      playback_device_capture_timestamps_uncorrelated := fun r k j b => by simp [hdev_spk]
      playback_device_playback_timestamps_uncorrelated := fun r r' k j b => by simp [hdev_spk] }

/-- **The composite stochastic world model class is not empty**: a degenerate
Dirac world satisfies both `StationaryNetworkDisturbances` and
`SecondOrderMoments` together with the deterministic handoff, request-lead, and
block-size bounds. -/
theorem StochasticWorld.example_holds :
    ∃ (m : StochasticWorld Unit 1) (P : Measure Unit) (world : Unit → World Unit 1),
      m.Holds P world := by
  let link : Link := ⟨fun _ => 1, fun _ _ => 0, ∅, ∅⟩
  let d₀ : Unit → Unit → Unit → Link := fun _ _ _ => link
  have hstate : ∀ u q, link.state u q = (0, false, false) := fun u q => by
    simp [Link.state, Link.Holds, Link.Loses, link]
  have hshift : ∀ τ ω, shiftTime τ (linkStates d₀ ω) = linkStates d₀ ω := fun τ ω => by
    funext i j u q; simp [shiftTime, linkStates, d₀, hstate]
  have hdrop : ∀ m ω, shiftCount m (droppedMessages d₀ ω) = droppedMessages d₀ ω := fun m ω => by
    funext i j q; simp [shiftCount, droppedMessages, d₀, link]
  have hmix : ∀ {β : Type} [MeasurableSpace β] (X : Unit → β) (A B : Set β),
      (Measure.dirac ()) {ω | X ω ∈ A ∧ X ω ∈ B}
        = (Measure.dirac ()) {ω | X ω ∈ A} * (Measure.dirac ()) {ω | X ω ∈ B} := by
    intro β _ X A B
    simp only [Measure.dirac_apply, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    by_cases hA : X () ∈ A <;> by_cases hB : X () ∈ B <;> simp [hA, hB]
  let w₀ : World Unit 1 :=
    { rate := 1
      rate_pos := one_pos
      sender := ()
      host := fun _ => ()
      hosts := fun _ => Or.inl rfl
      clock := fun _ => ⟨id, strictMono_id, continuous_id⟩
      source :=
        { capture := fun n => n
          capture_strictMono := Nat.strictMono_cast
          first := id
          first_zero := rfl
          first_strictMono := strictMono_id
          handed := fun b => b
          handed_strictMono := Nat.strictMono_cast
          handed_after := fun b => by simp
          reported := fun b => b }
      speaker := fun _ =>
        { out := fun k => k + 1
          out_strictMono := fun a b h => by simpa using h
          first := id
          first_zero := rfl
          first_strictMono := strictMono_id
          asked := fun b => b + 1 / 2
          asked_strictMono := fun a b h => by simpa using h
          asked_before := fun b => by norm_num
          reported := fun b => b + 1 }
      network := ⟨fun i j s q => (d₀ () i j).deliver s q,
        fun i j _ _ _ h => Link.deliver_after (d₀ () i j) (fun _ => one_pos) (fun _ _ => le_rfl) h⟩
      target := fun _ => 0 }
  let P₀ : Measure Unit := Measure.dirac ()
  have hmem : ∀ f : Unit → ℝ, MemLp f 2 P₀ := fun f =>
    MemLp.of_bound (Measurable.aestronglyMeasurable (measurable_of_countable f)) |f ()|
      (ae_of_all _ fun _ => by rw [Real.norm_eq_abs])
  let mNet₀ : StationaryNetworkDisturbances Unit :=
    { slope := fun _ _ => 0
      slope_nonneg := fun _ _ => le_rfl
      tailFactor := fun _ _ => 1
      tailFactor_pos := fun _ _ => one_pos
      tailScale := fun _ _ => 1
      tailScale_pos := fun _ _ => one_pos
      pauseRate := fun _ _ _ => 0
      pauseRate_nonneg := fun _ _ _ => le_rfl
      pauseLength := fun _ _ _ => Measure.dirac 1
      pauseLength_probability := fun _ _ _ => inferInstance
      pauseLength_pos := fun _ _ _ => by simp [Measure.dirac_apply']
      pauseLength_mean := fun _ _ _ => by rw [lintegral_dirac]; exact ENNReal.ofReal_lt_top
      lossProbability := fun _ _ => 0
      lossProbability_nonneg := fun _ _ => le_rfl
      lossProbability_lt_one := fun _ _ => zero_lt_one }
  let mMom₀ : SecondOrderMoments Unit 1 :=
    { rate := 1
      rate_pos := one_pos
      sender := ()
      host := fun _ => ()
      clock := fun _ => ClockNoise.zero
      txJitter := fun _ => ⟨0, fun _ => 0⟩
      rxJitter := fun _ => ⟨0, fun _ => 0⟩
      ownJitter := fun _ _ => ⟨0, fun _ _ => 0⟩
      capture := ClockNoise.zero
      playback := fun _ => ClockNoise.zero
      captureTimestampVariance := 0
      captureTimestampVariance_nonneg := le_rfl
      playbackTimestampVariance := fun _ => 0
      playbackTimestampVariance_nonneg := fun _ => le_rfl }
  let m : StochasticWorld Unit 1 :=
    { network := mNet₀
      moments := mMom₀
      handoff := 0
      handoff_nonneg := le_rfl
      leadLeast := 1 / 2
      leadMost := 1 / 2
      leadLeast_pos := by norm_num
      leadLeast_le := le_rfl
      blockLeast := 1
      blockMost := 1
      blockLeast_pos := one_pos
      blockLeast_le := le_rfl }
  have hclk_zero : ∀ t τ, secondDifference (fun t => (w₀.clock ()).read t - t) t τ = 0 := by
    intro t τ; simp [w₀, secondDifference]
  have hdev_cap : ∀ k j, gridDifference (devicePhase w₀.source.capture m.moments.rate) k j = 0 := by
    intro k j; simp [m, mMom₀, w₀, devicePhase, gridDifference]
  have hdev_spk : ∀ r k j, gridDifference (devicePhase (w₀.speaker r).out m.moments.rate) k j = 0 := by
    intro r k j; simp only [m, mMom₀, w₀, devicePhase, gridDifference]; push_cast; simp only [div_one]; ring
  refine ⟨m, P₀, fun _ => w₀, ?_⟩
  refine
    { links := ⟨d₀, ?_, ?_⟩
      handoff := fun _ b => by simp [m, w₀]
      lead := fun _ r b => by simp [m, w₀]; norm_num
      capture_blocks := fun _ b => by simp [m, w₀]
      playback_blocks := fun _ r b => by simp [m, w₀] }
  · exact
      { baseline_pos := fun _ _ _ _ => one_pos
        baseline_slow := fun _ _ _ _ _ => by simp [d₀, link, m, mNet₀]
        jitter_nonneg := fun _ _ _ _ _ => le_rfl
        jitter_near_zero := fun _ _ _ _ δ hδ => by simp [P₀, d₀, link, hδ]
        jitter_tail := fun _ _ _ _ x hx => by simp [P₀, d₀, link, not_lt.mpr hx]
        pause_length_pos := fun _ _ _ p hp => by simp [d₀, link] at hp
        paused_lt_one := fun _ _ _ => by simp [P₀, d₀, link, Link.Holds]
        outage_lt_one := fun _ _ _ => by simp [P₀, d₀, link, Link.Loses]
        pauses := fun _ _ _ _ _ _ _ _ => by simp [P₀, d₀, link, m, mNet₀]
        lost := fun _ _ _ => by simp [P₀, d₀, link, m, mNet₀]
        state_measurable := fun _ _ _ _ => measurable_const' fun _ _ => rfl
        lost_measurable := fun _ _ _ => by simp [d₀, link]
        states_stationary := fun τ => by simp only [hshift]
        states_mixing := fun A B _ _ => by simp only [hshift]; rw [hmix]; exact tendsto_const_nhds
        dropped_stationary := fun k => by simp only [hdrop]
        dropped_mixing := fun A B _ _ => by simp only [hdrop]; rw [hmix]; exact tendsto_const_nhds }
  · exact
      { prob := inferInstance
        network := fun _ _ _ _ _ => rfl
        rate_eq := fun _ => rfl
        sender_eq := fun _ => rfl
        host_eq := fun _ _ => rfl
        clocks := fun _ => ⟨fun _ _ => hmem _, fun t τ => by simp [hclk_zero],
          fun t₁ τ₁ t₂ τ₂ => by simp [m, mMom₀, hclk_zero, secondDifferenceCovariance_zero]⟩
        clocks_uncorrelated := fun i j hne => absurd (Subsingleton.elim i j) hne
        jitter := ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ _ _ => 0,
          fun _ _ _ _ _ => by simp [d₀, link],
          fun _ => ⟨fun _ => hmem _, fun _ => by simp [m, mMom₀], fun _ _ => by simp [m, mMom₀]⟩,
          fun _ => ⟨fun _ => hmem _, fun _ => by simp [m, mMom₀], fun _ _ => by simp [m, mMom₀]⟩,
          fun _ _ => ⟨fun _ _ => hmem _, fun _ _ => by simp [m, mMom₀], fun _ _ _ _ => by simp [m, mMom₀]⟩,
          fun _ _ _ _ _ _ => by simp,
          fun _ _ _ _ _ _ => by simp,
          fun _ _ _ _ _ _ _ _ _ => by simp,
          fun _ _ _ _ _ => by simp [hclk_zero],
          fun _ _ _ _ _ => by simp [hclk_zero],
          fun _ _ _ _ _ _ _ => by simp [hclk_zero],
          fun _ _ _ _ => by simp,
          fun _ _ _ _ => by simp,
          fun _ _ _ _ _ _ => by simp,
          fun _ _ _ _ _ => by simp,
          fun _ _ _ _ _ => by simp,
          fun _ _ _ _ _ _ _ => by simp,
          fun _ _ _ => by simp [w₀, captureError],
          fun _ _ _ => by simp [w₀, captureError],
          fun _ _ _ _ _ => by simp [w₀, captureError],
          fun _ _ _ _ => by simp [w₀, playbackError],
          fun _ _ _ _ => by simp [w₀, playbackError],
          fun _ _ _ _ _ _ => by simp [w₀, playbackError]⟩
        capture := ⟨fun _ _ => hmem _, fun k j => by simp [hdev_cap],
          fun k₁ j₁ k₂ j₂ => by simp [m, mMom₀, hdev_cap, secondDifferenceCovariance_zero]⟩
        playback := fun r => ⟨fun _ _ => hmem _, fun k j => by simp [hdev_spk],
          fun k₁ j₁ k₂ j₂ => by simp [m, mMom₀, hdev_spk, secondDifferenceCovariance_zero]⟩
        capture_clock_uncorrelated := fun i hne => absurd (Subsingleton.elim i _) hne
        playback_clock_uncorrelated := fun i r hne => absurd (Subsingleton.elim i _) hne
        capture_playback_uncorrelated := fun r hne => absurd (Subsingleton.elim _ _) hne
        playback_uncorrelated := fun r r' hne => absurd (Subsingleton.elim _ _) hne
        capture_timestamps := ⟨fun _ => hmem _, fun b => by simp [w₀, captureError],
          fun b b' => by simp [m, mMom₀, w₀, captureError]⟩
        playback_timestamps := fun r => ⟨fun _ => hmem _, fun b => by simp [w₀, playbackError],
          fun b b' => by simp [m, mMom₀, w₀, playbackError]⟩
        capture_playback_timestamps_uncorrelated := fun r b₁ b₂ => by simp [w₀, captureError]
        playback_timestamps_uncorrelated := fun r r' hne => absurd (Subsingleton.elim r r') hne
        clock_capture_timestamps_uncorrelated := fun i t τ b => by simp [hclk_zero]
        clock_playback_timestamps_uncorrelated := fun i r t τ b => by simp [hclk_zero]
        capture_device_capture_timestamps_uncorrelated := fun k j b => by simp [hdev_cap]
        capture_device_playback_timestamps_uncorrelated := fun r k j b => by simp [hdev_cap]
        playback_device_capture_timestamps_uncorrelated := fun r k j b => by simp [hdev_spk]
        playback_device_playback_timestamps_uncorrelated := fun r r' k j b => by simp [hdev_spk] }

end Further

/-! ## The generative model is not empty -/

section Example

open GenerativeWorld MeasureTheory ProbabilityTheory

/-- The example's model: three hosts, the sender and two speakers on their
own hosts, devices at one frame per second in blocks of one frame, a request
lead of half a second, a target latency of one second, and shape two. -/
private def exampleModel : GenerativeWorld (Fin 3) 2 where
  rate := 1
  rate_pos := one_pos
  sender := 0
  host := ![1, 2]
  device := id
  device_idem := fun _ => rfl
  device_host := fun _ => rfl
  shape := 2
  shape_pos := two_pos
  blockSize := 1
  blockSize_pos := one_pos
  lead := 1 / 2
  lead_pos := by norm_num
  targetLatency := 1
  targetLatency_nonneg := zero_le_one

/-- The example's member: round trips of one second, no pauses and no
wander. -/
private def exampleMember : Member (Fin 3) 2 where
  roundTrip := fun _ _ => 1
  roundTrip_pos := fun _ _ => one_pos
  roundTrip_symm := fun _ _ => rfl
  linkPauseRate := fun _ _ => 0
  linkPauseRate_nonneg := fun _ _ => le_rfl
  linkPauseLength := fun _ _ => Measure.dirac 1
  linkPauseLength_prob := fun _ _ => inferInstance
  linkPauseLength_pos := fun _ _ => by simp
  linkPauseLength_mean := fun _ _ => integrable_dirac eNorm_lt_top
  linkLoad_lt_one := fun _ _ => by simp
  hostPauseRate := fun _ => 0
  hostPauseRate_nonneg := fun _ => le_rfl
  hostPauseLength := fun _ => Measure.dirac 1
  hostPauseLength_prob := fun _ => inferInstance
  hostPauseLength_pos := fun _ => by simp
  hostPauseLength_mean := fun _ => integrable_dirac eNorm_lt_top
  hostLoad_lt_one := fun _ => by simp
  rateSpread := 1
  rateSpread_nonneg := zero_le_one
  wanderSize := fun _ => 0
  wanderSize_nonneg := fun _ => le_rfl
  wanderTime := fun _ => 1
  wanderTime_pos := fun _ => one_pos
  deviceWanderSize := fun _ => 0
  deviceWanderSize_nonneg := fun _ => le_rfl
  deviceWanderTime := fun _ => 1
  deviceWanderTime_pos := fun _ => one_pos
  reportSize := fun _ => 0
  reportSize_nonneg := fun _ => le_rfl
  reportTime := fun _ => 1
  reportTime_pos := fun _ => one_pos
  offsetRange := 1
  offsetRange_pos := one_pos
  captureStart := 0
  speakerStart := fun _ => 1

/-- The law of each coordinate of the example's probability space. -/
private def exampleLaw : Component (Fin 3) 2 → Measure ℝ
  | .split _ => betaMeasure 2 2
  | .offset _ => ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)
  | .logRate _ => gaussianReal 0 (Real.toNNReal ((1 : ℝ) ^ 2))
  | .wander _ => Measure.dirac 0
  | .linkPaused _ _ => Measure.dirac 0
  | .hostPaused _ => Measure.dirac 0
  | .deviceLogRate _ => gaussianReal 0 (Real.toNNReal ((1 : ℝ) ^ 2))
  | .deviceWander _ => Measure.dirac 0
  | .reportError _ => Measure.dirac 0

private instance (p : Component (Fin 3) 2) : IsProbabilityMeasure (exampleLaw p) := by
  cases p
  · exact isProbabilityMeasureBeta two_pos two_pos
  · exact cond_isProbabilityMeasure_of_finite (by rw [Real.volume_Icc]; norm_num)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  · exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 _))
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  · exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 _))
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))

/-- The pair of two distinct hosts. -/
private def examplePair (i j : Fin 3) (h : i ≠ j) : {z : Sym2 (Fin 3) // ¬ z.IsDiag} :=
  ⟨s(i, j), by simpa using h⟩

/-- The example's draw: the split of a pair, in the order of the hosts'
numbers, the offsets and the mean rates of the clocks of the hosts and of the
audio devices are coordinates of the probability space; there is no wander,
no pause and no error of a report. -/
private def exampleDraw (ω : Component (Fin 3) 2 → ℝ) : Draw (Fin 3) 2 where
  split := fun i j =>
    if h : i = j then 1 / 2
    else if i < j then splitOf (ω (.split (examplePair i j h)))
    else 1 - splitOf (ω (.split (examplePair i j h)))
  offset := fun h => ω (.offset h)
  logRate := fun h => ω (.logRate h)
  wander := fun _ _ => 0
  linkPaused := fun _ _ _ => 0
  hostPaused := fun _ _ => 0
  deviceLogRate := fun x => ω (.deviceLogRate x)
  deviceWander := fun _ _ => 0
  reportError := fun _ _ => 0

private theorem examplePair_swap {i j : Fin 3} (h : i ≠ j) :
    examplePair j i h.symm = examplePair i j h :=
  Subtype.ext Sym2.eq_swap

private theorem exampleDraw_split_mem (ω : Component (Fin 3) 2 → ℝ) (i j : Fin 3) :
    (exampleDraw ω).split i j ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [exampleDraw]
  split_ifs with h h'
  · constructor <;> norm_num
  · exact splitOf_mem _
  · have := splitOf_mem (ω (.split (examplePair i j h)))
    exact ⟨by linarith [this.2], by linarith [this.1]⟩

private theorem exampleDraw_split_swap (ω : Component (Fin 3) 2 → ℝ) (i j : Fin 3) :
    (exampleDraw ω).split i j + (exampleDraw ω).split j i = 1 := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hne : i ≠ j := hlt.ne
    simp only [exampleDraw, dite_eq_right hne, dite_eq_right hne.symm, ite_eq_left hlt,
      ite_eq_right hlt.not_gt, examplePair_swap hne]
    ring
  · subst heq
    simp only [exampleDraw]
    norm_num
  · have hne : i ≠ j := hgt.ne'
    simp only [exampleDraw, dite_eq_right hne, dite_eq_right hne.symm, ite_eq_left hgt,
      ite_eq_right hgt.not_gt, examplePair_swap hne]
    ring

private theorem exampleDraw_split_law {i j : Fin 3} (hij : i ≠ j) :
    HasLaw (fun ω => (exampleDraw ω).split i j) (betaMeasure 2 2) (Measure.pi exampleLaw) := by
  have hcoord : HasLaw (fun ω : Component (Fin 3) 2 → ℝ => ω (.split (examplePair i j hij)))
      (betaMeasure 2 2) (Measure.pi exampleLaw) :=
    (measurePreserving_eval exampleLaw (.split (examplePair i j hij))).hasLaw
  have hto : HasLaw splitOf (betaMeasure 2 2) (betaMeasure 2 2) :=
    HasLaw.id.congr (splitOf_ae_eq 2 2)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have heq : (fun ω => (exampleDraw ω).split i j)
        = fun ω => splitOf (ω (.split (examplePair i j hij))) := by
      funext ω
      simp only [exampleDraw, dite_eq_right hij, ite_eq_left hlt]
    rw [heq]
    exact hto.fun_comp hcoord
  · have heq : (fun ω => (exampleDraw ω).split i j)
        = fun ω => 1 - splitOf (ω (.split (examplePair i j hij))) := by
      funext ω
      simp only [exampleDraw, dite_eq_right hij, ite_eq_right hgt.not_gt]
    rw [heq]
    have hsub : HasLaw (fun x : ℝ => 1 - x) (betaMeasure 2 2) (betaMeasure 2 2) :=
      ⟨by fun_prop, betaMeasure_map_one_sub 2⟩
    exact hsub.fun_comp (hto.fun_comp hcoord)

/-- How each component of the example's draw depends on its coordinate. -/
private def exampleComponentMap (o : Orientation (Fin 3)) : (p : Component (Fin 3) 2) → ℝ → p.Val
  | .split z => fun u => if (o z).1.1 < (o z).1.2 then splitOf u else 1 - splitOf u
  | .offset _ => fun u => u
  | .logRate _ => fun u => u
  | .wander _ => fun _ _ => 0
  | .linkPaused _ _ => fun _ _ => 0
  | .hostPaused _ => fun _ _ => 0
  | .deviceLogRate _ => fun u => u
  | .deviceWander _ => fun _ _ => 0
  | .reportError _ => fun _ _ => 0

private theorem measurable_exampleComponentMap (o : Orientation (Fin 3)) (p : Component (Fin 3) 2) :
    Measurable (exampleComponentMap o p) := by
  cases p with
  | split z =>
    exact Measurable.ite (MeasurableSet.const _) measurable_splitOf (measurable_splitOf.const_sub 1)
  | offset h => exact measurable_id
  | logRate h => exact measurable_id
  | wander h => exact measurable_const
  | linkPaused i j => exact measurable_const
  | hostPaused h => exact measurable_const
  | deviceLogRate x => exact measurable_id
  | deviceWander x => exact measurable_const
  | reportError x => exact measurable_const

private theorem exampleDraw_component (o : Orientation (Fin 3)) (p : Component (Fin 3) 2)
    (ω : Component (Fin 3) 2 → ℝ) :
    (exampleDraw ω).component o p = exampleComponentMap o p (ω p) := by
  cases p with
  | split z =>
    have hz : s((o z).1.1, (o z).1.2) = z.1 := (o z).2
    have hne : (o z).1.1 ≠ (o z).1.2 := by
      intro h
      apply z.2
      rw [← hz]
      exact Sym2.mk_isDiag_iff.mpr h
    have hpair : examplePair (o z).1.1 (o z).1.2 hne = z := Subtype.ext hz
    simp only [Draw.component, exampleComponentMap, exampleDraw, dite_eq_right hne, hpair]
    rfl
  | offset h => rfl
  | logRate h => rfl
  | wander h => rfl
  | linkPaused i j => rfl
  | hostPaused h => rfl
  | deviceLogRate x => rfl
  | deviceWander x => rfl
  | reportError x => rfl

/-- The example's world: the one built from the example's draw. Each device
starts when the clock of its host reads the member's start and then runs at
the rate of its own clock. -/
private def exampleWorld (ω : Component (Fin 3) 2 → ℝ) : World (Fin 3) 2 where
  rate := 1
  rate_pos := one_pos
  sender := 0
  host := ![1, 2]
  hosts := fun h => by
    fin_cases h
    · exact Or.inl rfl
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
  clock := fun h =>
    { read := fun t => ω (.offset h) + Real.exp (ω (.logRate h)) * t
      strictMono := fun a b hab => by
        have := mul_lt_mul_of_pos_left hab (Real.exp_pos (ω (.logRate h)))
        linarith
      continuous := by fun_prop }
  source :=
    { capture := fun n =>
        -ω (.offset 0) * Real.exp (-ω (.logRate 0))
          + (n : ℝ) * Real.exp (-ω (.deviceLogRate none))
      capture_strictMono := fun a b hab => by
        have hab' : (a : ℝ) < b := Nat.cast_lt.mpr hab
        have := mul_lt_mul_of_pos_right hab' (Real.exp_pos (-ω (.deviceLogRate none)))
        linarith
      first := id
      first_zero := rfl
      first_strictMono := strictMono_id
      handed := fun b =>
        -ω (.offset 0) * Real.exp (-ω (.logRate 0))
          + (b : ℝ) * Real.exp (-ω (.deviceLogRate none))
      handed_strictMono := fun a b hab => by
        have hab' : (a : ℝ) < b := Nat.cast_lt.mpr hab
        have := mul_lt_mul_of_pos_right hab' (Real.exp_pos (-ω (.deviceLogRate none)))
        linarith
      handed_after := fun b => by simp
      reported := fun b =>
        (b : ℝ) * Real.exp (ω (.logRate 0)) * Real.exp (-ω (.deviceLogRate none)) }
  speaker := fun r =>
    { out := fun k =>
        (1 - ω (.offset (![1, 2] r))) * Real.exp (-ω (.logRate (![1, 2] r)))
          + (k : ℝ) * Real.exp (-ω (.deviceLogRate (some r)))
      out_strictMono := fun a b hab => by
        have hab' : (a : ℝ) < b := Nat.cast_lt.mpr hab
        have := mul_lt_mul_of_pos_right hab' (Real.exp_pos (-ω (.deviceLogRate (some r))))
        linarith
      first := id
      first_zero := rfl
      first_strictMono := strictMono_id
      asked := fun b =>
        (1 - ω (.offset (![1, 2] r))) * Real.exp (-ω (.logRate (![1, 2] r)))
          + ((b : ℝ) - 1 / 2) * Real.exp (-ω (.deviceLogRate (some r)))
      asked_strictMono := fun a b hab => by
        have hab' : (a : ℝ) < b := Nat.cast_lt.mpr hab
        have := mul_lt_mul_of_pos_right hab' (Real.exp_pos (-ω (.deviceLogRate (some r))))
        linarith
      asked_before := fun b => by
        have := Real.exp_pos (-ω (.deviceLogRate (some r)))
        simp only [id]
        linarith
      reported := fun b =>
        1 + (b : ℝ) * Real.exp (ω (.logRate (![1, 2] r)))
          * Real.exp (-ω (.deviceLogRate (some r))) }
  network :=
    { deliver := fun i j s _ => some (s + (exampleDraw ω).split i j * 1 + 0)
      after := fun i j s _ a h => by
        simp only [Option.some.injEq] at h
        have := (exampleDraw_split_mem ω i j).1
        linarith }
  target := fun _ => 1

private theorem exp_mul_exp_neg (c : ℝ) : Real.exp c * Real.exp (-c) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- In the example, the clock of an audio device advances at a constant
rate. -/
private theorem exampleDeviceReading (ω : Component (Fin 3) 2 → ℝ) (x : Option (Fin 2))
    (t : Time) :
    (exampleDraw ω).deviceReading x t = Real.exp (ω (.deviceLogRate x)) * t := by
  simp only [Draw.deviceReading, exampleDraw, add_zero, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  ring

private theorem exampleWorld_builds (ω : Component (Fin 3) 2 → ℝ) :
    exampleModel.Builds exampleMember (exampleDraw ω) (exampleWorld ω) where
  rate_eq := rfl
  sender_eq := rfl
  host_eq := rfl
  clock := fun h t => by
    simp only [exampleWorld, Draw.reading, exampleDraw, add_zero, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
    ring
  network := fun i j s q => by
    have hzero : ∀ t : Time, IsBacklog (fun _ : Time => (0 : ℝ)) t 0 := fun t =>
      isBacklog_zero_of_const (fun _ _ => rfl) t
    refine ⟨0, 0, 0, hzero _, hzero _, hzero _, ?_⟩
    change some (s + (exampleDraw ω).split i j * 1 + 0)
      = some (s + 0 + (exampleDraw ω).split i j * 1 + 0 + 0)
    congr 1
    ring
  deviceClock := fun x =>
    ⟨{ read := fun t => Real.exp (ω (.deviceLogRate x)) * t
       strictMono := fun a b hab => mul_lt_mul_of_pos_left hab (Real.exp_pos _)
       continuous := by fun_prop }, fun t => (exampleDeviceReading ω x t).symm⟩
  capture_start := by
    have h := exp_mul_exp_neg (ω (.logRate 0))
    change ω (.offset 0) + Real.exp (ω (.logRate 0))
        * (-ω (.offset 0) * Real.exp (-ω (.logRate 0))
          + ((0 : ℕ) : ℝ) * Real.exp (-ω (.deviceLogRate none))) = 0
    push_cast
    linear_combination (-ω (.offset 0)) * h
  capture := fun n => by
    have hg := exp_mul_exp_neg (ω (.deviceLogRate none))
    rw [exampleDeviceReading, exampleDeviceReading]
    change Real.exp (ω (.deviceLogRate none))
          * (-ω (.offset 0) * Real.exp (-ω (.logRate 0))
            + (n : ℝ) * Real.exp (-ω (.deviceLogRate none)))
        - Real.exp (ω (.deviceLogRate none))
          * (-ω (.offset 0) * Real.exp (-ω (.logRate 0))
            + ((0 : ℕ) : ℝ) * Real.exp (-ω (.deviceLogRate none)))
      = (n : ℝ) / 1
    push_cast
    linear_combination (n : ℝ) * hg
  capture_first := fun b => by simp [exampleWorld, exampleModel]
  capture_handed := fun b => by simp [exampleWorld]
  capture_reported := fun b => by
    have h := exp_mul_exp_neg (ω (.logRate 0))
    change (b : ℝ) * Real.exp (ω (.logRate 0)) * Real.exp (-ω (.deviceLogRate none))
      = ω (.offset 0) + Real.exp (ω (.logRate 0))
          * (-ω (.offset 0) * Real.exp (-ω (.logRate 0))
            + (b : ℝ) * Real.exp (-ω (.deviceLogRate none))) + 0
    linear_combination (ω (.offset 0)) * h
  speaker_start := fun r => by
    have h := exp_mul_exp_neg (ω (.logRate (![1, 2] r)))
    change ω (.offset (![1, 2] r)) + Real.exp (ω (.logRate (![1, 2] r)))
        * ((1 - ω (.offset (![1, 2] r))) * Real.exp (-ω (.logRate (![1, 2] r)))
          + ((0 : ℕ) : ℝ) * Real.exp (-ω (.deviceLogRate (some r)))) = 1
    push_cast
    linear_combination (1 - ω (.offset (![1, 2] r))) * h
  speaker_out := fun r k => by
    have hg := exp_mul_exp_neg (ω (.deviceLogRate (some r)))
    change (exampleDraw ω).deviceReading (some r)
          ((1 - ω (.offset (![1, 2] r))) * Real.exp (-ω (.logRate (![1, 2] r)))
            + (k : ℝ) * Real.exp (-ω (.deviceLogRate (some r))))
        - (exampleDraw ω).deviceReading (some r)
          ((1 - ω (.offset (![1, 2] r))) * Real.exp (-ω (.logRate (![1, 2] r)))
            + ((0 : ℕ) : ℝ) * Real.exp (-ω (.deviceLogRate (some r))))
      = (k : ℝ) / 1
    rw [exampleDeviceReading, exampleDeviceReading]
    push_cast
    linear_combination (k : ℝ) * hg
  speaker_first := fun r b => by simp [exampleWorld, exampleModel]
  speaker_asked := fun r b => by
    have hg := exp_mul_exp_neg (ω (.deviceLogRate (some r)))
    change (exampleDraw ω).deviceReading (some r)
          ((1 - ω (.offset (![1, 2] r))) * Real.exp (-ω (.logRate (![1, 2] r)))
            + (b : ℝ) * Real.exp (-ω (.deviceLogRate (some r))))
        - (exampleDraw ω).deviceReading (some r)
          ((1 - ω (.offset (![1, 2] r))) * Real.exp (-ω (.logRate (![1, 2] r)))
            + ((b : ℝ) - 1 / 2) * Real.exp (-ω (.deviceLogRate (some r))))
      = 1 / 2
    rw [exampleDeviceReading, exampleDeviceReading]
    linear_combination (1 / 2 : ℝ) * hg
  speaker_reported := fun r b => by
    have h := exp_mul_exp_neg (ω (.logRate (![1, 2] r)))
    change 1 + (b : ℝ) * Real.exp (ω (.logRate (![1, 2] r)))
          * Real.exp (-ω (.deviceLogRate (some r)))
      = ω (.offset (![1, 2] r)) + Real.exp (ω (.logRate (![1, 2] r)))
          * ((1 - ω (.offset (![1, 2] r))) * Real.exp (-ω (.logRate (![1, 2] r)))
            + (b : ℝ) * Real.exp (-ω (.deviceLogRate (some r)))) + 0
    linear_combination (-(1 - ω (.offset (![1, 2] r)))) * h
  target_eq := fun _ => rfl

private theorem exampleDraw_prior :
    exampleModel.Prior exampleMember (Measure.pi exampleLaw) exampleDraw where
  prob := inferInstance
  split_swap := exampleDraw_split_swap
  split_mem := exampleDraw_split_mem
  split_law := fun i j hij => exampleDraw_split_law hij
  offset_law := fun h => (measurePreserving_eval exampleLaw (.offset h)).hasLaw
  logRate_law := fun h => (measurePreserving_eval exampleLaw (.logRate h)).hasLaw
  wander_gaussian := fun _ => isGaussianProcess_zero _
  wander_mean := fun _ _ => by simp [exampleDraw]
  wander_covariance := fun _ _ _ => by
    simp only [exampleDraw, exampleMember]
    rw [covariance_const_left]
    simp
  wander_continuous := fun _ _ => continuous_const
  deviceLogRate_law := fun x =>
    (measurePreserving_eval exampleLaw (.deviceLogRate x)).hasLaw
  deviceWander_gaussian := fun _ => isGaussianProcess_zero _
  deviceWander_mean := fun _ _ => by simp [exampleDraw]
  deviceWander_covariance := fun _ _ _ => by
    simp only [exampleDraw, exampleMember]
    rw [covariance_const_left]
    simp
  deviceWander_continuous := fun _ _ => continuous_const
  reportError_gaussian := fun _ => isGaussianProcess_zero _
  reportError_mean := fun _ _ => by simp [exampleDraw]
  reportError_covariance := fun _ _ _ => by
    simp only [exampleDraw, exampleMember]
    rw [covariance_const_left]
    simp
  reportError_continuous := fun _ _ => continuous_const
  linkPaused_monotone := fun _ _ _ => monotone_const
  linkPaused_zero := fun _ _ _ => rfl
  linkPaused_rightContinuous := fun _ _ _ _ => continuousWithinAt_const
  linkPaused_increments := fun _ _ _ _ _ => iIndepFun_of_const _ fun _ => (0 : ℝ) - 0
  linkPaused_law := fun i j s t _ => by
    have h0 : Real.toNNReal (exampleMember.linkPauseRate i j * (t - s)) = 0 := by
      simp [exampleMember]
    rw [h0, pauseLaw_zero]
    change HasLaw (fun _ => (0 : ℝ) - 0) (Measure.dirac 0) _
    exact ⟨aemeasurable_const, by simp [Measure.map_const]⟩
  hostPaused_monotone := fun _ _ => monotone_const
  hostPaused_zero := fun _ _ => rfl
  hostPaused_rightContinuous := fun _ _ _ => continuousWithinAt_const
  hostPaused_increments := fun _ _ _ _ => iIndepFun_of_const _ fun _ => (0 : ℝ) - 0
  hostPaused_law := fun h s t _ => by
    have h0 : Real.toNNReal (exampleMember.hostPauseRate h * (t - s)) = 0 := by
      simp [exampleMember]
    rw [h0, pauseLaw_zero]
    change HasLaw (fun _ => (0 : ℝ) - 0) (Measure.dirac 0) _
    exact ⟨aemeasurable_const, by simp [Measure.map_const]⟩
  independent := fun o => by
    have h : (fun p ω => (exampleDraw ω).component o p)
        = fun p (ω : Component (Fin 3) 2 → ℝ) => exampleComponentMap o p (ω p) := by
      funext p ω
      exact exampleDraw_component o p ω
    rw [h]
    exact iIndepFun_pi fun p => (measurable_exampleComponentMap o p).aemeasurable

/-- **The generative model is not empty.** There is a random world of the
model with three hosts and two speakers. In it the splits, the clock offsets
and the clocks' mean rates are random; its member has no pauses and no
wander, so this does not show that members with either exist. -/
theorem GenerativeWorld.example_holds :
    ∃ (m : GenerativeWorld (Fin 3) 2) (f : GenerativeWorld.Member (Fin 3) 2) (Ω : Type)
      (_ : MeasurableSpace Ω) (P : Measure Ω) (world : Ω → World (Fin 3) 2),
      m.Holds f P world ∧ (∀ i j, f.linkPauseRate i j = 0) ∧ (∀ h, f.hostPauseRate h = 0)
        ∧ ∀ h, f.wanderSize h = 0 :=
  ⟨exampleModel, exampleMember, Component (Fin 3) 2 → ℝ, inferInstance, Measure.pi exampleLaw,
    exampleWorld, ⟨exampleDraw, exampleDraw_prior, exampleWorld_builds⟩,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

end Example

end Unisono.Spec
