/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Objectives
public import Unisono.Spec.Models.Bounded
public import Unisono.Spec.Models.Delays
public import Unisono.Spec.Models.SecondOrder
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
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
  `DelayModel.example_holds`, `SecondOrderModel.example_holds`).
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

/-- Every pending event of a state occurs at true time `t` or later. -/
def DueFrom (t : Time) : Prop :=
  t ≤ w.source.handed st.handedNext ∧ (∀ r, t ≤ (w.speaker r).asked (st.askedNext r))
    ∧ (∀ m ∈ st.inFlight, t ≤ m.arrival) ∧ (∀ u ∈ st.timers, t ≤ u.time)

theorem DueFrom.le_key {st : State H R Msg} {t : Time} (h : st.DueFrom w t) {e : Due R}
    (he : e ∈ st.due) : t ≤ (st.key w e).1 := by
  rcases st.mem_due he with rfl | ⟨r, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact h.1
  · exact h.2.1 r
  · simp only [key, List.getElem?_eq_getElem hp, Option.map_some, Option.getD_some]
    exact h.2.2.1 _ (List.getElem_mem hp)
  · simp only [key, List.getElem?_eq_getElem hp, Option.map_some, Option.getD_some]
    exact h.2.2.2 _ (List.getElem_mem hp)

theorem dueFrom_of_le_key {t : Time} (h : ∀ e ∈ st.due, t ≤ (st.key w e).1) :
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

/-- **The probabilistic network model is not empty**: a network of one host
whose link to itself has a constant baseline of one second, no jitter, no
pauses and no losses follows the model with zero rates. -/
theorem DelayModel.example_holds : ∃ (m : DelayModel) (P : Measure Unit)
    (d : Unit → Unit → Unit → Link), IsProbabilityMeasure P ∧ m.Holds P d := by
  let link : Link := ⟨fun _ => 1, fun _ => 0, ∅, ∅⟩
  let d : Unit → Unit → Unit → Link := fun _ _ _ => link
  have hstate : ∀ u, link.state u = (0, false, false) := by
    intro u
    simp [Link.state, Link.Holds, Link.Loses, link]
  have hshift : ∀ τ ω, shiftTime τ (linkStates d ω) = linkStates d ω := by
    intro τ ω
    funext i j u
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
    { slope := 0
      slope_nonneg := le_rfl
      tailFactor := 1
      tailFactor_pos := one_pos
      tailScale := 1
      tailScale_pos := one_pos
      pauseRate := fun _ => 0
      pauseRate_nonneg := fun _ => le_rfl
      pauseLength := fun _ => Measure.dirac 1
      pauseLength_probability := fun _ => inferInstance
      pauseLength_pos := fun _ => by simp [Measure.dirac_apply']
      pauseLength_mean := fun _ => by
        rw [lintegral_dirac]
        exact ENNReal.ofReal_lt_top
      lossProbability := 0
      lossProbability_nonneg := le_rfl
      lossProbability_lt_one := zero_lt_one },
    Measure.dirac (), d, inferInstance, ?_⟩
  refine
    { baseline_pos := fun _ _ _ _ => one_pos
      baseline_slow := fun _ _ _ _ _ => by simp [d, link]
      jitter_nonneg := fun _ _ _ _ => le_rfl
      jitter_near_zero := fun _ _ _ δ hδ => by simp [d, link, hδ]
      jitter_tail := fun _ _ _ x hx => by simp [d, link, not_lt.mpr hx]
      pause_length_pos := fun _ _ _ p hp => by simp [d, link] at hp
      paused_lt_one := fun _ _ _ => by simp [d, link, Link.Holds]
      outage_lt_one := fun _ _ _ => by simp [d, link, Link.Loses]
      pauses := fun _ _ _ _ _ _ _ _ => by simp [d, link]
      lost := fun _ _ _ => by simp [d, link]
      state_measurable := fun _ _ _ => measurable_const' fun _ _ => rfl
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

/-- **The second-order model is not empty**: a 3-host star (sender `0`, speakers
on hosts `1` and `2`) over a uniform probability space on `Bool × Bool`, with
nonzero uncorrelated link jitter of variance `1` on links `(0, 1)` and `(0, 2)`
and zero clock, device, and timestamp noise, satisfies `SecondOrderModel.Holds`.
Satisfiability with nonzero `ClockNoise` remains open because Gaussian
realizations of white or random-walk frequency noise do not yield globally
monotone `Clock` paths. -/
theorem SecondOrderModel.example_holds : ∃ (m : SecondOrderModel (Fin 3) 2)
    (P : Measure (Bool × Bool)) (world : Bool × Bool → World (Fin 3) 2)
    (d : Bool × Bool → Fin 3 → Fin 3 → Link),
    m.Holds P world d ∧
      m.ownJitter 0 1 = ⟨1, fun _ => 1⟩ ∧ m.ownJitter 0 2 = ⟨1, fun _ => 1⟩ := by
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
  let own : Bool × Bool → Fin 3 → Fin 3 → Time → ℝ := fun ω i j _ =>
    if i = 0 ∧ j = 1 then 1 + s1 ω else if i = 0 ∧ j = 2 then 1 + s2 ω else 0
  have hown_nonneg : ∀ ω i j u, 0 ≤ own ω i j u := by
    intro ω i j u
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
  let ownJ : Fin 3 → Fin 3 → JitterNoise := fun i j =>
    if i = 0 ∧ j = 1 then ⟨1, fun _ => 1⟩
    else if i = 0 ∧ j = 2 then ⟨1, fun _ => 1⟩
    else ⟨0, fun _ => 0⟩
  let m : SecondOrderModel (Fin 3) 2 :=
    { rate := 1
      rate_pos := one_pos
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
      clocks := fun i => ⟨fun _ _ => hmemLp _, fun t τ => by simp [hclk_zero],
        fun t₁ τ₁ t₂ τ₂ => by simp [m, hclk_zero, secondDifferenceCovariance_zero]⟩
      clocks_uncorrelated := fun i j _ t₁ τ₁ t₂ τ₂ => by simp [hclk_zero]
      jitter := ⟨fun _ _ _ => 0, fun _ _ _ => 0, own,
        fun ω i j u => by simp [d],
        fun _ => ⟨fun _ => hmemLp _, fun _ => by simp [m], fun _ _ => by simp [m]⟩,
        fun _ => ⟨fun _ => hmemLp _, fun _ => by simp [m], fun _ _ => by simp [m]⟩,
        fun i j => ⟨fun _ => hmemLp _, fun s => by
            rw [hint]
            by_cases h1 : i = 0 ∧ j = 1
            · simp [m, ownJ, own, s1, h1]; norm_num
            · by_cases h2 : i = 0 ∧ j = 2
              · simp [m, ownJ, own, s2, h2]; norm_num
              · simp [m, ownJ, own, h1, h2],
          fun s u => by
            rw [hint]
            by_cases h1 : i = 0 ∧ j = 1
            · simp [m, ownJ, own, s1, h1]; norm_num
            · by_cases h2 : i = 0 ∧ j = 2
              · simp [m, ownJ, own, s2, h2]; norm_num
              · simp [m, ownJ, own, h1, h2]⟩,
        fun _ _ _ _ _ => by simp,
        fun _ _ _ _ _ => by simp,
        fun _ _ _ _ _ => by simp,
        fun _ _ _ _ _ => by simp,
        fun i j i' j' hne s u => by
          have hzero_left : ∀ a b : Fin 3, ¬(a = 0 ∧ b = 1) → ¬(a = 0 ∧ b = 2) →
              ∀ ω t, own ω a b t = 0 := fun a b h1 h2 ω t => by simp [own, h1, h2]
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
        fun _ _ _ _ _ _ => by simp [hclk_zero],
        fun _ _ _ _ => by simp [hdev_cap],
        fun _ _ _ _ => by simp [hdev_cap],
        fun _ _ _ _ _ => by simp [hdev_cap],
        fun _ _ _ _ _ => by simp [hdev_spk],
        fun _ _ _ _ _ => by simp [hdev_spk],
        fun _ _ _ _ _ _ => by simp [hdev_spk],
        fun _ _ _ => by simp [world, captureError],
        fun _ _ _ => by simp [world, captureError],
        fun _ _ _ _ => by simp [world, captureError],
        fun _ _ _ _ => by simp [world, playbackError],
        fun _ _ _ _ => by simp [world, playbackError],
        fun _ _ _ _ _ => by simp [world, playbackError]⟩
      capture := ⟨fun _ _ => hmemLp _, fun k j => by simp [hdev_cap],
        fun k₁ j₁ k₂ j₂ => by simp [m, hdev_cap, secondDifferenceCovariance_zero]⟩
      playback := fun r => ⟨fun _ _ => hmemLp _, fun k j => by simp [hdev_spk],
        fun k₁ j₁ k₂ j₂ => by simp [m, hdev_spk, secondDifferenceCovariance_zero]⟩
      capture_clock_uncorrelated := fun i t τ k j => by simp [hclk_zero]
      playback_clock_uncorrelated := fun i r t τ k j => by simp [hclk_zero]
      capture_playback_uncorrelated := fun r k₁ j₁ k₂ j₂ => by simp [hdev_cap]
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

end Further

end Unisono.Spec
