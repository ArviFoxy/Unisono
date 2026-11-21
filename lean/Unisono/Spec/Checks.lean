/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Objectives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Checks of the definitions

Statements that say, about small cases, what the definitions of the
objectives say in words. They are not results about the problem; they are
there so that a definition that does not mean what its description says
fails here.

* The speed is one less how fast the latency changes (`speed_eq`).
* Missed samples: an output sample that plays anything but the source
  counts one (`missedAt_none`); playback that goes on counts nothing
  (`missedAt_continues`); a jump forward over `J` frames counts `J`
  (`missedAt_skip`); playing `J` frames again counts `J`
  (`missedAt_repeat`); after `g` output samples that played something
  else, which count `g`, content that goes on as if they had played counts
  nothing more (`missedAt_after_gap`), and content that resumes where it
  stopped counts nothing more either (`missedAt_resume`).
* The synchronisation cost of a frame, when every speaker plays it, is the
  variance of the times at which they play it (`sum_pairs_eq`).
* The run meets events in the order of true time
  (`Solution.eventTime_le_succ`), and a run that gets past every moment
  decides what every output sample plays (`Solution.decided`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal

variable {H : Type} {R : ℕ}

/-! ## Speed -/

/-- **The speed is one less how fast the latency changes.** Over a step of
the playback that goes on, the speed is one less the change of the latency,
the time an output sample leaves less the time its content was captured,
divided by the time between the two output samples. -/
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

/-- The missed samples counted at output sample `k`, which plays content `y`,
when the last output sample before it that played the source is `j`, which
played content `x`. -/
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

/-- Playback that goes on from one output sample to the next counts no missed
sample. -/
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

/-- After `g` output samples that played something else, which count `g`
missed samples, content that goes on as if they had played the source
counts no more. -/
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

/-- After `g` output samples that played something else, which count `g`
missed samples, content that resumes where it stopped counts no more. -/
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

/-! ## Synchronisation -/

/-- **The pairs and the variance.** The squares of the differences between the
times `t r` of `R` speakers, over all pairs, add up to `R` times the sum of
the squares of their distances from the mean: divided by `R ^ 2`, the
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

/-- The first of a list by `earliest` is in the list, and comes no later than
any other. -/
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

theorem wake_mem_due {p : ℕ} (hp : p < st.wakes.length) : Due.wake p ∈ st.due := by
  simp [due, hp]

theorem mem_due {e : Due R} (he : e ∈ st.due) :
    e = .handed st.handedNext ∨ (∃ r, e = .asked r (st.askedNext r))
      ∨ (∃ p < st.inFlight.length, e = .arrival p) ∨ (∃ p < st.wakes.length, e = .wake p) := by
  simp [due] at he
  rcases he with rfl | ⟨r, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨r, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, hp, rfl⟩))

/-- Every event that is due in a state comes at true time `t` or later. -/
def DueFrom (t : Time) : Prop :=
  t ≤ w.source.handed st.handedNext ∧ (∀ r, t ≤ (w.speaker r).asked (st.askedNext r))
    ∧ (∀ m ∈ st.inFlight, t ≤ m.arrival) ∧ (∀ u ∈ st.wakes, t ≤ u.time)

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
    simpa [key, List.getElem?_eq_getElem hp] using h _ (st.wake_mem_due hp)

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

theorem sendAll_wakes (h : H) (t : Time) (held : Finset ℕ)
    (sends : List (H × Msg × Finset ℕ)) :
    (st.sendAll w h t held sends).wakes = st.wakes := by
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

/-- A host that meets an event at true time `t` adds only events after `t`:
the messages it sends arrive after `t`, and the wake-ups it asks for come
after `t`. -/
theorem meet_dueFrom (σ : Solution H R Msg) (lookahead : ℕ+) {h : H} {t : Time}
    {obs : Observation H R Msg} (hst : st.DueFrom w t) :
    (st.meet σ w lookahead h t obs).DueFrom w t := by
  obtain ⟨h1, h2, h3, h4⟩ := hst
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [meet, sendAll_handedNext]
    exact h1
  · intro r
    simp only [meet, sendAll_askedNext]
    exact h2 r
  · intro m hm
    simp only [meet] at hm
    exact sendAll_inFlight w _ le_rfl _ _ (by exact h3) m hm
  · intro u hu
    simp only [meet, sendAll_wakes, List.mem_append, List.mem_filterMap] at hu
    rcases hu with hu | ⟨c, _, hc⟩
    · exact h4 u hu
    · split_ifs at hc with hlt
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hc
      have hread := Clock.read_timeAt hv
      exact ((w.clock h).strictMono.lt_iff_lt.mp (hread ▸ hlt)).le

/-- After the earliest event that is due is met, every event that is due
comes no earlier than it. -/
theorem step_dueFrom (σ : Solution H R Msg) (lookahead : ℕ+) {e : Due R}
    (he : earliest (st.key w) st.due = some e) (hst : st.DueFrom w (st.key w e).1) :
    (st.step σ w lookahead).DueFrom w (st.key w e).1 := by
  have hmem := (earliest_spec _ _ _ he).1
  unfold State.step
  rw [he]
  rcases st.mem_due hmem with rfl | ⟨r, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · have hm := st.meet_dueFrom w σ lookahead (h := w.sender)
      (obs := .handed (w.source.block st.handedNext)) hst
    exact ⟨(w.source.handed_strictMono (Nat.lt_succ_self _)).le, hm.2.1, hm.2.2.1, hm.2.2.2⟩
  · have hm := st.meet_dueFrom w σ lookahead (h := w.host r)
      (obs := .asked r ((w.speaker r).block (st.askedNext r))) hst
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
    apply meet_dueFrom
    exact ⟨hst.1, hst.2.1, fun m hm => hst.2.2.1 m (List.mem_of_mem_eraseIdx hm), hst.2.2.2⟩
  · simp only [List.getElem?_eq_getElem hp]
    have hkey : (st.key w (.wake p)).1 = st.wakes[p].time := by
      simp [key, List.getElem?_eq_getElem hp]
    rw [hkey] at hst ⊢
    apply meet_dueFrom
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

/-- **The run meets events in the order of true time.** -/
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

/-- A request of a device that comes before the event of step `n` has been
met by then. -/
theorem Solution.lt_askedNext (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    {n : ℕ} {r : Fin R} {b : ℕ} (h : (w.speaker r).asked b < σ.eventTime w lookahead n) :
    b < (σ.states w lookahead n).askedNext r := by
  by_contra hle
  have h1 := (w.speaker r).asked_strictMono.monotone (not_lt.mp hle)
  have h2 := σ.eventTime_le_asked w lookahead n r
  linarith

/-- **A run that gets past every moment decides every output sample.** When
the run's events go beyond any true time, every request of every device is
met, so each output sample plays what the solution decided at its request
(`Solution.plays`). -/
theorem Solution.decided (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)
    (hgo : ∀ T, ∃ n, T < σ.eventTime w lookahead n) (r : Fin R) (k : ℕ) :
    ∃ n, k < (w.speaker r).first ((σ.states w lookahead n).askedNext r) := by
  obtain ⟨n, hn⟩ := hgo ((w.speaker r).asked k)
  exact ⟨n, (σ.lt_askedNext w lookahead hn).trans_le
    ((w.speaker r).first_strictMono.id_le _)⟩

end Run

end Unisono.Spec
