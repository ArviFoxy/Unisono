/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.MissingSamples

/-!
# Frames that a playback never plays

A playback can leave frames of the source unplayed: it jumps over them, or
it resumes beyond them after output samples that play nothing. The
objectives that are charged per frame (synchronization, latency, tracking)
charge nothing for a frame at a speaker that does not play it. This file
shows that the missed samples pay for such frames, when the position
advances by at least `s > 0` frames in every step of continuous playback.

For the playback of one speaker:

* a step that is not continuous counts at least one missed sample, at its
  own output sample or at the next one (`one_le_missedAt_add`), so the steps
  that are not continuous number at most twice the missed samples
  (`le_continuousBefore_add`);
* the position of the last output sample that plays the source is at least
  `s` times the number of continuous steps, minus the missed samples counted
  so far (`le_lastPlayed`);
* the frames at or below that position that no step so far has passed number
  at most a constant plus three times the missed samples counted so far
  (`card_unpassed_le`). The constant, `firstFrames`, counts the frames up to
  the first position played.

Together (`neverPlayed_le_of_missed`): among the first `N` frames, those that the
playback never plays number at most `firstFrames` plus three times the
missed samples counted at the first `K + 1` output samples, whenever
`N ≤ s * K - 3 * missed`.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {plays : ℕ → Option ℝ}

/-! ## The quantities -/

/-- The playback plays frame `n`: some step of continuous playback passes
it. -/
def PlaysFrame (plays : ℕ → Option ℝ) (n : ℕ) : Prop :=
  ∃ k, Covers plays k n

/-- The number of frames among the first `N` that the playback never
plays. -/
def neverPlayed (plays : ℕ → Option ℝ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun n => ¬ PlaysFrame plays n).card

/-- The missed samples counted at the output samples before `K`. -/
def missedBefore (plays : ℕ → Option ℝ) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K, missedAt plays k

/-- The position played by the last output sample before `K` that plays the
source, if there is one. -/
def lastPlayed (plays : ℕ → Option ℝ) : ℕ → Option ℝ
  | 0 => none
  | K + 1 =>
      match plays K with
      | some x => some x
      | none => lastPlayed plays K

/-- The number of steps of continuous playback among the steps that start at
an output sample before `K`. -/
def continuousBefore (plays : ℕ → Option ℝ) (K : ℕ) : ℕ := by
  classical
  exact ((Finset.range K).filter fun k => PlaysContinuously plays k).card

/-- Some step of continuous playback between two output samples before `K`
passes frame `n`. -/
def PassedBefore (plays : ℕ → Option ℝ) (K n : ℕ) : Prop :=
  ∃ k, k + 1 < K ∧ Covers plays k n

/-- The frames at or below the position `x` that no step of continuous
playback between two output samples before `K` passes. -/
def unpassed (plays : ℕ → Option ℝ) (K : ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊x⌋₊ + 1)).filter fun n => ¬ PassedBefore plays K n

/-- The number of frames up to the first position that the playback plays;
zero if it never plays the source. -/
def firstFrames (plays : ℕ → Option ℝ) : ℕ := by
  classical
  exact if h : ∃ k, (plays k).isSome then ⌊(plays (Nat.find h)).getD 0⌋₊ + 1 else 0

/-! ## The last position played -/

theorem lastPlayed_succ_some {K : ℕ} {x : ℝ} (h : plays K = some x) :
    lastPlayed plays (K + 1) = some x := by
  simp [lastPlayed, h]

theorem lastPlayed_succ_none {K : ℕ} (h : plays K = none) :
    lastPlayed plays (K + 1) = lastPlayed plays K := by
  simp [lastPlayed, h]

/-- If no output sample before `K` has a last played position, none of them
plays the source. -/
theorem eq_none_of_lastPlayed_none :
    ∀ {K : ℕ}, lastPlayed plays K = none → ∀ j < K, plays j = none
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | K + 1, h, j, hj => by
      cases hK : plays K with
      | none =>
        rw [lastPlayed_succ_none hK] at h
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · exact eq_none_of_lastPlayed_none h j hlt
        · exact hK
      | some x =>
        rw [lastPlayed_succ_some hK] at h
        exact absurd h (by simp)

/-- The last played position before `K` is played by the output sample just
before the trailing ones that play nothing. -/
theorem lastPlayed_some :
    ∀ {K : ℕ} {x : ℝ}, lastPlayed plays K = some x →
      trailing plays K < K ∧ plays (K - 1 - trailing plays K) = some x
  | 0, x, h => by simp [lastPlayed] at h
  | K + 1, x, h => by
      cases hK : plays K with
      | none =>
        rw [lastPlayed_succ_none hK] at h
        obtain ⟨h1, h2⟩ := lastPlayed_some h
        rw [trailing_succ_none hK]
        refine ⟨by omega, ?_⟩
        have e : K + 1 - 1 - (trailing plays K + 1) = K - 1 - trailing plays K := by omega
        rw [e]
        exact h2
      | some y =>
        rw [lastPlayed_succ_some hK] at h
        rw [trailing_succ_some hK]
        refine ⟨Nat.succ_pos K, ?_⟩
        have e : K + 1 - 1 - 0 = K := by omega
        rw [e, hK]
        exact h

/-- The trailing output samples before `K` play nothing. -/
theorem eq_none_of_trailing :
    ∀ {K n : ℕ}, K - trailing plays K ≤ n → n < K → plays n = none
  | 0, n, _, hn => absurd hn (Nat.not_lt_zero n)
  | K + 1, n, h, hn => by
      cases hK : plays K with
      | none =>
        rw [trailing_succ_none hK] at h
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | rfl
        · exact eq_none_of_trailing (by omega) hlt
        · exact hK
      | some y =>
        rw [trailing_succ_some hK] at h
        omega

/-- The last output sample before `K` that plays the source, by its
index. -/
theorem findGreatest_isSome {K : ℕ} (h : trailing plays K < K) :
    Nat.findGreatest (fun j => (plays j).isSome) (K - 1) = K - 1 - trailing plays K := by
  rw [Nat.findGreatest_eq_iff]
  refine ⟨Nat.sub_le _ _, fun _ => isSome_before_trailing plays K h, fun n hn hnK hsome => ?_⟩
  have hnone := eq_none_of_trailing (plays := plays) (K := K) (n := n) (by omega) (by omega)
  rw [hnone] at hsome
  exact absurd hsome (by simp)

/-! ## The missed samples of one output sample -/

theorem missedAt_of_none {K : ℕ} (h : plays K = none) : missedAt plays K = 1 := by
  simp [missedAt, h]

/-- The missed samples counted at an output sample that plays the source
after an earlier one did: the frames that its position skips, beyond the
trailing output samples that played nothing, and the frames that it plays
again. -/
theorem missedAt_of_lastPlayed {K : ℕ} {x y : ℝ} (hy : plays K = some y)
    (hx : lastPlayed plays K = some x) :
    missedAt plays K
      = (⌊y - x - 1⌋ - (trailing plays K : ℤ)).toNat + ⌊1 - (y - x)⌋.toNat := by
  classical
  obtain ⟨ht, hlast⟩ := lastPlayed_some hx
  have hfind := findGreatest_isSome ht
  have hex : ∃ j < K, (plays j).isSome :=
    ⟨K - 1 - trailing plays K, by omega, by rw [hlast]; rfl⟩
  simp only [missedAt, hy]
  rw [ite_eq_left hex, hfind]
  simp only [hlast]
  have e : K - 1 - (K - 1 - trailing plays K) = trailing plays K := by omega
  rw [e]

/-- **A step that is not continuous counts a missed sample**, at its own
output sample or at the next one. -/
theorem one_le_missedAt_add {k : ℕ} (h : ¬ PlaysContinuously plays k) :
    1 ≤ missedAt plays k + missedAt plays (k + 1) := by
  cases hk : plays k with
  | none =>
    rw [missedAt_of_none hk]
    exact Nat.le_add_right 1 _
  | some x =>
    cases hk1 : plays (k + 1) with
    | none =>
      rw [missedAt_of_none hk1]
      exact Nat.le_add_left 1 _
    | some y =>
      rw [missedAt_of_lastPlayed hk1 (lastPlayed_succ_some hk), trailing_succ_some hk]
      have hnot : ¬ (x < y ∧ y < x + 2) := fun hc => h ⟨x, y, hk, hk1, hc.1, hc.2⟩
      rcases le_or_gt y x with hle | hlt
      · have h1 : (1 : ℤ) ≤ ⌊1 - (y - x)⌋ := Int.le_floor.mpr (by push_cast; linarith)
        omega
      · have hge : x + 2 ≤ y := not_lt.mp fun h2 => hnot ⟨hlt, h2⟩
        have h1 : (1 : ℤ) ≤ ⌊y - x - 1⌋ := Int.le_floor.mpr (by push_cast; linarith)
        omega

/-! ## Counting missed samples and continuous steps -/

theorem missedBefore_succ (plays : ℕ → Option ℝ) (K : ℕ) :
    missedBefore plays (K + 1) = missedBefore plays K + missedAt plays K := by
  unfold missedBefore
  rw [Finset.sum_range_succ]

theorem missedBefore_mono (plays : ℕ → Option ℝ) {K K' : ℕ} (h : K ≤ K') :
    missedBefore plays K ≤ missedBefore plays K' := by
  unfold missedBefore
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- When no output sample before `K` plays the source, each of them counts
one missed sample. -/
theorem missedBefore_of_none :
    ∀ {K : ℕ}, (∀ j < K, plays j = none) → missedBefore plays K = K
  | 0, _ => by simp [missedBefore]
  | K + 1, h => by
      rw [missedBefore_succ, missedBefore_of_none fun j hj => h j (Nat.lt_succ_of_lt hj),
        missedAt_of_none (h K (Nat.lt_succ_self K))]

theorem continuousBefore_succ_of {K : ℕ} (h : PlaysContinuously plays K) :
    continuousBefore plays (K + 1) = continuousBefore plays K + 1 := by
  classical
  unfold continuousBefore
  rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left h,
    Finset.card_insert_of_notMem (by simp)]

theorem continuousBefore_succ_of_not {K : ℕ} (h : ¬ PlaysContinuously plays K) :
    continuousBefore plays (K + 1) = continuousBefore plays K := by
  classical
  unfold continuousBefore
  rw [Finset.range_add_one, Finset.filter_insert, ite_eq_right h]

theorem continuousBefore_le (plays : ℕ → Option ℝ) (K : ℕ) : continuousBefore plays K ≤ K := by
  classical
  unfold continuousBefore
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range K)

/-- **The steps that are not continuous number at most twice the missed
samples.** -/
theorem le_continuousBefore_add (plays : ℕ → Option ℝ) :
    ∀ K, K ≤ continuousBefore plays K + missedBefore plays K + missedBefore plays (K + 1)
  | 0 => Nat.zero_le _
  | K + 1 => by
      have ih := le_continuousBefore_add plays K
      have e1 := missedBefore_succ plays K
      have e2 := missedBefore_succ plays (K + 1)
      by_cases hc : PlaysContinuously plays K
      · rw [continuousBefore_succ_of hc]
        omega
      · rw [continuousBefore_succ_of_not hc]
        have h1 := one_le_missedAt_add hc
        omega

/-! ## How far the playback has come -/

/-- **The last played position is at least the advance of the continuous
steps, minus the missed samples.** Let every position be at least zero, and
let the position advance by at least `s` in every step of continuous
playback. -/
theorem le_lastPlayed {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hpos : ∀ k x, plays k = some x → 0 ≤ x)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y) :
    ∀ K x, lastPlayed plays (K + 1) = some x →
      s * continuousBefore plays K - missedBefore plays (K + 1) ≤ x
  | 0, x, h => by
      cases h0 : plays 0 with
      | none =>
        rw [lastPlayed_succ_none h0] at h
        simp [lastPlayed] at h
      | some y =>
        rw [lastPlayed_succ_some h0, Option.some.injEq] at h
        have hx : 0 ≤ x := h ▸ hpos 0 y h0
        have hc : continuousBefore plays 0 = 0 := by simp [continuousBefore]
        have hm : (0 : ℝ) ≤ missedBefore plays 1 := Nat.cast_nonneg _
        rw [hc]
        simp only [Nat.cast_zero, mul_zero]
        linarith
  | K + 1, y, h => by
      have e2 := missedBefore_succ plays (K + 1)
      have hcle : (continuousBefore plays K : ℝ) ≤ K := by
        exact_mod_cast continuousBefore_le plays K
      cases hK1 : plays (K + 1) with
      | none =>
        rw [lastPlayed_succ_none hK1] at h
        have ih := le_lastPlayed hs0 hs1 hpos hslow K y h
        have hc : ¬ PlaysContinuously plays K := by
          rintro ⟨_, y', _, hy', _, _⟩
          rw [hK1] at hy'
          exact absurd hy' (by simp)
        rw [continuousBefore_succ_of_not hc, e2]
        push_cast
        have hm : (0 : ℝ) ≤ missedAt plays (K + 1) := Nat.cast_nonneg _
        linarith
      | some y' =>
        rw [lastPlayed_succ_some hK1, Option.some.injEq] at h
        subst h
        cases hl : lastPlayed plays (K + 1) with
        | none =>
          have hnone := eq_none_of_lastPlayed_none hl
          have hc : ¬ PlaysContinuously plays K := by
            rintro ⟨x', _, hx', _, _, _⟩
            rw [hnone K (Nat.lt_succ_self K)] at hx'
            exact absurd hx' (by simp)
          have hM : missedBefore plays (K + 1) = K + 1 := missedBefore_of_none hnone
          have hy0 := hpos (K + 1) y' hK1
          rw [continuousBefore_succ_of_not hc, e2, hM]
          push_cast
          have hm : (0 : ℝ) ≤ missedAt plays (K + 1) := Nat.cast_nonneg _
          have hsK : s * continuousBefore plays K ≤ K := by
            calc s * continuousBefore plays K ≤ 1 * K :=
                  mul_le_mul hs1 hcle (Nat.cast_nonneg _) zero_le_one
              _ = K := one_mul _
          linarith
        | some x =>
          have ih := le_lastPlayed hs0 hs1 hpos hslow K x hl
          by_cases hc : PlaysContinuously plays K
          · obtain ⟨x', y'', hx', hy'', h1, h2⟩ := hc
            have hxx : x = x' := by
              have := lastPlayed_succ_some hx'
              rw [hl, Option.some.injEq] at this
              exact this
            have hyy : y'' = y' := by
              rw [hK1, Option.some.injEq] at hy''
              exact hy''.symm
            subst hxx hyy
            have hadv := hslow K x y'' hx' hK1 h1 h2
            rw [continuousBefore_succ_of ⟨x, y'', hx', hK1, h1, h2⟩, e2]
            push_cast
            have hm : (0 : ℝ) ≤ missedAt plays (K + 1) := Nat.cast_nonneg _
            linarith
          · rw [continuousBefore_succ_of_not hc, e2, missedAt_of_lastPlayed hK1 hl]
            push_cast
            have h1 : (0 : ℝ) ≤ ((⌊y' - x - 1⌋ - (trailing plays (K + 1) : ℤ)).toNat : ℝ) :=
              Nat.cast_nonneg _
            have h2 : ((⌊1 - (y' - x)⌋ : ℤ) : ℝ) ≤ ((⌊1 - (y' - x)⌋.toNat : ℕ) : ℝ) := by
              exact_mod_cast Int.self_le_toNat _
            have h3 := Int.lt_floor_add_one (1 - (y' - x))
            linarith

/-! ## The frames that no step has passed -/

theorem mem_unpassed {K n : ℕ} {x : ℝ} :
    n ∈ unpassed plays K x ↔ n ≤ ⌊x⌋₊ ∧ ¬ PassedBefore plays K n := by
  classical
  unfold unpassed
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem PassedBefore.mono {K K' n : ℕ} (h : PassedBefore plays K n) (hK : K ≤ K') :
    PassedBefore plays K' n := by
  obtain ⟨k, hk, hc⟩ := h
  exact ⟨k, lt_of_lt_of_le hk hK, hc⟩

/-- The first position played, in terms of the first output sample that
plays the source. -/
theorem firstFrames_eq {K : ℕ} {y : ℝ} (hy : plays K = some y)
    (hl : lastPlayed plays K = none) : firstFrames plays = ⌊y⌋₊ + 1 := by
  classical
  have hex : ∃ k, (plays k).isSome := ⟨K, by rw [hy]; rfl⟩
  have hfind : Nat.find hex = K := by
    rw [Nat.find_eq_iff]
    refine ⟨by rw [hy]; rfl, fun j hj hsome => ?_⟩
    rw [eq_none_of_lastPlayed_none hl j hj] at hsome
    exact absurd hsome (by simp)
  unfold firstFrames
  rw [dite_eq_left hex, hfind, hy]
  rfl

/-- **The frames that no step has passed are paid for by missed samples.**
Let every position be at least zero. The frames at or below the last played
position that no step between output samples before `K` passes, plus three
for each trailing output sample that plays nothing, number at most
`firstFrames` plus three times the missed samples counted before `K`. -/
theorem card_unpassed_le (hpos : ∀ k x, plays k = some x → 0 ≤ x) :
    ∀ K x, lastPlayed plays K = some x →
      (unpassed plays K x).card + 3 * trailing plays K
        ≤ firstFrames plays + 3 * missedBefore plays K
  | 0, x, h => by simp [lastPlayed] at h
  | K + 1, y, h => by
      have eM := missedBefore_succ plays K
      cases hK : plays K with
      | none =>
        rw [lastPlayed_succ_none hK] at h
        have ih := card_unpassed_le hpos K y h
        have hsub : unpassed plays (K + 1) y ⊆ unpassed plays K y := by
          intro n hn
          rw [mem_unpassed] at hn ⊢
          exact ⟨hn.1, fun hp => hn.2 (hp.mono (Nat.le_succ K))⟩
        have hcard := Finset.card_le_card hsub
        rw [trailing_succ_none hK, eM, missedAt_of_none hK]
        omega
      | some y' =>
        rw [lastPlayed_succ_some hK, Option.some.injEq] at h
        subst h
        rw [trailing_succ_some hK]
        cases hl : lastPlayed plays K with
        | none =>
          have hfirst := firstFrames_eq hK hl
          have hcard : (unpassed plays (K + 1) y').card ≤ ⌊y'⌋₊ + 1 := by
            classical
            unfold unpassed
            exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
          omega
        | some x =>
          have ih := card_unpassed_le hpos K x hl
          obtain ⟨ht, hlast⟩ := lastPlayed_some hl
          have hmiss := missedAt_of_lastPlayed hK hl
          have hx0 : 0 ≤ x := hpos _ x hlast
          have hy0 : 0 ≤ y' := hpos K y' hK
          by_cases hcont : trailing plays K = 0 ∧ x < y' ∧ y' < x + 2
          · -- A step of continuous playback passes the frames between the two
            -- positions.
            obtain ⟨hg, h1, h2⟩ := hcont
            have hK1 : K - 1 - trailing plays K = K - 1 := by omega
            rw [hK1] at hlast
            have hsub : unpassed plays (K + 1) y' ⊆ unpassed plays K x := by
              intro n hn
              rw [mem_unpassed] at hn ⊢
              refine ⟨?_, fun hp => hn.2 (hp.mono (Nat.le_succ K))⟩
              by_contra hgt
              have hxn : x ≤ n := by
                have h3 : ⌊x⌋₊ < n := not_le.mp hgt
                have h4 := Nat.lt_floor_add_one x
                have h5 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h3
                push_cast at h5
                linarith
              have hny : (n : ℝ) ≤ y' := (Nat.le_floor_iff hy0).mp hn.1
              refine hn.2 ⟨K - 1, by omega, x, y', hlast, ?_, h1, h2, hxn, hny⟩
              have e : K - 1 + 1 = K := by omega
              rw [e]
              exact hK
            have hcard := Finset.card_le_card hsub
            omega
          · -- A break leaves at most the frames between the two positions.
            have hsub : unpassed plays (K + 1) y'
                ⊆ unpassed plays K x ∪ Finset.Ioc ⌊x⌋₊ ⌊y'⌋₊ := by
              intro n hn
              rw [mem_unpassed] at hn
              rw [Finset.mem_union, mem_unpassed, Finset.mem_Ioc]
              by_cases hnx : n ≤ ⌊x⌋₊
              · exact Or.inl ⟨hnx, fun hp => hn.2 (hp.mono (Nat.le_succ K))⟩
              · exact Or.inr ⟨not_le.mp hnx, hn.1⟩
            have hcard : (unpassed plays (K + 1) y').card
                ≤ (unpassed plays K x).card + (⌊y'⌋₊ - ⌊x⌋₊) := by
              refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
              rw [Nat.card_Ioc]
            have hbreak : ⌊y'⌋₊ - ⌊x⌋₊ ≤ 3 * trailing plays K + 3 * missedAt plays K := by
              rcases Nat.le_total ⌊y'⌋₊ ⌊x⌋₊ with hle | hle
              · omega
              · -- The floors differ by less than the advance plus one.
                have h1 : ((⌊y'⌋₊ : ℕ) : ℝ) ≤ y' := Nat.floor_le hy0
                have h2 := Nat.lt_floor_add_one x
                have hfl : ((⌊y'⌋₊ : ℤ) - ⌊x⌋₊ - 2 : ℤ) ≤ ⌊y' - x - 1⌋ := by
                  rw [Int.le_floor]
                  push_cast
                  linarith
                rcases Nat.eq_zero_or_pos (trailing plays K) with hg | hg
                · rcases Nat.eq_or_lt_of_le hle with heq | hlt
                  · omega
                  · have hxy : x < y' := by
                      have h3 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ⌊y'⌋₊ := by exact_mod_cast hlt
                      push_cast at h3
                      linarith
                    have hge : x + 2 ≤ y' := not_lt.mp fun h2' => hcont ⟨hg, hxy, h2'⟩
                    have hone : (1 : ℤ) ≤ ⌊y' - x - 1⌋ := Int.le_floor.mpr (by push_cast; linarith)
                    rw [hmiss, hg]
                    omega
                · rw [hmiss]
                  omega
            omega

/-! ## The frames that are never played -/

theorem neverPlayed_le (plays : ℕ → Option ℝ) (N : ℕ) : neverPlayed plays N ≤ N := by
  classical
  unfold neverPlayed
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range N)

theorem neverPlayed_mono (plays : ℕ → Option ℝ) {N N' : ℕ} (h : N ≤ N') :
    neverPlayed plays N ≤ neverPlayed plays N' := by
  classical
  unfold neverPlayed
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

/-- **The frames that are never played are paid for by missed samples.** Let
every position be at least zero, and let the position advance by at least
`s`, with `0 < s ≤ 1`, in every step of continuous playback. Let `M` be the
missed samples counted at the first `K + 1` output samples. If
`N ≤ s * K - 3 * M`, then at most `firstFrames + 3 * M` of the first `N`
frames are never played. -/
theorem neverPlayed_le_of_missed {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hpos : ∀ k x, plays k = some x → 0 ≤ x)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {K N : ℕ} (hN : (N : ℝ) ≤ s * K - 3 * missedBefore plays (K + 1)) :
    neverPlayed plays N ≤ firstFrames plays + 3 * missedBefore plays (K + 1) := by
  classical
  have hKK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  cases hl : lastPlayed plays (K + 1) with
  | none =>
    have hM : missedBefore plays (K + 1) = K + 1 :=
      missedBefore_of_none (eq_none_of_lastPlayed_none hl)
    rw [hM] at hN
    push_cast at hN
    have : s * K ≤ 1 * K := mul_le_mul_of_nonneg_right hs1 hKK
    linarith
  | some L =>
    have hreach := le_lastPlayed hs0 hs1 hpos hslow K L hl
    have hcount := le_continuousBefore_add plays K
    have hmono := missedBefore_mono plays (Nat.le_succ K)
    have hM0 : (0 : ℝ) ≤ missedBefore plays (K + 1) := Nat.cast_nonneg _
    have hcc : (K : ℝ) - 2 * missedBefore plays (K + 1) ≤ continuousBefore plays K := by
      have h1 : (K : ℝ) ≤ continuousBefore plays K + missedBefore plays K
          + missedBefore plays (K + 1) := by exact_mod_cast hcount
      have h2 : (missedBefore plays K : ℝ) ≤ missedBefore plays (K + 1) := by exact_mod_cast hmono
      linarith
    have hNL : (N : ℝ) ≤ L := by
      have h1 := mul_le_mul_of_nonneg_left hcc hs0
      have h2 : s * (2 * (missedBefore plays (K + 1) : ℝ)) ≤ 1 * (2 * missedBefore plays (K + 1)) :=
        mul_le_mul_of_nonneg_right hs1 (by positivity)
      nlinarith
    have hsub : ((Finset.range N).filter fun n => ¬ PlaysFrame plays n)
        ⊆ unpassed plays (K + 1) L := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      rw [mem_unpassed]
      refine ⟨Nat.le_floor ?_, fun ⟨k, _, hc⟩ => hn.2 ⟨k, hc⟩⟩
      have : (n : ℝ) < N := by exact_mod_cast hn.1
      linarith
    have hcard := Finset.card_le_card hsub
    have hinv := card_unpassed_le hpos (K + 1) L hl
    unfold neverPlayed
    omega

/-! ## Payments that come after the frames

A frame that a speaker never plays is paid for when the playback passes it,
which can be long after the frame was captured. The lemma below is about
numbers only. It shows that, at some arbitrarily late times, the missed
samples counted so far pay for the frames captured so far that are never
played, up to a part that is small against the time. -/

/-- **At some arbitrarily late times the missed samples have paid for the
frames that are never played.** For each of `R` speakers let `Ψ r N` be a
number of frames among the first `N`, and `Q r K` a number counted at the
first `K` output samples, such that `Ψ r N ≤ c₀ r + 3 * Q r (K + 1)` whenever
`N ≤ s * K - 3 * Q r (K + 1)`. Let frames and output samples come at `ρ` per
second, up to a constant `a`: by time `T` there are `F T` frames and
`K₁ r T` and `K₂ r T` output samples. Let a frame cost `σ r / ρ` and a
counted sample pay `π`, with `6 * σ r ≤ π * s * ρ`. Then for every `ε > 0`
there are arbitrarily late times `T` at which the cost of the frames exceeds
the payments by at most `ε * T`. -/
theorem exists_time_paid {R : ℕ} {ρ s a π : ℝ} (hρ : 0 < ρ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (ha : 0 ≤ a) (hπ0 : 0 ≤ π) (Ψ Q : Fin R → ℕ → ℕ) (c₀ : Fin R → ℕ)
    (hΨle : ∀ r N, Ψ r N ≤ N) (hQmono : ∀ r, Monotone (Q r))
    (hpay : ∀ r (K N : ℕ), (N : ℝ) ≤ s * K - 3 * (Q r (K + 1) : ℝ) →
      Ψ r N ≤ c₀ r + 3 * Q r (K + 1))
    (σ : Fin R → ℝ) (hσ : ∀ r, 0 ≤ σ r) (hπ : ∀ r, 6 * σ r ≤ π * s * ρ)
    (F : ℝ → ℕ) (K₁ K₂ : Fin R → ℝ → ℕ)
    (hF : ∀ T, 0 ≤ T → (F T : ℝ) ≤ ρ * T + a)
    (hK₁ : ∀ r T, 0 ≤ T → ρ * T - a ≤ K₁ r T) (hK₂ : ∀ r T, 0 ≤ T → ρ * T - a ≤ K₂ r T)
    {ε : ℝ} (hε : 0 < ε) (T₀ : ℝ) :
    ∃ T, T₀ ≤ T ∧
      2 / ρ * ∑ r, σ r * Ψ r (F T) - π * ∑ r, ((Q r (K₁ r T) : ℝ) + Q r (K₂ r T))
        ≤ ε * T := by
  by_contra hcon
  push Not at hcon
  have hs₀pos : 0 < s / 2 := by positivity
  have hρs : 0 < ρ * (s / 2) := mul_pos hρ hs₀pos
  -- What a frame costs, for each speaker, per frame of the shorter horizon.
  let κ : Fin R → ℝ := fun r => 2 * σ r / (ρ * (s / 2))
  have hκ0 : ∀ r, 0 ≤ κ r := fun r => div_nonneg (mul_nonneg zero_le_two (hσ r)) hρs.le
  have hκ : ∀ r, κ r ≤ 2 * π / 3 := fun r => by
    rw [div_le_iff₀ hρs]
    have := hπ r
    nlinarith
  have hκρ : ∀ r, κ r * (ρ * (s / 2)) = 2 * σ r := fun r => div_mul_cancel₀ _ hρs.ne'
  let c₁ : ℝ := s * a + s + a
  have hc₁ : 0 ≤ c₁ := by positivity
  let C : Fin R → ℝ := fun r => 2 * π / 3 * (c₀ r + c₁) + κ r * a
  -- Each speaker's payments by `T` cover its frames up to the shorter horizon.
  have hspeaker : ∀ r T, (a + 1) / ρ ≤ T →
      κ r * Ψ r (F (s / 2 * T)) - C r ≤ π * ((Q r (K₁ r T) : ℝ) + Q r (K₂ r T)) := by
    intro r T hT
    have hρT : a + 1 ≤ ρ * T := by
      rw [div_le_iff₀ hρ] at hT
      linarith
    have hT0 : 0 ≤ T := by
      by_contra hneg
      have : ρ * T < 0 := mul_neg_of_pos_of_neg hρ (not_le.mp hneg)
      linarith
    have h1 := hK₁ r T hT0
    have h2 := hK₂ r T hT0
    have hmin1 : (1 : ℝ) ≤ ((min (K₁ r T) (K₂ r T) : ℕ) : ℝ) := by
      rw [Nat.cast_min]
      exact le_min (by linarith) (by linarith)
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K + 1 = min (K₁ r T) (K₂ r T) := by
      have : 1 ≤ min (K₁ r T) (K₂ r T) := by exact_mod_cast hmin1
      exact ⟨min (K₁ r T) (K₂ r T) - 1, by omega⟩
    have hq1 : (Q r (K + 1) : ℝ) ≤ Q r (K₁ r T) := by
      exact_mod_cast hQmono r (hK ▸ min_le_left _ _)
    have hq2 : (Q r (K + 1) : ℝ) ≤ Q r (K₂ r T) := by
      exact_mod_cast hQmono r (hK ▸ min_le_right _ _)
    have hKlow : ρ * T - a - 1 ≤ K := by
      have hcast : ((K + 1 : ℕ) : ℝ) = ((min (K₁ r T) (K₂ r T) : ℕ) : ℝ) := by rw [hK]
      rw [Nat.cast_min] at hcast
      push_cast at hcast
      have : ρ * T - a ≤ min (K₁ r T : ℝ) (K₂ r T) := le_min h1 h2
      linarith
    have hNup : (F (s / 2 * T) : ℝ) ≤ ρ * (s / 2 * T) + a := hF _ (by positivity)
    have hΨN : (Ψ r (F (s / 2 * T)) : ℝ) ≤ F (s / 2 * T) := by exact_mod_cast hΨle r _
    have hΨ0 : (0 : ℝ) ≤ Ψ r (F (s / 2 * T)) := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ Q r (K + 1) := Nat.cast_nonneg _
    have hc₀ : (0 : ℝ) ≤ c₀ r := Nat.cast_nonneg _
    have hpaid : 2 * π * Q r (K + 1) ≤ π * ((Q r (K₁ r T) : ℝ) + Q r (K₂ r T)) := by
      have := mul_le_mul_of_nonneg_left (add_le_add hq1 hq2) hπ0
      linarith
    have hκa : 0 ≤ κ r * a := mul_nonneg (hκ0 r) ha
    by_cases hcase : (F (s / 2 * T) : ℝ) ≤ s * K - 3 * (Q r (K + 1) : ℝ)
    · -- The playback has passed the shorter horizon: the count pays.
      have h3 : (Ψ r (F (s / 2 * T)) : ℝ) ≤ c₀ r + 3 * Q r (K + 1) := by
        exact_mod_cast hpay r K _ hcase
      have hA2 : 2 * π / 3 * ((Ψ r (F (s / 2 * T)) : ℝ) - c₀ r) ≤ 2 * π * Q r (K + 1) := by
        have := mul_le_mul_of_nonneg_left (show (Ψ r (F (s / 2 * T)) : ℝ) - c₀ r
          ≤ 3 * Q r (K + 1) by linarith) (show (0 : ℝ) ≤ 2 * π / 3 by positivity)
        linarith
      have hA3 := mul_le_mul_of_nonneg_right (hκ r) hΨ0
      have hA4 : 0 ≤ 2 * π / 3 * c₁ := by positivity
      show κ r * Ψ r (F (s / 2 * T)) - (2 * π / 3 * (c₀ r + c₁) + κ r * a) ≤ _
      linarith
    · -- It has not: then many samples were counted.
      have hlt : s * K - 3 * (Q r (K + 1) : ℝ) < F (s / 2 * T) := not_le.mp hcase
      have hsK : s * (ρ * T - a - 1) ≤ s * K := mul_le_mul_of_nonneg_left hKlow hs0.le
      have h3q : ρ * (s / 2) * T - c₁ ≤ 3 * Q r (K + 1) := by
        show ρ * (s / 2) * T - (s * a + s + a) ≤ _
        nlinarith
      have hB2 : 2 * π / 3 * (ρ * (s / 2) * T - c₁) ≤ 2 * π * Q r (K + 1) := by
        have := mul_le_mul_of_nonneg_left h3q (show (0 : ℝ) ≤ 2 * π / 3 by positivity)
        linarith
      have hB3 : κ r * Ψ r (F (s / 2 * T)) ≤ κ r * (ρ * (s / 2 * T) + a) :=
        mul_le_mul_of_nonneg_left (hΨN.trans hNup) (hκ0 r)
      have hB4 : κ r * (ρ * (s / 2 * T)) = 2 * σ r * T := by
        have := hκρ r
        calc κ r * (ρ * (s / 2 * T)) = κ r * (ρ * (s / 2)) * T := by ring
          _ = 2 * σ r * T := by rw [this]
      have hB5 : 2 * σ r * T ≤ 2 * π / 3 * (ρ * (s / 2) * T) := by
        have h6 := hπ r
        have : 0 ≤ (π * s * ρ - 6 * σ r) * T := mul_nonneg (by linarith) hT0
        nlinarith
      have hB6 : 0 ≤ 2 * π / 3 * c₀ r := by positivity
      show κ r * Ψ r (F (s / 2 * T)) - (2 * π / 3 * (c₀ r + c₁) + κ r * a) ≤ _
      nlinarith
  -- The cost of the frames by `T`, and the payments by `T`.
  let Φ : ℝ → ℝ := fun T => 2 / ρ * ∑ r, σ r * Ψ r (F T)
  have hΦ0 : ∀ T, 0 ≤ Φ T := fun T =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => mul_nonneg (hσ r) (Nat.cast_nonneg _))
  have hscale : ∀ T, (∑ r, κ r * Ψ r (F (s / 2 * T))) = Φ (s / 2 * T) / (s / 2) := by
    intro T
    show _ = (2 / ρ * ∑ r, σ r * Ψ r (F (s / 2 * T))) / (s / 2)
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    show 2 * σ r / (ρ * (s / 2)) * _ = _
    field_simp
  have hsum : ∀ T, (a + 1) / ρ ≤ T →
      Φ (s / 2 * T) / (s / 2) - ∑ r, C r
        ≤ π * ∑ r, ((Q r (K₁ r T) : ℝ) + Q r (K₂ r T)) := by
    intro T hT
    rw [← hscale, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => hspeaker r T hT
  -- The cost of the frames is at most a multiple of the time.
  let S : ℝ := ∑ r, σ r
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => hσ r
  have hΦup : ∀ T, 0 ≤ T → a / ρ ≤ T → Φ T ≤ 4 * S * T := by
    intro T hT0 hT
    have haT : a ≤ ρ * T := by
      rw [div_le_iff₀ hρ] at hT
      linarith
    have hFT := hF T hT0
    have hle : ∑ r, σ r * (Ψ r (F T) : ℝ) ≤ S * (ρ * T + a) := by
      show _ ≤ (∑ r, σ r) * (ρ * T + a)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (hσ r)
      have : (Ψ r (F T) : ℝ) ≤ F T := by exact_mod_cast hΨle r _
      linarith
    have h2 : 2 / ρ * (S * (ρ * T + a)) ≤ 4 * S * T := by
      have h3 : 2 / ρ * (S * (ρ * T + a)) = 2 * S * T + 2 * S * (a / ρ) := by
        field_simp
      have h4 : a / ρ ≤ T := hT
      have h5 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ 2 * S by positivity)
      linarith
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans h2
  -- A sequence of times, each longer than the one before by the factor `2 / s`.
  let Tstar : ℝ := max (max T₀ ((a + 1) / ρ)) (max (2 * (∑ r, C r) / ε) 1)
  have hTstar1 : 1 ≤ Tstar := (le_max_right _ _).trans (le_max_right _ _)
  have hTstar0 : T₀ ≤ Tstar := (le_max_left _ _).trans (le_max_left _ _)
  have hTstarρ : (a + 1) / ρ ≤ Tstar := (le_max_right _ _).trans (le_max_left _ _)
  have hTstarC : 2 * (∑ r, C r) / ε ≤ Tstar := (le_max_left _ _).trans (le_max_right _ _)
  have hlam : 1 ≤ (s / 2)⁻¹ := by
    rw [one_le_inv₀ hs₀pos]
    linarith
  let Tseq : ℕ → ℝ := fun j => Tstar * (s / 2)⁻¹ ^ j
  have hTseq_ge : ∀ j, Tstar ≤ Tseq j := fun j =>
    le_mul_of_one_le_right (by linarith) (one_le_pow₀ hlam)
  have hTseq_succ : ∀ j, s / 2 * Tseq (j + 1) = Tseq j := by
    intro j
    show s / 2 * (Tstar * (s / 2)⁻¹ ^ (j + 1)) = Tstar * (s / 2)⁻¹ ^ j
    rw [pow_succ]
    field_simp
  have hgrow : ∀ j : ℕ, (j : ℝ) * (ε / 2) * Tseq j ≤ Φ (Tseq j) := by
    intro j
    induction j with
    | zero => simpa using hΦ0 (Tseq 0)
    | succ j ih =>
      have hTj := hTseq_ge (j + 1)
      have h1 := hcon (Tseq (j + 1)) (hTstar0.trans hTj)
      have h2 := hsum (Tseq (j + 1)) (hTstarρ.trans hTj)
      rw [hTseq_succ j] at h2
      have h3 : Φ (Tseq j) / (s / 2) = (s / 2)⁻¹ * Φ (Tseq j) := by
        rw [div_eq_mul_inv, mul_comm]
      have h4 : (s / 2)⁻¹ * Tseq j = Tseq (j + 1) := by
        rw [← hTseq_succ j]
        field_simp
      have h5 : (s / 2)⁻¹ * ((j : ℝ) * (ε / 2) * Tseq j) ≤ (s / 2)⁻¹ * Φ (Tseq j) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      have h6 : (s / 2)⁻¹ * ((j : ℝ) * (ε / 2) * Tseq j) = (j : ℝ) * (ε / 2) * Tseq (j + 1) := by
        rw [← h4]
        ring
      have h7 : ∑ r, C r ≤ ε / 2 * Tseq (j + 1) := by
        have h8 : 2 * (∑ r, C r) / ε ≤ Tseq (j + 1) := hTstarC.trans hTj
        rw [div_le_iff₀ hε] at h8
        linarith
      push_cast
      nlinarith
  -- The cost of the frames cannot grow faster than the time.
  obtain ⟨j, hj⟩ := exists_nat_gt (8 * S / ε)
  have hTj := hTseq_ge j
  have hTjpos : 0 < Tseq j := by linarith
  have hup := hΦup (Tseq j) hTjpos.le (by
    have : a / ρ ≤ (a + 1) / ρ := div_le_div_of_nonneg_right (by linarith) hρ.le
    linarith)
  have hlow := hgrow j
  have h9 : (j : ℝ) * (ε / 2) ≤ 4 * S := by
    by_contra hlt
    have := mul_lt_mul_of_pos_right (not_le.mp hlt) hTjpos
    linarith
  rw [div_lt_iff₀ hε] at hj
  linarith

end Unisono.Spec
