/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Stall

/-!
# Steps that break new ground

The latency of a frame is taken at the first step of continuous playback
that passes it. To bound the latency that a playback accrues from below, for
any playback, one has to know which steps pass frames for the first time.
This file names them and proves two facts about the playback of one speaker.

* `maxPlayed plays K` is the largest position played before output sample
  `K`, and zero if there is none.
* The step from output sample `k` to the next *breaks new ground* when
  playback is continuous over it and the position that it reaches exceeds
  every position played before (`NewGround`). Every frame above the largest
  earlier position and up to the position reached is passed by that step
  (`NewGround.covers`) and by no earlier step (`NewGround.not_covers`), so
  the step is the first that passes it.
* `add_le_lastPlayed`: between two output samples, the position played last
  advances by at least `s` for every step of continuous playback in between,
  minus the missed samples counted in between. Here `s` is the least advance
  of the position in a step of continuous playback. This is `le_lastPlayed`
  for a stretch that does not start at the first output sample.

Nothing here is about cost yet.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {plays : ℕ → Option ℝ}

/-! ## The position played last, over a stretch -/

/-- Once an output sample has played the source, every later output sample
has a position that was played last before it. -/
theorem lastPlayed_isSome_of_le {k₀ K : ℕ} (hk : k₀ ≤ K) (h : (lastPlayed plays k₀).isSome) :
    (lastPlayed plays K).isSome := by
  induction K, hk using Nat.le_induction with
  | base => exact h
  | succ K _ ih =>
    cases hK : plays K with
    | none =>
      rw [lastPlayed_succ_none hK]
      exact ih
    | some x =>
      rw [lastPlayed_succ_some hK]
      rfl

/-- **Over a stretch, the last played position advances by the continuous
steps, minus the missed samples.** Let the position advance by at least `s`
in every step of continuous playback. If `x₀` is the position
played last up to output sample `k₀`, then for every `K ≥ k₀` the position
played last up to output sample `K` is at least `x₀`, plus `s` for every
step of continuous playback that starts at an output sample from `k₀` to
`K - 1`, minus the missed samples counted at the output samples from
`k₀ + 1` to `K`. -/
theorem add_le_lastPlayed {s : ℝ}
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {k₀ : ℕ} {x₀ : ℝ} (h₀ : lastPlayed plays (k₀ + 1) = some x₀) :
    ∀ K, k₀ ≤ K → ∀ y, lastPlayed plays (K + 1) = some y →
      x₀ + s * ((continuousBefore plays K : ℝ) - continuousBefore plays k₀)
        - ((missedBefore plays (K + 1) : ℝ) - missedBefore plays (k₀ + 1)) ≤ y := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    intro y hy
    rw [h₀, Option.some.injEq] at hy
    subst hy
    simp
  | succ K hK ih =>
    intro z hz
    have e2 := missedBefore_succ plays (K + 1)
    have hsome : (lastPlayed plays (K + 1)).isSome :=
      lastPlayed_isSome_of_le (Nat.succ_le_succ hK) (by rw [h₀]; rfl)
    obtain ⟨x, hl⟩ := Option.isSome_iff_exists.mp hsome
    have ihx := ih x hl
    have hm : (0 : ℝ) ≤ missedAt plays (K + 1) := Nat.cast_nonneg _
    cases hK1 : plays (K + 1) with
    | none =>
      rw [lastPlayed_succ_none hK1, hl, Option.some.injEq] at hz
      subst hz
      have hc : ¬ PlaysContinuously plays K := by
        rintro ⟨_, y', _, hy', _, _⟩
        rw [hK1] at hy'
        exact absurd hy' (by simp)
      rw [continuousBefore_succ_of_not hc, e2]
      push_cast
      linarith
    | some y =>
      rw [lastPlayed_succ_some hK1, Option.some.injEq] at hz
      subst hz
      by_cases hc : PlaysContinuously plays K
      · obtain ⟨x', y', hx', hy', h1, h2⟩ := hc
        have hxx : x = x' := by
          have := lastPlayed_succ_some hx'
          rw [hl, Option.some.injEq] at this
          exact this
        have hyy : y' = y := by
          rw [hK1, Option.some.injEq] at hy'
          exact hy'.symm
        subst hxx hyy
        have hadv := hslow K x y' hx' hK1 h1 h2
        rw [continuousBefore_succ_of ⟨x, y', hx', hK1, h1, h2⟩, e2]
        push_cast
        linarith
      · rw [continuousBefore_succ_of_not hc, e2, missedAt_of_lastPlayed hK1 hl]
        push_cast
        have h1 : (0 : ℝ) ≤ ((⌊y - x - 1⌋ - (trailing plays (K + 1) : ℤ)).toNat : ℝ) :=
          Nat.cast_nonneg _
        have h2 : ((⌊1 - (y - x)⌋ : ℤ) : ℝ) ≤ ((⌊1 - (y - x)⌋.toNat : ℕ) : ℝ) := by
          exact_mod_cast Int.self_le_toNat _
        have h3 := Int.lt_floor_add_one (1 - (y - x))
        linarith

/-! ## The largest position played -/

/-- The largest position played before output sample `K`; zero if no output
sample before `K` plays the source. -/
def maxPlayed (plays : ℕ → Option ℝ) : ℕ → ℝ
  | 0 => 0
  | K + 1 =>
      match plays K with
      | some x => max x (maxPlayed plays K)
      | none => maxPlayed plays K

theorem maxPlayed_succ_some {K : ℕ} {x : ℝ} (h : plays K = some x) :
    maxPlayed plays (K + 1) = max x (maxPlayed plays K) := by
  simp [maxPlayed, h]

theorem maxPlayed_succ_none {K : ℕ} (h : plays K = none) :
    maxPlayed plays (K + 1) = maxPlayed plays K := by
  simp [maxPlayed, h]

/-- The largest position played never decreases. -/
theorem maxPlayed_mono (plays : ℕ → Option ℝ) : Monotone (maxPlayed plays) := by
  refine monotone_nat_of_le_succ fun K => ?_
  cases hK : plays K with
  | none => rw [maxPlayed_succ_none hK]
  | some x =>
    rw [maxPlayed_succ_some hK]
    exact le_max_right _ _

/-- Every position played before output sample `K` is at most the largest. -/
theorem le_maxPlayed {j K : ℕ} {x : ℝ} (h : plays j = some x) (hj : j < K) :
    x ≤ maxPlayed plays K := by
  have h1 : x ≤ maxPlayed plays (j + 1) := by
    rw [maxPlayed_succ_some h]
    exact le_max_left _ _
  exact h1.trans (maxPlayed_mono plays hj)

/-! ## Steps that break new ground -/

/-- The step from output sample `k` to the next breaks new ground: playback
is continuous over it, and the position that it reaches exceeds every
position played up to output sample `k`. -/
def NewGround (plays : ℕ → Option ℝ) (k : ℕ) : Prop :=
  ∃ x y, plays k = some x ∧ plays (k + 1) = some y ∧ x < y ∧ y < x + 2
    ∧ maxPlayed plays (k + 1) < y

/-- A step that breaks new ground is a step of continuous playback. -/
theorem NewGround.playsContinuously {k : ℕ} (h : NewGround plays k) :
    PlaysContinuously plays k := by
  obtain ⟨x, y, hx, hy, h1, h2, -⟩ := h
  exact ⟨x, y, hx, hy, h1, h2⟩

/-- A step that breaks new ground passes every frame above the largest
position played before and up to the position that it reaches. -/
theorem NewGround.covers {k n : ℕ} {y : ℝ} (h : NewGround plays k)
    (hy : plays (k + 1) = some y) (hlo : maxPlayed plays (k + 1) < n) (hhi : (n : ℝ) ≤ y) :
    Covers plays k n := by
  obtain ⟨x, y', hx, hy', h1, h2, -⟩ := h
  rw [hy, Option.some.injEq] at hy'
  subst hy'
  have hxm := le_maxPlayed hx (Nat.lt_succ_self k)
  exact ⟨x, y, hx, hy, h1, h2, by linarith, hhi⟩

/-- No earlier step passes a frame above the largest position played up to
output sample `k`. -/
theorem not_covers_of_maxPlayed_lt {j k n : ℕ} (hj : j < k)
    (hlo : maxPlayed plays (k + 1) < n) : ¬ Covers plays j n := by
  rintro ⟨x, y, -, hy, -, -, -, hny⟩
  have h1 := le_maxPlayed hy (Nat.succ_lt_succ hj)
  linarith

/-! ## When a frame on new ground is played -/

/-- **A frame above every earlier position is played within the step that
breaks new ground over it.** In a world, let the step of speaker `r` from
output sample `k` to the next break new ground, from the position `x` to the
position `y`, and let frame `n` lie above the largest position played up to
output sample `k` and at or below `y`. Then the step is the first that passes
the frame: the speaker plays the frame between the times at which the two
output samples leave, in proportion. -/
theorem World.latency_of_newGround {H : Type} {R : ℕ} (w : World H R)
    (plays : Fin R → ℕ → Option ℝ) {r : Fin R} {k n : ℕ} {x y : ℝ}
    (h : NewGround (plays r) k) (hx : plays r k = some x) (hy : plays r (k + 1) = some y)
    (hlo : maxPlayed (plays r) (k + 1) < n) (hhi : (n : ℝ) ≤ y) :
    w.latency plays r n
      = some ((w.speaker r).out k
          + ((n : ℝ) - x) / (y - x) * ((w.speaker r).out (k + 1) - (w.speaker r).out k)
          - w.source.capture n) := by
  classical
  have hcov : Covers (plays r) k n := h.covers hy hlo hhi
  unfold World.latency World.playTime Spec.playTime
  split
  · rename_i hex
    have hfind : Nat.find hex = k :=
      (Nat.find_eq_iff hex).mpr ⟨hcov, fun j hj => not_covers_of_maxPlayed_lt hj hlo⟩
    simp only [hfind, hx, hy, Option.map_some]
  · rename_i hne
    exact absurd ⟨k, hcov⟩ hne

/-- A frame on new ground is played no earlier than the first output sample
of the step that breaks new ground over it leaves: its latency is at least
the time from its capture to that output sample. -/
theorem World.le_latency_of_newGround {H : Type} {R : ℕ} (w : World H R)
    (plays : Fin R → ℕ → Option ℝ) {r : Fin R} {k n : ℕ} {y : ℝ}
    (h : NewGround (plays r) k) (hy : plays r (k + 1) = some y)
    (hlo : maxPlayed (plays r) (k + 1) < n) (hhi : (n : ℝ) ≤ y) :
    ∃ l, w.latency plays r n = some l ∧ (w.speaker r).out k - w.source.capture n ≤ l := by
  obtain ⟨x, y', hx, hy', h1, h2, h3⟩ := h
  rw [hy, Option.some.injEq] at hy'
  subst hy'
  refine ⟨_, w.latency_of_newGround plays ⟨x, y, hx, hy, h1, h2, h3⟩ hx hy hlo hhi, ?_⟩
  have hxm := le_maxPlayed hx (Nat.lt_succ_self k)
  have hout := (w.speaker r).out_strictMono (Nat.lt_succ_self k)
  have hfrac : 0 ≤ ((n : ℝ) - x) / (y - x)
      * ((w.speaker r).out (k + 1) - (w.speaker r).out k) :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) (by linarith)
  linarith

/-! ## How many frames the steps that break new ground pass -/

/-- The largest position played is not negative. -/
theorem maxPlayed_nonneg (plays : ℕ → Option ℝ) (K : ℕ) : 0 ≤ maxPlayed plays K :=
  maxPlayed_mono plays (Nat.zero_le K)

/-- After a step that breaks new ground, the largest position played is the
position that the step reached. -/
theorem NewGround.maxPlayed_eq {k : ℕ} {y : ℝ} (h : NewGround plays k)
    (hy : plays (k + 1) = some y) : maxPlayed plays (k + 1 + 1) = y := by
  obtain ⟨x, y', hx, hy', -, -, h3⟩ := h
  rw [hy, Option.some.injEq] at hy'
  subst hy'
  rw [maxPlayed_succ_some hy]
  exact max_eq_left h3.le

/-- A step that breaks new ground right after another one advances the
largest position played by at least `s`, the least advance of a step of
continuous playback. -/
theorem NewGround.add_le_maxPlayed {s : ℝ}
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {k : ℕ} (h₁ : NewGround plays k) (h₂ : NewGround plays (k + 1)) :
    maxPlayed plays (k + 1 + 1) + s ≤ maxPlayed plays (k + 1 + 1 + 1) := by
  obtain ⟨y, z, hy, hz, g1, g2, g3⟩ := h₂
  rw [h₁.maxPlayed_eq hy, NewGround.maxPlayed_eq ⟨y, z, hy, hz, g1, g2, g3⟩ hz]
  exact hslow (k + 1) y z hy hz g1 g2

/-- The number of steps that break new ground among the steps from output
sample `a` to output sample `b - 1`. -/
def newGroundCount (plays : ℕ → Option ℝ) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => by
      classical
      exact if a ≤ j ∧ NewGround plays j then newGroundCount plays a j + 1
        else newGroundCount plays a j

/-- The frames that the steps from output sample `a` to output sample
`b - 1` that break new ground pass: for each such step, the frames above the
largest position played before it and up to the position that it reaches. -/
def newFrames (plays : ℕ → Option ℝ) (a : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => by
      classical
      exact if a ≤ j ∧ NewGround plays j then
        newFrames plays a j
          ∪ Finset.Ioc ⌊maxPlayed plays (j + 1)⌋₊ ⌊maxPlayed plays (j + 1 + 1)⌋₊
      else newFrames plays a j

theorem newGroundCount_succ_of {a j : ℕ} (h : a ≤ j ∧ NewGround plays j) :
    newGroundCount plays a (j + 1) = newGroundCount plays a j + 1 := by
  simp [newGroundCount, h]

theorem newGroundCount_succ_of_not {a j : ℕ} (h : ¬ (a ≤ j ∧ NewGround plays j)) :
    newGroundCount plays a (j + 1) = newGroundCount plays a j := by
  simp [newGroundCount, h]

theorem newFrames_succ_of {a j : ℕ} (h : a ≤ j ∧ NewGround plays j) :
    newFrames plays a (j + 1)
      = newFrames plays a j
        ∪ Finset.Ioc ⌊maxPlayed plays (j + 1)⌋₊ ⌊maxPlayed plays (j + 1 + 1)⌋₊ := by
  simp [newFrames, h]

theorem newFrames_succ_of_not {a j : ℕ} (h : ¬ (a ≤ j ∧ NewGround plays j)) :
    newFrames plays a (j + 1) = newFrames plays a j := by
  simp [newFrames, h]

/-- No step before output sample `a` is counted. -/
theorem newGroundCount_of_le (a : ℕ) :
    ∀ j, j ≤ a → newGroundCount plays a j = 0 ∧ newFrames plays a j = ∅
  | 0, _ => ⟨rfl, rfl⟩
  | j + 1, h => by
    have ih := newGroundCount_of_le a j (Nat.le_of_succ_le h)
    have hcond : ¬ (a ≤ j ∧ NewGround plays j) := fun hc => absurd hc.1 (by omega)
    rw [newGroundCount_succ_of_not hcond, newFrames_succ_of_not hcond]
    exact ih

/-- Every frame that the steps before `b` pass on new ground is at most the
largest position played up to output sample `b`. -/
theorem le_floor_of_mem_newFrames (a : ℕ) :
    ∀ b n, n ∈ newFrames plays a b → n ≤ ⌊maxPlayed plays (b + 1)⌋₊
  | 0, n, h => by simp [newFrames] at h
  | j + 1, n, h => by
    have hmono := Nat.floor_le_floor (maxPlayed_mono plays (Nat.le_succ (j + 1)))
    by_cases hc : a ≤ j ∧ NewGround plays j
    · rw [newFrames_succ_of hc, Finset.mem_union, Finset.mem_Ioc] at h
      rcases h with h | h
      · exact (le_floor_of_mem_newFrames a j n h).trans hmono
      · exact h.2
    · rw [newFrames_succ_of_not hc] at h
      exact (le_floor_of_mem_newFrames a j n h).trans hmono

/-- **Each counted frame is on new ground of one counted step.** A frame
that the steps from `a` to `b - 1` pass on new ground lies above the largest
position played before one of those steps, which breaks new ground, and at
or below the largest position played after it. -/
theorem exists_of_mem_newFrames (a : ℕ) :
    ∀ b n, n ∈ newFrames plays a b → ∃ k, a ≤ k ∧ k < b ∧ NewGround plays k
      ∧ maxPlayed plays (k + 1) < n ∧ (n : ℝ) ≤ maxPlayed plays (k + 1 + 1)
  | 0, n, h => by simp [newFrames] at h
  | j + 1, n, h => by
    by_cases hc : a ≤ j ∧ NewGround plays j
    · rw [newFrames_succ_of hc, Finset.mem_union, Finset.mem_Ioc] at h
      rcases h with h | h
      · obtain ⟨k, hak, hkj, hk⟩ := exists_of_mem_newFrames a j n h
        exact ⟨k, hak, Nat.lt_succ_of_lt hkj, hk⟩
      · exact ⟨j, hc.1, Nat.lt_succ_self j, hc.2,
          (Nat.floor_lt (maxPlayed_nonneg plays (j + 1))).mp h.1,
          (Nat.le_floor_iff (maxPlayed_nonneg plays (j + 1 + 1))).mp h.2⟩
    · rw [newFrames_succ_of_not hc] at h
      obtain ⟨k, hak, hkj, hk⟩ := exists_of_mem_newFrames a j n h
      exact ⟨k, hak, Nat.lt_succ_of_lt hkj, hk⟩

/-- A step that breaks new ground adds the frames between the largest
positions played before and after it. -/
theorem card_newFrames_succ_of {a j : ℕ} (h : a ≤ j ∧ NewGround plays j) :
    (newFrames plays a (j + 1)).card
      = (newFrames plays a j).card
        + (⌊maxPlayed plays (j + 1 + 1)⌋₊ - ⌊maxPlayed plays (j + 1)⌋₊) := by
  rw [newFrames_succ_of h]
  have hdisj : newFrames plays a j
      ∩ Finset.Ioc ⌊maxPlayed plays (j + 1)⌋₊ ⌊maxPlayed plays (j + 1 + 1)⌋₊ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
    rw [Finset.mem_inter, Finset.mem_Ioc] at hn
    have := le_floor_of_mem_newFrames a j n hn.1
    omega
  have hcard := Finset.card_union_add_card_inter (newFrames plays a j)
    (Finset.Ioc ⌊maxPlayed plays (j + 1)⌋₊ ⌊maxPlayed plays (j + 1 + 1)⌋₊)
  rw [hdisj, Finset.card_empty, add_zero, Nat.card_Ioc] at hcard
  exact hcard

open Classical in
/-- The count of the frames on new ground, with the fraction of a frame that
the last step has passed, against the counted steps. A step that breaks new
ground right after another one adds `s`; the first step of a run of such
steps may add less, and the end of a run loses the fraction. -/
theorem newFrames_invariant {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    (a : ℕ) :
    ∀ j, a ≤ j →
      s * newGroundCount plays a j - (1 + s) * ((j : ℝ) - a - newGroundCount plays a j) - s
          + (if a < j ∧ NewGround plays (j - 1) then 0 else s)
        ≤ ((newFrames plays a j).card : ℝ)
          + (maxPlayed plays (j + 1) - ⌊maxPlayed plays (j + 1)⌋₊) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    obtain ⟨h0, h1⟩ := newGroundCount_of_le (plays := plays) a a le_rfl
    have hfl := Nat.floor_le (maxPlayed_nonneg plays (a + 1))
    have hif : (if a < a ∧ NewGround plays (a - 1) then (0 : ℝ) else s) = s := by simp
    rw [h0, h1, hif]
    simp only [Nat.cast_zero, mul_zero, Finset.card_empty, sub_self, zero_sub,
      zero_add]
    linarith
  | succ j hj ih =>
    have hM := maxPlayed_mono plays (Nat.le_succ (j + 1))
    have hlt₁ := Nat.lt_floor_add_one (maxPlayed plays (j + 1))
    have hfl₂ := Nat.floor_le (maxPlayed_nonneg plays (j + 1 + 1))
    have hpend : (0 : ℝ) ≤ (if a < j ∧ NewGround plays (j - 1) then 0 else s) := by
      split_ifs
      · exact le_rfl
      · exact hs0
    by_cases hng : NewGround plays j
    · have hcond : a ≤ j ∧ NewGround plays j := ⟨hj, hng⟩
      have hnext : (if a < j + 1 ∧ NewGround plays (j + 1 - 1) then (0 : ℝ) else s) = 0 := by
        simp [Nat.lt_succ_of_le hj, hng]
      have hsub : ((⌊maxPlayed plays (j + 1 + 1)⌋₊ - ⌊maxPlayed plays (j + 1)⌋₊ : ℕ) : ℝ)
          = (⌊maxPlayed plays (j + 1 + 1)⌋₊ : ℝ) - ⌊maxPlayed plays (j + 1)⌋₊ :=
        Nat.cast_sub (Nat.floor_le_floor hM)
      have hadv : s - (if a < j ∧ NewGround plays (j - 1) then 0 else s)
          ≤ maxPlayed plays (j + 1 + 1) - maxPlayed plays (j + 1) := by
        split_ifs with hprev
        · obtain ⟨hlt, hp⟩ := hprev
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          have hp' : NewGround plays i := by simpa using hp
          have := NewGround.add_le_maxPlayed hslow hp' hng
          linarith
        · linarith
      rw [newGroundCount_succ_of hcond, card_newFrames_succ_of hcond, hnext,
        Nat.cast_add (newFrames plays a j).card, hsub]
      push_cast
      linarith
    · have hcond : ¬ (a ≤ j ∧ NewGround plays j) := fun h => hng h.2
      have hnext : (if a < j + 1 ∧ NewGround plays (j + 1 - 1) then (0 : ℝ) else s) = s := by
        simp [hng]
      rw [newGroundCount_succ_of_not hcond, newFrames_succ_of_not hcond, hnext]
      push_cast
      linarith

/-- **The steps that break new ground pass about `s` frames each.** Let the
position advance by at least `s`, with `0 ≤ s`, in every step of continuous
playback. Among the steps from output sample `a` to output sample `b - 1`,
let `p` break new ground. Then the frames that those steps pass on new
ground number at least `s * p`, minus `1 + s` for each of the other steps
and once more. -/
theorem le_card_newFrames {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {a b : ℕ} (hab : a ≤ b) :
    s * newGroundCount plays a b
        - (1 + s) * ((b : ℝ) - a - newGroundCount plays a b + 1)
      ≤ ((newFrames plays a b).card : ℝ) := by
  classical
  have h := newFrames_invariant hs0 hslow a b hab
  have hlt := Nat.lt_floor_add_one (maxPlayed plays (b + 1))
  have hpend : (0 : ℝ) ≤ (if a < b ∧ NewGround plays (b - 1) then 0 else s) := by
    split_ifs
    · exact le_rfl
    · exact hs0
  linarith

/-! ## Steps over ground already played -/

/-- The number of steps of continuous playback, among the steps that start at
an output sample before `K`, that do not break new ground: they end at or
below a position that was played before. -/
def replayBefore (plays : ℕ → Option ℝ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => by
      classical
      exact if PlaysContinuously plays K ∧ ¬ NewGround plays K then replayBefore plays K + 1
        else replayBefore plays K

theorem replayBefore_succ_of {K : ℕ} (h : PlaysContinuously plays K ∧ ¬ NewGround plays K) :
    replayBefore plays (K + 1) = replayBefore plays K + 1 := by
  simp [replayBefore, h]

theorem replayBefore_succ_of_not {K : ℕ}
    (h : ¬ (PlaysContinuously plays K ∧ ¬ NewGround plays K)) :
    replayBefore plays (K + 1) = replayBefore plays K := by
  simp [replayBefore, h]

/-- If no output sample before `K` plays the source, the largest position
played is zero. -/
theorem maxPlayed_of_none : ∀ {K : ℕ}, (∀ k < K, plays k = none) → maxPlayed plays K = 0
  | 0, _ => rfl
  | K + 1, h => by
    rw [maxPlayed_succ_none (h K (Nat.lt_succ_self K))]
    exact maxPlayed_of_none fun k hk => h k (Nat.lt_succ_of_lt hk)

/-- **Steps over ground already played are paid for by missed samples.** Let
every position be at least zero, and let the position advance by at least
`s` in every step of continuous playback. Up to output sample `K`, the
distance from the position played last to the largest position played, plus
`s` for every step of continuous playback that did not break new ground, is
at most the missed samples counted so far: a step back counts the frames
that it plays again, and every step of continuous playback after it recovers
at least `s` of the distance. -/
theorem replay_le_missed {s : ℝ} (hpos : ∀ k x, plays k = some x → 0 ≤ x)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y) :
    ∀ K, maxPlayed plays (K + 1) - (lastPlayed plays (K + 1)).getD 0
        + s * replayBefore plays K ≤ missedBefore plays (K + 1)
  | 0 => by
    have hr : replayBefore plays 0 = 0 := rfl
    have hM0 : maxPlayed plays 0 = 0 := rfl
    cases h0 : plays 0 with
    | none =>
      have hl : lastPlayed plays (0 + 1) = none := by
        rw [lastPlayed_succ_none h0]
        rfl
      rw [maxPlayed_succ_none h0, hl, hr, hM0]
      simp
    | some y =>
      have hy0 := hpos 0 y h0
      rw [maxPlayed_succ_some h0, lastPlayed_succ_some h0, hr, hM0, max_eq_left hy0]
      simp
  | K + 1 => by
    have ih := replay_le_missed hpos hslow K
    have e2 := missedBefore_succ plays (K + 1)
    have hm : (0 : ℝ) ≤ missedAt plays (K + 1) := Nat.cast_nonneg _
    cases hK1 : plays (K + 1) with
    | none =>
      have hc : ¬ (PlaysContinuously plays K ∧ ¬ NewGround plays K) := by
        rintro ⟨⟨_, y', _, hy', _, _⟩, -⟩
        rw [hK1] at hy'
        exact absurd hy' (by simp)
      rw [maxPlayed_succ_none hK1, lastPlayed_succ_none hK1, replayBefore_succ_of_not hc, e2]
      push_cast
      linarith
    | some y =>
      rw [maxPlayed_succ_some hK1, lastPlayed_succ_some hK1, e2]
      simp only [Option.getD_some]
      push_cast
      cases hl : lastPlayed plays (K + 1) with
      | none =>
        have hnone := eq_none_of_lastPlayed_none hl
        have hM : maxPlayed plays (K + 1) = 0 := maxPlayed_of_none hnone
        have hc : ¬ (PlaysContinuously plays K ∧ ¬ NewGround plays K) := by
          rintro ⟨⟨x', _, hx', _, _, _⟩, -⟩
          rw [hnone K (Nat.lt_succ_self K)] at hx'
          exact absurd hx' (by simp)
        rw [hl, hM] at ih
        simp only [Option.getD_none] at ih
        have hy0 := hpos (K + 1) y hK1
        rw [replayBefore_succ_of_not hc, hM, max_eq_left hy0]
        linarith
      | some x =>
        rw [hl] at ih
        simp only [Option.getD_some] at ih
        obtain ⟨-, hxplayed⟩ := lastPlayed_some hl
        have hxM : x ≤ maxPlayed plays (K + 1) := le_maxPlayed hxplayed (by omega)
        by_cases hcont : PlaysContinuously plays K
        · obtain ⟨x', y', hx', hy', h1, h2⟩ := hcont
          have hxx : x = x' := by
            have := lastPlayed_succ_some hx'
            rw [hl, Option.some.injEq] at this
            exact this
          have hyy : y' = y := by
            rw [hK1, Option.some.injEq] at hy'
            exact hy'.symm
          subst hxx hyy
          by_cases hng : NewGround plays K
          · have hc : ¬ (PlaysContinuously plays K ∧ ¬ NewGround plays K) := fun h => h.2 hng
            obtain ⟨_, y₂, _, hy₂, _, _, h3⟩ := hng
            rw [hK1, Option.some.injEq] at hy₂
            subst hy₂
            rw [replayBefore_succ_of_not hc, max_eq_left h3.le]
            linarith
          · have hle : y' ≤ maxPlayed plays (K + 1) := by
              by_contra hgt
              exact hng ⟨x, y', hx', hK1, h1, h2, not_le.mp hgt⟩
            have hadv := hslow K x y' hx' hK1 h1 h2
            rw [replayBefore_succ_of ⟨⟨x, y', hx', hK1, h1, h2⟩, hng⟩, max_eq_right hle]
            push_cast
            linarith
        · have hc : ¬ (PlaysContinuously plays K ∧ ¬ NewGround plays K) := fun h => hcont h.1
          have hmiss : x - y ≤ missedAt plays (K + 1) := by
            rw [missedAt_of_lastPlayed hK1 hl]
            push_cast
            have h1 : (0 : ℝ) ≤ ((⌊y - x - 1⌋ - (trailing plays (K + 1) : ℤ)).toNat : ℝ) :=
              Nat.cast_nonneg _
            have h2 : ((⌊1 - (y - x)⌋ : ℤ) : ℝ) ≤ ((⌊1 - (y - x)⌋.toNat : ℕ) : ℝ) := by
              exact_mod_cast Int.self_le_toNat _
            have h3 := Int.lt_floor_add_one (1 - (y - x))
            linarith
          rw [replayBefore_succ_of_not hc]
          rcases le_total y (maxPlayed plays (K + 1)) with hyM | hyM
          · rw [max_eq_right hyM]
            linarith
          · rw [max_eq_left hyM]
            linarith

/-- **Every step of continuous playback breaks new ground or goes over
ground already played.** Among the steps from output sample `a` to output
sample `b - 1`, those that break new ground and those of continuous playback
that do not are together the steps of continuous playback. -/
theorem newGroundCount_add_replay {a : ℕ} :
    ∀ b, a ≤ b →
      newGroundCount plays a b + replayBefore plays b + continuousBefore plays a
        = continuousBefore plays b + replayBefore plays a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base =>
    rw [(newGroundCount_of_le (plays := plays) a a le_rfl).1]
    omega
  | succ b hab ih =>
    by_cases hng : NewGround plays b
    · have hcont := hng.playsContinuously
      rw [newGroundCount_succ_of ⟨hab, hng⟩, continuousBefore_succ_of hcont,
        replayBefore_succ_of_not fun h => h.2 hng]
      omega
    · by_cases hcont : PlaysContinuously plays b
      · rw [newGroundCount_succ_of_not fun h => hng h.2, continuousBefore_succ_of hcont,
          replayBefore_succ_of ⟨hcont, hng⟩]
        omega
      · rw [newGroundCount_succ_of_not fun h => hng h.2, continuousBefore_succ_of_not hcont,
          replayBefore_succ_of_not fun h => hcont h.1]
        omega

/-! ## A sum over the frames on new ground -/

/-- The steps of a stretch that break new ground number at most the steps of
the stretch. -/
theorem newGroundCount_le {a : ℕ} : ∀ b, a ≤ b → newGroundCount plays a b ≤ b - a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => rw [(newGroundCount_of_le (plays := plays) a a le_rfl).1]; omega
  | succ b hab ih =>
    by_cases hng : a ≤ b ∧ NewGround plays b
    · rw [newGroundCount_succ_of hng]
      omega
    · rw [newGroundCount_succ_of_not hng]
      omega

/-- **What the frames on new ground are worth, with the losses spelled
out.** Let the position advance by at least `s`, with `0 ≤ s`, in every step
of continuous playback, and consider the steps from output sample `a` to
output sample `b - 1`. Suppose that each frame which those steps pass on new
ground is worth at least `max g 0`, and let `0 ≤ G ≤ Gcap` and `0 ≤ g'` be
numbers with `G - g' ≤ max g 0`. Then the frames together are worth at least `s * G` for
each step, minus `(1 + 2 s) * Gcap` for each step that does not break new
ground, minus `(1 + s) * Gcap` once, and minus `s * g'` for each step. -/
theorem le_card_newFrames_mul {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, plays k = some x → plays (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {a b : ℕ} (hab : a ≤ b) {g G Gcap g' : ℝ} (hG0 : 0 ≤ G) (hGcap : G ≤ Gcap)
    (hg' : 0 ≤ g') (hg : G - g' ≤ max g 0) :
    s * ((b : ℝ) - a) * G
        - ((1 + 2 * s) * ((b : ℝ) - a - newGroundCount plays a b) + (1 + s)) * Gcap
        - s * ((b : ℝ) - a) * g'
      ≤ ((newFrames plays a b).card : ℝ) * max g 0 := by
  have hcard := le_card_newFrames hs0 hslow hab
  have hP : (newGroundCount plays a b : ℝ) ≤ (b : ℝ) - a := by
    have h := newGroundCount_le (plays := plays) b hab
    have h' : ((newGroundCount plays a b : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hab] at h'
    exact h'
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hc0 : (0 : ℝ) ≤ ((newFrames plays a b).card : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ max g 0 := le_max_right _ _
  -- The two sides of the count: what all steps would give, and what is lost.
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = s * ((b : ℝ) - a) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ,
      L = (1 + 2 * s) * ((b : ℝ) - a - newGroundCount plays a b) + (1 + s) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg hs0 hba
  have hL0 : 0 ≤ L := by
    rw [hL]
    have : (0 : ℝ) ≤ (1 + 2 * s) * ((b : ℝ) - a - newGroundCount plays a b) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hAL : A - L ≤ ((newFrames plays a b).card : ℝ) := by
    rw [hA, hL]
    linarith
  rw [← hA, ← hL]
  rcases le_total L A with hLA | hAL'
  · have h1 : (A - L) * (G - g') ≤ (A - L) * max g 0 :=
      mul_le_mul_of_nonneg_left hg (by linarith)
    have h2 : (A - L) * max g 0 ≤ ((newFrames plays a b).card : ℝ) * max g 0 :=
      mul_le_mul_of_nonneg_right hAL hM0
    have h3 : 0 ≤ L * (Gcap - G) := mul_nonneg hL0 (by linarith)
    have h4 : 0 ≤ L * g' := mul_nonneg hL0 hg'
    nlinarith
  · have h1 : 0 ≤ ((newFrames plays a b).card : ℝ) * max g 0 := mul_nonneg hc0 hM0
    have h2 : A * G ≤ A * Gcap := mul_le_mul_of_nonneg_left hGcap hA0
    have h3 : A * Gcap ≤ L * Gcap := mul_le_mul_of_nonneg_right hAL' (by linarith)
    have h4 : 0 ≤ A * g' := mul_nonneg hA0 hg'
    linarith

/-! ## The frames on new ground of different stretches -/

/-- A frame on new ground of a step of a stretch is one of the frames of the
stretch. -/
theorem mem_newFrames_of {a k n : ℕ} (hak : a ≤ k) (hng : NewGround plays k)
    (hlo : maxPlayed plays (k + 1) < n) (hhi : (n : ℝ) ≤ maxPlayed plays (k + 1 + 1)) :
    ∀ c, k < c → n ∈ newFrames plays a c
  | 0, h => absurd h (Nat.not_lt_zero k)
  | j + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · have ih := mem_newFrames_of hak hng hlo hhi j hlt
      by_cases hc : a ≤ j ∧ NewGround plays j
      · rw [newFrames_succ_of hc]
        exact Finset.mem_union_left _ ih
      · rw [newFrames_succ_of_not hc]
        exact ih
    · rw [newFrames_succ_of ⟨hak, hng⟩]
      refine Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨?_, ?_⟩)
      · exact (Nat.floor_lt (maxPlayed_nonneg plays (k + 1))).mpr hlo
      · exact (Nat.le_floor_iff (maxPlayed_nonneg plays (k + 1 + 1))).mpr hhi

/-- A longer stretch has the frames on new ground of a shorter one inside
it. -/
theorem newFrames_subset {a a' c c' : ℕ} (ha : a' ≤ a) (hc : c ≤ c') :
    newFrames plays a c ⊆ newFrames plays a' c' := by
  intro n hn
  obtain ⟨k, hak, hkc, hng, hlo, hhi⟩ := exists_of_mem_newFrames a c n hn
  exact mem_newFrames_of (ha.trans hak) hng hlo hhi c' (lt_of_lt_of_le hkc hc)

/-- Two stretches of which the second starts where the first ends, or later,
have no frame on new ground in common. -/
theorem disjoint_newFrames {a b c e : ℕ} (hbc : b ≤ c) :
    Disjoint (newFrames plays a b) (newFrames plays c e) := by
  rw [Finset.disjoint_left]
  intro n h1 h2
  have hle := le_floor_of_mem_newFrames a b n h1
  obtain ⟨k, hck, -, -, hlo, -⟩ := exists_of_mem_newFrames c e n h2
  have hmono := maxPlayed_mono plays (show b + 1 ≤ k + 1 by omega)
  have hfl : ((⌊maxPlayed plays (b + 1)⌋₊ : ℕ) : ℝ) ≤ maxPlayed plays (b + 1) :=
    Nat.floor_le (maxPlayed_nonneg plays (b + 1))
  have hn : (n : ℝ) ≤ ((⌊maxPlayed plays (b + 1)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hle
  linarith

/-- **The frames on new ground of the blocks, summed block by block.** For
blocks of `B` output samples and any cost of a frame that is not negative,
the costs of the frames that the steps inside each of the first `N` blocks
pass on new ground, summed over the blocks, are at most the costs of the
frames that the steps before output sample `N * B` pass on new ground. The
steps from the last output sample of a block to the first of the next are
left out on the left. -/
theorem sum_blocks_newFrames_le (g : ℕ → ENNReal) (B : ℕ) :
    ∀ N, ∑ b ∈ Finset.range N, ∑ n ∈ newFrames plays (b * B) ((b + 1) * B - 1), g n
      ≤ ∑ n ∈ newFrames plays 0 (N * B), g n
  | 0 => by simp
  | N + 1 => by
    have ih := sum_blocks_newFrames_le g B N
    have hsub₁ : newFrames plays 0 (N * B) ⊆ newFrames plays 0 ((N + 1) * B) :=
      newFrames_subset le_rfl (Nat.mul_le_mul_right B (Nat.le_succ N))
    have hsub₂ : newFrames plays (N * B) ((N + 1) * B - 1)
        ⊆ newFrames plays 0 ((N + 1) * B) :=
      newFrames_subset (Nat.zero_le _) (Nat.sub_le _ _)
    have hdisj : Disjoint (newFrames plays 0 (N * B))
        (newFrames plays (N * B) ((N + 1) * B - 1)) := disjoint_newFrames le_rfl
    rw [Finset.sum_range_succ]
    calc ∑ b ∈ Finset.range N, ∑ n ∈ newFrames plays (b * B) ((b + 1) * B - 1), g n
          + ∑ n ∈ newFrames plays (N * B) ((N + 1) * B - 1), g n
        ≤ ∑ n ∈ newFrames plays 0 (N * B), g n
          + ∑ n ∈ newFrames plays (N * B) ((N + 1) * B - 1), g n := add_le_add ih le_rfl
      _ = ∑ n ∈ newFrames plays 0 (N * B) ∪ newFrames plays (N * B) ((N + 1) * B - 1), g n :=
          (Finset.sum_union hdisj).symm
      _ ≤ ∑ n ∈ newFrames plays 0 ((N + 1) * B), g n :=
          Finset.sum_le_sum_of_subset (Finset.union_subset hsub₁ hsub₂)

end Unisono.Spec
