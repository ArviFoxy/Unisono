/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.FollowerCost

/-!
# Missed samples and discontinuities of a solution with the follower

`Unisono.Spec.FollowerCost` bounds the missed samples and the
discontinuities of playback that follows a target, for sequences. This file
applies it to the run of a solution with the follower
(`Solution.followed`), in any world in which the requests of a speaker's
device are handled without end.

The target is what the wrapped solution `σ` chooses for each output sample
(`Solution.chosen`). Where `σ` chooses nothing, the target is filled in:
it advances by one frame from the output sample before (`heldTarget`). So a
stretch in which `σ` chooses nothing has regular steps, and the step at
which `σ` chooses a position again carries the whole distance between that
position and where the target would be had it advanced by one frame per
output sample.

* `Solution.followed_follows`: the three sequences of a run satisfy
  `Follows`.
* `Solution.plays_none_or_chosen`: a speaker plays what the solution
  chooses, or nothing.
* `Solution.followed_sum_missedAt_le`, `Solution.followed_sum_discontinuityAt_le`:
  for `0 ≤ u < 1 ≤ J`, the missed samples and the discontinuities of a
  speaker are bounded by the number of its output samples that play nothing
  and by the excesses of the steps of the filled-in target
  (`stepExcess`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type}

/-- A target with the output samples at which it is unknown filled in:
where it is unknown, it advances by one frame from the output sample
before. -/
def heldTarget (X : ℕ → Option ℝ) : ℕ → ℝ
  | 0 => (X 0).getD 0
  | k + 1 => (X (k + 1)).getD (heldTarget X k + 1)

/-- The filled-in target is the target wherever the target is known. -/
theorem heldTarget_eq (X : ℕ → Option ℝ) (k : ℕ) :
    X k = none ∨ X k = some (heldTarget X k) := by
  cases k with
  | zero =>
    cases h : X 0 with
    | none => exact Or.inl rfl
    | some x => exact Or.inr (by simp [heldTarget, h])
  | succ k =>
    cases h : X (k + 1) with
    | none => exact Or.inl rfl
    | some x => exact Or.inr (by simp [heldTarget, h])

/-- A step of the filled-in target to an output sample at which the target
is unknown is regular. -/
theorem stepExcess_heldTarget_of_none {u J : ℝ} (hu : 0 ≤ u) {X : ℕ → Option ℝ} {k : ℕ}
    (h : X (k + 1) = none) : stepExcess u J (heldTarget X) k = 0 := by
  have e : heldTarget X (k + 1) = heldTarget X k + 1 := by simp [heldTarget, h]
  unfold stepExcess
  rw [e, ite_eq_right]
  rw [show heldTarget X k + 1 - heldTarget X k - 1 = 0 by ring, abs_zero]
  exact not_lt.mpr hu

variable [DecidableEq H] (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)

/-- Output sample zero belongs to block zero. -/
theorem PlaybackDevice.zero_mem_block (d : PlaybackDevice) : 0 ∈ d.block 0 := by
  unfold PlaybackDevice.block
  rw [List.mem_range'_1, d.first_zero]
  have := d.first_strictMono (Nat.lt_add_one 0)
  rw [d.first_zero] at this
  omega

/-- **The first output sample of the solution with a rule.** At output
sample zero the rule has no previous value: the solution with the rule
chooses the rule's step from nothing and from what `σ` chooses. -/
theorem Solution.stepped_chosen_zero (g : Option ℝ → Option ℝ → Option ℝ) {n : ℕ} {r : Fin R}
    (he : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r 0)) :
    (σ.stepped g).chosen w lookahead r 0 = g none (σ.chosen w lookahead r 0) := by
  have hb := σ.askedNext_of_earliest w lookahead he
  have hs := (σ.stepped_asked_iff g w lookahead n r 0).mpr ⟨hb, he⟩
  have hk0 := (w.speaker r).zero_mem_block
  rw [(σ.stepped g).chosen_eq w lookahead hk0 hs.2, σ.chosen_eq w lookahead hk0 he,
    σ.stepped_chosenAt g w lookahead n r 0 0]
  -- No request of the speaker is in the view yet.
  have hreq := σ.requestsOf_views w lookahead r n
  rw [hb] at hreq
  have hnone : ∀ e ∈ (σ.states w lookahead n).views (w.host r),
      ∀ outputs s, e.observation ≠ .asked r outputs s := by
    intro e hemem outputs s hobs
    have hmem : e ∈ requestsOf r ((σ.states w lookahead n).views (w.host r)) := by
      unfold requestsOf
      rw [List.mem_filter]
      exact ⟨hemem, by simp [hobs]⟩
    rw [hreq] at hmem
    simp at hmem
  have hcar : carried σ g (w.host r) ((σ.states w lookahead n).views (w.host r)) r = none := by
    have h1 := carried_append_of_ne σ g (w.host r) [] r
      ((σ.states w lookahead n).views (w.host r)) hnone
    rw [List.nil_append] at h1
    rw [h1]
    rfl
  rw [hcar]
  obtain ⟨m, hm⟩ : ∃ m, (w.speaker r).first (0 + 1) - (w.speaker r).first 0 = m + 1 :=
    ⟨(w.speaker r).first (0 + 1) - (w.speaker r).first 0 - 1, by
      have := (w.speaker r).first_strictMono (Nat.lt_add_one 0)
      omega⟩
  unfold PlaybackDevice.block
  rw [hm, (w.speaker r).first_zero, stepAt_range'_first]

/-- **The sequences of a run with the follower.** Let the run of `σ` handle
every request of the device of speaker `r`. Then what `σ` chooses for the
speaker's output samples, that target with its unknown values filled in,
and what the solution with the follower chooses satisfy `Follows`. -/
theorem Solution.followed_follows (u J : ℝ) {r : Fin R}
    (hprog : ∀ b, ∃ n, earliest ((σ.states w lookahead n).key w)
      (σ.states w lookahead n).due = some (.asked r b)) :
    Follows u J (heldTarget (σ.chosen w lookahead r)) (σ.chosen w lookahead r)
      ((σ.followed u J).chosen w lookahead r) where
  target := heldTarget_eq _
  start := by
    obtain ⟨n, hn⟩ := hprog 0
    have h := σ.stepped_chosen_zero w lookahead (followStep u J) hn
    rw [followStep_none_left] at h
    exact h
  step := fun k => by
    obtain ⟨n₁, h₁⟩ := hprog ((w.speaker r).blockOf k)
    obtain ⟨n₂, h₂⟩ := hprog ((w.speaker r).blockOf (k + 1))
    exact σ.stepped_chosen_succ w lookahead (followStep u J) h₁ h₂

/-- **A speaker plays what the solution chooses, or nothing.** -/
theorem Solution.plays_none_or_chosen {r : Fin R}
    (hprog : ∀ b, ∃ n, earliest ((σ.states w lookahead n).key w)
      (σ.states w lookahead n).due = some (.asked r b)) (k : ℕ) :
    σ.plays w lookahead r k = none ∨ σ.plays w lookahead r k = σ.chosen w lookahead r k := by
  classical
  obtain ⟨n, hn⟩ := hprog ((w.speaker r).blockOf k)
  rw [σ.plays_eq_playable_chosen w lookahead ((w.speaker r).mem_blockOf k) hn]
  cases hc : σ.chosen w lookahead r k with
  | none => exact Or.inl rfl
  | some x =>
    unfold playable
    simp only
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The run of the solution with the follower handles every request that
the run of the solution handles. -/
theorem Solution.followed_progress (u J : ℝ) {r : Fin R}
    (hprog : ∀ b, ∃ n, earliest ((σ.states w lookahead n).key w)
      (σ.states w lookahead n).due = some (.asked r b)) (b : ℕ) :
    ∃ n, earliest (((σ.followed u J).states w lookahead n).key w)
      ((σ.followed u J).states w lookahead n).due = some (.asked r b) := by
  obtain ⟨n, hn⟩ := hprog b
  exact ⟨n, ((σ.stepped_asked_iff (followStep u J) w lookahead n r b).mpr
    ⟨σ.askedNext_of_earliest w lookahead hn, hn⟩).2⟩

/-- **The missed samples of a speaker of a solution with the follower.** Let
`0 ≤ u < 1 ≤ J`, and let the run of `σ` handle every request of the device
of speaker `r`. The missed samples counted at the speaker's output samples
before `K` are at most `1 + 2 * J + 2 * u` times the number of those output
samples that play nothing, plus twice the sum of the excesses of the steps
of the filled-in target before `K`. -/
theorem Solution.followed_sum_missedAt_le {u J : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (hJ : 1 ≤ J)
    {r : Fin R}
    (hprog : ∀ b, ∃ n, earliest ((σ.states w lookahead n).key w)
      (σ.states w lookahead n).due = some (.asked r b)) (K : ℕ) :
    ∑ k ∈ Finset.range K, (missedAt ((σ.followed u J).plays w lookahead r) k : ℝ)
      ≤ (1 + 2 * J + 2 * u)
          * ∑ k ∈ Finset.range K, (missingAt ((σ.followed u J).plays w lookahead r) k : ℝ)
        + 2 * ∑ i ∈ Finset.range K,
            stepExcess u J (heldTarget (σ.chosen w lookahead r)) i :=
  (σ.followed_follows w lookahead u J hprog).sum_missedAt_le hu hu1 hJ
    ((σ.followed u J).plays_none_or_chosen w lookahead
      (σ.followed_progress w lookahead u J hprog)) K

/-- **The discontinuities of a speaker of a solution with the follower.**
In the setting of `Solution.followed_sum_missedAt_le`, the discontinuities
counted at the speaker's output samples before `K` are at most the number
of its output samples up to `K` that play nothing, plus the sum of the
excesses of the steps of the filled-in target before `K`. -/
theorem Solution.followed_sum_discontinuityAt_le {u J : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hJ : 1 ≤ J) {r : Fin R}
    (hprog : ∀ b, ∃ n, earliest ((σ.states w lookahead n).key w)
      (σ.states w lookahead n).due = some (.asked r b)) (K : ℕ) :
    ∑ k ∈ Finset.range K, (discontinuityAt ((σ.followed u J).plays w lookahead r) k : ℝ)
      ≤ ∑ k ∈ Finset.range (K + 1),
          (missingAt ((σ.followed u J).plays w lookahead r) k : ℝ)
        + ∑ i ∈ Finset.range K, stepExcess u J (heldTarget (σ.chosen w lookahead r)) i :=
  (σ.followed_follows w lookahead u J hprog).sum_discontinuityAt_le hu hu1 hJ
    ((σ.followed u J).plays_none_or_chosen w lookahead
      (σ.followed_progress w lookahead u J hprog)) K

end Unisono.Spec
