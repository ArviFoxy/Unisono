/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Follower
public import Unisono.Spec.OwnEvents

/-!
# The follower, output sample by output sample

`Unisono.Spec.Follower` states what the follower does at a request of a
playback device. This file states it along the whole run of a speaker, as
two sequences indexed by the output sample.

* `Solution.chosen σ w lookahead r k` is what the solution `σ` chooses for
  output sample `k` of speaker `r`, at the step of its run that handles the
  request of the block of `k`; it is nothing if no step handles that request
  (`Solution.chosen_eq`). What the speaker plays is that position if the
  host holds the frames around it (`Solution.plays_eq_playable_chosen`).
* `Solution.stepped_chosen_succ`: what the solution with a rule chooses for
  an output sample is the rule's step from what it chose for the output
  sample before and from what `σ` chooses for this one.
* `followStep_gap`: one step of the follower. With `y` the previous value,
  `x` the position that `σ` chooses and `z` what the follower gives: `z` is
  at most `max (|x - y - 1| - u) 0` from `x`; if `x` is within `J` frames of
  one frame after `y`, then `z` is one frame after `y` within `u`; otherwise
  `z` is `x`.
* `PlaybackDevice.blockOf`: the block of an output sample.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ} {Msg : Type}

/-- An output sample belongs to one block of a playback device only. -/
theorem PlaybackDevice.block_unique (d : PlaybackDevice) {k b b' : ℕ} (h : k ∈ d.block b)
    (h' : k ∈ d.block b') : b = b' := by
  unfold PlaybackDevice.block at h h'
  rw [List.mem_range'_1] at h h'
  have hm := d.first_strictMono
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · have h1 : d.first (b + 1) ≤ d.first b' := hm.monotone hlt
    have h2 : d.first b ≤ d.first (b + 1) := (hm (Nat.lt_succ_self b)).le
    omega
  · exact heq
  · have h1 : d.first (b' + 1) ≤ d.first b := hm.monotone hgt
    have h2 : d.first b' ≤ d.first (b' + 1) := (hm (Nat.lt_succ_self b')).le
    omega

/-- Every output sample belongs to a block of its playback device. -/
theorem PlaybackDevice.exists_block (d : PlaybackDevice) (k : ℕ) : ∃ b, k ∈ d.block b := by
  classical
  have hm := d.first_strictMono
  have hex : ∃ b, k < d.first (b + 1) := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (hm.id_le (k + 1))⟩
  refine ⟨Nat.find hex, ?_⟩
  have hspec := Nat.find_spec hex
  have hlow : d.first (Nat.find hex) ≤ k := by
    cases hb : Nat.find hex with
    | zero =>
      rw [d.first_zero]
      exact Nat.zero_le k
    | succ b =>
      have hmin := Nat.find_min hex (show b < Nat.find hex by omega)
      exact not_lt.mp hmin
  unfold PlaybackDevice.block
  rw [List.mem_range'_1]
  have h2 : d.first (Nat.find hex) ≤ d.first (Nat.find hex + 1) := (hm (Nat.lt_succ_self _)).le
  omega

open Classical in
/-- The block of an output sample of a playback device. -/
def PlaybackDevice.blockOf (d : PlaybackDevice) (k : ℕ) : ℕ := Nat.find (d.exists_block k)

/-- An output sample belongs to its block. -/
theorem PlaybackDevice.mem_blockOf (d : PlaybackDevice) (k : ℕ) : k ∈ d.block (d.blockOf k) := by
  classical
  exact Nat.find_spec (d.exists_block k)

/-- The block of an output sample is the block that it belongs to. -/
theorem PlaybackDevice.blockOf_eq (d : PlaybackDevice) {k b : ℕ} (h : k ∈ d.block b) :
    d.blockOf k = b :=
  d.block_unique (d.mem_blockOf k) h

/-- **One step of the follower.** Let `y` be the previous value, `x` the
position that the solution chooses, and `z` what the follower gives.

* `z` is at most `max (|x - y - 1| - u) 0` from `x`.
* If `x` is within `J` frames of one frame after `y`, then `z` is one frame
  after `y` within `u`, for `u ≥ 0`.
* If `x` is further than `J` frames from one frame after `y`, then `z` is
  `x`. -/
theorem followStep_gap {u J y x z : ℝ} (h : followStep u J (some y) (some x) = some z) :
    |z - x| ≤ max (|x - y - 1| - u) 0
      ∧ (0 ≤ u → |x - y - 1| ≤ J → |z - y - 1| ≤ u)
      ∧ (J < |x - y - 1| → z = x) := by
  simp only [followStep] at h
  by_cases h3 : |x - y - 1| ≤ u
  · rw [ite_eq_left h3] at h
    obtain rfl := Option.some.inj h
    refine ⟨?_, fun _ _ => h3, fun _ => rfl⟩
    rw [sub_self, abs_zero]
    exact le_max_right _ _
  · rw [ite_eq_right h3] at h
    by_cases h4 : |x - y - 1| ≤ J
    · rw [ite_eq_left h4] at h
      obtain rfl := Option.some.inj h
      have h7 := not_le.mp h3
      by_cases h5 : y + 1 < x
      · rw [ite_eq_left h5]
        have h6 : u < x - y - 1 := by rwa [abs_of_pos (by linarith)] at h7
        refine ⟨le_max_of_le_left ?_, fun hu _ => ?_, fun hJ => absurd h4 (not_le.mpr hJ)⟩
        · rw [abs_of_nonpos (by linarith), abs_of_pos (by linarith)]
          linarith
        · rw [show y + 1 + u - y - 1 = u by ring, abs_of_nonneg hu]
      · rw [ite_eq_right h5]
        have h6 : u < -(x - y - 1) := by rwa [abs_of_nonpos (by linarith)] at h7
        refine ⟨le_max_of_le_left ?_, fun hu _ => ?_, fun hJ => absurd h4 (not_le.mpr hJ)⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
        · rw [show y + 1 + -u - y - 1 = -u by ring, abs_neg, abs_of_nonneg hu]
    · rw [ite_eq_right h4] at h
      obtain rfl := Option.some.inj h
      refine ⟨?_, fun _ hJ => absurd hJ h4, fun _ => rfl⟩
      rw [sub_self, abs_zero]
      exact le_max_right _ _

variable [DecidableEq H] (σ : Solution H R Msg) (w : World H R) (lookahead : ℕ+)

open Classical in
/-- What the solution chooses for output sample `k` of speaker `r`: what it
chooses at the step of its run that handles the request of the block of
`k`, before the resampler checks that the frames are held. It is nothing if
no step handles that request. -/
def Solution.chosen (r : Fin R) (k : ℕ) : Option ℝ :=
  if h : ∃ n, earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r ((w.speaker r).blockOf k))
  then σ.chosenAt w lookahead (Classical.choose h) r ((w.speaker r).blockOf k) k
  else none

/-- At a step that handles the request of the block of output sample `k`,
the solution chooses `Solution.chosen` for `k`. -/
theorem Solution.chosen_eq {n : ℕ} {r : Fin R} {b k : ℕ} (hk : k ∈ (w.speaker r).block b)
    (he : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r b)) :
    σ.chosen w lookahead r k = σ.chosenAt w lookahead n r b k := by
  classical
  obtain rfl := (w.speaker r).blockOf_eq hk
  have hex : ∃ n, earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r ((w.speaker r).blockOf k)) := ⟨n, he⟩
  have hu : Classical.choose hex = n :=
    σ.asked_step_unique w lookahead
      (σ.askedNext_of_earliest w lookahead (Classical.choose_spec hex))
      (Classical.choose_spec hex) (σ.askedNext_of_earliest w lookahead he) he
  unfold Solution.chosen
  rw [dite_eq_left hex, hu]

/-- **What a speaker plays is what the solution chooses, if the request is
handled in time and the frames are held.** At the step that handles the
request of the block of output sample `k`, the speaker plays the position
that the solution chooses for `k` if the output sample has not left yet and
the host holds every frame less than the lookahead away from the position,
and nothing of the source otherwise. -/
theorem Solution.plays_eq_playable_chosen {n : ℕ} {r : Fin R} {b k : ℕ}
    (hk : k ∈ (w.speaker r).block b)
    (he : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r b)) :
    σ.plays w lookahead r k
      = if (w.speaker r).asked b < (w.speaker r).out k then
          playable lookahead ((σ.states w lookahead n).held (w.host r))
            (σ.chosen w lookahead r k)
        else none := by
  rw [σ.chosen_eq w lookahead hk he]
  exact Solution.plays_of_asked_step w σ lookahead
    (σ.askedNext_of_earliest w lookahead he) he hk

/-- **The solution with a rule, output sample by output sample.** When the
run handles the requests of the blocks of output samples `k` and `k + 1` of
speaker `r`, what the solution with the rule `g` chooses for `k + 1` is `g`
of what it chooses for `k` and of what `σ` chooses for `k + 1`. -/
theorem Solution.stepped_chosen_succ (g : Option ℝ → Option ℝ → Option ℝ) {n₁ n₂ : ℕ}
    {r : Fin R} {k : ℕ}
    (he₁ : earliest ((σ.states w lookahead n₁).key w) (σ.states w lookahead n₁).due
      = some (.asked r ((w.speaker r).blockOf k)))
    (he₂ : earliest ((σ.states w lookahead n₂).key w) (σ.states w lookahead n₂).due
      = some (.asked r ((w.speaker r).blockOf (k + 1)))) :
    (σ.stepped g).chosen w lookahead r (k + 1)
      = g ((σ.stepped g).chosen w lookahead r k) (σ.chosen w lookahead r (k + 1)) := by
  have hb₁ := σ.askedNext_of_earliest w lookahead he₁
  have hb₂ := σ.askedNext_of_earliest w lookahead he₂
  have hs₁ := (σ.stepped_asked_iff g w lookahead n₁ r ((w.speaker r).blockOf k)).mpr ⟨hb₁, he₁⟩
  have hs₂ := (σ.stepped_asked_iff g w lookahead n₂ r
    ((w.speaker r).blockOf (k + 1))).mpr ⟨hb₂, he₂⟩
  rw [(σ.stepped g).chosen_eq w lookahead ((w.speaker r).mem_blockOf (k + 1)) hs₂.2,
    (σ.stepped g).chosen_eq w lookahead ((w.speaker r).mem_blockOf k) hs₁.2,
    σ.chosen_eq w lookahead ((w.speaker r).mem_blockOf (k + 1)) he₂]
  exact σ.stepped_chosenAt_succ g w lookahead hb₁ he₁ ((w.speaker r).mem_blockOf k) hb₂ he₂
    ((w.speaker r).mem_blockOf (k + 1))

end Unisono.Spec
