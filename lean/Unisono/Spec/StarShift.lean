/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.ExactLatency

/-!
# What a star solution cannot tell apart, and what it costs

A star solution exchanges messages only with the sender. Shift the timelines
of the hosts along the links to and from the sender, and keep the links
between the other hosts as they are. A star solution plays the same in the
world before the shift and in the world after it
(`Solution.plays_shiftStarKeepPeers`), yet every speaker's play times move
with the timeline of its host. The solution therefore cannot be right in
both worlds.

* `shiftCost c x` is what a shift `x` of the speakers' play times costs at
  one frame: the weight of synchronization times the variance of the shifts
  across the speakers, plus the weight of tracking times the mean of their
  squares.
* Whatever latencies the speakers have before, the frame costs with the
  latencies shifted by `x` and by `-x` add up to at least twice the cost of
  the shift (`two_mul_shiftCost_le`).
* **The costs in the two worlds add up to at least twice the cost of half the
  shift** (`Solution.cost_shiftStarKeepPeers_add_ge`). The number of hosts
  and of speakers is arbitrary.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal NNReal
open Filter Topology

variable {H : Type} {R : ℕ}

/-! ## The cost of a shift at one frame -/

/-- What a shift `x` of the speakers' play times costs at one frame, for
weights `c`: `c.sync` times the variance of the shifts across the speakers,
plus `c.tracking` times the mean of their squares. -/
def shiftCost (c : Weights) (x : Fin R → ℝ) : ℝ :=
  (c.sync : ℝ) * varFin x + (c.tracking : ℝ) * ((∑ r : Fin R, x r ^ 2) / R)

theorem shiftCost_nonneg (c : Weights) (x : Fin R → ℝ) : 0 ≤ shiftCost c x := by
  unfold shiftCost varFin
  have h1 : 0 ≤ (∑ r : Fin R, (x r - meanFin x) ^ 2) / (R : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg R)
  have h2 : 0 ≤ (∑ r : Fin R, x r ^ 2) / (R : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg R)
  have hs : (0 : ℝ) ≤ c.sync := c.sync.coe_nonneg
  have ht : (0 : ℝ) ≤ c.tracking := c.tracking.coe_nonneg
  positivity

/-- The weighted synchronization and tracking cost of a frame that the
speakers play with latencies `ℓ`, when its target latency is `t`
(`World.weighted_frame_modal_split`). -/
def frameCost (c : Weights) (ℓ : Fin R → ℝ) (t : ℝ) : ℝ :=
  ((c.sync : ℝ) + (c.tracking : ℝ)) * varFin ℓ + (c.tracking : ℝ) * (meanFin ℓ - t) ^ 2

theorem frameCost_nonneg (c : Weights) (ℓ : Fin R → ℝ) (t : ℝ) : 0 ≤ frameCost c ℓ t := by
  unfold frameCost
  have hvar : 0 ≤ varFin ℓ :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg R)
  have hs : (0 : ℝ) ≤ c.sync := c.sync.coe_nonneg
  have ht : (0 : ℝ) ≤ c.tracking := c.tracking.coe_nonneg
  positivity

theorem meanFin_add (a b : Fin R → ℝ) :
    meanFin (fun r => a r + b r) = meanFin a + meanFin b := by
  unfold meanFin
  rw [Finset.sum_add_distrib, add_div]

theorem meanFin_sub (a b : Fin R → ℝ) :
    meanFin (fun r => a r - b r) = meanFin a - meanFin b := by
  unfold meanFin
  rw [Finset.sum_sub_distrib, sub_div]

/-- The variances of a sum and of a difference add up to twice the two
variances. -/
theorem varFin_add_add_varFin_sub (a b : Fin R → ℝ) :
    varFin (fun r => a r + b r) + varFin (fun r => a r - b r)
      = 2 * varFin a + 2 * varFin b := by
  unfold varFin
  rw [meanFin_add, meanFin_sub, ← add_div, ← Finset.sum_add_distrib]
  have hpt : ∀ r : Fin R,
      (a r + b r - (meanFin a + meanFin b)) ^ 2 + (a r - b r - (meanFin a - meanFin b)) ^ 2
        = 2 * (a r - meanFin a) ^ 2 + 2 * (b r - meanFin b) ^ 2 := fun r => by ring
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **A shift and its opposite cost at least twice the shift's own cost.**
Whatever latencies `ℓ` the speakers have and whatever the target `t` is, the
frame costs with the latencies shifted by `x` and by `-x` add up to at least
`2 * shiftCost c x`. -/
theorem two_mul_shiftCost_le (c : Weights) (hR : 0 < R) (ℓ x : Fin R → ℝ) (t : ℝ) :
    2 * shiftCost c x
      ≤ frameCost c (fun r => ℓ r + x r) t + frameCost c (fun r => ℓ r - x r) t := by
  have hs : (0 : ℝ) ≤ c.sync := c.sync.coe_nonneg
  have ht : (0 : ℝ) ≤ c.tracking := c.tracking.coe_nonneg
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hvarℓ : 0 ≤ varFin ℓ :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hRpos.le
  have hvar := varFin_add_add_varFin_sub ℓ x
  have hsplit := modal_sq_split hR x
  unfold shiftCost frameCost
  rw [meanFin_add, meanFin_sub, hsplit]
  have hsq : (meanFin ℓ + meanFin x - t) ^ 2 + (meanFin ℓ - meanFin x - t) ^ 2
      = 2 * (meanFin ℓ - t) ^ 2 + 2 * meanFin x ^ 2 := by ring
  nlinarith [mul_nonneg (add_nonneg hs ht) hvarℓ, mul_nonneg ht (sq_nonneg (meanFin ℓ - t))]

/-! ## The cost accrued by frames -/

theorem World.accruedFrames_mono (w : World H R) {f g : ℕ → ℝ≥0∞} (h : ∀ n, f n ≤ g n)
    (T : Time) : w.accruedFrames f T ≤ w.accruedFrames g T := by
  unfold World.accruedFrames
  refine tsum_le_tsum fun n => ?_
  split_ifs
  · exact mul_le_mul_left (h n) _
  · exact le_rfl

theorem World.accruedFrames_weighted (w : World H R) (a b : ℝ≥0∞) (f g : ℕ → ℝ≥0∞) (T : Time) :
    a * w.accruedFrames f T + b * w.accruedFrames g T
      = w.accruedFrames (fun n => a * f n + b * g n) T := by
  unfold World.accruedFrames
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add]
  refine tsum_congr fun n => ?_
  split_ifs
  · ring
  · simp

/-- **The cost is at least the long-run average of any lower bound on the
weighted synchronization and tracking of each frame.** -/
theorem World.longRun_frames_le_cost (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) (g : ℕ → ℝ≥0∞)
    (hg : ∀ n, g n ≤ (c.sync : ℝ≥0∞) * w.syncCost plays n
      + (c.tracking : ℝ≥0∞) * w.trackingCost plays n) :
    longRun (w.accruedFrames g) ≤ w.cost plays c := by
  unfold World.cost longRun
  apply Filter.limsup_le_limsup
  · refine Eventually.of_forall fun T => ENNReal.div_le_div_right ?_ _
    calc w.accruedFrames g T
        ≤ w.accruedFrames (fun n => (c.sync : ℝ≥0∞) * w.syncCost plays n
            + (c.tracking : ℝ≥0∞) * w.trackingCost plays n) T := w.accruedFrames_mono hg T
      _ = (c.sync : ℝ≥0∞) * w.accruedFrames (w.syncCost plays) T
            + (c.tracking : ℝ≥0∞) * w.accruedFrames (w.trackingCost plays) T :=
          (w.accruedFrames_weighted _ _ _ _ T).symm
      _ ≤ _ := by
          have h1 : (c.sync : ℝ≥0∞) * w.accruedFrames (w.syncCost plays) T
              + (c.tracking : ℝ≥0∞) * w.accruedFrames (w.trackingCost plays) T
              ≤ (c.sync : ℝ≥0∞) * w.accruedFrames (w.syncCost plays) T
                + (c.latency : ℝ≥0∞) * w.accruedFrames (w.latencyCost plays) T
                + (c.tracking : ℝ≥0∞) * w.accruedFrames (w.trackingCost plays) T := by
            rw [add_right_comm]
            exact le_self_add
          exact h1.trans (le_self_add.trans (le_self_add.trans le_self_add))
  · exact isCoboundedUnder_le_of_le atTop (x := 0) (fun _ => zero_le)
  · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩

/-! ## A star solution in two worlds that differ by a shift -/

section Star

variable [DecidableEq H] {Msg : Type}

omit [DecidableEq H] in
/-- Under a shift of the star links, an identical playback shifts speaker
`r`'s play time of each frame with the timeline of the speaker's host. -/
theorem playTime_shiftStarKeepPeers [DecidableEq H] (w : World H R) (Δ : H → ℝ)
    (hstar : ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + Δ i < a + Δ j)
    (plays : Fin R → ℕ → Option ℝ) (r : Fin R) (n : ℕ) :
    (shiftStarKeepPeers w Δ hstar).playTime plays r n
      = (w.playTime plays r n).map (· + Δ (w.host r)) := by
  classical
  unfold World.playTime Unisono.Spec.playTime
  split_ifs with h
  · cases hx : plays r (Nat.find h) <;> cases hy : plays r (Nat.find h + 1) <;> simp
    simp only [shiftStarKeepPeers]
    ring
  · simp

/-- **A star solution pays in one of two worlds that it cannot tell apart.**
Let `w` be a world and `X` a shift of the hosts' timelines along the links to
and from the sender, which leaves the sender's timeline in place. Let `σ` be
a star solution that makes progress in `w` and in the shifted world, in whose
run in `w` no two messages from different hosts arrive at one host at the
same time, and which plays every frame from frame `N` on in `w`. Then the
costs of `σ` in `w` and in the shifted world add up to at least twice
`shiftCost c` of half the speakers' shifts. -/
theorem Solution.cost_shiftStarKeepPeers_add_ge (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) (c : Weights) (hstar : σ.IsStar w.sender) (X : H → ℝ)
    (hXs : X w.sender = 0)
    (hstar₁ : ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + X i < a + X j)
    (hprog : ∀ T : Time, ∃ n, T < σ.eventTime w lookahead n)
    (hprog₁ : ∀ T : Time, ∃ n, T < σ.eventTime (shiftStarKeepPeers w X hstar₁) lookahead n)
    (harr : σ.NoCrossOriginCollision w lookahead) (hR : 0 < R) (N : ℕ)
    (hplay : ∀ n, N ≤ n → ∀ r, (w.playTime (σ.plays w lookahead) r n).isSome)
    (hunb : ∀ T : Time, ∃ n, T ≤ w.source.capture n) :
    ENNReal.ofReal (2 * shiftCost c fun r => X (w.host r) / 2)
      ≤ σ.cost w lookahead c + σ.cost (shiftStarKeepPeers w X hstar₁) lookahead c := by
  classical
  set w' := shiftStarKeepPeers w X hstar₁ with hw'
  set p := σ.plays w lookahead with hp
  have hplays : σ.plays w' lookahead = p :=
    σ.plays_shiftStarKeepPeers w lookahead hstar X hXs hstar₁ hprog hprog₁ harr
  -- The latencies in `w`.
  let ℓ : ℕ → Fin R → ℝ := fun n r => (w.playTime p r n).getD 0 - w.source.capture n
  have hT : ∀ n, N ≤ n → ∀ r, w.playTime p r n = some ((w.playTime p r n).getD 0) := by
    intro n hn r
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hplay n hn r)
    rw [ha]
    rfl
  let g₁ : ℕ → ℝ≥0∞ := fun n =>
    if N ≤ n then ENNReal.ofReal (frameCost c (ℓ n) (w.target n)) else 0
  let g₂ : ℕ → ℝ≥0∞ := fun n =>
    if N ≤ n then ENNReal.ofReal (frameCost c (fun r => ℓ n r + X (w.host r)) (w.target n))
    else 0
  have h₁ : longRun (w.accruedFrames g₁) ≤ σ.cost w lookahead c := by
    refine w.longRun_frames_le_cost p c g₁ fun n => ?_
    by_cases hn : N ≤ n
    · rw [w.weighted_frame_modal_split p c hR n (hT n hn)]
      simp only [g₁, hn, ↓reduceIte, frameCost, ℓ]
      exact le_rfl
    · simp [g₁, hn]
  have h₂ : longRun (w.accruedFrames g₂) ≤ σ.cost w' lookahead c := by
    have hsame : w'.accruedFrames g₂ = w.accruedFrames g₂ := rfl
    have h := w'.longRun_frames_le_cost p c g₂ (fun n => by
      by_cases hn : N ≤ n
      · have hT' : ∀ r, w'.playTime p r n
            = some ((w.playTime p r n).getD 0 + X (w.host r)) := fun r => by
          rw [hw', playTime_shiftStarKeepPeers, hT n hn r]
          rfl
        rw [w'.weighted_frame_modal_split p c hR n hT']
        have hsrc : w'.source = w.source := rfl
        have htgt : w'.target = w.target := rfl
        have hfun : (fun r => (w.playTime p r n).getD 0 + X (w.host r) - w.source.capture n)
            = fun r => ℓ n r + X (w.host r) := by
          funext r
          simp only [ℓ]
          ring
        rw [hsrc, htgt, hfun]
        simp only [g₂, hn, ↓reduceIte, frameCost]
        exact le_rfl
      · simp [g₂, hn])
    rw [hsame] at h
    unfold Solution.cost
    rw [hplays]
    exact h
  have hsum : ENNReal.ofReal (2 * shiftCost c fun r => X (w.host r) / 2)
      ≤ longRun (w.accruedFrames g₁) + longRun (w.accruedFrames g₂) := by
    refine w.longRun_accruedFrames_add_ge g₁ g₂ N (fun n hn => ?_) hunb
    simp only [g₁, g₂, hn, ↓reduceIte]
    have hquad := two_mul_shiftCost_le c hR (fun r => ℓ n r + X (w.host r) / 2)
      (fun r => X (w.host r) / 2) (w.target n)
    have e1 : (fun r => ℓ n r + X (w.host r) / 2 + X (w.host r) / 2)
        = fun r => ℓ n r + X (w.host r) := by
      funext r
      ring
    have e2 : (fun r => ℓ n r + X (w.host r) / 2 - X (w.host r) / 2) = ℓ n := by
      funext r
      ring
    beta_reduce at hquad
    rw [e1, e2] at hquad
    rw [← ENNReal.ofReal_add (frameCost_nonneg _ _ _) (frameCost_nonneg _ _ _)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact hsum.trans (add_le_add h₁ h₂)

end Star

end Unisono.Spec
