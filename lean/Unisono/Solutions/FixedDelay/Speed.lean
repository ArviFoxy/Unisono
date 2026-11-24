/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Latency
public import Unisono.Spec.ShiftedPlayback

/-!
# The baseline's speed

The baseline advances its position by one frame per output sample, plus a
correction of at most its slew.

* `step_le_slew`: in any world, when two consecutive output samples of a
  speaker both play the source, the second position is one frame after the
  first, within the slew.
* `withinSpeed_of_linear`: when frames are captured and output samples leave
  at the same rate, the baseline's speed stays within its slew of one, at
  every output sample from the first on.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- **What a speaker plays is the position its host chose for it.** -/
theorem chosen_of_plays (w : World H R) (lookahead : ℕ+) {n : ℕ} {r : Fin R} {b : ℕ}
    (hb : ((solution p : Solution H R Payload).states w lookahead n).askedNext r = b)
    (he : earliest (((solution p : Solution H R Payload).states w lookahead n).key w)
      ((solution p : Solution H R Payload).states w lookahead n).due = some (.asked r b))
    {k : ℕ} (hk : k ∈ (w.speaker r).block b) {x : ℝ}
    (hx : (solution p : Solution H R Payload).plays w lookahead r k = some x) :
    chosen p (memoryOf p (w.host r)
        (((solution p : Solution H R Payload).states w lookahead n).views (w.host r)))
      ((w.speaker r).first b) ((w.speaker r).reported b)
      ((memoryOf p (w.host r)
        (((solution p : Solution H R Payload).states w lookahead n).views (w.host r))).last r)
      ((w.speaker r).first b) (k - (w.speaker r).first b) = some x := by
  have h := plays_eq_chosen p w lookahead hb he hk
  rw [hx] at h
  generalize chosen p _ _ _ _ _ _ = c at h ⊢
  cases c with
  | none => simp [playable] at h
  | some y =>
    simp only [playable] at h
    split_ifs at h
    exact h.symm

/-- **The baseline advances by one frame per output sample, within its
slew.** In any world, when two consecutive output samples of a speaker both
play the source, the second position is one frame after the first, up to the
slew. -/
theorem step_le_slew (w : World H R) (lookahead : ℕ+) (hslew : 0 ≤ p.slew) {r : Fin R}
    {k : ℕ} {x y : ℝ}
    (hx : (solution p : Solution H R Payload).plays w lookahead r k = some x)
    (hy : (solution p : Solution H R Payload).plays w lookahead r (k + 1) = some y) :
    |y - x - 1| ≤ p.slew := by
  have hadv : ∀ goal : ℝ, some (advance p x goal) = some y → |y - x - 1| ≤ p.slew := by
    intro goal hgoal
    rw [Option.some.injEq] at hgoal
    rw [← hgoal]
    unfold advance
    have hc := clamp_mem (w := p.slew) (x := goal - x - 1) hslew
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  obtain ⟨b₂, n₂, hk₂, hb₂, he₂, -⟩ := exists_asked_of_plays_some (solution p : Solution H R Payload) w lookahead hy
  have hc₂ := chosen_of_plays p w lookahead hb₂ he₂ hk₂ hy
  have hkb₂ : (w.speaker r).first b₂ ≤ k + 1 ∧ k + 1 < (w.speaker r).first (b₂ + 1) := by
    have h := hk₂
    unfold PlaybackDevice.block at h
    rw [List.mem_range'_1] at h
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self b₂)
    omega
  rcases Nat.lt_or_ge ((w.speaker r).first b₂) (k + 1) with hlt | hge
  · -- The two output samples are in one block.
    have hk₂' : k ∈ (w.speaker r).block b₂ := by
      unfold PlaybackDevice.block
      rw [List.mem_range'_1]
      omega
    have hc₁ := chosen_of_plays p w lookahead hb₂ he₂ hk₂' hx
    obtain ⟨j, hj1, hj2⟩ : ∃ j, k - (w.speaker r).first b₂ = j
        ∧ k + 1 - (w.speaker r).first b₂ = j + 1 := ⟨_, rfl, by omega⟩
    rw [hj1] at hc₁
    rw [hj2] at hc₂
    cases ht : target p (memoryOf p (w.host r) (((solution p : Solution H R Payload).states w lookahead n₂).views (w.host r)))
        ((w.speaker r).first b₂) ((w.speaker r).reported b₂)
        ((w.speaker r).first b₂ + j + 1) with
    | none => simp [chosen, hc₁, choose, ht] at hc₂
    | some goal =>
      rw [chosen_succ p _ _ _ _ _ j hc₁ ht] at hc₂
      exact hadv goal hc₂
  · -- The second output sample is the first of its block.
    have hfirst : (w.speaker r).first b₂ = k + 1 := by omega
    obtain ⟨b₁, n₁, hk₁, hb₁, he₁, -⟩ := exists_asked_of_plays_some (solution p : Solution H R Payload) w lookahead hx
    have hc₁ := chosen_of_plays p w lookahead hb₁ he₁ hk₁ hx
    have hkb₁ : (w.speaker r).first b₁ ≤ k ∧ k < (w.speaker r).first (b₁ + 1) := by
      have h := hk₁
      unfold PlaybackDevice.block at h
      rw [List.mem_range'_1] at h
      have := (w.speaker r).first_strictMono (Nat.lt_succ_self b₁)
      omega
    have hb12 : b₂ = b₁ + 1 := by
      have h1 : b₁ < b₂ := (w.speaker r).first_strictMono.lt_iff_lt.mp (by omega)
      have h2 : b₂ ≤ b₁ + 1 := (w.speaker r).first_strictMono.le_iff_le.mp (by omega)
      omega
    have hn : n₁ < n₂ := by
      by_contra hge'
      have := (solution p : Solution H R Payload).askedNext_mono w lookahead r (not_lt.mp hge')
      simp only at this
      omega
    have hlast := last_at_next_request p w lookahead hb₁ he₁ (hb12 ▸ hb₂) hn
    unfold PlaybackDevice.block at hlast
    rw [lastChosen_block p _ r _ _ _ (by omega)] at hlast
    have hidx : (w.speaker r).first (b₁ + 1) - (w.speaker r).first b₁ - 1
        = k - (w.speaker r).first b₁ := by
      rw [← hb12]
      omega
    rw [hidx, hc₁, Option.map_some] at hlast
    have hpos : (w.speaker r).first b₁ + (k - (w.speaker r).first b₁) = k := by omega
    rw [hpos] at hlast
    have hz : k + 1 - (w.speaker r).first b₂ = 0 := by omega
    rw [hz, hlast] at hc₂
    cases ht : target p (memoryOf p (w.host r) (((solution p : Solution H R Payload).states w lookahead n₂).views (w.host r)))
        ((w.speaker r).first b₂) ((w.speaker r).reported b₂) ((w.speaker r).first b₂) with
    | none => simp [chosen, choose, ht] at hc₂
    | some goal =>
      simp only [chosen, choose, ht] at hc₂
      rw [ite_eq_left hfirst.symm] at hc₂
      exact hadv goal hc₂

/-- **The baseline's speed stays within its slew of one**, at every output
sample, when frames are captured and output samples leave at the same
rate. -/
theorem withinSpeed_of_linear (w : World H R) (lookahead : ℕ+) (hslew : 0 ≤ p.slew)
    {ρ t₀ : ℝ} (hρ : 0 < ρ) (hcap : ∀ n, w.source.capture n = t₀ + (n : ℝ) / ρ)
    (o : Fin R → ℝ) (hout : ∀ r k, (w.speaker r).out k = o r + (k : ℝ) / ρ) {u : ℝ}
    (hu : p.slew ≤ u) : (solution p : Solution H R Payload).WithinSpeed w lookahead u := by
  classical
  intro r k v hv
  unfold World.speed at hv
  cases hx : (solution p : Solution H R Payload).plays w lookahead r k with
  | none => simp [hx] at hv
  | some x =>
    cases hy : (solution p : Solution H R Payload).plays w lookahead r (k + 1) with
    | none => simp [hx, hy] at hv
    | some y =>
      simp only [hx, hy] at hv
      split_ifs at hv with hc
      rw [Option.some.injEq] at hv
      have hstep := step_le_slew p w lookahead hslew hx hy
      have hval : v = y - x := by
        rw [← hv, w.captured_of_linear hcap, w.captured_of_linear hcap, hout, hout]
        push_cast
        field_simp
        ring
      rw [hval]
      exact hstep.trans hu

end Unisono.Solutions.FixedDelay
