/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Memory
public import Unisono.Spec.Run
public import Unisono.Spec.Models.Bounded

/-!
# The baseline in a bounded world: the pace

Let `T` be a trajectory of positions, one for each output sample.

* Suppose a position advances by one frame per output sample plus a
  correction towards its target clamped to `[-w, w]`. Suppose also that the
  targets stay within `B` frames of `T`, and that `T` advances by one frame
  per output sample within `ν < w`. Then a position that starts within `B`
  of `T` stays within `B` of it (`advance_tracks`), and a position at any
  distance from `T` comes within `B` of it after finitely many output
  samples (`advance_converges`).
* The ideal trajectory satisfies this condition with
  `ν = 2 ε_D / (1 - ε_D)` (`trajectory_step`). Its position for output
  sample `k` is the one whose sound was captured at `o(k) - L`, where
  `o(k)` is the true time at which output sample `k` leaves, `L` is the
  latency, and `ε_D` bounds the devices' rate errors.
* At each request of a speaker, its host continues from the position it
  chose at the speaker's previous request (`last_at_next_request`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

/-- **The pace follows the target.** From output sample `K` on, let a
speaker's position `x` advance by one frame per output sample plus a
correction towards the target `xs` clamped to `[-w, w]`. Let the target
stay within `B` frames of a trajectory `T` that advances by one frame per
output sample within `ν < w`. If the position is within `B` of the
trajectory at `K`, it stays within `B` of it. -/
theorem advance_tracks {w ν B : ℝ} (hw : ν < w) (x xs T : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ k, K ≤ k → x (k + 1) = x k + 1 + clamp w (xs (k + 1) - x k - 1))
    (hband : ∀ k, K ≤ k → |xs k - T k| ≤ B)
    (hT : ∀ k, K ≤ k → |T (k + 1) - T k - 1| ≤ ν)
    (hstart : |x K - T K| ≤ B) :
    ∀ k, K ≤ k → |x k - T k| ≤ B := by
  intro k hk
  induction hk with
  | refl => exact hstart
  | step hle ih =>
    rename_i k
    have hb := abs_le.mp (hband (k + 1) (Nat.le_succ_of_le hle))
    have hν := abs_le.mp (hT k hle)
    have hd := abs_le.mp ih
    rw [hstep k hle]
    unfold clamp
    set a := xs (k + 1) - x k - 1
    rcases le_or_gt a w with ha | ha
    · rw [min_eq_right ha]
      rcases le_or_gt (-w) a with ha' | ha'
      · rw [max_eq_right ha']
        rw [abs_le]
        constructor <;> linarith
      · rw [max_eq_left ha'.le]
        rw [abs_le]
        constructor <;> linarith
    · rw [min_eq_left ha.le, max_eq_right (by linarith)]
      rw [abs_le]
      constructor <;> linarith

/-- One step of the pace: afterwards, the distance to the trajectory is at
most `B`, or it has shrunk by at least `w - ν`. -/
theorem advance_step {w ν B D e δ : ℝ} (hw : ν < w) (he : |e| ≤ B) (hδ : |δ| ≤ ν) :
    |D - δ + clamp w (e + δ - D)| ≤ max B (|D| - (w - ν)) := by
  have he' := abs_le.mp he
  have hδ' := abs_le.mp hδ
  have hD := le_abs_self D
  have hD' := neg_abs_le D
  have m1 := le_max_left B (|D| - (w - ν))
  have m2 := le_max_right B (|D| - (w - ν))
  unfold clamp
  rcases le_or_gt (e + δ - D) w with h1 | h1
  · rw [min_eq_right h1]
    rcases le_or_gt (-w) (e + δ - D) with h2 | h2
    · rw [max_eq_right h2, abs_le]
      constructor <;> linarith
    · rw [max_eq_left h2.le, abs_le]
      constructor <;> linarith
  · rw [min_eq_left h1.le, max_eq_right (by linarith), abs_le]
    constructor <;> linarith

/-- **The pace reaches the target's band from any distance.** Let the
position, the target and the trajectory be as in `advance_tracks`, except
that the position may start at any distance from the trajectory. Then the
position is within `B` of the trajectory from some output sample on. -/
theorem advance_converges {w ν B : ℝ} (hw : ν < w) (x xs T : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ k, K ≤ k → x (k + 1) = x k + 1 + clamp w (xs (k + 1) - x k - 1))
    (hband : ∀ k, K ≤ k → |xs k - T k| ≤ B)
    (hT : ∀ k, K ≤ k → |T (k + 1) - T k - 1| ≤ ν) :
    ∃ K', K ≤ K' ∧ ∀ k, K' ≤ k → |x k - T k| ≤ B := by
  have hgap : 0 < w - ν := by linarith
  -- After `j` steps the distance is at most `B` or its start less `j (w - ν)`.
  have hdecay : ∀ j : ℕ, |x (K + j) - T (K + j)| ≤ max B (|x K - T K| - j * (w - ν)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hk : K ≤ K + j := Nat.le_add_right K j
      have hs := hstep (K + j) hk
      have hb := hband (K + j + 1) (by omega)
      have ht := hT (K + j) hk
      have key := advance_step (D := x (K + j) - T (K + j)) (e := xs (K + j + 1) - T (K + j + 1))
        (δ := T (K + j + 1) - T (K + j) - 1) hw hb ht
      have hx : x (K + (j + 1)) - T (K + (j + 1))
          = (x (K + j) - T (K + j)) - (T (K + j + 1) - T (K + j) - 1)
            + clamp w ((xs (K + j + 1) - T (K + j + 1)) + (T (K + j + 1) - T (K + j) - 1)
              - (x (K + j) - T (K + j))) := by
        rw [show K + (j + 1) = K + j + 1 by ring, hs]
        ring_nf
      rw [hx]
      refine key.trans ?_
      push_cast
      apply max_le (le_max_left _ _)
      rcases le_total B (|x K - T K| - j * (w - ν)) with hc | hc
      · rw [max_eq_right hc] at ih
        apply le_max_of_le_right
        linarith
      · rw [max_eq_left hc] at ih
        apply le_max_of_le_left
        linarith
  -- Enough steps bring the distance within `B`.
  obtain ⟨j, hj⟩ := exists_nat_ge (|x K - T K| / (w - ν))
  have hin : |x (K + j) - T (K + j)| ≤ B := by
    have h := hdecay j
    have hmul : |x K - T K| ≤ j * (w - ν) := by
      have := (div_le_iff₀ hgap).mp hj
      linarith
    have hB : 0 ≤ B := le_trans (abs_nonneg _) (hband K le_rfl)
    exact h.trans (max_le le_rfl (by linarith))
  refine ⟨K + j, Nat.le_add_right K j, ?_⟩
  exact advance_tracks hw x xs T (K + j) (fun k hk => hstep k (by omega))
    (fun k hk => hband k (by omega)) (fun k hk => hT k (by omega)) hin

omit [DecidableEq H] in
/-- **The ideal trajectory advances by one frame per output sample within
`2 ε / (1 - ε)`.** Suppose the capture device and the playback device have
rate errors of at most `ε`, and that for every output sample `k` the sound
at position `T k` was captured exactly at `o(k) - L`. Then consecutive
positions are between `(1 - ε) / (1 + ε)` and `(1 + ε) / (1 - ε)` frames
apart. -/
theorem trajectory_step (w : World H R) {ε : ℝ} (hsrc : w.source.RateWithin w.rate ε)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (d : PlaybackDevice) (hd : d.RateWithin w.rate ε) (L : ℝ)
    (T : ℕ → ℝ) (hT : ∀ k, w.captured (T k) = d.out k - L) (k : ℕ) :
    |T (k + 1) - T k - 1| ≤ 2 * ε / (1 - ε) := by
  have hrate := w.rate_pos
  have hout := abs_le.mp (hd k)
  have hpos : 0 < d.out (k + 1) - d.out k := sub_pos.mpr (d.out_strictMono (Nat.lt_succ_self k))
  have hcap : w.captured (T (k + 1)) - w.captured (T k) = d.out (k + 1) - d.out k := by
    rw [hT, hT]; ring
  have hle : T k ≤ T (k + 1) := by
    by_contra hlt
    rw [not_le] at hlt
    have := (w.captured_sub_mem hsrc hlt.le).1
    have hlo : 0 < (1 - ε) / w.rate := div_pos (by linarith) hrate
    nlinarith
  obtain ⟨h1, h2⟩ := w.captured_sub_mem hsrc hle
  rw [hcap] at h1 h2
  set Δ := T (k + 1) - T k
  have e1 : (1 - ε) / w.rate = 1 / w.rate - ε / w.rate := sub_div _ _ _
  have e2 : (1 + ε) / w.rate = 1 / w.rate + ε / w.rate := add_div _ _ _
  -- From the two bounds: `(1 - ε) Δ ≤ 1 + ε` and `1 - ε ≤ (1 + ε) Δ`.
  have hA : (1 - ε) * Δ ≤ 1 + ε := by
    have : (1 - ε) / w.rate * Δ ≤ (1 + ε) / w.rate := by linarith
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hrate] at this
    exact this
  have hB : 1 - ε ≤ (1 + ε) * Δ := by
    have : (1 - ε) / w.rate ≤ (1 + ε) / w.rate * Δ := by linarith
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hrate] at this
    exact this
  have hpos1 : 0 < 1 - ε := by linarith
  have hpos2 : 0 < 1 + ε := by linarith
  rw [abs_le]
  constructor
  · have hB' : -(2 * ε) / (1 + ε) ≤ Δ - 1 := by
      rw [div_le_iff₀ hpos2]
      nlinarith
    have hcmp : 2 * ε / (1 + ε) ≤ 2 * ε / (1 - ε) :=
      div_le_div_of_nonneg_left (by linarith) hpos1 (by linarith)
    rw [neg_div] at hB'
    linarith
  · rw [le_div_iff₀ hpos1]
    nlinarith

omit [DecidableEq H] in
/-- Clamping a value to `[-w, w]` gives a value in `[-w, w]`. -/
theorem clamp_mem {w x : ℝ} (hw : 0 ≤ w) : -w ≤ clamp w x ∧ clamp w x ≤ w := by
  unfold clamp
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- **A speaker continues at its next request from where it ended.** At
every step after the one that handles request `b` of speaker `r`, up to the
one that handles request `b + 1`, the host of `r` remembers the last output
sample of request `b` and the position chosen for it. -/
theorem last_at_next_request (w : World H R) (lookahead : ℕ+) {n₁ n₂ : ℕ} {r : Fin R} {b : ℕ}
    (hb₁ : ((solution p : Solution H R Payload).states w lookahead n₁).askedNext r = b)
    (he₁ : earliest (((solution p : Solution H R Payload).states w lookahead n₁).key w)
      ((solution p : Solution H R Payload).states w lookahead n₁).due = some (.asked r b))
    (hb₂ : ((solution p : Solution H R Payload).states w lookahead n₂).askedNext r = b + 1)
    (hn : n₁ < n₂) :
    (memoryOf p (w.host r) (((solution p : Solution H R Payload).states w lookahead n₂).views (w.host r))).last r
      = lastChosen (positions p (memoryOf p (w.host r)
          (((solution p : Solution H R Payload).states w lookahead n₁).views (w.host r))) r
          ((w.speaker r).block b) ((w.speaker r).reported b)) := by
  set σ : Solution H R Payload := solution p
  have hh := σ.handled_of_asked w lookahead he₁
  have hsucc := σ.askedNext_succ w lookahead (hb₁ ▸ he₁)
  rw [hb₁] at hsucc
  have hv₁ : (σ.states w lookahead (n₁ + 1)).views (w.host r)
      = (σ.states w lookahead n₁).views (w.host r)
        ++ [⟨(w.clock (w.host r)).read ((w.speaker r).asked b),
          .asked r ((w.speaker r).block b) ((w.speaker r).reported b)⟩] := by
    rw [σ.views_succ w lookahead n₁ (w.host r), hh]
    simp
  obtain ⟨l, hl, hev⟩ := σ.views_append w lookahead (show n₁ + 1 ≤ n₂ by omega) (w.host r)
  rw [hl, hv₁, List.append_assoc, List.singleton_append]
  apply last_after_request p (w.host r) _ _ l rfl
  intro e he outs st heo
  obtain ⟨i, hi₁, hi₂, t, obs, hhi, rfl⟩ := hev e he
  simp only at heo
  subst heo
  exact σ.no_request_between w lookahead (hsucc.trans hb₂.symm) hi₁ hi₂ hhi

end Unisono.Solutions.FixedDelay
