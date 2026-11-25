/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Skips
public import Unisono.Spec.AtLatency

/-!
# Frames and missed samples from the positions that are played

The objectives are stated for the frames of the source and for output
samples. A solution decides positions, one for each output sample. This file
relates the two for any playback in any world, without assuming that the
playback holds one latency.

* `missedAt_le_abs`: the missed samples counted at an output sample that
  plays the source, after an earlier one did, are at most the distance
  between two numbers: by how much the position advanced since the last
  output sample that played the source, and how many output samples passed
  since then.
* `World.mul_le_captured_sub`, `World.captured_sub_le_mul`: between two
  positions, the capture time advances by at least, or at most, the distance
  of the positions times a bound for the time from one frame to the next
  among the frames between them.
* `World.latency_eq_of_some`: the latency of a frame that a speaker plays,
  written out: the frame lies within the first step of continuous playback
  that passes it, and is played between the two output samples of the step,
  in proportion.
* `World.latency_between`: **the latency of a frame lies between the
  latencies of the two positions played around it**, up to twice the
  difference between the longest and the shortest time from one frame to
  the next among the four frames around it. The latency of a position
  played at an output sample is the time from the capture of the sound at
  that position to the leaving of the output sample.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ}

/-- **Missed samples from the advance of the position.** Let output sample
`K` play the position `y`, and let `x` be the position that the last earlier
output sample that played the source played. The missed samples counted at
`K` are at most the distance between `y - x` and the number of output
samples from that earlier one to `K`. -/
theorem missedAt_le_abs {plays : ℕ → Option ℝ} {K : ℕ} {x y : ℝ} (hy : plays K = some y)
    (hx : lastPlayed plays K = some x) :
    (missedAt plays K : ℝ) ≤ |y - x - (trailing plays K + 1)| := by
  rw [missedAt_of_lastPlayed hy hx, Nat.cast_add]
  have hg : (0 : ℝ) ≤ trailing plays K := Nat.cast_nonneg _
  have h1 : (((⌊y - x - 1⌋ - (trailing plays K : ℤ)).toNat : ℕ) : ℝ)
      ≤ max (y - x - 1 - trailing plays K) 0 := by
    rcases le_total (⌊y - x - 1⌋ - (trailing plays K : ℤ)) 0 with h | h
    · rw [Int.toNat_eq_zero.mpr h, Nat.cast_zero]
      exact le_max_right _ _
    · have hc : (((⌊y - x - 1⌋ - (trailing plays K : ℤ)).toNat : ℕ) : ℝ)
          = (⌊y - x - 1⌋ : ℝ) - trailing plays K := by
        have h' : ((((⌊y - x - 1⌋ - (trailing plays K : ℤ)).toNat : ℕ) : ℤ) : ℝ)
            = ((⌊y - x - 1⌋ - (trailing plays K : ℤ) : ℤ) : ℝ) := by
          rw [Int.toNat_of_nonneg h]
        push_cast at h'
        exact h'
      rw [hc]
      have := Int.floor_le (y - x - 1)
      exact le_max_of_le_left (by linarith)
  have h2 : ((⌊1 - (y - x)⌋.toNat : ℕ) : ℝ) ≤ max (1 - (y - x)) 0 := by
    rcases le_total ⌊1 - (y - x)⌋ 0 with h | h
    · rw [Int.toNat_eq_zero.mpr h, Nat.cast_zero]
      exact le_max_right _ _
    · have hc : ((⌊1 - (y - x)⌋.toNat : ℕ) : ℝ) = (⌊1 - (y - x)⌋ : ℝ) := by
        have h' : (((⌊1 - (y - x)⌋.toNat : ℕ) : ℤ) : ℝ) = ((⌊1 - (y - x)⌋ : ℤ) : ℝ) := by
          rw [Int.toNat_of_nonneg h]
        push_cast at h'
        exact h'
      rw [hc]
      exact le_max_of_le_left (Int.floor_le _)
  rcases le_total (y - x - 1 - trailing plays K) 0 with h | h
  · rw [max_eq_right h] at h1
    have h3 : max (1 - (y - x)) 0 ≤ |y - x - (trailing plays K + 1)| := by
      rw [abs_of_nonpos (by linarith)]
      exact max_le (by linarith) (by linarith)
    linarith
  · rw [max_eq_left h] at h1
    have h3 : max (1 - (y - x)) 0 = 0 := max_eq_right (by linarith)
    rw [h3] at h2
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The capture time of a position between frame `i` and frame `i + 1`. -/
theorem World.captured_of_mem (w : World H R) {i : ℕ} {z : ℝ} (h1 : (i : ℝ) ≤ z)
    (h2 : z ≤ i + 1) :
    w.captured z
      = w.source.capture i + (z - i) * (w.source.capture (i + 1) - w.source.capture i) := by
  rcases eq_or_lt_of_le h2 with heq | hlt
  · have hcast : z = ((i + 1 : ℕ) : ℝ) := by
      rw [heq]
      push_cast
      ring
    rw [hcast, w.captured_natCast]
    push_cast
    ring
  · unfold World.captured
    have hf : ⌊z⌋₊ = i := by
      rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg i) h1)]
      exact ⟨h1, hlt⟩
    rw [hf]

/-- **The capture time advances at least as fast as the frames around.** If
the time from one frame to the next is at least `p` for every frame from the
one of position `a` to the one of position `b`, the sound at `b` was
captured at least `p * (b - a)` after the sound at `a`. -/
theorem World.mul_le_captured_sub (w : World H R) {p a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hp : ∀ i, ⌊a⌋₊ ≤ i → i ≤ ⌊b⌋₊ → p ≤ w.source.capture (i + 1) - w.source.capture i) :
    p * (b - a) ≤ w.captured b - w.captured a := by
  have hb0 : 0 ≤ b := le_trans ha hab
  have hia := Nat.floor_le ha
  have hia' := Nat.lt_floor_add_one a
  have hib := Nat.floor_le hb0
  have hib' := Nat.lt_floor_add_one b
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  rcases Nat.eq_or_lt_of_le hfloor with heq | hlt
  · have hba : w.captured b = w.source.capture ⌊a⌋₊
        + (b - ⌊a⌋₊) * (w.source.capture (⌊a⌋₊ + 1) - w.source.capture ⌊a⌋₊) := by
      refine w.captured_of_mem ?_ ?_
      · rw [heq]
        exact hib
      · rw [heq]
        exact hib'.le
    rw [w.captured_of_mem hia hia'.le, hba]
    have h1 := hp ⌊a⌋₊ le_rfl hfloor
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h1)]
  · have hints : ∀ j, ⌊a⌋₊ + 1 ≤ j → j ≤ ⌊b⌋₊ →
        p * ((j : ℝ) - ((⌊a⌋₊ + 1 : ℕ) : ℝ))
          ≤ w.source.capture j - w.source.capture (⌊a⌋₊ + 1) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base =>
        intro _
        simp
      | succ j hj ih =>
        intro hjb
        have h1 := ih (by omega)
        have h2 := hp j (by omega) (by omega)
        push_cast at h1 ⊢
        linarith
    have h1 := hints ⌊b⌋₊ hlt le_rfl
    have h2 := hp ⌊a⌋₊ le_rfl hfloor
    have h3 := hp ⌊b⌋₊ hfloor le_rfl
    rw [w.captured_of_mem hia hia'.le, w.captured_of_mem hib hib'.le]
    push_cast at h1
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (⌊a⌋₊ : ℝ) + 1 - a by linarith) (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr hib) (sub_nonneg.mpr h3)]

/-- **The capture time advances at most as fast as the frames around.** If
the time from one frame to the next is at most `p` for every frame from the
one of position `a` to the one of position `b`, the sound at `b` was
captured at most `p * (b - a)` after the sound at `a`. -/
theorem World.captured_sub_le_mul (w : World H R) {p a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hp : ∀ i, ⌊a⌋₊ ≤ i → i ≤ ⌊b⌋₊ → w.source.capture (i + 1) - w.source.capture i ≤ p) :
    w.captured b - w.captured a ≤ p * (b - a) := by
  have hb0 : 0 ≤ b := le_trans ha hab
  have hia := Nat.floor_le ha
  have hia' := Nat.lt_floor_add_one a
  have hib := Nat.floor_le hb0
  have hib' := Nat.lt_floor_add_one b
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  rcases Nat.eq_or_lt_of_le hfloor with heq | hlt
  · have hba : w.captured b = w.source.capture ⌊a⌋₊
        + (b - ⌊a⌋₊) * (w.source.capture (⌊a⌋₊ + 1) - w.source.capture ⌊a⌋₊) := by
      refine w.captured_of_mem ?_ ?_
      · rw [heq]
        exact hib
      · rw [heq]
        exact hib'.le
    rw [w.captured_of_mem hia hia'.le, hba]
    have h1 := hp ⌊a⌋₊ le_rfl hfloor
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h1)]
  · have hints : ∀ j, ⌊a⌋₊ + 1 ≤ j → j ≤ ⌊b⌋₊ →
        w.source.capture j - w.source.capture (⌊a⌋₊ + 1)
          ≤ p * ((j : ℝ) - ((⌊a⌋₊ + 1 : ℕ) : ℝ)) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base =>
        intro _
        simp
      | succ j hj ih =>
        intro hjb
        have h1 := ih (by omega)
        have h2 := hp j (by omega) (by omega)
        push_cast at h1 ⊢
        linarith
    have h1 := hints ⌊b⌋₊ hlt le_rfl
    have h2 := hp ⌊a⌋₊ le_rfl hfloor
    have h3 := hp ⌊b⌋₊ hfloor le_rfl
    rw [w.captured_of_mem hia hia'.le, w.captured_of_mem hib hib'.le]
    push_cast at h1
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (⌊a⌋₊ : ℝ) + 1 - a by linarith) (sub_nonneg.mpr h2),
      mul_nonneg (sub_nonneg.mpr hib) (sub_nonneg.mpr h3)]

/-- **The latency of a frame, written out.** A frame `n` that speaker `r`
plays lies within a step of continuous playback, from output sample `k` at
the position `x` to the next at the position `y`; no earlier step passes
it; and its latency is the time at which it is played, between the two
output samples in proportion, minus its capture time. -/
theorem World.latency_eq_of_some (w : World H R) (plays : Fin R → ℕ → Option ℝ) {r : Fin R}
    {n : ℕ} {l : ℝ} (hl : w.latency plays r n = some l) :
    ∃ k x y, plays r k = some x ∧ plays r (k + 1) = some y ∧ x < y ∧ y < x + 2
      ∧ x ≤ n ∧ (n : ℝ) ≤ y ∧ (∀ j, j < k → ¬ Covers (plays r) j n)
      ∧ l = (w.speaker r).out k
          + (n - x) / (y - x) * ((w.speaker r).out (k + 1) - (w.speaker r).out k)
          - w.source.capture n := by
  classical
  unfold World.latency World.playTime Spec.playTime at hl
  split at hl
  · rename_i hex
    obtain ⟨x, y, hx, hy, hxy, hyx, hxn, hny⟩ := Nat.find_spec hex
    simp only [hx, hy, Option.map_some, Option.some.injEq] at hl
    exact ⟨Nat.find hex, x, y, hx, hy, hxy, hyx, hxn, hny, fun j hj => Nat.find_min hex hj,
      hl.symm⟩
  · simp at hl

/-- **The latency of a frame lies between the latencies of the positions
played around it.** Let speaker `r` play frame `n` with latency `l`, at
positions that are not negative. Let the time from one frame to the next be
between `pLo` and `pHi` for the frames from two before `n` to one after `n`.
Then the frame lies within a step of continuous playback from output sample
`k`, at the position `x`, to the next, at the position `y`, and `l` lies
between the smaller and the larger of the two latencies
`out k - captured x` and `out (k + 1) - captured y`, up to
`2 * (pHi - pLo)`. -/
theorem World.latency_between (w : World H R) (plays : Fin R → ℕ → Option ℝ) {r : Fin R}
    {n : ℕ} {l : ℝ} (hl : w.latency plays r n = some l)
    (hpos : ∀ k x, plays r k = some x → 0 ≤ x) {pLo pHi : ℝ}
    (hp : ∀ i, n ≤ i + 2 → i ≤ n + 1 →
      pLo ≤ w.source.capture (i + 1) - w.source.capture i
        ∧ w.source.capture (i + 1) - w.source.capture i ≤ pHi) :
    ∃ k x y, plays r k = some x ∧ plays r (k + 1) = some y ∧ x < y ∧ y < x + 2
      ∧ x ≤ n ∧ (n : ℝ) ≤ y
      ∧ min ((w.speaker r).out k - w.captured x) ((w.speaker r).out (k + 1) - w.captured y)
          - 2 * (pHi - pLo) ≤ l
      ∧ l ≤ max ((w.speaker r).out k - w.captured x)
            ((w.speaker r).out (k + 1) - w.captured y) + 2 * (pHi - pLo) := by
  obtain ⟨k, x, y, hx, hy, hxy, hyx, hxn, hny, -, hl'⟩ := w.latency_eq_of_some plays hl
  have hx0 := hpos k x hx
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfx : n ≤ ⌊x⌋₊ + 2 := by
    have h1 : (n : ℝ) < x + 2 := by linarith
    have h2 := Nat.lt_floor_add_one x
    have h3 : (n : ℝ) < ((⌊x⌋₊ + 3 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h4 : n < ⌊x⌋₊ + 3 := by exact_mod_cast h3
    omega
  have hfy : ⌊y⌋₊ ≤ n + 1 := by
    have h1 : y < (n : ℝ) + 2 := by linarith
    have h2 : y < ((n + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h3 := (Nat.floor_lt (le_trans hx0 hxy.le)).mpr h2
    omega
  have hfxn : ⌊x⌋₊ ≤ n := Nat.floor_le_of_le hxn
  have hfyn : n ≤ ⌊y⌋₊ := Nat.le_floor hny
  have hfn : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  -- The capture times between the three positions.
  have hcn_lo := w.mul_le_captured_sub (p := pLo) hx0 hxn (fun i hi1 hi2 =>
    (hp i (by omega) (by rw [hfn] at hi2; omega)).1)
  have hcn_hi := w.captured_sub_le_mul (p := pHi) hx0 hxn (fun i hi1 hi2 =>
    (hp i (by omega) (by rw [hfn] at hi2; omega)).2)
  have hcy_lo := w.mul_le_captured_sub (p := pLo) hx0 hxy.le (fun i hi1 hi2 =>
    (hp i (by omega) (by omega)).1)
  have hcy_hi := w.captured_sub_le_mul (p := pHi) hx0 hxy.le (fun i hi1 hi2 =>
    (hp i (by omega) (by omega)).2)
  rw [w.captured_natCast] at hcn_lo hcn_hi
  -- The proportion of the step at which the frame is played.
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (n - x) / (y - x) := ⟨_, rfl⟩
  have hd : 0 < y - x := by linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθ]
    exact div_nonneg (by linarith) hd.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ]
    exact (div_le_one hd).mpr (by linarith)
  have hθd : θ * (y - x) = n - x := by
    rw [hθ]
    field_simp
  rw [← hθ] at hl'
  have hsub : (n : ℝ) - x ≤ 2 := by linarith
  have hsub0 : (0 : ℝ) ≤ n - x := by linarith
  have hband : 0 ≤ pHi - pLo := by
    have := hp n (by omega) (by omega)
    linarith [this.1, this.2]
  -- The frame's capture time against the proportion between the two positions.
  have hδ_hi : (1 - θ) * w.captured x + θ * w.captured y - w.source.capture n
      ≤ 2 * (pHi - pLo) := by
    have e1 : θ * (w.captured y - w.captured x) ≤ θ * (pHi * (y - x)) :=
      mul_le_mul_of_nonneg_left hcy_hi hθ0
    have e2 : θ * (pHi * (y - x)) = pHi * (n - x) := by
      rw [← hθd]
      ring
    nlinarith [mul_nonneg hband hsub0, mul_nonneg hband (sub_nonneg.mpr hsub)]
  have hδ_lo : -(2 * (pHi - pLo))
      ≤ (1 - θ) * w.captured x + θ * w.captured y - w.source.capture n := by
    have e1 : θ * (pLo * (y - x)) ≤ θ * (w.captured y - w.captured x) :=
      mul_le_mul_of_nonneg_left hcy_lo hθ0
    have e2 : θ * (pLo * (y - x)) = pLo * (n - x) := by
      rw [← hθd]
      ring
    nlinarith [mul_nonneg hband hsub0, mul_nonneg hband (sub_nonneg.mpr hsub)]
  set G := (w.speaker r).out k - w.captured x with hG
  set G' := (w.speaker r).out (k + 1) - w.captured y with hG'
  have hcomb : l = (1 - θ) * G + θ * G'
      + ((1 - θ) * w.captured x + θ * w.captured y - w.source.capture n) := by
    rw [hl', hG, hG']
    ring
  have hmin : min G G' ≤ (1 - θ) * G + θ * G' := by
    have h1 := min_le_left G G'
    have h2 := min_le_right G G'
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hθ1),
      mul_le_mul_of_nonneg_left h2 hθ0]
  have hmax : (1 - θ) * G + θ * G' ≤ max G G' := by
    have h1 := le_max_left G G'
    have h2 := le_max_right G G'
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hθ1),
      mul_le_mul_of_nonneg_left h2 hθ0]
  refine ⟨k, x, y, hx, hy, hxy, hyx, hxn, hny, ?_, ?_⟩ <;> linarith

end Unisono.Spec
