/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.MissingSamples

/-!
# Bounds by the number of output samples

A playback counts at most one discontinuity for each output sample. A
playback whose positions lie on a line in the output sample, or that plays
nothing, counts a bounded number of missed samples for each output sample,
whatever the slope of the line. This file states both as bounds on the
long-run averages, by the long-run number of output samples per second.

* `longRun_le_of_tendsto`: the long-run average of a cost accrued that is at
  most a function whose value per second converges.
* `World.longRun_outputs_le_rate`: when output sample `k` of speaker `r`
  leaves at `a r + k / s r`, the long-run number of output samples per
  second, averaged over the speakers, is at most the mean of the `s r`.
* `World.discontinuities_le_outputs`: the long-run number of discontinuities
  is at most the long-run number of output samples.
* `World.missed_le_of_slope`: when every played position of speaker `r` lies
  on a line of slope `c r > 0` in the output sample, with `c r - 1 ≤ d`, the
  long-run number of missed samples is at most `1 + 2 d` times the long-run
  number of output samples.

The bounds of `Unisono.Spec.MissingSamples` are sharper when the slope is
below two: there, missed samples and discontinuities are counted only where
an output sample plays nothing. The bounds of this file hold for every
slope. A slope of two or more means that the capture device's clock runs at
least twice as fast as the playback device's clock.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal NNReal
open Filter Topology

variable {H : Type} {R : ℕ}

/-! ## The number of output samples -/

/-- A cost accrued that is, from some horizon on, at most a function whose
value per second converges has a long-run average of at most the limit. -/
theorem longRun_le_of_tendsto {A G : Time → ℝ≥0∞} {B : ℝ≥0∞} (h : ∀ᶠ T in atTop, A T ≤ G T)
    (hG : Tendsto (fun T : Time => G T / ENNReal.ofReal T) atTop (𝓝 B)) : longRun A ≤ B := by
  unfold longRun
  calc limsup (fun T => A T / ENNReal.ofReal T) atTop
      ≤ limsup (fun T : Time => G T / ENNReal.ofReal T) atTop :=
        limsup_le_limsup (h.mono fun T hT => ENNReal.div_le_div_right hT _)
    _ = B := hG.limsup_eq

/-- When output sample `k` of a playback device leaves at `a + k / s`, with
`s > 0` output samples per second, fewer than `s (T - a) + 1` output samples
leave before the true time `T`. -/
theorem PlaybackDevice.find_le_of_line (d : PlaybackDevice) {a s : ℝ} (hs : 0 < s)
    (hout : ∀ k : ℕ, d.out k = a + k / s) {T : Time} (hunb : ∃ k, T ≤ d.out k)
    (hT : 0 ≤ s * (T - a) + 1) : (Nat.find hunb : ℝ) ≤ s * (T - a) + 1 := by
  rcases Nat.eq_zero_or_pos (Nat.find hunb) with h0 | hpos
  · rw [h0]
    simpa using hT
  · have hlt : d.out (Nat.find hunb - 1) < T :=
      not_le.mp (Nat.find_min hunb (Nat.sub_lt hpos Nat.one_pos))
    rw [hout] at hlt
    have hcast : ((Nat.find hunb - 1 : ℕ) : ℝ) = (Nat.find hunb : ℝ) - 1 := by
      rw [Nat.cast_sub hpos]
      simp
    rw [hcast] at hlt
    have h1 : ((Nat.find hunb : ℝ) - 1) / s < T - a := by linarith
    rw [div_lt_iff₀ hs, mul_comm] at h1
    linarith

/-- **The long-run number of output samples.** When output sample `k` of
speaker `r` leaves at `a r + k / s r`, with `s r > 0` output samples per
second, the long-run number of output samples per second, averaged over the
speakers, is at most the mean of the `s r`. -/
theorem World.longRun_outputs_le_rate (w : World H R) {a s : Fin R → ℝ} (hs : ∀ r, 0 < s r)
    (hout : ∀ (r : Fin R) (k : ℕ), (w.speaker r).out k = a r + k / s r) :
    longRun (w.accruedOutputs fun _ _ => 1) ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (s r) := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp [longRun, World.accruedOutputs]
  have hRtop : ((R : ℝ≥0∞))⁻¹ ≠ ⊤ := by
    simpa using hR.ne'
  have hunb : ∀ (T : Time) (r : Fin R), ∃ k, T ≤ (w.speaker r).out k := by
    intro T r
    obtain ⟨k, hk⟩ := exists_nat_gt ((T - a r) * s r)
    refine ⟨k, ?_⟩
    rw [hout]
    have h1 : T - a r < (k : ℝ) / s r := by
      rw [lt_div_iff₀ (hs r)]
      exact hk
    linarith
  have hev : ∀ᶠ T : ℝ in atTop, ∀ r, 0 ≤ s r * (T - a r) + 1 := by
    rw [eventually_all]
    intro r
    filter_upwards [eventually_ge_atTop (a r)] with T hT
    have h1 := mul_nonneg (hs r).le (sub_nonneg.mpr hT)
    linarith
  have hbound : ∀ᶠ T : ℝ in atTop, w.accruedOutputs (fun _ _ => 1) T
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (s r * (T - a r) + 1) := by
    filter_upwards [hev] with T hT
    rw [w.accruedOutputs_eq_sum _ (hunb T)]
    gcongr with r
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal
      ((w.speaker r).find_le_of_line (hs r) (hout r) (hunb T r) (hT r))
  have hlim : ∀ r, Tendsto
      (fun T : ℝ => ENNReal.ofReal (s r * (T - a r) + 1) / ENNReal.ofReal T) atTop
      (𝓝 (ENNReal.ofReal (s r))) := by
    intro r
    have hinv : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have h1 : Tendsto (fun T : ℝ => s r + (1 - s r * a r) * T⁻¹) atTop (𝓝 (s r)) := by
      have := (tendsto_const_nhds (x := s r)).add (hinv.const_mul (1 - s r * a r))
      rwa [mul_zero, add_zero] at this
    refine (ENNReal.tendsto_ofReal h1).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [← ENNReal.ofReal_div_of_pos hT]
    congr 1
    field_simp
    ring
  have hsumlim := tendsto_finsetSum Finset.univ fun r _ => hlim r
  have hall := ENNReal.Tendsto.const_mul hsumlim (Or.inr hRtop)
  refine longRun_le_of_tendsto hbound (hall.congr fun T => ?_)
  rw [mul_div_assoc, div_eq_mul_inv, Finset.sum_mul]
  simp only [div_eq_mul_inv]

/-- **A playback counts at most one discontinuity for each output sample.** -/
theorem World.discontinuities_le_outputs (w : World H R) (plays : Fin R → ℕ → Option ℝ) :
    w.discontinuities plays ≤ longRun (w.accruedOutputs fun _ _ => 1) := by
  classical
  unfold World.discontinuities
  refine w.longRun_outputs_le 0 (fun r k _ => ?_) (fun r k => ENNReal.natCast_ne_top _)
  have h : discontinuityAt (plays r) k ≤ 1 := by
    unfold discontinuityAt
    split_ifs <;> simp
  exact_mod_cast h

/-! ## Missed samples on a line of any slope -/

/-- **The missed samples of an output sample that plays after a gap, for any
slope.** Suppose that from output sample `K` on every played position lies on
the line `a + c * k`, with `c > 0` and `c - 1 ≤ d`. An output sample that
plays the source, after an earlier one from `K` on did, counts at most `d`
missed samples for itself and for each output sample of the gap before
it. -/
theorem missedAt_le_of_slope {plays : ℕ → Option ℝ} {a c : ℝ} {K : ℕ}
    (hline : ∀ k, K ≤ k → ∀ x, plays k = some x → x = a + c * k) (hc0 : 0 < c)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : c - 1 ≤ d) {k j : ℕ} (hj : K ≤ j) (hjk : j < k)
    (hpj : (plays j).isSome) {y : ℝ} (hy : plays k = some y) :
    (missedAt plays k : ℝ) ≤ d * (gapBefore plays k + 1) := by
  classical
  have hj1 : j ≤ k - 1 := by omega
  have hj₀ := Nat.le_findGreatest (P := fun j => (plays j).isSome) hj1 hpj
  have hsome := Nat.findGreatest_spec (P := fun j => (plays j).isSome) hj1 hpj
  have hle := Nat.findGreatest_le (P := fun j => (plays j).isSome) (k - 1)
  obtain ⟨j₀, hj₀def⟩ : ∃ j₀, j₀ = Nat.findGreatest (fun j => (plays j).isSome) (k - 1) :=
    ⟨_, rfl⟩
  rw [← hj₀def] at hj₀ hsome hle
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  have hxl := hline j₀ (hj.trans hj₀) x hx
  have hyl := hline k (hj.trans hjk.le) y hy
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = k - 1 - j₀ := ⟨_, rfl⟩
  have hkj : (k : ℝ) - j₀ = g + 1 := by
    have h1 : k = j₀ + g + 1 := by omega
    rw [h1]
    push_cast
    ring
  have hyx : y - x = c * ((g : ℝ) + 1) := by
    rw [hxl, hyl, ← hkj]
    ring
  have hgap : gapBefore plays k = g := by
    simp only [gapBefore, hy]
    rw [← hj₀def, hg]
  have hmissed : missedAt plays k
      = (⌊y - x - 1⌋ - ((g : ℕ) : ℤ)).toNat + ⌊1 - (y - x)⌋.toNat := by
    simp only [missedAt, hy]
    rw [ite_eq_left ⟨j, hjk, hpj⟩, ← hj₀def]
    simp only [hx]
    rw [hg]
  have hg1' : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  have hcg := mul_pos hc0 hg1'
  -- No frame is played a second time.
  have hrep : ⌊1 - (y - x)⌋.toNat = 0 := by
    have hlt : ⌊1 - (y - x)⌋ < 1 := by
      rw [Int.floor_lt]
      push_cast
      linarith
    exact Int.toNat_eq_zero.mpr (by omega)
  rw [hmissed, hrep, add_zero, hgap]
  refine toNat_cast_le ?_ (mul_nonneg hd0 hg1'.le)
  have hfl := Int.floor_le (y - x - 1)
  have h1 := mul_le_mul_of_nonneg_right hd hg1'.le
  have e : (c - 1) * ((g : ℝ) + 1) = c * ((g : ℝ) + 1) - g - 1 := by ring
  push_cast
  linarith

/-- From some output sample on, the missed samples that an output sample
counts are at most one, plus `d` for itself and for each output sample of the
gap before it. -/
theorem exists_missedAt_le_of_slope {plays : ℕ → Option ℝ} {a c : ℝ} {K : ℕ}
    (hline : ∀ k, K ≤ k → ∀ x, plays k = some x → x = a + c * k) (hc0 : 0 < c)
    {d : ℝ≥0} (hd : c - 1 ≤ d) :
    ∃ N₀ : ℕ, ∀ k, N₀ ≤ k →
      (missedAt plays k : ℝ≥0∞) ≤ 1 + (d : ℝ≥0∞) * gapBefore plays k + d := by
  classical
  have hnone : ∀ k, plays k = none →
      (missedAt plays k : ℝ≥0∞) ≤ 1 + (d : ℝ≥0∞) * gapBefore plays k + d := by
    intro k hk
    have e1 : missedAt plays k = 1 := by simp [missedAt, hk]
    rw [e1, Nat.cast_one, add_assoc]
    exact le_self_add
  by_cases hex : ∃ j, K ≤ j ∧ (plays j).isSome
  · obtain ⟨j, hj, hpj⟩ := hex
    refine ⟨j + 1, fun k hk => ?_⟩
    cases hpk : plays k with
    | none => exact hnone k hpk
    | some y =>
      have hreal := missedAt_le_of_slope hline hc0 d.coe_nonneg hd hj (by omega) hpj hpk
      have hnn : ((missedAt plays k : ℕ) : ℝ≥0) ≤ d * (gapBefore plays k + 1) := by
        exact_mod_cast hreal
      have henn : ((missedAt plays k : ℕ) : ℝ≥0∞) ≤ (d : ℝ≥0∞) * (gapBefore plays k + 1) := by
        exact_mod_cast hnn
      calc ((missedAt plays k : ℕ) : ℝ≥0∞) ≤ (d : ℝ≥0∞) * (gapBefore plays k + 1) := henn
        _ = (d : ℝ≥0∞) * gapBefore plays k + d := by ring
        _ ≤ 1 + ((d : ℝ≥0∞) * gapBefore plays k + d) := le_add_self
        _ = 1 + (d : ℝ≥0∞) * gapBefore plays k + d := (add_assoc _ _ _).symm
  · refine ⟨K, fun k hk => hnone k ?_⟩
    by_contra hsome
    exact hex ⟨k, hk, Option.isSome_iff_ne_none.mpr hsome⟩

/-- **The missed samples of a speaker that plays a line of any slope, or
nothing.** There is a finite constant such that the missed samples counted
over the first `M` output samples are at most the constant plus `1 + 2 d`
times `M`, for every `M`. -/
theorem sum_missedAt_le_of_slope {plays : ℕ → Option ℝ} {a c : ℝ} {K : ℕ}
    (hline : ∀ k, K ≤ k → ∀ x, plays k = some x → x = a + c * k) (hc0 : 0 < c)
    {d : ℝ≥0} (hd : c - 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ M : ℕ,
      ∑ k ∈ Finset.range M, (missedAt plays k : ℝ≥0∞)
        ≤ C + ((1 + 2 * d : ℝ≥0) : ℝ≥0∞) * M := by
  obtain ⟨N₀, hN₀⟩ := exists_missedAt_le_of_slope hline hc0 hd
  refine ⟨∑ k ∈ Finset.range N₀, (missedAt plays k : ℝ≥0∞),
    ENNReal.sum_ne_top.mpr fun k _ => ENNReal.natCast_ne_top _, fun M => ?_⟩
  have hpoint : ∀ k, (missedAt plays k : ℝ≥0∞)
      ≤ (if k < N₀ then (missedAt plays k : ℝ≥0∞) else 0)
        + (1 + (d : ℝ≥0∞) * gapBefore plays k + d) := by
    intro k
    by_cases hk : k < N₀
    · simp only [hk, ite_true]
      exact le_self_add
    · simp only [hk, ite_false, zero_add]
      exact hN₀ k (not_lt.mp hk)
  have hprefix : ∑ k ∈ Finset.range M, (if k < N₀ then (missedAt plays k : ℝ≥0∞) else 0)
      ≤ ∑ k ∈ Finset.range N₀, (missedAt plays k : ℝ≥0∞) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset fun k hk => ?_
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  have hgaps : ∑ k ∈ Finset.range M, (gapBefore plays k : ℝ≥0∞) ≤ M := by
    have h := sum_gapBefore_le plays M
    have hmiss : ∑ k ∈ Finset.range M, missingAt plays k ≤ M := by
      calc ∑ k ∈ Finset.range M, missingAt plays k ≤ ∑ _k ∈ Finset.range M, 1 :=
            Finset.sum_le_sum fun k _ => missingAt_le_one plays k
        _ = M := by simp
    have h' : ∑ k ∈ Finset.range M, gapBefore plays k ≤ M := by omega
    exact_mod_cast h'
  have hones : ∑ _k ∈ Finset.range M, (1 : ℝ≥0∞) = M := by simp
  have hds : ∑ _k ∈ Finset.range M, (d : ℝ≥0∞) = M * d := by simp
  calc ∑ k ∈ Finset.range M, (missedAt plays k : ℝ≥0∞)
      ≤ ∑ k ∈ Finset.range M, ((if k < N₀ then (missedAt plays k : ℝ≥0∞) else 0)
          + (1 + (d : ℝ≥0∞) * gapBefore plays k + d)) :=
        Finset.sum_le_sum fun k _ => hpoint k
    _ = ∑ k ∈ Finset.range M, (if k < N₀ then (missedAt plays k : ℝ≥0∞) else 0)
        + ((M : ℝ≥0∞) + (d : ℝ≥0∞) * ∑ k ∈ Finset.range M, (gapBefore plays k : ℝ≥0∞)
          + M * d) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hones, hds,
          Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range N₀, (missedAt plays k : ℝ≥0∞)
        + ((M : ℝ≥0∞) + (d : ℝ≥0∞) * M + M * d) := by
        gcongr
    _ = ∑ k ∈ Finset.range N₀, (missedAt plays k : ℝ≥0∞)
        + ((1 + 2 * d : ℝ≥0) : ℝ≥0∞) * M := by
        push_cast
        ring

/-- **The long-run missed samples of a playback of lines of any slope.**
Suppose that from output sample `K` on every played position of speaker `r`
lies on the line `a r + c r * k`, with `c r > 0` and `c r - 1 ≤ d`, and that
the output samples of every speaker leave without end. Then the long-run
number of missed samples is at most `1 + 2 d` times the long-run number of
output samples. -/
theorem World.missed_le_of_slope (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {a c : Fin R → ℝ} {K : ℕ} {d : ℝ≥0}
    (hline : ∀ r k, K ≤ k → ∀ x, plays r k = some x → x = a r + c r * k)
    (hc : ∀ r, 0 < c r) (hd : ∀ r, c r - 1 ≤ d)
    (hout : ∀ r (T : Time), ∃ k, T ≤ (w.speaker r).out k) :
    w.missed plays
      ≤ ((1 + 2 * d : ℝ≥0) : ℝ≥0∞) * longRun (w.accruedOutputs fun _ _ => 1) := by
  choose C hCfin hC using fun r => sum_missedAt_le_of_slope (hline r) (hc r) (hd r)
  refine longRun_le_mul_add (C := (R : ℝ≥0∞)⁻¹ * ∑ r, C r) (average_ne_top hCfin) _ fun T => ?_
  rw [w.accruedOutputs_eq_sum _ (fun r => hout r T), w.accruedOutputs_eq_sum _ (fun r => hout r T)]
  calc (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ Finset.range (Nat.find (hout r T)),
        (missedAt (plays r) k : ℝ≥0∞)
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, (C r + ((1 + 2 * d : ℝ≥0) : ℝ≥0∞)
          * ∑ _k ∈ Finset.range (Nat.find (hout r T)), 1) := by
        gcongr with r
        have h := hC r (Nat.find (hout r T))
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        exact h
    _ = (R : ℝ≥0∞)⁻¹ * ∑ r, C r + ((1 + 2 * d : ℝ≥0) : ℝ≥0∞)
        * ((R : ℝ≥0∞)⁻¹ * ∑ r, ∑ _k ∈ Finset.range (Nat.find (hout r T)), 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring

end Unisono.Spec
