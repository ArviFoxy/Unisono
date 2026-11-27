/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.LateBlocks

/-!
# The late rate of a held level

The late rate of the controller at a level `L` (`lateRate`) counts output
samples: the long-run number per second of output samples whose capture
block arrives too late, averaged over the speakers.
`Unisono.Solutions.Controller.LateBlocks` gives the long-run fraction of
capture blocks that are slow. This file passes from blocks to output
samples.

An output sample needs one capture block, the block that holds the last
frame that the resampler reads for it (`neededBlock`). The positions that
are due at consecutive output samples of a speaker differ by `γ`, the rate
of the capture device's clock divided by the rate of the playback device's
clock. The positions that need one given block lie in an interval of
`blockSize` frames, so at most `⌈blockSize / γ⌉` output samples of one
speaker need the same block (`card_le_of_line`, `neededBlock_mem`).

**Theorem** (`lateRate_le_of_slowBlocks`). In a world whose clocks run at
constant rates, suppose that for each speaker `r` the fraction of the first
`n` capture blocks that are slow for `r` converges to `q r`. Then the late
rate is at most the mean over the speakers of

  `(output samples per second of the speaker's device
    + capture blocks per second) * q r`.

The first rate is `rate * exp (deviceLogRate (some (device r)))` and the
second is `rate * exp (deviceLogRate none) / blockSize`, both in true time.
The second term is what the count by blocks loses: one output sample for
each slow block.

**Theorem** (`ae_lateRate_le`). In every random world of a member with
steady hosts, in which no speaker is on the sender's host, the bound holds
in almost every outcome with `q r` the probability `lateProbability` of the
member for the least delay from the sender to the host of `r` and the least
margin of `r`.

The cost of the controller in almost every outcome, and its mean, are in
`Unisono.Solutions.Controller.ExpectedCost`.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R}

/-! ## Limits -/

/-- If the mean of the first `n` terms of a sequence converges to `q`, then
the sum of its first `⌈ν T + C⌉` terms, divided by `T`, converges to `q ν`
as `T` grows. A constant `K` and a factor `M` are carried along. -/
theorem tendsto_sum_ceil_div {S : ℕ → ℝ} {q ν : ℝ} (hν : 0 < ν) (C K M : ℝ)
    (hS : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * S n) atTop (𝓝 q)) :
    Tendsto (fun T : ℝ => (K + M * S ⌈ν * T + C⌉₊) / T) atTop (𝓝 (M * (q * ν))) := by
  have hlin : Tendsto (fun T : ℝ => ν * T + C) atTop atTop :=
    tendsto_atTop_add_const_right _ C (tendsto_id.const_mul_atTop hν)
  have hN : Tendsto (fun T : ℝ => ⌈ν * T + C⌉₊) atTop atTop := tendsto_nat_ceil_atTop.comp hlin
  have hfrac : Tendsto (fun T : ℝ => ((⌈ν * T + C⌉₊ : ℕ) : ℝ)⁻¹ * S ⌈ν * T + C⌉₊) atTop (𝓝 q) :=
    hS.comp hN
  have hinv : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlo : Tendsto (fun T : ℝ => ν + C * T⁻¹) atTop (𝓝 ν) := by
    have := (tendsto_const_nhds (x := ν)).add (hinv.const_mul C)
    rwa [mul_zero, add_zero] at this
  have hhi : Tendsto (fun T : ℝ => ν + (C + 1) * T⁻¹) atTop (𝓝 ν) := by
    have := (tendsto_const_nhds (x := ν)).add (hinv.const_mul (C + 1))
    rwa [mul_zero, add_zero] at this
  have hratio : Tendsto (fun T : ℝ => ((⌈ν * T + C⌉₊ : ℕ) : ℝ) / T) atTop (𝓝 ν) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT
      have h1 := Nat.le_ceil (ν * T + C)
      rw [le_div_iff₀ hT]
      have e : (ν + C * T⁻¹) * T = ν * T + C := by
        field_simp
      rw [e]
      exact h1
    · filter_upwards [eventually_gt_atTop 0, hlin.eventually_ge_atTop 0] with T hT hpos
      have h1 := (Nat.ceil_lt_add_one hpos).le
      rw [div_le_iff₀ hT]
      have e : (ν + (C + 1) * T⁻¹) * T = ν * T + C + 1 := by
        field_simp
        ring
      rw [e]
      exact h1
  have hK : Tendsto (fun T : ℝ => K * T⁻¹) atTop (𝓝 0) := by
    have := hinv.const_mul K
    rwa [mul_zero] at this
  have hmain := hK.add ((hfrac.mul hratio).const_mul M)
  rw [zero_add] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hN.eventually_gt_atTop 0] with T hT hNT
  have hN0 : ((⌈ν * T + C⌉₊ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hNT.ne'
  have e : ((⌈ν * T + C⌉₊ : ℕ) : ℝ)⁻¹ * S ⌈ν * T + C⌉₊ * (((⌈ν * T + C⌉₊ : ℕ) : ℝ) / T)
      = S ⌈ν * T + C⌉₊ / T := by
    field_simp
  rw [e]
  ring

/-! ## Output samples that need one block -/

/-- Natural numbers whose values on a line of slope `γ > 0` lie in one
interval of length `B`, open on the left: at most `⌈B / γ⌉` of them. -/
theorem card_le_of_line {s : Finset ℕ} {x : ℕ → ℝ} {x₀ γ lo B : ℝ} (hγ : 0 < γ)
    (hx : ∀ k, x k = x₀ + γ * k) (h : ∀ k ∈ s, lo < x k ∧ x k ≤ lo + B) :
    s.card ≤ ⌈B / γ⌉₊ := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hsub : s ⊆ Finset.Ico (s.min' hne) (s.min' hne + ⌈B / γ⌉₊) := by
      intro k hk
      rw [Finset.mem_Ico]
      refine ⟨Finset.min'_le s k hk, ?_⟩
      have h1 := (h k hk).2
      have h2 := (h _ (Finset.min'_mem s hne)).1
      rw [hx] at h1 h2
      have hlt : ((k : ℝ) - (s.min' hne : ℕ)) * γ < B := by
        have e : ((k : ℝ) - (s.min' hne : ℕ)) * γ = γ * k - γ * (s.min' hne : ℕ) := by ring
        rw [e]
        linarith
      have hlt' : (k : ℝ) - (s.min' hne : ℕ) < B / γ := by
        rw [lt_div_iff₀ hγ]
        exact hlt
      have hceil := Nat.le_ceil (B / γ)
      have hcast : (k : ℝ) < ((s.min' hne + ⌈B / γ⌉₊ : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hcast
    calc s.card ≤ (Finset.Ico (s.min' hne) (s.min' hne + ⌈B / γ⌉₊)).card :=
          Finset.card_le_card hsub
      _ = ⌈B / γ⌉₊ := by simp

/-- The frames that need capture block `c`: a position `x` past the start of
the stream needs the block `c` only if `x + lookahead` lies in the interval
from `c * blockSize`, excluded, to `(c + 1) * blockSize`, included. -/
theorem neededBlock_mem (m : GenerativeWorld H R) (lookahead : ℕ+) {x : ℝ}
    (hx : 0 < x + ((lookahead : ℕ) : ℝ)) :
    ((neededBlock m lookahead x : ℕ) : ℝ) * m.blockSize < x + ((lookahead : ℕ) : ℝ)
      ∧ x + ((lookahead : ℕ) : ℝ)
        ≤ ((neededBlock m lookahead x : ℕ) : ℝ) * m.blockSize + m.blockSize := by
  have hB := m.blockSize_pos
  have hceil : 0 < ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := Nat.ceil_pos.mpr hx
  obtain ⟨N, hN⟩ : ∃ N, N + 1 = ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := ⟨_, Nat.sub_add_cancel hceil⟩
  have hNeed : neededBlock m lookahead x = N / m.blockSize := by
    unfold neededBlock
    rw [← hN, Nat.add_sub_cancel]
  rw [hNeed]
  have h1 : N / m.blockSize * m.blockSize ≤ N := Nat.div_mul_le_self N m.blockSize
  have h2 : N < N / m.blockSize * m.blockSize + m.blockSize := Nat.lt_div_mul_add hB
  constructor
  · have hlt : N / m.blockSize * m.blockSize < ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := by omega
    have h3 := Nat.lt_ceil.mp hlt
    push_cast at h3
    exact h3
  · have hle : ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ ≤ N / m.blockSize * m.blockSize + m.blockSize := by
      omega
    have h3 := Nat.le_ceil (x + ((lookahead : ℕ) : ℝ))
    have h4 : ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ ((N / m.blockSize * m.blockSize + m.blockSize : ℕ) : ℝ) := by exact_mod_cast hle
    push_cast at h4
    linarith

theorem slowAt_le_one (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R)
    (w : World H R) (lookahead : ℕ+) (L : ℝ) (r : Fin R) (k : ℕ) :
    slowAt m f d w lookahead L r k ≤ 1 := by
  unfold slowAt
  split_ifs <;> simp

/-- **Slow output samples, counted by their blocks.** Among the first `M`
output samples of speaker `r`, those whose block is slow number at most `K`
plus `⌈blockSize / γ⌉` for each slow block among the first `N` capture
blocks. Here `γ` is the rate of the capture device's clock divided by the
rate of the playback device's clock, the positions that are due are past the
start of the stream from output sample `K` on, and the output samples from
`K` to `M` need blocks before block `N`. -/
theorem sum_slowAt_le (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ) (r : Fin R)
    {K M N : ℕ} (hK : ∀ k, K ≤ k → 0 ≤ duePosition m f d w L r k)
    (hN : ∀ k, K ≤ k → k < M → neededBlock m lookahead (duePosition m f d w L r k) < N) :
    ∑ k ∈ Finset.range M, slowAt m f d w lookahead L r k
      ≤ K + ⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
            / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊
          * ∑ c ∈ Finset.range N,
            if marginLeast m f d lookahead L r < blockDelay m f d w r c then 1 else 0 := by
  classical
  have hγ : 0 < Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) := div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hsub : Finset.range M ⊆ Finset.range K ∪ Finset.Ico K M := by
    intro k hk
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    rw [Finset.mem_range] at hk
    omega
  have hdisj : Disjoint (Finset.range K) (Finset.Ico K M) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico] at hk'
    omega
  have hfirst : ∑ k ∈ Finset.range K, slowAt m f d w lookahead L r k ≤ K := by
    calc ∑ k ∈ Finset.range K, slowAt m f d w lookahead L r k
        ≤ ∑ _k ∈ Finset.range K, 1 :=
          Finset.sum_le_sum fun k _ => slowAt_le_one m f d w lookahead L r k
      _ = K := by simp
  have hmaps : ∀ k ∈ Finset.Ico K M,
      neededBlock m lookahead (duePosition m f d w L r k) ∈ Finset.range N := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact Finset.mem_range.mpr (hN k hk.1 hk.2)
  have hfiber : ∀ c ∈ Finset.range N,
      ∑ _k ∈ (Finset.Ico K M).filter
          (fun k => neededBlock m lookahead (duePosition m f d w L r k) = c),
          (if marginLeast m f d lookahead L r < blockDelay m f d w r c then 1 else 0)
        ≤ ⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
            / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊
          * (if marginLeast m f d lookahead L r < blockDelay m f d w r c then 1 else 0) := by
    intro c _
    rw [Finset.sum_const, smul_eq_mul]
    refine Nat.mul_le_mul_right _ ?_
    refine card_le_of_line (x := fun k => duePosition m f d w L r k)
      (lo := (c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)) hγ (duePosition_eq hS L r) ?_
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ico] at hk
    have hx0 := hK k hk.1.1
    have ha : (0 : ℝ) < ((lookahead : ℕ) : ℝ) := by exact_mod_cast lookahead.pos
    have hmem := neededBlock_mem m lookahead (x := duePosition m f d w L r k) (by linarith)
    rw [hk.2] at hmem
    constructor <;> linarith [hmem.1, hmem.2]
  have hsecond : ∑ k ∈ Finset.Ico K M, slowAt m f d w lookahead L r k
      ≤ ⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
            / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊
          * ∑ c ∈ Finset.range N,
            if marginLeast m f d lookahead L r < blockDelay m f d w r c then 1 else 0 := by
    calc ∑ k ∈ Finset.Ico K M, slowAt m f d w lookahead L r k
        = ∑ c ∈ Finset.range N, ∑ _k ∈ (Finset.Ico K M).filter
            (fun k => neededBlock m lookahead (duePosition m f d w L r k) = c),
            (if marginLeast m f d lookahead L r < blockDelay m f d w r c then 1 else 0) :=
          (Finset.sum_fiberwise_of_maps_to' hmaps
            (fun c => if marginLeast m f d lookahead L r < blockDelay m f d w r c
              then 1 else 0)).symm
      _ ≤ ∑ c ∈ Finset.range N,
            ⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
              / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊
            * (if marginLeast m f d lookahead L r < blockDelay m f d w r c then 1 else 0) :=
          Finset.sum_le_sum hfiber
      _ = _ := (Finset.mul_sum _ _ _).symm
  calc ∑ k ∈ Finset.range M, slowAt m f d w lookahead L r k
      ≤ ∑ k ∈ Finset.range K ∪ Finset.Ico K M, slowAt m f d w lookahead L r k :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ k ∈ Finset.range K, slowAt m f d w lookahead L r k
        + ∑ k ∈ Finset.Ico K M, slowAt m f d w lookahead L r k := Finset.sum_union hdisj
    _ ≤ _ := add_le_add hfirst hsecond

/-! ## The late rate -/

/-- **The long-run number of output samples whose block is slow.** In a
world whose clocks run at constant rates, suppose that for each speaker `r`
the fraction of the first `n` capture blocks that take more than the least
margin of `r` converges to `q r`. Then the long-run number per second of
output samples whose block takes more than the least margin, averaged over
the speakers, is at most the mean over the speakers of `⌈blockSize / γ⌉`
times `q r` times the number of capture blocks per second. Here `γ` is the
rate of the capture device's clock divided by the rate of the clock of the
speaker's playback device. -/
theorem longRun_slowAt_le (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ)
    {q : Fin R → ℝ}
    (hq : ∀ r, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ c ∈ Finset.range n,
        if marginLeast m f d lookahead L r < blockDelay m f d w r c then (1 : ℝ) else 0)
      atTop (𝓝 (q r))) :
    longRun (w.accruedOutputs fun r k => (slowAt m f d w lookahead L r k : ℝ≥0∞))
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
          ((⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
              / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊ : ℝ)
            * (q r * (m.rate * Real.exp (d.deviceLogRate none) / m.blockSize))) := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp [longRun, World.accruedOutputs]
  have hRtop : ((R : ℝ≥0∞))⁻¹ ≠ ⊤ := by
    simpa using hR.ne'
  have hρg : 0 < m.rate * Real.exp (d.deviceLogRate none) := mul_pos m.rate_pos (Real.exp_pos _)
  have hBpos : (0 : ℝ) < m.blockSize := by exact_mod_cast m.blockSize_pos
  have hν : 0 < m.rate * Real.exp (d.deviceLogRate none) / m.blockSize := div_pos hρg hBpos
  choose K hK using fun r => exists_duePosition_nonneg hS L r
  -- The bound on the accrued count at every horizon.
  obtain ⟨G, hG⟩ : ∃ G : Fin R → Time → ℝ, G = fun r T =>
      (K r : ℝ) + (⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
          / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊ : ℝ)
        * ∑ c ∈ Finset.range
            ⌈m.rate * Real.exp (d.deviceLogRate none) / m.blockSize * T
              + (((lookahead : ℕ) : ℝ) - m.rate * Real.exp (d.deviceLogRate none)
                  * (latencyOf m f d L r + w.source.capture 0)) / m.blockSize⌉₊,
          if marginLeast m f d lookahead L r < blockDelay m f d w r c then (1 : ℝ) else 0 :=
    ⟨_, rfl⟩
  have hout : ∀ (T : Time) (r : Fin R), ∃ k, T ≤ (w.speaker r).out k := by
    intro T r
    obtain ⟨b, hb⟩ := hS.asked_unbounded r T
    exact ⟨(w.speaker r).first b, (hb.trans (hS.asked_lt_out r b)).le⟩
  have hbound : ∀ T : Time,
      w.accruedOutputs (fun r k => (slowAt m f d w lookahead L r k : ℝ≥0∞)) T
        ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (G r T) := by
    intro T
    rw [w.accruedOutputs_eq_sum _ (hout T)]
    gcongr with r
    have hNle : ∀ k, K r ≤ k → k < Nat.find (hout T r) →
        neededBlock m lookahead (duePosition m f d w L r k)
          < ⌈m.rate * Real.exp (d.deviceLogRate none) / m.blockSize * T
              + (((lookahead : ℕ) : ℝ) - m.rate * Real.exp (d.deviceLogRate none)
                  * (latencyOf m f d L r + w.source.capture 0)) / m.blockSize⌉₊ := by
      intro k hk hkM
      have hlt : (w.speaker r).out k < T := not_le.mp (Nat.find_min (hout T r) hkM)
      have hx0 := hK r k hk
      have ha : (0 : ℝ) < ((lookahead : ℕ) : ℝ) := by exact_mod_cast lookahead.pos
      have hmem := (neededBlock_mem m lookahead (x := duePosition m f d w L r k)
        (by linarith)).1
      have hdue : duePosition m f d w L r k
          < m.rate * Real.exp (d.deviceLogRate none)
            * (T - latencyOf m f d L r - w.source.capture 0) := by
        unfold duePosition
        exact mul_lt_mul_of_pos_left (by linarith) hρg
      have hreal : ((neededBlock m lookahead (duePosition m f d w L r k) : ℕ) : ℝ)
          < m.rate * Real.exp (d.deviceLogRate none) / m.blockSize * T
              + (((lookahead : ℕ) : ℝ) - m.rate * Real.exp (d.deviceLogRate none)
                  * (latencyOf m f d L r + w.source.capture 0)) / m.blockSize := by
        have e : m.rate * Real.exp (d.deviceLogRate none) / m.blockSize * T
              + (((lookahead : ℕ) : ℝ) - m.rate * Real.exp (d.deviceLogRate none)
                  * (latencyOf m f d L r + w.source.capture 0)) / m.blockSize
            = (m.rate * Real.exp (d.deviceLogRate none)
                * (T - latencyOf m f d L r - w.source.capture 0)
              + ((lookahead : ℕ) : ℝ)) / m.blockSize := by
          field_simp
          ring
        rw [e, lt_div_iff₀ hBpos]
        linarith
      have hceil := Nat.le_ceil (m.rate * Real.exp (d.deviceLogRate none) / m.blockSize * T
              + (((lookahead : ℕ) : ℝ) - m.rate * Real.exp (d.deviceLogRate none)
                  * (latencyOf m f d L r + w.source.capture 0)) / m.blockSize)
      exact_mod_cast hreal.trans_le hceil
    have hsum := sum_slowAt_le hS lookahead L r (hK r) hNle
    have hcast : (∑ k ∈ Finset.range (Nat.find (hout T r)),
        (slowAt m f d w lookahead L r k : ℝ≥0∞))
        = ENNReal.ofReal ((∑ k ∈ Finset.range (Nat.find (hout T r)),
            slowAt m f d w lookahead L r k : ℕ) : ℝ) := by
      rw [ENNReal.ofReal_natCast]
      push_cast
      rfl
    rw [hcast]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsum' : ((∑ k ∈ Finset.range (Nat.find (hout T r)),
        slowAt m f d w lookahead L r k : ℕ) : ℝ)
        ≤ ((K r + ⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
            / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊
          * ∑ c ∈ Finset.range
              ⌈m.rate * Real.exp (d.deviceLogRate none) / m.blockSize * T
                + (((lookahead : ℕ) : ℝ) - m.rate * Real.exp (d.deviceLogRate none)
                    * (latencyOf m f d L r + w.source.capture 0)) / m.blockSize⌉₊,
            if marginLeast m f d lookahead L r < blockDelay m f d w r c then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast hsum
    rw [hG]
    push_cast at hsum' ⊢
    exact hsum'
  -- The bound per second converges.
  have hlim : ∀ r, Tendsto (fun T : Time => ENNReal.ofReal (G r T) / ENNReal.ofReal T) atTop
      (𝓝 (ENNReal.ofReal
        ((⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
            / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊ : ℝ)
          * (q r * (m.rate * Real.exp (d.deviceLogRate none) / m.blockSize))))) := by
    intro r
    have h1 := tendsto_sum_ceil_div hν
      ((((lookahead : ℕ) : ℝ) - m.rate * Real.exp (d.deviceLogRate none)
        * (latencyOf m f d L r + w.source.capture 0)) / m.blockSize) (K r)
      (⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
        / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊ : ℝ) (hq r)
    refine (ENNReal.tendsto_ofReal h1).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [ENNReal.ofReal_div_of_pos hT, hG]
  have hsumlim := tendsto_finsetSum Finset.univ fun r _ => hlim r
  have hall := ENNReal.Tendsto.const_mul hsumlim (Or.inr hRtop)
  refine longRun_le_of_tendsto (Eventually.of_forall hbound) (hall.congr fun T => ?_)
  rw [mul_div_assoc, div_eq_mul_inv, Finset.sum_mul]
  simp only [div_eq_mul_inv]

/-- **The late rate, from the fraction of slow blocks.** In a world whose
clocks run at constant rates, suppose that for each speaker `r` the fraction
of the first `n` capture blocks that take more than the least margin of `r`
converges to `q r`. Then the late rate is at most the mean over the speakers
of `q r` times the sum of two rates in true time: the output samples per
second of the speaker's playback device, and the capture blocks per second.
The second rate is what the count by blocks loses. -/
theorem lateRate_le_of_slowBlocks (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ)
    {q : Fin R → ℝ}
    (hq : ∀ r, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ c ∈ Finset.range n,
        if marginLeast m f d lookahead L r < blockDelay m f d w r c then (1 : ℝ) else 0)
      atTop (𝓝 (q r))) :
    lateRate m f d w lookahead L
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
          ((m.rate * Real.exp (d.deviceLogRate (some (m.device r)))
              + m.rate * Real.exp (d.deviceLogRate none) / m.blockSize) * q r) := by
  refine (lateRate_le hS lookahead L).trans ((longRun_slowAt_le hS lookahead L hq).trans ?_)
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun r _ => ENNReal.ofReal_le_ofReal ?_)
  have hq0 : 0 ≤ q r := by
    refine ge_of_tendsto' (hq r) fun n => ?_
    refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (Finset.sum_nonneg fun c _ => ?_)
    split_ifs <;> norm_num
  have hgc := Real.exp_pos (d.deviceLogRate none)
  have hgr := Real.exp_pos (d.deviceLogRate (some (m.device r)))
  have hρ := m.rate_pos
  have hBpos : (0 : ℝ) < m.blockSize := by exact_mod_cast m.blockSize_pos
  have hratio : 0 ≤ (m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r)))) := by positivity
  have hceil := (Nat.ceil_lt_add_one hratio).le
  have hν : 0 ≤ q r * (m.rate * Real.exp (d.deviceLogRate none) / m.blockSize) := by positivity
  calc (⌈(m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
          / Real.exp (d.deviceLogRate (some (m.device r))))⌉₊ : ℝ)
        * (q r * (m.rate * Real.exp (d.deviceLogRate none) / m.blockSize))
      ≤ ((m.blockSize : ℝ) / (Real.exp (d.deviceLogRate none)
          / Real.exp (d.deviceLogRate (some (m.device r)))) + 1)
        * (q r * (m.rate * Real.exp (d.deviceLogRate none) / m.blockSize)) :=
        mul_le_mul_of_nonneg_right hceil hν
    _ = (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))
          + m.rate * Real.exp (d.deviceLogRate none) / m.blockSize) * q r := by
        field_simp

/-- **The late rate of a held level in a member with steady hosts.** In
every random world of a member with steady hosts in which no speaker is on
the sender's host, in almost every outcome, the late rate at the level `L`
is at most the mean over the speakers of the following product. The first
factor is the sum of two rates in true time: the output samples per second
of the speaker's playback device, and the capture blocks per second. The
second factor is the probability, in the member, that a message from the
sender to the speaker's host takes more than the least margin of the
speaker (`lateProbability`). -/
theorem ae_lateRate_le [Fintype H] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D) (hf : f.SteadyHosts)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) (L : ℝ)
    (hnos : ∀ r, m.host r ≠ m.sender) :
    ∀ᵐ ω ∂P, lateRate m f (D ω) (world ω) lookahead L
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
          ((m.rate * Real.exp ((D ω).deviceLogRate (some (m.device r)))
              + m.rate * Real.exp ((D ω).deviceLogRate none) / m.blockSize)
            * lateProbability f m.sender (m.host r)
                ((D ω).split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
                (marginLeast m f (D ω) lookahead L r)) := by
  have hall : ∀ᵐ ω ∂P, ∀ r, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ c ∈ Finset.range n,
        if marginLeast m f (D ω) lookahead L r < blockDelay m f (D ω) (world ω) r c
        then (1 : ℝ) else 0) atTop
      (𝓝 (lateProbability f m.sender (m.host r)
        ((D ω).split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
        (marginLeast m f (D ω) lookahead L r))) :=
    ae_all_iff.mpr fun r => ae_tendsto_slowBlocks hD hf hB lookahead L r (hnos r)
  filter_upwards [hall, hD.ae_constantRates hf hB] with ω hω hS
  exact lateRate_le_of_slowBlocks hS lookahead L hω

end Unisono.Solutions.Controller
