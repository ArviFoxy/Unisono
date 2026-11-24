/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.ExactLatency

/-!
# The objectives of a playback with missing output samples

A solution that keeps a schedule and plays nothing when the data is late
produces a playback of the following kind: from some output sample on, each
output sample plays the position that its speaker's schedule gives, or
nothing of the source. This file bounds the six objectives of such a
playback by how often an output sample plays nothing.

**When every played position is at an exact latency**
(`World.PlaysOnlyAtLatencies`), every step of continuous playback has speed
one, so the long-run roughness is zero (`World.roughness_eq_zero_of_playsOnly`).
The bounds on latency, tracking and synchronization are in
`Unisono.Spec.ExactLatency`.

**When every played position lies on a line** `a + c * k` in the output
sample `k`, with `0 < c < 2`:

* playback breaks only where the next output sample plays nothing, so the
  long-run number of discontinuities is at most the long-run number of
  output samples that play nothing (`World.discontinuities_le_of_line`);
* an output sample that plays nothing counts as one missed sample. An output
  sample that plays after a gap counts the frames that the gap skipped beyond
  the output samples of the gap, which is at most `2 (c - 1)` per output
  sample of the gap when `c > 1` and nothing when `c ≤ 1`. So the long-run
  number of missed samples is at most `1 + 2 d` times the long-run number of
  output samples that play nothing, when `c - 1 ≤ d` for every speaker
  (`World.missed_le_of_line`). The number `c` is the rate of the capture
  device divided by the rate of the playback device; it differs from one by
  parts in a hundred thousand.

The long-run number of output samples that play nothing is the long-run
average of `missingAt` (`longRun (w.accruedOutputs ...)`), per second and
averaged over the speakers.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal NNReal
open Filter Topology

variable {H : Type} {R : ℕ}

/-! ## Long-run averages -/

/-- If, at every horizon, a cost accrued is at most a finite constant plus
`k` times another cost accrued, its long-run average is at most `k` times the
long-run average of the other. -/
theorem longRun_le_mul_add {A B : Time → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤) (k : ℝ≥0)
    (h : ∀ T, A T ≤ C + k * B T) : longRun A ≤ k * longRun B := by
  unfold longRun
  have h0 : Tendsto (fun T : ℝ => C / ENNReal.ofReal T) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_div ENNReal.tendsto_ofReal_atTop (Or.inr hC)
  rw [← limsup_weighted]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hev : ∀ᶠ T : ℝ in atTop, C / ENNReal.ofReal T ≤ ε :=
    (h0.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ε by exact_mod_cast hε))).mono
      fun T hT => hT.le
  have hbound : ∀ᶠ T : ℝ in atTop,
      A T / ENNReal.ofReal T ≤ (k : ℝ≥0∞) * B T / ENNReal.ofReal T + ε := by
    filter_upwards [hev] with T hT
    calc A T / ENNReal.ofReal T ≤ (C + k * B T) / ENNReal.ofReal T :=
          ENNReal.div_le_div_right (h T) _
      _ = C / ENNReal.ofReal T + k * B T / ENNReal.ofReal T := ENNReal.add_div
      _ ≤ ε + k * B T / ENNReal.ofReal T := by gcongr
      _ = k * B T / ENNReal.ofReal T + ε := add_comm _ _
  calc limsup (fun T => A T / ENNReal.ofReal T) atTop
      ≤ limsup (fun T : ℝ => (k : ℝ≥0∞) * B T / ENNReal.ofReal T + ε) atTop :=
        limsup_le_limsup hbound
    _ = limsup (fun T : ℝ => (k : ℝ≥0∞) * B T / ENNReal.ofReal T) atTop + ε :=
        limsup_add_const atTop _ _ (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
          (isCoboundedUnder_le_of_le atTop (x := 0) (fun _ => zero_le))

/-- When a playback device's output samples leave without end, those that
leave before the true time `T` are the first ones, up to a number. -/
theorem PlaybackDevice.tsum_out_lt (d : PlaybackDevice) {T : Time}
    (hunb : ∃ k, T ≤ d.out k) (cost : ℕ → ℝ≥0∞) :
    ∑' k, (if d.out k < T then cost k else 0)
      = ∑ k ∈ Finset.range (Nat.find hunb), cost k := by
  rw [tsum_eq_sum (s := Finset.range (Nat.find hunb))]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hlt : d.out k < T := not_le.mp (Nat.find_min hunb (Finset.mem_range.mp hk))
    simp [hlt]
  · intro k hk
    have hge : Nat.find hunb ≤ k := by simpa using hk
    have hT : T ≤ d.out k := (Nat.find_spec hunb).trans (d.out_strictMono.monotone hge)
    simp [not_lt.mpr hT]

/-- A cost of the output samples accrued until `T`, as a finite sum, when
the output samples of every speaker leave without end. -/
theorem World.accruedOutputs_eq_sum (w : World H R) (cost : Fin R → ℕ → ℝ≥0∞) {T : Time}
    (hout : ∀ r, ∃ k, T ≤ (w.speaker r).out k) :
    w.accruedOutputs cost T
      = (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ Finset.range (Nat.find (hout r)), cost r k := by
  unfold World.accruedOutputs
  congr 1
  exact Finset.sum_congr rfl fun r _ => (w.speaker r).tsum_out_lt (hout r) (cost r)

/-- A finite cost of the output samples that is at most another from some
output sample on has a long-run average at most that of the other. -/
theorem World.longRun_outputs_le (w : World H R) {cost cost' : Fin R → ℕ → ℝ≥0∞} (K : ℕ)
    (h : ∀ r k, K ≤ k → cost r k ≤ cost' r k) (hfin : ∀ r k, cost r k ≠ ⊤) :
    longRun (w.accruedOutputs cost) ≤ longRun (w.accruedOutputs cost') := by
  have hC : (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ Finset.range K, cost r k ≠ ⊤ :=
    average_ne_top fun r => ENNReal.sum_ne_top.mpr fun k _ => hfin r k
  have hmain := longRun_le_mul_add hC 1 (A := w.accruedOutputs cost)
    (B := w.accruedOutputs cost') fun T => by
    unfold World.accruedOutputs
    rw [ENNReal.coe_one, one_mul, ← mul_add, ← Finset.sum_add_distrib]
    gcongr with r
    have hsplit : ∑ k ∈ Finset.range K, cost r k
        = ∑' k, (if k < K then cost r k else 0) := by
      rw [tsum_eq_sum (s := Finset.range K)]
      · exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.mp hk]
      · intro k hk
        simp [show ¬ k < K by simpa using hk]
    rw [hsplit, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    by_cases hk : k < K
    · simp only [hk, ite_true]
      split_ifs
      · exact le_self_add
      · exact zero_le
    · simp only [hk, ite_false, zero_add]
      split_ifs
      · exact h r k (not_lt.mp hk)
      · exact le_rfl
  simpa using hmain

/-! ## Speed and roughness at exact latencies -/

/-- The next step of continuous playback after step `k` comes after `k`. -/
theorem nextContinuous_gt {plays : ℕ → Option ℝ} {k j : ℕ}
    (h : nextContinuous plays k = some j) : k < j := by
  classical
  unfold nextContinuous at h
  split_ifs at h with hex
  rw [Option.some.injEq] at h
  rw [← h]
  exact (Nat.find_spec hex).1

/-- **Playback only at exact latencies has speed one.** Every step of
continuous playback from output sample `K` on plays the source at the speed
of true time. -/
theorem World.speed_eq_one_of_playsOnly (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {K : ℕ} (h : w.PlaysOnlyAtLatencies plays L K) {r : Fin R} {k : ℕ}
    (hk : K ≤ k) {v : ℝ} (hv : w.speed plays r k = some v) : v = 1 := by
  classical
  unfold World.speed at hv
  split at hv
  · rename_i x y hx hy
    split_ifs at hv with hc
    have hE := h r k hk x hx
    have hE' := h r (k + 1) (Nat.le_succ_of_le hk) y hy
    have hpos : 0 < (w.speaker r).out (k + 1) - (w.speaker r).out k :=
      sub_pos.mpr ((w.speaker r).out_strictMono (Nat.lt_succ_self k))
    rw [Option.some.injEq] at hv
    rw [← hv, hE, hE', div_eq_one_iff_eq hpos.ne']
    ring
  · simp at hv

/-- Under playback only at exact latencies, a change of speed costs nothing
from output sample `K` on. -/
theorem World.roughnessCost_eq_zero_of_playsOnly (w : World H R)
    (plays : Fin R → ℕ → Option ℝ) {L : Fin R → ℝ} {K : ℕ}
    (h : w.PlaysOnlyAtLatencies plays L K) {r : Fin R} {k : ℕ} (hk : K ≤ k) :
    w.roughnessCost plays r k = 0 := by
  unfold World.roughnessCost
  split
  · rename_i v j hv hj
    split
    · rename_i v' hv'
      have e1 := w.speed_eq_one_of_playsOnly plays h hk hv
      have e2 := w.speed_eq_one_of_playsOnly plays h (hk.trans (nextContinuous_gt hj).le) hv'
      rw [e1, e2]
      simp
    · rfl
  · rfl

/-- **Playback only at exact latencies has no roughness in the long run.**
A gap in the playback does not change the speed on either side of it. -/
theorem World.roughness_eq_zero_of_playsOnly (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {K : ℕ} (h : w.PlaysOnlyAtLatencies plays L K) : w.roughness plays = 0 := by
  refine le_antisymm ?_ zero_le
  have hfin : (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ Finset.range (K + 1), w.roughnessCost plays r k ≠ ⊤ :=
    average_ne_top fun r => ENNReal.sum_ne_top.mpr fun k _ => by
      unfold World.roughnessCost
      split
      · split <;> simp
      · simp
  refine longRun_le hfin 0 fun T _ => ?_
  simpa using w.accruedOutputs_le _ K
    (fun r k hk => w.roughnessCost_eq_zero_of_playsOnly plays h hk.le) T

/-! ## Output samples that play nothing -/

/-- One if output sample `k` plays nothing of the source, zero if it plays
the source. -/
def missingAt (plays : ℕ → Option ℝ) (k : ℕ) : ℕ :=
  match plays k with
  | none => 1
  | some _ => 0

/-- For an output sample that plays the source: the number of output samples
between it and the last one before it that played the source. Zero for an
output sample that plays nothing. -/
def gapBefore (plays : ℕ → Option ℝ) (k : ℕ) : ℕ :=
  match plays k with
  | none => 0
  | some _ => k - 1 - Nat.findGreatest (fun j => (plays j).isSome) (k - 1)

/-- The number of output samples just before `M` that play nothing of the
source, back to the last one that plays it. -/
def trailing (plays : ℕ → Option ℝ) : ℕ → ℕ
  | 0 => 0
  | M + 1 =>
      match plays M with
      | none => trailing plays M + 1
      | some _ => 0

theorem missingAt_le_one (plays : ℕ → Option ℝ) (k : ℕ) : missingAt plays k ≤ 1 := by
  unfold missingAt
  split <;> simp

theorem trailing_le (plays : ℕ → Option ℝ) (M : ℕ) : trailing plays M ≤ M := by
  induction M with
  | zero => simp [trailing]
  | succ M ih =>
    unfold trailing
    split
    · omega
    · omega

theorem trailing_succ_none {plays : ℕ → Option ℝ} {M : ℕ} (h : plays M = none) :
    trailing plays (M + 1) = trailing plays M + 1 := by
  simp [trailing, h]

theorem trailing_succ_some {plays : ℕ → Option ℝ} {M : ℕ} {x : ℝ} (h : plays M = some x) :
    trailing plays (M + 1) = 0 := by
  simp [trailing, h]

/-- The output sample just before the trailing ones that play nothing plays
the source. -/
theorem isSome_before_trailing (plays : ℕ → Option ℝ) (M : ℕ) (h : trailing plays M < M) :
    (plays (M - 1 - trailing plays M)).isSome := by
  induction M with
  | zero => simp at h
  | succ M ih =>
    cases hM : plays M with
    | none =>
      rw [trailing_succ_none hM] at h ⊢
      have h' : trailing plays M < M := by omega
      have e : M + 1 - 1 - (trailing plays M + 1) = M - 1 - trailing plays M := by omega
      rw [e]
      exact ih h'
    | some x =>
      rw [trailing_succ_some hM]
      simp [hM]

/-- The gap before an output sample is at most the number of trailing output
samples before it that play nothing. -/
theorem gapBefore_le_trailing (plays : ℕ → Option ℝ) (M : ℕ) :
    gapBefore plays M ≤ trailing plays M := by
  unfold gapBefore
  split
  · exact Nat.zero_le _
  · rcases lt_or_ge (trailing plays M) M with hlt | hge
    · have hsome := isSome_before_trailing plays M hlt
      have hle := Nat.le_findGreatest (P := fun j => (plays j).isSome)
        (show M - 1 - trailing plays M ≤ M - 1 by omega) hsome
      omega
    · omega

/-- **Every output sample of a gap is counted once.** The gaps before the
output samples that play the source, added up, are at most the number of
output samples that play nothing. -/
theorem sum_gapBefore_le (plays : ℕ → Option ℝ) (M : ℕ) :
    ∑ k ∈ Finset.range M, gapBefore plays k + trailing plays M
      ≤ ∑ k ∈ Finset.range M, missingAt plays k := by
  induction M with
  | zero => simp [trailing]
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hgap := gapBefore_le_trailing plays M
    cases hM : plays M with
    | none =>
      have e1 : gapBefore plays M = 0 := by simp [gapBefore, hM]
      have e2 : missingAt plays M = 1 := by simp [missingAt, hM]
      have e3 : trailing plays (M + 1) = trailing plays M + 1 := by simp [trailing, hM]
      omega
    | some x =>
      have e2 : missingAt plays M = 0 := by simp [missingAt, hM]
      have e3 : trailing plays (M + 1) = 0 := by simp [trailing, hM]
      omega

/-! ## Positions on a line -/

/-- The natural number of an integer that is at most `B ≥ 0` is at most
`B`. -/
theorem toNat_cast_le {z : ℤ} {B : ℝ} (h : (z : ℝ) ≤ B) (hB : 0 ≤ B) :
    ((z.toNat : ℕ) : ℝ) ≤ B := by
  rcases le_total 0 z with hz | hz
  · have e : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]
    rw [e]
    exact h
  · rw [Int.toNat_of_nonpos hz]
    simpa using hB

/-- **The missed samples of an output sample that plays after a gap.**
Suppose that from output sample `K` on every played position lies on the
line `a + c * k`, with `0 < c < 2` and `c - 1 ≤ d`. An output sample that
plays the source, after an earlier one from `K` on did, counts at most `2 d`
missed samples for each output sample of the gap before it. -/
theorem missedAt_le_of_line {plays : ℕ → Option ℝ} {a c : ℝ} {K : ℕ}
    (hline : ∀ k, K ≤ k → ∀ x, plays k = some x → x = a + c * k) (hc0 : 0 < c) (hc2 : c < 2)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : c - 1 ≤ d) {k j : ℕ} (hj : K ≤ j) (hjk : j < k)
    (hpj : (plays j).isSome) {y : ℝ} (hy : plays k = some y) :
    (missedAt plays k : ℝ) ≤ 2 * d * gapBefore plays k := by
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
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
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
  rcases Nat.eq_zero_or_pos g with hgz | hgpos
  · -- No gap: the position advances by less than two frames.
    have hyx0 : y - x = c := by
      rw [hyx, hgz]
      simp
    have hlt : ⌊y - x - 1⌋ < 1 := by
      rw [Int.floor_lt]
      push_cast
      linarith
    have hz : (⌊y - x - 1⌋ - ((g : ℕ) : ℤ)).toNat = 0 := by
      apply Int.toNat_eq_zero.mpr
      rw [hgz]
      push_cast
      omega
    rw [hz, hgz]
    simp
  · -- A gap: the frames skipped beyond the output samples of the gap.
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hgpos
    refine toNat_cast_le ?_ (by positivity)
    have hfl := Int.floor_le (y - x - 1)
    have h1 := mul_nonneg (sub_nonneg.mpr hd) hg1'.le
    have h2 := mul_nonneg hd0 (sub_nonneg.mpr hg1)
    push_cast
    nlinarith

/-- From some output sample on, the missed samples that an output sample
counts are at most one if it plays nothing, plus `2 d` for each output sample
of the gap before it. -/
theorem exists_missedAt_le {plays : ℕ → Option ℝ} {a c : ℝ} {K : ℕ}
    (hline : ∀ k, K ≤ k → ∀ x, plays k = some x → x = a + c * k) (hc0 : 0 < c) (hc2 : c < 2)
    {d : ℝ≥0} (hd : c - 1 ≤ d) :
    ∃ N₀ : ℕ, ∀ k, N₀ ≤ k →
      (missedAt plays k : ℝ≥0∞)
        ≤ missingAt plays k + 2 * (d : ℝ≥0∞) * gapBefore plays k := by
  classical
  have hnone : ∀ k, plays k = none →
      (missedAt plays k : ℝ≥0∞) ≤ missingAt plays k + 2 * (d : ℝ≥0∞) * gapBefore plays k := by
    intro k hk
    have e1 : missedAt plays k = 1 := by simp [missedAt, hk]
    have e2 : missingAt plays k = 1 := by simp [missingAt, hk]
    rw [e1, e2]
    exact le_self_add
  by_cases hex : ∃ j, K ≤ j ∧ (plays j).isSome
  · obtain ⟨j, hj, hpj⟩ := hex
    refine ⟨j + 1, fun k hk => ?_⟩
    cases hpk : plays k with
    | none => exact hnone k hpk
    | some y =>
      have hreal := missedAt_le_of_line hline hc0 hc2 d.coe_nonneg hd hj (by omega) hpj hpk
      have hnn : ((missedAt plays k : ℕ) : ℝ≥0) ≤ 2 * d * gapBefore plays k := by
        exact_mod_cast hreal
      have henn : ((missedAt plays k : ℕ) : ℝ≥0∞) ≤ 2 * (d : ℝ≥0∞) * gapBefore plays k := by
        exact_mod_cast hnn
      exact henn.trans le_add_self
  · refine ⟨K, fun k hk => hnone k ?_⟩
    by_contra hsome
    exact hex ⟨k, hk, Option.isSome_iff_ne_none.mpr hsome⟩

/-- **The missed samples of a speaker that plays a line or nothing.** There
is a finite constant such that, over any number of output samples, the
missed samples counted are at most the constant plus `1 + 2 d` times the
number of output samples that play nothing. -/
theorem sum_missedAt_le {plays : ℕ → Option ℝ} {a c : ℝ} {K : ℕ}
    (hline : ∀ k, K ≤ k → ∀ x, plays k = some x → x = a + c * k) (hc0 : 0 < c) (hc2 : c < 2)
    {d : ℝ≥0} (hd : c - 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ M,
      ∑ k ∈ Finset.range M, (missedAt plays k : ℝ≥0∞)
        ≤ C + ((1 + 2 * d : ℝ≥0) : ℝ≥0∞) * ∑ k ∈ Finset.range M, (missingAt plays k : ℝ≥0∞) := by
  obtain ⟨N₀, hN₀⟩ := exists_missedAt_le hline hc0 hc2 hd
  refine ⟨∑ k ∈ Finset.range N₀, (missedAt plays k : ℝ≥0∞),
    ENNReal.sum_ne_top.mpr fun k _ => ENNReal.natCast_ne_top _, fun M => ?_⟩
  have hpoint : ∀ k, (missedAt plays k : ℝ≥0∞)
      ≤ (if k < N₀ then (missedAt plays k : ℝ≥0∞) else 0)
        + (missingAt plays k + 2 * (d : ℝ≥0∞) * gapBefore plays k) := by
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
  have hgaps : ∑ k ∈ Finset.range M, (gapBefore plays k : ℝ≥0∞)
      ≤ ∑ k ∈ Finset.range M, (missingAt plays k : ℝ≥0∞) := by
    have h := sum_gapBefore_le plays M
    have h' : ∑ k ∈ Finset.range M, gapBefore plays k ≤ ∑ k ∈ Finset.range M, missingAt plays k :=
      le_trans (Nat.le_add_right _ _) h
    exact_mod_cast h'
  calc ∑ k ∈ Finset.range M, (missedAt plays k : ℝ≥0∞)
      ≤ ∑ k ∈ Finset.range M, ((if k < N₀ then (missedAt plays k : ℝ≥0∞) else 0)
          + (missingAt plays k + 2 * (d : ℝ≥0∞) * gapBefore plays k)) :=
        Finset.sum_le_sum fun k _ => hpoint k
    _ = ∑ k ∈ Finset.range M, (if k < N₀ then (missedAt plays k : ℝ≥0∞) else 0)
        + (∑ k ∈ Finset.range M, (missingAt plays k : ℝ≥0∞)
          + 2 * (d : ℝ≥0∞) * ∑ k ∈ Finset.range M, (gapBefore plays k : ℝ≥0∞)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range N₀, (missedAt plays k : ℝ≥0∞)
        + (∑ k ∈ Finset.range M, (missingAt plays k : ℝ≥0∞)
          + 2 * (d : ℝ≥0∞) * ∑ k ∈ Finset.range M, (missingAt plays k : ℝ≥0∞)) := by
        gcongr
    _ = ∑ k ∈ Finset.range N₀, (missedAt plays k : ℝ≥0∞)
        + ((1 + 2 * d : ℝ≥0) : ℝ≥0∞) * ∑ k ∈ Finset.range M, (missingAt plays k : ℝ≥0∞) := by
        push_cast
        ring

/-- **Playback of a line breaks only where the next output sample plays
nothing.** -/
theorem discontinuityAt_le_of_line {plays : ℕ → Option ℝ} {a c : ℝ} {K : ℕ}
    (hline : ∀ k, K ≤ k → ∀ x, plays k = some x → x = a + c * k) (hc0 : 0 < c) (hc2 : c < 2)
    {k : ℕ} (hk : K ≤ k) : discontinuityAt plays k ≤ missingAt plays (k + 1) := by
  classical
  unfold discontinuityAt
  split_ifs with h
  · obtain ⟨hsome, hnot⟩ := h
    cases hnext : plays (k + 1) with
    | none => simp [missingAt, hnext]
    | some y =>
      exfalso
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
      have hxl := hline k hk x hx
      have hyl := hline (k + 1) (Nat.le_succ_of_le hk) y hnext
      push_cast at hyl
      exact hnot ⟨x, y, hx, hnext, by rw [hxl, hyl]; linarith, by rw [hxl, hyl]; linarith⟩
  · exact Nat.zero_le _

/-- The discontinuities of a speaker that plays a line or nothing, over any
number of output samples, are at most `K + 1` plus the number of output
samples that play nothing. -/
theorem sum_discontinuityAt_le {plays : ℕ → Option ℝ} {a c : ℝ} {K : ℕ}
    (hline : ∀ k, K ≤ k → ∀ x, plays k = some x → x = a + c * k) (hc0 : 0 < c) (hc2 : c < 2)
    (M : ℕ) :
    ∑ k ∈ Finset.range M, discontinuityAt plays k
      ≤ K + 1 + ∑ k ∈ Finset.range M, missingAt plays k := by
  classical
  have hone : ∀ k, discontinuityAt plays k ≤ 1 := by
    intro k
    unfold discontinuityAt
    split_ifs <;> simp
  have hind : ∀ M, ∑ k ∈ Finset.range M, discontinuityAt plays k
      ≤ min M K + ∑ k ∈ Finset.range (M + 1), missingAt plays k := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => missingAt plays k) (M + 1)]
      rcases lt_or_ge M K with hlt | hge
      · have h1 := hone M
        have e1 : min M K = M := min_eq_left hlt.le
        have e2 : min (M + 1) K = M + 1 := min_eq_left hlt
        omega
      · have h1 := discontinuityAt_le_of_line hline hc0 hc2 hge
        have e1 : min M K = K := min_eq_right hge
        have e2 : min (M + 1) K = K := min_eq_right (by omega)
        omega
  have h := hind M
  rw [Finset.sum_range_succ] at h
  have hM := missingAt_le_one plays M
  have hmin : min M K ≤ K := min_le_right _ _
  omega

/-! ## The long-run averages -/

/-- **The long-run missed samples of a playback of lines with missing
output samples.** Suppose that from output sample `K` on every played
position of speaker `r` lies on the line `a r + c r * k`, with `0 < c r < 2`
and `c r - 1 ≤ d`, and that the output samples of every speaker leave
without end. Then the long-run number of missed samples is at most `1 + 2 d`
times the long-run number of output samples that play nothing. -/
theorem World.missed_le_of_line (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {a c : Fin R → ℝ} {K : ℕ} {d : ℝ≥0}
    (hline : ∀ r k, K ≤ k → ∀ x, plays r k = some x → x = a r + c r * k)
    (hc : ∀ r, 0 < c r ∧ c r < 2) (hd : ∀ r, c r - 1 ≤ d)
    (hout : ∀ r (T : Time), ∃ k, T ≤ (w.speaker r).out k) :
    w.missed plays
      ≤ ((1 + 2 * d : ℝ≥0) : ℝ≥0∞)
        * longRun (w.accruedOutputs fun r k => (missingAt (plays r) k : ℝ≥0∞)) := by
  choose C hCfin hC using fun r => sum_missedAt_le (hline r) (hc r).1 (hc r).2 (hd r)
  refine longRun_le_mul_add (C := (R : ℝ≥0∞)⁻¹ * ∑ r, C r) (average_ne_top hCfin) _ fun T => ?_
  rw [w.accruedOutputs_eq_sum _ (fun r => hout r T), w.accruedOutputs_eq_sum _ (fun r => hout r T)]
  calc (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ Finset.range (Nat.find (hout r T)),
        (missedAt (plays r) k : ℝ≥0∞)
      ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, (C r + ((1 + 2 * d : ℝ≥0) : ℝ≥0∞)
          * ∑ k ∈ Finset.range (Nat.find (hout r T)), (missingAt (plays r) k : ℝ≥0∞)) := by
        gcongr with r
        exact hC r _
    _ = (R : ℝ≥0∞)⁻¹ * ∑ r, C r + ((1 + 2 * d : ℝ≥0) : ℝ≥0∞)
        * ((R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ Finset.range (Nat.find (hout r T)),
          (missingAt (plays r) k : ℝ≥0∞)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring

/-- **The long-run discontinuities of a playback of lines with missing
output samples** are at most the long-run number of output samples that play
nothing: playback breaks only where a gap begins. -/
theorem World.discontinuities_le_of_line (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {a c : Fin R → ℝ} {K : ℕ}
    (hline : ∀ r k, K ≤ k → ∀ x, plays r k = some x → x = a r + c r * k)
    (hc : ∀ r, 0 < c r ∧ c r < 2) (hout : ∀ r (T : Time), ∃ k, T ≤ (w.speaker r).out k) :
    w.discontinuities plays
      ≤ longRun (w.accruedOutputs fun r k => (missingAt (plays r) k : ℝ≥0∞)) := by
  have hC : (R : ℝ≥0∞)⁻¹ * ∑ _r : Fin R, ((K + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    average_ne_top fun _ => ENNReal.natCast_ne_top _
  have hmain := longRun_le_mul_add hC 1
    (A := w.accruedOutputs fun r k => (discontinuityAt (plays r) k : ℝ≥0∞))
    (B := w.accruedOutputs fun r k => (missingAt (plays r) k : ℝ≥0∞)) fun T => by
    rw [w.accruedOutputs_eq_sum _ (fun r => hout r T),
      w.accruedOutputs_eq_sum _ (fun r => hout r T), ENNReal.coe_one, one_mul, ← mul_add,
      ← Finset.sum_add_distrib]
    gcongr with r
    have h := sum_discontinuityAt_le (hline r) (hc r).1 (hc r).2 (Nat.find (hout r T))
    exact_mod_cast h
  simpa [World.discontinuities] using hmain

end Unisono.Spec
