/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Checks

/-!
# Playback at a latency

What the objectives come to for a playback in which, from some output sample
on, every speaker plays continuously and each output sample plays sound
captured within `E` seconds of a fixed latency `L` before the sample leaves
(`World.PlaysAtLatency`). These are statements about the objectives alone,
for any solution: a solution's guarantees follow from showing that its run
plays at a latency.

* Such a playback misses no samples and has no discontinuities in the long
  run (`missed_eq_zero`, `discontinuities_eq_zero`).
* Its long-run latency is at most `L + E + δ` (`meanLatency_le`), its
  synchronization cost at most `(E + δ)²` (`sync_le`), and its tracking
  cost at most `(D + E + δ)²` when every target latency is within `D` of `L`
  (`tracking_le`), where `δ` bounds the time between two output samples.
* Playback at a latency says nothing about roughness: within `E` a speaker
  can change its speed as often as it likes. A bound on roughness needs a
  bound on how a solution changes its speed.
* A cost accrued at most linearly in time has a long-run average at most its
  slope (`longRun_le`), which turns bounds on each frame and each output
  sample into bounds on the objectives.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal
open Filter Topology

variable {H : Type} {R : ℕ}

/-- **A cost accrued at most linearly has a bounded long-run average.** If,
for every horizon `T` from some `T₀` on, the cost accrued is at most
`B T + C` with `C` finite, its long-run average is at most `B`. -/
theorem longRun_le {accrued : Time → ℝ≥0∞} {B C : ℝ≥0∞} (hC : C ≠ ⊤) (T₀ : ℝ)
    (h : ∀ T, T₀ ≤ T → accrued T ≤ B * ENNReal.ofReal T + C) : longRun accrued ≤ B := by
  unfold longRun
  have hbound : ∀ᶠ T : ℝ in atTop, accrued T / ENNReal.ofReal T ≤ B + C / ENNReal.ofReal T := by
    filter_upwards [eventually_ge_atTop (max T₀ 1)] with T hT
    have hT0 : T₀ ≤ T := le_trans (le_max_left _ _) hT
    have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
    have hpos : ENNReal.ofReal T ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hfin : ENNReal.ofReal T ≠ ⊤ := ENNReal.ofReal_ne_top
    calc accrued T / ENNReal.ofReal T ≤ (B * ENNReal.ofReal T + C) / ENNReal.ofReal T :=
          ENNReal.div_le_div_right (h T hT0) _
      _ = B + C / ENNReal.ofReal T := by
          rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hpos hfin]
  have hlim : Tendsto (fun T : ℝ => B + C / ENNReal.ofReal T) atTop (𝓝 B) := by
    have h0 : Tendsto (fun T : ℝ => C / ENNReal.ofReal T) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_div ENNReal.tendsto_ofReal_atTop (Or.inr hC)
    simpa using tendsto_const_nhds.add h0
  calc limsup (fun T => accrued T / ENNReal.ofReal T) atTop
      ≤ limsup (fun T : ℝ => B + C / ENNReal.ofReal T) atTop := limsup_le_limsup hbound
    _ = B := hlim.limsup_eq

/-- A constant that bounds a count accrued over finitely many output samples
is finite. -/
theorem finite_outputs_ne_top (cost : Fin R → ℕ → ℕ) (K : ℕ) :
    (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ Finset.range (K + 1), (cost r k : ℝ≥0∞) ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp
  · apply ENNReal.mul_ne_top
    · simpa using hR.ne'
    · exact ENNReal.sum_ne_top.mpr fun r _ => ENNReal.sum_ne_top.mpr fun k _ =>
        ENNReal.natCast_ne_top _

/-- A cost of output samples that is zero after output sample `K` accrues
at most its sum up to `K`. -/
theorem World.accruedOutputs_le (w : World H R) (cost : Fin R → ℕ → ℝ≥0∞) (K : ℕ)
    (h : ∀ r k, K < k → cost r k = 0) (T : Time) :
    w.accruedOutputs cost T ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ∑ k ∈ Finset.range (K + 1), cost r k := by
  unfold World.accruedOutputs
  gcongr with r
  rw [tsum_eq_sum (s := Finset.range (K + 1))]
  · exact Finset.sum_le_sum fun k _ => by split_ifs <;> simp
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [h r k (by omega)]

/-- From output sample `K` on, every speaker plays continuously, and each
output sample plays sound captured within `E` seconds of `L` seconds before
the sample leaves. -/
def World.PlaysAtLatency (w : World H R) (plays : Fin R → ℕ → Option ℝ) (L E : ℝ) (K : ℕ) :
    Prop :=
  ∀ r k, K ≤ k → PlaysContinuously (plays r) k ∧
    ∃ x, plays r k = some x ∧ |w.captured x - ((w.speaker r).out k - L)| ≤ E

/-- **A playback at a latency misses no samples in the long run.** -/
theorem missed_eq_zero (w : World H R) (plays : Fin R → ℕ → Option ℝ) {L E : ℝ} {K : ℕ}
    (h : w.PlaysAtLatency plays L E K) : w.missed plays = 0 := by
  have hz : ∀ r k, K + 1 < k → (missedAt (plays r) k : ℝ≥0∞) = 0 := by
    intro r k hk
    obtain ⟨x, y, hx, hy, hxy, hyx⟩ := (h r (k - 1) (by omega)).1
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1] at hy
    have := missedAt_continues (plays r) (k := k - 1) hx (by rw [hk1]; exact hy) hxy hyx
    rw [hk1] at this
    simp [this]
  refine le_antisymm ?_ zero_le
  refine longRun_le (finite_outputs_ne_top (fun r k => missedAt (plays r) k) (K + 1)) 0
    fun T _ => ?_
  simpa using w.accruedOutputs_le _ (K + 1) hz T

/-- **A playback at a latency has no discontinuities in the long run.** -/
theorem discontinuities_eq_zero (w : World H R) (plays : Fin R → ℕ → Option ℝ) {L E : ℝ}
    {K : ℕ} (h : w.PlaysAtLatency plays L E K) : w.discontinuities plays = 0 := by
  have hz : ∀ r k, K < k → (discontinuityAt (plays r) k : ℝ≥0∞) = 0 := by
    intro r k hk
    simp [discontinuityAt_continues (plays r) (h r k hk.le).1]
  refine le_antisymm ?_ zero_le
  refine longRun_le (finite_outputs_ne_top (fun r k => discontinuityAt (plays r) k) K) 0
    fun T _ => ?_
  simpa using w.accruedOutputs_le _ K hz T

/-- Frames are captured one after another: the time between two frames is
positive. -/
theorem World.capture_step_pos (w : World H R) (m : ℕ) :
    0 < w.source.capture (m + 1) - w.source.capture m :=
  sub_pos.mpr (w.source.capture_strictMono (Nat.lt_succ_self m))

/-- The sound at a position no later than frame `n` was captured no later
than frame `n`. -/
theorem World.captured_le_capture (w : World H R) {x : ℝ} {n : ℕ} (hx : x ≤ n) :
    w.captured x ≤ w.source.capture n := by
  unfold World.captured
  have hfrac : x - ⌊x⌋₊ < 1 := by have := Nat.lt_floor_add_one x; linarith
  rcases lt_or_ge ⌊x⌋₊ n with hlt | hge
  · have hΔ := w.capture_step_pos ⌊x⌋₊
    have h1 : (x - ⌊x⌋₊) * (w.source.capture (⌊x⌋₊ + 1) - w.source.capture ⌊x⌋₊)
        ≤ w.source.capture (⌊x⌋₊ + 1) - w.source.capture ⌊x⌋₊ := by nlinarith
    have h2 : w.source.capture (⌊x⌋₊ + 1) ≤ w.source.capture n :=
      w.source.capture_strictMono.monotone hlt
    linarith
  · rcases le_or_gt 0 x with h0 | h0
    · have hm : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le h0
      have hn : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hge
      have hxn : x = n := le_antisymm hx (by linarith)
      have hfl : ⌊x⌋₊ = n := by rw [hxn, Nat.floor_natCast]
      rw [hfl, hxn]
      simp
    · have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have hn : n = 0 := by omega
      subst hn
      have hΔ := w.capture_step_pos 0
      rw [hfl]
      simp only [Nat.cast_zero, sub_zero, zero_add]
      nlinarith

/-- Frame `n` was captured no later than the sound at a position no earlier
than frame `n`. -/
theorem World.capture_le_captured (w : World H R) {y : ℝ} {n : ℕ} (hy : (n : ℝ) ≤ y) :
    w.source.capture n ≤ w.captured y := by
  unfold World.captured
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg n) hy
  have hm : n ≤ ⌊y⌋₊ := Nat.le_floor hy
  have hΔ := w.capture_step_pos ⌊y⌋₊
  have hfrac : 0 ≤ y - ⌊y⌋₊ := sub_nonneg.mpr (Nat.floor_le hy0)
  have h1 : w.source.capture n ≤ w.source.capture ⌊y⌋₊ := w.source.capture_strictMono.monotone hm
  nlinarith

/-- **The latency of a frame at a playback at a latency.** When no output
sample before `K` reached frame `n`, a speaker that plays it does so within
`E` plus one output step of the latency `L`. -/
theorem World.latency_near (w : World H R) (plays : Fin R → ℕ → Option ℝ) {L E δ : ℝ} {K : ℕ}
    (h : w.PlaysAtLatency plays L E K)
    (hδ : ∀ r k, K ≤ k → (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ δ)
    {r : Fin R} {n : ℕ} (hn : ∀ k, k < K → ¬ Covers (plays r) k n) {ℓ : ℝ}
    (hℓ : w.latency plays r n = some ℓ) : L - E - δ ≤ ℓ ∧ ℓ ≤ L + E + δ := by
  classical
  unfold World.latency World.playTime Spec.playTime at hℓ
  split at hℓ
  · rename_i hex
    have hcov := Nat.find_spec hex
    have hkK : K ≤ Nat.find hex := by
      by_contra hlt
      exact hn _ (not_le.mp hlt) hcov
    obtain ⟨x, y, hx, hy, hxy, hyx, hxn, hny⟩ := hcov
    simp only [hx, hy, Option.map_some, Option.some.injEq] at hℓ
    obtain ⟨-, x', hx', hE⟩ := h r _ hkK
    obtain ⟨-, y', hy', hE'⟩ := h r _ (Nat.le_succ_of_le hkK)
    rw [hx, Option.some.injEq] at hx'
    rw [hy, Option.some.injEq] at hy'
    subst hx' hy'
    set o := (w.speaker r).out
    set k := Nat.find hex
    have hstep := hδ r k hkK
    have hpos : 0 < o (k + 1) - o k := sub_pos.mpr ((w.speaker r).out_strictMono (Nat.lt_succ_self k))
    have hf0 : 0 ≤ ((n : ℝ) - x) / (y - x) := div_nonneg (by linarith) (by linarith)
    have hf1 : ((n : ℝ) - x) / (y - x) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hm0 : 0 ≤ ((n : ℝ) - x) / (y - x) * (o (k + 1) - o k) := mul_nonneg hf0 hpos.le
    have hm1 : ((n : ℝ) - x) / (y - x) * (o (k + 1) - o k) ≤ o (k + 1) - o k := by
      nlinarith
    have hcx := w.captured_le_capture hxn
    have hcy := w.capture_le_captured hny
    rw [abs_le] at hE hE'
    constructor <;> linarith [hE.1, hE.2, hE'.1, hE'.2]
  · simp at hℓ

/-- There is a frame beyond every frame that the output samples before `K`
reach. -/
theorem exists_frame_beyond (plays : Fin R → ℕ → Option ℝ) (K : ℕ) :
    ∃ N : ℕ, ∀ r k n, k < K → N ≤ n → ¬ Covers (plays r) k n := by
  set S := ∑ r, ∑ j ∈ Finset.range (K + 1), |(plays r j).getD 0| with hS
  refine ⟨⌈S⌉₊ + 1, ?_⟩
  rintro r k n hk hn ⟨x, y, -, hy, -, -, -, hny⟩
  have h1 : |(plays r (k + 1)).getD 0| ≤ ∑ j ∈ Finset.range (K + 1), |(plays r j).getD 0| :=
    Finset.single_le_sum (f := fun j => |(plays r j).getD 0|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have h2 : ∑ j ∈ Finset.range (K + 1), |(plays r j).getD 0| ≤ S :=
    Finset.single_le_sum (f := fun r => ∑ j ∈ Finset.range (K + 1), |(plays r j).getD 0|)
      (fun r _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ r)
  rw [hy, Option.getD_some] at h1
  have h3 := Nat.le_ceil S
  have h4 : ((⌈S⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h4
  have h5 := le_abs_self y
  linarith

/-- The average over the speakers of costs that are each at most `b` is at
most `b`. -/
theorem average_le {a : Fin R → ℝ≥0∞} {b : ℝ≥0∞} (h : ∀ r, a r ≤ b) :
    (R : ℝ≥0∞)⁻¹ * ∑ r, a r ≤ b := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp
  · have hR0 : (R : ℝ≥0∞) ≠ 0 := by simpa using hR.ne'
    calc (R : ℝ≥0∞)⁻¹ * ∑ r, a r ≤ (R : ℝ≥0∞)⁻¹ * ∑ _r : Fin R, b := by
          gcongr with r
          exact h r
      _ = b := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel hR0 (ENNReal.natCast_ne_top R), one_mul]

/-- The average over the speakers of finite costs is finite. -/
theorem average_ne_top {a : Fin R → ℝ≥0∞} (h : ∀ r, a r ≠ ⊤) :
    (R : ℝ≥0∞)⁻¹ * ∑ r, a r ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp
  · exact ENNReal.mul_ne_top (by simpa using hR.ne') (ENNReal.sum_ne_top.mpr fun r _ => h r)

/-- A cost of frames that is at most `B` from frame `N` on accrues at most
`B` per second, plus a constant, when frames are captured at most `δc`
seconds apart. -/
theorem World.accruedFrames_le (w : World H R) (cost : ℕ → ℝ≥0∞) {B : ℝ≥0∞} {δc : ℝ} (N : ℕ)
    (hB : ∀ n, N ≤ n → cost n ≤ B)
    (hc : ∀ n, w.source.capture (n + 1) - w.source.capture n ≤ δc) (T : Time) :
    w.accruedFrames cost T ≤ B * ENNReal.ofReal T
      + ((∑ n ∈ Finset.range N,
          cost n * ENNReal.ofReal (w.source.capture (n + 1) - w.source.capture n))
        + B * ENNReal.ofReal (δc - w.source.capture N)) := by
  set c := w.source.capture with hcdef
  have hmono : Monotone c := w.source.capture_strictMono.monotone
  have hδc : 0 ≤ δc := le_trans (w.capture_step_pos 0).le (hc 0)
  have htail : ∑' n, (if N ≤ n ∧ c n < T then ENNReal.ofReal (c (n + 1) - c n) else 0)
      ≤ ENNReal.ofReal (T + δc - c N) := by
    have hinv : ∀ M, ∑ n ∈ Finset.range M,
        (if N ≤ n ∧ c n < T then ENNReal.ofReal (c (n + 1) - c n) else 0)
        ≤ ENNReal.ofReal (min (c (max M N)) (T + δc) - c N) := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
        rw [Finset.sum_range_succ]
        by_cases hcond : N ≤ M ∧ c M < T
        · rw [ite_eq_left hcond]
          have hmax : max M N = M := max_eq_left hcond.1
          have hmax' : max (M + 1) N = M + 1 := max_eq_left (by omega)
          rw [hmax] at ih
          rw [hmax']
          have hmin : min (c M) (T + δc) = c M := min_eq_left (by linarith [hcond.2])
          have hmin' : min (c (M + 1)) (T + δc) = c (M + 1) := min_eq_left (by linarith [hc M])
          rw [hmin] at ih
          rw [hmin']
          have h0 : 0 ≤ c M - c N := sub_nonneg.mpr (hmono hcond.1)
          have h1 : 0 ≤ c (M + 1) - c M := sub_nonneg.mpr (hmono (Nat.le_succ M))
          calc _ ≤ ENNReal.ofReal (c M - c N) + ENNReal.ofReal (c (M + 1) - c M) := by gcongr
            _ = ENNReal.ofReal (c (M + 1) - c N) := by
                rw [← ENNReal.ofReal_add h0 h1]
                ring_nf
        · rw [ite_eq_right hcond, add_zero]
          refine ih.trans (ENNReal.ofReal_le_ofReal ?_)
          have : c (max M N) ≤ c (max (M + 1) N) := hmono (max_le_max (Nat.le_succ M) le_rfl)
          have : min (c (max M N)) (T + δc) ≤ min (c (max (M + 1) N)) (T + δc) :=
            min_le_min this le_rfl
          linarith
    refine ENNReal.tsum_le_of_sum_range_le fun M => (hinv M).trans (ENNReal.ofReal_le_ofReal ?_)
    linarith [min_le_right (c (max M N)) (T + δc)]
  have hsplit : ∀ n, (if c n < T then cost n * ENNReal.ofReal (c (n + 1) - c n) else 0)
      ≤ (if n < N then cost n * ENNReal.ofReal (c (n + 1) - c n) else 0)
        + B * (if N ≤ n ∧ c n < T then ENNReal.ofReal (c (n + 1) - c n) else 0) := by
    intro n
    by_cases hn : n < N
    · rw [ite_eq_left hn]
      split_ifs <;> simp
    · rw [ite_eq_right hn, zero_add]
      by_cases hT : c n < T
      · rw [ite_eq_left hT, ite_eq_left ⟨not_lt.mp hn, hT⟩]
        gcongr
        exact hB n (not_lt.mp hn)
      · rw [ite_eq_right hT]
        exact zero_le
  unfold World.accruedFrames
  calc ∑' n, (if c n < T then cost n * ENNReal.ofReal (c (n + 1) - c n) else 0)
      ≤ ∑' n, ((if n < N then cost n * ENNReal.ofReal (c (n + 1) - c n) else 0)
        + B * (if N ≤ n ∧ c n < T then ENNReal.ofReal (c (n + 1) - c n) else 0)) :=
        tsum_le_tsum hsplit
    _ = (∑ n ∈ Finset.range N, cost n * ENNReal.ofReal (c (n + 1) - c n))
        + B * ∑' n, (if N ≤ n ∧ c n < T then ENNReal.ofReal (c (n + 1) - c n) else 0) := by
        rw [tsum_add, ENNReal.tsum_mul_left, tsum_eq_sum (s := Finset.range N)]
        · exact congrArg₂ _ (Finset.sum_congr rfl fun n hn => by
            rw [ite_eq_left (Finset.mem_range.mp hn)]) rfl
        · intro n hn
          rw [ite_eq_right (by simpa using hn)]
    _ ≤ (∑ n ∈ Finset.range N, cost n * ENNReal.ofReal (c (n + 1) - c n))
        + B * ENNReal.ofReal (T + δc - c N) := by gcongr
    _ ≤ (∑ n ∈ Finset.range N, cost n * ENNReal.ofReal (c (n + 1) - c n))
        + B * (ENNReal.ofReal T + ENNReal.ofReal (δc - c N)) := by
        gcongr
        rw [show T + δc - c N = T + (δc - c N) by ring]
        exact ENNReal.ofReal_add_le
    _ = B * ENNReal.ofReal T + ((∑ n ∈ Finset.range N,
          cost n * ENNReal.ofReal (c (n + 1) - c n)) + B * ENNReal.ofReal (δc - c N)) := by
        ring

/-- A cost of frames that is finite at every frame and at most `B` from some
frame on has a long-run average at most `B`. -/
theorem World.longRun_frames_le (w : World H R) (cost : ℕ → ℝ≥0∞) {B : ℝ≥0∞} {δc : ℝ} (N : ℕ)
    (hB : ∀ n, N ≤ n → cost n ≤ B) (hBfin : B ≠ ⊤) (hfin : ∀ n, cost n ≠ ⊤)
    (hc : ∀ n, w.source.capture (n + 1) - w.source.capture n ≤ δc) :
    longRun (w.accruedFrames cost) ≤ B := by
  refine longRun_le ?_ 0 fun T _ => w.accruedFrames_le cost N hB hc T
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun n _ =>
    ENNReal.mul_ne_top (hfin n) ENNReal.ofReal_ne_top, ENNReal.mul_ne_top hBfin ENNReal.ofReal_ne_top⟩

/-- **The long-run latency of a playback at a latency** is at most `L + E + δ`,
where `δ` bounds the time between two output samples from `K` on, and frames
are captured at most `δc` apart. -/
theorem meanLatency_le (w : World H R) (plays : Fin R → ℕ → Option ℝ) {L E δ δc : ℝ} {K : ℕ}
    (h : w.PlaysAtLatency plays L E K)
    (hδ : ∀ r k, K ≤ k → (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ δ)
    (hc : ∀ n, w.source.capture (n + 1) - w.source.capture n ≤ δc) :
    w.meanLatency plays ≤ ENNReal.ofReal (L + E + δ) := by
  obtain ⟨N, hN⟩ := exists_frame_beyond plays K
  refine w.longRun_frames_le _ N (fun n hn => average_le fun r => ?_) ENNReal.ofReal_ne_top
    (fun n => average_ne_top fun r => ?_) hc
  · unfold World.latencyAt
    split
    · rename_i ℓ hl
      exact ENNReal.ofReal_le_ofReal (w.latency_near plays h hδ (fun k hk => hN r k n hk hn) hl).2
    · exact zero_le
  · unfold World.latencyAt
    split <;> simp

/-- A function of two speakers that is symmetric and zero when both are the
same sums over the pairs of distinct speakers, each counted once, to half
its sum over all ordered pairs. -/
theorem two_mul_sum_pairs (f : Fin R → Fin R → ℝ) (hsymm : ∀ a b, f a b = f b a)
    (hdiag : ∀ a, f a a = 0) :
    2 * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), f p.1 p.2
      = ∑ a, ∑ b, f a b := by
  have hpairs : ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), f p.1 p.2
      = ∑ a, ∑ b, if a < b then f a b else 0 := by
    rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have hsplit : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, not_lt.mpr hab.le]
    · subst hab
      simp [hdiag]
    · simp [hab, not_lt.mpr hab.le]
  have hswap : ∑ a, ∑ b, (if b < a then f a b else 0)
      = ∑ a, ∑ b, (if a < b then f a b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm]
  calc 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), f p.1 p.2
      = (∑ a, ∑ b, if a < b then f a b else 0) + ∑ a, ∑ b, if a < b then f a b else 0 := by
        rw [hpairs]; ring
    _ = (∑ a, ∑ b, if a < b then f a b else 0) + ∑ a, ∑ b, if b < a then f a b else 0 := by
        rw [hswap]
    _ = ∑ a, ∑ b, f a b := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => (hsplit a b).symm

/-- **Popoviciu's bound for pairs.** For `R` values within `M` of zero, the
squares of their differences, summed over the pairs, are at most `R² M²`:
the sum is `R` times the sum of the squares less the square of the sum. -/
theorem sum_pairs_sq_sub_le (d : Fin R → ℝ) {M : ℝ} (hd : ∀ r, |d r| ≤ M) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2), (d p.1 - d p.2) ^ 2
      ≤ (R : ℝ) ^ 2 * M ^ 2 := by
  have h2 := two_mul_sum_pairs (fun a b => (d a - d b) ^ 2) (fun a b => by ring) (fun a => by ring)
  have hexp : ∑ a, ∑ b, (d a - d b) ^ 2 = 2 * (R : ℝ) * ∑ a, d a ^ 2 - 2 * (∑ a, d a) ^ 2 := by
    have : ∀ a b, (d a - d b) ^ 2 = d a ^ 2 + d b ^ 2 - 2 * d a * d b := fun a b => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hsq : ∀ a, d a ^ 2 ≤ M ^ 2 := fun a => sq_le_sq' (abs_le.mp (hd a)).1 (abs_le.mp (hd a)).2
  have hsum : ∑ a, d a ^ 2 ≤ R * M ^ 2 := by
    calc ∑ a, d a ^ 2 ≤ ∑ _a : Fin R, M ^ 2 := Finset.sum_le_sum fun a _ => hsq a
      _ = R * M ^ 2 := by simp
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  nlinarith [sq_nonneg (∑ a, d a)]

/-- **The long-run synchronization cost of a playback at a latency** is at
most `(E + δ)²`. The bound is attained when half of the speakers play every
frame `E + δ` early and the other half `E + δ` late. -/
theorem sync_le (w : World H R) (plays : Fin R → ℕ → Option ℝ) {L E δ δc : ℝ} {K : ℕ}
    (h : w.PlaysAtLatency plays L E K)
    (hδ : ∀ r k, K ≤ k → (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ δ)
    (hc : ∀ n, w.source.capture (n + 1) - w.source.capture n ≤ δc) :
    w.sync plays ≤ ENNReal.ofReal ((E + δ) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_frame_beyond plays K
  have hfin : ∀ n, w.syncCost plays n ≠ ⊤ := by
    intro n
    unfold World.syncCost
    rcases Nat.eq_zero_or_pos R with hR | hR
    · subst hR
      simp
    · refine ENNReal.mul_ne_top (by simpa using hR.ne') (ENNReal.sum_ne_top.mpr fun p _ => ?_)
      unfold World.pairCost
      split <;> simp
  refine w.longRun_frames_le _ N (fun n hn => ?_) ENNReal.ofReal_ne_top hfin hc
  unfold World.syncCost
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp
  -- How far each speaker plays frame `n` from its capture plus `L`; zero
  -- for a speaker that does not play it.
  set dev : Fin R → ℝ := fun r => match w.playTime plays r n with
    | some t => t - w.source.capture n - L
    | none => 0 with hdevdef
  have hM : 0 ≤ E + δ := by
    obtain ⟨-, x, -, hx⟩ := h ⟨0, hR⟩ K le_rfl
    have hE : 0 ≤ E := le_trans (abs_nonneg _) hx
    have hout := (w.speaker ⟨0, hR⟩).out_strictMono (Nat.lt_succ_self K)
    linarith [hδ ⟨0, hR⟩ K le_rfl]
  have hdev : ∀ r, |dev r| ≤ E + δ := by
    intro r
    simp only [hdevdef]
    split
    · rename_i t ht
      have hl : w.latency plays r n = some (t - w.source.capture n) := by
        simp [World.latency, ht]
      obtain ⟨a1, a2⟩ := w.latency_near plays h hδ (fun k hk => hN r k n hk hn) hl
      rw [abs_le]
      constructor <;> linarith
    · simpa using hM
  have hpair : ∀ r r', w.pairCost plays r r' n ≤ ENNReal.ofReal ((dev r - dev r') ^ 2) := by
    intro r r'
    unfold World.pairCost
    split
    · rename_i t t' ht ht'
      simp only [hdevdef, ht, ht']
      apply le_of_eq
      congr 1
      ring
    · exact zero_le
  set s := Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2)
  have hR0 : ((R : ℝ≥0∞) ^ 2) ≠ 0 := by simpa using hR.ne'
  have hRt : ((R : ℝ≥0∞) ^ 2) ≠ ⊤ := by simp
  calc ((R : ℝ≥0∞) ^ 2)⁻¹ * ∑ p ∈ s, w.pairCost plays p.1 p.2 n
      ≤ ((R : ℝ≥0∞) ^ 2)⁻¹ * ∑ p ∈ s, ENNReal.ofReal ((dev p.1 - dev p.2) ^ 2) := by
        gcongr with p
        exact hpair _ _
    _ = ((R : ℝ≥0∞) ^ 2)⁻¹ * ENNReal.ofReal (∑ p ∈ s, (dev p.1 - dev p.2) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => sq_nonneg _)]
    _ ≤ ((R : ℝ≥0∞) ^ 2)⁻¹ * ENNReal.ofReal ((R : ℝ) ^ 2 * (E + δ) ^ 2) := by
        gcongr
        exact sum_pairs_sq_sub_le dev hdev
    _ = ENNReal.ofReal ((E + δ) ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ← mul_assoc, ENNReal.inv_mul_cancel hR0 hRt, one_mul]

/-- **The long-run tracking cost of a playback at a latency** is at most
`(D + E + δ)²`, when every target latency is within `D` of `L`. -/
theorem tracking_le (w : World H R) (plays : Fin R → ℕ → Option ℝ) {L E δ δc D : ℝ} {K : ℕ}
    (h : w.PlaysAtLatency plays L E K)
    (hδ : ∀ r k, K ≤ k → (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ δ)
    (hc : ∀ n, w.source.capture (n + 1) - w.source.capture n ≤ δc)
    (hD : ∀ n, |w.target n - L| ≤ D) :
    w.tracking plays ≤ ENNReal.ofReal ((D + E + δ) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_frame_beyond plays K
  refine w.longRun_frames_le _ N (fun n hn => average_le fun r => ?_) ENNReal.ofReal_ne_top
    (fun n => average_ne_top fun r => ?_) hc
  · unfold World.trackingAt
    split
    · rename_i ℓ hl
      obtain ⟨a1, a2⟩ := w.latency_near plays h hδ (fun k hk => hN r k n hk hn) hl
      apply ENNReal.ofReal_le_ofReal
      have hDn := abs_le.mp (hD n)
      have h1 : ℓ - w.target n ≤ D + E + δ := by linarith
      have h2 : -(D + E + δ) ≤ ℓ - w.target n := by linarith
      nlinarith
    · exact zero_le
  · unfold World.trackingAt
    split <;> simp

end Unisono.Spec
