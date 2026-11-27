/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.AtLatency
public import Unisono.Spec.Limits
public import Unisono.Spec.Models.Ideal
public import Unisono.Spec.Topologies
public import Mathlib.Order.Filter.ENNReal

/-!
# Playback at exact latencies

What a playback costs when every output sample of each speaker plays the
sound captured exactly a fixed time before it leaves, each speaker with its
own latency, in a world whose capture device runs at an exact rate. The
number of speakers and of hosts is arbitrary.

* The cost of a playback is at most the weighted sum of the long-run values
  of the six objectives (`World.cost_le`), and at least the weighted long-run
  tracking (`World.weighted_tracking_le_cost`).
* `World.PlaysAtLatencies` says that from some output sample on, every
  speaker `r` plays continuously the sound captured exactly `L r` seconds
  before each output sample leaves. Every frame that speaker `r` then plays
  has latency exactly `L r` (`World.latency_eq_of_exact`).
* The long-run tracking is then at most the mean over the speakers of the
  squares of `L r` minus the target latency (`World.tracking_le_of_exact`),
  the long-run synchronization is at most the sum over the pairs of speakers
  of the squares of the differences of their latencies, divided by the
  square of the number of speakers (`World.sync_le_of_exact`), and no samples
  are missed and playback has no discontinuities in the long run
  (`World.missed_eq_zero_of_exact`, `World.discontinuities_eq_zero_of_exact`).
* The bounds on latency, tracking and synchronization also hold when output
  samples may play nothing of the source, as long as every output sample
  that plays the source does so at the exact latency of its speaker
  (`World.PlaysOnlyAtLatencies`, `World.latency_eq_of_playsOnly`,
  `World.meanLatency_le_of_playsOnly`, `World.tracking_le_of_playsOnly`,
  `World.sync_le_of_playsOnly`). Frames that a speaker does not play add
  nothing to these three objectives; they count as missed samples
  (`Unisono.Spec.MissingSamples`).
* In an ideal constant world, the sound at position `x` counts as captured
  at a time that is linear in `x` (`IdealConstantWorld.Holds.captured_eq`).
* A star solution plays the same when the timelines of the hosts are shifted
  along the links to and from the sender, while the links between the other
  hosts stay as they are (`Solution.plays_shiftStarKeepPeers`). An ideal
  constant world shifted in this way is an ideal constant world
  (`IdealConstantWorld.Holds.shiftStarKeepPeers`).
-/

@[expose] public noncomputable section

namespace Unisono.Spec

open scoped ENNReal NNReal
open Filter Topology

variable {H : Type} {R : ℕ}

/-! ## The cost and the long-run values of the objectives -/

/-- The long-run average of a weighted accrued cost is the weight times the
long-run average of the accrued cost. -/
theorem limsup_weighted (k : ℝ≥0) (A : Time → ℝ≥0∞) :
    Filter.limsup (fun T : Time => (k : ℝ≥0∞) * A T / ENNReal.ofReal T) atTop
      = k * Filter.limsup (fun T : Time => A T / ENNReal.ofReal T) atTop := by
  simp_rw [mul_div_assoc]
  exact ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top

/-- **The cost is at most the weighted sum of the objectives.** The cost of
a playback is at most the sum, over the six objectives, of the weight times
the long-run value of the objective. -/
theorem World.cost_le (w : World H R) (plays : Fin R → ℕ → Option ℝ) (c : Weights) :
    w.cost plays c ≤ c.sync * w.sync plays + c.latency * w.meanLatency plays
      + c.tracking * w.tracking plays + c.roughness * w.roughness plays
      + c.missed * w.missed plays + c.discontinuities * w.discontinuities plays := by
  unfold World.cost World.sync World.meanLatency World.tracking World.roughness World.missed
    World.discontinuities longRun
  simp_rw [ENNReal.add_div]
  refine (ennreal_limsup_add_le _ _).trans (add_le_add ?_ (limsup_weighted _ _).le)
  refine (ennreal_limsup_add_le _ _).trans (add_le_add ?_ (limsup_weighted _ _).le)
  refine (ennreal_limsup_add_le _ _).trans (add_le_add ?_ (limsup_weighted _ _).le)
  refine (ennreal_limsup_add_le _ _).trans (add_le_add ?_ (limsup_weighted _ _).le)
  exact (ennreal_limsup_add_le _ _).trans
    (add_le_add (limsup_weighted _ _).le (limsup_weighted _ _).le)

/-- **The cost is at least the weighted tracking.** -/
theorem World.weighted_tracking_le_cost (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (c : Weights) : c.tracking * w.tracking plays ≤ w.cost plays c := by
  unfold World.cost World.tracking longRun
  rw [← limsup_weighted]
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun T => ?_) ?_ ?_
  · exact ENNReal.div_le_div_right
      (le_add_right (le_add_right (le_add_right le_add_self))) _
  · exact isCoboundedUnder_le_of_le atTop (x := 0) (fun _ => zero_le)
  · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩

/-! ## Playback at exact latencies -/

/-- Playback at exact latencies: from output sample `K` on, every speaker
plays continuously, and each output sample `k` of speaker `r` plays the sound
captured exactly `L r` seconds before the sample leaves. -/
def World.PlaysAtLatencies (w : World H R) (plays : Fin R → ℕ → Option ℝ) (L : Fin R → ℝ)
    (K : ℕ) : Prop :=
  ∀ r k, K ≤ k → PlaysContinuously (plays r) k ∧
    ∃ x, plays r k = some x ∧ w.captured x = (w.speaker r).out k - L r

/-- Playback at exact latencies is fixed-latency playback around latency
zero, with an error of the sum of the sizes of the latencies. -/
theorem World.PlaysAtLatencies.playsAtLatency {w : World H R}
    {plays : Fin R → ℕ → Option ℝ} {L : Fin R → ℝ} {K : ℕ}
    (h : w.PlaysAtLatencies plays L K) : w.PlaysAtLatency plays 0 (∑ r, |L r|) K := by
  intro r k hk
  obtain ⟨hcont, x, hx, hE⟩ := h r k hk
  refine ⟨hcont, x, hx, ?_⟩
  have h1 : w.captured x - ((w.speaker r).out k - 0) = -L r := by
    rw [hE]
    ring
  rw [h1, abs_neg]
  exact Finset.single_le_sum (f := fun r => |L r|) (fun _ _ => abs_nonneg _) (Finset.mem_univ r)

/-- Playback only at exact latencies: from output sample `K` on, every output
sample of speaker `r` that plays the source plays the sound captured exactly
`L r` seconds before the sample leaves. An output sample may also play
nothing of the source. -/
def World.PlaysOnlyAtLatencies (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    (L : Fin R → ℝ) (K : ℕ) : Prop :=
  ∀ r k, K ≤ k → ∀ x, plays r k = some x → w.captured x = (w.speaker r).out k - L r

/-- Playback at exact latencies is playback only at exact latencies. -/
theorem World.PlaysAtLatencies.playsOnly {w : World H R} {plays : Fin R → ℕ → Option ℝ}
    {L : Fin R → ℝ} {K : ℕ} (h : w.PlaysAtLatencies plays L K) :
    w.PlaysOnlyAtLatencies plays L K := by
  intro r k hk x hx
  obtain ⟨-, x', hx', hE⟩ := h r k hk
  rw [hx, Option.some.injEq] at hx'
  rw [hx']
  exact hE

/-- **Playback at exact latencies misses no samples in the long run.** -/
theorem World.missed_eq_zero_of_exact (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {K : ℕ} (h : w.PlaysAtLatencies plays L K) : w.missed plays = 0 :=
  missed_eq_zero w plays h.playsAtLatency

/-- **Playback at exact latencies has no discontinuities in the long run.** -/
theorem World.discontinuities_eq_zero_of_exact (w : World H R)
    (plays : Fin R → ℕ → Option ℝ) {L : Fin R → ℝ} {K : ℕ}
    (h : w.PlaysAtLatencies plays L K) : w.discontinuities plays = 0 :=
  discontinuities_eq_zero w plays h.playsAtLatency

/-- **The latency of each frame under playback only at exact latencies.**
Suppose that the sound at position `x` counts as captured at `t₀ + x / ρ`. If
no output sample before `K` plays frame `n`, a speaker `r` that plays frame
`n` does so with latency exactly `L r`. -/
theorem World.latency_eq_of_playsOnly (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {ρ t₀ : ℝ} {K : ℕ} (h : w.PlaysOnlyAtLatencies plays L K)
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ)
    {r : Fin R} {n : ℕ} (hn : ∀ k, k < K → ¬ Covers (plays r) k n) {ℓ : ℝ}
    (hℓ : w.latency plays r n = some ℓ) : ℓ = L r := by
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
    have hE := h r _ hkK x hx
    have hE' := h r _ (Nat.le_succ_of_le hkK) y hy
    set o := (w.speaker r).out
    set k := Nat.find hex
    rw [hcap] at hE hE'
    have hcn : w.source.capture n = t₀ + (n : ℝ) / ρ := by
      rw [← w.captured_natCast n, hcap]
    have hyx0 : y - x ≠ 0 := by linarith
    have hstep : o (k + 1) - o k = (y - x) / ρ := by
      have h1 : y / ρ - x / ρ = o (k + 1) - o k := by linarith
      rw [← h1]
      ring
    have hmul : ((n : ℝ) - x) / (y - x) * ((y - x) / ρ) = ((n : ℝ) - x) / ρ := by
      field_simp
    rw [hstep, hmul, hcn] at hℓ
    have hok : o k = t₀ + x / ρ + L r := by linarith
    rw [← hℓ, hok]
    ring
  · simp at hℓ

/-- **The latency of each frame under playback at exact latencies.** Suppose
that the sound at position `x` counts as captured at `t₀ + x / ρ`. If no
output sample before `K` plays frame `n`, a speaker `r` that plays frame `n`
does so with latency exactly `L r`. -/
theorem World.latency_eq_of_exact (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {ρ t₀ : ℝ} {K : ℕ} (h : w.PlaysAtLatencies plays L K)
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ)
    {r : Fin R} {n : ℕ} (hn : ∀ k, k < K → ¬ Covers (plays r) k n) {ℓ : ℝ}
    (hℓ : w.latency plays r n = some ℓ) : ℓ = L r :=
  w.latency_eq_of_playsOnly plays h.playsOnly hcap hn hℓ

/-- Frames are captured `1 / ρ` apart when the sound at position `x` counts
as captured at `t₀ + x / ρ`. -/
theorem World.capture_step_of_linear (w : World H R) {ρ t₀ : ℝ}
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ) (n : ℕ) :
    w.source.capture (n + 1) - w.source.capture n ≤ 1 / ρ := by
  rw [← w.captured_natCast, ← w.captured_natCast, hcap, hcap]
  push_cast
  apply le_of_eq
  ring

/-- **The long-run latency under playback only at exact latencies** is at
most the mean of the speakers' latencies. Frames that a speaker does not
play add nothing to it; they count as missed samples. -/
theorem World.meanLatency_le_of_playsOnly (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {ρ t₀ : ℝ} {K : ℕ} (h : w.PlaysOnlyAtLatencies plays L K)
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ) :
    w.meanLatency plays ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (L r) := by
  obtain ⟨N, hN⟩ := exists_frame_beyond plays K
  have hBfin : (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (L r) ≠ ⊤ :=
    average_ne_top fun _ => ENNReal.ofReal_ne_top
  refine w.longRun_frames_le _ N (fun n hn => ?_) hBfin
    (fun n => average_ne_top fun r => ?_) (w.capture_step_of_linear hcap)
  · unfold World.latencyCost
    gcongr with r
    unfold World.latencyAt
    split
    · rename_i ℓ hl
      have he := w.latency_eq_of_playsOnly plays h hcap (fun k hk => hN r k n hk hn) hl
      rw [he]
    · exact zero_le
  · unfold World.latencyAt
    split <;> simp

/-- **The long-run tracking under playback only at exact latencies** is at
most the mean, over the speakers, of the square of the speaker's latency
minus the target latency. -/
theorem World.tracking_le_of_playsOnly (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {ρ t₀ target : ℝ} {K : ℕ} (h : w.PlaysOnlyAtLatencies plays L K)
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ) (htarget : ∀ n, w.target n = target) :
    w.tracking plays ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal ((L r - target) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_frame_beyond plays K
  have hBfin : (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal ((L r - target) ^ 2) ≠ ⊤ :=
    average_ne_top fun _ => ENNReal.ofReal_ne_top
  refine w.longRun_frames_le _ N (fun n hn => ?_) hBfin
    (fun n => average_ne_top fun r => ?_) (w.capture_step_of_linear hcap)
  · unfold World.trackingCost
    gcongr with r
    unfold World.trackingAt
    split
    · rename_i ℓ hl
      have he := w.latency_eq_of_playsOnly plays h hcap (fun k hk => hN r k n hk hn) hl
      rw [he, htarget]
    · exact zero_le
  · unfold World.trackingAt
    split <;> simp

/-- **The long-run tracking under playback at exact latencies** is at most
the mean, over the speakers, of the square of the speaker's latency minus the
target latency. -/
theorem World.tracking_le_of_exact (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {ρ t₀ target : ℝ} {K : ℕ} (h : w.PlaysAtLatencies plays L K)
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ) (htarget : ∀ n, w.target n = target) :
    w.tracking plays ≤ (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal ((L r - target) ^ 2) :=
  w.tracking_le_of_playsOnly plays h.playsOnly hcap htarget

/-- **The long-run synchronization under playback only at exact latencies**
is at most the sum, over the pairs of speakers, of the squares of the
differences of their latencies, divided by the square of the number of
speakers. -/
theorem World.sync_le_of_playsOnly (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {ρ t₀ : ℝ} {K : ℕ} (h : w.PlaysOnlyAtLatencies plays L K)
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ) :
    w.sync plays ≤ ((R : ℝ≥0∞) ^ 2)⁻¹
      * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
          ENNReal.ofReal ((L p.1 - L p.2) ^ 2) := by
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
  have hBfin : ((R : ℝ≥0∞) ^ 2)⁻¹
      * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
          ENNReal.ofReal ((L p.1 - L p.2) ^ 2) ≠ ⊤ := by
    rcases Nat.eq_zero_or_pos R with hR | hR
    · subst hR
      simp
    · exact ENNReal.mul_ne_top (by simpa using hR.ne')
        (ENNReal.sum_ne_top.mpr fun p _ => ENNReal.ofReal_ne_top)
  refine w.longRun_frames_le _ N (fun n hn => ?_) hBfin hfin (w.capture_step_of_linear hcap)
  unfold World.syncCost
  gcongr with p
  unfold World.pairCost
  split
  · rename_i t t' ht ht'
    have hl : w.latency plays p.1 n = some (t - w.source.capture n) := by
      simp [World.latency, ht]
    have hl' : w.latency plays p.2 n = some (t' - w.source.capture n) := by
      simp [World.latency, ht']
    have e1 := w.latency_eq_of_playsOnly plays h hcap (fun k hk => hN p.1 k n hk hn) hl
    have e2 := w.latency_eq_of_playsOnly plays h hcap (fun k hk => hN p.2 k n hk hn) hl'
    have e0 : t - t' = L p.1 - L p.2 := by linarith
    rw [e0]
  · exact zero_le

/-- **The long-run synchronization under playback at exact latencies** is at
most the sum, over the pairs of speakers, of the squares of the differences
of their latencies, divided by the square of the number of speakers. -/
theorem World.sync_le_of_exact (w : World H R) (plays : Fin R → ℕ → Option ℝ)
    {L : Fin R → ℝ} {ρ t₀ : ℝ} {K : ℕ} (h : w.PlaysAtLatencies plays L K)
    (hcap : ∀ x : ℝ, w.captured x = t₀ + x / ρ) :
    w.sync plays ≤ ((R : ℝ≥0∞) ^ 2)⁻¹
      * ∑ p ∈ Finset.univ.filter (fun p : Fin R × Fin R => p.1 < p.2),
          ENNReal.ofReal ((L p.1 - L p.2) ^ 2) :=
  w.sync_le_of_playsOnly plays h.playsOnly hcap

/-- In an ideal constant world, the sound at position `x` counts as captured
at a time that is linear in `x`. -/
theorem IdealConstantWorld.Holds.captured_eq {m : IdealConstantWorld H R} {w : World H R}
    (hw : m.Holds w) : ∃ t₀ : Time, ∀ x : ℝ, w.captured x = t₀ + x / m.rate := by
  obtain ⟨t₀, ht⟩ := hw.capture
  refine ⟨t₀, fun x => ?_⟩
  have hρ := m.rate_pos.ne'
  unfold World.captured
  rw [ht, ht]
  push_cast
  field_simp
  ring

/-! ## Shifting the links to and from the sender -/

section Star

variable [DecidableEq H] {Msg : Type}

/-- **A star solution plays the same when the star links are shifted.**
Shift the timeline of every host by `Δ` along the links to and from the
sender, and keep the links between the other hosts as they are. A star
solution that makes progress in both worlds plays the same in both worlds. -/
theorem Solution.plays_shiftStarKeepPeers (σ : Solution H R Msg) (w : World H R)
    (lookahead : ℕ+) (hstar : σ.IsStar w.sender) (Δ : H → ℝ) (hΔs : Δ w.sender = 0)
    (hstar₁ : ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + Δ i < w.network.reach i j s q + Δ j)
    (hprog : ∀ T : Time, ∃ n, T < σ.eventTime w lookahead n)
    (hprog₁ : ∀ T : Time, ∃ n, T < σ.eventTime (shiftStarKeepPeers w Δ hstar₁) lookahead n) :
    σ.plays (shiftStarKeepPeers w Δ hstar₁) lookahead = σ.plays w lookahead := by
  set wPlus := shiftStarKeepPeers w Δ hstar₁
  set wAux := dropPeerLinks w
  have hnet₁ : ∀ i j s q a, wAux.network.deliver i j s q = some a →
    s + Δ i < wAux.network.reach i j s q + Δ j := by
    intro i j s q a h
    dsimp only [wAux, dropPeerLinks] at h
    split_ifs at h with hs
    · exact hstar₁ i j s q a hs h
  have heqW := star_states_eq_of_star_links_eq σ w wAux lookahead hstar
    rfl rfl rfl rfl rfl rfl (fun i j t q hs => by simp [wAux, dropPeerLinks, hs])
  have heqPlus := star_states_eq_of_star_links_eq σ (wAux.shiftHosts Δ hnet₁) wPlus lookahead
    hstar rfl rfl rfl rfl rfl rfl (fun i j t q hs => by
      change i = w.sender ∨ j = w.sender at hs
      simp [wPlus, shiftStarKeepPeers, wAux, dropPeerLinks, World.shiftHosts, hs])
  have hevEq : ∀ (w₁ w₂ : World H R),
      w₂.source = w₁.source → w₂.speaker = w₁.speaker → w₂.hostIndex = w₁.hostIndex →
      (∀ n, σ.states w₂ lookahead n = σ.states w₁ lookahead n) →
      ∀ n, σ.eventTime w₂ lookahead n = σ.eventTime w₁ lookahead n := by
    intro w₁ w₂ hsrc hspk hidx hst n
    unfold Solution.eventTime
    have hkey : (σ.states w₂ lookahead n).key w₂ = (σ.states w₁ lookahead n).key w₁ := by
      funext d
      rw [hst n]
      cases d <;> simp [State.key, hsrc, hspk, hidx]
    rw [hkey, hst n]
  have hprogAux : ∀ T, ∃ n, T < σ.eventTime wAux lookahead n := fun T => by
    obtain ⟨n, hn⟩ := hprog T
    exact ⟨n, by rw [hevEq w wAux rfl rfl rfl heqW.1 n]; exact hn⟩
  have hprogAux₁ : ∀ T, ∃ n, T < σ.eventTime (wAux.shiftHosts Δ hnet₁) lookahead n := fun T => by
    obtain ⟨n, hn⟩ := hprog₁ T
    exact ⟨n, by rw [← hevEq (wAux.shiftHosts Δ hnet₁) wPlus rfl rfl rfl heqPlus.1 n]; exact hn⟩
  have hshift := σ.plays_shiftHosts wAux lookahead Δ hΔs hnet₁ hprogAux hprogAux₁
  rw [heqPlus.2, hshift, heqW.2]

namespace IdealConstantWorld

/-- The parameters of an ideal constant world after a shift `x` of the hosts'
timelines along the links to and from the sender: such a link from host `i`
to host `j` takes `x j - x i` longer, and the other links are unchanged. -/
def starShifted (m : IdealConstantWorld H R) (x : H → ℝ)
    (hx : ∀ i j, (i = m.sender ∨ j = m.sender) → x i - x j < m.delay i j) :
    IdealConstantWorld H R :=
  { m with
    delay := fun i j =>
      if i = m.sender ∨ j = m.sender then m.delay i j + x j - x i else m.delay i j
    delay_pos := fun i j => by
      split_ifs with h
      · linarith [hx i j h]
      · exact m.delay_pos i j }

omit [DecidableEq H] in
/-- In an ideal constant world, a shift that keeps the delays to and from
the sender positive satisfies the condition of `shiftStarKeepPeers`. -/
theorem Holds.starNet {m : IdealConstantWorld H R} {w : World H R} (hw : m.Holds w)
    {x : H → ℝ} (hx : ∀ i j, (i = m.sender ∨ j = m.sender) → x i - x j < m.delay i j) :
    ∀ i j s q a, (i = w.sender ∨ j = w.sender) →
      w.network.deliver i j s q = some a → s + x i < w.network.reach i j s q + x j := by
  intro i j s q a hs _
  rw [hw.reach i j s q]
  rw [hw.sender_eq] at hs
  linarith [hx i j hs]

/-- **An ideal constant world with shifted star links is an ideal constant
world**, with the shifted delays, when the sender's timeline stays in
place. -/
theorem Holds.shiftStarKeepPeers {m : IdealConstantWorld H R} {w : World H R}
    (hw : m.Holds w) {x : H → ℝ} (hxs : x m.sender = 0)
    (hx : ∀ i j, (i = m.sender ∨ j = m.sender) → x i - x j < m.delay i j) :
    (m.starShifted x hx).Holds (Unisono.Spec.shiftStarKeepPeers w x (hw.starNet hx)) where
  rate_eq := hw.rate_eq
  sender_eq := hw.sender_eq
  host_eq := hw.host_eq
  clocks := fun h => by
    obtain ⟨c₀, hc⟩ := hw.clocks h
    refine ⟨c₀ - x h, fun t => ?_⟩
    change (w.clock h).read (t - x h) = t + (c₀ - x h)
    rw [hc]
    ring
  capture := hw.capture
  capture_first := hw.capture_first
  capture_handed := hw.capture_handed
  capture_reported := fun b => by
    have h := hw.capture_reported b
    have hs : x w.sender = 0 := by rw [hw.sender_eq]; exact hxs
    change |w.source.reported b
      - (w.clock w.sender).read (w.source.capture (w.source.first b) - x w.sender)| ≤ 0
    rw [hs, sub_zero]
    exact h
  speaker_out := fun r => by
    obtain ⟨t₀, ht⟩ := hw.speaker_out r
    refine ⟨t₀ + x (w.host r), fun k => ?_⟩
    change (w.speaker r).out k + x (w.host r) = t₀ + x (w.host r) + (k : ℝ) / m.rate
    rw [ht]
    ring
  speaker_first := hw.speaker_first
  speaker_asked := fun r b => by
    have h := hw.speaker_asked r b
    change (w.speaker r).out ((w.speaker r).first b) + x (w.host r)
      - ((w.speaker r).asked b + x (w.host r)) = m.lead
    linarith
  speaker_reported := fun r b => by
    have h := hw.speaker_reported r b
    change |(w.speaker r).reported b
      - (w.clock (w.host r)).read
          ((w.speaker r).out ((w.speaker r).first b) + x (w.host r) - x (w.host r))| ≤ 0
    rw [add_sub_cancel_right]
    exact h
  network := fun i j s q => by
    change (if i = w.sender ∨ j = w.sender then
        (w.network.deliver i j (s - x i) q).map (· + x j)
      else w.network.deliver i j s q)
      = some (s + (if i = m.sender ∨ j = m.sender then m.delay i j + x j - x i
        else m.delay i j))
    rw [hw.sender_eq]
    split_ifs with hs
    · rw [hw.network]
      simp only [Option.map_some, Option.some.injEq]
      ring
    · exact hw.network i j s q
  reach := fun i j s q => by
    change (if i = w.sender ∨ j = w.sender then w.network.reach i j (s - x i) q + x j
      else w.network.reach i j s q)
      = s + (if i = m.sender ∨ j = m.sender then m.delay i j + x j - x i
        else m.delay i j)
    rw [hw.sender_eq]
    split_ifs with hs
    · rw [hw.reach]
      ring
    · exact hw.reach i j s q
  target_eq := hw.target_eq

end IdealConstantWorld

end Star

end Unisono.Spec
