/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.LateRate

/-!
# The expected cost of a held level

The controller (`Unisono.Solutions.Controller`) holds the level at `L`, uses
the least-round-trip estimator for the sender's clock and the two-report
estimator for the devices. This file bounds its cost in almost every outcome
of a random world of a member with steady clocks, by a function of what is
drawn (`heldLevelCost`), and so bounds its expected cost by the mean of that
function.

`heldLevelCost` is the sum of two parts.

* The costs of the speakers' latencies (`latencyCosts`). The latency of
  speaker `r` is the level divided by the rate of the sender's clock, plus
  the asymmetry of the speaker's host (`latencyOf`). The part is the weight
  of synchronization times the mean square difference of the latencies, plus
  the weight of latency times their mean, plus the weight of tracking times
  the mean square of the latency minus the target latency.
* The weight of missed samples times `1 + 2 δ`, plus the weight of
  discontinuities, times a rate. Here `δ` is by how much the capture device's
  clock runs faster than the clock of the slowest playback device, as a
  fraction (`rateExcess`). In an outcome in which the capture device's clock
  runs less than twice as fast as the clock of every playback device, the
  rate is the bound on the late rate (`lateRateBound`): the mean over the
  speakers of the probability that a message from the sender to the
  speaker's host takes more than the least margin of the speaker, times the
  sum of the speaker's output samples per second and the capture blocks per
  second. In the other outcomes the rate is the number of output samples per
  second, averaged over the speakers (`outputRate`). Those outcomes have
  positive probability when the rates of the clocks are spread.

**Theorem** (`ae_cost_le_heldLevelCost`). In every random world of a member
with steady clocks in which no speaker is on the sender's host, the cost of
the controller is at most `heldLevelCost` of the draw, in almost every
outcome.

**Theorem** (`expectedCost_le_heldLevelCost`). So its expected cost is at
most the mean of `heldLevelCost`.

**Theorem** (`lintegral_heldLevelCost_lt_top`). The mean of `heldLevelCost`
is finite in every random world of every member: `heldLevelCost` is at most
a constant times one plus a sum of exponentials of three times, or minus
three times, the logarithms of the rates of the clocks
(`exists_heldLevelCost_le`), and those logarithms are Gaussian. So the
expected cost of the controller at a held level is finite
(`expectedCost_heldLevel_lt_top`). The bound by exponentials holds with the
larger of the two rates in every outcome (`exists_latencyCosts_add_le`), and
every function of the draw under it has a finite mean
(`lintegral_lt_top_of_le_exp`). The controller with a limiter
(`Unisono.Solutions.Controller.Limited`) is bounded through these two.

The theorems are upper bounds for one solution. They do not say that another
solution cannot have a lower cost, and the level `L` is given, not chosen by
the controller.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld MeasureTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  (p : FixedDelay.Params H)

/-- The costs of the speakers' latencies at the level `L`, for the draw `d`
and the weights `c`: the weight of synchronization times the mean square
difference of the latencies, plus the weight of latency times their mean,
plus the weight of tracking times the mean square of the latency minus the
target latency. -/
def latencyCosts (m : GenerativeWorld H R) (f : Member H R) (L : ℝ) (c : Weights)
    (d : Draw H R) : ℝ≥0∞ :=
  (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
      * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
        ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
    + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
    + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
      * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))

/-- By how much the capture device's clock runs faster than the clock of the
slowest playback device, as a fraction of the rate of the latter. Zero if no
playback device's clock runs slower than the capture device's. -/
def rateExcess (m : GenerativeWorld H R) (d : Draw H R) : ℝ≥0 :=
  Finset.univ.sup fun r : Fin R =>
    Real.toNNReal (Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1)

omit [DecidableEq H] in
theorem sub_one_le_rateExcess (m : GenerativeWorld H R) (d : Draw H R) (r : Fin R) :
    Real.exp (d.deviceLogRate none) / Real.exp (d.deviceLogRate (some (m.device r))) - 1
      ≤ rateExcess m d := by
  refine (Real.le_coe_toNNReal _).trans ?_
  have h := Finset.le_sup (f := fun r : Fin R =>
    Real.toNNReal (Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1)) (Finset.mem_univ r)
  exact_mod_cast h

/-- The bound on the late rate at the level `L`, for the draw `d`: the mean
over the speakers of the probability that a message from the sender to the
speaker's host takes more than the least margin of the speaker, times the
sum of the output samples per second of the speaker's playback device and
the capture blocks per second, both in true time. -/
def lateRateBound [Fintype H] (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+)
    (L : ℝ) (d : Draw H R) : ℝ≥0∞ :=
  (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
    ((m.rate * Real.exp (d.deviceLogRate (some (m.device r)))
        + m.rate * Real.exp (d.deviceLogRate none) / m.blockSize)
      * lateProbability f m.sender (m.host r)
          (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
          (marginLeast m f d lookahead L r))

/-- The number of output samples per second in true time, averaged over the
speakers, for the draw `d`. -/
def outputRate (m : GenerativeWorld H R) (d : Draw H R) : ℝ≥0∞ :=
  (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
    (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))

open Classical in
/-- The bound on the cost of the controller that holds the level `L`, for
the draw `d` and the weights `c`. It is the costs of the speakers' latencies
plus a multiple of a rate. The rate is the bound on the late rate when the
capture device's clock runs less than twice as fast as the clock of every
playback device, and the number of output samples per second otherwise. -/
def heldLevelCost [Fintype H] (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+)
    (L : ℝ) (c : Weights) (d : Draw H R) : ℝ≥0∞ :=
  latencyCosts m f L c d
    + ((c.missed : ℝ≥0∞) * ((1 + 2 * rateExcess m d : ℝ≥0) : ℝ≥0∞)
        + (c.discontinuities : ℝ≥0∞))
      * if ∀ r, Real.exp (d.deviceLogRate none)
          / Real.exp (d.deviceLogRate (some (m.device r))) < 2
        then lateRateBound m f lookahead L d else outputRate m d

/-- **The cost of a held level in a member with steady clocks.** In every
random world of a member with steady clocks in which no speaker is on the
sender's host, the cost of the controller that holds the level `L` is at
most `heldLevelCost` of the draw, in almost every outcome. -/
theorem ae_cost_le_heldLevelCost [Fintype H] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D) (hf : f.SteadyClocks)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hnos : ∀ r, m.host r ≠ m.sender)
    (hpsp : ∀ r, m.host r ∈ p.speakers) (c : Weights) :
    ∀ᵐ ω ∂P,
      (solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).cost
          (world ω) lookahead c
        ≤ heldLevelCost m f lookahead L c (D ω) := by
  filter_upwards [hD.ae_constantRates hf hB,
    ae_twoUndelayed p hD hf hB lookahead leastRoundTrip twoReports (constantLevel L) hps
      hcopies hperiod, ae_lateRate_le hD hf hB lookahead L hnos] with ω hS hund hlate
  have hδ := fun r => sub_one_le_rateExcess m (D ω) r
  unfold heldLevelCost
  split_ifs with hratio
  · refine (cost_le_under_pauses p hS lookahead L hps hnodup hcopies hnos hpsp
      (fun r => hund r (hnos r)) hratio hδ c).trans ?_
    exact add_le_add le_rfl (mul_le_mul' le_rfl hlate)
  · exact cost_le_outputs_under_pauses p hS lookahead L hps hnodup hcopies hnos hpsp
      (fun r => hund r (hnos r)) hδ c

/-- **The expected cost of a held level in a member with steady clocks.** In
every random world of a member with steady clocks in which no speaker is on
the sender's host, the expected cost of the controller that holds the level
`L` is at most the mean of `heldLevelCost` of the draw. -/
theorem expectedCost_le_heldLevelCost [Fintype H] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D)
    (hf : f.SteadyClocks) (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hnos : ∀ r, m.host r ≠ m.sender)
    (hpsp : ∀ r, m.host r ∈ p.speakers) (c : Weights) :
    (solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).expectedCost
        P world lookahead c
      ≤ ∫⁻ ω, heldLevelCost m f lookahead L c (D ω) ∂P :=
  lintegral_mono_ae (ae_cost_le_heldLevelCost p hD hf hB lookahead L hps hnodup hcopies hperiod
    hnos hpsp c)

/-! ## The mean of the bound is finite -/

/-- The mean of numbers that are each at most `B` is at most `B`. -/
theorem average_le {a : Fin R → ℝ≥0∞} {B : ℝ≥0∞} (h : ∀ r, a r ≤ B) :
    (R : ℝ≥0∞)⁻¹ * ∑ r, a r ≤ B := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp
  · have hR0 : (R : ℝ≥0∞) ≠ 0 := by simpa using hR.ne'
    calc (R : ℝ≥0∞)⁻¹ * ∑ r, a r ≤ (R : ℝ≥0∞)⁻¹ * ∑ _r : Fin R, B :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun r _ => h r)
      _ = (R : ℝ≥0∞)⁻¹ * (R * B) := by simp
      _ = B := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hR0 (ENNReal.natCast_ne_top R), one_mul]

/-- The sum over the pairs of speakers of numbers that are each at most `B`,
divided by the square of the number of speakers, is at most `B`. -/
theorem pairAverage_le {t : Fin R × Fin R → ℝ≥0∞} {B : ℝ≥0∞} (h : ∀ q, t q ≤ B) :
    ((R : ℝ≥0∞) ^ 2)⁻¹ * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2), t q
      ≤ B := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR
    simp
  · have hR0 : ((R : ℝ≥0∞) ^ 2) ≠ 0 := by simpa using hR.ne'
    have hRtop : ((R : ℝ≥0∞) ^ 2) ≠ ⊤ := by simp
    calc ((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2), t q
        ≤ ((R : ℝ≥0∞) ^ 2)⁻¹ * ∑ _q : Fin R × Fin R, B :=
          mul_le_mul' le_rfl ((Finset.sum_le_sum fun q _ => h q).trans
            (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)))
      _ = ((R : ℝ≥0∞) ^ 2)⁻¹ * ((R : ℝ≥0∞) ^ 2 * B) := by simp [pow_two]
      _ = B := by rw [← mul_assoc, ENNReal.inv_mul_cancel hR0 hRtop, one_mul]

/-- A nonnegative number whose cube is at most `G` is at most the cube root
of `G`. -/
theorem le_rpow_third {v G : ℝ} (hv : 0 ≤ v) (h : v ^ 3 ≤ G) :
    v ≤ G ^ (((3 : ℕ) : ℝ)⁻¹) := by
  calc v = (v ^ 3) ^ (((3 : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hv (by norm_num)).symm
    _ ≤ G ^ (((3 : ℕ) : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)

omit [DecidableEq H] in
/-- The probability that a message is late lies between zero and one. -/
theorem lateProbability_mem [Fintype H] (f : Member H R) (i j : H) (δ μ : ℝ) :
    0 ≤ lateProbability f i j δ μ ∧ lateProbability f i j δ μ ≤ 1 := by
  unfold lateProbability
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

omit [DecidableEq H] in
/-- **The costs of the latencies and of either rate, by exponentials of the
drawn rates.** There is a constant `K`, which depends on the member, the
level and the weights, such that for every draw whose splits lie between
zero and one, the following is at most `K` times one plus a sum of
exponentials: the costs of the speakers' latencies, plus the weight of
missed samples times `1 + 2 δ`, plus the weight of discontinuities, times
the larger of the bound on the late rate and the number of output samples
per second. Here `δ` is `rateExcess`. The exponentials are of three times
the logarithm of the rate of the capture device's clock and of each playback
device's clock, and of minus three times the logarithm of the rate of the
sender's clock and of each playback device's clock. -/
theorem exists_latencyCosts_add_le [Fintype H] (m : GenerativeWorld H R) (f : Member H R)
    (lookahead : ℕ+) (L : ℝ) (c : Weights) :
    ∃ K : ℝ, ∀ d : Draw H R, (∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1) →
      latencyCosts m f L c d
          + ((c.missed : ℝ≥0∞) * ((1 + 2 * rateExcess m d : ℝ≥0) : ℝ≥0∞)
              + (c.discontinuities : ℝ≥0∞))
            * max (lateRateBound m f lookahead L d) (outputRate m d)
        ≤ ENNReal.ofReal (K * (1 + Real.exp (-3 * d.logRate m.sender)
            + Real.exp (3 * d.deviceLogRate none)
            + ∑ r : Fin R, (Real.exp (3 * d.deviceLogRate (some (m.device r)))
              + Real.exp (-3 * d.deviceLogRate (some (m.device r)))))) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ r : Fin R,
      (f.roundTrip m.sender (m.host r) + f.roundTrip (m.host r) m.sender) / 2 := ⟨_, rfl⟩
  have hterm0 : ∀ r : Fin R,
      0 ≤ (f.roundTrip m.sender (m.host r) + f.roundTrip (m.host r) m.sender) / 2 := by
    intro r
    have h1 := (f.roundTrip_pos m.sender (m.host r)).le
    have h2 := (f.roundTrip_pos (m.host r) m.sender).le
    linarith
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun r _ => hterm0 r
  have hρ := m.rate_pos
  have hB : (0 : ℝ) < m.blockSize := by exact_mod_cast m.blockSize_pos
  have hκ0 : 0 ≤ m.rate * (1 + 1 / (m.blockSize : ℝ)) := by positivity
  refine ⟨(c.sync : ℝ) * (2 * A) ^ 2 + c.latency * (|L| + A)
      + c.tracking * (|L| + A + |m.targetLatency|) ^ 2
      + (3 * c.missed + c.discontinuities) * (m.rate * (1 + 1 / (m.blockSize : ℝ))),
    fun d hsplit => ?_⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = 1 + Real.exp (-3 * d.logRate m.sender)
      + Real.exp (3 * d.deviceLogRate none)
      + ∑ r : Fin R, (Real.exp (3 * d.deviceLogRate (some (m.device r)))
        + Real.exp (-3 * d.deviceLogRate (some (m.device r)))) := ⟨_, rfl⟩
  rw [← hG]
  have hsum0 : ∀ r : Fin R, 0 ≤ Real.exp (3 * d.deviceLogRate (some (m.device r)))
      + Real.exp (-3 * d.deviceLogRate (some (m.device r))) :=
    fun r => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hsingle : ∀ r : Fin R, Real.exp (3 * d.deviceLogRate (some (m.device r)))
      + Real.exp (-3 * d.deviceLogRate (some (m.device r)))
      ≤ ∑ r : Fin R, (Real.exp (3 * d.deviceLogRate (some (m.device r)))
        + Real.exp (-3 * d.deviceLogRate (some (m.device r)))) :=
    fun r => Finset.single_le_sum
      (f := fun r : Fin R => Real.exp (3 * d.deviceLogRate (some (m.device r)))
        + Real.exp (-3 * d.deviceLogRate (some (m.device r))))
      (fun r _ => hsum0 r) (Finset.mem_univ r)
  have hsumnn : 0 ≤ ∑ r : Fin R, (Real.exp (3 * d.deviceLogRate (some (m.device r)))
      + Real.exp (-3 * d.deviceLogRate (some (m.device r)))) :=
    Finset.sum_nonneg fun r _ => hsum0 r
  have he1 := (Real.exp_pos (-3 * d.logRate m.sender)).le
  have he2 := (Real.exp_pos (3 * d.deviceLogRate none)).le
  have hG1 : 1 ≤ G := by
    rw [hG]
    linarith
  have hG0 : 0 ≤ G := by linarith
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = G ^ (((3 : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
  have hΓ1 : 1 ≤ Γ := by
    rw [hΓ]
    exact Real.one_le_rpow hG1 (by positivity)
  have hΓ0 : 0 ≤ Γ := by linarith
  have hΓ3 : Γ ^ 3 = G := by
    rw [hΓ]
    exact Real.rpow_inv_natCast_pow hG0 (by norm_num)
  have hΓ2 : Γ ^ 2 ≤ G := by
    rw [← hΓ3]
    exact pow_le_pow_right₀ hΓ1 (by norm_num)
  have hΓG : Γ ≤ G := by
    rw [← hΓ3]
    exact le_self_pow₀ hΓ1 (by norm_num)
  -- Each exponential is at most the cube root.
  have hxS : Real.exp (-d.logRate m.sender) ≤ Γ := by
    rw [hΓ]
    refine le_rpow_third (Real.exp_pos _).le ?_
    have e : ((3 : ℕ) : ℝ) * -d.logRate m.sender = -3 * d.logRate m.sender := by
      push_cast
      ring
    rw [← Real.exp_nat_mul, e, hG]
    linarith
  have hyc : Real.exp (d.deviceLogRate none) ≤ Γ := by
    rw [hΓ]
    refine le_rpow_third (Real.exp_pos _).le ?_
    have e : ((3 : ℕ) : ℝ) * d.deviceLogRate none = 3 * d.deviceLogRate none := by
      push_cast
      ring
    rw [← Real.exp_nat_mul, e, hG]
    linarith
  have hyr : ∀ r : Fin R, Real.exp (d.deviceLogRate (some (m.device r))) ≤ Γ := by
    intro r
    rw [hΓ]
    refine le_rpow_third (Real.exp_pos _).le ?_
    have e : ((3 : ℕ) : ℝ) * d.deviceLogRate (some (m.device r))
        = 3 * d.deviceLogRate (some (m.device r)) := by
      push_cast
      ring
    rw [← Real.exp_nat_mul, e, hG]
    have h1 := hsingle r
    have h2 := (Real.exp_pos (-3 * d.deviceLogRate (some (m.device r)))).le
    linarith
  have hynr : ∀ r : Fin R, Real.exp (-d.deviceLogRate (some (m.device r))) ≤ Γ := by
    intro r
    rw [hΓ]
    refine le_rpow_third (Real.exp_pos _).le ?_
    have e : ((3 : ℕ) : ℝ) * -d.deviceLogRate (some (m.device r))
        = -3 * d.deviceLogRate (some (m.device r)) := by
      push_cast
      ring
    rw [← Real.exp_nat_mul, e, hG]
    have h1 := hsingle r
    have h2 := (Real.exp_pos (3 * d.deviceLogRate (some (m.device r)))).le
    linarith
  -- The latencies.
  have hasym : ∀ r : Fin R,
      |latencyOf m f d L r - L * Real.exp (-d.logRate m.sender)| ≤ A := by
    intro r
    have e : latencyOf m f d L r - L * Real.exp (-d.logRate m.sender)
        = (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2 := by
      unfold latencyOf
      rw [Real.exp_neg, div_eq_mul_inv L]
      ring
    rw [e]
    have h1 := hsplit m.sender (m.host r)
    have h2 := hsplit (m.host r) m.sender
    have h3 := f.roundTrip_pos m.sender (m.host r)
    have h4 := f.roundTrip_pos (m.host r) m.sender
    have h5 := mul_le_mul_of_nonneg_right h1.2.le h3.le
    have h6 := mul_nonneg h1.1.le h3.le
    have h7 := mul_le_mul_of_nonneg_right h2.2.le h4.le
    have h8 := mul_nonneg h2.1.le h4.le
    have hle : (f.roundTrip m.sender (m.host r) + f.roundTrip (m.host r) m.sender) / 2 ≤ A := by
      rw [hA]
      exact Finset.single_le_sum
        (f := fun r : Fin R =>
          (f.roundTrip m.sender (m.host r) + f.roundTrip (m.host r) m.sender) / 2)
        (fun r _ => hterm0 r) (Finset.mem_univ r)
    rw [abs_le]
    constructor <;> linarith
  have hLu : |L * Real.exp (-d.logRate m.sender)| ≤ |L| * Γ := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left hxS (abs_nonneg L)
  have hlatabs : ∀ r : Fin R, |latencyOf m f d L r| ≤ |L| * Γ + A := by
    intro r
    have h1 := abs_le.mp hLu
    have h2 := abs_le.mp (hasym r)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hdiff : ∀ q : Fin R × Fin R,
      (latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2 ≤ (2 * A) ^ 2 := by
    intro q
    have h1 := abs_le.mp (hasym q.1)
    have h2 := abs_le.mp (hasym q.2)
    refine sq_le_sq' ?_ ?_ <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- Synchronization.
  have hp1 : (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
        * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
          ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
      ≤ ENNReal.ofReal (c.sync * ((2 * A) ^ 2 * G)) := by
    have h1 : ((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2)
        ≤ ENNReal.ofReal ((2 * A) ^ 2 * G) :=
      pairAverage_le fun q => ENNReal.ofReal_le_ofReal
        ((hdiff q).trans (le_mul_of_one_le_right (sq_nonneg _) hG1))
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact mul_le_mul' le_rfl h1
  -- Latency.
  have hp2 : (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
      ≤ ENNReal.ofReal (c.latency * ((|L| + A) * G)) := by
    have h1 : (R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r)
        ≤ ENNReal.ofReal ((|L| + A) * G) :=
      average_le fun r => ENNReal.ofReal_le_ofReal (by
        have h2 := (le_abs_self _).trans (hlatabs r)
        have h3 : |L| * Γ ≤ |L| * G := mul_le_mul_of_nonneg_left hΓG (abs_nonneg L)
        have h4 : A * 1 ≤ A * G := mul_le_mul_of_nonneg_left hG1 hA0
        have e : (|L| + A) * G = |L| * G + A * G := by ring
        rw [e]
        linarith)
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact mul_le_mul' le_rfl h1
  -- Tracking.
  have hp3 : (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
        * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
      ≤ ENNReal.ofReal (c.tracking * ((|L| + A + |m.targetLatency|) ^ 2 * G)) := by
    have h1 : (R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2)
        ≤ ENNReal.ofReal ((|L| + A + |m.targetLatency|) ^ 2 * G) :=
      average_le fun r => ENNReal.ofReal_le_ofReal (by
        have h2 := abs_le.mp (hlatabs r)
        have h3 := neg_abs_le m.targetLatency
        have h4 := le_abs_self m.targetLatency
        have h5 : A * 1 ≤ A * Γ := mul_le_mul_of_nonneg_left hΓ1 hA0
        have h6 : |m.targetLatency| * 1 ≤ |m.targetLatency| * Γ :=
          mul_le_mul_of_nonneg_left hΓ1 (abs_nonneg _)
        have e : (|L| + A + |m.targetLatency|) * Γ
            = |L| * Γ + A * Γ + |m.targetLatency| * Γ := by ring
        have h7 : (latencyOf m f d L r - m.targetLatency) ^ 2
            ≤ ((|L| + A + |m.targetLatency|) * Γ) ^ 2 := by
          refine sq_le_sq' ?_ ?_ <;> rw [e] <;> linarith [h2.1, h2.2]
        calc (latencyOf m f d L r - m.targetLatency) ^ 2
            ≤ ((|L| + A + |m.targetLatency|) * Γ) ^ 2 := h7
          _ = (|L| + A + |m.targetLatency|) ^ 2 * Γ ^ 2 := by ring
          _ ≤ (|L| + A + |m.targetLatency|) ^ 2 * G :=
              mul_le_mul_of_nonneg_left hΓ2 (sq_nonneg _))
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact mul_le_mul' le_rfl h1
  -- Missed samples and discontinuities.
  have hδ : ((rateExcess m d : ℝ≥0) : ℝ) ≤ Γ ^ 2 := by
    have h1 : rateExcess m d ≤ Real.toNNReal (Γ ^ 2) := by
      refine Finset.sup_le fun r _ => Real.toNNReal_le_toNNReal ?_
      have h2 : Real.exp (d.deviceLogRate none) / Real.exp (d.deviceLogRate (some (m.device r)))
          = Real.exp (d.deviceLogRate none)
            * Real.exp (-d.deviceLogRate (some (m.device r))) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      have h3 := mul_le_mul hyc (hynr r) (Real.exp_pos _).le hΓ0
      rw [h2, pow_two]
      linarith
    have h4 : ((rateExcess m d : ℝ≥0) : ℝ) ≤ ((Real.toNNReal (Γ ^ 2) : ℝ≥0) : ℝ) := by
      exact_mod_cast h1
    rwa [Real.coe_toNNReal _ (sq_nonneg Γ)] at h4
  have hW : (c.missed : ℝ≥0∞) * ((1 + 2 * rateExcess m d : ℝ≥0) : ℝ≥0∞)
        + (c.discontinuities : ℝ≥0∞)
      ≤ ENNReal.ofReal (c.missed * (1 + 2 * Γ ^ 2) + c.discontinuities) := by
    have e : (c.missed : ℝ≥0∞) * ((1 + 2 * rateExcess m d : ℝ≥0) : ℝ≥0∞)
          + (c.discontinuities : ℝ≥0∞)
        = ENNReal.ofReal
          ((c.missed * (1 + 2 * rateExcess m d) + c.discontinuities : ℝ≥0) : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]
      push_cast
      rfl
    rw [e]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    gcongr
  have hrateB : ∀ x : ℝ≥0∞,
      x ≤ ENNReal.ofReal (m.rate * (1 + 1 / (m.blockSize : ℝ)) * Γ) →
      ((c.missed : ℝ≥0∞) * ((1 + 2 * rateExcess m d : ℝ≥0) : ℝ≥0∞)
          + (c.discontinuities : ℝ≥0∞)) * x
        ≤ ENNReal.ofReal ((3 * c.missed + c.discontinuities)
          * (m.rate * (1 + 1 / (m.blockSize : ℝ))) * G) := by
    intro x hx
    have hw0 : 0 ≤ (c.missed : ℝ) * (1 + 2 * Γ ^ 2) + c.discontinuities := by positivity
    have h5 : 0 ≤ ((c.missed : ℝ) + c.discontinuities) * (m.rate * (1 + 1 / (m.blockSize : ℝ))) :=
      mul_nonneg (by positivity) hκ0
    have h6 := mul_le_mul_of_nonneg_left hΓG h5
    rw [← hΓ3] at h6
    calc ((c.missed : ℝ≥0∞) * ((1 + 2 * rateExcess m d : ℝ≥0) : ℝ≥0∞)
            + (c.discontinuities : ℝ≥0∞)) * x
        ≤ ENNReal.ofReal (c.missed * (1 + 2 * Γ ^ 2) + c.discontinuities)
          * ENNReal.ofReal (m.rate * (1 + 1 / (m.blockSize : ℝ)) * Γ) := mul_le_mul' hW hx
      _ = ENNReal.ofReal ((c.missed * (1 + 2 * Γ ^ 2) + c.discontinuities)
          * (m.rate * (1 + 1 / (m.blockSize : ℝ)) * Γ)) := (ENNReal.ofReal_mul hw0).symm
      _ ≤ ENNReal.ofReal ((3 * c.missed + c.discontinuities)
          * (m.rate * (1 + 1 / (m.blockSize : ℝ))) * G) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← hΓ3]
          nlinarith [h6]
  -- The four parts together.
  have n1 : 0 ≤ (c.sync : ℝ) * ((2 * A) ^ 2 * G) :=
    mul_nonneg (NNReal.coe_nonneg _) (mul_nonneg (sq_nonneg _) hG0)
  have n2 : 0 ≤ (c.latency : ℝ) * ((|L| + A) * G) :=
    mul_nonneg (NNReal.coe_nonneg _) (mul_nonneg (add_nonneg (abs_nonneg L) hA0) hG0)
  have n3 : 0 ≤ (c.tracking : ℝ) * ((|L| + A + |m.targetLatency|) ^ 2 * G) :=
    mul_nonneg (NNReal.coe_nonneg _) (mul_nonneg (sq_nonneg _) hG0)
  have n4 : 0 ≤ (3 * (c.missed : ℝ) + c.discontinuities)
      * (m.rate * (1 + 1 / (m.blockSize : ℝ))) * G :=
    mul_nonneg (mul_nonneg (by positivity) hκ0) hG0
  unfold latencyCosts
  refine (add_le_add (add_le_add (add_le_add hp1 hp2) hp3) (hrateB _ ?_)).trans ?_
  · refine max_le ?_ ?_
    · unfold lateRateBound
      refine average_le fun r => ENNReal.ofReal_le_ofReal ?_
      have h1 : m.rate * Real.exp (d.deviceLogRate (some (m.device r)))
            + m.rate * Real.exp (d.deviceLogRate none) / m.blockSize
          ≤ m.rate * Γ + m.rate * Γ / m.blockSize :=
        add_le_add (mul_le_mul_of_nonneg_left (hyr r) hρ.le)
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyc hρ.le) hB.le)
      have h2 : 0 ≤ m.rate * Γ + m.rate * Γ / m.blockSize := by positivity
      calc (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))
              + m.rate * Real.exp (d.deviceLogRate none) / m.blockSize)
            * lateProbability f m.sender (m.host r)
              (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
              (marginLeast m f d lookahead L r)
          ≤ (m.rate * Γ + m.rate * Γ / m.blockSize) * 1 :=
            mul_le_mul h1 (lateProbability_mem f _ _ _ _).2 (lateProbability_mem f _ _ _ _).1 h2
        _ = m.rate * (1 + 1 / (m.blockSize : ℝ)) * Γ := by ring
    · unfold outputRate
      refine average_le fun r => ENNReal.ofReal_le_ofReal ?_
      have h1 : m.rate * Real.exp (d.deviceLogRate (some (m.device r))) ≤ m.rate * Γ :=
        mul_le_mul_of_nonneg_left (hyr r) hρ.le
      have h3 : (0 : ℝ) ≤ m.rate * (1 / (m.blockSize : ℝ)) * Γ := by positivity
      have e : m.rate * (1 + 1 / (m.blockSize : ℝ)) * Γ
          = m.rate * Γ + m.rate * (1 / (m.blockSize : ℝ)) * Γ := by ring
      rw [e]
      linarith
  · rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) n3,
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg n1 n2) n3) n4]
    refine le_of_eq ?_
    congr 1
    ring

omit [DecidableEq H] in
/-- **The bound on the cost of a held level, by exponentials of the drawn
rates.** There is a constant `K`, which depends on the member, the level and
the weights, such that for every draw whose splits lie between zero and one,
`heldLevelCost` is at most `K` times one plus a sum of exponentials: of
three times the logarithm of the rate of the capture device's clock and of
each playback device's clock, of minus three times the logarithm of the rate
of the sender's clock and of each playback device's clock. -/
theorem exists_heldLevelCost_le [Fintype H] (m : GenerativeWorld H R) (f : Member H R)
    (lookahead : ℕ+) (L : ℝ) (c : Weights) :
    ∃ K : ℝ, ∀ d : Draw H R, (∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1) →
      heldLevelCost m f lookahead L c d
        ≤ ENNReal.ofReal (K * (1 + Real.exp (-3 * d.logRate m.sender)
            + Real.exp (3 * d.deviceLogRate none)
            + ∑ r : Fin R, (Real.exp (3 * d.deviceLogRate (some (m.device r)))
              + Real.exp (-3 * d.deviceLogRate (some (m.device r)))))) := by
  obtain ⟨K, hK⟩ := exists_latencyCosts_add_le m f lookahead L c
  refine ⟨K, fun d hsplit => le_trans ?_ (hK d hsplit)⟩
  unfold heldLevelCost
  refine add_le_add le_rfl (mul_le_mul' le_rfl ?_)
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

omit [DecidableEq H] in
/-- **A function of the draw under the bound by exponentials has a finite
mean.** Suppose that for every draw whose splits lie between zero and one, a
function of the draw is at most a constant `K` times one plus the sum of
exponentials of `exists_latencyCosts_add_le`. Then its mean is finite in
every random world of every member, because the logarithms of the rates of
the clocks are Gaussian. -/
theorem lintegral_lt_top_of_le_exp [Fintype H] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) {F : Draw H R → ℝ≥0∞} {K : ℝ}
    (hK : ∀ d : Draw H R, (∀ i j, d.split i j ∈ Set.Ioo (0 : ℝ) 1) →
      F d ≤ ENNReal.ofReal (K * (1 + Real.exp (-3 * d.logRate m.sender)
          + Real.exp (3 * d.deviceLogRate none)
          + ∑ r : Fin R, (Real.exp (3 * d.deviceLogRate (some (m.device r)))
            + Real.exp (-3 * d.deviceLogRate (some (m.device r))))))) :
    ∫⁻ ω, F (D ω) ∂P < ⊤ := by
  have hprob := hD.prob
  have hx : ∀ (t : ℝ) (h : H), Integrable (fun ω => Real.exp (t * (D ω).logRate h)) P :=
    fun t h => (hD.logRate_law h).integrable_comp
      (ProbabilityTheory.integrable_exp_mul_gaussianReal t)
  have hy : ∀ (t : ℝ) (x : Option (Fin R)),
      Integrable (fun ω => Real.exp (t * (D ω).deviceLogRate x)) P :=
    fun t x => (hD.deviceLogRate_law x).integrable_comp
      (ProbabilityTheory.integrable_exp_mul_gaussianReal t)
  have hint : Integrable (fun ω => K * (1 + Real.exp (-3 * (D ω).logRate m.sender)
      + Real.exp (3 * (D ω).deviceLogRate none)
      + ∑ r : Fin R, (Real.exp (3 * (D ω).deviceLogRate (some (m.device r)))
        + Real.exp (-3 * (D ω).deviceLogRate (some (m.device r)))))) P := by
    refine Integrable.const_mul ?_ K
    refine (((integrable_const (1 : ℝ)).add (hx (-3) m.sender)).add (hy 3 none)).add ?_
    exact integrable_finsetSum _ fun r _ =>
      (hy 3 (some (m.device r))).add (hy (-3) (some (m.device r)))
  calc ∫⁻ ω, F (D ω) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (K * (1 + Real.exp (-3 * (D ω).logRate m.sender)
          + Real.exp (3 * (D ω).deviceLogRate none)
          + ∑ r : Fin R, (Real.exp (3 * (D ω).deviceLogRate (some (m.device r)))
            + Real.exp (-3 * (D ω).deviceLogRate (some (m.device r)))))) ∂P :=
        lintegral_mono fun ω => hK (D ω) (fun i j => hD.split_mem ω i j)
    _ < ⊤ := hint.lintegral_lt_top

omit [DecidableEq H] in
/-- **The mean of the bound on the cost of a held level is finite**, in
every random world of every member. -/
theorem lintegral_heldLevelCost_lt_top [Fintype H] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) (lookahead : ℕ+) (L : ℝ)
    (c : Weights) : ∫⁻ ω, heldLevelCost m f lookahead L c (D ω) ∂P < ⊤ := by
  obtain ⟨K, hK⟩ := exists_heldLevelCost_le m f lookahead L c
  exact lintegral_lt_top_of_le_exp hD (F := heldLevelCost m f lookahead L c) hK

/-- **The expected cost of a held level is finite.** In every random world
of a member with steady clocks in which no speaker is on the sender's host,
the controller that holds the level `L` has a finite expected cost, for
every level and all weights. -/
theorem expectedCost_heldLevel_lt_top [Fintype H] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D)
    (hf : f.SteadyClocks) (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hnos : ∀ r, m.host r ≠ m.sender)
    (hpsp : ∀ r, m.host r ∈ p.speakers) (c : Weights) :
    (solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).expectedCost
        P world lookahead c < ⊤ :=
  (expectedCost_le_heldLevelCost p hD hf hB lookahead L hps hnodup hcopies hperiod hnos hpsp
    c).trans_lt (lintegral_heldLevelCost_lt_top hD lookahead L c)

end Unisono.Solutions.Controller
