/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.ExpectedCost

/-!
# The controller with a limiter

The controller (`Unisono.Solutions.Controller`) does not keep the speed
bound of the solutions that it is compared with (`Solution.WithinStep`): a
new estimate of a clock line moves the position that is due by a fraction of
a frame between two output samples. The controller with a limiter is
`Solution.limited` applied to the controller, for a speed bound `u`. It
sends the same messages and sets the same timers. At each output sample it
plays the position that the controller chooses, except that the output
sample plays nothing of the source when the step from the previous output
sample would be a step of continuous playback that advances by one frame
outside `u` (`Unisono.Spec.Limiter`).

**Theorem** (`limited_withinStep`). In every world, with any estimators and
any rule for the level, the controller with a limiter keeps the speed bound
`u`.

The rest of the file holds the level at `L`, in a world whose clocks run at
constant rates, with exact timestamps and with pauses of links and none of hosts.
There the position that is due at output sample `k` of a speaker is a line
in `k`. The slope of the line is the rate of the capture device's clock
divided by the rate of the clock of the speaker's playback device
(`duePosition_eq`).

**Theorem** (`limited_plays_eq_heldLevel`). If that slope is within `u` of
one, then from some output sample on the speaker plays what it plays without
the limiter.

So in an outcome in which the slope of every speaker is within `u` of one,
for a bound `u` below one, the cost has the bound of the controller without
the limiter (`cost_limited_le_of_heldLevel`). In every other outcome the
limiter removes output samples, each output sample still plays the position
that is due or nothing, and the cost is bounded with the number of output
samples per second in place of the late rate (`cost_limited_le_outputs`).

`limitedCost` is the bound as a function of what is drawn. It is
`heldLevelCost` with a different condition for the bound on the late rate:
that the slope of every speaker is within `u` of one.

**Theorem** (`ae_cost_le_limitedCost`, `expectedCost_le_limitedCost`). In
every random world of a member with steady hosts in which no speaker is on
the sender's host, for a bound `u` below one, the cost of the controller
with a limiter is at most `limitedCost` of the draw in almost every outcome.
So its expected cost is at most the mean of `limitedCost`.

**Theorem** (`lintegral_limitedCost_lt_top`). The mean of `limitedCost` is
finite in every random world of every member, so the expected cost of the
controller with a limiter at a held level is finite
(`expectedCost_limited_lt_top`).

The theorems are upper bounds for one solution. They do not say that another
solution cannot have a lower cost, and the level `L` is given, not chosen by
the controller.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld MeasureTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} (p : FixedDelay.Params H)

/-- **The controller with a limiter keeps the speed bound**, in every world,
with any estimators and any rule for the level: in every step of continuous
playback, the position advances by one frame per output sample within `u`. -/
theorem limited_withinStep (clockEst : ClockEstimator) (deviceEst : DeviceEstimator)
    (levelRule : LevelRule H R) (u : ℝ) (w : World H R) (lookahead : ℕ+) :
    ((solution p clockEst deviceEst levelRule : Solution H R Payload).limited u).WithinStep w
      lookahead u :=
  Solution.limited_withinStep _ u w lookahead

/-- **Where the clocks of the devices agree within the bound, the limiter
lets the positions of a held level through.** Consider a world whose clocks
run at constant rates, with exact timestamps and with pauses of links and of
hosts, a speaker `r` whose host is not the sender's, a device estimator that
is exact on undisturbed reports, and the level held at `L`. Suppose that
from some true time on the host's estimate of the sender's clock is the line
of its undelayed exchanges, and that the rate of the capture device's clock
divided by the rate of the clock of the speaker's playback device is within
`u` of one. Then from some output sample on, the speaker of the controller
with a limiter plays what the speaker of the controller plays. -/
theorem limited_plays_eq_heldLevel (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀)
    {u : ℝ} (hu : |Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1| ≤ u) :
    ∃ K, ∀ k, K ≤ k →
      ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).limited u).plays
          w lookahead r k
        = (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
          lookahead r k := by
  obtain ⟨K, hK⟩ := speaker_chooses p hS lookahead hdev L hps hnodup hcopies r hnos hpsp hline
  refine ⟨K + 1, Solution.limited_plays_eq _ u w lookahead (K := K)
    (a := duePosition m f d w L r 0) hu fun n b k hk hkb hnb hne x hx => ?_⟩
  rcases hK n b k hk hkb hnb hne with h | h
  · rw [h] at hx
    cases hx
  · rw [h] at hx
    obtain rfl := Option.some.inj hx
    exact duePosition_eq hS L r k

/-- **The cost of a held level with a limiter, where the clocks of the
devices agree within the bound.** Consider a world whose clocks run at
constant rates, with exact timestamps and with pauses of links and none of hosts,
in which no speaker is on the sender's host. The controller with a limiter
for the speed bound `u`, below one, uses a device estimator that is exact on
undisturbed reports and holds the level at `L`, and from some true time on
the estimate of the sender's clock at every speaker's host is the line of
its undelayed exchanges. Suppose that the rate of the capture device's clock
divided by the rate of the clock of every playback device is within `u` of
one, and exceeds one by at most `δ`. Then the cost is at most the costs of
the speakers' latencies in synchronization, latency and tracking, plus the
weight of missed samples times `1 + 2 δ`, plus the weight of
discontinuities, times the late rate. -/
theorem cost_limited_le_of_heldLevel (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hline : ∀ r, ∃ T₀, ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w
      lookahead clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀)
    {u : ℝ} (hu1 : u < 1) (hu : ∀ r, |Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1| ≤ u)
    {δ : ℝ≥0} (hδ : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1 ≤ δ) (c : Weights) :
    ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).limited u).cost w
        lookahead c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * lateRate m f d w lookahead L := by
  obtain ⟨K₀, hK₀⟩ := exists_plays_heldLevel p hS lookahead hdev L hps hnodup hcopies hnos hpsp
    hline
  choose T₀ hT₀ using hline
  choose K hK using fun r => limited_plays_eq_heldLevel p hS lookahead hdev L hps hnodup
    hcopies r (hnos r) (hpsp r) (hT₀ r) (hu r)
  unfold Solution.cost
  refine cost_le_of_plays_margin hS lookahead L (K₀ := max K₀ (Finset.univ.sup K))
    (fun r k hk => ?_) (fun r => ?_) hδ c
  · rw [hK r k ((Finset.le_sup (Finset.mem_univ r)).trans ((le_max_right _ _).trans hk))]
    exact hK₀ r k ((le_max_left _ _).trans hk)
  · have h := (abs_le.mp (hu r)).2
    linarith

/-- **The cost of a held level with a limiter, at any rates of the devices'
clocks.** Consider the world and the controller with a limiter of
`cost_limited_le_of_heldLevel`, for any speed bound `u` and any rates of the
devices' clocks. Suppose that the rate of the capture device's clock divided
by the rate of the clock of every playback device exceeds one by at most
`δ`. Then the cost is at most the costs of the speakers' latencies in
synchronization, latency and tracking, plus the weight of missed samples
times `1 + 2 δ`, plus the weight of discontinuities, times the number of
output samples per second in true time, averaged over the speakers. -/
theorem cost_limited_le_outputs (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} {deviceEst : DeviceEstimator} (hdev : deviceEst.Exact) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hline : ∀ r, ∃ T₀, ClockLineFrom (solution p clockEst deviceEst (constantLevel L)) w
      lookahead clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀)
    (u : ℝ) {δ : ℝ≥0} (hδ : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) - 1 ≤ δ) (c : Weights) :
    ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).limited u).cost w
        lookahead c
      ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
          * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
            ENNReal.ofReal ((latencyOf m f d L q.1 - latencyOf m f d L q.2) ^ 2))
        + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f d L r))
        + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
          * ∑ r, ENNReal.ofReal ((latencyOf m f d L r - m.targetLatency) ^ 2))
        + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
          * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal
            (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))) := by
  obtain ⟨K₀, hK₀⟩ := exists_plays_heldLevel p hS lookahead hdev L hps hnodup hcopies hnos hpsp
    hline
  unfold Solution.cost
  refine cost_le_outputs_of_plays_due hS L (K₀ := K₀) (fun r k hk x hx => ?_) hδ c
  -- Whatever the limiter lets through, the controller plays.
  have h := Solution.limited_plays_eq_some _ u w lookahead hx
  rw [hK₀ r k hk] at h
  split_ifs at h with h'
  exact (Option.some.inj h).symm

open Classical in
/-- The bound on the cost of the controller with a limiter that holds the
level `L`, for the speed bound `u`, the draw `d` and the weights `c`. It is
the costs of the speakers' latencies plus a multiple of a rate. The rate is
the bound on the late rate when, for every speaker, the rate of the capture
device's clock divided by the rate of the clock of the speaker's playback
device is within `u` of one. It is the number of output samples per second
otherwise. -/
def limitedCost [Fintype H] (m : GenerativeWorld H R) (f : Member H R) (lookahead : ℕ+)
    (u L : ℝ) (c : Weights) (d : Draw H R) : ℝ≥0∞ :=
  latencyCosts m f L c d
    + ((c.missed : ℝ≥0∞) * ((1 + 2 * rateExcess m d : ℝ≥0) : ℝ≥0∞)
        + (c.discontinuities : ℝ≥0∞))
      * if ∀ r, |Real.exp (d.deviceLogRate none)
          / Real.exp (d.deviceLogRate (some (m.device r))) - 1| ≤ u
        then lateRateBound m f lookahead L d else outputRate m d

/-- **The cost of a held level with a limiter in a member with steady
hosts.** In every random world of a member with steady hosts in which no
speaker is on the sender's host, the cost of the controller with a limiter
for a speed bound `u` below one, holding the level `L`, is at most
`limitedCost` of the draw, in almost every outcome. -/
theorem ae_cost_le_limitedCost [Fintype H] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D) (hf : f.SteadyHosts)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) {u : ℝ} (hu1 : u < 1) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hnos : ∀ r, m.host r ≠ m.sender)
    (hpsp : ∀ r, m.host r ∈ p.speakers) (c : Weights) :
    ∀ᵐ ω ∂P,
      ((solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).limited
          u).cost (world ω) lookahead c
        ≤ limitedCost m f lookahead u L c (D ω) := by
  filter_upwards [hD.ae_constantRates hf hB,
    ae_twoUndelayed p hD hf hB lookahead leastRoundTrip twoReports (constantLevel L) hps
      hcopies hperiod, ae_lateRate_le hD hf hB lookahead L hnos] with ω hS hund hlate
  have hδ := fun r => sub_one_le_rateExcess m (D ω) r
  have hline : ∀ r, ∃ T₀, ClockLineFrom (solution p leastRoundTrip twoReports (constantLevel L))
      (world ω) lookahead leastRoundTrip (m.host r) (exchangeLine m f (D ω) (m.host r))
      T₀ := by
    intro r
    obtain ⟨n₀, hn₀⟩ := hund r (hnos r)
    exact ⟨_, clockLineFrom_of_undelayed p hS lookahead leastRoundTrip_exactFromLeast
      twoReports (constantLevel L) hps hn₀⟩
  unfold limitedCost
  split_ifs with hu
  · refine (cost_limited_le_of_heldLevel p hS lookahead twoReports_exact L hps hnodup hcopies
      hnos hpsp hline hu1 hu hδ c).trans ?_
    exact add_le_add le_rfl (mul_le_mul' le_rfl hlate)
  · exact cost_limited_le_outputs p hS lookahead twoReports_exact L hps hnodup hcopies hnos
      hpsp hline u hδ c

/-- **The expected cost of a held level with a limiter in a member with
steady hosts.** In every random world of a member with steady hosts in
which no speaker is on the sender's host, the expected cost of the
controller with a limiter for a speed bound `u` below one, holding the level
`L`, is at most the mean of `limitedCost` of the draw. -/
theorem expectedCost_le_limitedCost [Fintype H] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D)
    (hf : f.SteadyHosts) (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) {u : ℝ}
    (hu1 : u < 1) (L : ℝ) (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup)
    (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period) (hnos : ∀ r, m.host r ≠ m.sender)
    (hpsp : ∀ r, m.host r ∈ p.speakers) (c : Weights) :
    ((solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).limited
        u).expectedCost P world lookahead c
      ≤ ∫⁻ ω, limitedCost m f lookahead u L c (D ω) ∂P :=
  lintegral_mono_ae (ae_cost_le_limitedCost p hD hf hB lookahead hu1 L hps hnodup hcopies
    hperiod hnos hpsp c)

omit [DecidableEq H] in
/-- **The mean of the bound on the cost of a held level with a limiter is
finite**, in every random world of every member, for every speed bound. -/
theorem lintegral_limitedCost_lt_top [Fintype H] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → Draw H R} (hD : m.Prior f P D) (lookahead : ℕ+) (u L : ℝ)
    (c : Weights) : ∫⁻ ω, limitedCost m f lookahead u L c (D ω) ∂P < ⊤ := by
  obtain ⟨K, hK⟩ := exists_latencyCosts_add_le m f lookahead L c
  refine lintegral_lt_top_of_le_exp hD (F := limitedCost m f lookahead u L c) (K := K)
    fun d hsplit => le_trans ?_ (hK d hsplit)
  unfold limitedCost
  refine add_le_add le_rfl (mul_le_mul' le_rfl ?_)
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **The expected cost of a held level with a limiter is finite.** In every
random world of a member with steady hosts in which no speaker is on the
sender's host, the controller with a limiter for a speed bound `u` below
one, holding the level `L`, has a finite expected cost, for every level and
all weights. -/
theorem expectedCost_limited_lt_top [Fintype H] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D)
    (hf : f.SteadyHosts) (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) {u : ℝ}
    (hu1 : u < 1) (L : ℝ) (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup)
    (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period) (hnos : ∀ r, m.host r ≠ m.sender)
    (hpsp : ∀ r, m.host r ∈ p.speakers) (c : Weights) :
    ((solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).limited
        u).expectedCost P world lookahead c < ⊤ :=
  (expectedCost_le_limitedCost p hD hf hB lookahead hu1 L hps hnodup hcopies hperiod hnos hpsp
    c).trans_lt (lintegral_limitedCost_lt_top hD lookahead u L c)

end Unisono.Solutions.Controller
