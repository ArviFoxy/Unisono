/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Cost
public import Unisono.Solutions.Controller.Queries
public import Unisono.Spec.Models.GenerativeIdle

/-!
# Two clock exchanges escape every pause, almost surely

The controller's estimate of the sender's clock is exact once the view of a
host holds two clock exchanges that no pause delayed
(`Unisono.Solutions.Controller.Pauses`). That was assumed of the outcome.
This file proves it in almost every outcome of every random world of a member
with steady clocks.

* `arrival_of_idle`: a message sent while the sending host, the link and the
  receiving host have no backlog takes the least delay of its direction.
* `exists_twoUndelayed`: in a world whose clocks run at constant rates,
  suppose that all links and hosts are idle together during periods of any
  length, again and again. Then at some step the view of every receiving host
  holds two clock exchanges that no pause delayed, whose queries were sent at
  different readings. The host sends a query in every period that is longer
  than the polling period plus the time between two requests of one of its
  speakers; a query sent in an idle period reaches the sender, and its answer
  reaches the host, without delay.
* `ae_twoUndelayed`: this holds in almost every outcome of every random
  world of a member with steady clocks, because all links and hosts are idle
  together again and again in almost every outcome (`Prior.ae_idle`).
* `ae_cost_le_heldLevel`: so in almost every outcome the cost of a held level
  is bounded by the costs of the latencies plus a multiple of the late rate
  of the outcome, in the outcomes in which the clock of the capture device
  runs less than twice as fast as the clock of every playback device.

The late rate of an outcome is not evaluated here.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld MeasureTheory
open scoped ENNReal NNReal

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} (p : FixedDelay.Params H)

omit [DecidableEq H] in
/-- **A message sent in an idle period takes the least delay.** If the
sending host, the link and the receiving host have no backlog from true time
`a` to `b`, a message sent in that period that can arrive in it after the
least delay of its direction does arrive after that delay. -/
theorem arrival_of_idle {a b : ℝ} (i j : H) {s : Time}
    (hidle : ∀ (x : PauseIndex H) (t : ℝ), a ≤ t → t ≤ b → IsBacklog (d.paused x) t 0)
    (has : a ≤ s) (hsb : s + d.split i j * f.roundTrip i j ≤ b)
    (hδ : 0 ≤ d.split i j * f.roundTrip i j) :
    d.arrival f i j s = s + d.split i j * f.roundTrip i j := by
  have h1 : backlog (d.hostPaused i) s = 0 :=
    (hidle (.inr i) s has (by linarith)).backlog_eq
  have h2 : backlog (d.linkPaused i j) s = 0 :=
    (hidle (.inl (i, j)) s has (by linarith)).backlog_eq
  have h3 : backlog (d.hostPaused j) (s + d.split i j * f.roundTrip i j) = 0 :=
    (hidle (.inr j) _ (by linarith) hsb).backlog_eq
  unfold Draw.arrival
  simp only [h1, h2, h3, add_zero]

omit [DecidableEq H] in
/-- The requests of a playback device are evenly spaced. -/
theorem asked_succ_sub (hS : ConstantRates m f d w) (r : Fin R) (b : ℕ) :
    (w.speaker r).asked (b + 1) - (w.speaker r).asked b
      = m.blockSize / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := by
  have h1 := hS.asked r b
  have h2 := hS.asked r (b + 1)
  rw [hS.builds.speaker_first, hS.out] at h1 h2
  have e : (((b + 1) * m.blockSize : ℕ) : ℝ)
        / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
      - ((b * m.blockSize : ℕ) : ℝ) / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
      = m.blockSize / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := by
    push_cast
    ring
  linarith

omit [DecidableEq H] in
/-- After the first request of a playback device, every period as long as the
time between two requests holds a request. -/
theorem exists_asked_between (hS : ConstantRates m f d w) (r : Fin R) {T P : ℝ}
    (hT : (w.speaker r).asked 0 ≤ T) (hP : 0 ≤ P) :
    ∃ b, T + P ≤ (w.speaker r).asked b
      ∧ (w.speaker r).asked b
        ≤ T + P + m.blockSize / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) := by
  classical
  have hex : ∃ b, T + P ≤ (w.speaker r).asked b := by
    obtain ⟨b, hb⟩ := hS.asked_unbounded r (T + P)
    exact ⟨b, hb.le⟩
  have hΔ : 0 < (m.blockSize : ℝ) / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) :=
    div_pos (Nat.cast_pos.mpr m.blockSize_pos) (mul_pos m.rate_pos (Real.exp_pos _))
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]
    linarith
  · obtain ⟨b', hb'⟩ : ∃ b', Nat.find hex = b' + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := Nat.find_min hex (show b' < Nat.find hex by omega)
    have hstep := asked_succ_sub hS r b'
    rw [hb']
    have := not_le.mp hmin
    linarith

/-- In a world whose clocks run at constant rates, suppose that all links and
hosts are idle together during periods of any length, again and again. Then
after every true time a receiving host sends a clock query whose exchange is
not delayed, and from some step on its view holds that exchange. -/
theorem exists_undelayed_exchange (hS : ConstantRates m f d w) (lookahead : ℕ+)
    (hps : p.sender = m.sender) (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period) (r : Fin R)
    (hnos : m.host r ≠ m.sender)
    (hidle : ∀ M N : ℕ, ∃ a : ℕ, N ≤ a ∧ ∀ (x : PauseIndex H) (t : ℝ),
      (a : ℝ) ≤ t → t ≤ a + M → IsBacklog (d.paused x) t 0) (N : ℕ) :
    ∃ s : Time, (N : ℝ) ≤ s ∧ ∃ k, ∀ k', k ≤ k' →
      ∃ x ∈ plainExchangesOf (((FixedDelay.solution p :
          Solution H R FixedDelay.Payload).states w lookahead k').views (m.host r)),
        x.sent = (w.clock (m.host r)).read s
          ∧ x.roundTrip = undelayedRoundTrip m f d (m.host r) := by
  have hsend : w.sender = m.sender := hS.builds.sender_eq
  have hh : w.host r = m.host r := congrFun hS.builds.host_eq r
  have hsender : p.sender = w.sender := hps.trans hsend.symm
  have hg := Real.exp_pos (d.logRate (m.host r))
  have hδ₁ := hS.delay_pos (m.host r) m.sender
  have hδ₂ := hS.delay_pos m.sender (m.host r)
  have hΔ : 0 < (m.blockSize : ℝ) / (m.rate * Real.exp (d.deviceLogRate (some (m.device r)))) :=
    div_pos (Nat.cast_pos.mpr m.blockSize_pos) (mul_pos m.rate_pos (Real.exp_pos _))
  have hP : 0 ≤ p.period / Real.exp (d.logRate (m.host r)) := div_nonneg hperiod hg.le
  -- A period that holds a request at which the host asks, and the exchange of that query.
  obtain ⟨a, haN, hidle_a⟩ := hidle
    ⌈p.period / Real.exp (d.logRate (m.host r))
      + m.blockSize / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
      + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender
      + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)⌉₊
    (max N ⌈(w.speaker r).asked 0⌉₊)
  have hM := Nat.le_ceil (p.period / Real.exp (d.logRate (m.host r))
      + m.blockSize / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
      + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender
      + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
  have haN' : (N : ℝ) ≤ a := Nat.cast_le.mpr ((le_max_left _ _).trans haN)
  have ha0 : (w.speaker r).asked 0 ≤ a :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans haN))
  obtain ⟨b, hb1, hb2⟩ := exists_asked_between hS r ha0 hP
  have hb : (w.clock (w.host r)).read (a : ℝ) + p.period
      ≤ (w.clock (w.host r)).read ((w.speaker r).asked b) := by
    rw [hh, hS.clock, hS.clock]
    have h1 := mul_le_mul_of_nonneg_left hb1 hg.le
    rw [mul_add, mul_div_cancel₀ _ hg.ne'] at h1
    linarith
  obtain ⟨n, s, r', outs, st, hn, hask, hTs, hsb⟩ := FixedDelay.exists_query p w lookahead
    hS.handed_unbounded hS.asked_unbounded hperiod r (by rw [hh, hps]; exact hnos) hb
  rw [hh] at hn hask
  -- The query and its answer meet no backlog.
  have harr₁ : d.arrival f (m.host r) m.sender s
      = s + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender :=
    arrival_of_idle (m.host r) m.sender hidle_a hTs (by linarith) hδ₁.le
  have harr₂ : d.arrival f m.sender (m.host r)
        (s + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender)
      = s + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender
        + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r) :=
    arrival_of_idle m.sender (m.host r) hidle_a (by linarith) (by linarith) hδ₂.le
  have hstrict : ∀ s', s < s' →
      d.arrival f (m.host r) w.sender s < d.arrival f (m.host r) w.sender s' := by
    intro s' hs'
    rw [hsend, harr₁]
    have := hS.builds.le_arrival (m.host r) m.sender s'
    linarith
  obtain ⟨k, hk⟩ := FixedDelay.exchange_of_query p w lookahead
    (A := fun i j s => d.arrival f i j s) (fun i j s q => hS.builds.deliver i j s q) hsender
    hcopies (FixedDelay.progress_of_unbounded p w lookahead hS.handed_unbounded
      hS.asked_unbounded) hn hask hstrict
  refine ⟨s, haN'.trans hTs, k, fun k' hk' => ⟨_, hk k' hk', rfl, ?_⟩⟩
  show (w.clock (m.host r)).read
        (d.arrival f w.sender (m.host r) (d.arrival f (m.host r) w.sender s))
      - (w.clock (m.host r)).read s = undelayedRoundTrip m f d (m.host r)
  rw [hsend, harr₁, harr₂, hS.clock, hS.clock]
  unfold undelayedRoundTrip
  ring

/-- **Two clock exchanges escape the pauses when all links and hosts are
idle together again and again.** In a world whose clocks run at constant
rates, suppose that all links and hosts are idle together during periods of
any length, again and again. Then at some step the view of every receiving
host holds two clock exchanges that no pause delayed, whose queries were sent
at different readings. -/
theorem exists_twoUndelayed (hS : ConstantRates m f d w) (lookahead : ℕ+)
    (clockEst : ClockEstimator) (deviceEst : DeviceEstimator) (levelRule : LevelRule H R)
    (hps : p.sender = m.sender) (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period) (r : Fin R)
    (hnos : m.host r ≠ m.sender)
    (hidle : ∀ M N : ℕ, ∃ a : ℕ, N ≤ a ∧ ∀ (x : PauseIndex H) (t : ℝ),
      (a : ℝ) ≤ t → t ≤ a + M → IsBacklog (d.paused x) t 0) :
    ∃ n₀, TwoUndelayed (solution p clockEst deviceEst levelRule) w lookahead m f d (m.host r)
      n₀ := by
  obtain ⟨s₁, -, k₁, hk₁⟩ := exists_undelayed_exchange p hS lookahead hps hcopies hperiod r
    hnos hidle 0
  obtain ⟨s₂, hs₂, k₂, hk₂⟩ := exists_undelayed_exchange p hS lookahead hps hcopies hperiod r
    hnos hidle (⌈s₁⌉₊ + 1)
  have hlt : s₁ < s₂ := by
    have h1 := Nat.le_ceil s₁
    push_cast at hs₂
    linarith
  obtain ⟨x₁, hx₁, hsent₁, hrt₁⟩ := hk₁ (max k₁ k₂) (le_max_left _ _)
  obtain ⟨x₂, hx₂, hsent₂, hrt₂⟩ := hk₂ (max k₁ k₂) (le_max_right _ _)
  have hmore := sendsMore (R := R) p clockEst deviceEst levelRule
  refine ⟨max k₁ k₂, ?_⟩
  unfold TwoUndelayed
  rw [exchangesOf_eq, Solution.views_forget w Payload.plain lookahead hmore (max k₁ k₂)
    (m.host r)]
  refine ⟨x₁, hx₁, x₂, hx₂, hrt₁, hrt₂, ?_⟩
  rw [hsent₁, hsent₂]
  exact ((w.clock (m.host r)).strictMono hlt).ne

/-- **Two clock exchanges escape every pause, almost surely.** In every
random world of a member with steady clocks, in almost every outcome, at some
step the view of every receiving host holds two clock exchanges that no pause
delayed, whose queries were sent at different readings. -/
theorem ae_twoUndelayed [Fintype H] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D) (hf : f.SteadyClocks)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) (clockEst : ClockEstimator)
    (deviceEst : DeviceEstimator) (levelRule : LevelRule H R) (hps : p.sender = m.sender)
    (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period) :
    ∀ᵐ ω ∂P, ∀ r : Fin R, m.host r ≠ m.sender →
      ∃ n₀, TwoUndelayed (solution p clockEst deviceEst levelRule) (world ω) lookahead m f
        (D ω) (m.host r) n₀ := by
  filter_upwards [hD.ae_constantRates hf hB, hD.ae_idle] with ω hS hidle r hnos
  exact exists_twoUndelayed p hS lookahead clockEst deviceEst levelRule hps hcopies hperiod r
    hnos hidle

/-- **The cost of a held level in almost every outcome.** In every random
world of a member with steady clocks in which no speaker is on the sender's
host, the controller with the least-round-trip estimator holds the level at
`L`. In almost every outcome in which the clock of the capture device runs
less than twice as fast as the clock of every playback device, and faster by
a fraction of at most `δ`, the cost is at most the costs of the speakers'
latencies in synchronization, latency and tracking, plus the weight of
missed samples times `1 + 2 δ`, plus the weight of discontinuities, times
the late rate of the outcome. -/
theorem ae_cost_le_heldLevel [Fintype H] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Draw H R} {world : Ω → World H R} (hD : m.Prior f P D) (hf : f.SteadyClocks)
    (hB : ∀ ω, m.Builds f (D ω) (world ω)) (lookahead : ℕ+) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (hnos : ∀ r, m.host r ≠ m.sender)
    (hpsp : ∀ r, m.host r ∈ p.speakers) (δ : ℝ≥0) (c : Weights) :
    ∀ᵐ ω ∂P,
      (∀ r, Real.exp ((D ω).deviceLogRate none)
        / Real.exp ((D ω).deviceLogRate (some (m.device r))) < 2) →
      (∀ r, Real.exp ((D ω).deviceLogRate none)
        / Real.exp ((D ω).deviceLogRate (some (m.device r))) - 1 ≤ δ) →
      (solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).cost
          (world ω) lookahead c
        ≤ (c.sync : ℝ≥0∞) * (((R : ℝ≥0∞) ^ 2)⁻¹
            * ∑ q ∈ Finset.univ.filter (fun q : Fin R × Fin R => q.1 < q.2),
              ENNReal.ofReal ((latencyOf m f (D ω) L q.1 - latencyOf m f (D ω) L q.2) ^ 2))
          + (c.latency : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹ * ∑ r, ENNReal.ofReal (latencyOf m f (D ω) L r))
          + (c.tracking : ℝ≥0∞) * ((R : ℝ≥0∞)⁻¹
            * ∑ r, ENNReal.ofReal ((latencyOf m f (D ω) L r - m.targetLatency) ^ 2))
          + ((c.missed : ℝ≥0∞) * ((1 + 2 * δ : ℝ≥0) : ℝ≥0∞) + (c.discontinuities : ℝ≥0∞))
            * lateRate m f (D ω) (world ω) lookahead L := by
  filter_upwards [hD.ae_constantRates hf hB,
    ae_twoUndelayed p hD hf hB lookahead leastRoundTrip twoReports (constantLevel L) hps
      hcopies hperiod] with ω hS hund hratio hδ
  exact cost_le_under_pauses p hS lookahead L hps hnodup hcopies hnos hpsp
    (fun r => hund r (hnos r)) hratio hδ c

end Unisono.Solutions.Controller
