/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.HeldLevel
public import Unisono.Solutions.Controller.Views
public import Unisono.Solutions.FixedDelay.Latency
public import Unisono.Spec.ExactLatency
public import Unisono.Spec.Models.GenerativeRates

/-!
# The controller with clocks at constant rates

Consider a world in which the clocks of the hosts and of the audio devices
run at constant rates, each its own, the links have constant delays, and the
devices report exact timestamps (`GenerativeWorld.ConstantDelays`). The
baseline goes wrong in such a world in two ways: its clock estimate goes
stale between one clock query and the next, and it takes the rate of a
device for the rate of its host's clock. The controller
(`Unisono.Solutions.Controller`) measures both.

**Theorem** (`playsAtLatencies`). In such a world, with estimators that are
exact on undisturbed data and the level held at `L`, from some output sample
on every output sample of each speaker plays the sound captured exactly

`L / (rate of the sender's clock) + asymmetry of the speaker's host`

before the sample leaves. The asymmetry of a host is half the difference
between the delay from the sender to it and the delay back. The first term
is the level in true time: the level is counted on the sender's clock, and
no host can observe how fast that clock runs against true time.

The theorem is the case without pauses of the theorem about a held level
(`Unisono.Solutions.Controller.HeldLevel`): every block takes the least
delay of its direction, which is within the least margin, so no output
sample is missed.

* Every clock exchange in a host's view is a true exchange
  (`exchange_of_view`), and after some time the view holds two exchanges
  whose queries were sent at different readings (`exists_two_exchanges`), so
  an estimator that is exact on undisturbed exchanges returns the line of
  the undelayed exchanges (`clockLineFrom_of_exact`).
* The delay of every block is at most the least margin of every output
  sample, by the condition on the level.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} (p : FixedDelay.Params H)

/-! ## Arithmetic -/

/-- The least delay from the sender is within the least margin, under the
condition on the level. -/
private theorem leastMargin_arith {a mB ρ lead ε δsh δhs L rs gr gc : ℝ} (hε : ε < 1 / 2)
    (hρ : 0 < ρ) (hlead : 0 ≤ lead) (ha : 0 ≤ a) (hmB : 1 ≤ mB) (hrs : rs ≤ 1 + ε)
    (hrs0 : 0 < rs) (hgr : 1 - ε ≤ gr) (hgc : 1 - ε ≤ gc) (hL : 0 ≤ L)
    (hlat : ((a + 2 * (mB - 1)) / ρ + lead) / (1 - ε) + (δsh + δhs) / 2 < L / (1 + ε)) :
    δsh ≤ L / rs + (δsh - δhs) / 2 - lead / gr - (mB - 1) / (ρ * gr)
      - (a + mB - 1) / (ρ * gc) := by
  have h1ε : 0 < 1 - ε := by linarith
  have hρε : 0 < ρ * (1 - ε) := mul_pos hρ h1ε
  have h1 : L / (1 + ε) ≤ L / rs := by gcongr
  have h2 : lead / gr ≤ lead / (1 - ε) := by gcongr
  have h3 : (mB - 1) / (ρ * gr) ≤ (mB - 1) / (ρ * (1 - ε)) := by
    have hnum : 0 ≤ mB - 1 := by linarith
    gcongr
  have h4 : (a + mB - 1) / (ρ * gc) ≤ (a + mB - 1) / (ρ * (1 - ε)) := by
    have hnum : 0 ≤ a + mB - 1 := by linarith
    gcongr
  have e : ((a + 2 * (mB - 1)) / ρ + lead) / (1 - ε)
      = lead / (1 - ε) + (mB - 1) / (ρ * (1 - ε)) + (a + mB - 1) / (ρ * (1 - ε)) := by
    field_simp
    ring
  rw [e] at hlat
  linarith

/-! ## The clock exchanges in a host's view -/

/-- **Every clock exchange in a host's view is a true exchange.** The query
left the host at some true time; the sender's reading is the reading of the
sender's clock one delay later; and the answer arrived one more delay
later. -/
theorem exchange_of_view (hS : ConstantDelays m f d w) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) {n : ℕ} {h : H} {x : Exchange}
    (hx : x ∈ plainExchangesOf
      (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead n).views
        h)) :
    ∃ s₁ : Time, x.sent = (w.clock h).read s₁
      ∧ x.received = (w.clock w.sender).read (s₁ + d.split h w.sender * f.roundTrip h w.sender)
      ∧ x.arrived = (w.clock h).read (s₁ + d.split h w.sender * f.roundTrip h w.sender
          + d.split w.sender h * f.roundTrip w.sender h) := by
  obtain ⟨s₁, e1, e2, e3⟩ := exchange_of_built p hS.builds lookahead hsender hx
  rw [hS.arrival] at e2
  rw [hS.arrival, hS.arrival] at e3
  exact ⟨s₁, e1, e2, e3⟩

/-- **After some time, a host's view holds two clock exchanges whose queries
were sent at different readings.** -/
theorem exists_two_exchanges (hS : ConstantDelays m f d w) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 2) (hrates : ∀ h, |Real.exp (d.logRate h) - 1| ≤ ε)
    (hdevices : ∀ x, |Real.exp (d.deviceLogRate x) - 1| ≤ ε) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period)
    (r : Fin R) (hhs : w.host r ≠ w.sender) :
    ∃ T₀ : Time, ∀ n,
      T₀ < (FixedDelay.solution p : Solution H R FixedDelay.Payload).eventTime w lookahead n →
      ∃ x ∈ plainExchangesOf
          (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
            n).views (w.host r)),
        ∃ x' ∈ plainExchangesOf
          (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
            n).views (w.host r)),
          x.sent ≠ x'.sent := by
  have hw := hS.withinBounds hε0 hε hrates hdevices
  have hw' := hw
  obtain ⟨-, -, hspk, -, -, -, hlead, -, -, -, -⟩ := hw'
  have hρ := w.rate_pos
  have hδ₁ := hS.delay_pos (w.host r) w.sender
  have hδ₂ := hS.delay_pos w.sender (w.host r)
  have hP : 0 ≤ p.period / (1 - ε) := div_nonneg hperiod (by linarith)
  obtain ⟨b₁, hb₁⟩ := PlaybackDevice.asked_unbounded hρ (hspk r)
    (rateBounds m f d ε hε0 hε hS.delay_pos).deviceRate_lt_one (hlead r)
    ((w.speaker r).asked 0 + d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender
      + d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r))
  obtain ⟨b₂, hb₂⟩ := PlaybackDevice.asked_unbounded hρ (hspk r)
    (rateBounds m f d ε hε0 hε hS.delay_pos).deviceRate_lt_one (hlead r)
    ((w.speaker r).asked b₁ + p.period / (1 - ε))
  refine ⟨(w.speaker r).asked b₂
    + d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender
    + d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r), fun n hn => ?_⟩
  obtain ⟨k₀, -, hk₀e⟩ := FixedDelay.request_step p w _ hw lookahead r 0
  obtain ⟨k₁, -, hk₁e⟩ := FixedDelay.request_step p w _ hw lookahead r b₁
  obtain ⟨k₂, -, hk₂e⟩ := FixedDelay.request_step p w _ hw lookahead r b₂
  have hh₀ := Solution.handled_of_asked w (FixedDelay.solution p) lookahead hk₀e
  have hh₁ := Solution.handled_of_asked w (FixedDelay.solution p) lookahead hk₁e
  have hh₂ := Solution.handled_of_asked w (FixedDelay.solution p) lookahead hk₂e
  have ht₁ := Solution.handled_time w (FixedDelay.solution p) lookahead hh₁
  -- The estimate that the host remembers at request `b₁` was sent before it.
  obtain ⟨t₁, θ₁, -, ho₁, -, -⟩ := FixedDelay.offset_recent p w _ hw lookahead hsender hcopies
    hperiod hhs hh₀ (k := k₁) (by rw [ht₁]; exact hb₁)
  obtain ⟨s₁, s₂, s₄, hs₁, hs₄, hd₁, -, hd₂, -, -⟩ :=
    FixedDelay.offset_sample p w _ hw lookahead hsender hhs ho₁
  have hd₁' : d.split (w.host r) w.sender * f.roundTrip (w.host r) w.sender ≤ s₂ - s₁ := hd₁
  have hd₂' : d.split w.sender (w.host r) * f.roundTrip w.sender (w.host r) ≤ s₄ - s₂ := hd₂
  have hlt₁ : t₁ < (w.clock (w.host r)).read ((w.speaker r).asked b₁) := by
    rw [← hs₁]
    apply (w.clock (w.host r)).strictMono
    rw [ht₁] at hs₄
    linarith
  -- The estimate that it remembers at step `n` was sent after request `b₁`.
  obtain ⟨t₂, θ₂, s', ho₂, hle₂, hs'⟩ := FixedDelay.offset_recent p w _ hw lookahead hsender
    hcopies hperiod hhs hh₂ (k := n) hn
  have hs'' : (w.speaker r).asked b₂ - p.period / (1 - ε) ≤ s' := hs'
  have hlt₂ : (w.clock (w.host r)).read ((w.speaker r).asked b₁) < t₂ := by
    refine lt_of_lt_of_le ((w.clock (w.host r)).strictMono ?_) hle₂
    linarith
  -- Both answers are in the view at step `n`.
  have hns : w.host r ≠ p.sender := hsender ▸ hhs
  obtain ⟨e₁, he₁, i₁, u₁, F₁, hobs₁, -⟩ := FixedDelay.offset_received p (w.host r) hns _ ho₁
  obtain ⟨e₂, he₂, i₂, u₂, F₂, hobs₂, -⟩ := FixedDelay.offset_received p (w.host r) hns _ ho₂
  have hk₁n : k₁ ≤ n := by
    by_contra hcon
    have hmono := Solution.eventTime_mono w (FixedDelay.solution p) lookahead (not_le.mp hcon).le
    rw [ht₁] at hmono
    linarith
  obtain ⟨l, hl, -⟩ := Solution.views_append w (FixedDelay.solution p) lookahead hk₁n (w.host r)
  have he₁' : e₁ ∈ ((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
      n).views (w.host r) := by
    rw [hl]
    exact List.mem_append_left _ he₁
  exact ⟨⟨t₁, u₁, e₁.reading⟩, plainExchangesOf_mem he₁' hobs₁, ⟨t₂, u₂, e₂.reading⟩,
    plainExchangesOf_mem he₂ hobs₂, (hlt₁.trans hlt₂).ne⟩

/-! ## The clock line -/

/-- **Without pauses, an estimator that is exact on undisturbed exchanges
returns the line of the undelayed exchanges.** In a world with constant
rates within `ε < 1 / 2` of one and constant delays, from some true time on
the estimate of the sender's clock at a host other than the sender's is the
line on which its clock exchanges lie. -/
theorem clockLineFrom_of_exact (hS : ConstantDelays m f d w) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 2) (hrates : ∀ h, |Real.exp (d.logRate h) - 1| ≤ ε)
    (hdevices : ∀ x, |Real.exp (d.deviceLogRate x) - 1| ≤ ε) (lookahead : ℕ+)
    {clockEst : ClockEstimator} (hclock : clockEst.Exact) (deviceEst : DeviceEstimator)
    (levelRule : LevelRule H R) (hps : p.sender = m.sender) (hcopies : 0 < p.copies)
    (hperiod : 0 ≤ p.period) (r : Fin R) (hnos : m.host r ≠ m.sender) :
    ∃ T₀, ClockLineFrom (solution p clockEst deviceEst levelRule) w lookahead clockEst
      (m.host r) (exchangeLine m f d (m.host r)) T₀ := by
  have hmore := sendsMore (R := R) p clockEst deviceEst levelRule
  have hC := hS.toConstantRates
  have hsend : w.sender = m.sender := hS.builds.sender_eq
  have hhost : w.host r = m.host r := congrFun hS.builds.host_eq r
  have hsender : p.sender = w.sender := hps.trans hsend.symm
  have hhs : w.host r ≠ w.sender := by
    rw [hhost, hsend]
    exact hnos
  have hrh := Real.exp_pos (d.logRate (m.host r))
  obtain ⟨T₀, hT₀⟩ := exists_two_exchanges p hS hε0 hε hrates hdevices lookahead hsender hcopies
    hperiod r hhs
  refine ⟨T₀, fun n hn => ?_⟩
  rw [Solution.eventTime_forget w Payload.plain lookahead hmore] at hn
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := hT₀ n hn
  have hex : exchangesOf
      (((solution p clockEst deviceEst levelRule : Solution H R Payload).states w lookahead
        n).views (m.host r))
      = plainExchangesOf
        (((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
          n).views (w.host r)) := by
    rw [exchangesOf_eq, ← hhost, Solution.views_forget w Payload.plain lookahead hmore n
      (w.host r)]
  have hgoal : exchangeLine m f d (m.host r)
      = ⟨((d.offset m.sender
              - Real.exp (d.logRate m.sender) / Real.exp (d.logRate (m.host r))
                * d.offset (m.host r)
              + Real.exp (d.logRate m.sender)
                * (d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender))
            + (d.offset m.sender
              - Real.exp (d.logRate m.sender) / Real.exp (d.logRate (m.host r))
                * d.offset (m.host r)
              - Real.exp (d.logRate m.sender)
                * (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)))) / 2,
          Real.exp (d.logRate m.sender) / Real.exp (d.logRate (m.host r))⟩ := by
    unfold exchangeLine
    congr 1
    ring
  rw [hex, hgoal]
  refine hclock _ _ _ _ (fun x hx => ?_) ⟨x₁, hx₁, x₂, hx₂, hne⟩
  obtain ⟨s₁, e1, e2, e3⟩ := exchange_of_view p hS lookahead hsender hx
  rw [hC.clock, hhost] at e1 e3
  rw [hC.clock, hhost, hsend] at e2
  rw [hsend] at e3
  rw [e1, e2, e3]
  exact exchange_lines hrh.ne'

/-! ## The exact latency -/

/-- **A speaker of the controller plays at an exact latency.** Consider a
world with constant rates within `ε < 1 / 2` of one, a speaker `r` whose
host is not the sender's, estimators that are exact on undisturbed data, and
the level held at `L`. Suppose that the capture device's clock runs less
than twice as fast as the clock of the speaker's device, and that the level
exceeds the delivery margin. Then, from some output sample on, the speaker
plays continuously, and each output sample plays the sound captured exactly
the level divided by the rate of the sender's clock, plus the asymmetry of
the speaker's host, before the sample leaves. -/
theorem speaker_exact (hS : ConstantDelays m f d w) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hrates : ∀ h, |Real.exp (d.logRate h) - 1| ≤ ε)
    (hdevices : ∀ x, |Real.exp (d.deviceLogRate x) - 1| ≤ ε) (lookahead : ℕ+)
    {clockEst : ClockEstimator} (hclock : clockEst.Exact) {deviceEst : DeviceEstimator}
    (hdev : deviceEst.Exact) (L : ℝ) (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup)
    (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period) (r : Fin R)
    (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers)
    (hratio : Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) < 2)
    (hlat : ((((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate + m.lead) / (1 - ε)
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2
      < L / (1 + ε)) :
    ∃ K, ∀ k, K ≤ k →
      PlaysContinuously ((solution p clockEst deviceEst (constantLevel L) :
        Solution H R Payload).plays w lookahead r) k ∧
      ∃ x, (solution p clockEst deviceEst (constantLevel L) :
          Solution H R Payload).plays w lookahead r k = some x ∧
        w.captured x = (w.speaker r).out k
          - (L / Real.exp (d.logRate m.sender)
            + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
              - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) := by
  have hC := hS.toConstantRates
  have hρ := m.rate_pos
  have hrs := Real.exp_pos (d.logRate m.sender)
  have hgc := Real.exp_pos (d.deviceLogRate none)
  have hgr := Real.exp_pos (d.deviceLogRate (some (m.device r)))
  have hrsle : Real.exp (d.logRate m.sender) ≤ 1 + ε := by
    have := (abs_le.mp (hrates m.sender)).2
    linarith
  have hgrge : 1 - ε ≤ Real.exp (d.deviceLogRate (some (m.device r))) := by
    have := (abs_le.mp (hdevices (some (m.device r)))).1
    linarith
  have hgcge : 1 - ε ≤ Real.exp (d.deviceLogRate none) := by
    have := (abs_le.mp (hdevices none)).1
    linarith
  have h1 : (0 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (1 : ℝ) ≤ m.blockSize := by exact_mod_cast m.blockSize_pos
  -- The level is not negative.
  have hL : 0 ≤ L := by
    have hδ₁ := hS.delay_pos (m.host r) m.sender
    have hδ₂ := hS.delay_pos m.sender (m.host r)
    have h3 : 0 ≤ ((((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate + m.lead)
        / (1 - ε) :=
      div_nonneg (add_nonneg (div_nonneg (by linarith) hρ.le) m.lead_pos.le) (by linarith)
    by_contra hneg
    have h5 : L / (1 + ε) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le (by linarith)
    linarith
  obtain ⟨T₀, hline⟩ := clockLineFrom_of_exact p hS hε0 hε hrates hdevices lookahead hclock
    deviceEst (constantLevel L) hps hcopies hperiod r hnos
  obtain ⟨K, hK⟩ := plays_of_delay p hC lookahead hdev L hps hnodup hcopies r hnos hpsp hline
  -- Every block takes the least delay, which is within the least margin.
  have hdelay : ∀ c, blockDelay m f d w r c ≤ marginLeast m f d lookahead L r := by
    intro c
    unfold blockDelay marginLeast latencyOf
    rw [hS.arrival]
    have := leastMargin_arith hε hρ m.lead_pos.le h1 h2 hrsle hrs hgrge hgcge hL hlat
    linarith
  have hplays : ∀ k, K ≤ k →
      (solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
        lookahead r k = some (duePosition m f d w L r k) :=
    fun k hk => (hK k hk).1 (hdelay _)
  refine ⟨K, fun k hk => ⟨?_, duePosition m f d w L r k, hplays k hk, ?_⟩⟩
  · have hstep := duePosition_succ hC L r k
    have hc0 : 0 < Real.exp (d.deviceLogRate none)
        / Real.exp (d.deviceLogRate (some (m.device r))) := div_pos hgc hgr
    exact ⟨_, _, hplays k hk, hplays (k + 1) (le_trans hk (Nat.le_succ k)),
      by linarith, by linarith⟩
  · rw [captured_duePosition hC]
    rfl

/-- **The controller plays at exact latencies when clocks and devices run at
constant rates.** Consider a world with constant rates within `ε < 1 / 2` of
one, in which no speaker is on the sender's host, estimators that are exact
on undisturbed data, and the level held at `L`. Suppose that the capture
device's clock runs less than twice as fast as the clock of every speaker's
device, and that the level exceeds the delivery margin of every speaker.
Then, from some output sample on, every output sample of each speaker plays
the sound captured exactly the level divided by the rate of the sender's
clock, plus the asymmetry of the speaker's host, before the sample leaves. -/
theorem playsAtLatencies (hS : ConstantDelays m f d w) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hrates : ∀ h, |Real.exp (d.logRate h) - 1| ≤ ε)
    (hdevices : ∀ x, |Real.exp (d.deviceLogRate x) - 1| ≤ ε) (lookahead : ℕ+)
    {clockEst : ClockEstimator} (hclock : clockEst.Exact) {deviceEst : DeviceEstimator}
    (hdev : deviceEst.Exact) (L : ℝ) (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup)
    (hcopies : 0 < p.copies) (hperiod : 0 ≤ p.period)
    (hnos : ∀ r, m.host r ≠ m.sender) (hpsp : ∀ r, m.host r ∈ p.speakers)
    (hratio : ∀ r, Real.exp (d.deviceLogRate none)
      / Real.exp (d.deviceLogRate (some (m.device r))) < 2)
    (hlat : ∀ r,
      ((((lookahead : ℕ) : ℝ) + 2 * ((m.blockSize : ℝ) - 1)) / m.rate + m.lead) / (1 - ε)
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          + d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2
      < L / (1 + ε)) :
    ∃ K, w.PlaysAtLatencies
      ((solution p clockEst deviceEst (constantLevel L) : Solution H R Payload).plays w
        lookahead)
      (fun r => L / Real.exp (d.logRate m.sender)
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) K := by
  choose K hK using fun r => speaker_exact p hS hε0 hε hrates hdevices lookahead hclock hdev L
    hps hnodup hcopies hperiod r (hnos r) (hpsp r) (hratio r) (hlat r)
  exact ⟨Finset.univ.sup K, fun r k hk =>
    hK r k (le_trans (Finset.le_sup (Finset.mem_univ r)) hk)⟩


/-! ## The conditions of the theorem can be met -/

section Example

open MeasureTheory

/-- The example's model: three hosts, the sender and two speakers on their
own hosts and devices, devices at one frame per second in blocks of one
frame, a request lead of half a second, and shape two. -/
private def exampleModel : GenerativeWorld (Fin 3) 2 where
  rate := 1
  rate_pos := one_pos
  sender := 0
  host := ![1, 2]
  device := id
  device_idem := fun _ => rfl
  device_host := fun _ => rfl
  shape := 2
  shape_pos := two_pos
  blockSize := 1
  blockSize_pos := one_pos
  lead := 1 / 2
  lead_pos := by norm_num
  targetLatency := 3
  targetLatency_nonneg := by norm_num

/-- The example's member: round trips of one second, no pauses, no wander,
no spread of the clocks' mean rates and exact timestamps. -/
private def exampleMember : Member (Fin 3) 2 where
  roundTrip := fun _ _ => 1
  roundTrip_pos := fun _ _ => one_pos
  roundTrip_symm := fun _ _ => rfl
  linkPauseRate := fun _ _ => 0
  linkPauseRate_nonneg := fun _ _ => le_rfl
  linkPauseLength := fun _ _ => Measure.dirac 1
  linkPauseLength_prob := fun _ _ => inferInstance
  linkPauseLength_pos := fun _ _ => by simp
  linkPauseLength_mean := fun _ _ => integrable_dirac eNorm_lt_top
  linkLoad_lt_one := fun _ _ => by simp
  hostPauseRate := fun _ => 0
  hostPauseRate_nonneg := fun _ => le_rfl
  hostPauseLength := fun _ => Measure.dirac 1
  hostPauseLength_prob := fun _ => inferInstance
  hostPauseLength_pos := fun _ => by simp
  hostPauseLength_mean := fun _ => integrable_dirac eNorm_lt_top
  hostLoad_lt_one := fun _ => by simp
  rateSpread := 0
  rateSpread_nonneg := le_rfl
  wanderSize := fun _ => 0
  wanderSize_nonneg := fun _ => le_rfl
  wanderTime := fun _ => 1
  wanderTime_pos := fun _ => one_pos
  deviceWanderSize := fun _ => 0
  deviceWanderSize_nonneg := fun _ => le_rfl
  deviceWanderTime := fun _ => 1
  deviceWanderTime_pos := fun _ => one_pos
  reportSize := fun _ => 0
  reportSize_nonneg := fun _ => le_rfl
  reportTime := fun _ => 1
  reportTime_pos := fun _ => one_pos
  offsetRange := 1
  offsetRange_pos := one_pos
  captureStart := 0
  speakerStart := fun _ => 1

/-- The example's configuration: the sender sends the stream to both
speakers' hosts, each message once, and a host sends a clock query at most
once a second. -/
private def exampleParams : FixedDelay.Params (Fin 3) where
  sender := 0
  speakers := [1, 2]
  rate := 1
  latency := 3
  copies := 1
  period := 1
  slew := 1 / 2

/-- **The conditions of `playsAtLatencies` can be met.** There are a model, a
member, a world with constant rates and a configuration of the controller,
with the two-exchange and two-report estimators and the level held at three
seconds, that satisfy the conditions of the theorem; the controller
therefore plays at exact latencies in that world. In the example every clock
runs at the rate of true time, so it shows that the conditions are
consistent, and not that they hold in a world whose rates differ. -/
theorem playsAtLatencies_example :
    ∃ (m : GenerativeWorld (Fin 3) 2) (f : Member (Fin 3) 2) (d : Draw (Fin 3) 2)
      (w : World (Fin 3) 2) (p : FixedDelay.Params (Fin 3)) (K : ℕ),
      ConstantDelays m f d w ∧
        w.PlaysAtLatencies
          ((solution p twoExchanges twoReports (constantLevel 3) :
            Solution (Fin 3) 2 Payload).plays w 1)
          (fun r => 3 / Real.exp (d.logRate m.sender)
            + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
              - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) K := by
  have hex : ∀ h : Fin 3, h = exampleModel.sender ∨ ∃ r, exampleModel.host r = h := by
    intro h
    fin_cases h
    · exact Or.inl rfl
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
  have hnos : ∀ r, exampleModel.host r ≠ exampleModel.sender := by
    intro r
    fin_cases r
    · show (1 : Fin 3) ≠ 0
      decide
    · show (2 : Fin 3) ≠ 0
      decide
  have hspeakers : ∀ r, exampleModel.host r ∈ exampleParams.speakers := by
    intro r
    fin_cases r
    · show (1 : Fin 3) ∈ [1, 2]
      decide
    · show (2 : Fin 3) ∈ [1, 2]
      decide
  have hnodup : exampleParams.speakers.Nodup := by
    show ([1, 2] : List (Fin 3)).Nodup
    decide
  obtain ⟨y, hy⟩ : ∃ y : Component (Fin 3) 2 → ℝ, y = fun _ => 1 / 2 := ⟨_, rfl⟩
  have hS : ConstantDelays exampleModel exampleMember (canonicalDraw y)
      (canonicalWorld exampleModel exampleMember hex y) :=
    { builds := canonicalWorld_builds exampleModel exampleMember hex y
      no_wander := fun _ _ => rfl
      no_deviceWander := fun _ _ => rfl
      no_reportError := fun _ _ => rfl
      no_linkPauses := fun _ _ _ _ => rfl
      no_hostPauses := fun _ _ _ => rfl
      delay_pos := fun i j =>
        mul_pos (canonicalDraw_split_mem y i j).1 (exampleMember.roundTrip_pos i j) }
  have hrates : ∀ h, |Real.exp ((canonicalDraw y).logRate h) - 1| ≤ (0 : ℝ) := fun h => by
    simp [canonicalDraw]
  have hdevices : ∀ x, |Real.exp ((canonicalDraw y).deviceLogRate x) - 1| ≤ (0 : ℝ) :=
    fun x => by simp [canonicalDraw]
  obtain ⟨K, hK⟩ := playsAtLatencies exampleParams hS le_rfl (by norm_num) hrates hdevices 1
    twoExchanges_exact twoReports_exact 3 rfl hnodup Nat.one_pos zero_le_one hnos hspeakers
    (fun r => by simp [canonicalDraw])
    (fun r => by
      have hsw := canonicalDraw_split_swap y exampleModel.sender (exampleModel.host r)
      show ((((1 : ℕ) : ℝ) + 2 * (((1 : ℕ) : ℝ) - 1)) / 1 + 1 / 2) / (1 - 0)
          + ((canonicalDraw y).split exampleModel.sender (exampleModel.host r) * 1
            + (canonicalDraw y).split (exampleModel.host r) exampleModel.sender * 1) / 2
        < 3 / (1 + 0)
      norm_num
      linarith)
  exact ⟨exampleModel, exampleMember, canonicalDraw y, canonicalWorld exampleModel
    exampleMember hex y, exampleParams, K, hS, hK⟩

end Example

end Unisono.Solutions.Controller
