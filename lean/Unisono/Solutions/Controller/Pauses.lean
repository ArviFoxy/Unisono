/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.HeldLevel

/-!
# The controller's clock estimate when links and hosts pause

A pause of a link or of a host delays a clock query or its answer, so a
clock exchange that a pause delayed gives a wrong sample of the sender's
clock. A pause can only add to a delay. So, when the clocks run at constant
rates:

* the round trip of every clock exchange, on the querying host's clock, is
  at least the rate of that clock times the least round-trip time of the
  pair (`undelayedRoundTrip`), and an exchange with exactly that round trip
  was not delayed in either direction and lies on the lines of the undelayed
  exchanges (`exchange_roundTrip`);
* once a host's view holds two exchanges that were not delayed
  (`TwoUndelayed`), every estimator that is exact from the exchanges of
  least round trip returns the line of the undelayed exchanges from then on
  (`clockLineFrom_of_undelayed`), whatever pauses come later.

**Theorem** (`plays_under_pauses`). In a world whose clocks run at constant
rates, with exact timestamps and with pauses of links and of hosts, the
controller with the least-round-trip estimator holds the level at `L`. Once
two clock exchanges of a speaker's host were not delayed, from some output
sample on each output sample of the speaker plays the position that is due,
captured the latency before the sample leaves, if the message of the capture
block it needs took less than the sample's margin, and plays nothing of the
source otherwise.

Whether two clock exchanges of a host escape every pause is a property of
the outcome. It holds in almost every outcome of every random world of a
member with steady clocks (`ae_twoUndelayed` in
`Unisono.Solutions.Controller.Undelayed`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} (p : FixedDelay.Params H)

/-- The round trip, on the clock of host `h`, of a clock exchange with the
sender that no pause delays: the rate of the clock of `h` times the least
round-trip time of the pair. -/
def undelayedRoundTrip (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (h : H) : ℝ :=
  Real.exp (d.logRate h)
    * (d.split h m.sender * f.roundTrip h m.sender
      + d.split m.sender h * f.roundTrip m.sender h)

/-- At step `n` of the run, the view of host `h` holds two clock exchanges
that no pause delayed, whose queries were sent at different readings. -/
def TwoUndelayed (σ : Solution H R Payload) (w : World H R) (lookahead : ℕ+)
    (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (h : H) (n : ℕ) : Prop :=
  ∃ x ∈ exchangesOf ((σ.states w lookahead n).views h),
    ∃ x' ∈ exchangesOf ((σ.states w lookahead n).views h),
      x.roundTrip = undelayedRoundTrip m f d h ∧ x'.roundTrip = undelayedRoundTrip m f d h
        ∧ x.sent ≠ x'.sent

/-- **A pause can only lengthen the round trip of a clock exchange.** In a
world whose clocks run at constant rates, the round trip of every clock
exchange in a host's view is at least that of an undelayed exchange. An
exchange with exactly that round trip was delayed in neither direction: the
sender's reading in it lies on the two lines of the undelayed exchanges. -/
theorem exchange_roundTrip (hS : ConstantRates m f d w) (lookahead : ℕ+)
    (clockEst : ClockEstimator) (deviceEst : DeviceEstimator) (levelRule : LevelRule H R)
    (hps : p.sender = m.sender) {n : ℕ} {h : H} {x : Exchange}
    (hx : x ∈ exchangesOf
      (((solution p clockEst deviceEst levelRule : Solution H R Payload).states w lookahead
        n).views h)) :
    undelayedRoundTrip m f d h ≤ x.roundTrip
      ∧ (x.roundTrip = undelayedRoundTrip m f d h →
        x.received
            = (d.offset m.sender
                - Real.exp (d.logRate m.sender) / Real.exp (d.logRate h) * d.offset h
                + Real.exp (d.logRate m.sender) * (d.split h m.sender * f.roundTrip h m.sender))
              + Real.exp (d.logRate m.sender) / Real.exp (d.logRate h) * x.sent
          ∧ x.received
            = (d.offset m.sender
                - Real.exp (d.logRate m.sender) / Real.exp (d.logRate h) * d.offset h
                - Real.exp (d.logRate m.sender) * (d.split m.sender h * f.roundTrip m.sender h))
              + Real.exp (d.logRate m.sender) / Real.exp (d.logRate h) * x.arrived) := by
  have hmore := sendsMore (R := R) p clockEst deviceEst levelRule
  have hsend : w.sender = m.sender := hS.builds.sender_eq
  have hsender : p.sender = w.sender := hps.trans hsend.symm
  rw [exchangesOf_eq, Solution.views_forget w Payload.plain lookahead hmore n h] at hx
  obtain ⟨s₁, e1, e2, e3⟩ := exchange_of_built p hS.builds lookahead hsender hx
  rw [hS.clock] at e1 e3
  rw [hS.clock, hsend] at e2
  rw [hsend] at e3
  have hle₁ := hS.builds.le_arrival h m.sender s₁
  have hle₂ := hS.builds.le_arrival m.sender h (d.arrival f h m.sender s₁)
  have hrh := Real.exp_pos (d.logRate h)
  have hrt : x.roundTrip = Real.exp (d.logRate h)
      * (d.arrival f m.sender h (d.arrival f h m.sender s₁) - s₁) := by
    unfold Exchange.roundTrip
    rw [e1, e3]
    ring
  constructor
  · rw [hrt, undelayedRoundTrip]
    exact mul_le_mul_of_nonneg_left (by linarith) hrh.le
  · intro heq
    rw [hrt, undelayedRoundTrip] at heq
    have h3 := mul_left_cancel₀ hrh.ne' heq
    have h4 : d.arrival f h m.sender s₁ = s₁ + d.split h m.sender * f.roundTrip h m.sender := by
      linarith
    have h5 : d.arrival f m.sender h (d.arrival f h m.sender s₁)
        = s₁ + d.split h m.sender * f.roundTrip h m.sender
          + d.split m.sender h * f.roundTrip m.sender h := by linarith
    rw [e1, e2, e3, h5, h4]
    exact exchange_lines hrh.ne'

/-- **Once two clock exchanges were not delayed, the estimate of the
sender's clock is the line of the undelayed exchanges.** In a world whose
clocks run at constant rates, suppose that at step `n₀` the view of host `h`
holds two clock exchanges that no pause delayed. Then every estimator that
is exact from the exchanges of least round trip returns the line of the
undelayed exchanges at every step whose event occurs after that of `n₀`. -/
theorem clockLineFrom_of_undelayed (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {clockEst : ClockEstimator} (hclock : clockEst.ExactFromLeast)
    (deviceEst : DeviceEstimator) (levelRule : LevelRule H R) (hps : p.sender = m.sender)
    {h : H} {n₀ : ℕ}
    (hund : TwoUndelayed (solution p clockEst deviceEst levelRule) w lookahead m f d h n₀) :
    ClockLineFrom (solution p clockEst deviceEst levelRule) w lookahead clockEst h
      (exchangeLine m f d h)
      ((solution p clockEst deviceEst levelRule : Solution H R Payload).eventTime w lookahead
        n₀) := by
  intro n hn
  have hn₀ : n₀ ≤ n := by
    by_contra hcon
    have := Solution.eventTime_mono w
      (solution p clockEst deviceEst levelRule : Solution H R Payload) lookahead
      (not_le.mp hcon).le
    linarith
  obtain ⟨l, hl, -⟩ := Solution.views_append w
    (solution p clockEst deviceEst levelRule : Solution H R Payload) lookahead hn₀ h
  obtain ⟨x, hx, x', hx', hτ, hτ', hne⟩ := hund
  have hsub : ∀ y ∈ exchangesOf
        (((solution p clockEst deviceEst levelRule : Solution H R Payload).states w lookahead
          n₀).views h),
      y ∈ exchangesOf
        (((solution p clockEst deviceEst levelRule : Solution H R Payload).states w lookahead
          n).views h) := by
    intro y hy
    rw [hl]
    unfold exchangesOf
    rw [List.filterMap_append]
    exact List.mem_append_left _ hy
  have hgoal : exchangeLine m f d h
      = ⟨((d.offset m.sender
              - Real.exp (d.logRate m.sender) / Real.exp (d.logRate h) * d.offset h
              + Real.exp (d.logRate m.sender) * (d.split h m.sender * f.roundTrip h m.sender))
            + (d.offset m.sender
              - Real.exp (d.logRate m.sender) / Real.exp (d.logRate h) * d.offset h
              - Real.exp (d.logRate m.sender)
                * (d.split m.sender h * f.roundTrip m.sender h))) / 2,
          Real.exp (d.logRate m.sender) / Real.exp (d.logRate h)⟩ := by
    unfold exchangeLine
    congr 1
    ring
  rw [hgoal]
  exact hclock _ _ _ _ (undelayedRoundTrip m f d h)
    (fun y hy => (exchange_roundTrip p hS lookahead clockEst deviceEst levelRule hps hy).1)
    (fun y hy => (exchange_roundTrip p hS lookahead clockEst deviceEst levelRule hps hy).2)
    ⟨x, hsub x hx, x', hsub x' hx', hτ, hτ', hne⟩

/-- **What the controller plays when links and hosts pause.** Consider a
world whose clocks run at constant rates, with exact timestamps and with
pauses of links and of hosts, and a speaker `r` whose host is not the
sender's. The controller uses the least-round-trip estimator for the
sender's clock and the two-report estimator for the devices, and holds the
level at `L`. Suppose that at some step the view of the speaker's host holds
two clock exchanges that no pause delayed. Then, from some output sample on,
output sample `k` plays the position that is due, captured `latencyOf`
before the sample leaves, if the message of the capture block that the
sample needs took less than the sample's margin, and plays nothing of the
source otherwise. -/
theorem plays_under_pauses (hS : ConstantRates m f d w) (lookahead : ℕ+) (L : ℝ)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {n₀ : ℕ}
    (hund : TwoUndelayed (solution p leastRoundTrip twoReports (constantLevel L)) w lookahead
      m f d (m.host r) n₀) :
    ∃ K, ∀ k, K ≤ k →
      0 ≤ duePosition m f d w L r k ∧
      (solution p leastRoundTrip twoReports (constantLevel L) : Solution H R Payload).plays w
          lookahead r k
        = if blockDelay m f d w r (neededBlock m lookahead (duePosition m f d w L r k))
            < margin m f d w lookahead L r k
          then some (duePosition m f d w L r k) else none :=
  plays_eq_of_margin p hS lookahead twoReports_exact L hps hnodup hcopies r hnos hpsp
    (clockLineFrom_of_undelayed p hS lookahead leastRoundTrip_exactFromLeast twoReports
      (constantLevel L) hps hund)

end Unisono.Solutions.Controller
