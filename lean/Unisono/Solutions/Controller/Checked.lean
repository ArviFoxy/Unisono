/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.EstimateStep

/-!
# The error of a host's estimate between two bounds

A host of the controller with the timing rules (`timedRules`) keeps its
estimate of the sender's clock only where two checks hold
(`checkedReading`). What the block check says about the block that covers
the estimate is part of `timed_chosen`. This file states what the interval
check says, in the run of the controller in every world.

* `ruled_exchange`: **every clock exchange in a host's view is a true
  exchange.** The host sent the query at some true time, the network
  delivered it to the sender at a later true time, at which the sender's
  clock read what the exchange holds, and the network delivered the answer
  to the host at a still later true time, before every request that the run
  has not yet handled. This holds for any rules.
* `timed_reading_upper`: **the estimate is not too low.** When a host has an
  estimate `s` for an output sample at a request, there is a clock exchange
  whose query the host sent at most `exchangeWindow` before the request, on
  its own clock, such that the reading of the sender's clock when the query
  arrived, moved on by the host's slope times the time on the host's clock
  from the sending of the query to the reading that the host expects when
  the output sample leaves, is at most `s` plus half of the round trip in
  use plus `intervalSlack`.

* `timed_reading_lower`: **the estimate is not too high.** When a host has
  an estimate `s` at a request, one of the arrivals that it uses, of a block
  that arrived at a true time `tb'` before the request, bounds the reading
  of the sender's clock at any true time `o` minus `s` from below: by the
  drift from `tb'` to `o` (`World.drift`), plus the slope times the error of
  the expected output time, minus half of the round trip in use.
* `timed_chosen_bounds`: **the error of the estimate lies between two
  bounds.** `World.drift h sl a o` is how far the sender's clock ran ahead,
  from the true time `a` to the true time `o`, of a clock that advances by
  `sl` per second of the clock of host `h`. When a host chooses a position
  with the estimate `s`, then for every true time `o` the reading of the
  sender's clock at `o` minus `s` is
  at least the drift since the arrival of the block that the estimate rests
  on, plus the slope times the error of the expected output time, minus
  half of the round trip in use; and
  at most the drift since the host sent the query of the confirming
  exchange, plus the slope times the same error, plus half of the round
  trip in use, plus `intervalSlack`.
  The first bound holds because a block arrives after it was sent, the
  second because a query arrives after it was sent.

With `o` the true time at which the output sample leaves, the two bounds
enclose the error of the host's estimate of the sender's clock. Nothing is
assumed about clocks, delays or pauses.

Not proved here: any bound on the drift or on the error of the expected
output time.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- **Every clock exchange in a host's view is a true exchange.** In the run
of the controller with any rules in any world, for an exchange in the view
of host `h` there are true times `s₁`, `s₂` and `t₃` such that: the host's
clock read `sent` at `s₁`; the network delivered a message from the host,
sent at `s₁`, to the sender at `s₂`; the sender's clock read `received` at
`s₂`; the network delivered a message from the sender, sent at `s₂`, to the
host at `t₃`; the host's clock read `arrived` at `t₃`; and `t₃` is before
every request that the run has not yet handled. -/
theorem ruled_exchange (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)
    (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ} {h : H} {x : Exchange}
    (hx : x ∈ exchangesOf
      (((ruled p rules : Solution H R Payload).states w lookahead n).views h)) :
    ∃ s₁ s₂ t₃ : Time, x.sent = (w.clock h).read s₁
      ∧ x.received = (w.clock w.sender).read s₂
      ∧ x.arrived = (w.clock h).read t₃
      ∧ (∃ q, w.network.deliver h w.sender s₁ q = some s₂)
      ∧ (∃ q, w.network.deliver w.sender h s₂ q = some t₃)
      ∧ ∀ r : Fin R, t₃ < (w.speaker r).asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r) := by
  have hmore := ruled_sendsMore (R := R) p rules
  rw [exchangesOf_eq, Solution.views_forget w Payload.plain lookahead hmore n h] at hx
  obtain ⟨e, he, i, F, hobs, hread⟩ := mem_plainExchangesOf hx
  obtain ⟨j, hj, t, obs, hhj, rfl⟩ :=
    Solution.handled_of_mem_views w (FixedDelay.solution p) lookahead he
  simp only at hobs hread
  subst hobs
  obtain ⟨msg, hm, hdest, harr, -, hcont, -⟩ :=
    Solution.handled_received w (FixedDelay.solution p) lookahead hhj
  have hO := FixedDelay.origin_inFlight p w lookahead hsender j msg hm
  unfold FixedDelay.Origin at hO
  simp only [hcont] at hO
  obtain ⟨s₁, s₂, q, q', -, hs₁, hs₂, hdl₁, hdl₂⟩ := hO
  rw [hdest] at hs₁ hdl₁ hdl₂
  rw [harr] at hdl₂
  refine ⟨s₁, s₂, t, hs₁, hs₂, hread.symm, ⟨q, hdl₁⟩, ⟨q', hdl₂⟩, fun r => ?_⟩
  rw [Solution.askedNext_forget w Payload.plain lookahead hmore n]
  exact Solution.received_lt_asked _ w lookahead hj.le hhj r

omit [DecidableEq H] in
/-- A request adds no clock exchange to a view. -/
theorem exchangesOf_append_asked (l : List (Event H R Payload)) (reading : ℝ) (r : Fin R)
    (outputs : List ℕ) (stamp : ℝ) :
    exchangesOf (l ++ [⟨reading, .asked r outputs stamp⟩]) = exchangesOf l := by
  simp [exchangesOf, List.filterMap_append]

/-- **The estimate is not too low.** Take the controller with the timing
rules, any settings and any level rule, in any world. Let speaker `r` be on
a host other than the sender's, and let the host have the estimate `s` for
output sample `k` at the step that handles the request of block `β`. Then
there are true times `s₁`, `s₂` and `t₃` such that:

* the network delivered a message from the host, sent at `s₁`, to the
  sender at `s₂`, and a message from the sender, sent at `s₂`, to the host
  at `t₃`, before the request;
* the host's clock advanced by at most `exchangeWindow` from `s₁` to the
  request;
* the reading of the sender's clock at `s₂`, plus the host's slope times
  the time on the host's clock from `s₁` to the reading that the host
  expects when the output sample leaves (`outputAt`), is at most `s` plus
  half of the round trip in use plus `intervalSlack`. -/
theorem timed_reading_upper (p : FixedDelay.Params H) (w : World H R) (t : TimingSettings)
    (level : LevelRule H R) (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ}
    {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ} {s : ℝ}
    (hE : earliest (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w
          lookahead n).key w)
        ((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead n).due
      = some (.asked r β))
    (hs : (timedRules w.sender t level).reading (w.host r)
        (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead
          n).views (w.host r) ++ [w.askedEvent r β]) r k = some s) :
    ∃ s₁ s₂ t₃ : Time,
      (∃ q, w.network.deliver (w.host r) w.sender s₁ q = some s₂)
      ∧ (∃ q, w.network.deliver w.sender (w.host r) s₂ q = some t₃)
      ∧ t₃ < (w.speaker r).asked β
      ∧ requestReading w r β - (w.clock (w.host r)).read s₁ ≤ t.exchangeWindow
      ∧ (w.clock w.sender).read s₂
          + arrivalSlope t (((ruled p (timedRules w.sender t level) :
                Solution H R Payload).states w lookahead n).views (w.host r)
              ++ [w.askedEvent r β])
            * (outputAt t w r β k - (w.clock (w.host r)).read s₁)
        ≤ s + halfTrip t (((ruled p (timedRules w.sender t level) :
                Solution H R Payload).states w lookahead n).views (w.host r)
              ++ [w.askedEvent r β])
          + t.intervalSlack := by
  obtain ⟨hs', hchecks⟩ := checkedReading_eq_some.mp hs
  obtain ⟨⟨x, hxr, v, hv, hle⟩, -⟩ := hchecks.resolve_left hr
  obtain ⟨e, he, hx, hwin⟩ := mem_recentExchanges.mp hxr
  have he' : e = w.askedEvent r β := by
    rw [List.getLast?_concat] at he
    exact (Option.some.inj he).symm
  have hx' : x ∈ exchangesOf (((ruled p (timedRules w.sender t level) :
      Solution H R Payload).states w lookahead n).views (w.host r)) := by
    rw [← exchangesOf_append_asked _ ((w.clock (w.host r)).read ((w.speaker r).asked β)) r
      ((w.speaker r).block β) ((w.speaker r).reported β)]
    exact hx
  obtain ⟨s₁, s₂, t₃, e1, e2, -, hq1, hq2, hlt⟩ :=
    ruled_exchange p (timedRules w.sender t level) w hsender lookahead hx'
  have hnext := Solution.askedNext_of_earliest _ w lookahead hE
  refine ⟨s₁, s₂, t₃, hq1, hq2, ?_, ?_, ?_⟩
  · rw [← hnext]
    exact hlt r
  · rw [he', e1] at hwin
    exact hwin
  · unfold envelopeReading at hs'
    rw [ite_eq_right hr] at hs'
    have henv := envelope_add (arrivalSlope t (((ruled p (timedRules w.sender t level) :
        Solution H R Payload).states w lookahead n).views (w.host r) ++ [w.askedEvent r β])) 0
      (requestOutput t (((ruled p (timedRules w.sender t level) :
        Solution H R Payload).states w lookahead n).views (w.host r) ++ [w.askedEvent r β]) r k)
      (windowArrivals t (((ruled p (timedRules w.sender t level) :
        Solution H R Payload).states w lookahead n).views (w.host r) ++ [w.askedEvent r β]))
    rw [zero_add, hv, Option.map_some] at henv
    have hs'' : (some (v + arrivalSlope t (((ruled p (timedRules w.sender t level) :
          Solution H R Payload).states w lookahead n).views (w.host r) ++ [w.askedEvent r β])
        * requestOutput t (((ruled p (timedRules w.sender t level) :
          Solution H R Payload).states w lookahead n).views (w.host r) ++ [w.askedEvent r β])
          r k) : Option ℝ).map
        (· + halfTrip t (((ruled p (timedRules w.sender t level) :
          Solution H R Payload).states w lookahead n).views (w.host r) ++ [w.askedEvent r β]))
        = some s := by
      rw [← henv]
      exact hs'
    rw [Option.map_some] at hs''
    have hs3 := Option.some.inj hs''
    rw [requestOutput_eq (ruled p (timedRules w.sender t level)) w lookahead t hE k] at hs3
    rw [e1, e2] at hle
    rw [← hs3]
    linarith

/-- How far the sender's clock ran ahead, from the true time `a` to the true
time `o`, of a clock that advances by `sl` per second of the clock of host
`h`: the time on the sender's clock from `a` to `o`, minus `sl` times the
time on the clock of `h` from `a` to `o`. -/
def _root_.Unisono.Spec.World.drift (w : World H R) (h : H) (sl : ℝ) (a o : Time) : ℝ :=
  ((w.clock w.sender).read o - (w.clock w.sender).read a)
    - sl * ((w.clock h).read o - (w.clock h).read a)

/-- **The estimate is not too high.** Take the controller with the timing
rules, any settings and any level rule, in any world. Let speaker `r` be on
a host other than the sender's, and let the host have the estimate `s` for
output sample `k` at the step that handles the request of block `β`. Then
there are a block `b'` and a true time `tb'` before the request such that:
the network delivered the message of `b'` to the host at `tb'`; the pair of
the host's reading at `tb'` and the sender's reading at the handover of
`b'` is one of the arrivals that the estimate uses; and for every true time
`o`, the reading of the sender's clock at `o` minus `s` is at least the
drift from `tb'` to `o`, plus the slope times the reading of the host's
clock at `o` minus the reading that the host expects when the output sample
leaves, minus half of the round trip in use. -/
theorem timed_reading_lower (p : FixedDelay.Params H) (w : World H R) (t : TimingSettings)
    (level : LevelRule H R) (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ}
    {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ} {s : ℝ}
    (hE : earliest (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w
          lookahead n).key w)
        ((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead n).due
      = some (.asked r β))
    (hs : (timedRules w.sender t level).reading (w.host r)
        (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead
          n).views (w.host r) ++ [w.askedEvent r β]) r k = some s) :
    ∃ (b' : ℕ) (tb' : Time),
      ((w.clock (w.host r)).read tb', w.handedReading b')
          ∈ windowArrivals t (((ruled p (timedRules w.sender t level) :
              Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r β])
      ∧ (∃ q, w.network.deliver w.sender (w.host r) (w.source.handed b') q = some tb')
      ∧ tb' < (w.speaker r).asked β
      ∧ ∀ o : Time,
          w.drift (w.host r)
                (arrivalSlope t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])) tb' o
              + arrivalSlope t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])
                * ((w.clock (w.host r)).read o - outputAt t w r β k)
              - halfTrip t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])
            ≤ (w.clock w.sender).read o - s := by
  obtain ⟨hs', -⟩ := checkedReading_eq_some.mp hs
  have hnext := Solution.askedNext_of_earliest _ w lookahead hE
  have happ : arrivalsOf (((ruled p (timedRules w.sender t level) :
        Solution H R Payload).states w lookahead n).views (w.host r) ++ [w.askedEvent r β])
      = arrivalsOf (((ruled p (timedRules w.sender t level) :
        Solution H R Payload).states w lookahead n).views (w.host r)) :=
    arrivalsOf_append_asked _ _ _ _ _
  have hsub : ∀ a ∈ (timingParts t : ClockParts H R).arrivals
        (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead
          n).views (w.host r) ++ [w.askedEvent r β]),
      a ∈ arrivalsOf (((ruled p (timedRules w.sender t level) :
        Solution H R Payload).states w lookahead n).views (w.host r)) := by
    intro a ha
    rw [← happ]
    exact mem_arrivalsOf_of_window t ha
  obtain ⟨b', tb', hmem, ⟨q', hq'⟩, hlt', herr⟩ :=
    exists_reading_eq p (timedRules w.sender t level) w (kn := t.knots) rfl hsender
      lookahead hr (timingParts t) hsub hs'
  have ho := requestOutput_eq (ruled p (timedRules w.sender t level)) w lookahead t hE k
  refine ⟨b', tb', hmem, ⟨q', hq'⟩, ?_, fun o => ?_⟩
  · rw [← hnext]
    exact hlt' r
  · have h1 : w.handedReading b' ≤ (w.clock w.sender).read tb' :=
      (w.clock w.sender).strictMono.monotone (w.network.after _ _ _ _ _ hq').le
    have h2 : (w.clock w.sender).read o - s
        = ((w.clock w.sender).read o - w.handedReading b')
          - arrivalSlope t (((ruled p (timedRules w.sender t level) :
                Solution H R Payload).states w lookahead n).views (w.host r)
              ++ [w.askedEvent r β])
            * (outputAt t w r β k - (w.clock (w.host r)).read tb')
          - halfTrip t (((ruled p (timedRules w.sender t level) :
                Solution H R Payload).states w lookahead n).views (w.host r)
              ++ [w.askedEvent r β]) := by
      rw [herr o, ← ho]
      rfl
    unfold World.drift
    nlinarith [h1, h2]

/-- **The error of a host's estimate lies between two bounds.** Take the
controller with the timing rules, any settings and any level rule, in any
world. Let speaker `r` be on a host other than the sender's, and let the
host choose the position `x` for output sample `k` at the step that handles
the request of block `β`. Then there are an estimate `s`, a block `b`, a
block `b'` that arrived at the true time `tb'` before the request, and a
clock exchange whose query the host sent at `s₁`, at most `exchangeWindow`
before the request on its own clock, and whose answer arrived before the
request, such that:

* **The schedule.** The coordinate `x + 1` lies among those of block `b`,
  and the value of the schedule of the knots at `x + 1` plus the announced
  level of `x + 1` is `s`.
* **The block check.** The time by which the knot of `b` is later than its
  input, plus the level announced for the right end of `b`, lies between
  `levelLow` and `levelHigh` within `scheduleSlack`.
* **The error.** For every true time `o`, the reading of the sender's clock
  at `o` minus `s` is at least the drift from `tb'` to `o`, plus the slope
  times the reading of the host's clock at `o` minus the reading that the
  host expects when the output sample leaves, minus half of the round trip
  in use; and at most the drift from `s₁` to `o`, plus the same second term,
  plus half of the round trip in use, plus `intervalSlack`. -/
theorem timed_chosen_bounds (p : FixedDelay.Params H) (w : World H R) (t : TimingSettings)
    (level : LevelRule H R) (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ}
    {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ} {x : ℝ}
    (hE : earliest (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w
          lookahead n).key w)
        ((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead n).due
      = some (.asked r β))
    (hx : (ruled p (timedRules w.sender t level) : Solution H R Payload).chosenAt w lookahead n
      r β k = some x) :
    ∃ (s : ℝ) (b b' : ℕ) (tb' s₁ s₂ t₃ : Time),
      (w.source.first b : ℝ) ≤ x + 1 ∧ x + 1 < w.source.first b + w.blockLength b
      ∧ w.knotTime t.knots b (x + 1)
          + (((timedRules w.sender t level).announced p w lookahead b).1
            + (x + 1 - w.source.first b)
              * ((timedRules w.sender t level).announced p w lookahead b).2) = s
      ∧ t.levelLow - t.scheduleSlack
          ≤ w.knot t.knots b - w.knotInput t.knots b
            + (((timedRules w.sender t level).announced p w lookahead b).1
              + w.blockLength b * ((timedRules w.sender t level).announced p w lookahead b).2)
      ∧ w.knot t.knots b - w.knotInput t.knots b
            + (((timedRules w.sender t level).announced p w lookahead b).1
              + w.blockLength b * ((timedRules w.sender t level).announced p w lookahead b).2)
          ≤ t.levelHigh + t.scheduleSlack
      ∧ (∃ q, w.network.deliver w.sender (w.host r) (w.source.handed b') q = some tb')
      ∧ tb' < (w.speaker r).asked β
      ∧ (∃ q, w.network.deliver (w.host r) w.sender s₁ q = some s₂)
      ∧ (∃ q, w.network.deliver w.sender (w.host r) s₂ q = some t₃)
      ∧ t₃ < (w.speaker r).asked β
      ∧ requestReading w r β - (w.clock (w.host r)).read s₁ ≤ t.exchangeWindow
      ∧ ∀ o : Time,
          w.drift (w.host r)
                (arrivalSlope t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])) tb' o
              + arrivalSlope t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])
                * ((w.clock (w.host r)).read o - outputAt t w r β k)
              - halfTrip t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])
            ≤ (w.clock w.sender).read o - s
          ∧ (w.clock w.sender).read o - s
            ≤ w.drift (w.host r)
                (arrivalSlope t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])) s₁ o
              + arrivalSlope t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])
                * ((w.clock (w.host r)).read o - outputAt t w r β k)
              + halfTrip t (((ruled p (timedRules w.sender t level) :
                    Solution H R Payload).states w lookahead n).views (w.host r)
                  ++ [w.askedEvent r β])
              + t.intervalSlack := by
  obtain ⟨s, b, tb, b', tb', hs0, -, -, hlo, hhi, -, heq, ⟨q', hq'⟩, hlt', herr, hb1, hb2⟩ :=
    timed_chosen p w t level hsender lookahead hr hE hx
  obtain ⟨s₁, s₂, t₃, ⟨q₁, hq1⟩, hq2, hlt3, hwin, hup⟩ :=
    timed_reading_upper p w t level hsender lookahead hr hE hs0
  refine ⟨s, b, b', tb', s₁, s₂, t₃, hlo, hhi, heq, hb1, hb2, ⟨q', hq'⟩, hlt', ⟨q₁, hq1⟩, hq2,
    hlt3, hwin, fun o => ⟨?_, ?_⟩⟩
  · have h1 : w.handedReading b' ≤ (w.clock w.sender).read tb' :=
      (w.clock w.sender).strictMono.monotone (w.network.after _ _ _ _ _ hq').le
    have h2 := herr o
    unfold World.drift
    nlinarith [h1, h2]
  · have h1 : (w.clock w.sender).read s₁ ≤ (w.clock w.sender).read s₂ :=
      (w.clock w.sender).strictMono.monotone (w.network.after _ _ _ _ _ hq1).le
    unfold World.drift
    nlinarith [h1, hup]

end Unisono.Solutions.Controller
