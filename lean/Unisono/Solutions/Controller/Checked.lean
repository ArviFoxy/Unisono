/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.EstimateStep

/-!
# What the interval check says about the sender's clock

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

The sender's clock read less when the host sent the query than when the
query arrived. So the second statement bounds, from above, the reading of
the sender's clock when the output sample leaves minus the estimate, up to
the error of the slope over a time of at most `exchangeWindow` plus the
time from the request to the output sample. `timed_chosen` bounds the same
difference from below. Nothing is assumed about clocks, delays or pauses.

Not proved here: any bound on the error of the slope.
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
  obtain ⟨⟨e, he, x, hx, v, hwin, hv, hle⟩, -⟩ := hchecks.resolve_left hr
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

end Unisono.Solutions.Controller
