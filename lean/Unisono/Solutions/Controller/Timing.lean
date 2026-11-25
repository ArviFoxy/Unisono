/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Envelope
public import Unisono.Solutions.Controller.SteppedLevel

/-!
# The controller's timing from what its hosts observe

The rules of the controller (`Rules`) for worlds in which clocks wander and
links pause. Every estimate is a function of a bounded stretch of what a
host has observed, so that an estimate recovers after any disturbance. A
host that pauses handles the events of its audio devices late. The capture
schedule keeps advancing through handovers that are handled together
(`knotStep`); the readings at requests are still taken as the times of the
requests.

* **The capture schedule** comes from the readings of the sender's clock at
  the handovers (`knotCapture`).
* **When output samples leave.** A playback device requests each block a
  told lead, on its own clock, before the block's first output sample
  leaves, and its host handles the request then, or later when it is busy.
  From the
  readings of its clock at the two newest requests the host takes the
  ratio of its own clock to the device's clock: the time on its own clock
  per second of the device's clock, kept within `slopeBound` of one
  (`deviceRatio`). The reading that it expects when output sample `k`
  leaves is the reading at the newest request plus that ratio times the
  device's time from the request to the sample (`requestOutput`). At a
  request of block `β` in the run of any solution in any world this is
  `outputAt`, a function of the world alone (`requestOutput_eq`).
* **The sender's clock** comes from the arrivals of blocks
  (`envelopeReading`), with these parts (`timingParts`):
  the arrivals of the blocks that arrived within `window`, on the host's
  clock, before the request, or the newest arrival if there is none
  (`windowArrivals`); the slope between the newest arrival and the newest one
  that is at least `baseline` older, kept within `slopeBound` of one
  (`arrivalSlope`); and half of the least round trip of the newest
  `exchanges` clock exchanges, cut to `tripCap` (`halfTrip`).
* **The need** that a host reports in a clock query (`timedNeed`): the
  largest need of the blocks that arrived since the host sent the newest
  query that has been answered. The need of a block is the level at which
  the block would have arrived just in time: the host's estimate of the
  sender's clock at the arrival, plus the lead and one playback block on
  the sender's clock, minus the schedule's time for the first position that
  can need the block, which lies `ahead` frames before the block.

`timedRules sender t level` puts these together, for any level rule.

Nothing is proved here about how good the estimates are.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Model.Descent

variable {H : Type} {R : ℕ}

/-- The settings of the controller's timing. -/
structure TimingSettings where
  /-- The nominal rate of the devices, in frames per second. -/
  rate : ℝ
  /-- The request lead, in seconds of a playback device's clock. -/
  lead : ℝ
  /-- The number of output samples of a playback block. -/
  blockSize : ℕ
  /-- An upper bound for the resampler's lookahead, in frames. -/
  ahead : ℝ
  /-- How far back from a request, on the host's clock, the arrivals that
  the estimate of the sender's clock uses reach. -/
  window : ℝ
  /-- The least time, on the host's clock, between the two arrivals from
  which the slope is taken. -/
  baseline : ℝ
  /-- The largest distance from one of the slope of the sender's clock
  against a host's clock, and of the ratio of a host's clock to a device's
  clock, as the hosts estimate them. -/
  slopeBound : ℝ
  /-- The number of clock exchanges from which the least round trip is
  taken. -/
  exchanges : ℕ
  /-- The largest round trip that is used. -/
  tripCap : ℝ

/-- The first output sample of the block that a request asks for. -/
def firstOutput (e : Event H R Payload) : ℕ :=
  match e.observation with
  | .asked _ outputs _ => outputs.headD 0
  | _ => 0

/-- The ratio of the host's clock to the clock of the device of speaker
`r`, from the two newest requests in a view: the time on the host's clock
from one request to the other, divided by the device's nominal time
between their first output samples, kept within `slopeBound` of one. It is
one while there is only one request. -/
def deviceRatio (t : TimingSettings) (r : Fin R) (view : List (Event H R Payload)) : ℝ :=
  match (requestsOf r view).reverse with
  | e :: e' :: _ => clampTo (1 - t.slopeBound) (1 + t.slopeBound)
      ((e.reading - e'.reading) * t.rate / ((firstOutput e : ℝ) - firstOutput e'))
  | _ => 1

/-- The reading of the host's clock that the host expects when output
sample `k` of speaker `r` leaves, from a view that ends with a request of
that speaker's device. -/
def requestOutput (t : TimingSettings) (view : List (Event H R Payload)) (r : Fin R) (k : ℕ) :
    ℝ :=
  match (requestsOf r view).reverse with
  | e :: _ => e.reading + (t.lead + ((k : ℝ) - firstOutput e) / t.rate) * deviceRatio t r view
  | [] => 0

/-- The slope of the sender's clock against the host's clock, from the
newest arrival in a view and the newest arrival that is at least `baseline`
older on the host's clock, kept within `slopeBound` of one. It is one while
there are no two such arrivals. -/
def arrivalSlope (t : TimingSettings) (view : List (Event H R Payload)) : ℝ :=
  match (arrivalsOf view).reverse with
  | a :: rest =>
      match rest.find? (fun a' => decide (a'.1 ≤ a.1 - t.baseline)) with
      | some a' => clampTo (1 - t.slopeBound) (1 + t.slopeBound) ((a.2 - a'.2) / (a.1 - a'.1))
      | none => 1
  | [] => 1

/-- Half of the least round trip of the newest `exchanges` clock exchanges
in a view, cut to between zero and `tripCap`. It is zero while there is no
exchange. -/
def halfTrip (t : TimingSettings) (view : List (Event H R Payload)) : ℝ :=
  match (((exchangesOf view).reverse.take t.exchanges).map Exchange.roundTrip).min? with
  | some ρ => clampTo 0 t.tripCap ρ / 2
  | none => 0

/-- The arrivals that the estimate uses, from a view that ends with a
request: those of the blocks that arrived at most `window` before the
request, on the host's clock, or the newest arrival if there is none. -/
def windowArrivals (t : TimingSettings) (view : List (Event H R Payload)) : List (ℝ × ℝ) :=
  match view.getLast? with
  | some e =>
      match (arrivalsOf view).filter (fun a => decide (e.reading - t.window ≤ a.1)) with
      | [] => (arrivalsOf view).getLast?.toList
      | a :: as => a :: as
  | none => []

/-- Every arrival that the estimate uses is an arrival of the view. -/
theorem mem_arrivalsOf_of_window (t : TimingSettings) {view : List (Event H R Payload)}
    {a : ℝ × ℝ} (ha : a ∈ windowArrivals t view) : a ∈ arrivalsOf view := by
  unfold windowArrivals at ha
  cases hlast : view.getLast? with
  | none => simp [hlast] at ha
  | some e =>
    simp only [hlast] at ha
    cases hfilter : (arrivalsOf view).filter (fun a => decide (e.reading - t.window ≤ a.1)) with
    | nil =>
      simp only [hfilter] at ha
      rw [Option.mem_toList] at ha
      exact List.mem_of_getLast? ha
    | cons a' as =>
      simp only [hfilter] at ha
      have : a ∈ (arrivalsOf view).filter (fun a => decide (e.reading - t.window ≤ a.1)) := by
        rw [hfilter]
        exact ha
      exact (List.mem_filter.mp this).1

/-- A request adds no arrival to a view. -/
theorem arrivalsOf_append_asked (l : List (Event H R Payload)) (reading : ℝ) (r : Fin R)
    (outputs : List ℕ) (stamp : ℝ) :
    arrivalsOf (l ++ [⟨reading, .asked r outputs stamp⟩]) = arrivalsOf l := by
  simp [arrivalsOf, List.filterMap_append]

/-- The parts of the estimate of the sender's clock, for the settings
`t`. -/
def timingParts (t : TimingSettings) : ClockParts H R :=
  ⟨requestOutput t, arrivalSlope t, halfTrip t, windowArrivals t⟩

/-- **The need that a clock query reports.** From a host's view that ends
with a request of the device of speaker `r`: the largest need of the blocks
that arrived since the host sent the newest clock query that has been
answered. The need of a block that arrived when the host's clock read `y`
is the host's estimate of the sender's clock at `y`, plus the lead and one
playback block on the sender's clock, minus the time that the block's header
gives to the position `ahead` frames before the block. There is none while
the host uses no arrival or no such block arrived. -/
def timedNeed (t : TimingSettings) : H → List (Event H R Payload) → Option ℝ := fun _ view =>
  match view.getLast? with
  | some e =>
      match e.observation with
      | .asked r _ _ =>
          match envelope (arrivalSlope t view) 0 (windowArrivals t view) with
          | some v =>
              (view.filterMap fun e' =>
                match e'.observation with
                | .received _ (.block _ _ capture period _ _) _ =>
                    if ((((exchangesOf view).map Exchange.sent).max?).map
                        fun s => decide (s ≤ e'.reading)).getD true then
                      some (v + arrivalSlope t view * e'.reading + halfTrip t view
                        + arrivalSlope t view * deviceRatio t r view
                          * (t.lead + t.blockSize / t.rate)
                        - (capture - (t.ahead - 1) * period))
                    else none
                | _ => none).max?
          | none => none
      | _ => none
  | none => none

/-- **The rules of the controller's timing**, for the sender's host, the
settings `t` and a level rule: the capture schedule from the knots, with the
nominal time from one frame to the next for the first block; the estimate of
the sender's clock from the arrivals of blocks; and positions counted one
frame back, as the schedule of the knots counts them. -/
def timedRules [DecidableEq H] (sender : H) (t : TimingSettings) (level : LevelRule H R) :
    Rules H R :=
  ⟨level, knotCapture (1 / t.rate), envelopeReading sender (timingParts t), 1⟩

/-! ## What the output schedule is, as a function of the world -/

/-- The reading of the clock of the host of speaker `r` when the speaker's
device requests block `β`. -/
def requestReading (w : World H R) (r : Fin R) (β : ℕ) : ℝ :=
  (w.clock (w.host r)).read ((w.speaker r).asked β)

/-- The ratio of its own clock to the device's clock that the host of
speaker `r` takes at the request of block `β`: one at the first request;
afterwards the time on the host's clock from the request before to this
one, divided by the device's nominal time between the first output
samples of the two blocks, kept within `slopeBound` of one. -/
def ratioAt (t : TimingSettings) (w : World H R) (r : Fin R) : ℕ → ℝ
  | 0 => 1
  | β + 1 => clampTo (1 - t.slopeBound) (1 + t.slopeBound)
      ((requestReading w r (β + 1) - requestReading w r β) * t.rate
        / (((w.speaker r).first (β + 1) : ℝ) - (w.speaker r).first β))

/-- The reading of its clock that the host of speaker `r` expects, at the
request of block `β`, when output sample `k` leaves. -/
def outputAt (t : TimingSettings) (w : World H R) (r : Fin R) (β k : ℕ) : ℝ :=
  requestReading w r β
    + (t.lead + ((k : ℝ) - (w.speaker r).first β) / t.rate) * ratioAt t w r β

/-- The first output sample of the request of block `b`. -/
theorem firstOutput_askedEvent (w : World H R) (r : Fin R) (b : ℕ) :
    firstOutput (w.askedEvent r b : Event H R Payload) = (w.speaker r).first b := by
  show ((w.speaker r).block b).headD 0 = _
  rw [List.headD_eq_head?_getD, PlaybackDevice.head?_block]
  rfl

variable [DecidableEq H]

/-- **At the request of block `β`, the host expects `outputAt`.** In the run
of every solution in every world, at the step that handles the request of
block `β` of speaker `r`, the reading that the host expects when output
sample `k` leaves is a function of the world: the reading of its clock at
the request, plus the ratio `ratioAt` times the device's nominal time from
the request to the output sample. -/
theorem requestOutput_eq (σ : Solution H R Payload) (w : World H R) (lookahead : ℕ+)
    (t : TimingSettings) {n : ℕ} {r : Fin R} {β : ℕ}
    (hE : earliest ((σ.states w lookahead n).key w) (σ.states w lookahead n).due
      = some (.asked r β)) (k : ℕ) :
    requestOutput t ((σ.states w lookahead n).views (w.host r) ++ [w.askedEvent r β]) r k
      = outputAt t w r β k := by
  have hreq := σ.requestsOf_request w lookahead hE
  unfold requestOutput deviceRatio
  rw [hreq]
  cases β with
  | zero =>
    simp only [zero_add, List.range_one, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append]
    rw [firstOutput_askedEvent]
    rfl
  | succ β =>
    rw [List.range_succ, List.range_succ, List.map_append, List.map_append,
      List.reverse_append, List.reverse_append]
    simp only [List.map_cons, List.map_nil, List.reverse_singleton, List.cons_append,
      List.nil_append]
    rw [firstOutput_askedEvent, firstOutput_askedEvent]
    rfl

/-- **What a host of the controller chooses, and the error of its estimate,
in every world.** Take the controller with the timing rules, any settings
and any level rule, in any world. Let speaker `r` be on a host other than
the sender's, and let the host choose the position `x` for output sample `k`
at the step that handles the request of block `β`. Then there are an
estimate `s`, a block `b` and a block `b'`, both arrived at the host before
the request, such that:

* **The schedule.** The coordinate `x + 1` lies among those of block `b`,
  and the value of the schedule of the knots at `x + 1` plus the announced
  level of `x + 1` is `s`.
* **The estimate.** For every true time `o`, the reading of the sender's
  clock at `o` minus `s` is: the time on the sender's clock from the
  handover of `b'` to `o`, minus the slope times the time on the host's
  clock from the arrival of `b'` to the reading that the host expects when
  the output sample leaves (`outputAt`), minus half of the round trip.

With `o` the true time at which the output sample leaves, the second
statement is the error of the host's estimate. -/
theorem timed_chosen (p : FixedDelay.Params H) (w : World H R) (t : TimingSettings)
    (level : LevelRule H R) (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ}
    {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ} {x : ℝ}
    (hE : earliest (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w
          lookahead n).key w)
        ((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead n).due
      = some (.asked r β))
    (hx : (ruled p (timedRules w.sender t level) : Solution H R Payload).chosenAt w lookahead n
      r β k = some x) :
    ∃ s b tb b' tb',
      (∃ q, w.network.deliver w.sender (w.host r) (w.source.handed b) q = some tb)
      ∧ tb < (w.speaker r).asked β
      ∧ (w.source.first b : ℝ) ≤ x + 1 ∧ x + 1 < w.source.first b + w.blockLength b
      ∧ 0 < w.knotPeriod (1 / t.rate) b
          + ((timedRules w.sender t level).announced p w lookahead b).2
      ∧ w.knotTime (1 / t.rate) b (x + 1)
          + (((timedRules w.sender t level).announced p w lookahead b).1
            + (x + 1 - w.source.first b)
              * ((timedRules w.sender t level).announced p w lookahead b).2) = s
      ∧ (∃ q, w.network.deliver w.sender (w.host r) (w.source.handed b') q = some tb')
      ∧ tb' < (w.speaker r).asked β
      ∧ ∀ o : Time, (w.clock w.sender).read o - s
          = ((w.clock w.sender).read o - w.handedReading b')
            - arrivalSlope t (((ruled p (timedRules w.sender t level) :
                  Solution H R Payload).states w lookahead n).views (w.host r)
                ++ [w.askedEvent r β])
              * (outputAt t w r β k - (w.clock (w.host r)).read tb')
            - halfTrip t (((ruled p (timedRules w.sender t level) :
                  Solution H R Payload).states w lookahead n).views (w.host r)
                ++ [w.askedEvent r β]) := by
  obtain ⟨s, b, tb, hs, hq, hlt, hlo, hhi, hpos, heq⟩ :=
    ruled_chosen_knots p (timedRules w.sender t level) w (nominal := 1 / t.rate) rfl hsender
      lookahead hr hx
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
  obtain ⟨b', tb', -, hq', hlt', herr⟩ :=
    exists_reading_eq p (timedRules w.sender t level) w (nominal := 1 / t.rate) rfl hsender
      lookahead hr (timingParts t) hsub hs
  have ho := requestOutput_eq (ruled p (timedRules w.sender t level)) w lookahead t hE k
  refine ⟨s, b, tb, b', tb', hq, ?_, hlo, hhi, hpos, heq, hq', ?_, fun o => ?_⟩
  · rw [← hnext]
    exact hlt r
  · rw [← hnext]
    exact hlt' r
  · rw [herr o, ← ho]
    rfl

end Unisono.Solutions.Controller
