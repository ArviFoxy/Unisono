/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Targets
public import Unisono.Solutions.Controller.Timing

/-!
# The step of a host's estimate within a playback block

A host of the controller with the timing rules (`timedRules`) estimates the
reading of the sender's clock for every output sample of a playback block
from one view: its view when it handles the request of the block. Within the
block the estimate is therefore a line in the number of the output sample.

* `envelope_add`: moving the reading of the host's clock by `δ` moves the
  estimate from the arrivals by the slope times `δ`.
* `requestOutput_succ`: the reading that a host expects when an output
  sample leaves advances, from one output sample to the next, by the
  host's ratio of its own clock to the device's clock, divided by the
  nominal rate.
* `timed_estimate_succ`: **the step of the estimate.** For two consecutive
  output samples of one playback block for which the host has an estimate,
  the estimate for the second is the estimate for the first plus the host's
  slope times that ratio, divided by the nominal rate (`estimateStep`).
  This holds in the run of the controller in every world. The host has an
  estimate only where its two checks hold (`checkedReading`), so it may
  have one for one of the two output samples and none for the other.
* `abs_chosen_succ_sub_le`: so, in the setting `KnotSetting`, if the step
  of the estimate divided by the slope of every block of the schedule is
  within `v` of one, the position that the host chooses advances by one
  frame within `v` from one output sample of the block to the next.
* `stepOver_chosen_eq_zero`: for `v ≤ u` such a step of the target costs
  the follower nothing (`stepOver`).

Not proved here: how the estimate changes from one playback block to the
next, and when the slopes of the schedule are close to the step.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- Moving the reading `y` of the host's clock by `δ` moves the largest
value that the arrivals give by the slope times `δ`. -/
theorem envelope_add (s y δ : ℝ) :
    ∀ as : List (ℝ × ℝ), envelope s (y + δ) as = (envelope s y as).map (· + s * δ)
  | [] => rfl
  | a :: as => by
    unfold envelope
    rw [envelope_add s y δ as]
    cases envelope s y as with
    | none =>
      simp only [Option.map_none, Option.map_some]
      congr 1
      ring
    | some v =>
      simp only [Option.map_some]
      congr 1
      rw [← max_add_add_right]
      congr 1
      ring

/-- **The reading that a host expects when an output sample leaves
advances, from one output sample to the next, by the host's ratio of its own
clock to the device's clock, divided by the nominal rate**, in a view that
holds a request of the speaker's device. -/
theorem requestOutput_succ (t : TimingSettings) {view : List (Event H R Payload)} {r : Fin R}
    (h : requestsOf r view ≠ []) (k : ℕ) :
    requestOutput t view r (k + 1)
      = requestOutput t view r k + deviceRatio t r view / t.rate := by
  unfold requestOutput
  cases hrev : (requestsOf r view).reverse with
  | nil => exact absurd (List.reverse_eq_nil_iff.mp hrev) h
  | cons e rest =>
    simp only []
    push_cast
    ring

variable [DecidableEq H]

/-- **The estimate from the arrivals is a line in the number of the output
sample.** For a host other than the sender's, in a view that holds a request
of the speaker's device: the estimate for output sample `k + 1` is the
estimate for `k` plus the host's slope times its ratio of its own clock to
the device's clock, divided by the nominal rate. -/
theorem envelopeReading_succ (sender : H) (t : TimingSettings) {h : H}
    (hne : h ≠ sender) {view : List (Event H R Payload)} {r : Fin R}
    (hreq : requestsOf r view ≠ []) (k : ℕ) :
    envelopeReading sender (timingParts t) h view r (k + 1)
      = (envelopeReading sender (timingParts t) h view r k).map
        (· + arrivalSlope t view * (deviceRatio t r view / t.rate)) := by
  unfold envelopeReading
  rw [ite_eq_right hne, ite_eq_right hne]
  show (envelope (arrivalSlope t view) (requestOutput t view r (k + 1))
      (windowArrivals t view)).map (· + halfTrip t view) = _
  rw [requestOutput_succ t hreq k, envelope_add, Option.map_map]
  show _ = ((envelope (arrivalSlope t view) (requestOutput t view r k)
      (windowArrivals t view)).map (· + halfTrip t view)).map _
  rw [Option.map_map]
  congr 1
  funext v
  simp only [Function.comp_apply]
  ring

/-- **The estimate by which a host plays advances by the same step.** For a
host other than the sender's, in a view that holds a request of the
speaker's device: if the host has the estimate `s` for output sample `k`
and the estimate `s'` for `k + 1`, then `s'` is `s` plus the host's slope
times its ratio of its own clock to the device's clock, divided by the
nominal rate. -/
theorem timed_reading_succ (sender : H) (t : TimingSettings) (level : LevelRule H R) {h : H}
    (hne : h ≠ sender) {view : List (Event H R Payload)} {r : Fin R}
    (hreq : requestsOf r view ≠ []) {k : ℕ} {s s' : ℝ}
    (hs : (timedRules sender t level).reading h view r k = some s)
    (hs' : (timedRules sender t level).reading h view r (k + 1) = some s') :
    s' = s + arrivalSlope t view * (deviceRatio t r view / t.rate) := by
  have h1 := (checkedReading_eq_some.mp hs).1
  have h2 := (checkedReading_eq_some.mp hs').1
  rw [envelopeReading_succ sender t hne hreq k, h1, Option.map_some] at h2
  exact (Option.some.inj h2).symm

/-- By how much the estimate of the host of speaker `r` advances from one
output sample of playback block `β` to the next, in the run of the
controller with the timing rules: the host's slope times its ratio of its
own clock to the device's clock, both from its view at the request of the
block, divided by the nominal rate. -/
def estimateStep (p : FixedDelay.Params H) (w : World H R) (t : TimingSettings)
    (level : LevelRule H R) (lookahead : ℕ+) (r : Fin R) (β : ℕ) : ℝ :=
  arrivalSlope t
      ((ruled p (timedRules w.sender t level) : Solution H R Payload).requestView w lookahead
        r β)
    * (deviceRatio t r
        ((ruled p (timedRules w.sender t level) : Solution H R Payload).requestView w lookahead
          r β) / t.rate)

/-- **The step of the estimate within a playback block.** In the run of the
controller with the timing rules in any world, for a speaker on a host other
than the sender's: if output samples `k` and `k + 1` belong to the same
playback block and the host has the estimates `s` and `s'` for them, then
`s'` is `s` plus `estimateStep` of the block. -/
theorem timed_estimate_succ (p : FixedDelay.Params H) (w : World H R) (t : TimingSettings)
    (level : LevelRule H R) (lookahead : ℕ+) {r : Fin R} (hr : w.host r ≠ w.sender) {k : ℕ}
    (hblock : (w.speaker r).blockOf (k + 1) = (w.speaker r).blockOf k) {s s' : ℝ}
    (hs : (timedRules w.sender t level).estimate p w lookahead r k = some s)
    (hs' : (timedRules w.sender t level).estimate p w lookahead r (k + 1) = some s') :
    s' = s + estimateStep p w t level lookahead r ((w.speaker r).blockOf k) := by
  classical
  unfold Rules.estimate at hs hs'
  rw [hblock] at hs'
  unfold estimateStep
  by_cases hreq : requestsOf r
      ((ruled p (timedRules w.sender t level) : Solution H R Payload).requestView w lookahead r
        ((w.speaker r).blockOf k)) = []
  · -- The run never handles the request: the view is empty, and there is no estimate.
    have hview : (ruled p (timedRules w.sender t level) : Solution H R Payload).requestView w
        lookahead r ((w.speaker r).blockOf k) = [] := by
      unfold Solution.requestView at hreq ⊢
      split_ifs at hreq ⊢ with hex
      · rw [requestsOf_append] at hreq
        have h1 : requestsOf r [(w.askedEvent r ((w.speaker r).blockOf k) : Event H R Payload)]
            ≠ [] := by
          simp [requestsOf, World.askedEvent]
        exact absurd (List.append_eq_nil_iff.mp hreq).2 h1
      · rfl
    rw [hview] at hs
    have h1 := (checkedReading_eq_some.mp hs).1
    unfold envelopeReading at h1
    rw [ite_eq_right hr] at h1
    have h2 : (none : Option ℝ) = some s := h1
    exact absurd h2 (by simp)
  · exact timed_reading_succ w.sender t level hr hreq hs hs'

variable {p : FixedDelay.Params H} {w : World H R} {t : TimingSettings}
  {level : LevelRule H R} {A : H → H → Time → Time} {q : LevelSettings} {share : ℝ}

/-- **The chosen position advances regularly within a playback block when
the schedule's slopes are close to the step of the estimate.** In the
setting `KnotSetting` for the controller with the timing rules, let the host
of speaker `r`, other than the sender's, choose the positions `x` and `x'`
for the output samples `k` and `k + 1` of one playback block. If the step
of the estimate is positive and, divided by the slope of every block of the
schedule, is within `v` of one, with `0 ≤ v < 1`, then `x'` is one frame
after `x` within `v`. -/
theorem abs_chosen_succ_sub_le
    (hK : KnotSetting p (timedRules w.sender t level) w A q share (1 / t.rate))
    (lookahead : ℕ+) {r : Fin R} (hr : w.host r ≠ w.sender) {k : ℕ} {x x' : ℝ}
    (hblock : (w.speaker r).blockOf (k + 1) = (w.speaker r).blockOf k)
    (hx : (ruled p (timedRules w.sender t level) : Solution H R Payload).chosen w lookahead r k
      = some x)
    (hx' : (ruled p (timedRules w.sender t level) : Solution H R Payload).chosen w lookahead r
      (k + 1) = some x')
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hstep : 0 < estimateStep p w t level lookahead r ((w.speaker r).blockOf k))
    (hslope : ∀ c,
      estimateStep p w t level lookahead r ((w.speaker r).blockOf k) / (1 + v)
          ≤ dueSlope p (timedRules w.sender t level) w lookahead q share (1 / t.rate) c
        ∧ dueSlope p (timedRules w.sender t level) w lookahead q share (1 / t.rate) c
          ≤ estimateStep p w t level lookahead r ((w.speaker r).blockOf k) / (1 - v)) :
    |x' - x - 1| ≤ v := by
  obtain ⟨s, b, hs, -⟩ := (chosen_eq_some_iff hK lookahead hr k x).mp hx
  obtain ⟨s', b', hs', -⟩ := (chosen_eq_some_iff hK lookahead hr (k + 1) x').mp hx'
  have e := timed_estimate_succ p w t level lookahead hr hblock hs hs'
  have h := abs_chosen_sub_le hK lookahead hr hx hx' hs hs' (g := 1) zero_le_one hstep hv0 hv1
    (by rw [e]; ring) hslope
  rw [one_mul] at h
  exact h

/-- **Such a step of the target costs the follower nothing.** In the setting
of `abs_chosen_succ_sub_le`, with `v ≤ u`: the step of the filled-in target
from output sample `k` to the next differs from one frame by at most `u`,
so its `stepOver` is zero. -/
theorem stepOver_chosen_eq_zero
    (hK : KnotSetting p (timedRules w.sender t level) w A q share (1 / t.rate))
    (lookahead : ℕ+) {r : Fin R} (hr : w.host r ≠ w.sender) {k : ℕ} {x x' : ℝ}
    (hblock : (w.speaker r).blockOf (k + 1) = (w.speaker r).blockOf k)
    (hx : (ruled p (timedRules w.sender t level) : Solution H R Payload).chosen w lookahead r k
      = some x)
    (hx' : (ruled p (timedRules w.sender t level) : Solution H R Payload).chosen w lookahead r
      (k + 1) = some x')
    {u v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hvu : v ≤ u)
    (hstep : 0 < estimateStep p w t level lookahead r ((w.speaker r).blockOf k))
    (hslope : ∀ c,
      estimateStep p w t level lookahead r ((w.speaker r).blockOf k) / (1 + v)
          ≤ dueSlope p (timedRules w.sender t level) w lookahead q share (1 / t.rate) c
        ∧ dueSlope p (timedRules w.sender t level) w lookahead q share (1 / t.rate) c
          ≤ estimateStep p w t level lookahead r ((w.speaker r).blockOf k) / (1 - v)) :
    stepOver u
      (heldTarget ((ruled p (timedRules w.sender t level) : Solution H R Payload).chosen w
        lookahead r)) k = 0 := by
  have h := abs_chosen_succ_sub_le hK lookahead hr hblock hx hx' hv0 hv1 hstep hslope
  have e1 : heldTarget ((ruled p (timedRules w.sender t level) : Solution H R Payload).chosen w
      lookahead r) k = x := by
    rcases heldTarget_eq ((ruled p (timedRules w.sender t level) :
      Solution H R Payload).chosen w lookahead r) k with hn | hs
    · rw [hx] at hn
      exact absurd hn (by simp)
    · rw [hx] at hs
      exact (Option.some.inj hs).symm
  have e2 : heldTarget ((ruled p (timedRules w.sender t level) : Solution H R Payload).chosen w
      lookahead r) (k + 1) = x' := by
    rcases heldTarget_eq ((ruled p (timedRules w.sender t level) :
      Solution H R Payload).chosen w lookahead r) (k + 1) with hn | hs
    · rw [hx'] at hn
      exact absurd hn (by simp)
    · rw [hx'] at hs
      exact (Option.some.inj hs).symm
  unfold stepOver
  rw [e1, e2]
  exact max_eq_right (by linarith)

end Unisono.Solutions.Controller
