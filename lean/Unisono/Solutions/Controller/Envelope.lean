/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Knots

/-!
# The sender's clock from the arrivals of blocks

A block of the stream tells a receiving host about the sender's clock. With
the capture schedule of `Unisono.Solutions.Controller.Knots`, the value of a
block's schedule at its right end is the reading of the sender's clock when
the block was handed over, and the sender sends the block at that moment.
The host knows the reading of its own clock when the block arrives. This
file calls the two readings together the arrival of the block: the
reading of the host's clock when the block arrived, and the reading of
the sender's clock when the block was handed over.

A message arrives after it is sent. So when the host's clock shows the first
reading of an arrival, the sender's clock shows more than the second
reading: every arrival is a lower bound for the sender's clock. A block
that the network did not delay gives a bound that falls short of the
sender's clock by the least delay of the direction only. The host
therefore takes the largest of the bounds that its arrivals give, each
carried forward to the present at an estimated slope, and adds half of the
least round trip, which it knows from its clock exchanges.
This is the estimate of the sender's clock by the least round trip, with the
blocks of the stream as its data in the direction from the sender.

* `arrivalsOf`: the arrivals in a view.
* `envelope s y as`: the largest of the values `a.2 + s * (y - a.1)` over
  the arrivals `a` of the list `as`; it is at least each of them
  (`le_of_envelope`) and equal to one of them (`exists_of_envelope`).
* `ClockParts`, `envelopeReading`: the estimate as a rule for the controller
  (`Rules.reading`). The parts are the host's reading when an output sample
  leaves, the slope, half of the round trip, and the arrivals that are used.
* `mem_arrivalsOf_run`: in the run of the controller with a capture schedule
  from the knots, in every world: every arrival in a host's view is the
  reading of the host's clock at the arrival of a message that the sender
  sent at the handover of some block, with the reading of the sender's
  clock at that handover.
* `reading_le`, `exists_reading_eq`: **the error of the estimate, exactly.**
  For every arrival used, the reading of the sender's clock at any true time
  `o`, minus the estimate, is at most: the time on the sender's clock from
  the handover of the arrival's block to `o`, minus the slope times the time
  on the host's clock from the block's arrival to the reading that the host
  expects at `o`, minus half of the round trip. For one arrival used the two
  are equal. Nothing is assumed about the world.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The arrivals in a view, oldest first: for each block that arrived, the
reading of the host's clock at its arrival and the value of the block's
schedule at the right end of the block. -/
def arrivalsOf (l : List (Event H R Payload)) : List (ℝ × ℝ) :=
  l.filterMap fun e =>
    match e.observation with
    | .received _ (.block _ _ capture period _ _) F => some (e.reading, capture + F.card * period)
    | _ => none

/-- The largest of the values `a.2 + s * (y - a.1)` over the arrivals `a` of
a list; there is none for the empty list. -/
def envelope (s y : ℝ) : List (ℝ × ℝ) → Option ℝ
  | [] => none
  | a :: as =>
      match envelope s y as with
      | some v => some (max (a.2 + s * (y - a.1)) v)
      | none => some (a.2 + s * (y - a.1))

/-- The envelope of a list that is not empty has a value. -/
theorem envelope_isSome (s y : ℝ) {as : List (ℝ × ℝ)} (h : as ≠ []) :
    (envelope s y as).isSome := by
  cases as with
  | nil => exact absurd rfl h
  | cons a as =>
    unfold envelope
    cases envelope s y as <;> rfl

/-- The envelope is at least the value of each arrival. -/
theorem le_of_envelope {s y v : ℝ} :
    ∀ {as : List (ℝ × ℝ)}, envelope s y as = some v → ∀ a ∈ as, a.2 + s * (y - a.1) ≤ v
  | [], h, _, _ => by simp [envelope] at h
  | a :: as, h, a', ha' => by
    unfold envelope at h
    cases hrest : envelope s y as with
    | none =>
      rw [hrest] at h
      have hnil : as = [] := by
        by_contra hne
        have := envelope_isSome s y hne
        rw [hrest] at this
        exact absurd this (by simp)
      subst hnil
      rw [List.mem_singleton] at ha'
      subst ha'
      exact le_of_eq (Option.some.inj h)
    | some v' =>
      rw [hrest] at h
      have hv : max (a.2 + s * (y - a.1)) v' = v := Option.some.inj h
      rcases List.mem_cons.mp ha' with rfl | hmem
      · rw [← hv]
        exact le_max_left _ _
      · rw [← hv]
        exact le_trans (le_of_envelope hrest a' hmem) (le_max_right _ _)

/-- The envelope is the value of one of the arrivals. -/
theorem exists_of_envelope {s y v : ℝ} :
    ∀ {as : List (ℝ × ℝ)}, envelope s y as = some v → ∃ a ∈ as, v = a.2 + s * (y - a.1)
  | [], h => by simp [envelope] at h
  | a :: as, h => by
    unfold envelope at h
    cases hrest : envelope s y as with
    | none =>
      rw [hrest] at h
      exact ⟨a, List.mem_cons_self .., (Option.some.inj h).symm⟩
    | some v' =>
      rw [hrest] at h
      have hv : max (a.2 + s * (y - a.1)) v' = v := Option.some.inj h
      rcases le_total (a.2 + s * (y - a.1)) v' with hle | hle
      · rw [max_eq_right hle] at hv
        obtain ⟨a', ha', hav⟩ := exists_of_envelope hrest
        exact ⟨a', List.mem_cons_of_mem _ ha', by rw [← hv, hav]⟩
      · rw [max_eq_left hle] at hv
        exact ⟨a, List.mem_cons_self .., hv.symm⟩

/-- The parts of a host's estimate of the sender's clock from the arrivals
of blocks. Each is a function of the host's view at a request of a playback
device. -/
structure ClockParts (H : Type) (R : ℕ) where
  /-- The reading of the host's clock that the host expects when output
  sample `k` of speaker `r` leaves. -/
  output : List (Event H R Payload) → Fin R → ℕ → ℝ
  /-- The slope: by how much the host takes the sender's clock to advance
  while its own clock advances by one second. -/
  slope : List (Event H R Payload) → ℝ
  /-- Half of the least round trip between the host and the sender. -/
  halfTrip : List (Event H R Payload) → ℝ
  /-- The arrivals that the host uses. -/
  arrivals : List (Event H R Payload) → List (ℝ × ℝ)

/-- **The estimate of the sender's clock from the arrivals of blocks**, as a
rule for the controller. A host other than the sender takes the largest
value that its arrivals give for the reading that it expects of its own clock
when the output sample leaves, and adds half of the round trip; it has no
estimate while it uses no arrival. The sender's host uses its own clock. -/
def envelopeReading [DecidableEq H] (sender : H) (parts : ClockParts H R) :
    H → List (Event H R Payload) → Fin R → ℕ → Option ℝ :=
  fun h view r k =>
    if h = sender then some (parts.output view r k)
    else (envelope (parts.slope view) (parts.output view r k) (parts.arrivals view)).map
      (· + parts.halfTrip view)

/-- The estimate is at least what each arrival used gives. -/
theorem le_envelopeReading [DecidableEq H] {sender h : H} (hne : h ≠ sender)
    (parts : ClockParts H R) {view : List (Event H R Payload)} {r : Fin R} {k : ℕ} {s : ℝ}
    (hs : envelopeReading sender parts h view r k = some s) {a : ℝ × ℝ}
    (ha : a ∈ parts.arrivals view) :
    a.2 + parts.slope view * (parts.output view r k - a.1) + parts.halfTrip view ≤ s := by
  unfold envelopeReading at hs
  rw [ite_eq_right hne] at hs
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hs
  have := le_of_envelope hv a ha
  linarith

/-- The estimate is what one of the arrivals used gives. -/
theorem exists_envelopeReading_eq [DecidableEq H] {sender h : H} (hne : h ≠ sender)
    (parts : ClockParts H R) {view : List (Event H R Payload)} {r : Fin R} {k : ℕ} {s : ℝ}
    (hs : envelopeReading sender parts h view r k = some s) :
    ∃ a ∈ parts.arrivals view,
      s = a.2 + parts.slope view * (parts.output view r k - a.1) + parts.halfTrip view := by
  unfold envelopeReading at hs
  rw [ite_eq_right hne] at hs
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨a, ha, hav⟩ := exists_of_envelope hv
  exact ⟨a, ha, by rw [hav]⟩

variable [DecidableEq H] (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)

/-- **What an arrival is, in a run.** Let the capture schedule of the rules
come from the knots (`knotCapture`). Then every arrival in a host's view is,
for some block `b` and some true time `t` at which the network delivered to
the host a message that the sender sent at the handover of `b`: the reading
of the host's clock at `t`, and the reading of the sender's clock when it
handled the handover of `b`. The time `t` is before
every request that the run has not yet handled. This holds in every
world. -/
theorem mem_arrivalsOf_run {kn : KnotSettings} (hcap : rules.capture = knotCapture kn)
    (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ} {h : H} {a : ℝ × ℝ}
    (ha : a ∈ arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views h)) :
    ∃ b t, a = ((w.clock h).read t, w.handedReading b)
      ∧ (∃ q, w.network.deliver w.sender h (w.source.handed b) q = some t)
      ∧ (∀ r' : Fin R, t < (w.speaker r').asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r')) := by
  obtain ⟨e, he, hfe⟩ := List.mem_filterMap.mp ha
  cases hobs : e.observation with
  | handed frames stamp => simp [hobs] at hfe
  | asked r outputs stamp => simp [hobs] at hfe
  | timer => simp [hobs] at hfe
  | received j c F =>
    cases c with
    | ask sent need => simp [hobs] at hfe
    | answer sent received => simp [hobs] at hfe
    | block fr stamp cp pd lv sl =>
      simp only [hobs, Option.some.injEq] at hfe
      obtain ⟨b, t, hread, hq, hlt, hfr, hF, ⟨i, hi⟩, hhd⟩ :=
        ruled_received_block p rules w hsender lookahead he hobs
      unfold Rules.runHeader at hhd
      rw [Solution.handoverView_eq _ w lookahead hi] at hhd
      have hk := knotCapture_eq (ruled p rules : Solution H R Payload) w lookahead kn hi
        (w.source.first b) (w.source.reported b)
      have hcp : cp = w.handedReading b - w.blockLength b * w.knotPeriod kn b := by
        have h1 := congrArg Header.capture hhd
        simp only [Rules.header, hcap] at h1
        rw [h1, hk]
      have hpd : pd = w.knotPeriod kn b := by
        have h1 := congrArg Header.period hhd
        simp only [Rules.header, hcap] at h1
        rw [h1, hk]
      have hcard : F.card = w.blockLength b := by
        rw [hF]
        unfold CaptureDevice.block
        rw [List.toFinset_card_of_nodup List.nodup_range', List.length_range']
        rfl
      refine ⟨b, t, ?_, hq, hlt⟩
      rw [← hfe, hread, hcp, hpd, hcard]
      ring_nf

/-- **The estimate is not above what any arrival used allows.** In the
setting of `mem_arrivalsOf_run`, let the host use only arrivals of its view.
If the host's estimate for an output sample is `s`, then for every arrival
used there are a block `b` and a true time `t`, at which the network
delivered a message sent at the handover of `b`, with the following bound.
For every true time `o`: the reading of the sender's clock at `o` minus `s`
is at most the time on the sender's clock from the handover of `b` to `o`,
minus the slope times the time on the host's clock from `t` to the reading
that the host expects, minus half of the round trip. -/
theorem reading_le {kn : KnotSettings} (hcap : rules.capture = knotCapture kn)
    (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ} {h : H} (hne : h ≠ w.sender)
    (parts : ClockParts H R) {view : List (Event H R Payload)}
    (hsub : ∀ a ∈ parts.arrivals view,
      a ∈ arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views h))
    {r : Fin R} {k : ℕ} {s : ℝ}
    (hs : envelopeReading w.sender parts h view r k = some s) {a : ℝ × ℝ}
    (ha : a ∈ parts.arrivals view) :
    ∃ b t, a = ((w.clock h).read t, w.handedReading b)
      ∧ (∃ q, w.network.deliver w.sender h (w.source.handed b) q = some t)
      ∧ (∀ r' : Fin R, t < (w.speaker r').asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r'))
      ∧ ∀ o : Time, (w.clock w.sender).read o - s
          ≤ ((w.clock w.sender).read o - w.handedReading b)
            - parts.slope view * (parts.output view r k - (w.clock h).read t)
            - parts.halfTrip view := by
  obtain ⟨b, t, hab, hq, hlt⟩ :=
    mem_arrivalsOf_run p rules w hcap hsender lookahead (hsub a ha)
  refine ⟨b, t, hab, hq, hlt, fun o => ?_⟩
  have h1 := le_envelopeReading hne parts hs ha
  rw [hab] at h1
  simp only at h1
  linarith

/-- **The error of the estimate, exactly.** In the setting of `reading_le`,
for one arrival used the bound is an equality: there are a block `b` and a
true time `t`, at which the network delivered a message sent at the handover
of `b`, such that for every true time `o` the reading of the sender's clock
at `o` minus the estimate `s` is the time on the sender's clock from the
handover of `b` to `o`, minus the slope times the time on the host's clock
from `t` to the reading that the host expects, minus half of the round
trip. -/
theorem exists_reading_eq {kn : KnotSettings} (hcap : rules.capture = knotCapture kn)
    (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ} {h : H} (hne : h ≠ w.sender)
    (parts : ClockParts H R) {view : List (Event H R Payload)}
    (hsub : ∀ a ∈ parts.arrivals view,
      a ∈ arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views h))
    {r : Fin R} {k : ℕ} {s : ℝ}
    (hs : envelopeReading w.sender parts h view r k = some s) :
    ∃ b t, ((w.clock h).read t, w.handedReading b) ∈ parts.arrivals view
      ∧ (∃ q, w.network.deliver w.sender h (w.source.handed b) q = some t)
      ∧ (∀ r' : Fin R, t < (w.speaker r').asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r'))
      ∧ ∀ o : Time, (w.clock w.sender).read o - s
          = ((w.clock w.sender).read o - w.handedReading b)
            - parts.slope view * (parts.output view r k - (w.clock h).read t)
            - parts.halfTrip view := by
  obtain ⟨a, ha, hsa⟩ := exists_envelopeReading_eq hne parts hs
  obtain ⟨b, t, hab, hq, hlt⟩ :=
    mem_arrivalsOf_run p rules w hcap hsender lookahead (hsub a ha)
  refine ⟨b, t, hab ▸ ha, hq, hlt, fun o => ?_⟩
  rw [hsa, hab]
  ring

end Unisono.Solutions.Controller
