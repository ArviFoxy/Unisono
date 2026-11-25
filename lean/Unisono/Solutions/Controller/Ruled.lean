/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Views
public import Unisono.Spec.Limits
public import Unisono.Spec.OwnEvents
public import Unisono.Solutions.FixedDelay.Views
public import Unisono.Solutions.FixedDelay.Progress

/-!
# The controller with given rules

The controller of `Unisono.Solutions.Controller` takes its estimates from
two kinds of data only: clock exchanges and the timestamps that the devices
report. This file states the same controller for any rules, so that an
estimate may use everything that a host has observed, for example the
readings of its clock at the events of its devices and at the arrivals of
blocks.

`Rules` holds what completes the controller:

* `level`: how the sender chooses the level, and the need that a host
  reports in a clock query (`LevelRule`);
* `capture`: from the sender's view when the capture device hands over a
  block, the capture time that the block's header gives to the block's
  first frame, and the time from one frame to the next, both on the
  sender's clock;
* `reading`: from a host's view when a playback device requests a block,
  the host's estimate of the reading of the sender's clock when an output
  sample of that block leaves;
* `back`: how far the position that a speaker plays lies before the
  position that the schedule gives. A schedule may count positions from
  another origin than the frames of the source.

`ruled p rules` is the controller with these rules. It sends what the
baseline sends, with the headers and needs of the rules, and at a request it
plays, for each output sample, the position that is due by the headers of
its schedule when the sender's clock reads the host's estimate, moved back
by `rules.back`.

These statements hold in every world, for any rules:

* `ruled_sendsMore`: its messages are the baseline's messages with more in
  each, so its run is the baseline's run once the further fields are
  forgotten.
* `ruled_isStar`: its hosts exchange messages only with the sender.
* `ruled_plays_asked`: what it plays at a request.
* `ruled_block_header`: every block in transit carries the header that the
  rules give at the sender's view when the capture device handed the block
  over.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The rules that complete the controller. -/
structure Rules (H : Type) (R : ℕ) where
  /-- How the sender chooses the level, and the need that a host reports in
  a clock query. -/
  level : LevelRule H R
  /-- From the sender's view up to and including the handover of a block,
  the block's first frame and the block's timestamp: the capture time that
  the header gives to the first frame, and the time from one frame to the
  next, both on the sender's clock. -/
  capture : List (Event H R Payload) → ℕ → ℝ → ℝ × ℝ
  /-- From a host's view up to and including a request of the device of
  speaker `r`: the host's estimate of the reading of the sender's clock when
  output sample `k` leaves, if it has one. -/
  reading : H → List (Event H R Payload) → Fin R → ℕ → Option ℝ
  /-- How far the position that a speaker plays lies before the position
  that the schedule gives. -/
  back : ℝ

/-- The header that a block with first frame `f` carries under the rules,
given the sender's view up to and including the block's handover. -/
def Rules.header (rules : Rules H R) (view : List (Event H R Payload)) (f : ℕ) (stamp : ℝ) :
    Header :=
  ⟨f, (rules.capture view f stamp).1, (rules.capture view f stamp).2,
    (rules.level.announce view f).1, (rules.level.announce view f).2⟩

/-- The headers of the blocks that the sender's own capture device has
handed over in a view, oldest first: the headers that the rules put in those
blocks, each with the number of frames of its block. -/
def Rules.ownHeaders (rules : Rules H R) (l : List (Event H R Payload)) : List (Header × ℕ) :=
  (l.foldl
    (fun (acc : List (Event H R Payload) × List (Header × ℕ)) e =>
      (acc.1 ++ [e],
        match e.observation with
        | .handed frames stamp =>
            match frames.head? with
            | some f => acc.2 ++ [(rules.header (acc.1 ++ [e]) f.1 stamp, frames.length)]
            | none => acc.2
        | _ => acc.2))
    ([], [])).2

/-- A message of the baseline with the further fields that the rules give,
as host `h` fills them in at the view `view`. -/
def Rules.enrich (rules : Rules H R) (h : H) (view : List (Event H R Payload)) :
    FixedDelay.Payload → Payload
  | .block f stamp =>
      .block f stamp (rules.header view f stamp).capture (rules.header view f stamp).period
        (rules.header view f stamp).level (rules.header view f stamp).slope
  | .ask sent => .ask sent (rules.level.need h view)
  | .answer sent received => .answer sent received

/-- Forgetting the further fields of an enriched message gives the message
back. -/
theorem Rules.plain_enrich (rules : Rules H R) (h : H) (view : List (Event H R Payload))
    (x : FixedDelay.Payload) : (rules.enrich h view x).plain = x := by
  cases x <;> rfl

variable [DecidableEq H] (p : FixedDelay.Params H) (rules : Rules H R)

/-- The schedule that a host follows after the events `l`: the headers of
the blocks that have arrived, or at the sender's host the headers of the
blocks handed over. -/
def Rules.schedule (h : H) (l : List (Event H R Payload)) : List (Header × ℕ) :=
  if h = p.sender then rules.ownHeaders l else headersOf l

/-- **The controller with given rules.** Each host sends what the baseline
sends, with the further fields that the rules give. At a request of a
playback device, each output sample plays the position that is due by the
headers of the host's schedule when the sender's clock reads the host's
estimate for that output sample, moved back by `rules.back`; it plays
nothing while the host has no estimate, or while no block of its schedule
covers its own due position. -/
def ruled : Solution H R Payload := fun h view =>
  { sends := ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
        (view.map (Event.mapMsg Payload.plain))).sends.map
      fun s => (s.1, rules.enrich h view s.2.1, s.2.2)
    timers := ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
        (view.map (Event.mapMsg Payload.plain))).timers
    plays :=
      match view.getLast? with
      | some e =>
          match e.observation with
          | .asked r _ _ => fun k =>
              ((rules.reading h view r k).bind (dueOf (rules.schedule p h view))).map
                (· - rules.back)
          | _ => fun _ => none
      | none => fun _ => none }

/-- **The controller with given rules sends what the baseline sends, with
more in each message.** -/
theorem ruled_sendsMore :
    (ruled p rules : Solution H R Payload).SendsMore (FixedDelay.solution p) Payload.plain := by
  intro h v
  refine ⟨?_, rfl⟩
  show mapSends Payload.plain
      (((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
          (v.map (Event.mapMsg Payload.plain))).sends.map
        fun s => (s.1, rules.enrich h v s.2.1, s.2.2)) = _
  rw [mapSends, List.map_map]
  conv_rhs => rw [← List.map_id ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
    (v.map (Event.mapMsg Payload.plain))).sends]
  refine List.map_congr_left fun s _ => ?_
  simp [Rules.plain_enrich]

/-- **The hosts of the controller with given rules exchange messages only
with the sender.** -/
theorem ruled_isStar : (ruled p rules : Solution H R Payload).IsStar p.sender := by
  intro h view dst msg frames hmem
  change (dst, msg, frames) ∈ ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
      (view.map (Event.mapMsg Payload.plain))).sends.map
    (fun s => (s.1, rules.enrich h view s.2.1, s.2.2)) at hmem
  obtain ⟨s₀, hs₀, heq⟩ := List.mem_map.mp hmem
  have h1 := fixedDelay_isStar (R := R) p h (view.map (Event.mapMsg Payload.plain)) s₀.1
    s₀.2.1 s₀.2.2 hs₀
  have hdst : s₀.1 = dst := congrArg Prod.fst heq
  rw [← hdst]
  exact h1

/-- What the controller with given rules plays at a device request. -/
theorem ruled_plays_asked (h : H) (l : List (Event H R Payload)) (reading : ℝ) (r : Fin R)
    (outputs : List ℕ) (stamp : ℝ) (k : ℕ) :
    ((ruled p rules : Solution H R Payload) h
        (l ++ [⟨reading, .asked r outputs stamp⟩])).plays k
      = ((rules.reading h (l ++ [⟨reading, .asked r outputs stamp⟩]) r k).bind
          (dueOf (rules.schedule p h (l ++ [⟨reading, .asked r outputs stamp⟩])))).map
        (· - rules.back) := by
  simp [ruled]

/-- The controller with given rules sends a block only at the sender, when
the capture device hands over a block with that first frame and that
timestamp, and the block carries the header that the rules give at the
sender's view then. -/
theorem ruled_sends_block (h : H) (l : List (Event H R Payload)) (e : Event H R Payload)
    {s : H × Payload × Finset ℕ}
    (hs : s ∈ ((ruled p rules : Solution H R Payload) h (l ++ [e])).sends)
    {fr : ℕ} {stamp c pd lv sl : ℝ} (hb : s.2.1 = .block fr stamp c pd lv sl) :
    h = p.sender ∧ (∃ frames t₀, e.observation = .handed frames stamp
        ∧ frames.head? = some (fr, t₀))
      ∧ (⟨fr, c, pd, lv, sl⟩ : Header) = rules.header (l ++ [e]) fr stamp := by
  change s ∈ ((FixedDelay.solution p : Solution H R FixedDelay.Payload) h
      ((l ++ [e]).map (Event.mapMsg Payload.plain))).sends.map
    (fun s => (s.1, rules.enrich h (l ++ [e]) s.2.1, s.2.2)) at hs
  obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
  dsimp only at hb
  rw [List.map_append, List.map_cons, List.map_nil, FixedDelay.solution_append] at hs₀
  cases hpl : s₀.2.1 with
  | ask sent =>
    rw [hpl] at hb
    simp [Rules.enrich] at hb
  | answer sent received =>
    rw [hpl] at hb
    simp [Rules.enrich] at hb
  | block f' st' =>
    rw [hpl] at hb
    simp only [Rules.enrich, Payload.block.injEq] at hb
    obtain ⟨rfl, rfl, hc, hpd, hlv, hsl⟩ := hb
    obtain ⟨hh, frames, t₀, hobs, hhead⟩ := FixedDelay.act_sends_block p h _ _ hs₀ hpl
    refine ⟨hh, ⟨frames, t₀, ?_, hhead⟩, ?_⟩
    · obtain ⟨reading, obs⟩ := e
      cases obs with
      | handed frames' stamp' =>
        simpa [Event.mapMsg, Observation.mapMsg] using hobs
      | asked r outputs stamp' => simp [Event.mapMsg, Observation.mapMsg] at hobs
      | received i c' F => simp [Event.mapMsg, Observation.mapMsg] at hobs
      | timer => simp [Event.mapMsg, Observation.mapMsg] at hobs
    · rw [← hc, ← hpd, ← hlv, ← hsl]
      rfl

variable (w : World H R)

/-- **Every block in transit carries the header that the rules gave at its
handover.** A block of the controller with given rules in transit was sent
when the capture device handed over some block `b`; it carries that block's
first frame and timestamp, and the header that the rules give at the
sender's view at that moment. -/
theorem ruled_block_header (lookahead : ℕ+) (n : ℕ) {msg : InFlight H Payload}
    (hm : msg ∈ ((ruled p rules : Solution H R Payload).states w lookahead n).inFlight)
    {fr : ℕ} {stamp c pd lv sl : ℝ} (hc : msg.contents = .block fr stamp c pd lv sl) :
    ∃ i < n, ∃ b,
      (ruled p rules : Solution H R Payload).handled w lookahead i
          = some (w.sender, w.source.handed b,
            .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))
        ∧ fr = w.source.first b ∧ stamp = w.source.reported b
        ∧ (⟨fr, c, pd, lv, sl⟩ : Header)
          = rules.header
            (((ruled p rules : Solution H R Payload).states w lookahead i).views w.sender
              ++ [⟨(w.clock w.sender).read (w.source.handed b),
                .handed ((w.source.block b).map fun k => (k, w.target k))
                  (w.source.reported b)⟩])
            (w.source.first b) (w.source.reported b) := by
  induction n with
  | zero => simp [Solution.states, State.start] at hm
  | succ n ih =>
    rcases Solution.mem_inFlight_succ w _ lookahead n hm with
      hold | ⟨h, t, obs, hh, s, hs, -, -, hcont, -, -⟩
    · obtain ⟨i, hi, rest⟩ := ih hold
      exact ⟨i, Nat.lt_succ_of_lt hi, rest⟩
    · rw [hcont] at hc
      obtain ⟨hhs, ⟨frames, t₀, hobs, hhead⟩, hheader⟩ := ruled_sends_block p rules h _ _ hs hc
      dsimp only at hobs
      subst hobs
      obtain ⟨b, hhw, ht, hframes, hstamp⟩ := Solution.handled_handed w _ lookahead hh
      subst hhw ht hframes hstamp
      have hfr : fr = w.source.first b := by
        rw [List.head?_map, CaptureDevice.head?_block, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hhead
        exact hhead.1.symm
      subst hfr
      exact ⟨n, Nat.lt_succ_self n, b, hh, rfl, rfl, hheader⟩

/-- **Where a block of the controller with given rules comes from.** A
block in transit was sent by the sender when the capture device handed over
some block `b`. It carries that block's first frame, timestamp and frames,
and the header that the rules give at the sender's view at that moment; the
network delivers it as a message sent at the true time of the handover. -/
theorem ruled_block_origin (hsender : p.sender = w.sender) (lookahead : ℕ+) (n : ℕ)
    {msg : InFlight H Payload}
    (hm : msg ∈ ((ruled p rules : Solution H R Payload).states w lookahead n).inFlight)
    {fr : ℕ} {stamp c pd lv sl : ℝ} (hc : msg.contents = .block fr stamp c pd lv sl) :
    ∃ b, (∃ i < n, (ruled p rules : Solution H R Payload).handled w lookahead i
          = some (w.sender, w.source.handed b,
            .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))
        ∧ (⟨fr, c, pd, lv, sl⟩ : Header)
          = rules.header
            (((ruled p rules : Solution H R Payload).states w lookahead i).views w.sender
              ++ [w.handedEvent b])
            (w.source.first b) (w.source.reported b))
      ∧ fr = w.source.first b ∧ stamp = w.source.reported b ∧ msg.origin = w.sender
      ∧ msg.frames = (w.source.block b).toFinset
      ∧ ∃ q, w.network.deliver w.sender msg.destination (w.source.handed b) q
          = some msg.arrival := by
  obtain ⟨i, hi, b, hh, hfr, hst, hhd⟩ := ruled_block_header p rules w lookahead n hm hc
  have hfl := (State.fields_of_withoutPlays_eq
    (Solution.states_forget w Payload.plain lookahead (ruled_sendsMore p rules) n)).2.2.2.1
  have hmem : msg.mapMsg Payload.plain
      ∈ ((FixedDelay.solution p : Solution H R FixedDelay.Payload).states w lookahead
        n).inFlight := by
    rw [← hfl]
    exact List.mem_map_of_mem hm
  have horigin := FixedDelay.origin_inFlight p w lookahead hsender n _ hmem
  have hcont : (msg.mapMsg Payload.plain).contents = .block fr stamp := by
    show Payload.plain msg.contents = _
    rw [hc]
    rfl
  simp only [FixedDelay.Origin, hcont] at horigin
  obtain ⟨b', ho, hf', -, hframes, q, hq⟩ := horigin
  have hb : b' = b := w.source.first_strictMono.injective (hf'.symm.trans hfr)
  subst hb
  exact ⟨b', ⟨i, hi, hh, hhd⟩, hfr, hst, ho, hframes, q, hq⟩

/-- The header that the rules give to block `b` in the run of the
controller: the header at the sender's view when it handles the handover of
`b`. -/
def Rules.runHeader (lookahead : ℕ+) (b : ℕ) : Header :=
  rules.header ((ruled p rules : Solution H R Payload).handoverView w lookahead b)
    (w.source.first b) (w.source.reported b)

/-- **What a block that arrived tells a host.** A block in a host's view
arrived when the network delivered a message that the sender sent at the
handover of some block `b`, at a true time `t` before every request that the
run has not yet handled. The reading of the event is the reading of the
host's clock at `t`, and the block carries the first frame and the frames of
block `b` and the header that the rules gave at the handover. -/
theorem ruled_received_block (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ} {h : H}
    {e : Event H R Payload}
    (he : e ∈ ((ruled p rules : Solution H R Payload).states w lookahead n).views h)
    {j : H} {fr : ℕ} {stamp c pd lv sl : ℝ} {F : Finset ℕ}
    (ho : e.observation = .received j (.block fr stamp c pd lv sl) F) :
    ∃ b t, e.reading = (w.clock h).read t
      ∧ (∃ q, w.network.deliver w.sender h (w.source.handed b) q = some t)
      ∧ (∀ r : Fin R, t < (w.speaker r).asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r))
      ∧ fr = w.source.first b ∧ F = (w.source.block b).toFinset
      ∧ (∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
          = some (w.sender, w.source.handed b,
            .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
      ∧ (⟨fr, c, pd, lv, sl⟩ : Header) = rules.runHeader p w lookahead b := by
  obtain ⟨i₁, hi₁, t, obs, hh, rfl⟩ := Solution.handled_of_mem_views w _ lookahead he
  dsimp only at ho
  subst ho
  obtain ⟨m, hm, hd, ha, -, hcon, hF⟩ := Solution.handled_received w _ lookahead hh
  obtain ⟨b, ⟨i, hi, hhi, hhd⟩, hfr, -, -, hframes, q, hq⟩ :=
    ruled_block_origin p rules w hsender lookahead i₁ hm hcon
  refine ⟨b, t, rfl, ⟨q, ?_⟩,
    fun r => Solution.received_lt_asked _ w lookahead hi₁.le hh r, hfr, ?_, ⟨i, hhi⟩, ?_⟩
  · rw [← hd, ← ha]
    exact hq
  · rw [← hF]
    exact hframes
  · unfold Rules.runHeader
    rw [Solution.handoverView_eq _ w lookahead hhi]
    exact hhd

/-- **What a host of the controller chooses.** Let speaker `r` be on a host
other than the sender's. If, at step `n` of the run, the host chooses the
position `x` for output sample `k` at a request of block `β`, then:

* the host has an estimate `s` of the reading of the sender's clock when
  the output sample leaves;
* some block `b` of the stream, sent at its handover, arrived at the host at
  a true time `t` before every request that the run has not yet handled;
* the run handled the handover of block `b`;
* the header of block `b` covers the position that it says is due at `s`,
  and `x` is that position moved back by `rules.back`.

This holds in every world, for any rules. -/
theorem ruled_chosen (hsender : p.sender = w.sender) (lookahead : ℕ+) {n : ℕ} {r : Fin R}
    (hr : w.host r ≠ w.sender) {β k : ℕ} {x : ℝ}
    (hx : (ruled p rules : Solution H R Payload).chosenAt w lookahead n r β k = some x) :
    ∃ s b t,
      rules.reading (w.host r)
          (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r β]) r k = some s
      ∧ (∃ q, w.network.deliver w.sender (w.host r) (w.source.handed b) q = some t)
      ∧ (∀ r' : Fin R, t < (w.speaker r').asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r'))
      ∧ (∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
          = some (w.sender, w.source.handed b,
            .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
      ∧ (rules.runHeader p w lookahead b).Covers (w.blockLength b) s
      ∧ x + rules.back = (rules.runHeader p w lookahead b).due s := by
  classical
  unfold Solution.chosenAt at hx
  have hplays := ruled_plays_asked p rules (w.host r)
    (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r))
    ((w.clock (w.host r)).read ((w.speaker r).asked β)) r ((w.speaker r).block β)
    ((w.speaker r).reported β) k
  have hx' : (((rules.reading (w.host r)
        (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
          ++ [w.askedEvent r β]) r k).bind
      (dueOf (rules.schedule p (w.host r)
        (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
          ++ [w.askedEvent r β])))).map (· - rules.back)) = some x := by
    rw [← hx]
    exact hplays.symm
  obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.mp hx'
  obtain ⟨s, hs, hdue⟩ := Option.bind_eq_some_iff.mp hz
  have hsched : rules.schedule p (w.host r)
      (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
        ++ [w.askedEvent r β])
      = headersOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r)) := by
    unfold Rules.schedule
    rw [ite_eq_right (by rw [hsender]; exact hr)]
    exact headersOf_append_asked _ _ _ _ _
  rw [hsched] at hdue
  unfold dueOf at hdue
  obtain ⟨hc, hfind, hzc⟩ := Option.map_eq_some_iff.mp hdue
  have hmem := List.mem_of_find?_eq_some hfind
  have hcov : hc.1.Covers hc.2 s := by
    have := List.find?_some hfind
    simpa using this
  obtain ⟨e, he, i₀, stamp, F, hobs, hcount⟩ := mem_headersOf hmem
  obtain ⟨b, t, -, hq, hlt, hfr, hF, hhandled, hhd⟩ :=
    ruled_received_block p rules w hsender lookahead he hobs
  have hcard : hc.2 = w.blockLength b := by
    rw [hcount, hF]
    unfold CaptureDevice.block
    rw [List.toFinset_card_of_nodup List.nodup_range', List.length_range']
    rfl
  have hheader : hc.1 = rules.runHeader p w lookahead b := hhd
  refine ⟨s, b, t, hs, hq, hlt, hhandled, ?_, ?_⟩
  · rw [← hheader, ← hcard]
    exact hcov
  · rw [← hheader, hzc, ← hzx]
    ring

/-- **Every request is handled**, in a world whose capture device hands over
blocks without end and whose playback devices request blocks without end:
the run of the controller with given rules handles every request of every
speaker at some step. -/
theorem ruled_request_step (hhand : ∀ T, ∃ b, T < w.source.handed b)
    (hask : ∀ r T, ∃ b, T < (w.speaker r).asked b) (lookahead : ℕ+) (r : Fin R) (b : ℕ) :
    ∃ n, earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
      ((ruled p rules : Solution H R Payload).states w lookahead n).due
        = some (.asked r b) := by
  obtain ⟨m, hm⟩ := FixedDelay.progress_of_unbounded p w lookahead hhand hask
    ((w.speaker r).asked b)
  rw [← Solution.eventTime_forget w Payload.plain lookahead (ruled_sendsMore p rules) m] at hm
  obtain ⟨n, -, -, h2⟩ := Solution.exists_asked_step w (ruled p rules) lookahead
    (Solution.lt_askedNext (ruled p rules) w lookahead hm)
  exact ⟨n, h2⟩

/-- **Every handover is handled**, in a world whose capture device hands
over blocks without end and whose playback devices request blocks without
end. -/
theorem ruled_handover_step (hhand : ∀ T, ∃ b, T < w.source.handed b)
    (hask : ∀ r T, ∃ b, T < (w.speaker r).asked b) (lookahead : ℕ+) (b : ℕ) :
    ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)) := by
  obtain ⟨n, hn⟩ := FixedDelay.progress_of_unbounded p w lookahead hhand hask
    (w.source.handed b)
  rw [← Solution.eventTime_forget w Payload.plain lookahead (ruled_sendsMore p rules) n] at hn
  obtain ⟨i, -, -, hE⟩ := Solution.exists_handed_step w (ruled p rules) lookahead
    (Solution.lt_handedNext w (ruled p rules) lookahead hn)
  exact ⟨i, Solution.handled_of_handed _ w lookahead hE⟩

end Unisono.Solutions.Controller
