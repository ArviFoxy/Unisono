/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.DueSchedule
public import Unisono.Solutions.Controller.Envelope
public import Unisono.Solutions.FixedDelay.NoLoss

/-!
# What a host of the controller holds at a request, without loss

In a world without loss, a message that host `i` sends to host `j` at true
time `s` arrives at a time `A i j s`. The worlds built from draws are of
this kind. `NoLoss p w A` collects this and what the controller needs of
its parameters: its sender is the world's, it sends the stream to the host
of every speaker, once or more.

For the controller with given rules in such a world, and a speaker on a
host other than the sender's:

* `ruled_block_arrived`: a block whose message arrived before the event of
  a step is in the host's view at that step, with the reading of the host's
  clock at the arrival, the frames of the block and the block's header.
* `runHeader_mem_headersOf`, `headersOf_noLoss`: so the headers that the
  host holds are those of the blocks that arrived.
* `arrival_mem_arrivalsOf`, `mem_arrivalsOf_noLoss`: under the capture
  schedule of the knots, the pairs of readings that the host holds are, for
  the blocks that arrived, the reading of its clock at the arrival and the
  reading of the sender's clock at the block's handover.
* `ruled_chosen_iff`: **what a host chooses, exactly.** With the capture
  schedule of the knots and the level rule `knotLevel`, at the step that
  handles a request: the host chooses the position `x` for an output sample
  exactly when it has an estimate `s` of the sender's clock, the block `b`
  whose edges enclose `s` arrived before the request, and `x` is the
  position that the header of `b` gives for `s`, moved back by
  `rules.back`.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- A world without loss, for the controller with the parameters `p`: every
message arrives, at a time `A i j s` that depends on the two hosts and on
the true time `s` at which it is sent; the controller's sender is the
world's; the hosts to which the controller sends the stream are listed
once, each at least one copy is sent, and the host of every speaker is among
them. -/
structure NoLoss (p : FixedDelay.Params H) (w : World H R) (A : H → H → Time → Time) :
    Prop where
  deliver : ∀ i j s q, w.network.deliver i j s q = some (A i j s)
  sender : p.sender = w.sender
  nodup : p.speakers.Nodup
  copies : 0 < p.copies
  speakers : ∀ r, w.host r ∈ p.speakers

variable {p : FixedDelay.Params H} {rules : Rules H R} {w : World H R}
  {A : H → H → Time → Time}

/-- **A block that arrived is in the host's view.** In a world without
loss, let the message of block `b` to the host of speaker `r`, a host other
than the sender's, arrive before the event of step `n`. Then the host's view
at step `n` holds the arrival: an event with the reading of the host's
clock at the arrival, the first frame and the frames of the block, and the
header that the rules gave the block. -/
theorem ruled_block_arrived (hN : NoLoss p w A) (lookahead : ℕ+) {r : Fin R}
    (hr : w.host r ≠ w.sender) {b n : ℕ}
    (hk : A w.sender (w.host r) (w.source.handed b)
      < (ruled p rules : Solution H R Payload).eventTime w lookahead n) :
    ∃ stamp cp pd lv sl,
      (⟨(w.clock (w.host r)).read (A w.sender (w.host r) (w.source.handed b)),
          .received w.sender (.block (w.source.first b) stamp cp pd lv sl)
            (w.source.block b).toFinset⟩ : Event H R Payload)
        ∈ ((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
      ∧ (⟨w.source.first b, cp, pd, lv, sl⟩ : Header) = rules.runHeader p w lookahead b := by
  have hk' : A w.sender (w.host r) (w.source.handed b)
      < (FixedDelay.solution p : Solution H R FixedDelay.Payload).eventTime w lookahead n := by
    rw [← Solution.eventTime_forget w Payload.plain lookahead (ruled_sendsMore p rules) n]
    exact hk
  obtain ⟨i, hin, hi⟩ := FixedDelay.block_handled_of_noLoss p w lookahead hN.deliver hN.sender
    hN.nodup hN.copies (hN.speakers r) hr hk'
  have hf := Solution.handled_forget w Payload.plain lookahead (ruled_sendsMore p rules) i
  rw [hi] at hf
  obtain ⟨x, hx, hxeq⟩ := Option.map_eq_some_iff.mp hf
  obtain ⟨h', t', obs'⟩ := x
  simp only [Prod.mk.injEq] at hxeq
  obtain ⟨hh, ht, hobs⟩ := hxeq
  subst hh ht
  cases obs' with
  | handed frames stamp => simp [Observation.mapMsg] at hobs
  | asked r' outputs stamp => simp [Observation.mapMsg] at hobs
  | timer => simp [Observation.mapMsg] at hobs
  | received j c F =>
    simp only [Observation.mapMsg, Observation.received.injEq] at hobs
    obtain ⟨hj, hc, hF⟩ := hobs
    subst hj hF
    cases c with
    | ask sent need => simp [Payload.plain] at hc
    | answer sent received => simp [Payload.plain] at hc
    | block fr stamp cp pd lv sl =>
      simp only [Payload.plain, FixedDelay.Payload.block.injEq] at hc
      obtain ⟨hfr, -⟩ := hc
      subst hfr
      have hmem := Solution.mem_views_of_handled w _ lookahead hx hin
      obtain ⟨b', t, -, -, -, hfr', -, -, hhd⟩ :=
        ruled_received_block p rules w hN.sender lookahead hmem rfl
      have hb : b = b' := w.source.first_strictMono.injective hfr'
      subst hb
      exact ⟨stamp, cp, pd, lv, sl, hmem, hhd⟩

/-- **The header of a block that arrived is in the host's schedule.** -/
theorem runHeader_mem_headersOf (hN : NoLoss p w A) (lookahead : ℕ+) {r : Fin R}
    (hr : w.host r ≠ w.sender) {b n : ℕ}
    (hk : A w.sender (w.host r) (w.source.handed b)
      < (ruled p rules : Solution H R Payload).eventTime w lookahead n) :
    (rules.runHeader p w lookahead b, w.blockLength b)
      ∈ headersOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r)) := by
  obtain ⟨stamp, cp, pd, lv, sl, hmem, hhd⟩ := ruled_block_arrived hN lookahead hr hk
  have h1 := headersOf_mem hmem (i := w.sender) (f := w.source.first b) (stamp := stamp)
    (capture := cp) (period := pd) (level := lv) (slope := sl)
    (F := (w.source.block b).toFinset) rfl
  have hcard : (w.source.block b).toFinset.card = w.blockLength b := by
    unfold CaptureDevice.block
    rw [List.toFinset_card_of_nodup List.nodup_range', List.length_range']
    rfl
  rw [hhd, hcard] at h1
  exact h1

/-- **Every header in a host's schedule is that of a block that arrived**
before every request that the run has not yet handled. -/
theorem headersOf_noLoss (hN : NoLoss p w A) (lookahead : ℕ+) {n : ℕ} {h : H}
    {x : Header × ℕ}
    (hx : x ∈ headersOf (((ruled p rules : Solution H R Payload).states w lookahead n).views h)) :
    ∃ c, x = (rules.runHeader p w lookahead c, w.blockLength c)
      ∧ ∀ r' : Fin R, A w.sender h (w.source.handed c) < (w.speaker r').asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r') := by
  obtain ⟨e, he, i₀, stamp, F, hobs, hcount⟩ := mem_headersOf hx
  obtain ⟨c, t, -, ⟨q, hq⟩, hlt, -, hF, -, hhd⟩ :=
    ruled_received_block p rules w hN.sender lookahead he hobs
  have ht : t = A w.sender h (w.source.handed c) := by
    rw [hN.deliver] at hq
    exact (Option.some.inj hq).symm
  have hcard : x.2 = w.blockLength c := by
    rw [hcount, hF]
    unfold CaptureDevice.block
    rw [List.toFinset_card_of_nodup List.nodup_range', List.length_range']
    rfl
  refine ⟨c, ?_, fun r' => ht ▸ hlt r'⟩
  have h1 : x.1 = rules.runHeader p w lookahead c := hhd
  exact Prod.ext h1 hcard

/-- **The pair of readings of a block that arrived is among the host's
arrivals**, under the capture schedule of the knots: the reading of the
host's clock at the arrival, and the reading of the sender's clock at the
block's handover. -/
theorem arrival_mem_arrivalsOf {nominal : ℝ} (hcap : rules.capture = knotCapture nominal)
    (hN : NoLoss p w A) (lookahead : ℕ+) {r : Fin R} (hr : w.host r ≠ w.sender) {b n : ℕ}
    (hk : A w.sender (w.host r) (w.source.handed b)
      < (ruled p rules : Solution H R Payload).eventTime w lookahead n) :
    ((w.clock (w.host r)).read (A w.sender (w.host r) (w.source.handed b)), w.handedReading b)
      ∈ arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r)) := by
  obtain ⟨stamp, cp, pd, lv, sl, hmem, hhd⟩ := ruled_block_arrived hN lookahead hr hk
  have hin : ((w.clock (w.host r)).read (A w.sender (w.host r) (w.source.handed b)),
      cp + ((w.source.block b).toFinset.card : ℝ) * pd)
      ∈ arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
        (w.host r)) := List.mem_filterMap.mpr ⟨_, hmem, rfl⟩
  obtain ⟨b', t, hab, ⟨q, hq⟩, -⟩ :=
    mem_arrivalsOf_run p rules w hcap hN.sender lookahead hin
  have ht : t = A w.sender (w.host r) (w.source.handed b') := by
    rw [hN.deliver] at hq
    exact (Option.some.inj hq).symm
  -- The header's line ends at the reading of the block's own handover.
  have hknot : cp + ((w.source.block b).toFinset.card : ℝ) * pd = w.handedReading b := by
    have hcard : (w.source.block b).toFinset.card = w.blockLength b := by
      unfold CaptureDevice.block
      rw [List.toFinset_card_of_nodup List.nodup_range', List.length_range']
      rfl
    obtain ⟨i, hi⟩ : ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
        = some (w.sender, w.source.handed b,
          .handed ((w.source.block b).map fun k => (k, w.target k))
            (w.source.reported b)) := by
      obtain ⟨b'', t'', -, -, -, hfr'', -, hhandled, -⟩ :=
        ruled_received_block p rules w hN.sender lookahead hmem rfl
      have hb : b = b'' := w.source.first_strictMono.injective hfr''
      subst hb
      exact hhandled
    have hH := runHeader_knots p rules w lookahead hcap hi
    rw [← hhd] at hH
    have hcp : cp = w.handedReading b - w.blockLength b * w.knotPeriod nominal b :=
      congrArg Header.capture hH
    have hpd : pd = w.knotPeriod nominal b := congrArg Header.period hH
    rw [hcard, hcp, hpd]
    ring
  rw [hknot] at hin
  exact hin

/-- **Every pair among a host's arrivals is that of a block that arrived**
before every request that the run has not yet handled, under the capture
schedule of the knots. -/
theorem mem_arrivalsOf_noLoss {nominal : ℝ} (hcap : rules.capture = knotCapture nominal)
    (hN : NoLoss p w A) (lookahead : ℕ+) {n : ℕ} {h : H} {a : ℝ × ℝ}
    (ha : a ∈ arrivalsOf (((ruled p rules : Solution H R Payload).states w lookahead n).views h)) :
    ∃ b, a = ((w.clock h).read (A w.sender h (w.source.handed b)), w.handedReading b)
      ∧ ∀ r' : Fin R, A w.sender h (w.source.handed b) < (w.speaker r').asked
          (((ruled p rules : Solution H R Payload).states w lookahead n).askedNext r') := by
  obtain ⟨b, t, hab, ⟨q, hq⟩, hlt⟩ := mem_arrivalsOf_run p rules w hcap hN.sender lookahead ha
  have ht : t = A w.sender h (w.source.handed b) := by
    rw [hN.deliver] at hq
    exact (Option.some.inj hq).symm
  exact ⟨b, ht ▸ hab, fun r' => ht ▸ hlt r'⟩

/-- **What a host chooses, exactly.** Take the controller with the capture
schedule of the knots and the level rule `knotLevel`, with `0 ≤ share < 1`
and a positive time from one frame to the next for the first block, in a
world without loss whose capture device hands over blocks without end. Let
speaker `r` be on a host other than the sender's, and let step `n` handle
the request of block `β`. The host chooses the position `x` for output
sample `k` exactly when: it has an estimate `s` of the reading of the
sender's clock when the output sample leaves; `s` lies from the edge of some
block `b` to just before the edge of `b + 1`; the message of `b` arrived
before the request; and `x` is the first frame of `b` plus the distance of
`s` from the edge of `b` divided by the slope of `b`, moved back by
`rules.back`. -/
theorem ruled_chosen_iff {q : LevelSettings} {share nominal : ℝ}
    {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture nominal)
    (hlev : rules.level = knotLevel q share nominal need) (hs0 : 0 ≤ share) (hs1 : share < 1)
    (hnominal : 0 < nominal) (hN : NoLoss p w A) (lookahead : ℕ+)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    {n : ℕ} {r : Fin R} (hr : w.host r ≠ w.sender) {β : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (k : ℕ) (x : ℝ) :
    (ruled p rules : Solution H R Payload).chosenAt w lookahead n r β k = some x
      ↔ ∃ s b,
        rules.reading (w.host r)
            (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
              ++ [w.askedEvent r β]) r k = some s
        ∧ dueEdge p rules w lookahead q share nominal b ≤ s
        ∧ s < dueEdge p rules w lookahead q share nominal (b + 1)
        ∧ A w.sender (w.host r) (w.source.handed b) < (w.speaker r).asked β
        ∧ x = w.source.first b + (s - dueEdge p rules w lookahead q share nominal b)
              / dueSlope p rules w lookahead q share nominal b - rules.back := by
  have hnext := Solution.askedNext_of_earliest _ w lookahead hE
  have htime : (ruled p rules : Solution H R Payload).eventTime w lookahead n
      = (w.speaker r).asked β :=
    Solution.handled_time w _ lookahead (Solution.handled_of_asked w _ lookahead hE)
  constructor
  · intro hx
    obtain ⟨s, b, t, hs, ⟨q', hq'⟩, hlt, -, hcov, hdue, -⟩ :=
      ruled_chosen p rules w hN.sender lookahead hr hx
    have ht : t = A w.sender (w.host r) (w.source.handed b) := by
      rw [hN.deliver] at hq'
      exact (Option.some.inj hq').symm
    obtain ⟨h1, h2⟩ := (covers_iff hcap hlev hs0 hs1 hnominal hprog b s).mp hcov
    refine ⟨s, b, hs, h1, h2, ?_, ?_⟩
    · rw [← hnext, ← ht]
      exact hlt r
    · rw [← runHeader_due hcap hlev hprog b s, ← hdue]
      ring
  · rintro ⟨s, b, hs, h1, h2, harr, hx⟩
    have hcov := (covers_iff hcap hlev hs0 hs1 hnominal hprog b s).mpr ⟨h1, h2⟩
    have hmem := runHeader_mem_headersOf (rules := rules) hN lookahead hr
      (b := b) (n := n) (by rw [htime]; exact harr)
    have hall : ∀ y ∈ headersOf (((ruled p rules : Solution H R Payload).states w lookahead
        n).views (w.host r)), ∃ c, y = (rules.runHeader p w lookahead c, w.blockLength c) := by
      intro y hy
      obtain ⟨c, hc, -⟩ := headersOf_noLoss hN lookahead hy
      exact ⟨c, hc⟩
    have hdue := dueOf_eq_of_mem hcap hlev hs0 hs1 hnominal hprog hall hmem hcov
    have hsched : rules.schedule p (w.host r)
        (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
          ++ [w.askedEvent r β])
        = headersOf (((ruled p rules : Solution H R Payload).states w lookahead n).views
          (w.host r)) := by
      unfold Rules.schedule
      rw [ite_eq_right (by rw [hN.sender]; exact hr)]
      exact headersOf_append_asked _ _ _ _ _
    unfold Solution.chosenAt
    have hplays := ruled_plays_asked p rules (w.host r)
      (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r))
      ((w.clock (w.host r)).read ((w.speaker r).asked β)) r ((w.speaker r).block β)
      ((w.speaker r).reported β) k
    have hgoal : ((rules.reading (w.host r)
          (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r β]) r k).bind
        (dueOf (rules.schedule p (w.host r)
          (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r β])))).map (· - rules.back) = some x := by
      rw [hs, hsched]
      simp only [Option.bind_some, hdue, Option.map_some]
      rw [runHeader_due hcap hlev hprog b s, hx]
    exact hplays.trans hgoal

end Unisono.Solutions.Controller
