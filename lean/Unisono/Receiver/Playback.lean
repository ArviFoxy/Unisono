/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Receiver.Packet

/-!
# Receiver: playhead movement, playback cycles, and path-delay reports

Playhead stepping (`pass`, `take`, `skip`, `new`), late-run boundedness and
restart recovery (`late_run_is_short`, `restart_stores`), device cycles
(`cycle`, `due_at`), and report/echo path-delay handling (`report`, `reported`,
`echo`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Receiver

open Unisono.Presence

variable {N M K : Std.Usize}

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

/-! ## The playhead -/

/-- Moving the playhead forward by a number of frames. It stops at the
largest index. The frames held afterwards are the held frames that are not
behind it. -/
@[step]
theorem pass_spec (r : receiver.Receiver N M K) (frames : Std.U32) :
    receiver.Receiver.pass r frames ⦃ r' =>
      r'.following = r.following ∧ r'.timeline = r.timeline
      ∧ r'.presence.base.val = min U64.max (r.presence.base.val + frames.val)
      ∧ ∀ j, Held r'.presence j ↔
          min U64.max (r.presence.base.val + frames.val) ≤ j ∧ Held r.presence j ⦄ := by
  unfold receiver.Receiver.pass presence.Presence.impl.base
  simp only [bind_ok]
  step as ⟨i, hi⟩
  have hiv : i.val = frames.val := by rw [hi]; exact U32.cast_U64_val frames
  step as ⟨target, htarget⟩
  have htv : target.val = min U64.max (r.presence.base.val + frames.val) := by
    rw [htarget, U64.saturating_add_val, hiv]
  step as ⟨p, hpb, hph⟩
  have hb : r.presence.base.val ≤ U64.max := by scalar_tac
  refine ⟨?_, ?_⟩
  · rw [hpb, htv]
    omega
  · intro j
    rw [hph j, htv]

/-- Taking the next run of frames for the device, by a receiver that follows
a timeline.

The run starts at the playhead and has at most `limit` frames, and at least
one if `limit` is not zero. Its frames are all held or all not held, as the
run says, and the frame after it is of the other kind unless the run reached
the limit. The playhead moves forward by the length of the run and stops at
the largest index, and the frames held afterwards are the held frames that
are not behind it. -/
theorem take_spec (r : receiver.Receiver N M K) (limit : Std.U32)
    (hf : r.following = true) :
    receiver.Receiver.take r limit ⦃ out =>
      out.1.first = r.presence.base
      ∧ out.1.frames.val ≤ limit.val
      ∧ (0 < limit.val → 0 < out.1.frames.val)
      ∧ (∀ k, k < out.1.frames.val →
          (Held r.presence (r.presence.base.val + k) ↔ out.1.held = true))
      ∧ (out.1.frames.val < limit.val →
          (Held r.presence (r.presence.base.val + out.1.frames.val) ↔ out.1.held = false))
      ∧ out.2.following = true ∧ out.2.timeline = r.timeline
      ∧ out.2.presence.base.val = min U64.max (r.presence.base.val + out.1.frames.val)
      ∧ ∀ j, Held out.2.presence j ↔
          min U64.max (r.presence.base.val + out.1.frames.val) ≤ j ∧ Held r.presence j ⦄ := by
  unfold receiver.Receiver.take presence.Presence.impl.base
  simp only [bind_ok, hf, ↓reduceIte]
  step as ⟨run, hrl, hrall, hrnext⟩
  split
  · rename_i hpos
    have hpos' : 0 < run.val := by scalar_tac
    step as ⟨r1, c1, c2, c3, c4⟩
    refine ⟨hrl, fun _ => hpos', fun k hk => ?_, fun hlt => ?_, c1.trans hf, c2, c3, c4⟩
    · simp [hrall k hk]
    · simpa using hrnext hlt
  · rename_i hzero
    have hzero' : run.val = 0 := by scalar_tac
    step as ⟨gap, hgl, hgall, hgnext⟩
    step as ⟨r1, c1, c2, c3, c4⟩
    refine ⟨hgl, fun hlim => ?_, fun k hk => ?_, fun hlt => ?_, c1.trans hf, c2, c3, c4⟩
    · by_contra hc
      have hg0 : gap.val = 0 := by omega
      have h1 := hgnext (by omega)
      have h2 := hrnext (by omega)
      rw [hg0] at h1
      rw [hzero'] at h2
      exact h2 h1
    · simp [hgall k hk]
    · simpa using hgnext hlt

/-- Without a timeline there is nothing to take, and nothing changes. -/
theorem take_idle (r : receiver.Receiver N M K) (limit : Std.U32)
    (hf : r.following = false) :
    receiver.Receiver.take r limit ⦃ out => out.1.frames.val = 0 ∧ out.2 = r ⦄ := by
  unfold receiver.Receiver.take presence.Presence.impl.base
  simp [hf]

/-- Moving the playhead forward to an index without giving the frames before
it to the device. The playhead is afterwards the later of where it was and
that index, so it never moves back; the number returned is how far it moved;
and the frames held afterwards are the held frames that are not behind it. A
receiver that follows no timeline does nothing. -/
theorem skip_spec (r : receiver.Receiver N M K) (target : Std.U64) :
    receiver.Receiver.skip r target ⦃ out =>
      out.2.following = r.following ∧ out.2.timeline = r.timeline
      ∧ out.1.val = out.2.presence.base.val - r.presence.base.val
      ∧ (r.following = true →
          out.2.presence.base.val = max r.presence.base.val target.val
          ∧ ∀ j, Held out.2.presence j ↔ target.val ≤ j ∧ Held r.presence j)
      ∧ (r.following = false → out.2.presence = r.presence) ⦄ := by
  unfold receiver.Receiver.skip presence.Presence.impl.base
  simp only [bind_ok]
  split
  · rename_i hf
    split
    · rename_i hle
      have hle' : target.val ≤ r.presence.base.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨trivial, trivial, by simp, fun _ => ⟨by omega, fun j => ?_⟩, fun hc => ?_⟩
      · constructor
        · intro h
          exact ⟨by have := h.1.1; omega, h⟩
        · exact fun h => h.2
      · rw [hf] at hc; cases hc
    · rename_i hgt
      have hgt' : r.presence.base.val < target.val := by scalar_tac
      step as ⟨p, hpb, hph⟩
      step as ⟨n, hn⟩
      have hnv : n.val = target.val - r.presence.base.val := by
        rw [hn]; exact U64.wrapping_sub_val _ _ (by omega)
      refine ⟨by rw [hnv, hpb]; omega, fun _ => ⟨hpb, hph⟩, fun hc => ?_⟩
      rw [hf] at hc; cases hc
  · rename_i hf
    have hf' : r.following = false := by simpa using hf
    simp only [WP.spec_ok]
    refine ⟨trivial, trivial, by simp, fun hc => ?_, fun _ => trivial⟩
    rw [hf'] at hc; cases hc

/-- A new receiver follows no timeline, binds the configured stream, and has
no pending candidate. -/
theorem new_spec (N M K : Std.Usize) (settings : receiver.Settings) :
    receiver.Receiver.new N M K settings ⦃ r =>
      r.stream = settings.stream ∧ r.following = false ∧ r.has_candidate = false
      ∧ r.silence = settings.silence ∧ r.limit = settings.limit ⦄ := by
  unfold receiver.Receiver.new player.Player.new
  step with Unisono.Presence.new_spec as ⟨p⟩
  step as ⟨e⟩
  step as ⟨a⟩
  step with Unisono.Answers.new_total as ⟨l⟩

/-! ## A receiver cannot stay behind what arrives -/

theorem freshBy_le_now (r : receiver.Receiver N M K) (t : Std.I64) :
    (freshBy r t).val ≤ t.val := by
  unfold freshBy
  split <;> scalar_tac

theorem freshBy_eq (r : receiver.Receiver N M K) (t : Std.I64) (h : r.fresh.val ≤ t.val) :
    freshBy r t = r.fresh := by
  unfold freshBy
  split
  · scalar_tac
  · rfl

/-- A packet did nothing for the receiver: every frame of it was behind the
playhead, and the receiver did not start anew at it. -/
def Useless (hd : receiver.Heard) : Prop := hd.restarted = false ∧ OnlyLate hd.marked

/-- A packet of the followed timeline on the receiver's stream is not taken
for another one, and if it did nothing for the receiver, the set time of
silence had not yet passed since a frame last arrived at or ahead of the
playhead. -/
theorem followed_packet (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64)
    (hstream : h.stream = r.stream) (hf : r.following = true) (hX : h.timeline = r.timeline) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.2.stream = r.stream ∧ out.2.following = true
      ∧ out.2.timeline = r.timeline ∧ out.2.silence = r.silence
      ∧ (Useless out.1 →
          out.2.fresh = freshBy r t
          ∧ ¬ r.silence.val ≤ (core.num.I64.saturating_sub t (freshBy r t)).val) ⦄ := by
  have hA : ¬ Adopts r h.timeline t := by
    rintro (hc | ⟨hne, -⟩)
    · rw [hf] at hc; cases hc
    · exact hne hX
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨hstr, hs, -, -, -, -, hsame⟩
  obtain ⟨-, -, f, tl, -, -, -, hres, harr, -, hfresh⟩ := hsame hstream hA hX
  refine ⟨hstr, f.trans hf, tl, hs, ?_⟩
  rintro ⟨hno, hlate⟩
  refine ⟨hfresh hno hlate, fun hsil => ?_⟩
  obtain ⟨p1, -, -, -, hall_iff, harr1⟩ := harr hno
  have hall : AllLate r.presence h.index.val h.frames.val :=
    hall_iff.mp ((onlyLate_iff harr1).mp hlate)
  have hre : Restarts r h t := ⟨hall, hsil⟩
  rw [hno] at hres
  simp [hre] at hres

/-- Takes in packets one after the other and collects what was done with
each. -/
def hear (r : receiver.Receiver N M K) :
    List (packet.Audio × Std.I64) →
      Result (List receiver.Heard × receiver.Receiver N M K)
  | [] => ok ([], r)
  | p :: rest => do
    let out ← receiver.Receiver.packet r p.1 p.2
    let later ← hear out.2 rest
    ok (out.1 :: later.1, later.2)

theorem hear_late (X : Std.U64) (t0 : ℤ) (rest : List (packet.Audio × Std.I64)) :
    ∀ r : receiver.Receiver N M K, r.following = true → r.timeline = X →
      (∀ p ∈ rest, p.1.stream = r.stream ∧ p.1.timeline = X ∧ t0 ≤ p.2.val) →
      hear r rest ⦃ out =>
        r.fresh.val ≤ t0 → (∀ hd ∈ out.1, Useless hd) →
          ∀ p ∈ rest, p.2.val < t0 + r.silence.val ⦄ := by
  induction rest with
  | nil =>
    intro r _ _ _
    simp [hear]
  | cons p rest ih =>
    intro r hf hX hall
    have hp := hall p (by simp)
    simp only [hear]
    apply WP.spec_bind (followed_packet r p.1 p.2 hp.1 hf (hp.2.1.trans hX.symm))
    rintro out ⟨hstr', hf', htl', hs', huse⟩
    apply WP.spec_bind (ih out.2 hf' (htl'.trans hX) (fun q hq => by
      have hq' := hall q (by simp [hq])
      exact ⟨hq'.1.trans hstr'.symm, hq'.2⟩))
    rintro later hlater
    simp only [WP.spec_ok]
    intro hfresh hall_useless q hq
    have hhead : Useless out.1 := hall_useless out.1 (by simp)
    obtain ⟨hfr, hnot⟩ := huse hhead
    have hsame : freshBy r p.2 = r.fresh := freshBy_eq r p.2 (by omega)
    rcases List.mem_cons.mp hq with rfl | hq'
    · rw [hsame, I64.saturating_sub_val] at hnot
      have hsil : r.silence.val ≤ 2 ^ 63 - 1 := by scalar_tac
      by_contra hcon
      apply hnot
      have : r.silence.val ≤ q.2.val - r.fresh.val := by omega
      exact le_max_of_le_right (le_min hsil this)
    · have hrest := hlater (by rw [hfr, hsame]; exact hfresh)
        (fun hd hhd => hall_useless hd (by simp [hhd])) q hq'
      rw [hs'] at hrest
      exact hrest

/-- From any state of a receiver that follows a timeline: if packets of that
timeline on its stream arrive, none before the first of them, and every one is
behind the playhead with all its frames without making the receiver start anew,
then all of them arrive within the set time of silence after the first.

Put the other way round: once that time has passed since the first packet, a
packet either has a frame at or ahead of the playhead or the receiver starts
anew at it. A playhead that is ahead of everything that arrives does not
last. -/
theorem late_run_is_short (r : receiver.Receiver N M K) (h0 : packet.Audio) (t0 : Std.I64)
    (rest : List (packet.Audio × Std.I64)) (hstream0 : h0.stream = r.stream)
    (hf : r.following = true) (hX : h0.timeline = r.timeline)
    (hall : ∀ p ∈ rest, p.1.stream = r.stream ∧ p.1.timeline = r.timeline ∧ t0.val ≤ p.2.val) :
    hear r ((h0, t0) :: rest) ⦃ out =>
      (∀ hd ∈ out.1, Useless hd) → ∀ p ∈ rest, p.2.val < t0.val + r.silence.val ⦄ := by
  simp only [hear]
  apply WP.spec_bind (followed_packet r h0 t0 hstream0 hf hX)
  rintro out ⟨hstr', hf', htl', hs', huse⟩
  apply WP.spec_bind (hear_late r.timeline t0.val rest out.2 hf' htl' (fun q hq => by
    have hq' := hall q hq
    exact ⟨hq'.1.trans hstr'.symm, hq'.2⟩))
  rintro later hlater
  simp only [WP.spec_ok]
  intro hall_useless q hq
  have hhead : Useless out.1 := hall_useless out.1 (by simp)
  obtain ⟨hfr, -⟩ := huse hhead
  have hrest := hlater (by rw [hfr]; exact freshBy_le_now r t0)
    (fun hd hhd => hall_useless hd (by simp [hhd])) q hq
  rw [hs'] at hrest
  exact hrest

/-- A receiver that starts anew at a packet holds the packet's first frame
afterwards, if it has room for a frame and the packet has one. -/
theorem restart_stores (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64)
    (hstream : h.stream = r.stream) (hf : r.following = true) (hX : h.timeline = r.timeline)
    (hroom : 0 < widthOf N.val) (hframes : 0 < h.frames.val) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.1.restarted = true → 0 < out.1.marked.stored.val ⦄ := by
  have hA : ¬ Adopts r h.timeline t := by
    rintro (hc | ⟨hne, -⟩)
    · rw [hf] at hc; cases hc
    · exact hne hX
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨-, -, -, -, -, -, hsame⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hnew, -⟩ := hsame hstream hA hX
  intro hre
  obtain ⟨p0, hb, hempty, harr⟩ := hnew hre
  exact harr.stored_pos (by rw [hb]) hempty hroom hframes

/-! ## A cycle of the device -/

/-- Taking queued schedules into use when the position due has reached them
changes only the schedules. -/
@[step]
theorem reached_spec (r : receiver.Receiver N M K) (schedule : timing.Schedule)
    (now : timing.Position) (first : Std.I64) :
    receiver.Receiver.reached r schedule now first ⦃ out =>
      SameStream out.2 r ∧ out.2.path = r.path ∧ out.2.clock = r.clock
      ∧ out.2.arrived = r.arrived ∧ out.2.player = r.player ∧ out.2.identity = r.identity
      ∧ out.2.reports = r.reports ∧ out.2.departures = r.departures
      ∧ out.2.answers = r.answers ⦄ := by
  unfold receiver.Receiver.reached
  cases r.next with
  | none => simp [SameStream]
  | some next =>
    simp only
    split
    · step as ⟨r1, hsame1, hp1, hc1, ha1, hpl1, hid1, hrep1, hdep1, hans1⟩
      step as ⟨o⟩
      cases o with
      | none =>
        simpa using ⟨hsame1, hp1, hc1, ha1, hpl1, hid1, hrep1, hdep1, hans1⟩
      | some turned =>
        simp only
        cases r1.next with
        | none =>
          simpa using ⟨hsame1, hp1, hc1, ha1, hpl1, hid1, hrep1, hdep1, hans1⟩
        | some next1 =>
          simp only
          split
          · step as ⟨r2, hsame2, hp2, hc2, ha2, hpl2, hid2, hrep2, hdep2, hans2⟩
            step as ⟨o1⟩
            cases o1 <;>
              simpa using
                ⟨hsame2.trans hsame1, hp2.trans hp1, hc2.trans hc1, ha2.trans ha1,
                  hpl2.trans hpl1, hid2.trans hid1, hrep2.trans hrep1, hdep2.trans hdep1,
                  hans2.trans hans1⟩
          · simpa using ⟨hsame1, hp1, hc1, ha1, hpl1, hid1, hrep1, hdep1, hans1⟩
    · simp [SameStream]

/-- Asking which position is due at a time returns for every state and every
time. -/
theorem due_at_total (r : receiver.Receiver N M K) (time : Std.I64) :
    receiver.Receiver.due_at r time ⦃ _ => True ⦄ := by
  unfold receiver.Receiver.due_at relation.Estimator.impl.line
  split
  · simp only [bind_ok]
    cases r.clock.line with
    | none => simp
    | some line =>
      simp only
      cases r.schedule with
      | none => simp
      | some schedule =>
        simp only
        step as ⟨first⟩
        step as ⟨o⟩
  · simp

/-- Planning a cycle of the device returns for every state and every reading
of the clock, and changes only the schedules and the regulator: every other
field of the receiver stays as it was. -/
theorem cycle_spec (r : receiver.Receiver N M K) (time duration : Std.I64)
    (frames : Std.U32) :
    receiver.Receiver.cycle r time duration frames ⦃ out =>
      SameStream out.2 r ∧ out.2.path = r.path ∧ out.2.clock = r.clock
      ∧ out.2.arrived = r.arrived ∧ out.2.identity = r.identity
      ∧ out.2.reports = r.reports ∧ out.2.departures = r.departures
      ∧ out.2.answers = r.answers ⦄ := by
  unfold receiver.Receiver.cycle relation.Estimator.impl.line
  split
  · simp only [bind_ok]
    cases r.clock.line with
    | none => simp [SameStream]
    | some line =>
      simp only
      cases r.schedule with
      | none => simp [SameStream]
      | some schedule =>
        simp only
        step as ⟨first⟩
        step as ⟨i, hi⟩
        step as ⟨last⟩
        step as ⟨o1⟩
        cases o1 with
        | none => simp [SameStream]
        | some now =>
          simp only
          step as ⟨o2, r1, hsame, hp, hc, ha, _, hid, hrep, hdep, hans⟩
          cases o2 with
          | none =>
            simpa using ⟨hsame, hp, hc, ha, hid, hrep, hdep, hans⟩
          | some turned =>
            obtain ⟨schedule1, now1⟩ := turned
            simp only
            step as ⟨o3⟩
            cases o3 with
            | none =>
              simpa using ⟨hsame, hp, hc, ha, hid, hrep, hdep, hans⟩
            | some later =>
              simp only
              step as ⟨out⟩
              simpa using ⟨hsame, hp, hc, ha, hid, hrep, hdep, hans⟩
  · simp [SameStream]

/-! ## Reports and the delay of the path -/

/-- Making a report changes nothing about the timeline that is followed or
the frames that are held. A receiver that follows no timeline makes none; one
that does stamps its configured stream and numbers its reports one after the
other. -/
theorem report_spec (r : receiver.Receiver N M K) :
    receiver.Receiver.report r ⦃ out =>
      SameStream out.2 r
      ∧ (r.following = false → out.1 = none)
      ∧ (r.following = true →
          out.1 = some ⟨r.stream, r.timeline, r.identity, r.reports⟩) ⦄ := by
  unfold receiver.Receiver.report
  split
  · rename_i hf
    step as ⟨next⟩
    simp [SameStream, hf]
  · rename_i hf
    simp [SameStream, hf]

/-- Taking in when a report left changes nothing about the timeline that is
followed or the frames that are held. -/
theorem reported_spec (r : receiver.Receiver N M K) (sequence : Std.U64)
    (departure : Std.I64) :
    receiver.Receiver.reported r sequence departure ⦃ r' => SameStream r' r ⦄ := by
  unfold receiver.Receiver.reported
  step as ⟨a⟩
  simp [SameStream]

@[step]
theorem halved_total (both : Std.I64) : receiver.halved both ⦃ _ => True ⦄ := by
  unfold receiver.halved
  run

/-- Taking in the sender's answer to a report returns for every state and
every answer, and changes nothing about the timeline that is followed or the
frames that are held: only what is known about the delay of the path. -/
theorem echo_spec (r : receiver.Receiver N M K) (echo : packet.Echo) :
    receiver.Receiver.echo r echo ⦃ r' => SameStream r' r ⦄ := by
  unfold receiver.Receiver.echo relation.Estimator.impl.line
  split
  · split
    · simp [SameStream]
    · split
      · simp [SameStream]
      · step as ⟨o⟩
        cases o with
        | none => simp [SameStream]
        | some departure =>
          simp only
          cases r.clock.line with
          | none => simp [SameStream]
          | some forward =>
            simp only
            step with Unisono.Answers.observe_total as ⟨l⟩
            step with Unisono.Answers.shortest_total as ⟨o2⟩
            cases o2 with
            | none => simp [SameStream]
            | some smallest =>
              simp only
              step as ⟨i1⟩
              simp [SameStream]
  · simp [SameStream]

/-- An echo belonging to another stream is ignored without changing any state. -/
theorem wrong_stream_echo_noop (r : receiver.Receiver N M K) (echo : packet.Echo)
    (hdiff : echo.stream ≠ r.stream) :
    receiver.Receiver.echo r echo ⦃ r' => r' = r ⦄ := by
  unfold receiver.Receiver.echo
  split
  · have hne : (echo.stream != r.stream) = true := by simpa using hdiff
    simp [hne]
  · simp

end Unisono.Receiver
