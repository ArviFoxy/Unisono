/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Arrivals
public import Unisono.Presence
public import Unisono.Relation

/-!
# The receiver of a stream

What the functions of `unisono_core::receiver` do to the timeline a receiver
follows, to the frames it holds and to its playhead. The statements hold for
every state of the receiver: none assumes that the state was reached by the
receiver's own functions.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Receiver

open Unisono.Presence

variable {N M K : Std.Usize}

/-- Two states of a receiver agree in the timeline they follow, in when they
last heard it, in their settings and in the frames they hold. They may differ
in the estimate of the sender's clock, in the arrivals they keep and in the
schedule. -/
def SameStream (a b : receiver.Receiver N M K) : Prop :=
  a.following = b.following ∧ a.timeline = b.timeline ∧ a.heard = b.heard
  ∧ a.silence = b.silence ∧ a.limit = b.limit ∧ a.presence = b.presence

theorem SameStream.refl (a : receiver.Receiver N M K) : SameStream a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameStream.trans {a b c : receiver.Receiver N M K} (h1 : SameStream a b)
    (h2 : SameStream b c) : SameStream a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6⟩

/-! ## What a packet says about the sender's clock -/

@[step]
theorem span_of_total (h : packet.Audio) : receiver.span_of h ⦃ _ => True ⦄ := by
  unfold receiver.span_of
  step*

@[step]
theorem estimator_new_total (M : Std.Usize) (span limit : Std.I64) :
    relation.Estimator.new M span limit ⦃ _ => True ⦄ := by
  unfold relation.Estimator.new
  simp

@[step]
theorem arrivals_new_total (K : Std.Usize) : arrivals.Arrivals.new K ⦃ _ => True ⦄ := by
  unfold arrivals.Arrivals.new
  simp

@[step]
theorem remember_total (e : relation.Estimator M) (span : Std.I64) :
    relation.Estimator.remember e span ⦃ _ => True ⦄ := by
  unfold relation.Estimator.remember
  simp

@[step]
theorem stamped_arrival_total (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.stamped_arrival r h ⦃ _ => True ⦄ := by
  unfold receiver.Receiver.stamped_arrival
  step*

/-- Giving the estimate a sample changes the estimate and nothing else. -/
@[step]
theorem sample_spec (r : receiver.Receiver N M K) (h : packet.Audio) (arrived : Std.I64) :
    receiver.Receiver.sample r h arrived ⦃ r' =>
      SameStream r' r ∧ r'.arrivals = r.arrivals ∧ r'.schedule = r.schedule ⦄ := by
  unfold receiver.Receiver.sample
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨o, ho⟩
  step as ⟨window, hwindow⟩
  step with Unisono.Relation.observe_total as ⟨e⟩
  simp [SameStream]

/-- Taking the clock measurement from a packet changes the estimate of the
sender's clock and the kept arrivals, and nothing else. -/
@[step]
theorem measure_spec (r : receiver.Receiver N M K) (h : packet.Audio) (arrival : Std.I64) :
    receiver.Receiver.measure r h arrival ⦃ r' =>
      SameStream r' r ∧ r'.schedule = r.schedule ⦄ := by
  unfold receiver.Receiver.measure
  step as ⟨i⟩
  step as ⟨e⟩
  step as ⟨o⟩
  cases o with
  | none =>
    simp only [bind_ok]
    step as ⟨a⟩
    simp [SameStream]
  | some arrived =>
    simp only
    step as ⟨r1, hsame, harr, hsched⟩
    step as ⟨a⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsame
    simp only [SameStream]
    exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, hsched⟩

/-- Keeping what a packet says about when frames are due changes the schedule
and nothing else. -/
@[step]
theorem note_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.note r h ⦃ r' => SameStream r' r ⦄ := by
  unfold receiver.Receiver.note
  cases r.schedule with
  | none => simp [SameStream]
  | some s =>
    simp only [bind_ok, Std.uncurry]
    split <;> simp [SameStream]

/-! ## Which timeline is followed -/

/-- The time at which a receiver last heard its timeline, put right against
the clock: it is not later than now. -/
def heardBy (r : receiver.Receiver N M K) (t : Std.I64) : Std.I64 :=
  if r.heard > t then t else r.heard

/-- Whether a receiver whose state has these parts takes up the timeline of a
packet: it follows no timeline, or the packet's timeline is another one and
either it is later or the followed one has been silent for the set time. -/
def AdoptsAt (following : Bool) (followed : Std.U64) (heard silence : Std.I64)
    (timeline : Std.U64) (t : Std.I64) : Prop :=
  following = false
  ∨ (timeline ≠ followed
      ∧ (followed.val < timeline.val
        ∨ silence.val ≤ (core.num.I64.saturating_sub t heard).val))

instance (following : Bool) (followed : Std.U64) (heard silence : Std.I64)
    (timeline : Std.U64) (t : Std.I64) :
    Decidable (AdoptsAt following followed heard silence timeline t) := by
  unfold AdoptsAt; infer_instance

/-- Whether a packet of `timeline` that arrives at `t` makes the receiver
take up that timeline. -/
def Adopts (r : receiver.Receiver N M K) (timeline : Std.U64) (t : Std.I64) : Prop :=
  AdoptsAt r.following r.timeline (heardBy r t) r.silence timeline t

instance (r : receiver.Receiver N M K) (timeline : Std.U64) (t : Std.I64) :
    Decidable (Adopts r timeline t) := by
  unfold Adopts; infer_instance

@[step]
theorem adopts_spec (r : receiver.Receiver N M K) (timeline : Std.U64) (t : Std.I64) :
    receiver.Receiver.adopts r timeline t ⦃ b =>
      b = decide (AdoptsAt r.following r.timeline r.heard r.silence timeline t) ⦄ := by
  unfold receiver.Receiver.adopts
  split
  · rename_i hf
    split
    · rename_i heq
      simp [AdoptsAt, hf, heq]
    · rename_i hne
      split
      · rename_i hgt
        have : r.timeline.val < timeline.val := by scalar_tac
        simp [AdoptsAt, hf, hne, this]
      · rename_i hle
        have : ¬ r.timeline.val < timeline.val := by scalar_tac
        step as ⟨i, hi⟩
        have hiff : i ≥ r.silence
            ↔ AdoptsAt r.following r.timeline r.heard r.silence timeline t := by
          unfold AdoptsAt
          rw [← hi]
          constructor
          · intro hge
            exact Or.inr ⟨hne, Or.inr (by scalar_tac)⟩
          · rintro (hnf | ⟨-, hlt | hsil⟩)
            · rw [hf] at hnf; cases hnf
            · exact absurd hlt this
            · scalar_tac
        simp [hiff]
  · rename_i hf
    simp [AdoptsAt, hf]

/-- Taking up the timeline of a packet: the receiver follows it, holds
nothing, and has its playhead at the packet's first frame. -/
@[step]
theorem adopt_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.adopt r h ⦃ r' =>
      r'.following = true ∧ r'.timeline = h.timeline ∧ r'.heard = r.heard
      ∧ r'.silence = r.silence ∧ r'.limit = r.limit
      ∧ r'.presence.base = h.index ∧ ∀ j, ¬ Held r'.presence j ⦄ := by
  unfold receiver.Receiver.adopt
  step as ⟨p, hpb, hph⟩
  step as ⟨i⟩
  step as ⟨e⟩
  step as ⟨a⟩
  exact ⟨hpb, hph⟩

/-- Taking in a packet of the followed timeline: its frames arrive, and the
time at which the timeline was last heard is now. -/
@[step]
theorem accept_spec (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64)
    (adopted : Bool) :
    receiver.Receiver.accept r h t adopted ⦃ out =>
      out.1.ignored = false ∧ out.1.adopted = adopted
      ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline ∧ out.2.heard = t
      ∧ out.2.silence = r.silence ∧ out.2.limit = r.limit
      ∧ Arrived r.presence h.index.val h.frames.val out.2.presence out.1.marked ⦄ := by
  unfold receiver.Receiver.accept
  step as ⟨r1, hs1, hsched1⟩
  step as ⟨r2, hs2⟩
  step as ⟨i, hi⟩
  have hiv : i.val = h.frames.val := by rw [hi]; exact U16.cast_U32_val h.frames
  step as ⟨marked, p, harr⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hs1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hs2
  simp only at a1 a2 a3 a4 a5 a6
  refine ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, ?_⟩
  rw [b6, a6, hiv] at harr
  exact harr

/-- What a receiver does with a packet, in three cases.

It takes up the packet's timeline: then it follows that timeline, held nothing
of it before this packet, and has heard it now. Or the packet is of another
timeline than the followed one and is not taken up: then nothing changes but
the correction of the time last heard. Or the packet is of the followed
timeline: then its frames arrive and the timeline has been heard now.

The settings never change. -/
theorem packet_spec (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.2.silence = r.silence ∧ out.2.limit = r.limit
      ∧ (Adopts r h.timeline t →
          out.1.adopted = true ∧ out.1.ignored = false
          ∧ out.2.following = true ∧ out.2.timeline = h.timeline ∧ out.2.heard = t
          ∧ ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
              ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1.marked)
      ∧ (¬ Adopts r h.timeline t → h.timeline ≠ r.timeline →
          out.1.adopted = false ∧ out.1.ignored = true
          ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline
          ∧ out.2.heard = heardBy r t ∧ out.2.presence = r.presence)
      ∧ (¬ Adopts r h.timeline t → h.timeline = r.timeline →
          out.1.adopted = false ∧ out.1.ignored = false
          ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline ∧ out.2.heard = t
          ∧ Arrived r.presence h.index.val h.frames.val out.2.presence out.1.marked) ⦄ := by
  unfold receiver.Receiver.packet
  have hheard : (if r.heard > t then ok t else ok r.heard) = ok (heardBy r t) := by
    unfold heardBy
    split <;> rfl
  rw [hheard]
  step as ⟨adopted, hadopted⟩
  have hiff : adopted = true ↔ Adopts r h.timeline t := by
    rw [hadopted]
    simp [Adopts]
  split
  · rename_i hyes
    have hA : Adopts r h.timeline t := hiff.mp hyes
    step as ⟨r1, c1, c2, c3, c4, c5, c6, c7⟩
    step as ⟨out, d1, d2, d3, d4, d5, d6, d7, d8⟩
    refine ⟨d6.trans c4, d7.trans c5, fun _ => ?_, fun hno => absurd hA hno,
      fun hno => absurd hA hno⟩
    exact ⟨d2.trans hyes, d1, d3.trans c1, d4.trans c2, d5, r1.presence, c6, c7, d8⟩
  · rename_i hno
    have hA : ¬ Adopts r h.timeline t := fun hc => hno (hiff.mpr hc)
    split
    · rename_i hne
      have hne' : h.timeline ≠ r.timeline := by simpa using hne
      simp only [WP.spec_ok]
      refine ⟨trivial, trivial, fun hc => absurd hc hA, fun _ _ => ?_,
        fun _ heq => absurd heq hne'⟩
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    · rename_i heq
      have heq' : h.timeline = r.timeline := by
        have : ¬ h.timeline ≠ r.timeline := by simpa using heq
        exact not_not.mp this
      step as ⟨out, d1, d2, d3, d4, d5, d6, d7, d8⟩
      have had : adopted = false := by simpa using hno
      refine ⟨d6, d7, fun hc => absurd hc hA, fun _ hne => absurd heq' hne, fun _ _ => ?_⟩
      exact ⟨d2.trans had, d1, d3, d4, d5, d8⟩

/-! ## Following the packets that arrive, from any state -/

theorem heardBy_le_now (r : receiver.Receiver N M K) (t : Std.I64) :
    (heardBy r t).val ≤ t.val := by
  unfold heardBy
  split <;> scalar_tac

theorem heardBy_eq (r : receiver.Receiver N M K) (t : Std.I64) (h : r.heard.val ≤ t.val) :
    heardBy r t = r.heard := by
  unfold heardBy
  split
  · scalar_tac
  · rfl

/-- The receiver follows timeline `X`, or it follows a later timeline that it
last heard at `t0` or before. -/
def Toward (X : Std.U64) (t0 : ℤ) (r : receiver.Receiver N M K) : Prop :=
  r.following = true ∧ (r.timeline = X ∨ (X.val < r.timeline.val ∧ r.heard.val ≤ t0))

/-- After a packet, whatever the state before: the receiver follows the
packet's timeline, or a later one that it has not heard since before the
packet. -/
theorem first_packet (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64) :
    receiver.Receiver.packet r h t ⦃ out =>
      Toward h.timeline t.val out.2 ∧ out.2.silence = r.silence ⦄ := by
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨hs, -, hyes, hother, hsame⟩
  refine ⟨?_, hs⟩
  by_cases hA : Adopts r h.timeline t
  · obtain ⟨-, -, f, tl, -⟩ := hyes hA
    exact ⟨f, Or.inl tl⟩
  · have hf : r.following = true := by
      by_contra hc
      exact hA (Or.inl (by simpa using hc))
    by_cases hne : h.timeline = r.timeline
    · obtain ⟨-, -, f, tl, -⟩ := hsame hA hne
      exact ⟨f.trans hf, Or.inl (tl.trans hne.symm)⟩
    · obtain ⟨-, -, f, tl, hh, -⟩ := hother hA hne
      refine ⟨f.trans hf, Or.inr ⟨?_, ?_⟩⟩
      · rw [tl]
        have hnlt : ¬ r.timeline.val < h.timeline.val :=
          fun hlt => hA (Or.inr ⟨hne, Or.inl hlt⟩)
        have hneq : h.timeline.val ≠ r.timeline.val :=
          fun hv => hne (UScalar.eq_of_val_eq hv)
        omega
      · rw [hh]
        exact heardBy_le_now r t

/-- A later packet of timeline `X`, at a time not before `t0`: the receiver
stays on its way to `X`, and it follows `X` if it did already or if the set
time of silence has passed since `t0`. -/
theorem later_packet (X : Std.U64) (t0 : ℤ) (r : receiver.Receiver N M K) (h : packet.Audio)
    (t : Std.I64) (hT : Toward X t0 r) (hX : h.timeline = X) (ht : t0 ≤ t.val) :
    receiver.Receiver.packet r h t ⦃ out =>
      Toward X t0 out.2 ∧ out.2.silence = r.silence
      ∧ (r.timeline = X → out.2.timeline = X)
      ∧ (t0 + r.silence.val ≤ t.val → out.2.timeline = X) ⦄ := by
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨hs, -, hyes, hother, hsame⟩
  obtain ⟨hf, hway⟩ := hT
  by_cases hA : Adopts r h.timeline t
  · obtain ⟨-, -, f, tl, -⟩ := hyes hA
    have htl : out.2.timeline = X := tl.trans hX
    exact ⟨⟨f, Or.inl htl⟩, hs, fun _ => htl, fun _ => htl⟩
  · by_cases hne : h.timeline = r.timeline
    · obtain ⟨-, -, f, tl, -⟩ := hsame hA hne
      have htl : out.2.timeline = X := tl.trans (hne.symm.trans hX)
      exact ⟨⟨f.trans hf, Or.inl htl⟩, hs, fun _ => htl, fun _ => htl⟩
    · obtain ⟨-, -, f, tl, hh, -⟩ := hother hA hne
      have hnX : r.timeline ≠ X := fun hc => hne (hX.trans hc.symm)
      rcases hway with hc | ⟨hlt, hheard⟩
      · exact absurd hc hnX
      · have hsame_heard : heardBy r t = r.heard := heardBy_eq r t (by omega)
        refine ⟨⟨f.trans hf, Or.inr ⟨by rw [tl]; exact hlt, by rw [hh, hsame_heard]; exact hheard⟩⟩,
          hs, fun hc => absurd hc hnX, fun hlate => ?_⟩
        exfalso
        apply hA
        refine Or.inr ⟨hne, Or.inr ?_⟩
        rw [hsame_heard, I64.saturating_sub_val]
        have hsil : r.silence.val ≤ 2 ^ 63 - 1 := by scalar_tac
        have : r.silence.val ≤ t.val - r.heard.val := by omega
        exact le_max_of_le_right (le_min hsil this)

/-- Takes in packets one after the other. -/
def feed (r : receiver.Receiver N M K) :
    List (packet.Audio × Std.I64) → Result (receiver.Receiver N M K)
  | [] => ok r
  | p :: rest => do
    let out ← receiver.Receiver.packet r p.1 p.2
    feed out.2 rest

theorem feed_toward (X : Std.U64) (t0 : ℤ) (rest : List (packet.Audio × Std.I64)) :
    ∀ r : receiver.Receiver N M K, Toward X t0 r →
      (∀ p ∈ rest, p.1.timeline = X ∧ t0 ≤ p.2.val) →
      feed r rest ⦃ r' =>
        r'.following = true
        ∧ ((r.timeline = X ∨ ∃ p ∈ rest, t0 + r.silence.val ≤ p.2.val) →
            r'.timeline = X) ⦄ := by
  induction rest with
  | nil =>
    intro r hT _
    simp only [feed, WP.spec_ok]
    refine ⟨hT.1, ?_⟩
    rintro (h | ⟨p, hp, -⟩)
    · exact h
    · simp at hp
  | cons p rest ih =>
    intro r hT hall
    have hp := hall p (by simp)
    simp only [feed]
    apply WP.spec_bind (later_packet X t0 r p.1 p.2 hT hp.1 hp.2)
    rintro out ⟨hT', hs, hstay, hlate⟩
    apply WP.spec_mono (ih out.2 hT' (fun q hq => hall q (by simp [hq])))
    rintro r' ⟨hf, himp⟩
    refine ⟨hf, ?_⟩
    rintro (h | ⟨q, hq, hql⟩)
    · exact himp (Or.inl (hstay h))
    · rcases List.mem_cons.mp hq with rfl | hq'
      · exact himp (Or.inl (hlate hql))
      · exact himp (Or.inr ⟨q, hq', by rw [hs]; exact hql⟩)

/-- From any state, a receiver that is sent packets of one timeline follows
that timeline once a packet arrives after the set time of silence, counted
from the first of them, and it goes on following it.

`r` is any state at all. The packets after the first are of the same timeline
and do not arrive before the first, and one of them arrives when the time of
silence has passed. -/
theorem follows_after_silence (r : receiver.Receiver N M K) (h0 : packet.Audio)
    (t0 : Std.I64) (rest : List (packet.Audio × Std.I64))
    (hall : ∀ p ∈ rest, p.1.timeline = h0.timeline ∧ t0.val ≤ p.2.val)
    (hlate : ∃ p ∈ rest, t0.val + r.silence.val ≤ p.2.val) :
    feed r ((h0, t0) :: rest) ⦃ r' =>
      r'.following = true ∧ r'.timeline = h0.timeline ⦄ := by
  simp only [feed]
  apply WP.spec_bind (first_packet r h0 t0)
  rintro out ⟨hT, hs⟩
  apply WP.spec_mono (feed_toward h0.timeline t0.val rest out.2 hT hall)
  rintro r' ⟨hf, himp⟩
  obtain ⟨p, hp, hpl⟩ := hlate
  exact ⟨hf, himp (Or.inr ⟨p, hp, by rw [hs]; exact hpl⟩)⟩

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

/-- A new receiver follows no timeline. -/
theorem new_spec (N M K : Std.Usize) (silence limit : Std.I64) :
    receiver.Receiver.new N M K silence limit ⦃ r =>
      r.following = false ∧ r.silence = silence ∧ r.limit = limit ⦄ := by
  unfold receiver.Receiver.new
  step with Unisono.Presence.new_spec as ⟨p⟩
  step as ⟨e⟩
  step as ⟨a⟩

end Unisono.Receiver
