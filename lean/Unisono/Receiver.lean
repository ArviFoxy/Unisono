/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import UnisonoCore
public import Unisono.Scalar
public import Unisono.Arrivals
public import Unisono.Player
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
last heard it and last had a frame that was not behind the playhead, in their
settings and in the frames they hold. They may differ in the estimate of the
sender's clock, in the arrivals they keep, in the schedule and in the
regulator. -/
def SameStream (a b : receiver.Receiver N M K) : Prop :=
  a.following = b.following ∧ a.timeline = b.timeline ∧ a.heard = b.heard
  ∧ a.fresh = b.fresh ∧ a.silence = b.silence ∧ a.limit = b.limit
  ∧ a.presence = b.presence

theorem SameStream.refl (a : receiver.Receiver N M K) : SameStream a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameStream.trans {a b c : receiver.Receiver N M K} (h1 : SameStream a b)
    (h2 : SameStream b c) : SameStream a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7⟩

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
      SameStream r' r ∧ r'.arrived = r.arrived ∧ r'.schedule = r.schedule ⦄ := by
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
  step as ⟨e1⟩
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
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hsame
    simp only [SameStream]
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hsched⟩

/-- Keeping what a packet says about when frames are due changes the schedule
and nothing else. -/
@[step]
theorem note_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.note r h ⦃ r' => SameStream r' r ⦄ := by
  unfold receiver.Receiver.note
  simp [SameStream]

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
      ∧ r'.fresh = r.fresh ∧ r'.silence = r.silence ∧ r'.limit = r.limit
      ∧ r'.presence.base = h.index ∧ ∀ j, ¬ Held r'.presence j ⦄ := by
  unfold receiver.Receiver.adopt
  step as ⟨p, hpb, hph⟩
  step as ⟨i⟩
  step as ⟨e⟩
  step as ⟨a⟩
  step with Unisono.Player.stop_total as ⟨p1⟩
  step as ⟨e1⟩
  exact ⟨hpb, hph⟩

/-! ## A playhead that is ahead of everything that arrives -/

/-- The time at which a receiver last had a frame at or ahead of its playhead,
put right against the clock: it is not later than now. -/
def freshBy (r : receiver.Receiver N M K) (t : Std.I64) : Std.I64 :=
  if r.fresh > t then t else r.fresh

/-- Every frame of a packet was behind the playhead, and it had a frame. -/
def OnlyLate (m : presence.Marked) : Prop :=
  m.late.val ≠ 0 ∧ m.stored.val = 0 ∧ m.duplicate.val = 0 ∧ m.early.val = 0

instance (m : presence.Marked) : Decidable (OnlyLate m) := by
  unfold OnlyLate; infer_instance

/-- Every frame of the packet of `d` frames from index `first` on lies before
the stretch, and it has a frame. -/
def AllLate (p : presence.Presence N) (first d : ℕ) : Prop :=
  countOf p first d presence.Outcome.Late ≠ 0
  ∧ countOf p first d presence.Outcome.Stored = 0
  ∧ countOf p first d presence.Outcome.Duplicate = 0
  ∧ countOf p first d presence.Outcome.Early = 0

instance (p : presence.Presence N) (first d : ℕ) : Decidable (AllLate p first d) := by
  unfold AllLate; infer_instance

theorem onlyLate_iff {p s : presence.Presence N} {first d : ℕ} {m : presence.Marked}
    (h : Arrived p first d s m) : OnlyLate m ↔ AllLate p first d := by
  obtain ⟨-, -, h1, h2, h3, h4⟩ := h
  unfold OnlyLate AllLate
  rw [h1, h2, h3, h4]

/-- The packet shows that the playhead is wrong: all its frames are behind
the playhead, and no packet has had a frame at or ahead of it for the set
time. The receiver then starts anew at this packet. -/
def Restarts (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64) : Prop :=
  AllLate r.presence h.index.val h.frames.val
  ∧ r.silence.val ≤ (core.num.I64.saturating_sub t (freshBy r t)).val

instance (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64) :
    Decidable (Restarts r h t) := by
  unfold Restarts; infer_instance

@[step]
theorem stale_spec (r : receiver.Receiver N M K) (m : presence.Marked) (t : Std.I64) :
    receiver.Receiver.stale r m t ⦃ out =>
      out.1 = decide (OnlyLate m
        ∧ r.silence.val ≤ (core.num.I64.saturating_sub t (freshBy r t)).val)
      ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline
      ∧ out.2.heard = r.heard ∧ out.2.fresh = freshBy r t ∧ out.2.silence = r.silence
      ∧ out.2.limit = r.limit ∧ out.2.presence = r.presence
      ∧ out.2.player = r.player ⦄ := by
  unfold receiver.Receiver.stale
  have hfresh : (if r.fresh > t then ok t else ok r.fresh) = ok (freshBy r t) := by
    unfold freshBy
    split <;> rfl
  rw [hfresh]
  simp only [bind_ok]
  split
  · rename_i h0
    have : m.late.val = 0 := by scalar_tac
    simp [OnlyLate, this]
  · rename_i h0
    have hl : m.late.val ≠ 0 := by scalar_tac
    split
    · rename_i h1
      have : m.stored.val ≠ 0 := by scalar_tac
      simp [OnlyLate, this]
    · rename_i h1
      have hs : m.stored.val = 0 := by scalar_tac
      split
      · rename_i h2
        have : m.duplicate.val ≠ 0 := by scalar_tac
        simp [OnlyLate, this]
      · rename_i h2
        have hd : m.duplicate.val = 0 := by scalar_tac
        split
        · rename_i h3
          have : m.early.val ≠ 0 := by scalar_tac
          simp [OnlyLate, this]
        · rename_i h3
          have he : m.early.val = 0 := by scalar_tac
          step as ⟨i, hi⟩
          have hiff : i ≥ r.silence ↔ (OnlyLate m
              ∧ r.silence.val ≤ (core.num.I64.saturating_sub t (freshBy r t)).val) := by
            rw [← hi]
            constructor
            · intro hge
              exact ⟨⟨hl, hs, hd, he⟩, by scalar_tac⟩
            · rintro ⟨-, hge⟩
              scalar_tac
          simp [hiff]

/-- Starting anew at a packet: the playhead is at the packet's first frame and
nothing but the packet's frames is held. -/
@[step]
theorem renew_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.renew r h ⦃ out =>
      out.2.following = r.following ∧ out.2.timeline = r.timeline
      ∧ out.2.heard = r.heard ∧ out.2.fresh = r.fresh ∧ out.2.silence = r.silence
      ∧ out.2.limit = r.limit
      ∧ ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
          ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1 ⦄ := by
  unfold receiver.Receiver.renew
  step as ⟨p, hpb, hph⟩
  step with Unisono.Player.stop_total as ⟨p1⟩
  step as ⟨i, hi⟩
  have hiv : i.val = h.frames.val := by rw [hi]; exact U16.cast_U32_val h.frames
  step as ⟨m, p2, harr⟩
  rw [hiv] at harr
  exact ⟨p, hpb, hph, harr⟩

/-- Taking in how a packet's frames were marked: a packet with a frame at or
ahead of the playhead makes now the time at which such a frame last arrived,
and any other packet leaves that time as it was. -/
@[step]
theorem refresh_spec (r : receiver.Receiver N M K) (h : packet.Audio) (m : presence.Marked)
    (t : Std.I64) :
    receiver.Receiver.refresh r h m t ⦃ r' =>
      r'.following = r.following ∧ r'.timeline = r.timeline ∧ r'.heard = r.heard
      ∧ r'.silence = r.silence ∧ r'.limit = r.limit ∧ r'.presence = r.presence
      ∧ (r'.fresh = t ∨ r'.fresh = r.fresh)
      ∧ (m.stored.val = 0 → m.duplicate.val = 0 → m.early.val = 0 →
          r'.fresh = r.fresh) ⦄ := by
  unfold receiver.Receiver.refresh
  split
  · rename_i h1
    have : m.stored.val ≠ 0 := by scalar_tac
    step as ⟨r1, hs⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hs
    exact ⟨a1, a2, a3, a5, a6, a7, Or.inl a4, fun h0 => absurd h0 this⟩
  · split
    · rename_i h1 h2
      have : m.duplicate.val ≠ 0 := by scalar_tac
      step as ⟨r1, hs⟩
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hs
      exact ⟨a1, a2, a3, a5, a6, a7, Or.inl a4, fun _ h0 => absurd h0 this⟩
    · split
      · rename_i h1 h2 h3
        have : m.early.val ≠ 0 := by scalar_tac
        simp only [WP.spec_ok]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, Or.inl trivial,
          fun _ _ h0 => absurd h0 this⟩
      · simp

/-- Taking in a packet of the followed timeline. The timeline has been heard
now. If the packet shows that the playhead is wrong, the receiver starts anew
at it and holds the packet's frames from an empty stretch; otherwise the
packet's frames arrive at the stretch as it is. -/
@[step]
theorem accept_spec (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64)
    (adopted : Bool) :
    receiver.Receiver.accept r h t adopted ⦃ out =>
      out.1.ignored = false ∧ out.1.adopted = adopted
      ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline ∧ out.2.heard = t
      ∧ out.2.silence = r.silence ∧ out.2.limit = r.limit
      ∧ out.1.restarted = decide (Restarts r h t)
      ∧ (out.1.restarted = false →
          Arrived r.presence h.index.val h.frames.val out.2.presence out.1.marked)
      ∧ (out.1.restarted = true →
          ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
            ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1.marked)
      ∧ (out.1.restarted = false → OnlyLate out.1.marked →
          out.2.fresh = freshBy r t) ⦄ := by
  unfold receiver.Receiver.accept
  step as ⟨r1, hs1, hsched1⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hs1
  simp only at a1 a2 a3 a4 a5 a6 a7
  step as ⟨i, hi⟩
  have hiv : i.val = h.frames.val := by rw [hi]; exact U16.cast_U32_val h.frames
  step as ⟨first, p, harr⟩
  rw [a7, hiv] at harr
  step as ⟨restarted, r2, hres, b1, b2, b3, b4, b5, b6, b7, b8⟩
  have hfb : freshBy { r1 with presence := p } t = freshBy r t := by
    unfold freshBy
    simp only [a4]
  rw [hfb] at hres b4
  have hrestarts : restarted = decide (Restarts r h t) := by
    rw [hres]
    apply decide_eq_decide.mpr
    unfold Restarts
    rw [onlyLate_iff harr, a5]
  cases restarted with
  | true =>
    simp only [↓reduceIte]
    step as ⟨out1, c1, c2, c3, c4, c5, c6, p0, c7, c8, c9⟩
    obtain ⟨m1, r4⟩ := out1
    simp only at c1 c2 c3 c4 c5 c6 c9 ⊢
    step as ⟨r5, d1, d2, d3, d4, d5, d6, d7, d8⟩
    refine ⟨d1.trans (c1.trans (b1.trans a1)), d2.trans (c2.trans (b2.trans a2)),
      d3.trans (c3.trans (b3.trans a3)), d4.trans (c5.trans (b5.trans a5)),
      d5.trans (c6.trans (b6.trans a6)), hrestarts, fun hc => (by cases hc), fun _ => ?_,
      fun hc => (by cases hc)⟩
    rw [d6]
    exact ⟨p0, c7, c8, c9⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    step as ⟨r5, d1, d2, d3, d4, d5, d6, d7, d8⟩
    refine ⟨d1.trans (b1.trans a1), d2.trans (b2.trans a2), d3.trans (b3.trans a3),
      d4.trans (b5.trans a5), d5.trans (b6.trans a6), hrestarts, fun _ => ?_,
      fun hc => (by cases hc), fun _ hlate => ?_⟩
    · rw [d6, b7]
      exact harr
    · obtain ⟨-, l2, l3, l4⟩ := hlate
      rw [d8 l2 l3 l4, b4]

/-- What a receiver does with a packet, in three cases.

It takes up the packet's timeline: then it follows that timeline, held nothing
of it before this packet, and has heard it now. Or the packet is of another
timeline than the followed one and is not taken up: then nothing changes but
the correction of the time last heard. Or the packet is of the followed
timeline: then the timeline has been heard now, and the packet's frames
arrive, at the stretch as it is or, if the packet shows that the playhead is
wrong, at an empty stretch that starts at the packet.

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
          ∧ out.2.heard = heardBy r t ∧ out.2.presence = r.presence
          ∧ out.2.fresh = r.fresh)
      ∧ (¬ Adopts r h.timeline t → h.timeline = r.timeline →
          out.1.adopted = false ∧ out.1.ignored = false
          ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline ∧ out.2.heard = t
          ∧ out.1.restarted = decide (Restarts r h t)
          ∧ (out.1.restarted = false →
              Arrived r.presence h.index.val h.frames.val out.2.presence out.1.marked)
          ∧ (out.1.restarted = true →
              ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
                ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1.marked)
          ∧ (out.1.restarted = false → OnlyLate out.1.marked →
              out.2.fresh = freshBy r t)) ⦄ := by
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
    step as ⟨r1, c1, c2, c3, c4, c5, c6, c7, c8⟩
    step as ⟨out, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩
    refine ⟨d6.trans c5, d7.trans c6, fun _ => ?_, fun hno => absurd hA hno,
      fun hno => absurd hA hno⟩
    refine ⟨d2.trans hyes, d1, d3.trans c1, d4.trans c2, d5, ?_⟩
    cases hre : out.1.restarted with
    | false => exact ⟨r1.presence, c7, c8, d9 hre⟩
    | true => exact d10 hre
  · rename_i hno
    have hA : ¬ Adopts r h.timeline t := fun hc => hno (hiff.mpr hc)
    split
    · rename_i hne
      have hne' : h.timeline ≠ r.timeline := by simpa using hne
      simp only [WP.spec_ok]
      refine ⟨trivial, trivial, fun hc => absurd hc hA, fun _ _ => ?_,
        fun _ heq => absurd heq hne'⟩
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    · rename_i heq
      have heq' : h.timeline = r.timeline := by
        have : ¬ h.timeline ≠ r.timeline := by simpa using heq
        exact not_not.mp this
      step as ⟨out, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩
      have had : adopted = false := by simpa using hno
      refine ⟨d6, d7, fun hc => absurd hc hA, fun _ hne => absurd heq' hne, fun _ _ => ?_⟩
      exact ⟨d2.trans had, d1, d3, d4, d5, d8, d9, d10, d11⟩

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
theorem new_spec (N M K : Std.Usize) (settings : receiver.Settings) :
    receiver.Receiver.new N M K settings ⦃ r =>
      r.following = false ∧ r.silence = settings.silence ∧ r.limit = settings.limit ⦄ := by
  unfold receiver.Receiver.new player.Player.new
  step with Unisono.Presence.new_spec as ⟨p⟩
  step as ⟨e⟩
  step as ⟨a⟩

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

/-- A packet of the followed timeline is not taken for another one, and if it
did nothing for the receiver, the set time of silence had not yet passed since
a frame last arrived at or ahead of the playhead. -/
theorem followed_packet (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64)
    (hf : r.following = true) (hX : h.timeline = r.timeline) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.2.following = true ∧ out.2.timeline = r.timeline ∧ out.2.silence = r.silence
      ∧ (Useless out.1 →
          out.2.fresh = freshBy r t
          ∧ ¬ r.silence.val ≤ (core.num.I64.saturating_sub t (freshBy r t)).val) ⦄ := by
  have hA : ¬ Adopts r h.timeline t := by
    rintro (hc | ⟨hne, -⟩)
    · rw [hf] at hc; cases hc
    · exact hne hX
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨hs, -, -, -, hsame⟩
  obtain ⟨-, -, f, tl, -, hres, harr, -, hfresh⟩ := hsame hA hX
  refine ⟨f.trans hf, tl, hs, ?_⟩
  rintro ⟨hno, hlate⟩
  refine ⟨hfresh hno hlate, fun hsil => ?_⟩
  have hall : AllLate r.presence h.index.val h.frames.val :=
    (onlyLate_iff (harr hno)).mp hlate
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
      (∀ p ∈ rest, p.1.timeline = X ∧ t0 ≤ p.2.val) →
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
    apply WP.spec_bind (followed_packet r p.1 p.2 hf (hp.1.trans hX.symm))
    rintro out ⟨hf', htl', hs', huse⟩
    apply WP.spec_bind (ih out.2 hf' (htl'.trans hX) (fun q hq => hall q (by simp [hq])))
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
timeline arrive, none before the first of them, and every one is behind the
playhead with all its frames without making the receiver start anew, then all
of them arrive within the set time of silence after the first.

Put the other way round: once that time has passed since the first packet, a
packet either has a frame at or ahead of the playhead or the receiver starts
anew at it. A playhead that is ahead of everything that arrives does not
last. -/
theorem late_run_is_short (r : receiver.Receiver N M K) (h0 : packet.Audio) (t0 : Std.I64)
    (rest : List (packet.Audio × Std.I64)) (hf : r.following = true)
    (hX : h0.timeline = r.timeline)
    (hall : ∀ p ∈ rest, p.1.timeline = r.timeline ∧ t0.val ≤ p.2.val) :
    hear r ((h0, t0) :: rest) ⦃ out =>
      (∀ hd ∈ out.1, Useless hd) → ∀ p ∈ rest, p.2.val < t0.val + r.silence.val ⦄ := by
  simp only [hear]
  apply WP.spec_bind (followed_packet r h0 t0 hf hX)
  rintro out ⟨hf', htl', hs', huse⟩
  apply WP.spec_bind (hear_late r.timeline t0.val rest out.2 hf' htl' hall)
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
    (hf : r.following = true) (hX : h.timeline = r.timeline)
    (hroom : 0 < widthOf N.val) (hframes : 0 < h.frames.val) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.1.restarted = true → 0 < out.1.marked.stored.val ⦄ := by
  have hA : ¬ Adopts r h.timeline t := by
    rintro (hc | ⟨hne, -⟩)
    · rw [hf] at hc; cases hc
    · exact hne hX
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨-, -, -, -, hsame⟩
  obtain ⟨-, -, -, -, -, -, -, hnew, -⟩ := hsame hA hX
  intro hre
  obtain ⟨p0, hb, hempty, harr⟩ := hnew hre
  exact harr.stored_pos (by rw [hb]) hempty hroom hframes

/-! ## A cycle of the device -/

/-- Planning a cycle of the device returns for every state and every reading
of the clock, and changes nothing about the timeline that is followed or the
frames that are held: only the regulator moves. -/
theorem cycle_spec (r : receiver.Receiver N M K) (time duration : Std.I64)
    (frames : Std.U32) :
    receiver.Receiver.cycle r time duration frames ⦃ out => SameStream out.2 r ⦄ := by
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
          step as ⟨o2⟩
          cases o2 with
          | none => simp [SameStream]
          | some later =>
            simp only
            step as ⟨out⟩
            simp [SameStream]
  · simp [SameStream]

/-! ## Reports and the delay of the path -/

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

@[step]
theorem middle_total (e : relation.Estimator M) :
    relation.Estimator.middle e ⦃ _ => True ⦄ := by
  unfold relation.Estimator.middle
  run

/-- Taking the delay of the path from the two estimates changes that delay
and nothing else. -/
@[step]
theorem measure_path_spec (r : receiver.Receiver N M K) :
    receiver.Receiver.measure_path r ⦃ r' => SameStream r' r ⦄ := by
  unfold receiver.Receiver.measure_path relation.Estimator.impl.line
  simp only [bind_ok]
  cases r.clock.line with
  | none => simp [SameStream]
  | some forward =>
    simp only
    cases r.back.line with
    | none => simp [SameStream]
    | some back =>
      simp only
      step as ⟨o⟩
      cases o with
      | none => simp [SameStream]
      | some time =>
        simp only
        step as ⟨sender⟩
        step as ⟨i⟩
        step as ⟨i1, hi1⟩
        step as ⟨i2⟩
        step as ⟨i3, hi3⟩
        step as ⟨both, hboth⟩
        step as ⟨half, hhalf⟩
        split
        · simp [SameStream]
        · step as ⟨i4⟩
          simp [SameStream]

/-- Making a report changes nothing about the timeline that is followed or
the frames that are held. A receiver that follows no timeline makes none; one
that does numbers its reports one after the other. -/
theorem report_spec (r : receiver.Receiver N M K) (stream : Std.U16) :
    receiver.Receiver.report r stream ⦃ out =>
      SameStream out.2 r
      ∧ (r.following = false → out.1 = none)
      ∧ (r.following = true →
          out.1 = some ⟨stream, r.timeline, r.identity, r.reports⟩) ⦄ := by
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

/-- Taking in the sender's answer to a report returns for every state and
every answer, and changes nothing about the timeline that is followed or the
frames that are held: only the estimate of the path. -/
theorem echo_spec (r : receiver.Receiver N M K) (echo : packet.Echo) :
    receiver.Receiver.echo r echo ⦃ r' => SameStream r' r ⦄ := by
  unfold receiver.Receiver.echo
  split
  · split
    · simp [SameStream]
    · step as ⟨o⟩
      cases o with
      | none => simp [SameStream]
      | some departure =>
        simp only
        step as ⟨i, hi⟩
        step as ⟨o1, ho1⟩
        step as ⟨window, hwindow⟩
        step with Unisono.Relation.observe_total as ⟨e⟩
        step as ⟨r1, hsame⟩
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hsame
        exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · simp [SameStream]

end Unisono.Receiver
