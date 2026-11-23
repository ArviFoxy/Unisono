/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Receiver.Adopt

/-!
# Receiver: packet ingestion and silence recovery

Packet processing (`packet_spec`), handling playheads behind or ahead of
incoming frames, and following a new timeline after silence
(`follows_after_silence`).
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

theorem countOf_late_zero {p : presence.Presence N} {first d : ℕ} (hge : p.base.val ≤ first) :
    countOf p first d presence.Outcome.Late = 0 := by
  induction d with
  | zero => simp [countOf]
  | succ d ih =>
    rw [countOf_succ, ih]
    have hnot : outcomeOf p (first + d) ≠ presence.Outcome.Late := by
      unfold outcomeOf
      split
      · split <;> decide
      · split
        · omega
        · decide
    simp [hnot]

theorem allLate_slide_iff {p p' : presence.Presence N} {first d : ℕ}
    (hkeep : first ≤ p.base.val → p' = p)
    (hbound : p.base.val < first → p'.base.val ≤ first) :
    AllLate p' first d ↔ AllLate p first d := by
  by_cases hle : first ≤ p.base.val
  · rw [hkeep hle]
  · have hlt : p.base.val < first := by omega
    have h0 : countOf p first d presence.Outcome.Late = 0 :=
      countOf_late_zero (Nat.le_of_lt hlt)
    have h0' : countOf p' first d presence.Outcome.Late = 0 :=
      countOf_late_zero (hbound hlt)
    constructor
    · intro h; exact absurd h0' h.1
    · intro h; exact absurd h0 h.1

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
      ∧ out.2.stream = r.stream ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline
      ∧ out.2.clock_id = r.clock_id ∧ out.2.has_candidate = r.has_candidate
      ∧ out.2.candidate = r.candidate ∧ out.2.heard = r.heard ∧ out.2.fresh = freshBy r t
      ∧ out.2.silence = r.silence ∧ out.2.limit = r.limit ∧ out.2.presence = r.presence
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

/-- Starting anew at a packet: the playhead is at the packet's first frame,
nothing but the packet's frames is held, and the windows of the clock's
estimate, which are numbered by the index, can be numbered from the start
again. -/
@[step]
theorem renew_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.renew r h ⦃ out =>
      out.2.stream = r.stream ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline
      ∧ out.2.clock_id = r.clock_id ∧ out.2.has_candidate = r.has_candidate
      ∧ out.2.candidate = r.candidate ∧ out.2.heard = r.heard ∧ out.2.fresh = r.fresh
      ∧ out.2.silence = r.silence ∧ out.2.limit = r.limit
      ∧ out.2.clock.window = 0#u64
      ∧ ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
          ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1 ⦄ := by
  unfold receiver.Receiver.renew
  step as ⟨p, hpb, hph⟩
  step with Unisono.Player.stop_total as ⟨p1⟩
  step with Unisono.Player.modal_stop_total as ⟨mp1⟩
  step as ⟨e1, hlatest, hwindow, hkept⟩
  step as ⟨i, hi⟩
  have hiv : i.val = h.frames.val := by rw [hi]; exact U16.cast_U32_val h.frames
  step as ⟨m, p2, harr⟩
  rw [hiv] at harr
  exact ⟨hwindow, p, hpb, hph, harr⟩

/-- Taking in how a packet's frames were marked: a packet with a frame at or
ahead of the playhead, or a packet without frames whose index the stretch
covers, makes now the time
at which such a frame last arrived, and any non-empty packet whose frames are
all late leaves that time as it was. -/
@[step]
theorem refresh_spec (r : receiver.Receiver N M K) (h : packet.Audio) (m : presence.Marked)
    (t : Std.I64) :
    receiver.Receiver.refresh r h m t ⦃ r' =>
      r'.stream = r.stream ∧ r'.following = r.following ∧ r'.timeline = r.timeline
      ∧ r'.clock_id = r.clock_id ∧ r'.has_candidate = r.has_candidate
      ∧ r'.candidate = r.candidate ∧ r'.heard = r.heard
      ∧ r'.silence = r.silence ∧ r'.limit = r.limit ∧ r'.presence = r.presence
      ∧ (r'.fresh = t ∨ r'.fresh = r.fresh)
      ∧ (m.stored.val = 0 → m.duplicate.val = 0 → m.early.val = 0 → h.frames.val ≠ 0 →
          r'.fresh = r.fresh) ⦄ := by
  unfold receiver.Receiver.refresh
  split
  · rename_i h1
    have : m.stored.val ≠ 0 := by scalar_tac
    step as ⟨r1, hs⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hs
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a9, a10, a11, Or.inl a8, fun h0 => absurd h0 this⟩
  · split
    · rename_i h1 h2
      have : m.duplicate.val ≠ 0 := by scalar_tac
      step as ⟨r1, hs⟩
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hs
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a9, a10, a11, Or.inl a8, fun _ h0 => absurd h0 this⟩
    · split
      · rename_i h1 h2 h3
        have hf0 : h.frames.val = 0 := by scalar_tac
        step as ⟨b, _⟩
        split
        · step as ⟨r1, hs⟩
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hs
          exact ⟨a1, a2, a3, a4, a5, a6, a7, a9, a10, a11, Or.inl a8,
            fun _ _ _ hnz => absurd hf0 hnz⟩
        · split
          · rw [WP.spec_ok]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl,
              fun _ _ _ hnz => absurd hf0 hnz⟩
          · rw [WP.spec_ok]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr rfl,
              fun _ _ _ _ => rfl⟩
      · split
        · rename_i h1 h2 h3 h4
          have : m.early.val ≠ 0 := by scalar_tac
          rw [WP.spec_ok]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl,
            fun _ _ h0 _ => absurd h0 this⟩
        · rw [WP.spec_ok]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr rfl,
            fun _ _ _ _ => rfl⟩

/-- Taking in a packet of the followed timeline. The timeline has been heard
now. If the packet shows that the playhead is wrong, the receiver starts anew
at it and holds the packet's frames from an empty stretch; otherwise the
packet's frames arrive at the stretch, moved forward to them first if the
sender's clock is not known yet. -/
@[step]
theorem accept_spec (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64)
    (adopted : Bool) :
    receiver.Receiver.accept r h t adopted ⦃ out =>
      out.1.ignored = false ∧ out.1.adopted = adopted
      ∧ out.2.stream = r.stream ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline
      ∧ out.2.clock_id = r.clock_id ∧ out.2.has_candidate = r.has_candidate
      ∧ out.2.candidate = r.candidate ∧ out.2.heard = t
      ∧ out.2.silence = r.silence ∧ out.2.limit = r.limit
      ∧ out.1.restarted = decide (Restarts r h t)
      ∧ (out.1.restarted = false →
          ∃ p1 : presence.Presence N,
            r.presence.base.val ≤ p1.base.val
            ∧ (r.use_sync = false → r.clock.line ≠ none → p1 = r.presence)
            ∧ (r.use_sync = true → r.sync_snapshot.valid = true → p1 = r.presence)
            ∧ (h.index.val ≤ r.presence.base.val → p1 = r.presence)
            ∧ (AllLate p1 h.index.val h.frames.val ↔ AllLate r.presence h.index.val h.frames.val)
            ∧ Arrived p1 h.index.val h.frames.val out.2.presence out.1.marked)
      ∧ (out.1.restarted = true →
          ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
            ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1.marked)
      ∧ (out.1.restarted = false → OnlyLate out.1.marked →
          out.2.fresh = freshBy r t) ⦄ := by
  unfold receiver.Receiver.accept
  step as ⟨r0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, sus, ssnap, sbase, sline, ssync, snoop,
    sbound⟩
  have hall_iff : AllLate r0.presence h.index.val h.frames.val
      ↔ AllLate r.presence h.index.val h.frames.val :=
    allLate_slide_iff (fun hle => by rw [snoop hle]) sbound
  have hmeas :
      (if r0.use_sync = true then ok r0 else receiver.Receiver.measure r0 h t)
        ⦃ r1 => SameStream r1 r0 ⦄ := by
    split
    · simp [SameStream]
    · apply WP.spec_mono (measure_spec r0 h t)
      intro r1 hr1; exact hr1.1
  apply WP.spec_bind hmeas
  intro r1 hs1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hs1
  step as ⟨i, hi⟩
  have hiv : i.val = h.frames.val := by rw [hi]; exact U16.cast_U32_val h.frames
  step as ⟨first, p, harr⟩
  rw [a11, hiv] at harr
  step as ⟨restarted, r2, hres, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩
  have hfb : freshBy { r1 with presence := p } t = freshBy r t := by
    unfold freshBy
    simp only [a8, s8]
  rw [hfb] at hres b8
  have hrestarts : restarted = decide (Restarts r h t) := by
    rw [hres]
    apply decide_eq_decide.mpr
    unfold Restarts
    rw [onlyLate_iff harr, hall_iff, a9, s9]
  cases restarted with
  | true =>
    simp only [↓reduceIte]
    step as ⟨out1, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, cwin, p0, c11, c12, c13⟩
    obtain ⟨m1, r4⟩ := out1
    simp only at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c13 ⊢
    step as ⟨r5, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩
    refine ⟨d1.trans (c1.trans (b1.trans (a1.trans s1))),
      d2.trans (c2.trans (b2.trans (a2.trans s2))),
      d3.trans (c3.trans (b3.trans (a3.trans s3))),
      d4.trans (c4.trans (b4.trans (a4.trans s4))),
      d5.trans (c5.trans (b5.trans (a5.trans s5))),
      d6.trans (c6.trans (b6.trans (a6.trans s6))),
      d7.trans (c7.trans (b7.trans (a7.trans s7))),
      d8.trans (c9.trans (b9.trans (a9.trans s9))),
      d9.trans (c10.trans (b10.trans (a10.trans s10))),
      hrestarts, fun hc => (by cases hc), fun _ => ?_, fun hc => (by cases hc)⟩
    rw [d10]
    exact ⟨p0, c11, c12, c13⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    step as ⟨r5, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩
    refine ⟨d1.trans (b1.trans (a1.trans s1)),
      d2.trans (b2.trans (a2.trans s2)),
      d3.trans (b3.trans (a3.trans s3)),
      d4.trans (b4.trans (a4.trans s4)),
      d5.trans (b5.trans (a5.trans s5)),
      d6.trans (b6.trans (a6.trans s6)),
      d7.trans (b7.trans (a7.trans s7)),
      d8.trans (b9.trans (a9.trans s9)),
      d9.trans (b10.trans (a10.trans s10)),
      hrestarts, fun _ => ?_, fun hc => (by cases hc), fun _ hlate => ?_⟩
    · refine ⟨r0.presence, sbase,
        fun hu hl => by rw [sline hu hl],
        fun hu hv => by rw [ssync hu hv],
        fun hle => by rw [snoop hle],
        hall_iff, ?_⟩
      rw [d10, b11]
      exact harr
    · obtain ⟨l1, l2, l3, l4⟩ := hlate
      have hnz : h.frames.val ≠ 0 := by
        obtain ⟨-, -, -, -, hlate_cnt, -⟩ := harr
        have hle := countOf_le r0.presence h.index.val h.frames.val presence.Outcome.Late
        omega
      rw [d12 l2 l3 l4 hnz, b8]

/-- What a receiver does with a packet, in four cases.

A packet of another stream is ignored without changing any state. Otherwise, if
the receiver takes up the packet's timeline, it follows that timeline, held
nothing of it before this packet, and has heard it now. If the packet is of
another timeline than the followed one and is not taken up, it is recorded as
the confirmation candidate and nothing else changes except the correction of
the time last heard. If the packet is of the followed timeline, the candidate
is cleared, the timeline has been heard now, and the packet's frames arrive at
the stretch (or at an empty stretch starting at the packet on restart).

The stream and settings never change. -/
theorem packet_spec (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.2.stream = r.stream ∧ out.2.silence = r.silence ∧ out.2.limit = r.limit
      ∧ (h.stream ≠ r.stream →
          out.1.adopted = false ∧ out.1.ignored = true ∧ out.2 = r)
      ∧ (h.stream = r.stream → Adopts r h.timeline t →
          out.1.adopted = true ∧ out.1.ignored = false
          ∧ out.2.following = true ∧ out.2.timeline = h.timeline
          ∧ out.2.clock_id = h.clock ∧ out.2.has_candidate = false ∧ out.2.heard = t
          ∧ ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
              ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1.marked)
      ∧ (h.stream = r.stream → ¬ Adopts r h.timeline t → h.timeline ≠ r.timeline →
          out.1.adopted = false ∧ out.1.ignored = true
          ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline
          ∧ out.2.clock_id = r.clock_id
          ∧ out.2.has_candidate = true ∧ out.2.candidate = h.timeline
          ∧ out.2.heard = heardBy r t ∧ out.2.presence = r.presence
          ∧ out.2.fresh = r.fresh
          ∧ out.2.player = r.player ∧ out.2.schedule = r.schedule
          ∧ out.2.clock = r.clock ∧ out.2.path = r.path
          ∧ out.2.answers = r.answers ∧ out.2.departures = r.departures)
      ∧ (h.stream = r.stream → ¬ Adopts r h.timeline t → h.timeline = r.timeline →
          out.1.adopted = false ∧ out.1.ignored = false
          ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline
          ∧ out.2.clock_id = r.clock_id ∧ out.2.has_candidate = false ∧ out.2.heard = t
          ∧ out.1.restarted = decide (Restarts r h t)
          ∧ (out.1.restarted = false →
              ∃ p1 : presence.Presence N,
                r.presence.base.val ≤ p1.base.val
                ∧ (r.use_sync = false → r.clock.line ≠ none → p1 = r.presence)
                ∧ (r.use_sync = true → r.sync_snapshot.valid = true → p1 = r.presence)
                ∧ (h.index.val ≤ r.presence.base.val → p1 = r.presence)
                ∧ (AllLate p1 h.index.val h.frames.val
                    ↔ AllLate r.presence h.index.val h.frames.val)
                ∧ Arrived p1 h.index.val h.frames.val out.2.presence out.1.marked)
          ∧ (out.1.restarted = true →
              ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
                ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1.marked)
          ∧ (out.1.restarted = false → OnlyLate out.1.marked →
              out.2.fresh = freshBy r t)) ⦄ := by
  unfold receiver.Receiver.packet
  split
  · rename_i hdiff
    have hdiff' : h.stream ≠ r.stream := by simpa using hdiff
    rw [WP.spec_ok]
    exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩,
      fun heq => absurd heq hdiff',
      fun heq => absurd heq hdiff',
      fun heq => absurd heq hdiff'⟩
  · rename_i hsame_s
    have hsame_s' : h.stream = r.stream := by
      have : ¬ h.stream ≠ r.stream := by simpa using hsame_s
      exact not_not.mp this
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
      step as ⟨r1, c1, c2, c3, c4, c5, c6, c7, c8, c9, cpath, c10, c11, _, _⟩
      step as ⟨out, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩
      refine ⟨d3.trans c1, d10.trans c8, d11.trans c9,
        fun hne => absurd hsame_s' hne,
        fun _ _ => ?_,
        fun _ hno => absurd hA hno,
        fun _ hno => absurd hA hno⟩
      refine ⟨d2.trans hyes, d1, d4.trans c2, d5.trans c3, d6.trans c4, d7.trans c5, d9, ?_⟩
      cases hre : out.1.restarted with
      | false =>
        obtain ⟨p1, _, _, _, hnoop, _, harr⟩ := d13 hre
        have hp1 : p1 = r1.presence := hnoop (by rw [c10])
        rw [hp1] at harr
        exact ⟨r1.presence, c10, c11, harr⟩
      | true => exact d14 hre
    · rename_i hno
      have hA : ¬ Adopts r h.timeline t := fun hc => hno (hiff.mpr hc)
      split
      · rename_i hne
        have hne' : h.timeline ≠ r.timeline := by simpa using hne
        rw [WP.spec_ok]
        refine ⟨rfl, rfl, rfl,
          fun hdiff => absurd hsame_s' hdiff,
          fun _ hc => absurd hc hA,
          fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, rfl, rfl, rfl, rfl⟩,
          fun _ _ heq => absurd heq hne'⟩
      · rename_i heq
        have heq' : h.timeline = r.timeline := by
          have : ¬ h.timeline ≠ r.timeline := by simpa using heq
          exact not_not.mp this
        step as ⟨out, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩
        have had : adopted = false := by simpa using hno
        refine ⟨d3, d10, d11,
          fun hdiff => absurd hsame_s' hdiff,
          fun _ hc => absurd hc hA,
          fun _ _ hne => absurd heq' hne,
          fun _ _ _ => ⟨d2.trans had, d1, d4, d5, d6, d7, d9, d12, d13, d14, d15⟩⟩

/-- A packet belonging to another stream is ignored and leaves the receiver
state completely unchanged. -/
theorem wrong_stream_packet_noop (r : receiver.Receiver N M K) (h : packet.Audio)
    (t : Std.I64) (hdiff : h.stream ≠ r.stream) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.1.ignored = true ∧ out.1.adopted = false ∧ out.2 = r ⦄ := by
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨-, -, -, hwrong, -, -, -⟩
  obtain ⟨ha, hi, heq⟩ := hwrong hdiff
  exact ⟨hi, ha, heq⟩

/-- One stray packet of another timeline, while a timeline is followed and no
other is waiting, is left out: the timeline, the playhead, the held frames,
the regulator, the schedule, the clock estimate, the path delay, the answers,
and the report departures all stay. Its timeline is only remembered, for a
second packet to confirm. -/
theorem single_stray_timeline_noop (r : receiver.Receiver N M K) (h : packet.Audio)
    (t : Std.I64) (hstream : h.stream = r.stream) (hf : r.following = true)
    (hnc : r.has_candidate = false) (hdiff : h.timeline ≠ r.timeline) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.1.ignored = true ∧ out.1.adopted = false
      ∧ out.2.following = true ∧ out.2.timeline = r.timeline
      ∧ out.2.presence = r.presence ∧ out.2.fresh = r.fresh
      ∧ out.2.has_candidate = true ∧ out.2.candidate = h.timeline
      ∧ out.2.player = r.player ∧ out.2.schedule = r.schedule
      ∧ out.2.clock = r.clock ∧ out.2.path = r.path
      ∧ out.2.answers = r.answers ∧ out.2.departures = r.departures ⦄ := by
  have hnotA : ¬ Adopts r h.timeline t := by
    rintro (hc | ⟨-, hc, -⟩)
    · rw [hf] at hc; cases hc
    · rw [hnc] at hc; cases hc
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨-, -, -, -, -, hother, -⟩
  obtain ⟨ha, hi, hfo, htl, -, hcand, hct, -, hpr, hfr, hpl, hsc, hcl, hpa, han, hde⟩ :=
    hother hstream hnotA hdiff
  exact ⟨hi, ha, hfo.trans hf, htl, hpr, hfr, hcand, hct, hpl, hsc, hcl, hpa, han, hde⟩

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

/-- The receiver follows timeline `X`, or it has recorded `X` as its
confirmation candidate while following another timeline last heard at `t0`
or before. -/
def Toward (X : Std.U64) (t0 : ℤ) (r : receiver.Receiver N M K) : Prop :=
  r.following = true
  ∧ (r.timeline = X ∨ (r.has_candidate = true ∧ r.candidate = X ∧ r.heard.val ≤ t0))

/-- After a packet of the receiver's stream, whatever the state before: the
receiver follows the packet's timeline, or has recorded it as a candidate
against another timeline that it has not heard since before the packet. -/
theorem first_packet (r : receiver.Receiver N M K) (h : packet.Audio) (t : Std.I64)
    (hstream : h.stream = r.stream) :
    receiver.Receiver.packet r h t ⦃ out =>
      Toward h.timeline t.val out.2
      ∧ out.2.stream = r.stream ∧ out.2.silence = r.silence ⦄ := by
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨hstr, hs, -, -, hyes, hother, hsame⟩
  refine ⟨?_, hstr, hs⟩
  by_cases hA : Adopts r h.timeline t
  · obtain ⟨-, -, f, tl, -⟩ := hyes hstream hA
    exact ⟨f, Or.inl tl⟩
  · have hf : r.following = true := by
      by_contra hc
      exact hA (Or.inl (by simpa using hc))
    by_cases hne : h.timeline = r.timeline
    · obtain ⟨-, -, f, tl, -⟩ := hsame hstream hA hne
      exact ⟨f.trans hf, Or.inl (tl.trans hne.symm)⟩
    · obtain ⟨-, -, f, -, -, hhc, hcand, hh, -⟩ := hother hstream hA hne
      refine ⟨f.trans hf, Or.inr ⟨hhc, hcand, ?_⟩⟩
      rw [hh]
      exact heardBy_le_now r t

/-- A later packet of timeline `X` on the same stream, at a time not before
`t0`: the receiver stays on its way to `X`, and it follows `X` if it did
already or if the set time of silence has passed since `t0`. -/
theorem later_packet (X : Std.U64) (t0 : ℤ) (r : receiver.Receiver N M K) (h : packet.Audio)
    (t : Std.I64) (hT : Toward X t0 r) (hstream : h.stream = r.stream)
    (hX : h.timeline = X) (ht : t0 ≤ t.val) :
    receiver.Receiver.packet r h t ⦃ out =>
      Toward X t0 out.2 ∧ out.2.stream = r.stream ∧ out.2.silence = r.silence
      ∧ (r.timeline = X → out.2.timeline = X)
      ∧ (t0 + r.silence.val ≤ t.val → out.2.timeline = X) ⦄ := by
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨hstr, hs, -, -, hyes, hother, hsame⟩
  obtain ⟨hf, hway⟩ := hT
  by_cases hA : Adopts r h.timeline t
  · obtain ⟨-, -, f, tl, -⟩ := hyes hstream hA
    have htl : out.2.timeline = X := tl.trans hX
    exact ⟨⟨f, Or.inl htl⟩, hstr, hs, fun _ => htl, fun _ => htl⟩
  · by_cases hne : h.timeline = r.timeline
    · obtain ⟨-, -, f, tl, -⟩ := hsame hstream hA hne
      have htl : out.2.timeline = X := tl.trans (hne.symm.trans hX)
      exact ⟨⟨f.trans hf, Or.inl htl⟩, hstr, hs, fun _ => htl, fun _ => htl⟩
    · obtain ⟨-, -, f, -, -, hhc, hcand, hh, -⟩ := hother hstream hA hne
      have hnX : r.timeline ≠ X := fun hc => hne (hX.trans hc.symm)
      rcases hway with hc | ⟨hrc, hrcand, hheard⟩
      · exact absurd hc hnX
      · have hsame_heard : heardBy r t = r.heard := heardBy_eq r t (by omega)
        refine ⟨⟨f.trans hf, Or.inr ⟨hhc, hcand.trans hX, by rw [hh, hsame_heard]; exact hheard⟩⟩,
          hstr, hs, fun hc => absurd hc hnX, fun hlate => ?_⟩
        exfalso
        apply hA
        refine Or.inr ⟨hne, hrc, hrcand.trans hX.symm, Or.inr ?_⟩
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
      (∀ p ∈ rest, p.1.stream = r.stream ∧ p.1.timeline = X ∧ t0 ≤ p.2.val) →
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
    apply WP.spec_bind (later_packet X t0 r p.1 p.2 hT hp.1 hp.2.1 hp.2.2)
    rintro out ⟨hT', hstr, hs, hstay, hlate⟩
    apply WP.spec_mono (ih out.2 hT' (fun q hq => by
      have hq' := hall q (by simp [hq])
      exact ⟨hq'.1.trans hstr.symm, hq'.2⟩))
    rintro r' ⟨hf, himp⟩
    refine ⟨hf, ?_⟩
    rintro (h | ⟨q, hq, hql⟩)
    · exact himp (Or.inl (hstay h))
    · rcases List.mem_cons.mp hq with rfl | hq'
      · exact himp (Or.inl (hlate hql))
      · exact himp (Or.inr ⟨q, hq', by rw [hs]; exact hql⟩)

/-- From any state, a receiver that is sent packets of one timeline on its
stream follows that timeline once a packet arrives after the set time of
silence, counted from the first of them, and it goes on following it.

`r` is any state at all. The packets are of the receiver's stream and one
timeline, none after the first arrives before the first, and one of them
arrives when the time of silence has passed. -/
theorem follows_after_silence (r : receiver.Receiver N M K) (h0 : packet.Audio)
    (t0 : Std.I64) (rest : List (packet.Audio × Std.I64))
    (hstream0 : h0.stream = r.stream)
    (hall : ∀ p ∈ rest, p.1.stream = r.stream ∧ p.1.timeline = h0.timeline ∧ t0.val ≤ p.2.val)
    (hlate : ∃ p ∈ rest, t0.val + r.silence.val ≤ p.2.val) :
    feed r ((h0, t0) :: rest) ⦃ r' =>
      r'.following = true ∧ r'.timeline = h0.timeline ⦄ := by
  simp only [feed]
  apply WP.spec_bind (first_packet r h0 t0 hstream0)
  rintro out ⟨hT, hstr, hs⟩
  apply WP.spec_mono (feed_toward h0.timeline t0.val rest out.2 hT (fun q hq => by
    have hq' := hall q hq
    exact ⟨hq'.1.trans hstr.symm, hq'.2⟩))
  rintro r' ⟨hf, himp⟩
  obtain ⟨p, hp, hpl⟩ := hlate
  exact ⟨hf, himp (Or.inr ⟨p, hp, by rw [hs]; exact hpl⟩)⟩


end Unisono.Receiver
