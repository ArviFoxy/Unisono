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

/-- Two states of a receiver agree in the stream, timeline, clock identity and
confirmation candidate they track, in when they last heard the stream and last
had a frame that was not behind the playhead, in their settings and in the
frames they hold. They may differ in the estimate of the sender's clock, in the
arrivals they keep, in the path delay, in the schedule and in the regulator. -/
def SameStream (a b : receiver.Receiver N M K) : Prop :=
  a.stream = b.stream ∧ a.following = b.following ∧ a.timeline = b.timeline
  ∧ a.clock_id = b.clock_id ∧ a.has_candidate = b.has_candidate ∧ a.candidate = b.candidate
  ∧ a.heard = b.heard ∧ a.fresh = b.fresh ∧ a.silence = b.silence ∧ a.limit = b.limit
  ∧ a.presence = b.presence

theorem SameStream.refl (a : receiver.Receiver N M K) : SameStream a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameStream.trans {a b c : receiver.Receiver N M K} (h1 : SameStream a b)
    (h2 : SameStream b c) : SameStream a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8, a9.trans b9, a10.trans b10, a11.trans b11⟩

/-! ## What a packet says about the sender's clock -/

/-- Runs a function to its end: step by step, taking a conditional apart
wherever one stands in the way. -/
local macro "run" : tactic => `(tactic| repeat' (first | split | step*))

@[step]
theorem span_of_total (h : packet.Audio) : receiver.span_of h ⦃ _ => True ⦄ := by
  unfold receiver.span_of
  step*

@[step]
theorem arrivals_new_total (K : Std.Usize) : arrivals.Arrivals.new K ⦃ _ => True ⦄ := by
  unfold arrivals.Arrivals.new
  simp

@[step]
theorem stamped_arrival_total (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.stamped_arrival r h ⦃ _ => True ⦄ := by
  unfold receiver.Receiver.stamped_arrival
  step*

@[step]
theorem middle_total (e : relation.Estimator M) :
    relation.Estimator.middle e ⦃ _ => True ⦄ := by
  unfold relation.Estimator.middle
  run

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

/-- Taking the delay of the path from the two estimates changes that delay
and nothing else. -/
@[step]
theorem measure_path_spec (r : receiver.Receiver N M K) :
    receiver.Receiver.measure_path r ⦃ r' =>
      SameStream r' r ∧ r'.schedule = r.schedule ⦄ := by
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

/-- Taking the clock measurement from a packet changes the estimates, path
delay, and kept arrivals, and nothing else. -/
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
    step as ⟨r1, hsame1, _, hsched1⟩
    step as ⟨r2, hsame2, hsched2⟩
    step as ⟨a⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hsame2.trans hsame1
    simp only [SameStream]
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hsched2.trans hsched1⟩

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
packet: it follows no timeline, or the packet's timeline is a confirmed
candidate different from the followed one and either it is later or the
followed one has been silent for the set time. -/
def AdoptsAt (following : Bool) (followed : Std.U64) (hasCandidate : Bool)
    (candidate : Std.U64) (heard silence : Std.I64)
    (timeline : Std.U64) (t : Std.I64) : Prop :=
  following = false
  ∨ (timeline ≠ followed ∧ hasCandidate = true ∧ candidate = timeline
      ∧ (followed.val < timeline.val
        ∨ silence.val ≤ (core.num.I64.saturating_sub t heard).val))

instance (following : Bool) (followed : Std.U64) (hasCandidate : Bool)
    (candidate : Std.U64) (heard silence : Std.I64)
    (timeline : Std.U64) (t : Std.I64) :
    Decidable (AdoptsAt following followed hasCandidate candidate heard silence timeline t) := by
  unfold AdoptsAt; infer_instance

/-- Whether a packet of `timeline` that arrives at `t` makes the receiver
take up that timeline. -/
def Adopts (r : receiver.Receiver N M K) (timeline : Std.U64) (t : Std.I64) : Prop :=
  AdoptsAt r.following r.timeline r.has_candidate r.candidate (heardBy r t) r.silence timeline t

instance (r : receiver.Receiver N M K) (timeline : Std.U64) (t : Std.I64) :
    Decidable (Adopts r timeline t) := by
  unfold Adopts; infer_instance

@[step]
theorem adopts_spec (r : receiver.Receiver N M K) (timeline : Std.U64) (t : Std.I64) :
    receiver.Receiver.adopts r timeline t ⦃ b =>
      b = decide (AdoptsAt r.following r.timeline r.has_candidate r.candidate
        r.heard r.silence timeline t) ⦄ := by
  unfold receiver.Receiver.adopts
  split
  · rename_i hf
    split
    · rename_i heq
      simp [AdoptsAt, hf, heq]
    · rename_i hne
      split
      · rename_i hc
        split
        · rename_i hcand_ne
          have hcand_ne' : r.candidate ≠ timeline := by simpa using hcand_ne
          simp [AdoptsAt, hf, hne, hc, hcand_ne']
        · rename_i hcand_eq
          have hcand_eq' : r.candidate = timeline := by
            have : ¬ r.candidate ≠ timeline := by simpa using hcand_eq
            exact not_not.mp this
          split
          · rename_i hgt
            have : r.timeline.val < timeline.val := by scalar_tac
            simp [AdoptsAt, hf, hne, hc, hcand_eq', this]
          · rename_i hle
            have : ¬ r.timeline.val < timeline.val := by scalar_tac
            step as ⟨i, hi⟩
            have hiff : i ≥ r.silence
                ↔ AdoptsAt r.following r.timeline r.has_candidate r.candidate
                    r.heard r.silence timeline t := by
              unfold AdoptsAt
              rw [← hi]
              constructor
              · intro hge
                exact Or.inr ⟨hne, hc, hcand_eq', Or.inr (by scalar_tac)⟩
              · rintro (hnf | ⟨-, -, -, hlt | hsil⟩)
                · rw [hf] at hnf; cases hnf
                · exact absurd hlt this
                · scalar_tac
            simp [hiff]
      · rename_i hnc
        have hnc' : r.has_candidate = false := by simpa using hnc
        simp [AdoptsAt, hf, hne, hnc']
  · rename_i hf
    simp [AdoptsAt, hf]

/-- Taking up the timeline of a packet: the receiver follows it, holds
nothing, clears any candidate, and has its playhead at the packet's first frame.
When restarting on the same sender clock, the clock and return estimators,
departure records, and path delay are preserved; on a different clock they are
reset. -/
@[step]
theorem adopt_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.adopt r h ⦃ r' =>
      r'.stream = r.stream ∧ r'.following = true ∧ r'.timeline = h.timeline
      ∧ r'.clock_id = h.clock ∧ r'.has_candidate = false
      ∧ r'.heard = r.heard ∧ r'.fresh = r.fresh ∧ r'.silence = r.silence ∧ r'.limit = r.limit
      ∧ r'.presence.base = h.index ∧ (∀ j, ¬ Held r'.presence j)
      ∧ (r.following = true → h.clock = r.clock_id →
          r'.path = r.path ∧ r'.departures = r.departures
          ∧ r'.back.kept = r.back.kept ∧ r'.back.len = r.back.len ∧ r'.back.line = r.back.line
          ∧ r'.clock.latest = core.num.I64.MIN ∧ r'.clock.window = 0#u64
          ∧ (r.clock.lowest = none →
              r'.clock.kept = r.clock.kept ∧ r'.clock.len = r.clock.len
              ∧ r'.clock.line = r.clock.line))
      ∧ (r.following = true → h.clock ≠ r.clock_id →
          r'.path = 0#i64 ∧ r'.clock.len.val = 0 ∧ r'.clock.line = none
          ∧ r'.back.len.val = 0 ∧ r'.back.line = none) ⦄ := by
  unfold receiver.Receiver.adopt
  split
  · rename_i hf
    simp only [bind_ok]
    step as ⟨p, hpb, hph⟩
    step as ⟨a⟩
    step with Unisono.Player.stop_total as ⟨p1⟩
    split
    · rename_i hclk
      have hclk' : h.clock = r.clock_id := by simpa using hclk
      step as ⟨i⟩
      step as ⟨e, _, _, he_kept, he_len, _, _, _, he_low, he_line⟩
      step as ⟨e1, he1_hw, he1_win, he1_keep⟩
      step as ⟨e2, _, _, he2_kept, he2_len, _, _, _, _, he2_line⟩
      refine ⟨hpb, hph, ?_, ?_⟩
      · intro _ _
        refine ⟨he2_kept, he2_len, he2_line, he1_hw, he1_win, fun hlo => ?_⟩
        obtain ⟨hk, hl, hli⟩ := he1_keep (by rw [he_low]; exact hlo)
        exact ⟨hk.trans he_kept, hl.trans he_len, hli.trans he_line⟩
      · intro _ hne
        exact absurd hclk' hne
    · rename_i hclk
      have hclk' : h.clock ≠ r.clock_id := by simpa using hclk
      simp only [hf]
      step as ⟨i1⟩
      step as ⟨e, _, _, _, _, he_len, _, _, he_line⟩
      step as ⟨e1, _, _, _, _, he1_len, _, _, he1_line⟩
      refine ⟨hpb, hph, ?_, ?_⟩
      · intro heq
        exact absurd heq hclk'
      · intro _
        exact ⟨he_len, he_line, he1_len, he1_line⟩
  · rename_i hnf
    have hnf' : r.following = false := by simpa using hnf
    simp only [bind_ok]
    step as ⟨p, hpb, hph⟩
    step as ⟨a⟩
    step with Unisono.Player.stop_total as ⟨p1⟩
    simp only [hnf', Bool.false_eq_true, ↓reduceIte]
    step as ⟨i1⟩
    step as ⟨e⟩
    step as ⟨e1⟩
    refine ⟨hpb, hph, ?_, ?_⟩ <;> (intro hc; cases hc)

/-! ## Sliding the stretch during warmup -/

/-- Sliding the stretch forward before the clock locks: leaves stream,
timeline, clock, and settings untouched, never moves the playhead backward,
does nothing once the clock has locked or when the packet does not start past
the playhead, and never advances the playhead past the packet's first frame. -/
@[step]
theorem slide_warmup_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.slide_warmup r h ⦃ r' =>
      r'.stream = r.stream ∧ r'.following = r.following ∧ r'.timeline = r.timeline
      ∧ r'.clock_id = r.clock_id ∧ r'.has_candidate = r.has_candidate
      ∧ r'.candidate = r.candidate ∧ r'.heard = r.heard ∧ r'.fresh = r.fresh
      ∧ r'.silence = r.silence ∧ r'.limit = r.limit ∧ r'.clock = r.clock
      ∧ r.presence.base.val ≤ r'.presence.base.val
      ∧ (r.clock.line ≠ none → r' = r)
      ∧ (h.index.val ≤ r.presence.base.val → r' = r)
      ∧ (r.presence.base.val < h.index.val → r'.presence.base.val ≤ h.index.val) ⦄ := by
  unfold receiver.Receiver.slide_warmup relation.Estimator.impl.line
  simp only [bind_ok]
  cases hline : r.clock.line with
  | some line =>
    simp [core.option.Option.is_some]; omega
  | none =>
    simp only [core.option.Option.is_some, Option.isSome, Bool.false_eq_true, ↓reduceIte]
    step as ⟨width, hwidth⟩
    split
    · simp; omega
    · unfold presence.Presence.impl.base
      simp only [bind_ok]
      step as ⟨i, hi⟩
      step as ⟨end_, hend⟩
      step as ⟨stretch_end, hse⟩
      step as ⟨limit, hlim⟩
      split
      · rename_i hgt
        have hgt' : r.presence.base.val < h.index.val := by scalar_tac
        split
        · split
          · step as ⟨target, htarget⟩
            have hnb : (if target < h.index then ok target else ok h.index) =
                ok (if target < h.index then target else h.index) := by
              split <;> rfl
            rw [hnb]
            simp only [bind_ok]
            set new_base := if target < h.index then target else h.index
            have hnb_le : new_base.val ≤ h.index.val := by
              subst new_base
              split <;> scalar_tac
            step as ⟨p, hpb, _⟩
            refine ⟨by omega, fun hne => absurd rfl hne, fun hle => by omega,
              fun _ => by omega⟩
          · simp; omega
        · simp; omega
      · simp; omega

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
  step as ⟨e1, hlatest, hwindow, hkept⟩
  step as ⟨i, hi⟩
  have hiv : i.val = h.frames.val := by rw [hi]; exact U16.cast_U32_val h.frames
  step as ⟨m, p2, harr⟩
  rw [hiv] at harr
  exact ⟨hwindow, p, hpb, hph, harr⟩

/-- Taking in how a packet's frames were marked: a packet with a frame at or
ahead of the playhead (or a covered zero-frame keepalive) makes now the time
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
packet's frames arrive at the stretch (slid forward during warmup if needed). -/
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
            ∧ (r.clock.line ≠ none → p1 = r.presence)
            ∧ (h.index.val ≤ r.presence.base.val → p1 = r.presence)
            ∧ (AllLate p1 h.index.val h.frames.val ↔ AllLate r.presence h.index.val h.frames.val)
            ∧ Arrived p1 h.index.val h.frames.val out.2.presence out.1.marked)
      ∧ (out.1.restarted = true →
          ∃ p0 : presence.Presence N, p0.base = h.index ∧ (∀ j, ¬ Held p0 j)
            ∧ Arrived p0 h.index.val h.frames.val out.2.presence out.1.marked)
      ∧ (out.1.restarted = false → OnlyLate out.1.marked →
          out.2.fresh = freshBy r t) ⦄ := by
  unfold receiver.Receiver.accept
  step as ⟨r0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, sbase, sline, snoop, sbound⟩
  have hall_iff : AllLate r0.presence h.index.val h.frames.val
      ↔ AllLate r.presence h.index.val h.frames.val :=
    allLate_slide_iff (fun hle => by rw [snoop hle]) sbound
  step as ⟨r1, hs1, hsched1⟩
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
        fun hl => by rw [sline hl],
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
          ∧ out.2.fresh = r.fresh)
      ∧ (h.stream = r.stream → ¬ Adopts r h.timeline t → h.timeline = r.timeline →
          out.1.adopted = false ∧ out.1.ignored = false
          ∧ out.2.following = r.following ∧ out.2.timeline = r.timeline
          ∧ out.2.clock_id = r.clock_id ∧ out.2.has_candidate = false ∧ out.2.heard = t
          ∧ out.1.restarted = decide (Restarts r h t)
          ∧ (out.1.restarted = false →
              ∃ p1 : presence.Presence N,
                r.presence.base.val ≤ p1.base.val
                ∧ (r.clock.line ≠ none → p1 = r.presence)
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
      step as ⟨r1, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, _, _⟩
      step as ⟨out, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩
      refine ⟨d3.trans c1, d10.trans c8, d11.trans c9,
        fun hne => absurd hsame_s' hne,
        fun _ _ => ?_,
        fun _ hno => absurd hA hno,
        fun _ hno => absurd hA hno⟩
      refine ⟨d2.trans hyes, d1, d4.trans c2, d5.trans c3, d6.trans c4, d7.trans c5, d9, ?_⟩
      cases hre : out.1.restarted with
      | false =>
        obtain ⟨p1, _, _, hnoop, _, harr⟩ := d13 hre
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
          fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
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

/-- A single stray packet of another timeline while following a timeline with
no pending candidate is ignored and cannot hijack the timeline or playhead;
it only records the candidate for confirmation. -/
theorem single_stray_timeline_noop (r : receiver.Receiver N M K) (h : packet.Audio)
    (t : Std.I64) (hstream : h.stream = r.stream) (hf : r.following = true)
    (hnc : r.has_candidate = false) (hdiff : h.timeline ≠ r.timeline) :
    receiver.Receiver.packet r h t ⦃ out =>
      out.1.ignored = true ∧ out.1.adopted = false
      ∧ out.2.following = true ∧ out.2.timeline = r.timeline
      ∧ out.2.presence = r.presence ∧ out.2.fresh = r.fresh
      ∧ out.2.has_candidate = true ∧ out.2.candidate = h.timeline ⦄ := by
  have hnotA : ¬ Adopts r h.timeline t := by
    rintro (hc | ⟨-, hc, -⟩)
    · rw [hf] at hc; cases hc
    · rw [hnc] at hc; cases hc
  apply WP.spec_mono (packet_spec r h t)
  rintro out ⟨-, -, -, -, -, hother, -⟩
  obtain ⟨ha, hi, hfo, htl, -, hcand, hct, -, hpr, hfr⟩ := hother hstream hnotA hdiff
  exact ⟨hi, ha, hfo.trans hf, htl, hpr, hfr, hcand, hct⟩

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

/-- Taking in the sender's answer to a report returns for every state and
every answer, and changes nothing about the timeline that is followed or the
frames that are held: only the estimate of the path. -/
theorem echo_spec (r : receiver.Receiver N M K) (echo : packet.Echo) :
    receiver.Receiver.echo r echo ⦃ r' => SameStream r' r ⦄ := by
  unfold receiver.Receiver.echo
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
          step as ⟨i, hi⟩
          step as ⟨o1, ho1⟩
          step as ⟨window, hwindow⟩
          step with Unisono.Relation.observe_total as ⟨e⟩
          step as ⟨r1, hsame, _⟩
          exact hsame
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
