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
public import Unisono.Answers

/-!
# Receiver: clock observations and timeline adoption

`SameStream`, sender-clock packet observation (`observe_packet`), timeline
adoption and candidate confirmation (`adopt`), and keeping newest frames before
the clock relation is known (`keep_newest`).
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
theorem arrivals_new_spec (K : Std.Usize) :
    arrivals.Arrivals.new K ⦃ a => arrivals.Arrivals.new K = ok a ⦄ := by
  unfold arrivals.Arrivals.new
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
  step as ⟨o⟩
  cases o with
  | none =>
    simp only [bind_ok]
    step as ⟨a⟩
    simp [SameStream]
  | some arrived =>
    simp only
    step as ⟨r1, hsame1, _, hsched1⟩
    step as ⟨a⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hsame1
    simp only [SameStream]
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hsched1⟩

/-- Taking the next schedule kept into use changes only the schedules. -/
@[step]
theorem turn_spec (r : receiver.Receiver N M K) :
    receiver.Receiver.turn r ⦃ r' =>
      SameStream r' r ∧ r'.path = r.path ∧ r'.clock = r.clock ∧ r'.arrived = r.arrived
      ∧ r'.player = r.player ∧ r'.identity = r.identity ∧ r'.reports = r.reports
      ∧ r'.departures = r.departures ∧ r'.answers = r.answers ⦄ := by
  unfold receiver.Receiver.turn
  cases r.next <;> simp [SameStream]

/-- Keeping what a packet says about when frames are due changes the
schedules and nothing else. -/
@[step]
theorem note_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.note r h ⦃ r' => SameStream r' r ⦄ := by
  unfold receiver.Receiver.note
  repeat' split
  all_goals first
    | (simp [SameStream]; done)
    | (step with Unisono.Player.continues_total as ⟨b⟩
       split
       · simp [SameStream]
       · first
         | (simp [SameStream]; done)
         | (step as ⟨r1, hsame, _, _, _, _, _, _, _, _⟩
            simpa [SameStream] using hsame))

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
nothing, has no other timeline waiting, and has its playhead at the packet's
first frame. What is known about the delay of the path stays as it is. When
the timeline is on the clock of the one before, the estimate of that clock,
the path answers, and the departures of reports stay; on another clock (or on
first adoption) the clock estimate and path answers are cleared and report
departures are reset. -/
@[step]
theorem adopt_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.adopt r h ⦃ r' =>
      r'.stream = r.stream ∧ r'.following = true ∧ r'.timeline = h.timeline
      ∧ r'.clock_id = h.clock ∧ r'.has_candidate = false
      ∧ r'.heard = r.heard ∧ r'.fresh = r.fresh ∧ r'.silence = r.silence ∧ r'.limit = r.limit
      ∧ r'.path = r.path
      ∧ r'.presence.base = h.index ∧ (∀ j, ¬ Held r'.presence j)
      ∧ (r.following = true → h.clock = r.clock_id →
          r'.answers = r.answers ∧ r'.departures = r.departures
          ∧ r'.clock.latest = core.num.I64.MIN ∧ r'.clock.window = 0#u64
          ∧ (r.clock.lowest = none →
              r'.clock.kept = r.clock.kept ∧ r'.clock.len = r.clock.len
              ∧ r'.clock.line = r.clock.line))
      ∧ (r.following = false ∨ h.clock ≠ r.clock_id →
          r'.clock.len.val = 0 ∧ r'.clock.line = none
          ∧ arrivals.Arrivals.new K = ok r'.arrived
          ∧ arrivals.Arrivals.new K = ok r'.departures
          ∧ ∀ k, k < (8#usize).val → ∀ p, r'.answers.places.val[k]? = some p → p.held = false) ⦄ := by
  unfold receiver.Receiver.adopt
  split
  · rename_i hf
    simp only [bind_ok]
    step as ⟨p, hpb, hph⟩
    step as ⟨a, ha⟩
    step with Unisono.Player.stop_total as ⟨p1⟩
    split
    · rename_i hclk
      have hclk' : h.clock = r.clock_id := by simpa using hclk
      step as ⟨i⟩
      step as ⟨e, _, _, he_kept, he_len, _, _, _, he_low, he_line⟩
      step as ⟨e1, he1_hw, he1_win, he1_keep⟩
      refine ⟨hpb, hph, ?_, ?_⟩
      · intro _ _
        refine ⟨he1_hw, he1_win, fun hlo => ?_⟩
        obtain ⟨hk, hl, hli⟩ := he1_keep (by rw [he_low]; exact hlo)
        exact ⟨hk.trans he_kept, hl.trans he_len, hli.trans he_line⟩
      · rintro (hf0 | hne)
        · rw [hf] at hf0; cases hf0
        · exact absurd hclk' hne
    · rename_i hclk
      have hclk' : h.clock ≠ r.clock_id := by simpa using hclk
      step as ⟨i1⟩
      step as ⟨e, _, _, _, _, he_len, _, _, he_line⟩
      step with Unisono.Answers.clear_spec as ⟨a1, ha1⟩
      refine ⟨hpb, hph, ?_, ?_⟩
      · intro _ heq
        exact absurd heq hclk'
      · intro _
        exact ⟨he_len, he_line, ha, ha, ha1⟩
  · rename_i hnf
    have hnf' : r.following = false := by simpa using hnf
    simp only [bind_ok]
    step as ⟨p, hpb, hph⟩
    step as ⟨a, ha⟩
    step with Unisono.Player.stop_total as ⟨p1⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    step as ⟨i1⟩
    step as ⟨e, _, _, _, _, he_len, _, _, he_line⟩
    step with Unisono.Answers.clear_spec as ⟨a1, ha1⟩
    refine ⟨hpb, hph, ?_, ?_⟩
    · intro hc; rw [hnf'] at hc; cases hc
    · intro _; exact ⟨he_len, he_line, ha, ha, ha1⟩

/-! ## Keeping the newest frames before the clock is known -/

/-- Moving the stretch forward to the newest frames: the stream, the
timeline, the clock and the settings stay; the playhead never goes back, and
never past the packet's first frame; and nothing moves once the sender's
clock is known, or when the packet does not begin after the playhead. -/
@[step]
theorem keep_newest_spec (r : receiver.Receiver N M K) (h : packet.Audio) :
    receiver.Receiver.keep_newest r h ⦃ r' =>
      r'.stream = r.stream ∧ r'.following = r.following ∧ r'.timeline = r.timeline
      ∧ r'.clock_id = r.clock_id ∧ r'.has_candidate = r.has_candidate
      ∧ r'.candidate = r.candidate ∧ r'.heard = r.heard ∧ r'.fresh = r.fresh
      ∧ r'.silence = r.silence ∧ r'.limit = r.limit ∧ r'.clock = r.clock
      ∧ r.presence.base.val ≤ r'.presence.base.val
      ∧ (r.clock.line ≠ none → r' = r)
      ∧ (h.index.val ≤ r.presence.base.val → r' = r)
      ∧ (r.presence.base.val < h.index.val → r'.presence.base.val ≤ h.index.val) ⦄ := by
  unfold receiver.Receiver.keep_newest relation.Estimator.impl.line
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


end Unisono.Receiver
