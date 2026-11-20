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

end Unisono.Receiver
