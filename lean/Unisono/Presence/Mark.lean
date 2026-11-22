/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Presence.Bits

/-!
# Presence bitmap: marking arriving frames

Frame arrival outcomes (`outcomeOf`, `mark_frame`, `mark_at`, `held_at`,
`count`, `Arrived`, `mark`) and algebraic laws (`Arrived.comm`, `Arrived.again`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open unisono_core

namespace Unisono.Presence

variable {N : Std.Usize}

/-! ## The arrival of frames -/

/-- What becomes of the frame at index `i` when it arrives. -/
def outcomeOf (p : presence.Presence N) (i : ℕ) : presence.Outcome :=
  if Covered p i then (if bitOf p i then presence.Outcome.Duplicate else presence.Outcome.Stored)
  else if i < p.base.val then presence.Outcome.Late
  else presence.Outcome.Early

/-- The arrival of one frame: its outcome is the one its index has, the
stretch stays where it is, and the frame is held afterwards if it lies in the
stretch. Nothing else changes in what is held. -/
@[step]
theorem mark_frame_spec (p : presence.Presence N) (index : Std.U64) :
    presence.Presence.mark_frame p index ⦃ r =>
      r.1 = outcomeOf p index.val ∧ r.2.base = p.base
      ∧ ∀ j, Held r.2 j ↔ Held p j ∨ (j = index.val ∧ Covered p j) ⦄ := by
  unfold presence.Presence.mark_frame
  step as ⟨b, hb⟩
  split
  · rename_i hc
    have hcov : Covered p index.val := by simpa [hb] using hc
    step as ⟨was, p1, hbase, h0, h1⟩
    obtain ⟨hwas, hbits⟩ := h1 hcov.pos
    have hheld : ∀ j, Held p1 j ↔ Held p j ∨ (j = index.val ∧ Covered p j) := by
      intro j
      unfold Held
      rw [covered_congr hbase, hbits]
      by_cases hs : SamePlace N.val index.val j
      · simp only [hs, ↓reduceIte, and_true]
        constructor
        · intro hcj
          exact Or.inr ⟨(hcov.eq_of_samePlace hcj hs).symm, hcj⟩
        · rintro (⟨hcj, -⟩ | ⟨-, hcj⟩) <;> exact hcj
      · simp only [hs, ↓reduceIte]
        constructor
        · exact Or.inl
        · rintro (h | ⟨rfl, -⟩)
          · exact h
          · exact absurd (SamePlace.refl _ _) hs
    split
    · rename_i hw
      simp only [WP.spec_ok]
      refine ⟨?_, hbase, hheld⟩
      have : bitOf p index.val = true := by rw [← hwas]; exact hw
      simp [outcomeOf, hcov, this]
    · rename_i hw
      simp only [WP.spec_ok]
      refine ⟨?_, hbase, hheld⟩
      have : bitOf p index.val = false := by rw [← hwas]; simpa using hw
      simp [outcomeOf, hcov, this]
  · rename_i hc
    have hcov : ¬ Covered p index.val := by simpa [hb] using hc
    have hheld : ∀ j, Held p j ↔ Held p j ∨ (j = index.val ∧ Covered p j) := by
      intro j
      constructor
      · exact Or.inl
      · rintro (h | ⟨rfl, hcj⟩)
        · exact h
        · exact absurd hcj hcov
    split
    · rename_i hlt
      have : index.val < p.base.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, trivial, hheld⟩
      simp [outcomeOf, hcov, this]
    · rename_i hlt
      have : ¬ index.val < p.base.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, trivial, hheld⟩
      simp [outcomeOf, hcov, this]

/-- The arrival of the frame at an offset from an index. Past the largest
index there is no frame, and its outcome is the one of an index beyond the
stretch. -/
@[step]
theorem mark_at_spec (p : presence.Presence N) (first : Std.U64) (offset : Std.U32) :
    presence.Presence.mark_at p first offset ⦃ r =>
      r.1 = outcomeOf p (first.val + offset.val) ∧ r.2.base = p.base
      ∧ ∀ j, Held r.2 j ↔ Held p j ∨ (j = first.val + offset.val ∧ Covered p j) ⦄ := by
  unfold presence.Presence.mark_at
  step as ⟨i, hi⟩
  have hiv : i.val = offset.val := by rw [hi]; exact U32.cast_U64_val offset
  step as ⟨o, ho⟩
  cases o with
  | none =>
    simp only at ho
    have hb : p.base.val ≤ U64.max := by scalar_tac
    have hcov : ¬ Covered p (first.val + offset.val) := by
      unfold Covered; omega
    have hlate : ¬ first.val + offset.val < p.base.val := by omega
    simp only [WP.spec_ok]
    refine ⟨?_, trivial, ?_⟩
    · simp [outcomeOf, hcov, hlate]
    · intro j
      constructor
      · exact Or.inl
      · rintro (h | ⟨rfl, hc⟩)
        · exact h
        · exact absurd hc hcov
  | some index =>
    simp only at ho
    obtain ⟨-, hidx, -⟩ := ho
    have hval : index.val = first.val + offset.val := by omega
    simp only
    step as ⟨out, h1, h2, h3⟩
    rw [hval] at h1 h3
    exact ⟨h1, h2, h3⟩

/-- Whether the frame at an offset from an index is held. -/
@[step]
theorem held_at_spec (p : presence.Presence N) (start : Std.U64) (offset : Std.U32) :
    presence.Presence.held_at p start offset ⦃ r =>
      r = true ↔ Held p (start.val + offset.val) ⦄ := by
  unfold presence.Presence.held_at
  step as ⟨i, hi⟩
  have hiv : i.val = offset.val := by rw [hi]; exact U32.cast_U64_val offset
  step as ⟨o, ho⟩
  cases o with
  | none =>
    simp only at ho
    have hcov : ¬ Covered p (start.val + offset.val) := by
      unfold Covered; omega
    simp [Held, hcov]
  | some index =>
    simp only at ho
    obtain ⟨-, hidx, -⟩ := ho
    have hval : index.val = start.val + offset.val := by omega
    simp only
    step as ⟨r, hr⟩
    rw [hval] at hr
    exact hr

deriving instance DecidableEq for presence.Outcome

/-- Counting a frame adds one to the count of its outcome. -/
@[step]
theorem count_spec (m : presence.Marked) (o : presence.Outcome) :
    presence.Marked.count m o ⦃ r =>
      r.stored = (if o = presence.Outcome.Stored
        then core.num.U32.saturating_add m.stored 1#u32 else m.stored)
      ∧ r.duplicate = (if o = presence.Outcome.Duplicate
        then core.num.U32.saturating_add m.duplicate 1#u32 else m.duplicate)
      ∧ r.late = (if o = presence.Outcome.Late
        then core.num.U32.saturating_add m.late 1#u32 else m.late)
      ∧ r.early = (if o = presence.Outcome.Early
        then core.num.U32.saturating_add m.early 1#u32 else m.early) ⦄ := by
  unfold presence.Marked.count
  cases o <;> simp only <;> step*

/-- How many of the frames at `first`, ..., `first + d - 1` have the outcome
`o` when they arrive at `p`. -/
def countOf (p : presence.Presence N) (first d : ℕ) (o : presence.Outcome) : ℕ :=
  (List.range d).countP (fun k => decide (outcomeOf p (first + k) = o))

theorem countOf_succ (p : presence.Presence N) (first d : ℕ) (o : presence.Outcome) :
    countOf p first (d + 1) o
      = countOf p first d o + if outcomeOf p (first + d) = o then 1 else 0 := by
  unfold countOf
  rw [List.range_succ, List.countP_append, List.countP_singleton]
  simp

theorem countOf_le (p : presence.Presence N) (first d : ℕ) (o : presence.Outcome) :
    countOf p first d o ≤ d := by
  unfold countOf
  have := List.countP_le_length (p := fun k => decide (outcomeOf p (first + k) = o))
    (l := List.range d)
  simpa using this

/-- Every frame of a packet has exactly one outcome. -/
theorem countOf_total (p : presence.Presence N) (first d : ℕ) :
    countOf p first d presence.Outcome.Stored + countOf p first d presence.Outcome.Duplicate
      + countOf p first d presence.Outcome.Late + countOf p first d presence.Outcome.Early
      = d := by
  induction d with
  | zero => simp [countOf]
  | succ d ih =>
    simp only [countOf_succ]
    cases h : outcomeOf p (first + d) <;> simp <;> omega

/-- A count that follows the number of frames with one outcome, after one
more frame. It does not reach the largest number, so nothing saturates. -/
theorem tally_step (x : Std.U32) (c d frames : ℕ) (hx : x.val = c) (hc : c ≤ d)
    (hd : d < frames) (hf : frames ≤ U32.max) (hit : Prop) [Decidable hit] :
    (if hit then core.num.U32.saturating_add x 1#u32 else x).val
      = c + if hit then 1 else 0 := by
  split
  · rw [U32.saturating_add_one_val x frames (by omega) hf, hx]
  · simp [hx]

/-- The receiver's state and counts after the first `d` frames of a packet
that starts at index `first` have arrived at `p`. -/
def Arrived (p : presence.Presence N) (first d : ℕ) (s : presence.Presence N)
    (m : presence.Marked) : Prop :=
  s.base = p.base
  ∧ (∀ j, Held s j ↔ Held p j ∨ (first ≤ j ∧ j < first + d ∧ Covered p j))
  ∧ m.stored.val = countOf p first d presence.Outcome.Stored
  ∧ m.duplicate.val = countOf p first d presence.Outcome.Duplicate
  ∧ m.late.val = countOf p first d presence.Outcome.Late
  ∧ m.early.val = countOf p first d presence.Outcome.Early

/-- Before a frame of the packet arrives, its outcome is the one it has at the
state the packet found: no earlier frame of the packet has its index. -/
theorem Arrived.outcomeOf_next {p s : presence.Presence N} {first d : ℕ}
    {m : presence.Marked} (h : Arrived p first d s m) :
    outcomeOf s (first + d) = outcomeOf p (first + d) := by
  obtain ⟨hbase, hheld, -⟩ := h
  have hh := hheld (first + d)
  unfold outcomeOf
  rw [hbase]
  by_cases hc : Covered p (first + d)
  · have hcs : Covered s (first + d) := (covered_congr hbase _).mpr hc
    have hbit : bitOf s (first + d) = bitOf p (first + d) := by
      rw [Bool.eq_iff_iff]
      unfold Held at hh
      constructor
      · intro hb
        rcases hh.mp ⟨hcs, hb⟩ with h1 | h1
        · exact h1.2
        · omega
      · intro hb
        exact (hh.mpr (Or.inl ⟨hc, hb⟩)).2
    simp [hc, hcs, hbit]
  · have hcs : ¬ Covered s (first + d) := fun h => hc ((covered_congr hbase _).mp h)
    simp [hc, hcs]

theorem mark_loop_spec (p : presence.Presence N) (first : Std.U64) (frames : Std.U32) :
    presence.Presence.mark_loop p first frames
      { stored := 0#u32, duplicate := 0#u32, late := 0#u32, early := 0#u32 } 0#u32 ⦃ r =>
      Arrived p first.val frames.val r.2 r.1 ⦄ := by
  unfold presence.Presence.mark_loop
  apply loop.spec_decr_nat
    (measure := fun x : presence.Presence N × presence.Marked × Std.U32 =>
      frames.val - x.2.2.val)
    (inv := fun x : presence.Presence N × presence.Marked × Std.U32 =>
      x.2.2.val ≤ frames.val ∧ Arrived p first.val x.2.2.val x.1 x.2.1)
  · rintro ⟨s, m, d⟩ ⟨hd, harr⟩
    dsimp only at hd harr
    unfold presence.Presence.mark_loop.body
    simp only
    split
    · have hlt : d.val < frames.val := by scalar_tac
      have hf : frames.val ≤ U32.max := by scalar_tac
      have hnext := harr.outcomeOf_next
      obtain ⟨hbase, hheld, hst, hdu, hla, hea⟩ := harr
      step as ⟨outcome, s1, hout, hb1, hh1⟩
      step as ⟨m1, hm1s, hm1d, hm1l, hm1e⟩
      step as ⟨d1, hd1⟩
      have hd1v : d1.val = d.val + 1 := by
        rw [hd1]; exact U32.saturating_add_one_val d frames.val hlt hf
      rw [hnext] at hout
      refine ⟨by omega, ⟨hb1.trans hbase, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
      · intro j
        rw [hh1, hheld, covered_congr hbase, hd1v]
        constructor
        · rintro ((h | ⟨a, b, c⟩) | ⟨rfl, c⟩)
          · exact Or.inl h
          · exact Or.inr ⟨a, by omega, c⟩
          · exact Or.inr ⟨by omega, by omega, c⟩
        · rintro (h | ⟨a, b, c⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hj : j = first.val + d.val
            · exact Or.inr ⟨hj, c⟩
            · exact Or.inl (Or.inr ⟨a, by omega, c⟩)
      · rw [hm1s, hd1v, countOf_succ, hout]
        exact tally_step _ _ d.val frames.val hst (countOf_le _ _ _ _) hlt hf _
      · rw [hm1d, hd1v, countOf_succ, hout]
        exact tally_step _ _ d.val frames.val hdu (countOf_le _ _ _ _) hlt hf _
      · rw [hm1l, hd1v, countOf_succ, hout]
        exact tally_step _ _ d.val frames.val hla (countOf_le _ _ _ _) hlt hf _
      · rw [hm1e, hd1v, countOf_succ, hout]
        exact tally_step _ _ d.val frames.val hea (countOf_le _ _ _ _) hlt hf _
    · have hdf : d.val = frames.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [← hdf]
      exact harr
  · dsimp only
    have h0 : (0#u32).val = 0 := by rfl
    rw [h0]
    refine ⟨by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      constructor
      · exact Or.inl
      · rintro (h | ⟨a, b, -⟩)
        · exact h
        · omega
    all_goals simp [countOf]

/-- The arrival of a packet of `frames` frames from index `first` on. The
stretch stays where it is. A frame is held afterwards exactly when it was held
before or it is a frame of the packet that lies in the stretch. Each count is
the number of the packet's frames whose index has that outcome. -/
@[step]
theorem mark_spec (p : presence.Presence N) (first : Std.U64) (frames : Std.U32) :
    presence.Presence.mark p first frames ⦃ r =>
      Arrived p first.val frames.val r.2 r.1 ⦄ := by
  unfold presence.Presence.mark
  exact mark_loop_spec p first frames

/-- A packet that arrives at a stretch which starts at its first frame and
holds nothing has its first frame stored, if the stretch has room for a frame
and the packet has one. -/
theorem Arrived.stored_pos {p s : presence.Presence N} {first d : ℕ} {m : presence.Marked}
    (h : Arrived p first d s m) (hbase : p.base.val = first) (hempty : ∀ j, ¬ Held p j)
    (hroom : 0 < widthOf N.val) (hd : 0 < d) : 0 < m.stored.val := by
  obtain ⟨-, -, hst, -⟩ := h
  rw [hst]
  unfold countOf
  rw [List.countP_pos_iff]
  refine ⟨0, by simpa using hd, ?_⟩
  have hb : p.base.val ≤ U64.max := by scalar_tac
  have hc : Covered p (first + 0) := by
    unfold Covered
    omega
  have hbit : bitOf p (first + 0) = false := by
    by_contra hcon
    exact hempty (first + 0) ⟨hc, by simpa using hcon⟩
  unfold outcomeOf
  simp only [hc, ↓reduceIte, hbit]
  simp

/-- Two packets leave the same frames held in whichever order they arrive. -/
theorem Arrived.comm {p q r q' r' : presence.Presence N} {a b da db : ℕ}
    {m1 m2 m3 m4 : presence.Marked}
    (h1 : Arrived p a da q m1) (h2 : Arrived q b db r m2)
    (h3 : Arrived p b db q' m3) (h4 : Arrived q' a da r' m4) :
    r.base = r'.base ∧ ∀ j, Held r j ↔ Held r' j := by
  obtain ⟨hb1, hh1, -⟩ := h1
  obtain ⟨hb2, hh2, -⟩ := h2
  obtain ⟨hb3, hh3, -⟩ := h3
  obtain ⟨hb4, hh4, -⟩ := h4
  refine ⟨by rw [hb2, hb1, hb4, hb3], fun j => ?_⟩
  rw [hh2, hh1, hh4, hh3, covered_congr hb1, covered_congr hb3]
  tauto

/-- A packet that arrives a second time changes nothing in what is held, and
none of its frames counts as stored. -/
theorem Arrived.again {p q r : presence.Presence N} {a d : ℕ} {m1 m2 : presence.Marked}
    (h1 : Arrived p a d q m1) (h2 : Arrived q a d r m2) :
    (∀ j, Held r j ↔ Held q j) ∧ m2.stored.val = 0 := by
  obtain ⟨hb1, hh1, -⟩ := h1
  obtain ⟨hb2, hh2, hst, -⟩ := h2
  constructor
  · intro j
    rw [hh2, hh1, covered_congr hb1]
    tauto
  · rw [hst]
    unfold countOf
    rw [List.countP_eq_zero]
    intro k hk
    have hk' : k < d := by simpa using hk
    simp only [decide_eq_true_eq]
    unfold outcomeOf
    by_cases hc : Covered q (a + k)
    · have hheld : Held q (a + k) :=
        (hh1 (a + k)).mpr (Or.inr ⟨by omega, by omega, (covered_congr hb1 _).mp hc⟩)
      simp [hc, hheld.2]
    · simp only [hc, ↓reduceIte]
      split <;> simp


end Unisono.Presence
