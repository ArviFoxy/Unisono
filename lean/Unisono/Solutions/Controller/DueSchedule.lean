/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.KnotLevel

/-!
# The schedule on which positions are due

With the capture schedule of the knots (`knotCapture`) and the level rule
`knotLevel`, every block's header gives a line: the reading of the sender's
clock at which each coordinate of the block is due, its capture time plus
its level. This file shows that the lines of all blocks form one schedule
that is continuous and increases, in every world in which the capture
device hands over blocks without end.

For the run of the controller with such rules:

* `dueEdge b` is the reading at which the left end of block `b` is due, and
  `dueSlope b` is by how much the reading that is due increases from one
  frame to the next within block `b`.
* `dueEdge_succ`: block `b + 1` starts where block `b` ends.
* `dueSlope_pos`, `dueEdge_strictMono`: the slope is positive, so the edges
  increase.
* `covers_iff`: the header of block `b` covers the position that it says is
  due at the reading `s` exactly when `s` lies from the edge of `b` to just
  before the edge of `b + 1`; `runHeader_due` gives that position.
* `covers_unique`: at most one block covers a reading.
* `dueOf_eq_of_mem`: so a host that holds the header of the block that
  covers `s` finds that block's position, whichever other headers it holds.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : FixedDelay.Params H) (rules : Rules H R)
  (w : World H R) (lookahead : ℕ+) (q : LevelSettings) (share : ℝ) (kn : KnotSettings)

/-- The reading of the sender's clock at which the left end of block `b` is
due: the value of the schedule of the knots there plus the level that the
rule announces for it. -/
def dueEdge (b : ℕ) : ℝ :=
  w.knotStart kn b + (announcedAt (ruled p rules) w lookahead q share kn b).1

/-- By how much the reading that is due increases from one frame to the
next within block `b`: the time from one frame to the next on the schedule
of the knots plus the slope that the rule announces. -/
def dueSlope (b : ℕ) : ℝ :=
  w.knotPeriod kn b + (announcedAt (ruled p rules) w lookahead q share kn b).2

variable {p rules w lookahead q share kn}

/-- What rules with the level rule `knotLevel` announce with a block. -/
theorem announced_eq_announcedAt {need : H → List (Event H R Payload) → Option ℝ}
    (hlev : rules.level = knotLevel q share kn need) (b : ℕ) :
    rules.announced p w lookahead b
      = announcedAt (ruled p rules) w lookahead q share kn b := by
  unfold Rules.announced announcedAt
  rw [hlev]
  rfl

/-- **Block `b + 1` starts where block `b` ends.** -/
theorem dueEdge_succ
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) :
    dueEdge p rules w lookahead q share kn (b + 1)
      = dueEdge p rules w lookahead q share kn b
        + w.blockLength b * dueSlope p rules w lookahead q share kn b := by
  obtain ⟨i, hi⟩ := hprog b
  obtain ⟨i', hi'⟩ := hprog (b + 1)
  unfold dueEdge dueSlope
  rw [w.knotStart_succ kn b, announcedAt_succ _ w lookahead q share kn hi hi',
    ← w.knotStart_add kn b]
  ring

/-- **The schedule advances within every block.** -/
theorem dueSlope_pos (hs0 : 0 ≤ share) (hs1 : share < 1) (hnominal : kn.Valid)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) : 0 < dueSlope p rules w lookahead q share kn b := by
  obtain ⟨i, hi⟩ := hprog b
  obtain ⟨h1, h2⟩ := knotPeriod_add_slope_pos _ w lookahead q hs0 hs1 hnominal hi
  exact lt_of_lt_of_le h1 h2

/-- **The slope of the schedule in every block is the nominal time from one
frame to the next, within the shares `bound` and `share`**, in every world:
at least `(1 - share) * (1 - bound)` times the nominal time, and at most
`(1 + share) * (1 + bound)` times it. -/
theorem dueSlope_mem (hs0 : 0 ≤ share) (hs1 : share < 1) (hnominal : kn.Valid)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) :
    (1 - share) * (kn.nominal * (1 - kn.bound))
        ≤ dueSlope p rules w lookahead q share kn b
      ∧ dueSlope p rules w lookahead q share kn b
        ≤ (1 + share) * (kn.nominal * (1 + kn.bound)) := by
  obtain ⟨i, hi⟩ := hprog b
  obtain ⟨-, h2⟩ := knotPeriod_add_slope_pos _ w lookahead q hs0 hs1 hnominal hi
  have h3 := knotPeriod_add_slope_le _ w lookahead q hs0 hnominal hi
  obtain ⟨hp1, hp2⟩ := w.knotPeriod_mem hnominal b
  exact ⟨le_trans (mul_le_mul_of_nonneg_left hp1 (by linarith)) h2,
    le_trans h3 (mul_le_mul_of_nonneg_left hp2 (by linarith))⟩

/-- **The edges of the blocks increase.** -/
theorem dueEdge_strictMono (hs0 : 0 ≤ share) (hs1 : share < 1) (hnominal : kn.Valid)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    StrictMono (dueEdge p rules w lookahead q share kn) := by
  refine strictMono_nat_of_lt_succ fun b => ?_
  rw [dueEdge_succ hprog b]
  have hlen : (0 : ℝ) < w.blockLength b := by exact_mod_cast w.blockLength_pos b
  have := mul_pos hlen (dueSlope_pos (q := q) hs0 hs1 hnominal hprog b)
  linarith

/-- The header of a block, by its edge and its slope. -/
theorem runHeader_eq {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture kn)
    (hlev : rules.level = knotLevel q share kn need)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) :
    rules.runHeader p w lookahead b
      = ⟨w.source.first b, w.handedReading b - w.blockLength b * w.knotPeriod kn b,
        w.knotPeriod kn b,
        (announcedAt (ruled p rules) w lookahead q share kn b).1
          + (w.knot kn b - w.handedReading b),
        (announcedAt (ruled p rules) w lookahead q share kn b).2⟩ := by
  obtain ⟨i, hi⟩ := hprog b
  rw [runHeader_knots p rules w lookahead hcap hi, announced_eq_announcedAt hlev b]

/-- **The position that the header of a block says is due** at the reading
`s`: the block's first frame plus the distance of `s` from the block's edge,
divided by the block's slope. -/
theorem runHeader_due {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture kn)
    (hlev : rules.level = knotLevel q share kn need)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) (s : ℝ) :
    (rules.runHeader p w lookahead b).due s
      = w.source.first b + (s - dueEdge p rules w lookahead q share kn b)
          / dueSlope p rules w lookahead q share kn b := by
  rw [runHeader_eq hcap hlev hprog b]
  unfold Header.due dueEdge dueSlope World.knotStart
  simp only
  ring_nf

/-- **When the header of a block covers a reading.** The header of block
`b` covers the position that it says is due at the reading `s` exactly when
`s` lies from the edge of `b` to just before the edge of `b + 1`. -/
theorem covers_iff {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture kn)
    (hlev : rules.level = knotLevel q share kn need) (hs0 : 0 ≤ share) (hs1 : share < 1)
    (hnominal : kn.Valid)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) (s : ℝ) :
    (rules.runHeader p w lookahead b).Covers (w.blockLength b) s
      ↔ dueEdge p rules w lookahead q share kn b ≤ s
        ∧ s < dueEdge p rules w lookahead q share kn (b + 1) := by
  have hpos := dueSlope_pos (q := q) hs0 hs1 hnominal hprog b
  have hdue := runHeader_due hcap hlev hprog b s
  have hslope : (rules.runHeader p w lookahead b).period
      + (rules.runHeader p w lookahead b).slope
      = dueSlope p rules w lookahead q share kn b := by
    rw [runHeader_eq hcap hlev hprog b]
    rfl
  have hfirst : ((rules.runHeader p w lookahead b).first : ℝ) = w.source.first b := by
    rw [runHeader_eq hcap hlev hprog b]
  unfold Header.Covers
  rw [hslope, hdue, hfirst, dueEdge_succ hprog b]
  constructor
  · rintro ⟨-, h1, h2⟩
    have h3 : 0 ≤ (s - dueEdge p rules w lookahead q share kn b)
        / dueSlope p rules w lookahead q share kn b := by linarith
    have h4 : (s - dueEdge p rules w lookahead q share kn b)
        / dueSlope p rules w lookahead q share kn b < w.blockLength b := by linarith
    rw [div_lt_iff₀ hpos] at h4
    have h5 := (div_nonneg_iff.mp h3).resolve_right (by
      rintro ⟨-, h6⟩
      linarith)
    exact ⟨by linarith [h5.1], by linarith⟩
  · rintro ⟨h1, h2⟩
    have h3 : 0 ≤ (s - dueEdge p rules w lookahead q share kn b)
        / dueSlope p rules w lookahead q share kn b :=
      div_nonneg (by linarith) hpos.le
    have h4 : (s - dueEdge p rules w lookahead q share kn b)
        / dueSlope p rules w lookahead q share kn b < w.blockLength b := by
      rw [div_lt_iff₀ hpos]
      linarith
    exact ⟨hpos, by linarith, by linarith⟩

/-- **At most one block covers a reading.** -/
theorem covers_unique {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture kn)
    (hlev : rules.level = knotLevel q share kn need) (hs0 : 0 ≤ share) (hs1 : share < 1)
    (hnominal : kn.Valid)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    {b b' : ℕ} {s : ℝ}
    (hb : (rules.runHeader p w lookahead b).Covers (w.blockLength b) s)
    (hb' : (rules.runHeader p w lookahead b').Covers (w.blockLength b') s) : b = b' := by
  obtain ⟨h1, h2⟩ := (covers_iff hcap hlev hs0 hs1 hnominal hprog b s).mp hb
  obtain ⟨h1', h2'⟩ := (covers_iff hcap hlev hs0 hs1 hnominal hprog b' s).mp hb'
  have hmono := dueEdge_strictMono (p := p) (rules := rules) (w := w) (lookahead := lookahead)
    (q := q) hs0 hs1 hnominal hprog
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · have := hmono.monotone (show b + 1 ≤ b' from hlt)
    linarith
  · exact heq
  · have := hmono.monotone (show b' + 1 ≤ b from hgt)
    linarith

/-- **A host that holds the header of the covering block finds its
position.** Let every header in a list be the header of some block of the
run, with the block's number of frames. If the list holds the header of a
block `b` that covers the reading `s`, the position that is due at `s` by
the list is the one that the header of `b` gives. -/
theorem dueOf_eq_of_mem {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture kn)
    (hlev : rules.level = knotLevel q share kn need) (hs0 : 0 ≤ share) (hs1 : share < 1)
    (hnominal : kn.Valid)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    {hs : List (Header × ℕ)}
    (hall : ∀ x ∈ hs, ∃ c, x = (rules.runHeader p w lookahead c, w.blockLength c))
    {b : ℕ} {s : ℝ}
    (hmem : (rules.runHeader p w lookahead b, w.blockLength b) ∈ hs)
    (hcov : (rules.runHeader p w lookahead b).Covers (w.blockLength b) s) :
    dueOf hs s = some ((rules.runHeader p w lookahead b).due s) := by
  classical
  unfold dueOf
  cases hfind : hs.find? (fun e => decide (e.1.Covers e.2 s)) with
  | none =>
    have := List.find?_eq_none.mp hfind _ hmem
    simp only [decide_eq_true_eq] at this
    exact absurd hcov this
  | some x =>
    have hx := List.mem_of_find?_eq_some hfind
    have hxc : x.1.Covers x.2 s := by
      have := List.find?_some hfind
      simpa using this
    obtain ⟨c, rfl⟩ := hall x hx
    obtain rfl := covers_unique hcap hlev hs0 hs1 hnominal hprog hxc hcov
    rfl

/-! ## The schedule as a function of the coordinate -/

variable (p rules w lookahead q share kn) in
/-- The reading of the sender's clock at which the coordinate `z` is due, by
the line of block `b`. -/
def dueAt (b : ℕ) (z : ℝ) : ℝ :=
  dueEdge p rules w lookahead q share kn b
    + (z - w.source.first b) * dueSlope p rules w lookahead q share kn b

/-- At the first frame of the next block, the line of a block gives the edge
of the next block. -/
theorem dueAt_right
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) :
    dueAt p rules w lookahead q share kn b (w.source.first (b + 1))
      = dueEdge p rules w lookahead q share kn (b + 1) := by
  have hle : w.source.first b ≤ w.source.first (b + 1) :=
    (w.source.first_strictMono (Nat.lt_succ_self b)).le
  have hcast : ((w.blockLength b : ℕ) : ℝ)
      = (w.source.first (b + 1) : ℝ) - w.source.first b := by
    unfold World.blockLength
    rw [Nat.cast_sub hle]
  unfold dueAt
  rw [dueEdge_succ hprog b, hcast]

/-- **The schedule against the slopes of the blocks.** Let the coordinate
`z` lie at or before the right end of block `b`, and the coordinate `z'` in
a block `b'` at or after `b`, with `z ≤ z'`, and let the slopes of the blocks from `b` to `b'` lie
between `σLo` and `σHi`. Then from `z` to `z'` the reading that is due
increases by at least `σLo * (z' - z)` and by at most `σHi * (z' - z)`. -/
theorem dueAt_sub_mem
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    {σLo σHi : ℝ} {b : ℕ} {z : ℝ} (hz2 : z ≤ w.source.first (b + 1)) :
    ∀ b', b ≤ b' →
      (∀ c, b ≤ c → c ≤ b' → σLo ≤ dueSlope p rules w lookahead q share kn c
        ∧ dueSlope p rules w lookahead q share kn c ≤ σHi) →
      ∀ z' : ℝ, (w.source.first b' : ℝ) ≤ z' → z' ≤ w.source.first (b' + 1) → z ≤ z' →
        σLo * (z' - z) ≤ dueAt p rules w lookahead q share kn b' z'
            - dueAt p rules w lookahead q share kn b z
          ∧ dueAt p rules w lookahead q share kn b' z'
              - dueAt p rules w lookahead q share kn b z ≤ σHi * (z' - z) := by
  intro b' hbb'
  induction b', hbb' using Nat.le_induction with
  | base =>
    intro hσ z' _ _ hzz'
    obtain ⟨h1, h2⟩ := hσ b le_rfl le_rfl
    have hd : dueAt p rules w lookahead q share kn b z'
        - dueAt p rules w lookahead q share kn b z
        = (z' - z) * dueSlope p rules w lookahead q share kn b := by
      unfold dueAt
      ring
    rw [hd]
    have h0 : 0 ≤ z' - z := sub_nonneg.mpr hzz'
    constructor <;> nlinarith
  | succ b' hbb' ih =>
    intro hσ z' hz1' hz2' hzz'
    obtain ⟨h1, h2⟩ := hσ (b' + 1) (Nat.le_succ_of_le hbb') le_rfl
    have hfirst : (w.source.first (b + 1) : ℝ) ≤ w.source.first (b' + 1) := by
      exact_mod_cast w.source.first_strictMono.monotone (Nat.succ_le_succ hbb')
    have hfb' : (w.source.first b' : ℝ) ≤ w.source.first (b' + 1) := by
      exact_mod_cast (w.source.first_strictMono (Nat.lt_succ_self b')).le
    obtain ⟨i1, i2⟩ := ih (fun c hc1 hc2 => hσ c hc1 (Nat.le_succ_of_le hc2))
      (w.source.first (b' + 1)) hfb' le_rfl (le_trans hz2 hfirst)
    rw [dueAt_right hprog b'] at i1 i2
    have hd : dueAt p rules w lookahead q share kn (b' + 1) z'
        = dueEdge p rules w lookahead q share kn (b' + 1)
          + (z' - w.source.first (b' + 1))
            * dueSlope p rules w lookahead q share kn (b' + 1) := rfl
    rw [hd]
    have h0 : 0 ≤ z' - w.source.first (b' + 1) := sub_nonneg.mpr hz1'
    constructor <;> nlinarith

end Unisono.Solutions.Controller
