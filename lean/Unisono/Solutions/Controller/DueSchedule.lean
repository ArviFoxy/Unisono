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
  (w : World H R) (lookahead : ℕ+) (q : LevelSettings) (share nominal : ℝ)

/-- The reading of the sender's clock at which the left end of block `b` is
due: the value of the schedule of the knots there plus the level that the
rule announces for it. -/
def dueEdge (b : ℕ) : ℝ :=
  w.knotStart nominal b + (announcedAt (ruled p rules) w lookahead q share nominal b).1

/-- By how much the reading that is due increases from one frame to the
next within block `b`: the time from one frame to the next on the schedule
of the knots plus the slope that the rule announces. -/
def dueSlope (b : ℕ) : ℝ :=
  w.knotPeriod nominal b + (announcedAt (ruled p rules) w lookahead q share nominal b).2

variable {p rules w lookahead q share nominal}

/-- What rules with the level rule `knotLevel` announce with a block. -/
theorem announced_eq_announcedAt {need : H → List (Event H R Payload) → Option ℝ}
    (hlev : rules.level = knotLevel q share nominal need) (b : ℕ) :
    rules.announced p w lookahead b
      = announcedAt (ruled p rules) w lookahead q share nominal b := by
  unfold Rules.announced announcedAt
  rw [hlev]
  rfl

/-- **Block `b + 1` starts where block `b` ends.** -/
theorem dueEdge_succ
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) :
    dueEdge p rules w lookahead q share nominal (b + 1)
      = dueEdge p rules w lookahead q share nominal b
        + w.blockLength b * dueSlope p rules w lookahead q share nominal b := by
  obtain ⟨i, hi⟩ := hprog b
  obtain ⟨i', hi'⟩ := hprog (b + 1)
  unfold dueEdge dueSlope
  rw [w.knotStart_succ nominal b, announcedAt_succ _ w lookahead q share nominal hi hi',
    ← w.knotStart_add nominal b]
  ring

/-- **The schedule advances within every block.** -/
theorem dueSlope_pos (hs0 : 0 ≤ share) (hs1 : share < 1) (hnominal : 0 < nominal)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) : 0 < dueSlope p rules w lookahead q share nominal b := by
  obtain ⟨i, hi⟩ := hprog b
  obtain ⟨h1, h2⟩ := knotPeriod_add_slope_pos _ w lookahead q hs0 hs1 hnominal hi
  exact lt_of_lt_of_le h1 h2

/-- **The edges of the blocks increase.** -/
theorem dueEdge_strictMono (hs0 : 0 ≤ share) (hs1 : share < 1) (hnominal : 0 < nominal)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b))) :
    StrictMono (dueEdge p rules w lookahead q share nominal) := by
  refine strictMono_nat_of_lt_succ fun b => ?_
  rw [dueEdge_succ hprog b]
  have hlen : (0 : ℝ) < w.blockLength b := by exact_mod_cast w.blockLength_pos b
  have := mul_pos hlen (dueSlope_pos (q := q) hs0 hs1 hnominal hprog b)
  linarith

/-- The header of a block, by its edge and its slope. -/
theorem runHeader_eq {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture nominal)
    (hlev : rules.level = knotLevel q share nominal need)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) :
    rules.runHeader p w lookahead b
      = ⟨w.source.first b, w.knotStart nominal b, w.knotPeriod nominal b,
        (announcedAt (ruled p rules) w lookahead q share nominal b).1,
        (announcedAt (ruled p rules) w lookahead q share nominal b).2⟩ := by
  obtain ⟨i, hi⟩ := hprog b
  rw [runHeader_knots p rules w lookahead hcap hi, announced_eq_announcedAt hlev b]

/-- **The position that the header of a block says is due** at the reading
`s`: the block's first frame plus the distance of `s` from the block's edge,
divided by the block's slope. -/
theorem runHeader_due {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture nominal)
    (hlev : rules.level = knotLevel q share nominal need)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) (s : ℝ) :
    (rules.runHeader p w lookahead b).due s
      = w.source.first b + (s - dueEdge p rules w lookahead q share nominal b)
          / dueSlope p rules w lookahead q share nominal b := by
  rw [runHeader_eq hcap hlev hprog b]
  unfold Header.due dueEdge dueSlope
  simp only
  ring_nf

/-- **When the header of a block covers a reading.** The header of block
`b` covers the position that it says is due at the reading `s` exactly when
`s` lies from the edge of `b` to just before the edge of `b + 1`. -/
theorem covers_iff {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture nominal)
    (hlev : rules.level = knotLevel q share nominal need) (hs0 : 0 ≤ share) (hs1 : share < 1)
    (hnominal : 0 < nominal)
    (hprog : ∀ b, ∃ i, (ruled p rules : Solution H R Payload).handled w lookahead i
      = some (w.sender, w.source.handed b,
        .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)))
    (b : ℕ) (s : ℝ) :
    (rules.runHeader p w lookahead b).Covers (w.blockLength b) s
      ↔ dueEdge p rules w lookahead q share nominal b ≤ s
        ∧ s < dueEdge p rules w lookahead q share nominal (b + 1) := by
  have hpos := dueSlope_pos (q := q) hs0 hs1 hnominal hprog b
  have hdue := runHeader_due hcap hlev hprog b s
  have hslope : (rules.runHeader p w lookahead b).period
      + (rules.runHeader p w lookahead b).slope
      = dueSlope p rules w lookahead q share nominal b := by
    rw [runHeader_eq hcap hlev hprog b]
    rfl
  have hfirst : ((rules.runHeader p w lookahead b).first : ℝ) = w.source.first b := by
    rw [runHeader_eq hcap hlev hprog b]
  unfold Header.Covers
  rw [hslope, hdue, hfirst, dueEdge_succ hprog b]
  constructor
  · rintro ⟨-, h1, h2⟩
    have h3 : 0 ≤ (s - dueEdge p rules w lookahead q share nominal b)
        / dueSlope p rules w lookahead q share nominal b := by linarith
    have h4 : (s - dueEdge p rules w lookahead q share nominal b)
        / dueSlope p rules w lookahead q share nominal b < w.blockLength b := by linarith
    rw [div_lt_iff₀ hpos] at h4
    have h5 := (div_nonneg_iff.mp h3).resolve_right (by
      rintro ⟨-, h6⟩
      linarith)
    exact ⟨by linarith [h5.1], by linarith⟩
  · rintro ⟨h1, h2⟩
    have h3 : 0 ≤ (s - dueEdge p rules w lookahead q share nominal b)
        / dueSlope p rules w lookahead q share nominal b :=
      div_nonneg (by linarith) hpos.le
    have h4 : (s - dueEdge p rules w lookahead q share nominal b)
        / dueSlope p rules w lookahead q share nominal b < w.blockLength b := by
      rw [div_lt_iff₀ hpos]
      linarith
    exact ⟨hpos, by linarith, by linarith⟩

/-- **At most one block covers a reading.** -/
theorem covers_unique {need : H → List (Event H R Payload) → Option ℝ}
    (hcap : rules.capture = knotCapture nominal)
    (hlev : rules.level = knotLevel q share nominal need) (hs0 : 0 ≤ share) (hs1 : share < 1)
    (hnominal : 0 < nominal)
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
    (hcap : rules.capture = knotCapture nominal)
    (hlev : rules.level = knotLevel q share nominal need) (hs0 : 0 ≤ share) (hs1 : share < 1)
    (hnominal : 0 < nominal)
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

end Unisono.Solutions.Controller
