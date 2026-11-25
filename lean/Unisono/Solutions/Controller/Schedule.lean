/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The schedule of a level that changes

The sender of the controller announces, with every block of the source, the
level of the block's first frame and the change of the level from one frame
to the next (`Header.level`, `Header.slope`). This file collects what
follows from the announcements alone, as facts about real numbers.

* `levelAt`: the level that the announcements give to a position: the level
  of the block of the position plus the slope of that block for each frame
  since the block's first.
* `levelAt_of_mem`: its value inside a block.
* `lt_of_levelAt`: when each block starts at the level at which the block
  before it ended, and the time `π` from one frame to the next plus the
  slope is positive in every block, the time at which a position is due,
  `π * x + levelAt x`, increases strictly with the position. So at most one
  position is due at any time.
* `Header.eq_of_due`, `Header.due_of_eq`: the position that a header says is
  due when the sender's clock reads `s` is the position whose capture time
  plus level, both by the header, is `s`.

The first block of the stream, block zero, is left out of the conditions:
its header is not made from the line of the capture device.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

/-- The level that the announcements give to the position `x`, for blocks of
`B` frames: `ann b` is the level of the first frame of block `b` and the
change of the level from one frame to the next within the block. -/
def levelAt (ann : ℕ → ℝ × ℝ) (B : ℕ) (x : ℝ) : ℝ :=
  (ann (⌊x⌋₊ / B)).1 + (x - ((⌊x⌋₊ / B * B : ℕ) : ℝ)) * (ann (⌊x⌋₊ / B)).2

/-- The block of a position, and its level, when the position lies among
the frames of block `c`. -/
theorem levelAt_of_mem (ann : ℕ → ℝ × ℝ) {B c : ℕ} {x : ℝ}
    (hlo : ((c * B : ℕ) : ℝ) ≤ x) (hhi : x < ((c * B : ℕ) : ℝ) + B) :
    ⌊x⌋₊ / B = c ∧ levelAt ann B x = (ann c).1 + (x - ((c * B : ℕ) : ℝ)) * (ann c).2 := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hlo
  have h1 : c * B ≤ ⌊x⌋₊ := Nat.le_floor hlo
  have h2 : ⌊x⌋₊ < c * B + B := by
    have h3 : x < ((c * B + B : ℕ) : ℝ) := by
      push_cast
      push_cast at hhi
      exact hhi
    exact (Nat.floor_lt hx0).mpr h3
  have hdiv : ⌊x⌋₊ / B = c := Nat.div_eq_of_lt_le h1 (by
    have e : (c + 1) * B = c * B + B := by ring
    rw [e]
    exact h2)
  refine ⟨hdiv, ?_⟩
  unfold levelAt
  rw [hdiv]

/-- **The time at which a position is due increases with the position.** Let
`ann b` be the level and the slope that the sender announces with block
`b`, for blocks of `B > 0` frames, and `π` the time from one frame to the
next. From block one on, let every block start at the level at which the
block before it ended, and let `π` plus the slope be positive. Then for two
positions `x < y` past the first block, `π * x` plus the level of `x` is
less than `π * y` plus the level of `y`. -/
theorem lt_of_levelAt {ann : ℕ → ℝ × ℝ} {B : ℕ} (hB : 0 < B) {π : ℝ}
    (hcont : ∀ b, 1 ≤ b → (ann (b + 1)).1 = (ann b).1 + (B : ℝ) * (ann b).2)
    (hslope : ∀ b, 1 ≤ b → 0 < π + (ann b).2) {x y : ℝ} (hx : (B : ℝ) ≤ x) (hxy : x < y) :
    π * x + levelAt ann B x < π * y + levelAt ann B y := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hx0 : 0 ≤ x := le_trans hBpos.le hx
  have hy0 : 0 ≤ y := le_trans hx0 hxy.le
  -- The blocks of the two positions.
  have hblock : ∀ z : ℝ, 0 ≤ z → ((⌊z⌋₊ / B * B : ℕ) : ℝ) ≤ z
      ∧ z < ((⌊z⌋₊ / B * B : ℕ) : ℝ) + B := by
    intro z hz
    have h1 := Nat.div_mul_le_self ⌊z⌋₊ B
    have h2 := Nat.lt_div_mul_add hB (a := ⌊z⌋₊)
    have h3 : ((⌊z⌋₊ / B * B : ℕ) : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast h1
    have h4 : (⌊z⌋₊ : ℝ) + 1 ≤ ((⌊z⌋₊ / B * B : ℕ) : ℝ) + (B : ℝ) := by exact_mod_cast h2
    have h5 := Nat.floor_le hz
    have h6 := Nat.lt_floor_add_one z
    constructor <;> linarith
  have hcx1 : 1 ≤ ⌊x⌋₊ / B := by
    have h1 : B ≤ ⌊x⌋₊ := Nat.le_floor hx
    exact (Nat.le_div_iff_mul_le hB).mpr (by simpa using h1)
  have hcxy : ⌊x⌋₊ / B ≤ ⌊y⌋₊ / B := Nat.div_le_div_right (Nat.floor_le_floor hxy.le)
  -- The time at which the first frame of a block is due.
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ, ∀ b, G b = π * ((b * B : ℕ) : ℝ) + (ann b).1 := ⟨_, fun _ => rfl⟩
  have hstep : ∀ b, 1 ≤ b → G (b + 1) = G b + (B : ℝ) * (π + (ann b).2) := by
    intro b hb
    rw [hG, hG, hcont b hb]
    push_cast
    ring
  have hmono : ∀ j b, 1 ≤ b → G b ≤ G (b + j) := by
    intro j
    induction j with
    | zero =>
      intro b _
      exact le_rfl
    | succ j ih =>
      intro b hb
      have h1 := ih b hb
      have h2 := hstep (b + j) (by omega)
      have h3 := mul_pos hBpos (hslope (b + j) (by omega))
      rw [show b + (j + 1) = b + j + 1 from rfl]
      linarith
  -- The value inside a block.
  have hval : ∀ z : ℝ, π * z + levelAt ann B z
      = G (⌊z⌋₊ / B) + (z - ((⌊z⌋₊ / B * B : ℕ) : ℝ)) * (π + (ann (⌊z⌋₊ / B)).2) := by
    intro z
    rw [hG]
    unfold levelAt
    ring
  rw [hval x, hval y]
  obtain ⟨hxlo, hxhi⟩ := hblock x hx0
  obtain ⟨hylo, hyhi⟩ := hblock y hy0
  rcases Nat.eq_or_lt_of_le hcxy with heq | hlt
  · rw [← heq] at hylo hyhi ⊢
    have h1 := hslope _ hcx1
    nlinarith
  · have h1 := hslope _ hcx1
    have h2 := hstep _ hcx1
    have h3 := hmono (⌊y⌋₊ / B - (⌊x⌋₊ / B + 1)) (⌊x⌋₊ / B + 1) (by omega)
    rw [show ⌊x⌋₊ / B + 1 + (⌊y⌋₊ / B - (⌊x⌋₊ / B + 1)) = ⌊y⌋₊ / B from by omega] at h3
    have h4 := hslope (⌊y⌋₊ / B) (by omega)
    have h5 : (x - ((⌊x⌋₊ / B * B : ℕ) : ℝ)) * (π + (ann (⌊x⌋₊ / B)).2)
        < (B : ℝ) * (π + (ann (⌊x⌋₊ / B)).2) :=
      mul_lt_mul_of_pos_right (by linarith) h1
    have h6 : 0 ≤ (y - ((⌊y⌋₊ / B * B : ℕ) : ℝ)) * (π + (ann (⌊y⌋₊ / B)).2) :=
      mul_nonneg (by linarith) h4.le
    linarith

/-- **What a header says is due.** If the header says that the position `x`
is due when the sender's clock reads `s`, and its schedule advances with the
position, then the capture time of `x` plus the level of `x`, both by the
header, is `s`. -/
theorem Header.eq_of_due {hd : Header} {s x : ℝ} (hpos : 0 < hd.period + hd.slope)
    (hx : hd.due s = x) :
    hd.capture + (x - hd.first) * hd.period + (hd.level + (x - hd.first) * hd.slope) = s := by
  unfold Header.due at hx
  rw [← hx]
  field_simp
  ring

/-- The converse of `Header.eq_of_due`. -/
theorem Header.due_of_eq {hd : Header} {s x : ℝ} (hpos : 0 < hd.period + hd.slope)
    (hx : hd.capture + (x - hd.first) * hd.period + (hd.level + (x - hd.first) * hd.slope)
      = s) :
    hd.due s = x := by
  unfold Header.due
  rw [← hx]
  field_simp
  ring

end Unisono.Solutions.Controller
