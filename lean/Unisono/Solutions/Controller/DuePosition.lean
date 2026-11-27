/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Targets

/-!
# The position that is due at a reading, as a function of the reading

The schedule of the controller gives, for every block `b`, the stretch of
readings of the sender's clock from the edge of `b` to the edge of `b + 1`,
and within it the position that is due at each reading. `duePos s` is that
position for the block whose stretch holds `s`, moved back by `rules.back`:
the position that a host chooses when its estimate is `s`
(`chosen_eq_some_iff`). It is a function of the world and of the run of the
sender, not of any host's estimate.

* `exists_dueEdge_cover`: a reading from the edge of a block to before the
  edge of a later block is held by the stretch of a block between them.
* `duePos_eq`: its value from the block whose stretch holds the reading.
* `duePos_sub_mem`: in the setting `KnotSetting`, from a reading `s` to a
  later reading `s'`, both held by stretches of blocks, the position that is
  due advances by at least `s' - s` divided by the largest slope of the
  schedule and by at most `s' - s` divided by the least slope. The slopes
  are those of `dueSlope_mem`: the nominal time from one frame to the next,
  within the shares `bound` and `share`.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : FixedDelay.Params H) (rules : Rules H R)
  (w : World H R) (lookahead : ℕ+) (q : LevelSettings) (share : ℝ) (kn : KnotSettings)

open Classical in
/-- **The position that is due when the sender's clock reads `s`**, by the
schedule of the run: for the block `b` whose stretch of the schedule holds
`s`, the block's first frame plus the distance of `s` from the block's edge
divided by the block's slope, moved back by `rules.back`. Zero if no block's
stretch holds `s`. -/
def duePos (s : ℝ) : ℝ :=
  if h : ∃ b, dueEdge p rules w lookahead q share kn b ≤ s
      ∧ s < dueEdge p rules w lookahead q share kn (b + 1) then
    w.source.first (Classical.choose h)
      + (s - dueEdge p rules w lookahead q share kn (Classical.choose h))
        / dueSlope p rules w lookahead q share kn (Classical.choose h)
      - rules.back
  else 0

variable {p rules w lookahead q share kn}

/-- **A reading between two edges is held by the stretch of a block between
them**, when the edges of the blocks increase: if `s` lies from the edge of
block `b₁` to before the edge of block `b₂`, some block from `b₁` to before
`b₂` has `s` from its edge to before the edge of the next block. -/
theorem exists_dueEdge_cover (hmono : StrictMono (dueEdge p rules w lookahead q share kn))
    {b₁ b₂ : ℕ} {s : ℝ} (h1 : dueEdge p rules w lookahead q share kn b₁ ≤ s)
    (h2 : s < dueEdge p rules w lookahead q share kn b₂) :
    ∃ b, b₁ ≤ b ∧ b < b₂ ∧ dueEdge p rules w lookahead q share kn b ≤ s
      ∧ s < dueEdge p rules w lookahead q share kn (b + 1) := by
  classical
  have hb₂ : 0 < b₂ := by
    rcases Nat.eq_zero_or_pos b₂ with h0 | hpos
    · subst h0
      have := hmono.monotone (Nat.zero_le b₁)
      linarith
    · exact hpos
  have hex : ∃ b, s < dueEdge p rules w lookahead q share kn (b + 1) :=
    ⟨b₂ - 1, by rw [Nat.sub_add_cancel hb₂]; exact h2⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ b₂ - 1 :=
    Nat.find_min' hex (by rw [Nat.sub_add_cancel hb₂]; exact h2)
  have hge : b₁ ≤ Nat.find hex := by
    by_contra hlt
    have := hmono.monotone (Nat.succ_le_of_lt (not_le.mp hlt))
    linarith
  refine ⟨Nat.find hex, hge, by omega, ?_, hspec⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · have h3 : b₁ = 0 := by omega
    rw [h0, ← h3]
    exact h1
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel hpos] at hmin
    exact not_lt.mp hmin

/-- **The position that is due at a reading held by the stretch of block
`b`**, when the edges of the blocks increase. -/
theorem duePos_eq (hmono : StrictMono (dueEdge p rules w lookahead q share kn)) {b : ℕ}
    {s : ℝ} (h1 : dueEdge p rules w lookahead q share kn b ≤ s)
    (h2 : s < dueEdge p rules w lookahead q share kn (b + 1)) :
    duePos p rules w lookahead q share kn s
      = w.source.first b + (s - dueEdge p rules w lookahead q share kn b)
          / dueSlope p rules w lookahead q share kn b - rules.back := by
  classical
  have hex : ∃ b, dueEdge p rules w lookahead q share kn b ≤ s
      ∧ s < dueEdge p rules w lookahead q share kn (b + 1) := ⟨b, h1, h2⟩
  obtain ⟨h1', h2'⟩ := Classical.choose_spec hex
  have hb : Classical.choose hex = b := by
    rcases lt_trichotomy (Classical.choose hex) b with hlt | heq | hgt
    · have := hmono.monotone (Nat.succ_le_of_lt hlt)
      linarith
    · exact heq
    · have := hmono.monotone (Nat.succ_le_of_lt hgt)
      linarith
  unfold duePos
  rw [dite_eq_left hex, hb]

/-- **How the position that is due advances with the reading.** In the
setting `KnotSetting`, let the stretch of block `b` hold the reading `s`,
and the stretch of block `b'` a reading `s' ≥ s`. Then from `s` to `s'` the
position that is due advances by at least `s' - s` divided by
`(1 + share) * (nominal * (1 + bound))`, and by at most `s' - s` divided by
`(1 - share) * (nominal * (1 - bound))`. -/
theorem duePos_sub_mem {A : H → H → Time → Time}
    (hK : KnotSetting p rules w A q share kn) (lookahead : ℕ+) {b b' : ℕ} {s s' : ℝ}
    (h1 : dueEdge p rules w lookahead q share kn b ≤ s)
    (h2 : s < dueEdge p rules w lookahead q share kn (b + 1))
    (h1' : dueEdge p rules w lookahead q share kn b' ≤ s')
    (h2' : s' < dueEdge p rules w lookahead q share kn (b' + 1)) (hss' : s ≤ s') :
    (s' - s) / ((1 + share) * (kn.nominal * (1 + kn.bound)))
        ≤ duePos p rules w lookahead q share kn s' - duePos p rules w lookahead q share kn s
      ∧ duePos p rules w lookahead q share kn s' - duePos p rules w lookahead q share kn s
        ≤ (s' - s) / ((1 - share) * (kn.nominal * (1 - kn.bound))) := by
  have hprog := hK.handovers lookahead
  have hs0 := hK.share_nonneg
  have hs1 := hK.share_lt_one
  obtain ⟨hn, hb0, hb1⟩ := hK.nominal_pos
  have hmonoE := dueEdge_strictMono (p := p) (rules := rules) (w := w) (lookahead := lookahead)
    (q := q) hs0 hs1 hK.nominal_pos hprog
  have hslope := fun c => dueSlope_mem (p := p) (rules := rules) (w := w)
    (lookahead := lookahead) (q := q) hs0 hs1 hK.nominal_pos hprog c
  have hσlo : 0 < (1 - share) * (kn.nominal * (1 - kn.bound)) :=
    mul_pos (by linarith) (mul_pos hn (by linarith))
  have hσhi : 0 < (1 + share) * (kn.nominal * (1 + kn.bound)) :=
    mul_pos (by linarith) (mul_pos hn (by linarith))
  have hpos : ∀ c, 0 < dueSlope p rules w lookahead q share kn c :=
    fun c => lt_of_lt_of_le hσlo (hslope c).1
  rw [duePos_eq hmonoE h1 h2, duePos_eq hmonoE h1' h2']
  -- The two coordinates.
  obtain ⟨z, hz⟩ : ∃ z, z = (w.source.first b : ℝ)
      + (s - dueEdge p rules w lookahead q share kn b)
        / dueSlope p rules w lookahead q share kn b := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z', z' = (w.source.first b' : ℝ)
      + (s' - dueEdge p rules w lookahead q share kn b')
        / dueSlope p rules w lookahead q share kn b' := ⟨_, rfl⟩
  rw [← hz, ← hz']
  have hbb' : b ≤ b' := by
    by_contra hlt
    have := hmonoE.monotone (Nat.succ_le_of_lt (not_le.mp hlt))
    linarith
  have hcast : ∀ c : ℕ, (w.source.first (c + 1) : ℝ)
      = (w.source.first c : ℝ) + w.blockLength c := by
    intro c
    have hle : w.source.first c ≤ w.source.first (c + 1) :=
      (w.source.first_strictMono (Nat.lt_succ_self c)).le
    unfold World.blockLength
    rw [Nat.cast_sub hle]
    ring
  have hz1 : (w.source.first b : ℝ) ≤ z := by
    rw [hz]
    have := div_nonneg (by linarith : 0 ≤ s - dueEdge p rules w lookahead q share kn b)
      (hpos b).le
    linarith
  have hz2 : z ≤ w.source.first (b + 1) := by
    rw [hz, hcast b, add_le_add_iff_left, div_le_iff₀ (hpos b)]
    have := dueEdge_succ (p := p) (rules := rules) (w := w) (lookahead := lookahead) (q := q)
      (share := share) (kn := kn) hprog b
    linarith
  have hz1' : (w.source.first b' : ℝ) ≤ z' := by
    rw [hz']
    have := div_nonneg (by linarith : 0 ≤ s' - dueEdge p rules w lookahead q share kn b')
      (hpos b').le
    linarith
  have hz2' : z' ≤ w.source.first (b' + 1) := by
    rw [hz', hcast b', add_le_add_iff_left, div_le_iff₀ (hpos b')]
    have := dueEdge_succ (p := p) (rules := rules) (w := w) (lookahead := lookahead) (q := q)
      (share := share) (kn := kn) hprog b'
    linarith
  have hzz' : z ≤ z' := by
    rcases eq_or_lt_of_le hbb' with heq | hlt
    · subst heq
      rw [hz, hz', add_le_add_iff_left]
      exact div_le_div_of_nonneg_right (by linarith) (hpos b).le
    · have hfirst : (w.source.first (b + 1) : ℝ) ≤ w.source.first b' := by
        exact_mod_cast w.source.first_strictMono.monotone (Nat.succ_le_of_lt hlt)
      linarith
  have hdz : dueAt p rules w lookahead q share kn b z = s := by
    unfold dueAt
    rw [hz, add_sub_cancel_left, div_mul_cancel₀ _ (hpos b).ne']
    ring
  have hdz' : dueAt p rules w lookahead q share kn b' z' = s' := by
    unfold dueAt
    rw [hz', add_sub_cancel_left, div_mul_cancel₀ _ (hpos b').ne']
    ring
  obtain ⟨hlo, hhi⟩ := dueAt_sub_mem hprog hz2 b' hbb' (fun c _ _ => hslope c) z' hz1' hz2' hzz'
  rw [hdz, hdz'] at hlo hhi
  have e : z' - rules.back - (z - rules.back) = z' - z := by ring
  rw [e]
  constructor
  · rw [div_le_iff₀ hσhi]
    linarith
  · rw [le_div_iff₀ hσlo]
    linarith

end Unisono.Solutions.Controller
