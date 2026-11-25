/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Silent

/-!
# The positions that the controller aims at, output sample by output sample

For the controller with the schedule of the knots in a world without loss
(`KnotSetting`), and a speaker on a host other than the sender's:

* `Rules.estimate`: the host's estimate of the sender's clock for output
  sample `k`, taken at the request of the block of `k`.
* `chosen_eq_some_iff`: what the controller chooses for output sample `k`
  (`Solution.chosen`), in terms of that estimate: the position `x` exactly
  when the block whose edges enclose the estimate arrived before the
  request, and `x` is the position that its header gives.
* `estimate_sub_mem`: **two positions against their estimates.** Let the
  controller choose `x` for an output sample with the estimate `s`, and `x'`
  for another with an estimate `s' ≥ s`. If the slopes of the schedule in
  the blocks from the one of `x` to the one of `x'` lie between `σLo` and
  `σHi`, then `σLo * (x' - x) ≤ s' - s ≤ σHi * (x' - x)`. So the distance
  between two positions is the difference of their estimates divided by a
  slope of the schedule in between.
* `abs_chosen_sub_le`: hence, if the estimate advances from one to the
  other by `g` times a number `a`, and `a` divided by every slope in between
  is within `v` of one, the position advances by `g` frames within `g * v`.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H]

/-- The host's estimate of the reading of the sender's clock when output
sample `k` of speaker `r` leaves: what the rules give at the host's view
when it handles the request of the block of `k`. -/
def Rules.estimate (p : FixedDelay.Params H) (rules : Rules H R) (w : World H R)
    (lookahead : ℕ+) (r : Fin R) (k : ℕ) : Option ℝ :=
  rules.reading (w.host r)
    ((ruled p rules : Solution H R Payload).requestView w lookahead r
      ((w.speaker r).blockOf k)) r k

variable {p : FixedDelay.Params H} {rules : Rules H R} {w : World H R}
  {A : H → H → Time → Time} {q : LevelSettings} {share nominal : ℝ}

/-- **What the controller chooses for an output sample.** In the setting
`KnotSetting`, for a speaker on a host other than the sender's: the
controller chooses the position `x` for output sample `k` exactly when the
host's estimate for `k` is some `s` that lies from the edge of a block `b`
to just before the edge of `b + 1`, the message of `b` arrived before the
request of the block of `k`, and `x` is the first frame of `b` plus the
distance of `s` from the edge divided by the slope of `b`, moved back by
`rules.back`. -/
theorem chosen_eq_some_iff (hK : KnotSetting p rules w A q share nominal) (lookahead : ℕ+)
    {r : Fin R} (hr : w.host r ≠ w.sender) (k : ℕ) (x : ℝ) :
    (ruled p rules : Solution H R Payload).chosen w lookahead r k = some x
      ↔ ∃ s b, rules.estimate p w lookahead r k = some s
        ∧ dueEdge p rules w lookahead q share nominal b ≤ s
        ∧ s < dueEdge p rules w lookahead q share nominal (b + 1)
        ∧ A w.sender (w.host r) (w.source.handed b)
          < (w.speaker r).asked ((w.speaker r).blockOf k)
        ∧ x = w.source.first b + (s - dueEdge p rules w lookahead q share nominal b)
              / dueSlope p rules w lookahead q share nominal b - rules.back := by
  obtain ⟨need, hlev⟩ := hK.level
  obtain ⟨n, hE⟩ := hK.requests lookahead r ((w.speaker r).blockOf k)
  rw [Solution.chosen_eq _ w lookahead ((w.speaker r).mem_blockOf k) hE]
  unfold Rules.estimate
  rw [Solution.requestView_eq _ w lookahead hE]
  exact ruled_chosen_iff hK.capture hlev hK.share_nonneg hK.share_lt_one hK.nominal_pos
    hK.noLoss lookahead (hK.handovers lookahead) hr hE k x

/-- **Two positions against their estimates.** In the setting
`KnotSetting`, let the controller choose `x` for output sample `j` with the
estimate `s`, and `x'` for output sample `k` with the estimate `s'`, where
`s ≤ s'`. There are blocks `b ≤ b'` whose edges enclose `s` and `s'` such
that: if the slopes of the blocks from `b` to `b'` lie between `σLo` and
`σHi`, then `σLo * (x' - x) ≤ s' - s` and `s' - s ≤ σHi * (x' - x)`. -/
theorem estimate_sub_mem (hK : KnotSetting p rules w A q share nominal) (lookahead : ℕ+)
    {r : Fin R} (hr : w.host r ≠ w.sender) {j k : ℕ} {x x' s s' : ℝ}
    (hx : (ruled p rules : Solution H R Payload).chosen w lookahead r j = some x)
    (hx' : (ruled p rules : Solution H R Payload).chosen w lookahead r k = some x')
    (hs : rules.estimate p w lookahead r j = some s)
    (hs' : rules.estimate p w lookahead r k = some s') (hss' : s ≤ s') :
    ∃ b b', b ≤ b'
      ∧ dueEdge p rules w lookahead q share nominal b ≤ s
      ∧ s < dueEdge p rules w lookahead q share nominal (b + 1)
      ∧ dueEdge p rules w lookahead q share nominal b' ≤ s'
      ∧ s' < dueEdge p rules w lookahead q share nominal (b' + 1)
      ∧ ∀ σLo σHi : ℝ,
        (∀ c, b ≤ c → c ≤ b' → σLo ≤ dueSlope p rules w lookahead q share nominal c
          ∧ dueSlope p rules w lookahead q share nominal c ≤ σHi) →
        σLo * (x' - x) ≤ s' - s ∧ s' - s ≤ σHi * (x' - x) := by
  have hprog := hK.handovers lookahead
  obtain ⟨s₁, b, hs₁, h1, h2, -, hxeq⟩ := (chosen_eq_some_iff hK lookahead hr j x).mp hx
  obtain ⟨s₂, b', hs₂, h1', h2', -, hxeq'⟩ := (chosen_eq_some_iff hK lookahead hr k x').mp hx'
  rw [hs, Option.some.injEq] at hs₁
  rw [hs', Option.some.injEq] at hs₂
  subst hs₁ hs₂
  have hmono := dueEdge_strictMono (p := p) (rules := rules) (w := w) (lookahead := lookahead)
    (q := q) hK.share_nonneg hK.share_lt_one hK.nominal_pos hprog
  have hbb' : b ≤ b' := by
    by_contra hlt
    rw [not_le] at hlt
    have := hmono.monotone (show b' + 1 ≤ b from hlt)
    linarith
  refine ⟨b, b', hbb', h1, h2, h1', h2', fun σLo σHi hσ => ?_⟩
  have hpos := dueSlope_pos (p := p) (rules := rules) (w := w) (lookahead := lookahead) (q := q)
    hK.share_nonneg hK.share_lt_one hK.nominal_pos hprog b
  have hpos' := dueSlope_pos (p := p) (rules := rules) (w := w) (lookahead := lookahead)
    (q := q) hK.share_nonneg hK.share_lt_one hK.nominal_pos hprog b'
  -- The coordinates of the two positions.
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = x + rules.back := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : ℝ, z' = x' + rules.back := ⟨_, rfl⟩
  have hzv : z = w.source.first b + (s - dueEdge p rules w lookahead q share nominal b)
      / dueSlope p rules w lookahead q share nominal b := by
    rw [hz, hxeq]
    ring
  have hzv' : z' = w.source.first b' + (s' - dueEdge p rules w lookahead q share nominal b')
      / dueSlope p rules w lookahead q share nominal b' := by
    rw [hz', hxeq']
    ring
  have hdz : dueAt p rules w lookahead q share nominal b z = s := by
    unfold dueAt
    rw [hzv]
    field_simp
    ring
  have hdz' : dueAt p rules w lookahead q share nominal b' z' = s' := by
    unfold dueAt
    rw [hzv']
    field_simp
    ring
  have hfrac : 0 ≤ (s - dueEdge p rules w lookahead q share nominal b)
      / dueSlope p rules w lookahead q share nominal b := div_nonneg (by linarith) hpos.le
  have hfrac' : 0 ≤ (s' - dueEdge p rules w lookahead q share nominal b')
      / dueSlope p rules w lookahead q share nominal b' := div_nonneg (by linarith) hpos'.le
  have hzlo' : (w.source.first b' : ℝ) ≤ z' := by linarith
  have hlen : ∀ c, ((w.blockLength c : ℕ) : ℝ)
      = (w.source.first (c + 1) : ℝ) - w.source.first c := by
    intro c
    unfold World.blockLength
    rw [Nat.cast_sub (w.source.first_strictMono (Nat.lt_succ_self c)).le]
  have hzhi : z ≤ w.source.first (b + 1) := by
    have h3 : (s - dueEdge p rules w lookahead q share nominal b)
        / dueSlope p rules w lookahead q share nominal b ≤ w.blockLength b := by
      rw [div_le_iff₀ hpos]
      have := dueEdge_succ (p := p) (rules := rules) (w := w) (lookahead := lookahead)
        (q := q) (share := share) (nominal := nominal) hprog b
      linarith
    rw [hlen b] at h3
    linarith
  have hzhi' : z' ≤ w.source.first (b' + 1) := by
    have h3 : (s' - dueEdge p rules w lookahead q share nominal b')
        / dueSlope p rules w lookahead q share nominal b' ≤ w.blockLength b' := by
      rw [div_le_iff₀ hpos']
      have := dueEdge_succ (p := p) (rules := rules) (w := w) (lookahead := lookahead)
        (q := q) (share := share) (nominal := nominal) hprog b'
      linarith
    rw [hlen b'] at h3
    linarith
  have hzz' : z ≤ z' := by
    rcases Nat.eq_or_lt_of_le hbb' with heq | hlt
    · subst heq
      rw [hzv, hzv']
      have : (s - dueEdge p rules w lookahead q share nominal b)
          / dueSlope p rules w lookahead q share nominal b
          ≤ (s' - dueEdge p rules w lookahead q share nominal b)
            / dueSlope p rules w lookahead q share nominal b :=
        div_le_div_of_nonneg_right (by linarith) hpos.le
      linarith
    · have hf : (w.source.first (b + 1) : ℝ) ≤ w.source.first b' := by
        exact_mod_cast w.source.first_strictMono.monotone (show b + 1 ≤ b' from hlt)
      linarith
  obtain ⟨g1, g2⟩ := dueAt_sub_mem (q := q) (share := share) (nominal := nominal) hprog hzhi
    b' hbb' hσ z' hzlo' hzhi' hzz'
  rw [hdz, hdz'] at g1 g2
  have hd : z' - z = x' - x := by
    rw [hz, hz']
    ring
  rw [hd] at g1 g2
  exact ⟨g1, g2⟩

/-- **The advance of the position from the advance of the estimate.** In
the setting of `estimate_sub_mem`, let the estimate advance by `g * a`, with
`g ≥ 0` and `a > 0`, and let `a` divided by the slope of every block from
the one of `x` to the one of `x'` be within `v` of one, with `0 ≤ v < 1`.
Then the position advances by `g` frames within `g * v`. -/
theorem abs_chosen_sub_le (hK : KnotSetting p rules w A q share nominal) (lookahead : ℕ+)
    {r : Fin R} (hr : w.host r ≠ w.sender) {j k : ℕ} {x x' s s' : ℝ}
    (hx : (ruled p rules : Solution H R Payload).chosen w lookahead r j = some x)
    (hx' : (ruled p rules : Solution H R Payload).chosen w lookahead r k = some x')
    (hs : rules.estimate p w lookahead r j = some s)
    (hs' : rules.estimate p w lookahead r k = some s') {g a v : ℝ} (hg : 0 ≤ g) (ha : 0 < a)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hadv : s' - s = g * a)
    (hslope : ∀ c, a / (1 + v) ≤ dueSlope p rules w lookahead q share nominal c
      ∧ dueSlope p rules w lookahead q share nominal c ≤ a / (1 - v)) :
    |x' - x - g| ≤ g * v := by
  have hss' : s ≤ s' := by nlinarith
  obtain ⟨b, b', -, -, -, -, -, hsand⟩ := estimate_sub_mem hK lookahead hr hx hx' hs hs' hss'
  obtain ⟨h1, h2⟩ := hsand (a / (1 + v)) (a / (1 - v)) fun c _ _ => hslope c
  rw [hadv] at h1 h2
  have h1v : 0 < 1 + v := by linarith
  have h2v : 0 < 1 - v := by linarith
  -- From the two bounds: `x' - x ≤ g * (1 + v)` and `g * (1 - v) ≤ x' - x`.
  have hup : x' - x ≤ g * (1 + v) := by
    have h3 : a / (1 + v) * (x' - x) ≤ g * a := h1
    rw [div_mul_eq_mul_div, div_le_iff₀ h1v] at h3
    nlinarith
  have hlo : g * (1 - v) ≤ x' - x := by
    have h3 : g * a ≤ a / (1 - v) * (x' - x) := h2
    rw [div_mul_eq_mul_div, le_div_iff₀ h2v] at h3
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

end Unisono.Solutions.Controller
