/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ProposedBuild
public import Unisono.Spec.FrameArrival

/-!
# Stretches during which nothing arrives, in the proposed model

In a world built from a regular draw of `Unisono.Spec.ProposedWorld`, each
of the three disturbances of a link gives a stretch during which no message
sent on the link is handled. `Unisono.Spec.Solution.stall_le_of_quiet` then
says what such a stretch costs every solution that carries frames only on
links from the sender or to the sender.

* `Draw.Regular.le_released`, `Draw.Regular.least_le_observed`: a
  message is released onto the link when it is sent or later, and the
  program of the receiving host handles it at least the least delay of the
  direction after its release.
* `Builds.quiet_of_outage`: while the link is in an outage from `t₀` to `e`,
  no message sent at `t₀` or later is handled before `e` plus the least
  delay.
* `Builds.quiet_of_linkPause`: the same while a pause of the link holds
  every message that leaves its sender between `t₀` and `e` until `e`.
* `Builds.quiet_of_jitter`: while the jitter of the link is at least `x`
  from `t₀` to `t₁`, no message sent at `t₀` or later is handled before the
  earlier of `t₀ + x` and `t₁`, plus the least delay. A large jitter costs
  only until the jitter is redrawn, because a message released after the
  redraw can arrive before one released earlier.

All four hold in one outcome. They are not yet combined into a bound on
expected cost.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open GenerativeWorld (backlog)

variable {H : Type} {R : ℕ} {m : Told H R} {f : Member H R} {d : Draw H R} {w : World H R}

namespace Draw.Regular

variable (hd : d.Regular f)
include hd

/-- A message is released onto the link when it is sent, or later. -/
theorem le_released (i j : H) (s : Time) : s ≤ d.released i j s := by
  have h1 := hd.hostBacklog_nonneg i s
  have h2 := hd.linkBacklog_nonneg i j (d.leaves i s)
  unfold Draw.released Draw.leaves at *
  linarith

/-- The program of the receiving host handles a message at least the least
delay of the direction after the message is released onto the link. -/
theorem least_le_observed (i j : H) (s : Time) :
    d.released i j s + d.split i j * f.roundTrip i j ≤ d.observed f i j s := by
  have h1 := hd.reaches_le_observed i j s
  have h2 : 0 ≤ d.jitter i j (d.released i j s) := hd.jitter_nonneg i j _
  unfold Draw.reaches at h1
  linarith

end Draw.Regular

section Quiet

/-- A message that the network of a built world delivers is not lost, and
the program handles it at `Draw.observed`. -/
theorem Builds.observed_of_deliver (hB : Builds m f d w) {i j : H} {s : Time} {q : ℕ}
    {a : Time} (h : w.network.deliver i j s q = some a) :
    ¬ d.lost i j s q ∧ d.observed f i j s = a := by
  classical
  rw [hB.deliver] at h
  unfold Draw.delivery at h
  split_ifs at h with hl
  exact ⟨hl, Option.some.inj h⟩

/-- **An outage is a stretch during which nothing arrives.** In a world
built from a regular draw, let the link from `i` to `j` be in an outage at
every true time from `t₀` to before `e`. Then no message that `i` sends to
`j` at `t₀` or later is handled before `e` plus the least delay of the
direction. -/
theorem Builds.quiet_of_outage (hB : Builds m f d w) (hd : d.Regular f) {i j : H}
    {t₀ e : Time} (hout : ∀ u, t₀ ≤ u → u < e → 0 < backlog (d.outage i j) u) (s : Time)
    (q : ℕ) (a : Time) (hs : t₀ ≤ s) (h : w.network.deliver i j s q = some a) :
    e + d.split i j * f.roundTrip i j ≤ a := by
  obtain ⟨hlost, ha⟩ := hB.observed_of_deliver h
  have hrel := hd.le_released i j s
  have he : e ≤ d.released i j s := by
    by_contra hlt
    exact hlost (Or.inl (hout _ (hs.trans hrel) (not_le.mp hlt)))
  have h2 := hd.least_le_observed i j s
  linarith

/-- **A pause of the link is a stretch during which nothing arrives.** In a
world built from a regular draw, let the pauses of the link from `i` to `j`
hold every message that leaves `i` between `t₀` and `e` until `e` or later.
Then no message that `i` sends to `j` at `t₀` or later is handled before `e`
plus the least delay of the direction. -/
theorem Builds.quiet_of_linkPause (hB : Builds m f d w) (hd : d.Regular f) {i j : H}
    {t₀ e : Time}
    (hpause : ∀ u, t₀ ≤ u → u < e → e ≤ u + backlog (d.linkPaused i j) u) (s : Time)
    (q : ℕ) (a : Time) (hs : t₀ ≤ s) (h : w.network.deliver i j s q = some a) :
    e + d.split i j * f.roundTrip i j ≤ a := by
  obtain ⟨-, ha⟩ := hB.observed_of_deliver h
  have hleave : s ≤ d.leaves i s := by
    have := hd.hostBacklog_nonneg i s
    unfold Draw.leaves
    linarith
  have he : e ≤ d.released i j s := by
    by_cases hlt : d.leaves i s < e
    · exact hpause _ (hs.trans hleave) hlt
    · have := hd.linkBacklog_nonneg i j (d.leaves i s)
      unfold Draw.released
      linarith [not_lt.mp hlt]
  have h2 := hd.least_le_observed i j s
  linarith

/-- **A large jitter is a stretch during which nothing arrives, until the
jitter is redrawn.** In a world built from a regular draw, let the jitter of
the link from `i` to `j` be at least `x` at every true time from `t₀` to
before `t₁`. Then no message that `i` sends to `j` at `t₀` or later is
handled before the earlier of `t₀ + x` and `t₁`, plus the least delay of the
direction. -/
theorem Builds.quiet_of_jitter (hB : Builds m f d w) (hd : d.Regular f) {i j : H}
    {t₀ t₁ x : ℝ} (hjit : ∀ u, t₀ ≤ u → u < t₁ → x ≤ d.jitter i j u) (s : Time) (q : ℕ)
    (a : Time) (hs : t₀ ≤ s) (h : w.network.deliver i j s q = some a) :
    min (t₀ + x) t₁ + d.split i j * f.roundTrip i j ≤ a := by
  obtain ⟨-, ha⟩ := hB.observed_of_deliver h
  have hrel := hd.le_released i j s
  have hobs := hd.reaches_le_observed i j s
  have hnn : 0 ≤ d.jitter i j (d.released i j s) := hd.jitter_nonneg i j _
  by_cases hlt : d.released i j s < t₁
  · have hx := hjit _ (hs.trans hrel) hlt
    have hmin := min_le_left (t₀ + x) t₁
    unfold Draw.reaches at hobs
    linarith
  · have hmin := min_le_right (t₀ + x) t₁
    unfold Draw.reaches at hobs
    linarith [not_lt.mp hlt]

end Quiet

end Unisono.Spec.ProposedWorld
