/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeIdle
public import Unisono.Spec.Models.GenerativeDelivery

/-!
# Messages and device events in a period without pauses

A message from host `i` to host `j` waits for the backlog of host `i`, of
the link and of host `j`. `Draw.PathIdle d i j a b` says that none of the
three has a backlog at the true time `a` and that no pause of any of them
begins until `b` (`IdleOn`). In a world built from a draw whose paused
times never decrease:

* `Builds.arrival_eq_of_pathIdle`: a message sent in such a period, early
  enough to arrive in it, takes exactly the least delay of its direction.
* `Builds.arrival_le_of_pathIdle`: a message sent before the period has
  arrived by the least delay after the start of the period. So a message
  that arrives later than that was sent in the period
  (`Builds.le_of_lt_arrival`).
* `Builds.handed_of_idleOn`: while the sender's host is idle it handles the
  handover of a block when the block's last frame is captured.
* `Builds.asked_of_idleOn`: while a speaker's host is idle it handles a
  request when the device raises it, the request lead before the block's
  first output sample leaves, on the device's clock.
* `Builds.arrival_of_captured`, `Builds.block_of_lt_arrival`: a block whose
  last frame is captured in a period in which the path from the sender to a
  host is idle reaches the host the least delay after that capture; and a
  block that reaches the host later than the least delay after the start of
  the period is such a block.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R}

/-- From the true time `a` to `b` nothing delays a message from host `i` to
host `j`: host `i`, the link from `i` to `j` and host `j` have no backlog at
`a`, and no pause of any of them begins until `b`. -/
structure Draw.PathIdle (d : Draw H R) (i j : H) (a b : Time) : Prop where
  /-- The sending host. -/
  source : IdleOn (d.hostPaused i) a b
  /-- The link. -/
  link : IdleOn (d.linkPaused i j) a b
  /-- The receiving host. -/
  target : IdleOn (d.hostPaused j) a b

/-- **A message sent while its path is idle takes the least delay of its
direction**, when it is sent early enough to arrive in the period. -/
theorem Builds.arrival_eq_of_pathIdle (hB : m.Builds f d w) {i j : H}
    (hlink : Monotone (d.linkPaused i j)) (hi : Monotone (d.hostPaused i))
    (hj : Monotone (d.hostPaused j)) {a b : Time} (hidle : d.PathIdle i j a b) {s : Time}
    (has : a ≤ s) (hsb : s + d.split i j * f.roundTrip i j ≤ b)
    (hδ : 0 ≤ d.split i j * f.roundTrip i j) :
    d.arrival f i j s = s + d.split i j * f.roundTrip i j := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, he⟩ := hB.arrival_eq i j s
  have e₁ : v₁ = 0 := hv₁.unique (hidle.source.isBacklog hi has (by linarith))
  subst e₁
  have e₂ : v₂ = 0 := hv₂.unique (hidle.link.isBacklog hlink (by linarith) (by linarith))
  subst e₂
  have e₃ : v₃ = 0 := hv₃.unique (hidle.target.isBacklog hj (by linarith) (by linarith))
  subst e₃
  rw [he]
  ring

/-- **A message sent before an idle period has arrived by the least delay
after the start of the period.** -/
theorem Builds.arrival_le_of_pathIdle (hB : m.Builds f d w) {i j : H}
    (hlink : Monotone (d.linkPaused i j)) (hi : Monotone (d.hostPaused i))
    (hj : Monotone (d.hostPaused j)) {a b : Time} (hidle : d.PathIdle i j a b) {s : Time}
    (hsa : s ≤ a) (hab : a + d.split i j * f.roundTrip i j ≤ b)
    (hδ : 0 ≤ d.split i j * f.roundTrip i j) :
    d.arrival f i j s ≤ a + d.split i j * f.roundTrip i j := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, he⟩ := hB.arrival_eq i j s
  have h₁ := hv₁.add_le_add hi (hidle.source.isBacklog hi le_rfl (by linarith)) hsa
  have h₂ := hv₂.add_le_add hlink (hidle.link.isBacklog hlink le_rfl (by linarith))
    (by linarith : s + v₁ ≤ a)
  have h₃ := hv₃.add_le_add hj
    (hidle.target.isBacklog hj (by linarith : a ≤ a + d.split i j * f.roundTrip i j) hab)
    (by linarith : s + v₁ + d.split i j * f.roundTrip i j + v₂
      ≤ a + d.split i j * f.roundTrip i j)
  rw [he]
  linarith

/-- **A message that arrives later than the least delay after the start of
an idle period was sent in the period.** -/
theorem Builds.le_of_lt_arrival (hB : m.Builds f d w) {i j : H}
    (hlink : Monotone (d.linkPaused i j)) (hi : Monotone (d.hostPaused i))
    (hj : Monotone (d.hostPaused j)) {a b : Time} (hidle : d.PathIdle i j a b) {s : Time}
    (hab : a + d.split i j * f.roundTrip i j ≤ b)
    (hδ : 0 ≤ d.split i j * f.roundTrip i j)
    (hlt : a + d.split i j * f.roundTrip i j < d.arrival f i j s) : a ≤ s := by
  by_contra hsa
  exact absurd (hB.arrival_le_of_pathIdle hlink hi hj hidle (not_le.mp hsa).le hab hδ)
    (not_le.mpr hlt)

/-- **While the sender's host is idle it handles the handover of a block
when the block's last frame is captured.** -/
theorem Builds.handed_of_idleOn (hB : m.Builds f d w)
    (hs : Monotone (d.hostPaused w.sender)) {a b : Time}
    (hidle : IdleOn (d.hostPaused w.sender) a b) {β : ℕ}
    (ha : a ≤ w.source.capture (w.source.first (β + 1) - 1))
    (hb : w.source.capture (w.source.first (β + 1) - 1) ≤ b) :
    w.source.handed β = w.source.capture (w.source.first (β + 1) - 1) := by
  obtain ⟨v, hv, h⟩ := hB.capture_handed β
  rw [h, hv.unique (hidle.isBacklog hs ha hb), add_zero]

/-- **While a speaker's host is idle it handles a request when the device
raises it**: the request lead, on the device's clock, before the block's
first output sample leaves. The request is one that the host handles after
the start of the idle period and by its end. -/
theorem Builds.asked_of_idleOn (hB : m.Builds f d w) {r : Fin R}
    (hh : Monotone (d.hostPaused (w.host r))) {a b : Time}
    (hidle : IdleOn (d.hostPaused (w.host r)) a b) {β : ℕ}
    (ha : a < (w.speaker r).asked β) (hb : (w.speaker r).asked β ≤ b) :
    d.deviceReading (some (m.device r)) ((w.speaker r).out ((w.speaker r).first β))
      - d.deviceReading (some (m.device r)) ((w.speaker r).asked β) = m.lead := by
  obtain ⟨ρ, v, hρ, hv, h⟩ := hB.speaker_asked r β
  have hv0 := hv.nonneg
  have haρ : a ≤ ρ := by
    by_contra hlt
    have h1 := hv.add_le_add hh (hidle.isBacklog hh le_rfl (by linarith)) (not_le.mp hlt).le
    linarith
  have e : v = 0 := hv.unique (hidle.isBacklog hh haρ (by linarith))
  rw [h, e, add_zero]
  exact hρ

/-- **A block whose last frame is captured in an idle period reaches the
host after the least delay.** Let the path from the sender to host `j` be
idle from `a` to `b`, and let the last frame of block `β` be captured in
that period, early enough for the block to arrive in it. Then the sender's
host handles the handover at that capture, and the block reaches `j` the
least delay later. -/
theorem Builds.arrival_of_captured (hB : m.Builds f d w) {j : H}
    (hlink : Monotone (d.linkPaused w.sender j)) (hs : Monotone (d.hostPaused w.sender))
    (hj : Monotone (d.hostPaused j)) {a b : Time} (hidle : d.PathIdle w.sender j a b)
    (hδ : 0 ≤ d.split w.sender j * f.roundTrip w.sender j) {β : ℕ}
    (ha : a ≤ w.source.capture (w.source.first (β + 1) - 1))
    (hb : w.source.capture (w.source.first (β + 1) - 1)
      + d.split w.sender j * f.roundTrip w.sender j ≤ b) :
    w.source.handed β = w.source.capture (w.source.first (β + 1) - 1)
      ∧ d.arrival f w.sender j (w.source.handed β)
        = w.source.capture (w.source.first (β + 1) - 1)
          + d.split w.sender j * f.roundTrip w.sender j := by
  have h1 := hB.handed_of_idleOn hs hidle.source ha (by linarith)
  refine ⟨h1, ?_⟩
  rw [h1]
  exact hB.arrival_eq_of_pathIdle hlink hs hj hidle ha hb hδ

/-- **A block that reaches a host later than the least delay after the
start of an idle period was finished in the period.** Let the path from the
sender to host `j` be idle from `a` to `b`, and let block `β` reach `j`
later than the least delay after `a`, and by `b`. Then the block's last
frame was captured after `a`, the sender's host handled the handover at
that capture, and the block reached `j` the least delay later. -/
theorem Builds.block_of_lt_arrival (hB : m.Builds f d w) {j : H}
    (hlink : Monotone (d.linkPaused w.sender j)) (hs : Monotone (d.hostPaused w.sender))
    (hj : Monotone (d.hostPaused j)) {a b : Time} (hidle : d.PathIdle w.sender j a b)
    (hδ : 0 ≤ d.split w.sender j * f.roundTrip w.sender j) {β : ℕ}
    (hlt : a + d.split w.sender j * f.roundTrip w.sender j
      < d.arrival f w.sender j (w.source.handed β))
    (hle : d.arrival f w.sender j (w.source.handed β) ≤ b) :
    a < w.source.capture (w.source.first (β + 1) - 1)
      ∧ w.source.handed β = w.source.capture (w.source.first (β + 1) - 1)
      ∧ d.arrival f w.sender j (w.source.handed β)
        = w.source.capture (w.source.first (β + 1) - 1)
          + d.split w.sender j * f.roundTrip w.sender j := by
  have hab : a + d.split w.sender j * f.roundTrip w.sender j ≤ b := hlt.le.trans hle
  have h1 : a ≤ w.source.handed β := hB.le_of_lt_arrival hlink hs hj hidle hab hδ hlt
  have h2 := hB.le_arrival w.sender j (w.source.handed β)
  have h3 := hB.arrival_eq_of_pathIdle hlink hs hj hidle h1 (h2.trans hle) hδ
  have h4 : a < w.source.handed β := by
    rw [h3] at hlt
    linarith
  obtain ⟨v, hv, hh⟩ := hB.capture_handed β
  have hv0 := hv.nonneg
  have hac : a ≤ w.source.capture (w.source.first (β + 1) - 1) := by
    by_contra hlt'
    have h5 := hv.add_le_add hs (hidle.source.isBacklog hs le_rfl (by linarith))
      (not_le.mp hlt').le
    linarith
  have e : v = 0 := hv.unique (hidle.source.isBacklog hs hac (by linarith))
  have h6 : w.source.handed β = w.source.capture (w.source.first (β + 1) - 1) := by
    rw [hh, e, add_zero]
  refine ⟨by rw [← h6]; exact h4, h6, ?_⟩
  rw [h3, h6]

end Unisono.Spec.GenerativeWorld
