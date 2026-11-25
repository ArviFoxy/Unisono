/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Late
public import Unisono.Spec.Models.GenerativeDelivery
public import Unisono.Spec.Models.GenerativeProgress

/-!
# A silent output sample in a world built from a draw

In a world built from a draw of the generative model
(`GenerativeWorld.Builds`), the sender's host handles the handover of a
block after its backlog at the capture of the block's last frame, and the
network delivers the block after the backlogs of the link and of the
receiving host. This file puts those together and reads the room of
`timed_silent_room` as a statement about the draw.

* `Draw.reaches d f sender h c`: when host `h` observes a block whose last
  frame is captured at the true time `c`: the sender's host handles the
  handover after its backlog at `c` and sends the block, which arrives when
  the draw says (`Draw.arrival`). A block that is finished later reaches the
  host no earlier (`Builds.reaches_mono`), and the block `b` of the stream
  reaches the host at `reaches` of the capture of its last frame
  (`Builds.arrival_handed`).
* `Builds.noLoss`, `Builds.knotSetting`: a world built from a draw is a
  world without loss, and the setting `KnotSetting` holds in it for the
  controller with the timing rules and the level rule `knotLevel`.
* `Builds.silent_reaches`: **an output sample is silent only if the stream
  is late by the room.** For the controller with playback that follows the
  position that is due, an output sample whose request was handled before
  it leaves plays nothing only if the host has no estimate, or the stream
  has not started for it, or: for every true time `τ` at which the sender's
  clock read at most the room less than at the request, a block finished at
  `τ` would not have reached the host by the request.

The last statement does not mention the blocks of the stream: it compares
the room with the time that the stream takes from the capture device to the
host at one true time. Not proved here: any bound on the parts of the room
that depend on the run (the round trip in use, the slope, the ratio, the
drift, and the lateness of a knot).
-/

@[expose] public noncomputable section

namespace Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ}

/-- When host `h` observes a block whose last frame is captured at the true
time `c`, by the draw: the sender's host handles the handover after its
backlog at `c` and sends the block then, and the block arrives when the
draw says. -/
def Draw.reaches (d : Draw H R) (f : Member H R) (sender h : H) (c : Time) : Time :=
  d.arrival f sender h (c + backlog (d.hostPaused sender) c)

variable {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R} {w : World H R}

/-- In a world built from a draw, the backlog of a host at any true time is
the value of `backlog`. -/
theorem Builds.isBacklog_host (hB : m.Builds f d w) (i : H) (s : Time) :
    IsBacklog (d.hostPaused i) s (backlog (d.hostPaused i) s) := by
  obtain ⟨v₁, v₂, v₃, h1, -, -, -⟩ := hB.network i i s 0
  rw [h1.backlog_eq]
  exact h1

/-- **The sender's host handles the handover of a block after its backlog at
the capture of the block's last frame.** -/
theorem Builds.handed_eq (hB : m.Builds f d w) (b : ℕ) :
    w.source.handed b
      = w.source.capture (w.source.first (b + 1) - 1)
        + backlog (d.hostPaused w.sender) (w.source.capture (w.source.first (b + 1) - 1)) := by
  obtain ⟨v, hv, hh⟩ := hB.capture_handed b
  rw [hh, hv.backlog_eq]

/-- **Block `b` of the stream reaches a host at `reaches` of the capture of
its last frame.** -/
theorem Builds.arrival_handed (hB : m.Builds f d w) (h : H) (b : ℕ) :
    d.arrival f w.sender h (w.source.handed b)
      = d.reaches f w.sender h (w.source.capture (w.source.first (b + 1) - 1)) := by
  rw [hB.handed_eq b]
  rfl

/-- **A block that is finished later reaches a host no earlier**, when the
paused times of the link and of the two hosts never decrease. -/
theorem Builds.reaches_mono (hB : m.Builds f d w) {i j : H}
    (hlink : Monotone (d.linkPaused i j)) (hi : Monotone (d.hostPaused i))
    (hj : Monotone (d.hostPaused j)) : Monotone (d.reaches f i j) := by
  intro c c' hcc'
  have h1 := (hB.isBacklog_host i c).add_le_add hi (hB.isBacklog_host i c') hcc'
  exact hB.arrival_mono hlink hi hj h1

/-- Capture blocks hold the block size of the model. -/
theorem Builds.blockLength_eq (hB : m.Builds f d w) (b : ℕ) :
    w.blockLength b = m.blockSize := by
  unfold World.blockLength
  rw [hB.capture_first, hB.capture_first]
  rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]

end Unisono.Spec.GenerativeWorld

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} {p : FixedDelay.Params H}

omit [DecidableEq H] in
/-- **A world built from a draw is a world without loss** for the
controller, when the controller's sender is the model's, the hosts to which
it sends the stream are listed once and include the host of every speaker,
and it sends at least one copy. -/
theorem _root_.Unisono.Spec.GenerativeWorld.Builds.noLoss (hB : m.Builds f d w)
    (hsender : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hspeakers : ∀ r, m.host r ∈ p.speakers) : NoLoss p w (d.arrival f) where
  deliver := hB.deliver
  sender := hsender.trans hB.sender_eq.symm
  nodup := hnodup
  copies := hcopies
  speakers := fun r => by
    rw [hB.host_eq]
    exact hspeakers r

omit [DecidableEq H] in
/-- **The setting of the knots holds in a world built from a draw**, for
the controller with any rules whose capture schedule is that of the knots
and whose level rule is `knotLevel`, with `0 ≤ share < 1` and valid settings
of the knots. -/
theorem _root_.Unisono.Spec.GenerativeWorld.Builds.knotSetting (hB : m.Builds f d w)
    (hsender : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (hspeakers : ∀ r, m.host r ∈ p.speakers) {rules : Rules H R} {q : LevelSettings}
    {share : ℝ} {kn : KnotSettings} (hcap : rules.capture = knotCapture kn)
    (hlev : ∃ need, rules.level = knotLevel q share kn need) (hs0 : 0 ≤ share)
    (hs1 : share < 1) (hkn : kn.Valid) : KnotSetting p rules w (d.arrival f) q share kn where
  noLoss := hB.noLoss hsender hnodup hcopies hspeakers
  capture := hcap
  level := hlev
  share_nonneg := hs0
  share_lt_one := hs1
  nominal_pos := hkn
  handed := hB.handed_unbounded
  asked := hB.asked_unbounded

variable {q : LevelSettings} {share : ℝ} {t : TimingSettings} {level : LevelRule H R}

/-- **An output sample is silent only if the stream is late by the room.**
In a world built from a draw whose paused times never decrease, in the
setting `KnotSetting` for the controller with the timing rules, with
`q.lo ≤ q.hi` and a start of the level between them, take the controller
with playback that follows the position that is due, for `u ≤ J`. Let
speaker `r` be on a host other than the sender's, let step `n` handle the
request of block `β` before output sample `k` of that block leaves, and let
that output sample play nothing. Then the host has no estimate; or it has
an estimate `s` and one of these holds:

* `s` lies before the edge of block zero;
* the position that is due at `s` lies within `J - u` frames of the start;
* there are a block `b'` and an arrival that the estimate uses, at the true
  time `tb''` before the request, such that for every true time `τ` at
  which the sender's clock read at most the room less than at the request,
  a block finished at `τ` reaches the host at or after the request
  (`Draw.reaches`). The room is that of `timed_silent_room`, with the block
  size of the model for the number of frames of `b'`. -/
theorem _root_.Unisono.Spec.GenerativeWorld.Builds.silent_reaches (hB : m.Builds f d w)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ i, Monotone (d.hostPaused i))
    (hK : KnotSetting p (timedRules w.sender t level) w (d.arrival f) q share t.knots)
    (lookahead : ℕ+) {u J : ℝ} (huJ : u ≤ J) (hlohi : q.lo ≤ q.hi)
    (hstart : q.start ∈ Set.Icc q.lo q.hi) {n : ℕ} {r : Fin R} (hr : w.host r ≠ w.sender)
    {β k : ℕ}
    (hE : earliest (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w
          lookahead n).key w)
        ((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead n).due
      = some (.asked r β))
    (hk : k ∈ (w.speaker r).block β)
    (hlt : (w.speaker r).asked β < (w.speaker r).out k)
    (hsilent : ((ruled p (timedRules w.sender t level) : Solution H R Payload).followed u
      J).plays w lookahead r k = none) :
    (timedRules w.sender t level).reading (w.host r)
        (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead
          n).views (w.host r) ++ [w.askedEvent r β]) r k = none
      ∨ ∃ s, (timedRules w.sender t level).reading (w.host r)
          (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead
            n).views (w.host r) ++ [w.askedEvent r β]) r k = some s
        ∧ (s < dueEdge p (timedRules w.sender t level) w lookahead q share t.knots 0
          ∨ (∃ b x, dueEdge p (timedRules w.sender t level) w lookahead q share t.knots b ≤ s
              ∧ s < dueEdge p (timedRules w.sender t level) w lookahead q share t.knots (b + 1)
              ∧ x = w.source.first b
                  + (s - dueEdge p (timedRules w.sender t level) w lookahead q share t.knots b)
                    / dueSlope p (timedRules w.sender t level) w lookahead q share t.knots b
                  - (timedRules w.sender t level).back
              ∧ x < J - u)
          ∨ ∃ (b' b'' : ℕ) (tb'' : Time),
              ((w.clock (w.host r)).read tb'', w.handedReading b'')
                  ∈ windowArrivals t (((ruled p (timedRules w.sender t level) :
                      Solution H R Payload).states w lookahead n).views (w.host r)
                    ++ [w.askedEvent r β])
              ∧ tb'' < (w.speaker r).asked β
              ∧ ∀ τ : Time,
                  (w.clock w.sender).read ((w.speaker r).asked β) - (w.clock w.sender).read τ
                    ≤ q.lo
                      - halfTrip t (((ruled p (timedRules w.sender t level) :
                          Solution H R Payload).states w lookahead n).views (w.host r)
                        ++ [w.askedEvent r β])
                      - arrivalSlope t (((ruled p (timedRules w.sender t level) :
                            Solution H R Payload).states w lookahead n).views (w.host r)
                          ++ [w.askedEvent r β])
                        * ((t.lead + ((k : ℝ) - (w.speaker r).first β) / t.rate)
                          * ratioAt t w r β)
                      - (1 + share) * (t.knots.nominal * (1 + t.knots.bound))
                        * (J - u + (lookahead : ℕ))
                      - m.blockSize * t.knots.nominal * (1 + t.knots.bound)
                      + w.drift (w.host r)
                          (arrivalSlope t (((ruled p (timedRules w.sender t level) :
                              Solution H R Payload).states w lookahead n).views (w.host r)
                            ++ [w.askedEvent r β])) tb'' ((w.speaker r).asked β)
                      + w.knotLate t.knots b' →
                  (w.speaker r).asked β ≤ d.reaches f w.sender (w.host r) τ) := by
  rcases timed_silent_room hK lookahead huJ hlohi hstart hr hE hk hlt hsilent with
    hnone | ⟨s, hs, hcase⟩
  · exact Or.inl hnone
  · refine Or.inr ⟨s, hs, ?_⟩
    rcases hcase with h0 | htrans | ⟨b', b'', tb'', hlate, hmem, hlt'', hroom⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl htrans)
    · refine Or.inr (Or.inr ⟨b', b'', tb'', hmem, hlt'', fun τ hτ => ?_⟩)
      rw [hB.blockLength_eq b'] at hroom
      have hread : (w.clock w.sender).read (w.source.capture (w.source.first (b' + 1) - 1))
          ≤ (w.clock w.sender).read τ := by
        have h1 : w.captureReading (w.source.first (b' + 1) - 1)
            = (w.clock w.sender).read (w.source.capture (w.source.first (b' + 1) - 1)) := rfl
        rw [h1] at hroom
        linarith
      have hle : w.source.capture (w.source.first (b' + 1) - 1) ≤ τ :=
        (w.clock w.sender).strictMono.le_iff_le.mp hread
      rw [hB.arrival_handed (w.host r) b'] at hlate
      exact hlate.trans (hB.reaches_mono (hlink _ _) (hhost _) (hhost _) hle)

end Unisono.Solutions.Controller
