/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.BuiltLate

/-!
# The room of a silent output sample, from bounds on its parts

`Builds.silent_reaches` states the room of a silent output sample with the
parts that depend on the run: half of the round trip in use, the host's
slope and ratio, the drift since the arrival that the estimate rests on, and
the lateness of a knot. This file replaces them by bounds.

* `roomMin`: the room with half of `tripCap` for half of the round trip,
  the largest slope and ratio, a bound `D` for the drift and a bound `K` for
  how far a knot lies before the capture of its block's last frame.
* `Builds.silent_late`: in a world built from a draw, let the drift over
  every stretch that ends at a request and is at most `window` long on the
  host's clock be at least `-D`, and let every knot be at most `K` earlier
  than the capture of its block's last frame. Then an output sample whose
  request was handled before it leaves plays nothing only if the host has
  no estimate, or the stream has not started for it, or one of these holds:
  **late by the room**: for every true time `τ` at which the sender's clock
  read at most `roomMin` less than at the request, a block finished at `τ`
  reaches the host at or after the request; **late by the window**: no
  block arrived within `window` before the request, and then every block
  whose last frame was captured within `window` before the request, on the
  host's clock, reaches the host at or after the request.

Not proved here: the two bounds `D` and `K` from what is drawn, and when a
host has no estimate.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d : Draw H R} {w : World H R} {p : FixedDelay.Params H}

/-- **The least room**, for a bound `D` of the drift and a bound `K` of how
far a knot lies before the capture of its block's last frame: the least
level `q.lo`, minus half of `tripCap`, minus the square of `1 + slopeBound`
times the request lead plus the nominal time of a playback block, minus the
largest slope of the schedule times `J - u` plus the lookahead, minus the
largest time of a block's frames on the schedule, minus `D` and `K`. -/
def roomMin (q : LevelSettings) (share : ℝ) (t : TimingSettings) (blockSize : ℕ) (J u : ℝ)
    (lookahead : ℕ+) (D K : ℝ) : ℝ :=
  q.lo - t.tripCap / 2 - (1 + t.slopeBound) ^ 2 * (t.lead + blockSize / t.rate)
    - (1 + share) * (t.knots.nominal * (1 + t.knots.bound)) * (J - u + (lookahead : ℕ))
    - blockSize * t.knots.nominal * (1 + t.knots.bound) - D - K

variable {q : LevelSettings} {share : ℝ} {t : TimingSettings} {level : LevelRule H R}

/-- **A silent output sample is late by the room or by the window.** In a
world built from a draw whose paused times never decrease, in the setting
`KnotSetting` for the controller with the timing rules, with `q.lo ≤ q.hi`,
a start of the level between them, `0 ≤ slopeBound ≤ 1`, `0 ≤ lead`,
`0 < rate` and `0 ≤ tripCap`. Let speaker `r` be on a host other than the
sender's, let step `n` handle the request of block `β` before output sample
`k` of that block leaves, and let that output sample of the controller with
playback that follows the due position, `u ≤ J`, play nothing. Assume:

* for every true time `a` before the request from which the host's clock
  advanced by at most `window` until the request, and every slope `sl`
  within `slopeBound` of one, the drift from `a` to the request is at least
  `-D`;
* for every block, its knot is at most `K` earlier than the capture of its
  last frame.

Then the host has no estimate; or it has an estimate `s` and one of these
holds: `s` lies before the edge of block zero; the position that is due at
`s` lies within `J - u` frames of the start; for every true time `τ` at
which the sender's clock read at most `roomMin` less than at the request, a
block finished at `τ` reaches the host at or after the request; or every
block whose last frame was captured at most `window` before the request, on
the host's clock, reaches the host at or after the request. -/
theorem _root_.Unisono.Spec.GenerativeWorld.Builds.silent_late (hB : m.Builds f d w)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ i, Monotone (d.hostPaused i))
    (hK : KnotSetting p (timedRules w.sender t level) w (d.arrival f) q share t.knots)
    (lookahead : ℕ+) {u J : ℝ} (huJ : u ≤ J) (hlohi : q.lo ≤ q.hi)
    (hstart : q.start ∈ Set.Icc q.lo q.hi) (hsb0 : 0 ≤ t.slopeBound) (hsb1 : t.slopeBound ≤ 1)
    (hlead : 0 ≤ t.lead) (hrate : 0 < t.rate) (hcap : 0 ≤ t.tripCap) {n : ℕ} {r : Fin R}
    (hr : w.host r ≠ w.sender) {β k : ℕ}
    (hE : earliest (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w
          lookahead n).key w)
        ((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead n).due
      = some (.asked r β))
    (hk : k ∈ (w.speaker r).block β)
    (hlt : (w.speaker r).asked β < (w.speaker r).out k)
    (hsilent : ((ruled p (timedRules w.sender t level) : Solution H R Payload).followed u
      J).plays w lookahead r k = none)
    {D K : ℝ}
    (hdrift : ∀ a : Time, a < (w.speaker r).asked β →
      (w.clock (w.host r)).read ((w.speaker r).asked β) - (w.clock (w.host r)).read a
        ≤ t.window →
      ∀ sl ∈ Set.Icc (1 - t.slopeBound) (1 + t.slopeBound),
        -D ≤ w.drift (w.host r) sl a ((w.speaker r).asked β))
    (hknot : ∀ b', -K ≤ w.knotLate t.knots b') :
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
          ∨ (∀ τ : Time,
              (w.clock w.sender).read ((w.speaker r).asked β) - (w.clock w.sender).read τ
                  ≤ roomMin q share t m.blockSize J u lookahead D K →
                (w.speaker r).asked β ≤ d.reaches f w.sender (w.host r) τ)
          ∨ ∀ b : ℕ,
              (w.clock (w.host r)).read ((w.speaker r).asked β)
                  - (w.clock (w.host r)).read (w.source.capture (w.source.first (b + 1) - 1))
                ≤ t.window →
              (w.speaker r).asked β
                ≤ d.reaches f w.sender (w.host r)
                  (w.source.capture (w.source.first (b + 1) - 1))) := by
  rcases hB.silent_reaches hlink hhost hK lookahead huJ hlohi hstart hr hE hk hlt hsilent with
    hnone | ⟨s, hs, hcase⟩
  · exact Or.inl hnone
  · refine Or.inr ⟨s, hs, ?_⟩
    rcases hcase with h0 | htrans | ⟨b', b'', tb'', hmem, hlt'', hall⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl htrans)
    · obtain ⟨-, hwin | ⟨hold, -⟩⟩ := mem_windowArrivals t hmem
      · -- The arrival that the estimate rests on is within the window.
        refine Or.inr (Or.inr (Or.inl fun τ hτ => hall τ (le_trans hτ ?_)))
        have hsl := arrivalSlope_mem t hsb0
          (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead
            n).views (w.host r) ++ [w.askedEvent r β])
        have hratio := ratioAt_mem t hsb0 w r β
        have hhalf := (halfTrip_mem t hcap
          (((ruled p (timedRules w.sender t level) : Solution H R Payload).states w lookahead
            n).views (w.host r) ++ [w.askedEvent r β])).2
        have hwin' : (w.clock (w.host r)).read ((w.speaker r).asked β) - t.window
            ≤ (w.clock (w.host r)).read tb'' := hwin
        have hd := hdrift tb'' hlt'' (by linarith) _ hsl
        have hkn := hknot b'
        -- The device's time from the request to the output sample.
        have hfirst : (w.speaker r).first β = β * m.blockSize := hB.speaker_first r β
        have hfirst' : (w.speaker r).first (β + 1) = (β + 1) * m.blockSize :=
          hB.speaker_first r (β + 1)
        have hkmem : (w.speaker r).first β ≤ k ∧ k < (w.speaker r).first β + m.blockSize := by
          unfold PlaybackDevice.block at hk
          obtain ⟨i, hi, hki⟩ : ∃ i < (w.speaker r).first (β + 1) - (w.speaker r).first β,
              k = (w.speaker r).first β + i := by
            simpa [List.mem_range'] using hk
          have hlen : (w.speaker r).first (β + 1) - (w.speaker r).first β = m.blockSize := by
            rw [hfirst', hfirst, Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
          rw [hlen] at hi
          exact ⟨by omega, by omega⟩
        have hk1 : ((w.speaker r).first β : ℝ) ≤ k := by exact_mod_cast hkmem.1
        have hk2 : (k : ℝ) - (w.speaker r).first β ≤ m.blockSize := by
          have h4 : (k : ℝ) < ((w.speaker r).first β : ℝ) + m.blockSize := by
            exact_mod_cast hkmem.2
          linarith
        have hX0 : 0 ≤ t.lead + ((k : ℝ) - (w.speaker r).first β) / t.rate :=
          add_nonneg hlead (div_nonneg (by linarith) hrate.le)
        have hX1 : t.lead + ((k : ℝ) - (w.speaker r).first β) / t.rate
            ≤ t.lead + m.blockSize / t.rate := by
          have := div_le_div_of_nonneg_right hk2 hrate.le
          linarith
        have hsl0 : 0 ≤ arrivalSlope t (((ruled p (timedRules w.sender t level) :
            Solution H R Payload).states w lookahead n).views (w.host r)
          ++ [w.askedEvent r β]) := by linarith [hsl.1]
        have hr0 : 0 ≤ ratioAt t w r β := by linarith [hratio.1]
        have hprod : arrivalSlope t (((ruled p (timedRules w.sender t level) :
              Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r β])
            * ((t.lead + ((k : ℝ) - (w.speaker r).first β) / t.rate) * ratioAt t w r β)
            ≤ (1 + t.slopeBound) ^ 2 * (t.lead + m.blockSize / t.rate) := by
          have hY0 : 0 ≤ t.lead + (m.blockSize : ℝ) / t.rate := le_trans hX0 hX1
          have h5 : (t.lead + ((k : ℝ) - (w.speaker r).first β) / t.rate) * ratioAt t w r β
              ≤ (t.lead + m.blockSize / t.rate) * (1 + t.slopeBound) :=
            mul_le_mul hX1 hratio.2 hr0 hY0
          have h6 := mul_le_mul hsl.2 h5 (mul_nonneg hX0 hr0) (by linarith)
          calc _ ≤ (1 + t.slopeBound) * ((t.lead + m.blockSize / t.rate) * (1 + t.slopeBound)) :=
                h6
            _ = (1 + t.slopeBound) ^ 2 * (t.lead + m.blockSize / t.rate) := by ring
        unfold roomMin
        linarith
      · -- No arrival within the window before the request.
        refine Or.inr (Or.inr (Or.inr fun b hb => ?_))
        by_contra hcon
        rw [not_le] at hcon
        rw [← hB.arrival_handed (w.host r) b] at hcon
        have hev : (ruled p (timedRules w.sender t level) : Solution H R Payload).eventTime w
            lookahead n = (w.speaker r).asked β :=
          Solution.handled_time w _ lookahead (Solution.handled_of_asked w _ lookahead hE)
        have hin := arrival_mem_arrivalsOf hK.capture hK.noLoss lookahead hr (b := b) (n := n)
          (by rw [hev]; exact hcon)
        have hin' : ((w.clock (w.host r)).read (d.arrival f w.sender (w.host r)
              (w.source.handed b)), w.handedReading b)
            ∈ arrivalsOf (((ruled p (timedRules w.sender t level) :
                Solution H R Payload).states w lookahead n).views (w.host r)
              ++ [w.askedEvent r β]) := by
          have happ : arrivalsOf (((ruled p (timedRules w.sender t level) :
                Solution H R Payload).states w lookahead n).views (w.host r)
              ++ [w.askedEvent r β])
              = arrivalsOf (((ruled p (timedRules w.sender t level) :
                Solution H R Payload).states w lookahead n).views (w.host r)) :=
            arrivalsOf_append_asked _ _ _ _ _
          rw [happ]
          exact hin
        have h1 := hold _ hin'
        have h2 : w.source.capture (w.source.first (b + 1) - 1)
            ≤ d.arrival f w.sender (w.host r) (w.source.handed b) := by
          have h3 := w.source.handed_after b
          have hafter := w.network.after _ _ _ 0 _ (hB.deliver w.sender (w.host r)
            (w.source.handed b) 0)
          linarith
        have h6 := (w.clock (w.host r)).strictMono.monotone h2
        have h7 : (w.askedEvent r β : Event H R Payload).reading
            = (w.clock (w.host r)).read ((w.speaker r).asked β) := rfl
        rw [h7] at h1
        simp only at h1
        linarith

end Unisono.Solutions.Controller
