/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.Checked
public import Unisono.Solutions.Controller.ChosenLatency

/-!
# An output sample is silent only when a block is late by a stated room

`followed_silent` lists why an output sample of the controller with
playback that follows the due position plays nothing. This file turns the
case of a block that has not arrived into a statement about readings of the
sender's clock, in the setting `KnotSetting`.

* `followed_silent_knot`: for any rules of the setting whose level stays
  between `q.lo` and `q.hi`. If an output sample plays nothing, then the
  host has no estimate; or its estimate `s` lies before the edge of block
  zero; or the position that is due lies within `J - u` frames of the start
  of the stream; or some block `b'` has not arrived at the request, and the
  knot of `b'` is at most `s`, plus the largest slope of the schedule times
  `J - u` plus the lookahead, minus `q.lo`, plus the largest time of the
  frames of `b'` on the schedule.
* `timed_silent_room`: for the timing rules, with the lower bound of the
  estimate (`timed_reading_lower`). In the last case, the reading of the
  sender's clock at the capture of the last frame of `b'` is earlier than
  its reading at the request by at least **the room**: the least level
  `q.lo`, minus half of the round trip in use, minus the host's slope times
  its ratio times the device's time from the request to the output sample,
  minus the allowance for `J - u` plus the lookahead frames, minus the
  largest time of the frames of `b'` on the schedule, plus the drift since
  the arrival that the estimate rests on, plus the time by which the knot
  of `b'` is later than the capture of its last frame.

So an output sample whose request was handled in time is silent, apart from
the start of the stream and from a missing estimate, only if a block whose
last frame was captured at least the room before the request, on the
sender's clock, had not arrived by the request.

Not proved here: when a host has no estimate, and any bound on the drift or
on the lateness of a knot.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H]

variable {p : FixedDelay.Params H} {rules : Rules H R} {w : World H R}
  {A : H → H → Time → Time} {q : LevelSettings} {share : ℝ} {kn : KnotSettings}

/-- **When an output sample plays nothing, by the knots.** In the setting
`KnotSetting`, with `q.lo ≤ q.hi`, a start of the level between them, and
`0 ≤ rules.back`, take the controller with playback that follows the
position that is due, for `u ≤ J`. Let speaker `r` be on a host other than
the sender's, let step `n` handle the request of block `β` before output
sample `k` of that block leaves, and let that output sample play nothing.
Then the host has no estimate; or it has an estimate `s` and one of these
holds:

* `s` lies before the edge of block zero;
* `s` lies between the edges of a block `b` and the next, and the position
  that the header of `b` gives for `s`, moved back by `rules.back`, is less
  than `J - u`;
* some block `b'` arrived at or after the request, and the knot of `b'` is
  at most `s`, plus the largest slope of the schedule times `J - u` plus
  the lookahead, minus `q.lo`, plus the number of frames of `b'` times the
  largest time from one frame to the next. -/
theorem followed_silent_knot (hK : KnotSetting p rules w A q share kn) (lookahead : ℕ+)
    {u J : ℝ} (huJ : u ≤ J) (hlohi : q.lo ≤ q.hi) (hstart : q.start ∈ Set.Icc q.lo q.hi)
    (hback : 0 ≤ rules.back) {n : ℕ} {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ}
    (hE : earliest (((ruled p rules : Solution H R Payload).states w lookahead n).key w)
        ((ruled p rules : Solution H R Payload).states w lookahead n).due = some (.asked r β))
    (hk : k ∈ (w.speaker r).block β)
    (hlt : (w.speaker r).asked β < (w.speaker r).out k)
    (hsilent : ((ruled p rules : Solution H R Payload).followed u J).plays w lookahead r k
      = none) :
    rules.reading (w.host r)
        (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
          ++ [w.askedEvent r β]) r k = none
      ∨ ∃ s, rules.reading (w.host r)
          (((ruled p rules : Solution H R Payload).states w lookahead n).views (w.host r)
            ++ [w.askedEvent r β]) r k = some s
        ∧ (s < dueEdge p rules w lookahead q share kn 0
          ∨ (∃ b x, dueEdge p rules w lookahead q share kn b ≤ s
              ∧ s < dueEdge p rules w lookahead q share kn (b + 1)
              ∧ x = w.source.first b + (s - dueEdge p rules w lookahead q share kn b)
                  / dueSlope p rules w lookahead q share kn b - rules.back
              ∧ x < J - u)
          ∨ ∃ b', (w.speaker r).asked β ≤ A w.sender (w.host r) (w.source.handed b')
              ∧ w.knot kn b'
                ≤ s + (1 + share) * (kn.nominal * (1 + kn.bound)) * (J - u + (lookahead : ℕ))
                  - q.lo + w.blockLength b' * kn.nominal * (1 + kn.bound)) := by
  have hprog := hK.handovers lookahead
  have hs0 := hK.share_nonneg
  have hs1 := hK.share_lt_one
  have hkn := hK.nominal_pos
  obtain ⟨hn, hb0, hb1⟩ := hkn
  have hσhi : 0 ≤ (1 + share) * (kn.nominal * (1 + kn.bound)) :=
    mul_nonneg (by linarith) (mul_nonneg hn.le (by linarith))
  have hJL : 0 ≤ J - u + ((lookahead : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hΔ : 0 ≤ (1 + share) * (kn.nominal * (1 + kn.bound)) * (J - u + ((lookahead : ℕ) : ℝ)) :=
    mul_nonneg hσhi hJL
  -- A knot from the edge of its block.
  have hA : ∀ (b' : ℕ) (Δ : ℝ), dueEdge p rules w lookahead q share kn b' ≤ Δ →
      w.knot kn b' ≤ Δ - q.lo + w.blockLength b' * kn.nominal * (1 + kn.bound) := by
    intro b' Δ hd
    obtain ⟨i, hi⟩ := hprog b'
    have h1 := w.knotStart_add kn b'
    have h2 := (w.knotPeriod_mem hK.nominal_pos b').2
    have h3 := (announcedAt_fst_mem _ w lookahead q share kn hlohi hstart hi).1
    have hlen : (0 : ℝ) ≤ w.blockLength b' := Nat.cast_nonneg _
    have h4 : (w.blockLength b' : ℝ) * w.knotPeriod kn b'
        ≤ w.blockLength b' * kn.nominal * (1 + kn.bound) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hlen
    unfold dueEdge at hd
    linarith
  rcases followed_silent hK lookahead huJ hr hE hk hlt hsilent with hnone | ⟨s, hs, hcase⟩
  · exact Or.inl hnone
  · refine Or.inr ⟨s, hs, ?_⟩
    rcases hcase with h0 | ⟨b, hb, hlate⟩ | ⟨b, x, hb1', hb2, hx, hx2 | ⟨b', hb', hlate⟩⟩
    · exact Or.inl h0
    · refine Or.inr (Or.inr ⟨b, hlate, ?_⟩)
      have := hA b s hb
      linarith
    · exact Or.inr (Or.inl ⟨b, x, hb1', hb2, hx, hx2⟩)
    · refine Or.inr (Or.inr ⟨b', hlate, ?_⟩)
      have hd : dueEdge p rules w lookahead q share kn b'
          ≤ s + (1 + share) * (kn.nominal * (1 + kn.bound)) * (J - u + ((lookahead : ℕ) : ℝ)) := by
        rcases le_or_gt b' b with hle | hgt
        · have := (dueEdge_strictMono (q := q) hs0 hs1 hK.nominal_pos hprog).monotone hle
          linarith
        · have hslope := dueSlope_pos (q := q) hs0 hs1 hK.nominal_pos hprog b
          have hcast : ((w.blockLength b : ℕ) : ℝ)
              = (w.source.first (b + 1) : ℝ) - w.source.first b := by
            unfold World.blockLength
            rw [Nat.cast_sub (w.source.first_strictMono (Nat.lt_succ_self b)).le]
          have hz : dueAt p rules w lookahead q share kn b (x + rules.back) = s := by
            unfold dueAt
            rw [hx]
            field_simp
            ring
          have hz2 : x + rules.back ≤ w.source.first (b + 1) := by
            have hedge := dueEdge_succ (q := q) (share := share) (kn := kn) hprog b
            rw [hedge] at hb2
            have h5 : (s - dueEdge p rules w lookahead q share kn b)
                / dueSlope p rules w lookahead q share kn b < w.blockLength b := by
              rw [div_lt_iff₀ hslope]
              linarith
            rw [hx]
            linarith
          have hfirst : (w.source.first (b + 1) : ℝ) ≤ w.source.first b' := by
            exact_mod_cast w.source.first_strictMono.monotone hgt
          have hmem := dueAt_sub_mem (q := q) hprog hz2 b' hgt.le
            (fun c _ _ => dueSlope_mem (q := q) hs0 hs1 hK.nominal_pos hprog c)
            (w.source.first b') le_rfl
            (by exact_mod_cast (w.source.first_strictMono (Nat.lt_succ_self b')).le)
            (hz2.trans hfirst)
          have he : dueAt p rules w lookahead q share kn b' (w.source.first b')
              = dueEdge p rules w lookahead q share kn b' := by
            unfold dueAt
            ring
          rw [he, hz] at hmem
          have h6 : (w.source.first b' : ℝ) - (x + rules.back)
              ≤ J - u + ((lookahead : ℕ) : ℝ) := by linarith
          have h7 := mul_le_mul_of_nonneg_left h6 hσhi
          linarith [hmem.2]
      have := hA b' _ hd
      linarith

/-- **A silent output sample and the room.** In the setting `KnotSetting`
for the controller with the timing rules and the schedule of its settings,
with `q.lo ≤ q.hi` and a start of the level between them, take the
controller with playback that follows the position that is due, for
`u ≤ J`. Let speaker `r` be on a host other than the sender's, let step `n`
handle the request of block `β` before output sample `k` of that block
leaves, and let that output sample play nothing. Then the host has no
estimate; or it has an estimate `s` and one of these holds:

* `s` lies before the edge of block zero;
* the position that is due at `s` lies within `J - u` frames of the start;
* some block `b'` arrived at or after the request, and the reading of the
  sender's clock at the capture of the last frame of `b'` is earlier than
  its reading at the request by at least the room: `q.lo`, minus half of
  the round trip in use, minus the slope times the ratio times the device's
  time from the request to the output sample, minus the largest slope of
  the schedule times `J - u` plus the lookahead, minus the largest time of
  the frames of `b'` on the schedule, plus the drift from the arrival
  `tb''` that the estimate rests on to the request, plus the time by which
  the knot of `b'` is later than the capture of its last frame. -/
theorem timed_silent_room {t : TimingSettings} {level : LevelRule H R}
    (hK : KnotSetting p (timedRules w.sender t level) w A q share t.knots) (lookahead : ℕ+)
    {u J : ℝ} (huJ : u ≤ J) (hlohi : q.lo ≤ q.hi) (hstart : q.start ∈ Set.Icc q.lo q.hi)
    {n : ℕ} {r : Fin R} (hr : w.host r ≠ w.sender) {β k : ℕ}
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
              (w.speaker r).asked β ≤ A w.sender (w.host r) (w.source.handed b')
              ∧ ((w.clock (w.host r)).read tb'', w.handedReading b'')
                  ∈ windowArrivals t (((ruled p (timedRules w.sender t level) :
                      Solution H R Payload).states w lookahead n).views (w.host r)
                    ++ [w.askedEvent r β])
              ∧ tb'' < (w.speaker r).asked β
              ∧ w.captureReading (w.source.first (b' + 1) - 1)
                ≤ (w.clock w.sender).read ((w.speaker r).asked β)
                  - (q.lo
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
                    - w.blockLength b' * t.knots.nominal * (1 + t.knots.bound)
                    + w.drift (w.host r)
                        (arrivalSlope t (((ruled p (timedRules w.sender t level) :
                            Solution H R Payload).states w lookahead n).views (w.host r)
                          ++ [w.askedEvent r β])) tb'' ((w.speaker r).asked β)
                    + w.knotLate t.knots b')) := by
  have hback : (0 : ℝ) ≤ (timedRules w.sender t level).back := by
    show (0 : ℝ) ≤ 1
    exact zero_le_one
  rcases followed_silent_knot hK lookahead huJ hlohi hstart hback hr hE hk hlt hsilent with
    hnone | ⟨s, hs, hcase⟩
  · exact Or.inl hnone
  · refine Or.inr ⟨s, hs, ?_⟩
    rcases hcase with h0 | htrans | ⟨b', hlate, hknot⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl htrans)
    · obtain ⟨b'', tb'', hmem, -, hlt'', hlow⟩ :=
        timed_reading_lower p w t level hK.noLoss.sender lookahead hr hE hs
      refine Or.inr (Or.inr ⟨b', b'', tb'', hlate, hmem, hlt'', ?_⟩)
      have h1 := hlow ((w.speaker r).asked β)
      have e1 : (w.clock (w.host r)).read ((w.speaker r).asked β) - outputAt t w r β k
          = -((t.lead + ((k : ℝ) - (w.speaker r).first β) / t.rate) * ratioAt t w r β) := by
        unfold outputAt requestReading
        ring
      rw [e1, mul_neg] at h1
      unfold World.knotLate
      linarith

end Unisono.Solutions.Controller
