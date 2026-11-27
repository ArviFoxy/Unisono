/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.ProposedRelink
public import Unisono.Spec.Models.ProposedQuiet
public import Unisono.Spec.Models.GenerativeLinkPause
public import Unisono.Spec.FollowerSteps

/-!
# Two worlds that differ only in the jitter of one link from a time on

Take a world and two draws that differ only in the jitter of the link from
`i₀` to `j₀` from a true time `θ` on (`Draw.SameExceptJitterFrom`), and give
the world the network of each draw (`relinked`). The two worlds have the
same clocks and audio devices.

* `deliversSameBefore_relinked`: they deliver every message at the same
  time, or both at or after `θ` plus the least delay of the link. Jitter
  does not change when a message is released onto its link, so it does not
  change which messages are lost.
* `plays_eq_of_sameJitter`, `lastPlayed_eq_of_sameJitter`: so every solution
  plays the same in both at every output sample of a playback block that is
  requested before `θ` plus the least delay.
* `stall_le_of_sameJitter`: what a jitter of at least `x` from `θ` to `t₁`
  costs, with the room of the world without it. The room is the room that
  the solution kept before it could know of the jitter: it is the same in
  both worlds, so it does not depend on the jitter that begins at `θ`.

All of this holds in one outcome. It is what a bound on expected cost pairs
with the independence of a newly drawn jitter from everything before it.
-/

@[expose] public noncomputable section

namespace Unisono.Spec.ProposedWorld

open GenerativeWorld (backlog)

variable {H : Type} {R : ℕ} {Msg : Type}

/-- **Two draws are the same except for the jitter of the link from `i₀` to
`j₀` from the true time `θ` on.** The clocks and the audio devices are not
compared: the two draws are used with one world. -/
structure Draw.SameExceptJitterFrom (d d' : Draw H R) (i₀ j₀ : H) (θ : Time) : Prop where
  split : d'.split = d.split
  hostPaused : d'.hostPaused = d.hostPaused
  linkPaused : d'.linkPaused = d.linkPaused
  outage : d'.outage = d.outage
  dropped : d'.dropped = d.dropped
  jitter_of_ne : ∀ i j, (i, j) ≠ (i₀, j₀) → d'.jitter i j = d.jitter i j
  jitter_before : ∀ u, u < θ → d'.jitter i₀ j₀ u = d.jitter i₀ j₀ u

namespace Draw

variable (d : Draw H R) (f : Member H R)

/-- A lost message is not delivered. -/
theorem delivery_of_lost {i j : H} {s : Time} {q : ℕ} (h : d.lost i j s q) :
    d.delivery f i j s q = none := by
  classical
  unfold Draw.delivery
  rw [ite_eq_left h]

/-- A message that is not lost is handled at `observed`. -/
theorem delivery_of_not_lost {i j : H} {s : Time} {q : ℕ} (h : ¬ d.lost i j s q) :
    d.delivery f i j s q = some (d.observed f i j s) := by
  classical
  unfold Draw.delivery
  rw [ite_eq_right h]

end Draw

variable {f : Member H R} {d d' : Draw H R} {i₀ j₀ : H} {θ : Time}

/-- **Before a change of jitter can arrive, the two worlds deliver the
same.** For two draws that differ only in the jitter of the link from `i₀`
to `j₀` from `θ` on, a world with the network of the one and with the
network of the other delivers every message at the same time, or both at or
after `θ` plus the least delay of that link. -/
theorem deliversSameBefore_relinked [DecidableEq H] (hd : d.Shaped) (hd' : d'.Shaped)
    (h : d.SameExceptJitterFrom d' i₀ j₀ θ) (w : World H R) :
    World.DeliversSameBefore (θ + d.split i₀ j₀ * f.roundTrip i₀ j₀)
      (relinked f d hd w) (relinked f d' hd' w) := by
  intro i j t q
  show (d.delivery f i j t q = d'.delivery f i j t q
      ∧ ∀ a, d.delivery f i j t q = some a → d.reaches f i j t = d'.reaches f i j t) ∨
    ∃ a₁ a₂, d.delivery f i j t q = some a₁ ∧ d'.delivery f i j t q = some a₂
      ∧ θ + d.split i₀ j₀ * f.roundTrip i₀ j₀ ≤ a₁ ∧ θ + d.split i₀ j₀ * f.roundTrip i₀ j₀ ≤ a₂
  have hrel : d'.released i j t = d.released i j t := by
    unfold Draw.released Draw.leaves
    rw [h.hostPaused, h.linkPaused]
  have hlost : d'.lost i j t q ↔ d.lost i j t q := by
    unfold Draw.lost
    rw [hrel, h.outage, h.dropped]
  by_cases hl : d.lost i j t q
  · left
    rw [d.delivery_of_lost f hl, d'.delivery_of_lost f (hlost.mpr hl)]
    exact ⟨rfl, fun a ha => by cases ha⟩
  · have hl' : ¬ d'.lost i j t q := fun h' => hl (hlost.mp h')
    rw [d.delivery_of_not_lost f hl, d'.delivery_of_not_lost f hl']
    by_cases hsame : (i, j) ≠ (i₀, j₀) ∨ d.released i j t < θ
    · have hj : d'.jitter i j (d.released i j t) = d.jitter i j (d.released i j t) := by
        by_cases hij : (i, j) = (i₀, j₀)
        · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hij
          rcases hsame with hne | hlt
          · exact absurd rfl hne
          · exact h.jitter_before _ hlt
        · rw [h.jitter_of_ne i j hij]
      have hreach : d'.reaches f i j t = d.reaches f i j t := by
        unfold Draw.reaches
        rw [hrel, h.split, hj]
      have hobs : d'.observed f i j t = d.observed f i j t := by
        unfold Draw.observed
        rw [hreach, h.hostPaused]
      left
      exact ⟨by rw [hobs], fun _ _ => hreach.symm⟩
    · obtain ⟨hij, hge⟩ := not_or.mp hsame
      have hij' : (i, j) = (i₀, j₀) := not_not.mp hij
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hij'
      have hge' : θ ≤ d.released i j t := not_lt.mp hge
      right
      refine ⟨_, _, rfl, rfl, ?_, ?_⟩
      · have := Draw.least_le_observed f hd.jitterLevel_nonneg i j t
        linarith
      · have := Draw.least_le_observed f hd'.jitterLevel_nonneg i j t
        rw [hrel, h.split] at this
        linarith

/-- **Before a change of jitter can arrive, every solution plays the same in
both worlds**: at every output sample of every playback block that is
requested before `θ` plus the least delay of the link. -/
theorem plays_eq_of_sameJitter [DecidableEq H] (hd : d.Shaped) (hd' : d'.Shaped)
    (h : d.SameExceptJitterFrom d' i₀ j₀ θ) (w : World H R) (σ : Solution H R Msg)
    (lookahead : ℕ+) {r : Fin R} {b k : ℕ}
    (hb : (w.speaker r).asked b < θ + d.split i₀ j₀ * f.roundTrip i₀ j₀)
    (hk : k ∈ (w.speaker r).block b) :
    σ.plays (relinked f d' hd' w) lookahead r k = σ.plays (relinked f d hd w) lookahead r k :=
  σ.plays_eq_of_sameBefore (w₁ := relinked f d hd w) (w₂ := relinked f d' hd' w) rfl rfl rfl
    rfl rfl rfl (deliversSameBefore_relinked hd hd' h w) lookahead hb hk

/-- The position that a solution played last before a playback block whose
earlier blocks are all requested before `θ` plus the least delay is the same
in both worlds. -/
theorem lastPlayed_eq_of_sameJitter [DecidableEq H] (hd : d.Shaped) (hd' : d'.Shaped)
    (h : d.SameExceptJitterFrom d' i₀ j₀ θ) (w : World H R) (σ : Solution H R Msg)
    (lookahead : ℕ+) {r : Fin R} {b : ℕ}
    (hb : ∀ b' < b, (w.speaker r).asked b' < θ + d.split i₀ j₀ * f.roundTrip i₀ j₀) :
    lastPlayed (σ.plays (relinked f d' hd' w) lookahead r) ((w.speaker r).first b)
      = lastPlayed (σ.plays (relinked f d hd w) lookahead r) ((w.speaker r).first b) := by
  refine lastPlayed_congr fun k hk => ?_
  obtain ⟨b', hb'⟩ := (w.speaker r).exists_block k
  have hlt : b' < b := by
    by_contra hge
    have h1 : (w.speaker r).first b ≤ (w.speaker r).first b' :=
      (w.speaker r).first_strictMono.monotone (not_lt.mp hge)
    unfold PlaybackDevice.block at hb'
    rw [List.mem_range'_1] at hb'
    omega
  exact plays_eq_of_sameJitter hd hd' h w σ lookahead (hb b' hlt) hb'

/-- **What a jitter costs, with the room of the world without it.** Take a
world `w` built from a draw, and two draws `d` and `d'` with its clocks and
audio devices that differ only in the jitter of the link from the sender to
the host of speaker `r` from the true time `θ` on, where the jitter of `d'`
is at least `x` from `θ` to before `t₁`. Consider a solution that carries
frames only on links from the sender or to the sender, whose position at
speaker `r`, in the world of `d'`, advances by at least `s` in every step of
continuous playback, with `0 ≤ s ≤ 1`. Let playback block `b` be one whose
earlier blocks are all requested before `θ` plus the least delay `δ` of the
link, let capture block `c` be handed over at `θ` or later, and let playback
block `β` be requested no later than the earlier of `θ + x` and `t₁`, plus
`δ`. Then, in the world of `d'`, `s` for each output sample from the first
of block `b` to `K`, in a playback block up to `β`, is at most the room from
the position played last before block `b` in the world of `d` to the first
frame of block `c` minus the lookahead, plus the missed samples counted at
those output samples, plus `s` times the discontinuities counted there and
one more. -/
theorem stall_le_of_sameJitter [DecidableEq H] {m : Told H R} {e : Draw H R} {w : World H R}
    (hB : Builds m f e w) {a a' : Draw H R} (hd : (e.withLinks a).Shaped)
    (hd' : (e.withLinks a').Shaped) {r : Fin R} {θ t₁ x : ℝ}
    (h : (e.withLinks a).SameExceptJitterFrom (e.withLinks a') w.sender (w.host r) θ)
    (hjit : ∀ u, θ ≤ u → u < t₁ → x ≤ (e.withLinks a').jitter w.sender (w.host r) u)
    (σ : Solution H R Msg)
    (hframes : σ.CarriesFramesOn fun h dst => h = w.sender ∨ dst = w.sender) (lookahead : ℕ+)
    (hr : w.host r ≠ w.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k y z,
      σ.plays (relinked f (e.withLinks a') hd' w) lookahead r k = some y →
      σ.plays (relinked f (e.withLinks a') hd' w) lookahead r (k + 1) = some z →
      y < z → z < y + 2 → y + s ≤ z)
    {c β b K : ℕ} (hK : (w.speaker r).first b ≤ K) (hKβ : K < (w.speaker r).first (β + 1))
    (hb : ∀ b' < b, (w.speaker r).asked b'
      < θ + (e.withLinks a).split w.sender (w.host r) * f.roundTrip w.sender (w.host r))
    (hc : θ ≤ w.source.handed c)
    (hβ : (w.speaker r).asked β
      ≤ min (θ + x) t₁
        + (e.withLinks a).split w.sender (w.host r) * f.roundTrip w.sender (w.host r)) :
    s * ((K : ℝ) + 1 - ((w.speaker r).first b : ℕ))
      ≤ max ((w.source.first c : ℝ) - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays (relinked f (e.withLinks a) hd w) lookahead r)
              ((w.speaker r).first b)).getD 0) 0
        + ∑ k ∈ Finset.Ico ((w.speaker r).first b) (K + 1),
            (missedAt (σ.plays (relinked f (e.withLinks a') hd' w) lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico ((w.speaker r).first b) K,
            (discontinuityAt (σ.plays (relinked f (e.withLinks a') hd' w) lookahead r) k : ℝ)
              + 1) := by
  have hB' := hB.relinked hd'
  have hsplit : (e.withLinks a').split w.sender (w.host r)
      = (e.withLinks a).split w.sender (w.host r) := rfl
  have hquiet := hB'.quiet_of_jitter hd'.jitterLevel_nonneg hjit
  have hmain := σ.stall_le_of_quiet (relinked f (e.withLinks a') hd' w) lookahead hframes hr
    hs0 hs1 hslow (t₀ := θ)
    (e := min (θ + x) t₁
      + (e.withLinks a').split w.sender (w.host r) * f.roundTrip w.sender (w.host r))
    (fun u q a ha hdel => hquiet u q a ha hdel) hK hKβ hc (by rw [hsplit]; exact hβ)
  rw [lastPlayed_eq_of_sameJitter hd hd' h w σ lookahead hb] at hmain
  exact hmain

end Unisono.Spec.ProposedWorld
