/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeBlockLatency
public import Unisono.Spec.Models.GenerativeLinkPause

/-!
# The room of a speaker before a playback block

For a solution whose hosts exchange messages only with the sender, what a
speaker can still play when the link from the sender pauses is bounded by
what can have arrived. This file names that bound and states the two facts
about it that a bound on expected cost will pair.

* `World.blockFrom w T` is the first capture block that is handed over at or
  after true time `T`.
* `room` of speaker `r` before playback block `b`, for a draw: take the
  first capture block `c` that is handed over no earlier than the least
  delay before the request of block `b`. No frame of block `c` or of a later
  block can have arrived by that request. The room is
  `c * blockSize - lookahead` minus the position played last before block
  `b`: how far the speaker can still advance without a new arrival.

**Latency** (`ConstantRates.room_lt_latency`). Every frame that a step
inside playback block `b` passes on new ground is played with a latency
above the least latency plus the time in which the capture device captures
as many frames as the room before block `b + 1` holds, minus the small terms
of `ConstantRates.block_lt_latency`.

**Pause** (`drawWorld_stall_le_room`). If a pause of the link from the
sender begins early enough that block `b` is the first playback block
requested after it can be noticed, the output samples from the first of
block `b` on cost missed samples and discontinuities except for the room
before block `b`, taken in the world without the pause.

Both hold in one outcome. They are not yet combined into a bound on expected
cost.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {H : Type} {R : ℕ}

/-- The first capture block that is handed over at or after true time `T`;
zero if there is none. -/
def World.blockFrom (w : World H R) (T : Time) : ℕ := by
  classical
  exact if h : ∃ c, T ≤ w.source.handed c then Nat.find h else 0

theorem World.le_handed_blockFrom (w : World H R) {T : Time}
    (h : ∃ c, T ≤ w.source.handed c) : T ≤ w.source.handed (w.blockFrom T) := by
  classical
  unfold World.blockFrom
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem World.handed_lt_of_lt_blockFrom (w : World H R) {T : Time}
    (h : ∃ c, T ≤ w.source.handed c) {c : ℕ} (hc : c < w.blockFrom T) :
    w.source.handed c < T := by
  classical
  unfold World.blockFrom at hc
  rw [dite_eq_left h] at hc
  exact not_le.mp (Nat.find_min h hc)

namespace GenerativeWorld

variable {Msg : Type} [DecidableEq H] {m : GenerativeWorld H R} {f : Member H R}
  {d d' : Draw H R} {w : World H R}

/-- The room of speaker `r` before playback block `b`, for the draw `d`, the
world `w` and what the speaker plays: `c * blockSize - lookahead` minus the
position played last before block `b` (zero if none), where `c` is the first
capture block that is handed over no earlier than the least delay before the
request of block `b`. -/
def room (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (lookahead : ℕ+) (plays : ℕ → Option ℝ) (r : Fin R) (b : ℕ) : ℝ :=
  (w.blockFrom ((w.speaker r).asked b
        - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) : ℝ) * m.blockSize
    - ((lookahead : ℕ) : ℝ) - (lastPlayed plays (b * m.blockSize)).getD 0

omit [DecidableEq H] in
/-- In a world whose clocks run at constant rates, some capture block is
handed over at or after every true time. -/
theorem ConstantRates.exists_le_handed (hS : ConstantRates m f d w) (T : Time) :
    ∃ c, T ≤ w.source.handed c := by
  obtain ⟨c, hc⟩ := hS.handed_unbounded T
  exact ⟨c, hc.le⟩

/-- **The frames of a playback block are played late by the room before the
next block.** Consider a world whose clocks run at constant rates, with
exact timestamps and with pauses of links and of hosts, a solution whose
hosts exchange messages only with the sender, and a speaker `r` whose host
is not the sender's, whose position advances by at least `s`, with `0 ≤ s`,
in every step of continuous playback. If the speaker has played the source
before playback block `b + 1`, every frame that a step between two output
samples of playback block `b` passes on new ground is played with a latency
above `leastLatency`, plus the time in which the capture device captures as
many frames as the room before block `b + 1` holds, minus the three small
terms of `ConstantRates.block_lt_latency`. -/
theorem ConstantRates.room_lt_latency (hS : ConstantRates m f d w) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R} (hr : m.host r ≠ m.sender)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {b : ℕ} {xLast : ℝ}
    (hlast : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) = some xLast)
    {n : ℕ}
    (hn : n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
      ((b + 1) * m.blockSize - 1)) :
    ∃ l, w.latency (σ.plays w lookahead) r n = some l ∧
      leastLatency m f d lookahead r
          + room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
            / (m.rate * Real.exp (d.deviceLogRate none))
          - 2 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          - (m.blockSize : ℝ)
            * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
              - s / (m.rate * Real.exp (d.deviceLogRate none))) 0
          - (s * (((m.blockSize : ℝ) - 1)
                - ((continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
                  - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
              + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
            / (m.rate * Real.exp (d.deviceLogRate none))
        < l := by
  have hex := hS.exists_le_handed ((w.speaker r).asked (b + 1)
    - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
  have hc : w.blockFrom ((w.speaker r).asked (b + 1)
        - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) = 0
      ∨ w.source.handed (w.blockFrom ((w.speaker r).asked (b + 1)
        - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) - 1)
        < (w.speaker r).asked (b + 1)
          - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r) := by
    rcases Nat.eq_zero_or_pos (w.blockFrom ((w.speaker r).asked (b + 1)
      - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))) with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr (w.handed_lt_of_lt_blockFrom hex (Nat.sub_lt hpos Nat.one_pos))
  have h := hS.block_lt_latency σ hstar lookahead hr hs0 hslow hlast hc hn
  unfold room
  rw [hlast]
  exact h

/-- **What a pause costs, against the room of the world without it.** Take
two draws with steady clocks that differ by pauses of the link from the
sender to the host of speaker `r` from `θ` on: `d` without and `d'` with a
pause of length at least `X` that begins at `θ`. Consider a solution whose
hosts exchange messages only with the sender, whose position at speaker `r`,
in the world with the pause, advances by at least `s` in every step of
continuous playback, with `0 ≤ s ≤ 1`. Let `b` be a playback block such that
all earlier blocks are requested before `θ` plus the least delay `δ`, and
block `b` itself no earlier, and let playback block `β` be requested no
later than `θ + X + δ`. Then, in the world with the pause, `s` for each
output sample from the first of block `b` to `K`, in a playback block up to
`β`, is at most the room before block `b` in the world without the pause, or
zero if that is negative, plus the missed samples counted at those output
samples, plus `s` times the discontinuities counted there and one more. -/
theorem drawWorld_stall_le_room {hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h} {θ : Time}
    (hd : d.Steady) (hd' : d'.Steady) {r : Fin R}
    (h : d.SameExceptLinkFrom d' m.sender (m.host r) θ) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) (hr : m.host r ≠ m.sender) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays (drawWorld m f hex d' hd') lookahead r k = some x →
      σ.plays (drawWorld m f hex d' hd') lookahead r (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {X : ℝ}
    (hjump : ∀ t < θ, X ≤ d'.linkPaused m.sender (m.host r) θ
      - d'.linkPaused m.sender (m.host r) t)
    {β b K : ℕ} (hK : b * m.blockSize ≤ K) (hKβ : K / m.blockSize ≤ β)
    (hb : ∀ b' < b, ((drawWorld m f hex d hd).speaker r).asked b'
      < θ + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    (hθ : θ + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
      ≤ ((drawWorld m f hex d hd).speaker r).asked b)
    (hβ : ((drawWorld m f hex d hd).speaker r).asked β
      ≤ θ + X + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) :
    s * ((K : ℝ) + 1 - (b * m.blockSize : ℕ))
      ≤ max (room m f d (drawWorld m f hex d hd) lookahead
          (σ.plays (drawWorld m f hex d hd) lookahead r) r b) 0
        + ∑ k ∈ Finset.Ico (b * m.blockSize) (K + 1),
            (missedAt (σ.plays (drawWorld m f hex d' hd') lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico (b * m.blockSize) K,
            (discontinuityAt (σ.plays (drawWorld m f hex d' hd') lookahead r) k : ℝ) + 1) := by
  have hS := drawWorld_constantRates m f hex d hd
  have hexc := hS.exists_le_handed (((drawWorld m f hex d hd).speaker r).asked b
    - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
  have hc := (drawWorld m f hex d hd).le_handed_blockFrom hexc
  exact drawWorld_stall_le_of_pause hd hd' h σ hstar lookahead hr hs0 hs1 hslow hjump hK hKβ hb
    (by linarith) hβ

/-- **The latency that one playback block accrues, against the room before
the next.** In the setting of `ConstantRates.room_lt_latency`, let `G` be
`leastLatency` plus the time in which the capture device captures as many
frames as the room before block `b + 1` holds, minus two periods of the
playback device and `blockSize` times the positive part of one period of the
playback device less the time in which the capture device captures `s`
frames. Let `Gcap ≥ 0` be any cap. Then the latencies of the frames that the
steps between two output samples of block `b` pass on new ground sum to at
least `s * (blockSize - 1)` times the smaller of `G` and `Gcap` (zero if `G`
is negative), minus `(1 + 2 s) * Gcap` for each of those steps that does not
break new ground, minus `(1 + s) * Gcap`, and minus `s * (blockSize - 1)`
times the time in which the capture device captures `s` frames for each step
of the block that is not continuous and one frame for each missed sample
counted in the block. -/
theorem ConstantRates.le_sum_latencyAt (hS : ConstantRates m f d w) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R} (hr : m.host r ≠ m.sender)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {b : ℕ} {xLast : ℝ}
    (hlast : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) = some xLast)
    {Gcap : ℝ} (hcap : 0 ≤ Gcap) :
    ENNReal.ofReal
        (s * ((m.blockSize : ℝ) - 1)
            * min (max (leastLatency m f d lookahead r
                + room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
                  / (m.rate * Real.exp (d.deviceLogRate none))
                - 2 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
                - (m.blockSize : ℝ)
                  * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
                    - s / (m.rate * Real.exp (d.deviceLogRate none))) 0) 0) Gcap
          - ((1 + 2 * s) * ((m.blockSize : ℝ) - 1
                - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
                    ((b + 1) * m.blockSize - 1))
              + (1 + s)) * Gcap
          - s * ((m.blockSize : ℝ) - 1)
            * ((s * (((m.blockSize : ℝ) - 1)
                  - ((continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
                    - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                  - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
              / (m.rate * Real.exp (d.deviceLogRate none))))
      ≤ ∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize) ((b + 1) * m.blockSize - 1),
          w.latencyAt (σ.plays w lookahead) r n := by
  have hc0 : 0 < m.rate * Real.exp (d.deviceLogRate none) :=
    mul_pos m.rate_pos (Real.exp_pos _)
  have hBpos := m.blockSize_pos
  -- The quantities of the block.
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = leastLatency m f d lookahead r
      + room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
        / (m.rate * Real.exp (d.deviceLogRate none))
      - 2 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
      - (m.blockSize : ℝ)
        * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          - s / (m.rate * Real.exp (d.deviceLogRate none))) 0 := ⟨_, rfl⟩
  obtain ⟨pen, hpen⟩ : ∃ pen : ℝ, pen = (s * (((m.blockSize : ℝ) - 1)
        - ((continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
          - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
      + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
        - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
      / (m.rate * Real.exp (d.deviceLogRate none)) := ⟨_, rfl⟩
  rw [← hG, ← hpen]
  have hle : b * m.blockSize ≤ (b + 1) * m.blockSize - 1 := by
    have e : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
    omega
  have hsize : (((b + 1) * m.blockSize - 1 : ℕ) : ℝ) - ((b * m.blockSize : ℕ) : ℝ)
      = (m.blockSize : ℝ) - 1 := by
    have e : (b + 1) * m.blockSize - 1 + 1 = b * m.blockSize + m.blockSize := by
      have e' : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
      omega
    have e2 : (((b + 1) * m.blockSize - 1 : ℕ) : ℝ) + 1
        = ((b * m.blockSize : ℕ) : ℝ) + (m.blockSize : ℝ) := by exact_mod_cast e
    linarith
  -- The losses are not negative.
  have hcont := continuousBefore_le_add (plays := σ.plays w lookahead r) hle
  have hcont' : (continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
      - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
      ≤ (m.blockSize : ℝ) - 1 := by
    have h' : (continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
        ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
          + (((b + 1) * m.blockSize - 1 - b * m.blockSize : ℕ) : ℝ) := by exact_mod_cast hcont
    rw [Nat.cast_sub hle, hsize] at h'
    linarith
  have hmiss : (missedBefore (σ.plays w lookahead r) (b * m.blockSize) : ℝ)
      ≤ missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) := by
    have h := missedBefore_mono (σ.plays w lookahead r)
      (show b * m.blockSize ≤ (b + 1) * m.blockSize by
        exact Nat.mul_le_mul_right _ (Nat.le_succ b))
    exact_mod_cast h
  have hpen0 : 0 ≤ pen := by
    rw [hpen]
    exact div_nonneg (add_nonneg (mul_nonneg hs0 (by linarith)) (by linarith)) hc0.le
  -- The smaller of `G` and the cap.
  have hĜ0 : 0 ≤ min (max G 0) Gcap := le_min (le_max_right _ _) hcap
  have hĜcap : min (max G 0) Gcap ≤ Gcap := min_le_right _ _
  have hĜg : min (max G 0) Gcap - pen ≤ max (G - pen) 0 := by
    have h1 : min (max G 0) Gcap ≤ max G 0 := min_le_left _ _
    rcases le_total 0 G with hG0 | hG0
    · have hmax : max G 0 = G := max_eq_left hG0
      have h2 : min (max G 0) Gcap - pen ≤ G - pen := by linarith
      exact h2.trans (le_max_left _ _)
    · have hmax : max G 0 = 0 := max_eq_right hG0
      have h2 : min (max G 0) Gcap - pen ≤ 0 := by linarith
      exact h2.trans (le_max_right _ _)
  have hcount := le_card_newFrames_mul hs0 hslow hle hĜ0 hĜcap hpen0 hĜg
  rw [hsize] at hcount
  -- Each frame is worth at least `max (G - pen) 0`.
  have hframe : ∀ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
      ((b + 1) * m.blockSize - 1),
      ENNReal.ofReal (max (G - pen) 0) ≤ w.latencyAt (σ.plays w lookahead) r n := by
    intro n hn
    obtain ⟨l, hl, hlt⟩ := hS.room_lt_latency σ hstar lookahead hr hs0 hslow hlast hn
    rw [← hG, ← hpen] at hlt
    unfold World.latencyAt
    rw [hl]
    rcases le_total (G - pen) 0 with hneg | hpos
    · rw [max_eq_right hneg, ENNReal.ofReal_zero]
      exact bot_le
    · rw [max_eq_left hpos]
      exact ENNReal.ofReal_le_ofReal hlt.le
  calc ENNReal.ofReal
        (s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap
          - ((1 + 2 * s) * ((m.blockSize : ℝ) - 1
                - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
                    ((b + 1) * m.blockSize - 1))
              + (1 + s)) * Gcap
          - s * ((m.blockSize : ℝ) - 1) * pen)
      ≤ ENNReal.ofReal (((newFrames (σ.plays w lookahead r) (b * m.blockSize)
          ((b + 1) * m.blockSize - 1)).card : ℝ) * max (G - pen) 0) :=
        ENNReal.ofReal_le_ofReal hcount
    _ = ∑ _n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
          ((b + 1) * m.blockSize - 1), ENNReal.ofReal (max (G - pen) 0) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
          ((b + 1) * m.blockSize - 1), w.latencyAt (σ.plays w lookahead) r n :=
        Finset.sum_le_sum hframe

end GenerativeWorld

/-- If no output sample before `K` plays the source, no step before `K`
breaks new ground. -/
theorem newGroundCount_of_none {plays : ℕ → Option ℝ} (a : ℕ) :
    ∀ K, (∀ k < K, plays k = none) → newGroundCount plays a K = 0
  | 0, _ => rfl
  | K + 1, h => by
    have ih := newGroundCount_of_none a K fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hc : ¬ (a ≤ K ∧ NewGround plays K) := by
      rintro ⟨-, x, _, hx, -⟩
      rw [h K (Nat.lt_succ_self K)] at hx
      exact absurd hx (by simp)
    rw [newGroundCount_succ_of_not hc]
    exact ih

namespace GenerativeWorld

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] {m : GenerativeWorld H R}
  {f : Member H R} {d : Draw H R} {w : World H R}

/-- **The latency of one playback block, with its losses on the other
side.** In the setting of `ConstantRates.le_sum_latencyAt`, for every
playback block `b`, whether or not the speaker has played the source by
then: `s * (blockSize - 1)` times the smaller of `G` and the cap `Gcap`
(zero if `G` is negative) is at most the latencies of the frames that the
steps inside block `b` pass on new ground, plus the losses of the block:
`(1 + 2 s) * Gcap` for each of those steps that does not break new ground,
`(1 + s) * Gcap`, and `s * (blockSize - 1)` times the time in which the
capture device captures `s` frames for each step that is not continuous and
one frame for each missed sample of the block. Here `blockSize` is at least
one, `0 ≤ s` and `0 ≤ Gcap`. -/
theorem ConstantRates.le_sum_add_loss (hS : ConstantRates m f d w) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R} (hr : m.host r ≠ m.sender)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    (b : ℕ) {Gcap : ℝ} (hcap : 0 ≤ Gcap) :
    ENNReal.ofReal
        (s * ((m.blockSize : ℝ) - 1)
            * min (max (leastLatency m f d lookahead r
                + room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
                  / (m.rate * Real.exp (d.deviceLogRate none))
                - 2 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
                - (m.blockSize : ℝ)
                  * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
                    - s / (m.rate * Real.exp (d.deviceLogRate none))) 0) 0) Gcap)
      ≤ ∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize) ((b + 1) * m.blockSize - 1),
          w.latencyAt (σ.plays w lookahead) r n
        + ENNReal.ofReal
          (((1 + 2 * s) * ((m.blockSize : ℝ) - 1
                - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
                    ((b + 1) * m.blockSize - 1))
              + (1 + s)) * Gcap
            + s * ((m.blockSize : ℝ) - 1)
              * ((s * (((m.blockSize : ℝ) - 1)
                    - ((continuousBefore (σ.plays w lookahead r)
                          ((b + 1) * m.blockSize - 1) : ℝ)
                      - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                  + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                    - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
                / (m.rate * Real.exp (d.deviceLogRate none)))) := by
  obtain ⟨Ĝ, hĜ⟩ : ∃ Ĝ : ℝ, Ĝ = min (max (leastLatency m f d lookahead r
      + room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
        / (m.rate * Real.exp (d.deviceLogRate none))
      - 2 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
      - (m.blockSize : ℝ)
        * max (1 / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))
          - s / (m.rate * Real.exp (d.deviceLogRate none))) 0) 0) Gcap := ⟨_, rfl⟩
  obtain ⟨err, herr⟩ : ∃ err : ℝ, err = ((1 + 2 * s) * ((m.blockSize : ℝ) - 1
        - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
            ((b + 1) * m.blockSize - 1))
      + (1 + s)) * Gcap
    + s * ((m.blockSize : ℝ) - 1)
      * ((s * (((m.blockSize : ℝ) - 1)
            - ((continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
              - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
          + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
            - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
        / (m.rate * Real.exp (d.deviceLogRate none))) := ⟨_, rfl⟩
  rw [← hĜ, ← herr]
  have hc0 : 0 < m.rate * Real.exp (d.deviceLogRate none) :=
    mul_pos m.rate_pos (Real.exp_pos _)
  have hB1 : (0 : ℝ) ≤ (m.blockSize : ℝ) - 1 := by
    have h1 : 1 ≤ m.blockSize := m.blockSize_pos
    have h2 : (1 : ℝ) ≤ (m.blockSize : ℝ) := by exact_mod_cast h1
    linarith
  have hĜ0 : 0 ≤ Ĝ := by
    rw [hĜ]
    exact le_min (le_max_right _ _) hcap
  have hĜcap : Ĝ ≤ Gcap := by
    rw [hĜ]
    exact min_le_right _ _
  cases hlast : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) with
  | some xLast =>
    have h := hS.le_sum_latencyAt σ hstar lookahead hr hs0 hslow hlast hcap
    rw [← hĜ] at h
    have hsplit : s * ((m.blockSize : ℝ) - 1) * Ĝ
        = (s * ((m.blockSize : ℝ) - 1) * Ĝ - err) + err := by ring
    have herr' : s * ((m.blockSize : ℝ) - 1) * Ĝ - err
        = s * ((m.blockSize : ℝ) - 1) * Ĝ
          - ((1 + 2 * s) * ((m.blockSize : ℝ) - 1
                - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
                    ((b + 1) * m.blockSize - 1))
              + (1 + s)) * Gcap
          - s * ((m.blockSize : ℝ) - 1)
            * ((s * (((m.blockSize : ℝ) - 1)
                  - ((continuousBefore (σ.plays w lookahead r)
                        ((b + 1) * m.blockSize - 1) : ℝ)
                    - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                  - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
              / (m.rate * Real.exp (d.deviceLogRate none))) := by
      rw [herr]
      ring
    rw [← herr'] at h
    calc ENNReal.ofReal (s * ((m.blockSize : ℝ) - 1) * Ĝ)
        = ENNReal.ofReal ((s * ((m.blockSize : ℝ) - 1) * Ĝ - err) + err) := by rw [← hsplit]
      _ ≤ ENNReal.ofReal (s * ((m.blockSize : ℝ) - 1) * Ĝ - err) + ENNReal.ofReal err :=
          ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add h le_rfl
  | none =>
    -- Nothing was played: no step breaks new ground, and the losses cover the bound.
    have hnone := eq_none_of_lastPlayed_none hlast
    have hcount : newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
        ((b + 1) * m.blockSize - 1) = 0 :=
      newGroundCount_of_none _ _ fun k hk => hnone k (by omega)
    have hle : b * m.blockSize ≤ (b + 1) * m.blockSize - 1 := by
      have e : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
      have := m.blockSize_pos
      omega
    have hsize : (((b + 1) * m.blockSize - 1 : ℕ) : ℝ) - ((b * m.blockSize : ℕ) : ℝ)
        = (m.blockSize : ℝ) - 1 := by
      have e : (b + 1) * m.blockSize - 1 + 1 = b * m.blockSize + m.blockSize := by
        have e' : (b + 1) * m.blockSize = b * m.blockSize + m.blockSize := by ring
        have := m.blockSize_pos
        omega
      have e2 : (((b + 1) * m.blockSize - 1 : ℕ) : ℝ) + 1
          = ((b * m.blockSize : ℕ) : ℝ) + (m.blockSize : ℝ) := by exact_mod_cast e
      linarith
    have hcont := continuousBefore_le_add (plays := σ.plays w lookahead r) hle
    have hcont' : (continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
        - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
        ≤ (m.blockSize : ℝ) - 1 := by
      have h' : (continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
          ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
            + (((b + 1) * m.blockSize - 1 - b * m.blockSize : ℕ) : ℝ) := by
        exact_mod_cast hcont
      rw [Nat.cast_sub hle, hsize] at h'
      linarith
    have hmiss : (missedBefore (σ.plays w lookahead r) (b * m.blockSize) : ℝ)
        ≤ missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) := by
      have h := missedBefore_mono (σ.plays w lookahead r)
        (show b * m.blockSize ≤ (b + 1) * m.blockSize from
          Nat.mul_le_mul_right _ (Nat.le_succ b))
      exact_mod_cast h
    have hpen : (0 : ℝ) ≤ s * ((m.blockSize : ℝ) - 1)
        * ((s * (((m.blockSize : ℝ) - 1)
              - ((continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
                - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
            + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
              - missedBefore (σ.plays w lookahead r) (b * m.blockSize)))
          / (m.rate * Real.exp (d.deviceLogRate none))) :=
      mul_nonneg (mul_nonneg hs0 hB1)
        (div_nonneg (add_nonneg (mul_nonneg hs0 (by linarith)) (by linarith)) hc0.le)
    have hbound : s * ((m.blockSize : ℝ) - 1) * Ĝ ≤ err := by
      rw [herr, hcount]
      have h1 : s * ((m.blockSize : ℝ) - 1) * Ĝ ≤ s * ((m.blockSize : ℝ) - 1) * Gcap :=
        mul_le_mul_of_nonneg_left hĜcap (mul_nonneg hs0 hB1)
      have h2 : (0 : ℝ) ≤ ((m.blockSize : ℝ) - 1) * Gcap := mul_nonneg hB1 hcap
      have h3 : (0 : ℝ) ≤ s * (((m.blockSize : ℝ) - 1) * Gcap) := mul_nonneg hs0 h2
      have h4 : (0 : ℝ) ≤ (1 + s) * Gcap := mul_nonneg (by linarith) hcap
      push_cast
      nlinarith
    exact (ENNReal.ofReal_le_ofReal hbound).trans le_add_self

end GenerativeWorld

end Unisono.Spec
