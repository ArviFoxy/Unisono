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
about it that a bound on expected cost will pair. Both hold in one outcome
of any member of the generative model: the clocks may wander and the
timestamps may have errors.

* `World.blockFrom w T` is the first capture block that is handed over at or
  after true time `T`.
* `room` of speaker `r` before playback block `b`, for a draw: take the
  first capture block `c` that is handed over no earlier than the least
  delay before the request of block `b`. No frame of block `c` or of a later
  block can have arrived by that request. The room is
  `c * blockSize - lookahead` minus the position played last before block
  `b`: how far the speaker can still advance without a new arrival.

**Latency** (`Builds.room_le_latency`, `Builds.le_sum_add_loss`). Every
frame that a step inside playback block `b` passes on new ground is played
with a latency of at least a cap `Gcap`, or of at least the least delay,
plus the time from the request of block `b + 1` to its first output sample,
plus the time `pc` for each frame of the room before block `b + 1` and for
`lookahead - 1` frames, minus small terms. Here `pc` is at most the time
between two frames captured near the block, and the small terms use `pr`,
at least the time between two output samples of the block. Summed over the
block, with the losses on the other side, the statement holds for every
block.

**Pause** (`Builds.stall_le_room`). If paused time of the link from the
sender begins in an interval so early that block `b` is the first playback
block requested after it can be noticed, the output samples from the first
of block `b` on cost missed samples and discontinuities except for the room
before block `b`, taken in the world without that paused time.

The same quantity is on both sides: a large room means late frames, a small
room means missed samples in a pause. The two are not yet combined into a
bound on expected cost.
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
/-- In a world built from a draw, some capture block is handed over at or
after every true time: the clock of the capture device never stands
still. -/
theorem Builds.exists_le_handed (hB : m.Builds f d w) (T : Time) :
    ∃ c, T ≤ w.source.handed c := by
  obtain ⟨dc, hdc⟩ := hB.deviceClock none
  obtain ⟨n, hn⟩ := exists_nat_gt ((dc.read T - dc.read (w.source.capture 0)) * m.rate)
  refine ⟨n, ?_⟩
  have hcap : T < w.source.capture n := by
    by_contra hle
    have h1 := dc.strictMono.monotone (not_lt.mp hle)
    have h2 := hB.capture n
    rw [← hdc (w.source.capture n), ← hdc (w.source.capture 0)] at h2
    have h3 : (n : ℝ) / m.rate ≤ dc.read T - dc.read (w.source.capture 0) := by linarith
    have h4 := (div_le_iff₀ m.rate_pos).mp h3
    linarith
  have hidx : n ≤ w.source.first (n + 1) - 1 := by
    rw [hB.capture_first]
    have h5 : n + 1 ≤ (n + 1) * m.blockSize := Nat.le_mul_of_pos_right _ m.blockSize_pos
    omega
  exact (hcap.le.trans (w.source.capture_strictMono.monotone hidx)).trans
    (w.source.handed_after n)

/-- **The frames of a playback block are played late by the room before the
next block.** `Builds.block_le_latency` with the capture block of the room:
in a world built from a draw whose least delays are not negative and whose
paused times never decrease, for a solution whose hosts exchange messages
only with the sender and a speaker `r` whose host is not the sender's, whose
position advances by at least `s ≥ 0` in every step of continuous playback.
Let the speaker have played the source before playback block `b + 1`, and
let `pr`, `pc` and `Gcap` bound the audio devices near block `b` as in
`Builds.block_le_latency`. Then every frame that a step between two output
samples of block `b` passes on new ground is played with a latency of at
least the smaller of `Gcap` and: the least delay, plus the time from the
request of block `b + 1` to its first output sample, plus `pc` times the
room before block `b + 1` and `lookahead - 1` frames, minus the small terms
of `Builds.block_le_latency`. -/
theorem Builds.room_le_latency (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {b : ℕ} {xLast : ℝ}
    (hlast : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) = some xLast)
    {pc pr Gcap : ℝ} (hpc0 : 0 ≤ pc)
    (hpr : ∀ k, b * m.blockSize ≤ k → k < (b + 1) * m.blockSize →
      (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ pr)
    (hpc : ∀ i, (w.speaker r).out (b * m.blockSize) - Gcap < w.source.capture i →
      w.source.capture (i + 1) ≤ (w.speaker r).asked (b + 1) →
      pc ≤ w.source.capture (i + 1) - w.source.capture i)
    {n : ℕ}
    (hn : n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
      ((b + 1) * m.blockSize - 1)) :
    ∃ l, w.latency (σ.plays w lookahead) r n = some l ∧
      min Gcap
          (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
            + ((w.speaker r).out ((b + 1) * m.blockSize) - (w.speaker r).asked (b + 1))
            + pc * (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
              + ((lookahead : ℕ) : ℝ) - 1)
            - 2 * pr
            - (m.blockSize : ℝ) * max (pr - s * pc) 0
            - pc * (s * (((m.blockSize : ℝ) - 1)
                  - ((continuousBefore (σ.plays w lookahead r)
                        ((b + 1) * m.blockSize - 1) : ℝ)
                    - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                  - missedBefore (σ.plays w lookahead r) (b * m.blockSize))))
        ≤ l := by
  have hex := hB.exists_le_handed ((w.speaker r).asked (b + 1)
    - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
  have h := hB.block_le_latency hpos hlink hhost σ hstar lookahead hr hs0 hslow hlast
    (w.le_handed_blockFrom hex) (fun c' hc' => w.handed_lt_of_lt_blockFrom hex hc') hpc0 hpr
    hpc hn
  have e : room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
        + ((lookahead : ℕ) : ℝ) - 1
      = (w.blockFrom ((w.speaker r).asked (b + 1)
          - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) : ℝ)
        * m.blockSize - 1 - xLast := by
    unfold room
    rw [hlast]
    simp only [Option.getD_some]
    ring
  rw [e]
  exact h

/-- **The latency of one playback block against the room, with its losses
on the other side, and each latency counted up to the cap.** In the setting of `Builds.room_le_latency`, for every
playback block `b`, whether or not the speaker has played the source by
then. Let `G` be the least delay, plus the time from the request of block
`b + 1` to its first output sample, plus `pc` times the room before block
`b + 1` and `lookahead - 1` frames, minus `2 * pr` and `blockSize` times the
positive part of `pr - s * pc`. Let `Gcap ≥ 0` be the cap. Then
`s * (blockSize - 1)` times the smaller of `G` and `Gcap` (zero if `G` is
negative) is at most the latencies of the frames that the steps inside block
`b` pass on new ground, each counted up to `Gcap`, plus the losses of the
block: `(1 + 2 s) * Gcap` for
each of those steps that does not break new ground, `(1 + s) * Gcap`, and
`s * (blockSize - 1) * pc` times: `s` for each step that is not continuous
and one for each missed sample of the block. -/
theorem Builds.le_sum_min_add_loss (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    (b : ℕ) {pc pr Gcap : ℝ} (hpc0 : 0 ≤ pc) (hcap : 0 ≤ Gcap)
    (hpr : ∀ k, b * m.blockSize ≤ k → k < (b + 1) * m.blockSize →
      (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ pr)
    (hpc : ∀ i, (w.speaker r).out (b * m.blockSize) - Gcap < w.source.capture i →
      w.source.capture (i + 1) ≤ (w.speaker r).asked (b + 1) →
      pc ≤ w.source.capture (i + 1) - w.source.capture i) :
    ENNReal.ofReal
        (s * ((m.blockSize : ℝ) - 1)
          * min (max (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
              + ((w.speaker r).out ((b + 1) * m.blockSize) - (w.speaker r).asked (b + 1))
              + pc * (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
                + ((lookahead : ℕ) : ℝ) - 1)
              - 2 * pr
              - (m.blockSize : ℝ) * max (pr - s * pc) 0) 0) Gcap)
      ≤ ∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize) ((b + 1) * m.blockSize - 1),
          min (w.latencyAt (σ.plays w lookahead) r n) (ENNReal.ofReal Gcap)
        + ENNReal.ofReal
          (((1 + 2 * s) * ((m.blockSize : ℝ) - 1
                - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
                    ((b + 1) * m.blockSize - 1))
              + (1 + s)) * Gcap
            + s * ((m.blockSize : ℝ) - 1)
              * (pc * (s * (((m.blockSize : ℝ) - 1)
                    - ((continuousBefore (σ.plays w lookahead r)
                          ((b + 1) * m.blockSize - 1) : ℝ)
                      - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                  + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                    - missedBefore (σ.plays w lookahead r) (b * m.blockSize))))) := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
      + ((w.speaker r).out ((b + 1) * m.blockSize) - (w.speaker r).asked (b + 1))
      + pc * (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
        + ((lookahead : ℕ) : ℝ) - 1)
      - 2 * pr
      - (m.blockSize : ℝ) * max (pr - s * pc) 0 := ⟨_, rfl⟩
  obtain ⟨pen, hpen⟩ : ∃ pen : ℝ, pen = pc * (s * (((m.blockSize : ℝ) - 1)
        - ((continuousBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize - 1) : ℝ)
          - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
      + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
        - missedBefore (σ.plays w lookahead r) (b * m.blockSize))) := ⟨_, rfl⟩
  rw [← hG, ← hpen]
  have hB1 : (0 : ℝ) ≤ (m.blockSize : ℝ) - 1 := by
    have h1 : 1 ≤ m.blockSize := m.blockSize_pos
    have h2 : (1 : ℝ) ≤ (m.blockSize : ℝ) := by exact_mod_cast h1
    linarith
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
      (show b * m.blockSize ≤ (b + 1) * m.blockSize from
        Nat.mul_le_mul_right _ (Nat.le_succ b))
    exact_mod_cast h
  have hpen0 : 0 ≤ pen := by
    rw [hpen]
    exact mul_nonneg hpc0 (add_nonneg (mul_nonneg hs0 (by linarith)) (by linarith))
  -- The smaller of `G` and the cap.
  have hĜ0 : 0 ≤ min (max G 0) Gcap := le_min (le_max_right _ _) hcap
  have hĜcap : min (max G 0) Gcap ≤ Gcap := min_le_right _ _
  have hA0 : (0 : ℝ) ≤ s * ((m.blockSize : ℝ) - 1) := mul_nonneg hs0 hB1
  obtain ⟨err, herr⟩ : ∃ err : ℝ, err = ((1 + 2 * s) * ((m.blockSize : ℝ) - 1
        - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
            ((b + 1) * m.blockSize - 1))
      + (1 + s)) * Gcap
    + s * ((m.blockSize : ℝ) - 1) * pen := ⟨_, rfl⟩
  rw [← herr]
  cases hlast : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) with
  | some xLast =>
    have hĜg : min (max G 0) Gcap - pen ≤ max (min Gcap (G - pen)) 0 := by
      have h1 : min (max G 0) Gcap ≤ max G 0 := min_le_left _ _
      rcases le_total 0 G with hG0 | hG0
      · have hmax : max G 0 = G := max_eq_left hG0
        have h2 : min (max G 0) Gcap - pen ≤ min Gcap (G - pen) :=
          le_min (by linarith) (by linarith)
        exact h2.trans (le_max_left _ _)
      · have hmax : max G 0 = 0 := max_eq_right hG0
        have h2 : min (max G 0) Gcap - pen ≤ 0 := by linarith
        exact h2.trans (le_max_right _ _)
    have hcount := le_card_newFrames_mul hs0 hslow hle hĜ0 hĜcap hpen0 hĜg
    rw [hsize] at hcount
    have hframe : ∀ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
        ((b + 1) * m.blockSize - 1),
        ENNReal.ofReal (max (min Gcap (G - pen)) 0)
          ≤ min (w.latencyAt (σ.plays w lookahead) r n) (ENNReal.ofReal Gcap) := by
      intro n hn
      refine le_min ?_ (ENNReal.ofReal_le_ofReal (max_le (min_le_left _ _) hcap))
      obtain ⟨l, hl, hlt⟩ := hB.room_le_latency hpos hlink hhost σ hstar lookahead hr hs0
        hslow hlast hpc0 hpr hpc hn
      rw [← hG, ← hpen] at hlt
      unfold World.latencyAt
      rw [hl]
      rcases le_total (min Gcap (G - pen)) 0 with hneg | hpos'
      · rw [max_eq_right hneg, ENNReal.ofReal_zero]
        exact bot_le
      · rw [max_eq_left hpos']
        exact ENNReal.ofReal_le_ofReal hlt
    have hsplit : s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap
        = (s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap - err) + err := by ring
    have hcount' : s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap - err
        ≤ ((newFrames (σ.plays w lookahead r) (b * m.blockSize)
          ((b + 1) * m.blockSize - 1)).card : ℝ) * max (min Gcap (G - pen)) 0 := by
      rw [herr]
      linarith
    calc ENNReal.ofReal (s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap)
        = ENNReal.ofReal ((s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap - err) + err) := by
          rw [← hsplit]
      _ ≤ ENNReal.ofReal (s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap - err)
          + ENNReal.ofReal err := ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal (((newFrames (σ.plays w lookahead r) (b * m.blockSize)
            ((b + 1) * m.blockSize - 1)).card : ℝ) * max (min Gcap (G - pen)) 0)
          + ENNReal.ofReal err := add_le_add (ENNReal.ofReal_le_ofReal hcount') le_rfl
      _ = ∑ _n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize)
            ((b + 1) * m.blockSize - 1), ENNReal.ofReal (max (min Gcap (G - pen)) 0)
          + ENNReal.ofReal err := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ _ := add_le_add (Finset.sum_le_sum hframe) le_rfl
  | none =>
    -- Nothing was played: no step breaks new ground, and the losses cover the bound.
    have hnone := eq_none_of_lastPlayed_none hlast
    have hcount : newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
        ((b + 1) * m.blockSize - 1) = 0 :=
      newGroundCount_of_none _ _ fun k hk => hnone k (by omega)
    have hbound : s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap ≤ err := by
      rw [herr, hcount]
      have h1 : s * ((m.blockSize : ℝ) - 1) * min (max G 0) Gcap
          ≤ s * ((m.blockSize : ℝ) - 1) * Gcap := mul_le_mul_of_nonneg_left hĜcap hA0
      have h2 : (0 : ℝ) ≤ ((m.blockSize : ℝ) - 1) * Gcap := mul_nonneg hB1 hcap
      have h3 : (0 : ℝ) ≤ s * (((m.blockSize : ℝ) - 1) * Gcap) := mul_nonneg hs0 h2
      have h4 : (0 : ℝ) ≤ (1 + s) * Gcap := mul_nonneg (by linarith) hcap
      have h5 : (0 : ℝ) ≤ s * ((m.blockSize : ℝ) - 1) * pen := mul_nonneg hA0 hpen0
      push_cast
      nlinarith
    exact (ENNReal.ofReal_le_ofReal hbound).trans le_add_self

/-- **The latency of one playback block against the room, with its losses
on the other side.** In the setting of `Builds.room_le_latency`, for every
playback block `b`, whether or not the speaker has played the source by
then. Let `G` be the least delay, plus the time from the request of block
`b + 1` to its first output sample, plus `pc` times the room before block
`b + 1` and `lookahead - 1` frames, minus `2 * pr` and `blockSize` times the
positive part of `pr - s * pc`. Let `Gcap ≥ 0` be the cap. Then
`s * (blockSize - 1)` times the smaller of `G` and `Gcap` (zero if `G` is
negative) is at most the latencies of the frames that the steps inside block
`b` pass on new ground, plus the losses of the block: `(1 + 2 s) * Gcap` for
each of those steps that does not break new ground, `(1 + s) * Gcap`, and
`s * (blockSize - 1) * pc` times: `s` for each step that is not continuous
and one for each missed sample of the block. -/
theorem Builds.le_sum_add_loss (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    (b : ℕ) {pc pr Gcap : ℝ} (hpc0 : 0 ≤ pc) (hcap : 0 ≤ Gcap)
    (hpr : ∀ k, b * m.blockSize ≤ k → k < (b + 1) * m.blockSize →
      (w.speaker r).out (k + 1) - (w.speaker r).out k ≤ pr)
    (hpc : ∀ i, (w.speaker r).out (b * m.blockSize) - Gcap < w.source.capture i →
      w.source.capture (i + 1) ≤ (w.speaker r).asked (b + 1) →
      pc ≤ w.source.capture (i + 1) - w.source.capture i) :
    ENNReal.ofReal
        (s * ((m.blockSize : ℝ) - 1)
          * min (max (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
              + ((w.speaker r).out ((b + 1) * m.blockSize) - (w.speaker r).asked (b + 1))
              + pc * (room m f d w lookahead (σ.plays w lookahead r) r (b + 1)
                + ((lookahead : ℕ) : ℝ) - 1)
              - 2 * pr
              - (m.blockSize : ℝ) * max (pr - s * pc) 0) 0) Gcap)
      ≤ ∑ n ∈ newFrames (σ.plays w lookahead r) (b * m.blockSize) ((b + 1) * m.blockSize - 1),
          w.latencyAt (σ.plays w lookahead) r n
        + ENNReal.ofReal
          (((1 + 2 * s) * ((m.blockSize : ℝ) - 1
                - newGroundCount (σ.plays w lookahead r) (b * m.blockSize)
                    ((b + 1) * m.blockSize - 1))
              + (1 + s)) * Gcap
            + s * ((m.blockSize : ℝ) - 1)
              * (pc * (s * (((m.blockSize : ℝ) - 1)
                    - ((continuousBefore (σ.plays w lookahead r)
                          ((b + 1) * m.blockSize - 1) : ℝ)
                      - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                  + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                    - missedBefore (σ.plays w lookahead r) (b * m.blockSize))))) :=
  (hB.le_sum_min_add_loss hpos hlink hhost σ hstar lookahead hr hs0 hslow b hpc0 hcap hpr
    hpc).trans (add_le_add (Finset.sum_le_sum fun _ _ => min_le_left _ _) le_rfl)

/-- **What paused time of the link costs, against the room of the world
without it.** Take two draws that differ by pauses of the link from the
sender to the host of speaker `r` from `θ₁` on: `d` without and `d'` with
paused time `X` that begins between `θ₁` and `θ₂`. Let the least delays of
`d'` be not negative and its paused times never decrease. Consider a
solution whose hosts exchange messages only with the sender, whose position
at speaker `r`, in the world with the paused time, advances by at least `s`
in every step of continuous playback, with `0 ≤ s ≤ 1`. Let `b` be a
playback block such that all earlier blocks are requested before `θ₁` plus
the least delay `δ`, and block `b` itself no earlier than `θ₂ + δ`, and let
playback block `β` be requested no later than `θ₁ + X + δ`. Then, in the
world with the paused time, `s` for each output sample from the first of
block `b` to `K`, in a playback block up to `β`, is at most the room before
block `b` in the world without it, or zero if that is negative, plus the
missed samples counted at those output samples, plus `s` times the
discontinuities counted there and one more. -/
theorem Builds.stall_le_room {w' : World H R} (hB : m.Builds f d w) (hB' : m.Builds f d' w')
    {θ₁ θ₂ : ℝ} {r : Fin R} (h : d.SameExceptLinkFrom d' m.sender (m.host r) θ₁)
    (hpos : ∀ i j, 0 ≤ d'.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d'.linkPaused i j)) (hhost : ∀ x, Monotone (d'.hostPaused x))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+)
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays w' lookahead r k = some x →
      σ.plays w' lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    (hθ : θ₁ ≤ θ₂) {β b K : ℕ} (hK : b * m.blockSize ≤ K) (hKβ : K / m.blockSize ≤ β)
    (hb : ∀ b' < b, (w.speaker r).asked b'
      < θ₁ + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    (hθb : θ₂ + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
      ≤ (w.speaker r).asked b)
    (hβ : (w.speaker r).asked β
      ≤ θ₁ + (d'.linkPaused m.sender (m.host r) θ₂ - d'.linkPaused m.sender (m.host r) θ₁)
        + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) :
    s * ((K : ℝ) + 1 - (b * m.blockSize : ℕ))
      ≤ max (room m f d w lookahead (σ.plays w lookahead r) r b) 0
        + ∑ k ∈ Finset.Ico (b * m.blockSize) (K + 1),
            (missedAt (σ.plays w' lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico (b * m.blockSize) K,
            (discontinuityAt (σ.plays w' lookahead r) k : ℝ) + 1) := by
  have hexc := hB.exists_le_handed ((w.speaker r).asked b
    - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
  have hc := w.le_handed_blockFrom hexc
  exact hB.stall_le_of_sameExcept hB' h hpos hlink hhost σ hstar lookahead hr hs0 hs1 hslow hθ
    hK hKβ hb (by linarith) hβ

end GenerativeWorld

end Unisono.Spec
