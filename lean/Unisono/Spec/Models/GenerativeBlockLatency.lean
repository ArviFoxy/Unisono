/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeStall
public import Unisono.Spec.NewGround

/-!
# The latency of the frames of one playback block, against the room

A solution through the sender can ride out a pause of the link only with the
frames that its host holds beyond the position that it plays: its *room*.
The room is paid for with latency. This file states that trade for one
playback block, in one outcome of any member of the generative model: the
clocks of the hosts and of the audio devices may wander.

Consider a world built from a draw, a solution whose hosts exchange messages
only with the sender, and a speaker whose host is not the sender's, whose
position advances by at least `s` in every step of continuous playback. Take
a playback block `b`, and let `c` be the first capture block that is handed
over no earlier than the least delay before the request of playback block
`b + 1`: only frames of capture blocks before `c` can have arrived by that
request. Because the clocks may wander, the theorem takes two bounds on the
audio devices near the block: `pr`, at least the time between two output
samples of block `b`, and `pc`, at most the time between two frames that are
captured in a window before the request of block `b + 1`. The window starts
a time `Gcap` before the first output sample of block `b` leaves.

**Theorem** (`Builds.block_le_latency`). Every frame that a step inside
playback block `b` passes on new ground is played with a latency of at least
the smaller of `Gcap` and the following: the least delay, plus the time from
the request of block `b + 1` to its first output sample, plus `pc` for each
frame from the position played last in blocks up to `b` to the last frame of
capture block `c - 1`, minus

* `2 * pr`,
* `blockSize` times the amount by which `pr` exceeds `s * pc`, when it does:
  within the block the position may fall behind the capture by that much per
  output sample,
* `s * pc` for each step inside the block that is not continuous, and `pc`
  for each missed sample counted in the block.

The cap `Gcap` is what lets the bound use the capture device only in a
window: a frame with a latency below `Gcap` was captured inside it.

So a large room at the end of a block means that the frames of the block
were played late. The statement holds in one outcome, for every solution
through the sender. It is not yet a bound on the cost.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

variable {plays : ℕ → Option ℝ}

/-- Between two output samples, the steps of continuous playback number at
most the steps. -/
theorem continuousBefore_le_add {k K : ℕ} (h : k ≤ K) :
    continuousBefore plays K ≤ continuousBefore plays k + (K - k) := by
  induction K, h using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    by_cases hc : PlaysContinuously plays K
    · rw [continuousBefore_succ_of hc]
      omega
    · rw [continuousBefore_succ_of_not hc]
      omega

/-- If each of the frames from `n` to `N - 1` is followed by the next one no
sooner than `pc` later, frame `N` is captured at least `pc * (N - n)` after
frame `n`. -/
theorem CaptureDevice.mul_le_capture_sub (dev : CaptureDevice) {pc : ℝ} {n N : ℕ}
    (hnN : n ≤ N) (hper : ∀ i, n ≤ i → i < N → pc ≤ dev.capture (i + 1) - dev.capture i) :
    pc * ((N : ℝ) - n) ≤ dev.capture N - dev.capture n := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have h1 := ih fun i hi hiN => hper i hi (Nat.lt_succ_of_lt hiN)
    have h2 := hper N hN (Nat.lt_succ_self N)
    push_cast
    linarith

/-- If each of the output samples from `j` to `K - 1` is followed by the
next one no later than `pr` later, output sample `K` leaves at most
`pr * (K - j)` after output sample `j`. -/
theorem PlaybackDevice.out_sub_le_mul (dev : PlaybackDevice) {pr : ℝ} {j K : ℕ}
    (hjK : j ≤ K) (hper : ∀ k, j ≤ k → k < K → dev.out (k + 1) - dev.out k ≤ pr) :
    dev.out K - dev.out j ≤ pr * ((K : ℝ) - j) := by
  induction K, hjK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    have h1 := ih fun k hk hkK => hper k hk (Nat.lt_succ_of_lt hkK)
    have h2 := hper K hK (Nat.lt_succ_self K)
    push_cast
    linarith

namespace GenerativeWorld

variable {H : Type} {R : ℕ} {Msg : Type} [DecidableEq H] {m : GenerativeWorld H R}
  {f : Member H R} {d : Draw H R} {w : World H R}

/-- **The frames of a playback block are played late by the room that is
left after it.** Consider a world built from a draw whose least delays are
not negative and whose paused times never decrease, a solution whose hosts
exchange messages only with the sender, and a speaker `r` whose host is not
the sender's, whose position advances by at least `s`, with `0 ≤ s`, in
every step of continuous playback. Let `xLast` be the position played last
before playback block `b + 1`, and let `c` be the first capture block that is
handed over no earlier than the least delay before the request of playback
block `b + 1`. Let `pr` be at least the time between two output samples of
block `b`, and let `0 ≤ pc` be at most the time from a frame to the next for
every frame that is captured later than `Gcap` before the first output
sample of block `b` leaves and whose next frame is captured by the request
of block `b + 1`. Then every frame that a step between two output samples of
playback block `b` passes on new ground is played with a latency of at least
the smaller of `Gcap` and: the least delay, plus the time from the request
of block `b + 1` to its first output sample, plus `pc` times
`c * blockSize - 1 - xLast`, minus `2 * pr`, minus `blockSize` times the
positive part of `pr - s * pc`, minus `pc` times: `s` for each step of the
block that is not continuous and one for each missed sample counted in the
block. -/
theorem Builds.block_le_latency (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {b c : ℕ} {xLast : ℝ}
    (hlast : lastPlayed (σ.plays w lookahead r) ((b + 1) * m.blockSize) = some xLast)
    (hcle : (w.speaker r).asked (b + 1)
        - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
      ≤ w.source.handed c)
    (hclt : ∀ c' < c, w.source.handed c'
      < (w.speaker r).asked (b + 1)
        - d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
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
            + pc * ((c : ℝ) * m.blockSize - 1 - xLast)
            - 2 * pr
            - (m.blockSize : ℝ) * max (pr - s * pc) 0
            - pc * (s * (((m.blockSize : ℝ) - 1)
                  - ((continuousBefore (σ.plays w lookahead r)
                        ((b + 1) * m.blockSize - 1) : ℝ)
                    - continuousBefore (σ.plays w lookahead r) (b * m.blockSize)))
                + ((missedBefore (σ.plays w lookahead r) ((b + 1) * m.blockSize) : ℝ)
                  - missedBefore (σ.plays w lookahead r) (b * m.blockSize))))
        ≤ l := by
  have hBpos := m.blockSize_pos
  have hδ := hpos m.sender (m.host r)
  -- The last output sample of the block.
  obtain ⟨K, hK⟩ : ∃ K, K + 1 = (b + 1) * m.blockSize :=
    ⟨(b + 1) * m.blockSize - 1, Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos b) hBpos)⟩
  have hKe : (b + 1) * m.blockSize - 1 = K := by omega
  have hbK : b * m.blockSize + m.blockSize = K + 1 := by
    rw [hK]
    ring
  rw [hKe] at hn ⊢
  rw [← hK] at hlast hpr ⊢
  -- The step that passes the frame.
  obtain ⟨j, haj, hjK, hng, hlo, hhi⟩ := exists_of_mem_newFrames _ _ n hn
  obtain ⟨x, y, hx, hy, h1, h2, h3⟩ := hng
  have hng : NewGround (σ.plays w lookahead r) j := ⟨x, y, hx, hy, h1, h2, h3⟩
  rw [hng.maxPlayed_eq hy] at hhi
  obtain ⟨l, hl, hle⟩ := w.le_latency_of_newGround (σ.plays w lookahead) hng hy hlo hhi
  refine ⟨l, hl, ?_⟩
  rcases le_or_gt Gcap l with hcapl | hcapl
  · exact (min_le_left _ _).trans hcapl
  refine (min_le_right _ _).trans ?_
  -- Output sample `j + 1` is in block `b`, so its position needs an arrival.
  have hjb : (j + 1) / m.blockSize = b := by
    refine Nat.div_eq_of_lt_le (by omega) ?_
    rw [← hK]
    omega
  obtain ⟨hy0, -⟩ := hB.arrival_lt_of_plays hpos hlink hhost σ hstar lookahead hr hy
  have harr := hB.le_arrival m.sender (m.host r) (w.source.handed c)
  have hyc := hB.le_of_plays_before hpos hlink hhost σ hstar lookahead hr (c := c)
    (β := b + 1) (by linarith) (by rw [hjb]; exact Nat.le_succ b) hy
  have hla : (1 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := by
    have h1 : 1 ≤ (lookahead : ℕ) := lookahead.pos
    exact_mod_cast h1
  -- Some capture block was handed over before: `c` is not zero.
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0
      push_cast at hyc
      linarith
    · exact h0
  obtain ⟨N, hN⟩ : ∃ N, N + 1 = c * m.blockSize :=
    ⟨c * m.blockSize - 1, Nat.sub_add_cancel (Nat.mul_pos hcpos hBpos)⟩
  have hNR : (N : ℝ) + 1 = (c : ℝ) * m.blockSize := by exact_mod_cast hN
  obtain ⟨c', hcc⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hhand : w.source.handed c' = w.source.capture N := by
    rw [hB.capture_handed, hB.capture_first]
    congr 1
    rw [← hcc]
    omega
  have hNlt := hclt c' (by omega)
  rw [hhand] at hNlt
  -- The frame is at or before the last frame of that capture block.
  have hnN : n ≤ N := by
    have h4 : ((n : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by linarith
    exact_mod_cast h4
  -- The frame was captured inside the window.
  have houtj : (w.speaker r).out (b * m.blockSize) ≤ (w.speaker r).out j :=
    (w.speaker r).out_strictMono.monotone haj
  have hcapn : (w.speaker r).out (b * m.blockSize) - Gcap < w.source.capture n := by
    linarith
  have hcap := w.source.mul_le_capture_sub hnN fun i hi hiN => by
    refine hpc i ?_ ?_
    · exact lt_of_lt_of_le hcapn (w.source.capture_strictMono.monotone hi)
    · have := w.source.capture_strictMono.monotone (show i + 1 ≤ N from hiN)
      linarith
  have hout := (w.speaker r).out_sub_le_mul (show j ≤ K + 1 by omega) fun k hk hkK =>
    hpr k (haj.trans hk) hkK
  push_cast at hout
  -- The position played last advances from the step to the end of the block.
  have hadv := add_le_lastPlayed hslow (lastPlayed_succ_some hy) K (Nat.succ_le_of_lt hjK)
    xLast hlast
  have hcont₁ := continuousBefore_le_add (plays := σ.plays w lookahead r)
    (show b * m.blockSize ≤ j + 1 by omega)
  have hcont₂ := continuousBefore_le_add (plays := σ.plays w lookahead r)
    (show b * m.blockSize ≤ K by omega)
  have hmiss := missedBefore_mono (σ.plays w lookahead r)
    (show b * m.blockSize ≤ j + 1 + 1 by omega)
  have hcont₁' : (continuousBefore (σ.plays w lookahead r) (j + 1) : ℝ)
      ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
        + ((j : ℝ) + 1 - (b * m.blockSize : ℕ)) := by
    have e : ((j + 1 - b * m.blockSize : ℕ) : ℝ) = (j : ℝ) + 1 - (b * m.blockSize : ℕ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have h' : (continuousBefore (σ.plays w lookahead r) (j + 1) : ℝ)
        ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
          + ((j + 1 - b * m.blockSize : ℕ) : ℝ) := by exact_mod_cast hcont₁
    rw [e] at h'
    exact h'
  have hcont₂' : (continuousBefore (σ.plays w lookahead r) K : ℝ)
      ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
        + ((m.blockSize : ℝ) - 1) := by
    have e : ((K - b * m.blockSize : ℕ) : ℝ) = (m.blockSize : ℝ) - 1 := by
      have h4 : K - b * m.blockSize + 1 = m.blockSize := by omega
      have h5 : ((K - b * m.blockSize : ℕ) : ℝ) + 1 = (m.blockSize : ℝ) := by
        exact_mod_cast h4
      linarith
    have h' : (continuousBefore (σ.plays w lookahead r) K : ℝ)
        ≤ continuousBefore (σ.plays w lookahead r) (b * m.blockSize)
          + ((K - b * m.blockSize : ℕ) : ℝ) := by exact_mod_cast hcont₂
    rw [e] at h'
    exact h'
  have hmiss' : (missedBefore (σ.plays w lookahead r) (b * m.blockSize) : ℝ)
      ≤ missedBefore (σ.plays w lookahead r) (j + 1 + 1) := by exact_mod_cast hmiss
  -- Sizes within the block.
  have hjR : (j : ℝ) + 1 ≤ K := by exact_mod_cast Nat.succ_le_of_lt hjK
  have hKB : (K : ℝ) + 1 = (b * m.blockSize : ℕ) + (m.blockSize : ℝ) := by
    have : ((b * m.blockSize + m.blockSize : ℕ) : ℝ) = ((K + 1 : ℕ) : ℝ) := by
      rw [hbK]
    push_cast at this ⊢
    linarith
  have hajR : ((b * m.blockSize : ℕ) : ℝ) ≤ j := by exact_mod_cast haj
  -- The drift of the position against the capture within the block.
  have hdrift : ((K : ℝ) - j - 1) * (pr - s * pc)
      ≤ (m.blockSize : ℝ) * max (pr - s * pc) 0 := by
    have h0 : 0 ≤ (K : ℝ) - j - 1 := by linarith
    have hBle : (K : ℝ) - j - 1 ≤ m.blockSize := by linarith
    calc ((K : ℝ) - j - 1) * (pr - s * pc)
        ≤ ((K : ℝ) - j - 1) * max (pr - s * pc) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) h0
      _ ≤ (m.blockSize : ℝ) * max (pr - s * pc) 0 :=
          mul_le_mul_of_nonneg_right hBle (le_max_right _ _)
  -- How many frames lie between the frame and the last frame of the capture block.
  have hcontStep : s * ((K : ℝ) - j - 1 - (((m.blockSize : ℝ) - 1)
        - ((continuousBefore (σ.plays w lookahead r) K : ℝ)
          - continuousBefore (σ.plays w lookahead r) (b * m.blockSize))))
      ≤ s * ((continuousBefore (σ.plays w lookahead r) K : ℝ)
        - continuousBefore (σ.plays w lookahead r) (j + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hs0
  have hframes : ((c : ℝ) * m.blockSize - 1 - xLast)
        + s * ((K : ℝ) - j - 1 - (((m.blockSize : ℝ) - 1)
          - ((continuousBefore (σ.plays w lookahead r) K : ℝ)
            - continuousBefore (σ.plays w lookahead r) (b * m.blockSize))))
        - ((missedBefore (σ.plays w lookahead r) (K + 1) : ℝ)
          - missedBefore (σ.plays w lookahead r) (b * m.blockSize))
      ≤ (N : ℝ) - n := by
    linarith
  have hcapture := mul_le_mul_of_nonneg_left hframes hpc0
  linarith

end GenerativeWorld

end Unisono.Spec
