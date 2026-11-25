/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeStall
public import Unisono.Spec.Models.GenerativePauses
public import Unisono.Spec.Causality

/-!
# One pause of the link from the sender

A pause of length `X` of the link from host `i` to host `j` begins at true
time `θ` when the paused time of the link at `θ` exceeds its value at every
earlier time by at least `X`. This file proves two things about such a
pause, in one outcome. Neither needs the link or a host to be idle when the
pause begins.

**After the pause begins, nothing sent arrives before it ends.** Every
message that host `i` sends to host `j` at or after `θ` arrives at or after
`θ + X` plus the least delay of the direction (`Builds.arrival_ge_of_pause`).
For a solution whose hosts exchange messages only with the sender, the
output samples of a speaker that are requested until then can play only
positions that need capture blocks handed over before `θ`, so they cost
missed samples and discontinuities as `Builds.stall_le` says
(`Builds.stall_le_of_pause`).

**Before the pause can be noticed, every solution plays the same with and
without it.** Take two draws with steady clocks that differ only in the
paused time of the link from `i` to `j`, and only from true time `θ` on
(`Draw.SameExceptLinkFrom`). Their worlds deliver every message at the same
time, or both at or after `θ` plus the least delay of the direction
(`drawWorld_deliversSameBefore`). So every solution plays the same in both
at every output sample of every playback block that is requested before
that time (`drawWorld_plays_eq`), and the position that it played last
before such a block is the same (`drawWorld_lastPlayed_eq`).

Together (`drawWorld_stall_le_of_pause`): what the output samples of the
window cost in the world with the pause is bounded from below with the room
that the solution had in the world without it. The world without the pause
does not depend on whether the pause occurs. This is what lets a bound on
expected cost use that a pause begins independently of what was played
before. No such bound is proved here.
-/

@[expose] public noncomputable section

namespace Unisono.Spec

/-- The position played last before output sample `K` depends only on what
is played before `K`. -/
theorem lastPlayed_congr {p q : ℕ → Option ℝ} :
    ∀ {K : ℕ}, (∀ k < K, p k = q k) → lastPlayed p K = lastPlayed q K
  | 0, _ => rfl
  | K + 1, h => by
    have hK := h K (Nat.lt_succ_self K)
    have ih := lastPlayed_congr (K := K) fun k hk => h k (Nat.lt_succ_of_lt hk)
    simp only [lastPlayed]
    rw [hK, ih]

namespace GenerativeWorld

variable {H : Type} {R : ℕ} {Msg : Type} {m : GenerativeWorld H R} {f : Member H R}
  {d d' : Draw H R} {w : World H R}

/-! ## Arrivals after a pause begins -/

/-- **A pause adds its length to the backlog.** Suppose that the paused time
never decreases and that a pause of length at least `X` begins at `θ`. Then
the backlog `v` at a true time `e` at or after `θ` is worked off at or after
`θ + X`. -/
theorem IsBacklog.pause_le {paused : Time → ℝ} (hmono : Monotone paused) {θ X e v : ℝ}
    (hjump : ∀ s < θ, X ≤ paused θ - paused s) (he : θ ≤ e) (h : IsBacklog paused e v) :
    θ + X ≤ e + v := by
  have hv : ∀ ε : ℝ, 0 < ε → X - (e - θ) ≤ v + ε := by
    intro ε hε
    have h1 := h.1 ⟨θ - ε, by linarith, rfl⟩
    have h2 := hjump (θ - ε) (by linarith)
    have h3 := hmono he
    linarith
  have h4 := le_of_forall_pos_le_add hv
  linarith

/-- **After a pause of a link begins, nothing sent arrives before it ends.**
In a world built from a draw, suppose that the paused time of the link from
`i` to `j` never decreases and that a pause of length at least `X` of that
link begins at `θ`. Then every message that `i` sends to `j` at or after `θ`
arrives at or after `θ + X` plus the least delay of the direction. -/
theorem Builds.arrival_ge_of_pause (hB : m.Builds f d w) {i j : H}
    (hlink : Monotone (d.linkPaused i j)) {θ X : ℝ}
    (hjump : ∀ s < θ, X ≤ d.linkPaused i j θ - d.linkPaused i j s) {s : Time} (hs : θ ≤ s) :
    θ + X + d.split i j * f.roundTrip i j ≤ d.arrival f i j s := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, he⟩ := hB.arrival_eq i j s
  have h1 := hv₁.nonneg
  have h3 := hv₃.nonneg
  have h2 := hv₂.pause_le hlink hjump (by linarith)
  rw [he]
  linarith

section Stall

variable [DecidableEq H]

/-- **What every solution through the sender pays during a pause of the link
to a speaker's host.** Consider a world built from a draw whose least delays
are not negative and whose paused times never decrease, a solution whose
hosts exchange messages only with the sender, and a speaker whose host is
not the sender's, whose position advances by at least `s` in every step of
continuous playback, with `0 ≤ s ≤ 1`. Suppose that a pause of length at
least `X` of the link from the sender to the speaker's host begins at `θ`,
that capture block `c` is handed over at or after `θ`, and that playback
block `β` is requested no later than `θ + X` plus the least delay. Then for
output samples `k₀ ≤ K` with `K` in a playback block up to `β`: `s` for each
output sample from `k₀` to `K` is at most the room from the position played
last before `k₀` to `c * blockSize - lookahead`, plus the missed samples
counted from `k₀` to `K`, plus `s` times the discontinuities counted from
`k₀` to `K - 1` and one more. -/
theorem Builds.stall_le_of_pause (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {θ X : ℝ}
    (hjump : ∀ t < θ, X ≤ d.linkPaused m.sender (m.host r) θ
      - d.linkPaused m.sender (m.host r) t)
    {c β k₀ K : ℕ} (hK : k₀ ≤ K) (hKβ : K / m.blockSize ≤ β)
    (hc : θ ≤ w.source.handed c)
    (hβ : (w.speaker r).asked β
      ≤ θ + X + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) :
    s * ((K : ℝ) + 1 - k₀)
      ≤ max ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
        + ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt (σ.plays w lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt (σ.plays w lookahead r) k : ℝ)
          + 1) :=
  hB.stall_le hpos hlink hhost σ hstar lookahead hr hs0 hs1 hslow hK hKβ
    (hβ.trans (hB.arrival_ge_of_pause (hlink m.sender (m.host r)) hjump hc))

end Stall

/-! ## Two draws that differ by pauses of one link from a true time on -/

/-- The draws `d` and `d'` differ only in the paused time of the link from
`i₀` to `j₀`, and only from true time `θ` on: the splits, the offsets and
rates of all clocks, the paused times of all hosts and of all other links
are the same, and the paused time of that link is the same before `θ`. -/
structure Draw.SameExceptLinkFrom (d d' : Draw H R) (i₀ j₀ : H) (θ : Time) : Prop where
  split : d'.split = d.split
  offset : d'.offset = d.offset
  logRate : d'.logRate = d.logRate
  deviceLogRate : d'.deviceLogRate = d.deviceLogRate
  hostPaused : d'.hostPaused = d.hostPaused
  linkPaused : ∀ i j, (i, j) ≠ (i₀, j₀) → d'.linkPaused i j = d.linkPaused i j
  before : ∀ t < θ, d'.linkPaused i₀ j₀ t = d.linkPaused i₀ j₀ t

/-- The backlog at a true time before `θ` depends only on the paused time
before `θ`. -/
theorem backlog_eq_of_agree {p p' : Time → ℝ} {θ e : Time} (h : ∀ t < θ, p' t = p t)
    (he : e < θ) : backlog p' e = backlog p e := by
  unfold backlog
  congr 1
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by rw [h e he, h s (lt_of_le_of_lt hs he)]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by rw [h e he, h s (lt_of_le_of_lt hs he)]⟩

/-- **Two draws that differ by pauses of one link from `θ` on deliver the
same before the difference can arrive.** In worlds built from the two draws,
every message arrives at the same time in both, or in both at or after `θ`
plus the least delay of the direction of that link. -/
theorem arrival_of_sameExceptLinkFrom {i₀ j₀ : H} {θ : Time} {w' : World H R}
    (h : d.SameExceptLinkFrom d' i₀ j₀ θ) (hB : m.Builds f d w) (hB' : m.Builds f d' w')
    (i j : H) (s : Time) :
    d'.arrival f i j s = d.arrival f i j s
      ∨ (θ + d.split i₀ j₀ * f.roundTrip i₀ j₀ ≤ d.arrival f i j s
        ∧ θ + d.split i₀ j₀ * f.roundTrip i₀ j₀ ≤ d'.arrival f i j s) := by
  by_cases hij : (i, j) = (i₀, j₀)
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hij
    by_cases he : s + backlog (d.hostPaused i) s < θ
    · left
      unfold Draw.arrival
      rw [h.split, h.hostPaused, backlog_eq_of_agree h.before he]
    · right
      have he' := not_lt.mp he
      obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, hea⟩ := hB.arrival_eq i j s
      obtain ⟨v₁', v₂', v₃', hv₁', hv₂', hv₃', hea'⟩ := hB'.arrival_eq i j s
      have e₁ := hv₁.backlog_eq
      have e₁' := hv₁'.backlog_eq
      rw [h.hostPaused] at e₁'
      have h2 := hv₂.nonneg
      have h3 := hv₃.nonneg
      have h2' := hv₂'.nonneg
      have h3' := hv₃'.nonneg
      have hsplit : d'.split i j = d.split i j := by rw [h.split]
      rw [hea, hea', hsplit]
      constructor <;> linarith
  · left
    unfold Draw.arrival
    rw [h.split, h.hostPaused, h.linkPaused i j hij]

/-! ## The worlds of the two draws -/

section Worlds

variable [DecidableEq H] {hex : ∀ h, h = m.sender ∨ ∃ r, m.host r = h} {i₀ j₀ : H} {θ : Time}

omit [DecidableEq H] in
/-- The worlds of two draws with steady clocks that differ by pauses of one
link from `θ` on deliver every message at the same time, or both at or after
`θ` plus the least delay of the direction of that link. -/
theorem drawWorld_deliversSameBefore (hd : d.Steady) (hd' : d'.Steady)
    (h : d.SameExceptLinkFrom d' i₀ j₀ θ) :
    World.DeliversSameBefore (θ + d.split i₀ j₀ * f.roundTrip i₀ j₀)
      (drawWorld m f hex d hd) (drawWorld m f hex d' hd') := by
  intro i j t q
  rcases arrival_of_sameExceptLinkFrom h (drawWorld_builds m f hex d hd)
    (drawWorld_builds m f hex d' hd') i j t with he | ⟨h1, h2⟩
  · left
    show some (d.arrival f i j t) = some (d'.arrival f i j t)
    rw [he]
  · right
    exact ⟨_, _, rfl, rfl, h1, h2⟩

/-- **Before a pause can be noticed, every solution plays the same with and
without it.** In the worlds of two draws with steady clocks that differ by
pauses of one link from `θ` on, every solution plays the same at every
output sample of every playback block that is requested before `θ` plus the
least delay of the direction of that link. -/
theorem drawWorld_plays_eq (hd : d.Steady) (hd' : d'.Steady)
    (h : d.SameExceptLinkFrom d' i₀ j₀ θ) (σ : Solution H R Msg) (lookahead : ℕ+) {r : Fin R}
    {b k : ℕ}
    (hb : ((drawWorld m f hex d hd).speaker r).asked b
      < θ + d.split i₀ j₀ * f.roundTrip i₀ j₀)
    (hk : k ∈ ((drawWorld m f hex d hd).speaker r).block b) :
    σ.plays (drawWorld m f hex d' hd') lookahead r k
      = σ.plays (drawWorld m f hex d hd) lookahead r k := by
  refine σ.plays_eq_of_sameBefore (w₁ := drawWorld m f hex d hd)
    (w₂ := drawWorld m f hex d' hd') rfl rfl ?_ ?_ ?_ rfl
    (drawWorld_deliversSameBefore hd hd' h) lookahead hb hk
  · unfold drawWorld
    simp only [h.offset, h.logRate]
  · unfold drawWorld
    simp only [h.offset, h.logRate, h.deviceLogRate]
  · unfold drawWorld
    simp only [h.offset, h.logRate, h.deviceLogRate]

/-- The position that a solution played last before a playback block that is
requested before `θ` plus the least delay is the same in the worlds of two
draws that differ by pauses of one link from `θ` on. -/
theorem drawWorld_lastPlayed_eq (hd : d.Steady) (hd' : d'.Steady)
    (h : d.SameExceptLinkFrom d' i₀ j₀ θ) (σ : Solution H R Msg) (lookahead : ℕ+) {r : Fin R}
    {b : ℕ}
    (hb : ∀ b' < b, ((drawWorld m f hex d hd).speaker r).asked b'
      < θ + d.split i₀ j₀ * f.roundTrip i₀ j₀) :
    lastPlayed (σ.plays (drawWorld m f hex d' hd') lookahead r) (b * m.blockSize)
      = lastPlayed (σ.plays (drawWorld m f hex d hd) lookahead r) (b * m.blockSize) := by
  refine lastPlayed_congr fun k hk => ?_
  have hlt : k / m.blockSize < b := (Nat.div_lt_iff_lt_mul m.blockSize_pos).mpr hk
  refine drawWorld_plays_eq hd hd' h σ lookahead (hb _ hlt) ?_
  show k ∈ List.range' ((k / m.blockSize) * m.blockSize)
    ((k / m.blockSize + 1) * m.blockSize - (k / m.blockSize) * m.blockSize)
  rw [List.mem_range'_1]
  have h1 := Nat.div_mul_le_self k m.blockSize
  have h2 := Nat.lt_div_mul_add (a := k) m.blockSize_pos
  have e : (k / m.blockSize + 1) * m.blockSize = k / m.blockSize * m.blockSize + m.blockSize := by
    ring
  rw [e]
  omega

/-- **What a pause costs, with the room of the world without it.** Take two
draws with steady clocks that differ by pauses of the link from the sender to
the host of speaker `r` from `θ` on: `d` without and `d'` with a pause of
length at least `X` that begins at `θ`. Consider a solution whose hosts
exchange messages only with the sender, whose position at speaker `r`, in
the world with the pause, advances by at least `s` in every step of
continuous playback, with `0 ≤ s ≤ 1`. Let playback block `b` be one whose
earlier blocks are all requested before `θ` plus the least delay `δ`, let
capture block `c` be handed over at or after `θ`, and let playback block `β`
be requested no later than `θ + X + δ`. Then, in the world with the pause,
`s` for each output sample from the first of block `b` to `K`, in a playback
block up to `β`, is at most the room from the position played last before
block `b` in the world without the pause to `c * blockSize - lookahead`,
plus the missed samples counted at those output samples, plus `s` times the
discontinuities counted there and one more. -/
theorem drawWorld_stall_le_of_pause (hd : d.Steady) (hd' : d'.Steady) {r : Fin R}
    (h : d.SameExceptLinkFrom d' m.sender (m.host r) θ) (σ : Solution H R Msg)
    (hstar : σ.IsStar m.sender) (lookahead : ℕ+) (hr : m.host r ≠ m.sender) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays (drawWorld m f hex d' hd') lookahead r k = some x →
      σ.plays (drawWorld m f hex d' hd') lookahead r (k + 1) = some y → x < y → y < x + 2 →
      x + s ≤ y)
    {X : ℝ}
    (hjump : ∀ t < θ, X ≤ d'.linkPaused m.sender (m.host r) θ
      - d'.linkPaused m.sender (m.host r) t)
    {c β b K : ℕ} (hK : b * m.blockSize ≤ K) (hKβ : K / m.blockSize ≤ β)
    (hb : ∀ b' < b, ((drawWorld m f hex d hd).speaker r).asked b'
      < θ + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    (hc : θ ≤ (drawWorld m f hex d hd).source.handed c)
    (hβ : ((drawWorld m f hex d hd).speaker r).asked β
      ≤ θ + X + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) :
    s * ((K : ℝ) + 1 - (b * m.blockSize : ℕ))
      ≤ max ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays (drawWorld m f hex d hd) lookahead r)
              (b * m.blockSize)).getD 0) 0
        + ∑ k ∈ Finset.Ico (b * m.blockSize) (K + 1),
            (missedAt (σ.plays (drawWorld m f hex d' hd') lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico (b * m.blockSize) K,
            (discontinuityAt (σ.plays (drawWorld m f hex d' hd') lookahead r) k : ℝ) + 1) := by
  have hsplit : d'.split m.sender (m.host r) = d.split m.sender (m.host r) := by rw [h.split]
  have hsrc : (drawWorld m f hex d' hd').source = (drawWorld m f hex d hd).source := by
    unfold drawWorld
    simp only [h.offset, h.logRate, h.deviceLogRate]
  have hspk : (drawWorld m f hex d' hd').speaker = (drawWorld m f hex d hd).speaker := by
    unfold drawWorld
    simp only [h.offset, h.logRate, h.deviceLogRate]
  have hmain := (drawWorld_builds m f hex d' hd').stall_le_of_pause
    (fun i j => mul_nonneg (hd'.split_mem i j).1.le (f.roundTrip_pos i j).le)
    hd'.linkPaused_monotone hd'.hostPaused_monotone σ hstar lookahead hr hs0 hs1 hslow hjump
    hK hKβ (c := c) (by rw [hsrc]; exact hc) (by rw [hspk, hsplit]; exact hβ)
  rw [drawWorld_lastPlayed_eq hd hd' h σ lookahead hb] at hmain
  exact hmain

end Worlds

end GenerativeWorld

end Unisono.Spec
