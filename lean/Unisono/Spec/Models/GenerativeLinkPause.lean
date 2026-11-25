/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Spec.Models.GenerativeStall
public import Unisono.Spec.Models.GenerativeTransfer
public import Unisono.Spec.Causality

/-!
# Paused time of the link from the sender that begins in a short interval

Take two true times `θ₁ ≤ θ₂` and the paused time of the link from host `i`
to host `j` that begins between them: the paused time at `θ₂` minus the
paused time at `θ₁`. This file proves two things about it, in one outcome,
for every member of the generative model: the clocks may wander, the
timestamps may have errors, and the link and the hosts may have backlogs
when the interval begins.

**Nothing sent after the interval arrives before the paused time is worked
off.** Every message that host `i` sends to host `j` at or after `θ₂`
arrives at or after `θ₁`, plus the paused time that began in the interval,
plus the least delay of the direction (`Builds.arrival_ge_of_paused`). For a
solution whose hosts exchange messages only with the sender, the output
samples of a speaker that are requested until then can play only positions
that need capture blocks handed over before `θ₂`, so they cost missed
samples and discontinuities as `Builds.stall_le` says
(`Builds.stall_le_of_paused`).

**Before the difference can arrive, every solution plays the same with and
without it.** Take two draws that differ only in the paused time of the link
from `i` to `j`, and only from true time `θ` on (`Draw.SameExceptLinkFrom`).
Worlds built from them have the same hosts, clocks, audio devices and target
latencies (`Builds.same_devices`), and deliver every message at the same
time, or both at or after `θ` plus the least delay of the direction
(`Builds.deliversSameBefore`). So every solution plays the same in both at
every output sample of every playback block that is requested before that
time (`Builds.plays_eq_of_sameExcept`), and the position that it played last
before such a block is the same (`Builds.lastPlayed_eq`).

Together (`Builds.stall_le_of_sameExcept`): what the output samples of the
window cost in the world with the paused time is bounded from below with the
room that the solution had in the world without it. The world without it
does not depend on whether a pause begins in the interval. This is what lets
a bound on expected cost use that pauses begin independently of what was
played before. No such bound is proved here.
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

/-! ## Arrivals after paused time has begun -/

/-- **Paused time that has begun is in the backlog until it is worked off.**
Suppose that the paused time never decreases. The backlog `v` at a true time
`e` at or after `θ₂` is worked off at or after `θ₁` plus the paused time that
began between `θ₁` and `θ₂`. -/
theorem IsBacklog.increment_le {paused : Time → ℝ} (hmono : Monotone paused) {θ₁ θ₂ e v : ℝ}
    (hθ : θ₁ ≤ θ₂) (he : θ₂ ≤ e) (h : IsBacklog paused e v) :
    θ₁ + (paused θ₂ - paused θ₁) ≤ e + v := by
  have h1 := h.1 ⟨θ₁, hθ.trans he, rfl⟩
  have h2 := hmono he
  linarith

/-- **Nothing sent after paused time of a link has begun arrives before it
is worked off.** In a world built from a draw, suppose that the paused time
of the link from `i` to `j` never decreases. Then every message that `i`
sends to `j` at or after `θ₂` arrives at or after `θ₁`, plus the paused time
of the link that began between `θ₁` and `θ₂`, plus the least delay of the
direction. -/
theorem Builds.arrival_ge_of_paused (hB : m.Builds f d w) {i j : H}
    (hlink : Monotone (d.linkPaused i j)) {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂) {s : Time}
    (hs : θ₂ ≤ s) :
    θ₁ + (d.linkPaused i j θ₂ - d.linkPaused i j θ₁) + d.split i j * f.roundTrip i j
      ≤ d.arrival f i j s := by
  obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, he⟩ := hB.arrival_eq i j s
  have h1 := hv₁.nonneg
  have h3 := hv₃.nonneg
  have h2 := hv₂.increment_le hlink hθ (by linarith)
  rw [he]
  linarith

section Stall

variable [DecidableEq H]

/-- **What every solution through the sender pays while paused time of the
link to a speaker's host is worked off.** Consider a world built from a draw
whose least delays are not negative and whose paused times never decrease, a
solution whose hosts exchange messages only with the sender, and a speaker
whose host is not the sender's, whose position advances by at least `s` in
every step of continuous playback, with `0 ≤ s ≤ 1`. Let `X` be the paused
time of the link from the sender to the speaker's host that begins between
`θ₁` and `θ₂`. Suppose that capture block `c` is handed over at or after
`θ₂`, and that playback block `β` is requested no later than `θ₁ + X` plus
the least delay. Then for output samples `k₀ ≤ K` with `K` in a playback
block up to `β`: `s` for each output sample from `k₀` to `K` is at most the
room from the position played last before `k₀` to
`c * blockSize - lookahead`, plus the missed samples counted from `k₀` to
`K`, plus `s` times the discontinuities counted from `k₀` to `K - 1` and one
more. -/
theorem Builds.stall_le_of_paused (hB : m.Builds f d w)
    (hpos : ∀ i j, 0 ≤ d.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d.linkPaused i j)) (hhost : ∀ h, Monotone (d.hostPaused h))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+) {r : Fin R}
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays w lookahead r k = some x →
      σ.plays w lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂) {c β k₀ K : ℕ} (hK : k₀ ≤ K) (hKβ : K / m.blockSize ≤ β)
    (hc : θ₂ ≤ w.source.handed c)
    (hβ : (w.speaker r).asked β
      ≤ θ₁ + (d.linkPaused m.sender (m.host r) θ₂ - d.linkPaused m.sender (m.host r) θ₁)
        + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) :
    s * ((K : ℝ) + 1 - k₀)
      ≤ max ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays w lookahead r) k₀).getD 0) 0
        + ∑ k ∈ Finset.Ico k₀ (K + 1), (missedAt (σ.plays w lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico k₀ K, (discontinuityAt (σ.plays w lookahead r) k : ℝ)
          + 1) :=
  hB.stall_le hpos hlink hhost σ hstar lookahead hr hs0 hs1 hslow hK hKβ
    (hβ.trans (hB.arrival_ge_of_paused (hlink m.sender (m.host r)) hθ hc))

end Stall

/-! ## Two draws that differ by pauses of one link from a true time on -/

/-- The draws `d` and `d'` differ only in the paused time of the link from
`i₀` to `j₀`, and only from true time `θ` on: the splits, the clocks of the
hosts and of the audio devices, the errors of the reported timestamps, the
paused times of all hosts and of all other links are the same, and the
paused time of that link is the same before `θ`. -/
structure Draw.SameExceptLinkFrom (d d' : Draw H R) (i₀ j₀ : H) (θ : Time) : Prop where
  split : d'.split = d.split
  offset : d'.offset = d.offset
  logRate : d'.logRate = d.logRate
  wander : d'.wander = d.wander
  deviceLogRate : d'.deviceLogRate = d.deviceLogRate
  deviceWander : d'.deviceWander = d.deviceWander
  reportError : d'.reportError = d.reportError
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

/-! ## The worlds built from the two draws -/

/-- **The clocks and the pauses of the hosts of a draw determine the hosts,
clocks, audio devices and target latencies of the world built from it.** Two
worlds built from draws with the same offsets, rates and wander of all
clocks, the same errors of the reported timestamps and the same paused times
of the hosts have the same sender, hosts, clocks, capture device, playback
devices and target latencies. They can differ only in when messages arrive.
The paused times of the hosts matter because a host handles the events of
its audio devices after its backlog. -/
theorem Builds.same_devices {w' : World H R} (h : m.Builds f d w) (h' : m.Builds f d' w')
    (hoffset : d'.offset = d.offset) (hlogRate : d'.logRate = d.logRate)
    (hwander : d'.wander = d.wander) (hdevlog : d'.deviceLogRate = d.deviceLogRate)
    (hdevwander : d'.deviceWander = d.deviceWander) (herr : d'.reportError = d.reportError)
    (hhostp : d'.hostPaused = d.hostPaused) :
    w'.sender = w.sender ∧ w'.host = w.host ∧ w'.clock = w.clock ∧ w'.source = w.source
      ∧ w'.speaker = w.speaker ∧ w'.target = w.target := by
  have hread : ∀ x t, d'.reading x t = d.reading x t := by
    intro x t
    unfold Draw.reading
    rw [hoffset, hlogRate, hwander]
  have hdev : ∀ x t, d'.deviceReading x t = d.deviceReading x t := by
    intro x t
    unfold Draw.deviceReading
    rw [hdevlog, hdevwander]
  have hsender : w'.sender = w.sender := h'.sender_eq.trans h.sender_eq.symm
  have hhost : w'.host = w.host := h'.host_eq.trans h.host_eq.symm
  have hclock : w'.clock = w.clock :=
    funext fun x => Clock.ext_read fun t =>
      (h'.clock x t).trans ((hread x t).trans (h.clock x t).symm)
  have hinj : ∀ x, Function.Injective (w.clock x).read := fun x =>
    (w.clock x).strictMono.injective
  have hdinj : ∀ x, Function.Injective (d.deviceReading x) := fun x => by
    obtain ⟨c, hc⟩ := h.deviceClock x
    have heq : d.deviceReading x = c.read := funext fun t => (hc t).symm
    rw [heq]
    exact c.strictMono.injective
  refine ⟨hsender, hhost, hclock, ?_, ?_, ?_⟩
  · have hcap0 : w'.source.capture 0 = w.source.capture 0 := by
      apply hinj w.sender
      have h2 := h'.capture_start
      rw [hsender, hclock] at h2
      rw [h2, h.capture_start]
    have hcap : ∀ n, w'.source.capture n = w.source.capture n := fun n => by
      apply hdinj none
      have h1 := h.capture n
      have h2 := h'.capture n
      rw [hdev none (w'.source.capture n), hdev none (w'.source.capture 0), hcap0] at h2
      linarith
    have hfirst : ∀ b, w'.source.first b = w.source.first b := fun b =>
      (h'.capture_first b).trans (h.capture_first b).symm
    refine CaptureDevice.ext_fields hcap hfirst (fun b => ?_) (fun b => ?_)
    · obtain ⟨v, hv, e⟩ := h.capture_handed b
      obtain ⟨v', hv', e'⟩ := h'.capture_handed b
      rw [hhostp, hsender, hfirst, hcap] at hv'
      rw [e', e, hv'.unique hv, hfirst, hcap]
    · rw [h'.capture_reported, h.capture_reported, hfirst, hcap, hsender, hclock, herr]
  · funext r
    have hout0 : (w'.speaker r).out 0 = (w.speaker r).out 0 := by
      apply hinj (w.host r)
      have h2 := h'.speaker_start r
      rw [hhost, hclock] at h2
      rw [h2, h.speaker_start r]
    have hout : ∀ k, (w'.speaker r).out k = (w.speaker r).out k := fun k => by
      apply hdinj (some (m.device r))
      have h1 := h.speaker_out r k
      have h2 := h'.speaker_out r k
      rw [hdev (some (m.device r)) ((w'.speaker r).out k),
        hdev (some (m.device r)) ((w'.speaker r).out 0), hout0] at h2
      linarith
    have hfirst : ∀ b, (w'.speaker r).first b = (w.speaker r).first b := fun b =>
      (h'.speaker_first r b).trans (h.speaker_first r b).symm
    refine PlaybackDevice.ext_fields hout hfirst (fun b => ?_) (fun b => ?_)
    · obtain ⟨ρ, v, hρ, hv, e⟩ := h.speaker_asked r b
      obtain ⟨ρ', v', hρ', hv', e'⟩ := h'.speaker_asked r b
      have hρeq : ρ' = ρ := by
        apply hdinj (some (m.device r))
        rw [hdev (some (m.device r)) ((w'.speaker r).out ((w'.speaker r).first b)),
          hdev (some (m.device r)) ρ', hfirst, hout] at hρ'
        linarith
      subst hρeq
      rw [hhostp, hhost] at hv'
      rw [e', e, hv'.unique hv]
    · rw [h'.speaker_reported, h.speaker_reported, hfirst, hout, hhost, hclock, herr]
  · funext n
    rw [h'.target_eq, h.target_eq]

section Worlds

variable [DecidableEq H] {i₀ j₀ : H} {θ : Time} {w' : World H R}

omit [DecidableEq H] in
/-- Worlds built from two draws that differ by pauses of one link from `θ`
on deliver every message at the same time, or both at or after `θ` plus the
least delay of the direction of that link. -/
theorem Builds.deliversSameBefore (hB : m.Builds f d w) (hB' : m.Builds f d' w')
    (h : d.SameExceptLinkFrom d' i₀ j₀ θ) :
    World.DeliversSameBefore (θ + d.split i₀ j₀ * f.roundTrip i₀ j₀) w w' := by
  intro i j t q
  rw [hB.deliver i j t q, hB'.deliver i j t q]
  rcases arrival_of_sameExceptLinkFrom h hB hB' i j t with he | ⟨h1, h2⟩
  · left
    rw [he]
  · right
    exact ⟨_, _, rfl, rfl, h1, h2⟩

/-- **Before the difference can arrive, every solution plays the same in
both worlds.** In worlds built from two draws that differ by pauses of one
link from `θ` on, every solution plays the same at every output sample of
every playback block that is requested before `θ` plus the least delay of
the direction of that link. -/
theorem Builds.plays_eq_of_sameExcept (hB : m.Builds f d w) (hB' : m.Builds f d' w')
    (h : d.SameExceptLinkFrom d' i₀ j₀ θ) (σ : Solution H R Msg) (lookahead : ℕ+) {r : Fin R}
    {b k : ℕ} (hb : (w.speaker r).asked b < θ + d.split i₀ j₀ * f.roundTrip i₀ j₀)
    (hk : k ∈ (w.speaker r).block b) :
    σ.plays w' lookahead r k = σ.plays w lookahead r k := by
  obtain ⟨hsender, hhost, hclock, hsrc, hspk, htgt⟩ := hB.same_devices hB' h.offset
    h.logRate h.wander h.deviceLogRate h.deviceWander h.reportError h.hostPaused
  exact σ.plays_eq_of_sameBefore (w₁ := w) (w₂ := w') hsender hhost hclock hsrc hspk htgt
    (hB.deliversSameBefore hB' h) lookahead hb hk

/-- The position that a solution played last before a playback block whose
earlier blocks are all requested before `θ` plus the least delay is the same
in worlds built from two draws that differ by pauses of one link from `θ`
on. -/
theorem Builds.lastPlayed_eq (hB : m.Builds f d w) (hB' : m.Builds f d' w')
    (h : d.SameExceptLinkFrom d' i₀ j₀ θ) (σ : Solution H R Msg) (lookahead : ℕ+) {r : Fin R}
    {b : ℕ}
    (hb : ∀ b' < b, (w.speaker r).asked b' < θ + d.split i₀ j₀ * f.roundTrip i₀ j₀) :
    lastPlayed (σ.plays w' lookahead r) (b * m.blockSize)
      = lastPlayed (σ.plays w lookahead r) (b * m.blockSize) := by
  refine lastPlayed_congr fun k hk => ?_
  have hlt : k / m.blockSize < b := (Nat.div_lt_iff_lt_mul m.blockSize_pos).mpr hk
  refine hB.plays_eq_of_sameExcept hB' h σ lookahead (hb _ hlt) ?_
  unfold PlaybackDevice.block
  rw [hB.speaker_first, hB.speaker_first, List.mem_range'_1]
  have h1 := Nat.div_mul_le_self k m.blockSize
  have h2 := Nat.lt_div_mul_add (a := k) m.blockSize_pos
  have e : (k / m.blockSize + 1) * m.blockSize = k / m.blockSize * m.blockSize + m.blockSize := by
    ring
  rw [e]
  omega

/-- **What paused time of the link costs, with the room of the world
without it.** Take two draws that differ by pauses of the link from the
sender to the host of speaker `r` from `θ₁` on: `d` without and `d'` with
paused time `X` that begins between `θ₁` and `θ₂`. Let the least delays of
`d'` be not negative and its paused times never decrease. Consider a
solution whose hosts exchange messages only with the sender, whose position
at speaker `r`, in the world with the paused time, advances by at least `s`
in every step of continuous playback, with `0 ≤ s ≤ 1`. Let playback block
`b` be one whose earlier blocks are all requested before `θ₁` plus the least
delay `δ`, let capture block `c` be handed over at or after `θ₂`, and let
playback block `β` be requested no later than `θ₁ + X + δ`. Then, in the
world with the paused time, `s` for each output sample from the first of
block `b` to `K`, in a playback block up to `β`, is at most the room from the
position played last before block `b` in the world without it to
`c * blockSize - lookahead`, plus the missed samples counted at those output
samples, plus `s` times the discontinuities counted there and one more. -/
theorem Builds.stall_le_of_sameExcept (hB : m.Builds f d w) (hB' : m.Builds f d' w')
    {θ₁ θ₂ : ℝ} {r : Fin R} (h : d.SameExceptLinkFrom d' m.sender (m.host r) θ₁)
    (hpos : ∀ i j, 0 ≤ d'.split i j * f.roundTrip i j)
    (hlink : ∀ i j, Monotone (d'.linkPaused i j)) (hhost : ∀ x, Monotone (d'.hostPaused x))
    (σ : Solution H R Msg) (hstar : σ.IsStar m.sender) (lookahead : ℕ+)
    (hr : m.host r ≠ m.sender) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hslow : ∀ k x y, σ.plays w' lookahead r k = some x →
      σ.plays w' lookahead r (k + 1) = some y → x < y → y < x + 2 → x + s ≤ y)
    (hθ : θ₁ ≤ θ₂) {c β b K : ℕ} (hK : b * m.blockSize ≤ K) (hKβ : K / m.blockSize ≤ β)
    (hb : ∀ b' < b, (w.speaker r).asked b'
      < θ₁ + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r))
    (hc : θ₂ ≤ w.source.handed c)
    (hβ : (w.speaker r).asked β
      ≤ θ₁ + (d'.linkPaused m.sender (m.host r) θ₂ - d'.linkPaused m.sender (m.host r) θ₁)
        + d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)) :
    s * ((K : ℝ) + 1 - (b * m.blockSize : ℕ))
      ≤ max ((c : ℝ) * m.blockSize - ((lookahead : ℕ) : ℝ)
          - (lastPlayed (σ.plays w lookahead r) (b * m.blockSize)).getD 0) 0
        + ∑ k ∈ Finset.Ico (b * m.blockSize) (K + 1),
            (missedAt (σ.plays w' lookahead r) k : ℝ)
        + s * (∑ k ∈ Finset.Ico (b * m.blockSize) K,
            (discontinuityAt (σ.plays w' lookahead r) k : ℝ) + 1) := by
  obtain ⟨-, -, -, hsrc, hspk, -⟩ := hB.same_devices hB' h.offset h.logRate h.wander
    h.deviceLogRate h.deviceWander h.reportError h.hostPaused
  have hsplit : d'.split m.sender (m.host r) = d.split m.sender (m.host r) := by rw [h.split]
  have hmain := hB'.stall_le_of_paused hpos hlink hhost σ hstar lookahead hr hs0 hs1 hslow hθ
    hK hKβ (c := c) (by rw [hsrc]; exact hc) (by rw [hspk, hsplit]; exact hβ)
  rw [hB.lastPlayed_eq hB' h σ lookahead hb] at hmain
  exact hmain

end Worlds

end GenerativeWorld

end Unisono.Spec
