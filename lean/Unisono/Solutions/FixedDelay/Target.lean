/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.FixedDelay.Clocks
public import Unisono.Solutions.FixedDelay.Progress

/-!
# The baseline in a bounded world: the target

Notation: `o(k)` is the true time at which output sample `k` of a speaker
leaves its device, `c(f)` the true time at which frame `f` was captured,
`ρ` the nominal rate, and `ε_R`, `ε_C` and `ε_D` are the bounds on timestamp
errors, on the clocks' rate errors and on the devices' rate errors.

* The baseline's target for output sample `k` comes from an estimate of the
  capture time `o(k) - L`. This estimate is within an explicit error of
  `o(k) - L` (`target_time_error`), and the sound at the target was captured
  within a further error of `o(k) - L` (`captured_nominal`,
  `captured_target`).
* Consider a request that occurs more than the longest round trip after an
  earlier request of the same speaker, and more than the longest delay from
  the sender after the handoff of some block. Then every output sample of
  the requested block has a target, with an error that grows with the ages
  of the clock estimate and of the block (`target_band`).
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.FixedDelay

open Unisono.Spec

variable {H : Type} {R : ℕ} [DecidableEq H] (p : Params H)

omit [DecidableEq H] in
/-- **The capture time behind the baseline's target.** Speaker `r`'s host
estimates that the sound for output sample `k` of block `b` was captured at
`c(f) + (ô + (k - g) / ρ + θ̂ - L - ĉ)`. Here `f` and `ĉ` are the first frame
and timestamp of a source block `b'`, `ô` and `g` are the timestamp and
first output sample of block `b`, and `θ̂` estimates the sender's clock
minus the host's clock within `e` of their true difference at some true time
`s₂`. In a world that satisfies the bounds, this estimate is within
`2 ε_R + e + 2 ε_C |o(g) - s₂| + ε_C |o(g) - c(f)| + ε_D (k - g) / ρ` of
`o(k) - L`. -/
theorem target_time_error (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (r : Fin R)
    {b b' k : ℕ} (hk : (w.speaker r).first b ≤ k) {s₂ θ L e : ℝ}
    (hθ : |θ - ((w.clock w.sender).read s₂ - (w.clock (w.host r)).read s₂)| ≤ e) :
    |w.source.capture (w.source.first b')
        + ((w.speaker r).reported b + ((k : ℝ) - (w.speaker r).first b) / w.rate + θ - L
          - w.source.reported b')
        - ((w.speaker r).out k - L)|
      ≤ 2 * B.report + e
        + 2 * B.clockRate * |(w.speaker r).out ((w.speaker r).first b) - s₂|
        + B.clockRate * |(w.speaker r).out ((w.speaker r).first b)
            - w.source.capture (w.source.first b')|
        + B.deviceRate * ((k : ℝ) - (w.speaker r).first b) / w.rate := by
  obtain ⟨hclocks, -, hspeakers, hsrc, hsp, -, -, -, -, -, -⟩ := hw
  set g := (w.speaker r).first b
  set f := w.source.first b'
  set C := w.clock (w.host r)
  set S := w.clock w.sender
  set og := (w.speaker r).out g
  set cf := w.source.capture f
  have h₁ := abs_le.mp (hsp r b)
  have h₂ := abs_le.mp (hsrc b')
  have hθ' := abs_le.mp hθ
  have hdrift := abs_le.mp (offset_drift_abs (hclocks (w.host r)) (hclocks w.sender) s₂ og)
  have hS := abs_le.mp (Clock.read_sub_near (hclocks w.sender) cf og)
  have hout := PlaybackDevice.out_sub_mem (hspeakers r) hk
  have hrate := w.rate_pos
  have hkg : (0 : ℝ) ≤ (k : ℝ) - g := by
    have : (g : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have e1 : (1 - B.deviceRate) / w.rate * ((k : ℝ) - g)
      = ((k : ℝ) - g) / w.rate - B.deviceRate * ((k : ℝ) - g) / w.rate := by
    field_simp
  have e2 : (1 + B.deviceRate) / w.rate * ((k : ℝ) - g)
      = ((k : ℝ) - g) / w.rate + B.deviceRate * ((k : ℝ) - g) / w.rate := by
    field_simp
  rw [e1] at hout
  rw [e2] at hout
  rw [abs_le]
  constructor <;> linarith [hout.1, hout.2]

omit [DecidableEq H] in
/-- Convert a time `τ` to a position by counting from frame `f` at the
nominal rate: `x = f + (τ - c(f)) ρ`. When the capture device's rate error
is at most `ε`, the sound at `x` was captured within `ε |τ - c(f)|` of
`τ`. -/
theorem captured_nominal (w : World H R) {ε : ℝ} (hd : w.source.RateWithin w.rate ε) (f : ℕ)
    (τ : ℝ) :
    |w.captured (f + (τ - w.source.capture f) * w.rate) - τ|
      ≤ ε * |τ - w.source.capture f| := by
  have hrate := w.rate_pos
  have hcf : w.captured f = w.source.capture f := w.captured_natCast f
  set cf := w.source.capture f
  rcases le_total cf τ with h | h
  · have hle : (f : ℝ) ≤ f + (τ - cf) * w.rate := by nlinarith
    have hm := w.captured_sub_mem hd hle
    rw [hcf] at hm
    have e1 : (1 - ε) / w.rate * (f + (τ - cf) * w.rate - f) = (1 - ε) * (τ - cf) := by
      field_simp; ring
    have e2 : (1 + ε) / w.rate * (f + (τ - cf) * w.rate - f) = (1 + ε) * (τ - cf) := by
      field_simp; ring
    rw [e1] at hm
    rw [e2] at hm
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_le]
    constructor <;> nlinarith [hm.1, hm.2]
  · have hle : (f : ℝ) + (τ - cf) * w.rate ≤ f := by nlinarith
    have hm := w.captured_sub_mem hd hle
    rw [hcf] at hm
    have e1 : (1 - ε) / w.rate * (f - (f + (τ - cf) * w.rate)) = (1 - ε) * (cf - τ) := by
      field_simp; ring
    have e2 : (1 + ε) / w.rate * (f - (f + (τ - cf) * w.rate)) = (1 + ε) * (cf - τ) := by
      field_simp; ring
    rw [e1] at hm
    rw [e2] at hm
    rw [abs_of_nonpos (sub_nonpos.mpr h), abs_le]
    constructor <;> nlinarith [hm.1, hm.2]

omit [DecidableEq H] in
/-- **The capture-time error of the baseline's target.** Consider a world
that satisfies the bounds, and the target that speaker `r`'s host gives
output sample `k` of block `b`, computed from block `b'` and from a clock
estimate within `e` of the true difference at `s₂`. The sound at this target
was captured within `err + ε_D (|o(k) - L - c(f)| + err)` of `o(k) - L`,
where `err` is the bound of `target_time_error`. -/
theorem captured_target (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (r : Fin R)
    {b b' k : ℕ} (hk : (w.speaker r).first b ≤ k) {s₂ θ L e : ℝ}
    (hθ : |θ - ((w.clock w.sender).read s₂ - (w.clock (w.host r)).read s₂)| ≤ e) :
    |w.captured (w.source.first b'
        + ((w.speaker r).reported b + ((k : ℝ) - (w.speaker r).first b) / w.rate + θ - L
          - w.source.reported b') * w.rate)
        - ((w.speaker r).out k - L)|
      ≤ (2 * B.report + e
          + 2 * B.clockRate * |(w.speaker r).out ((w.speaker r).first b) - s₂|
          + B.clockRate * |(w.speaker r).out ((w.speaker r).first b)
              - w.source.capture (w.source.first b')|
          + B.deviceRate * ((k : ℝ) - (w.speaker r).first b) / w.rate)
        + B.deviceRate * (|(w.speaker r).out k - L - w.source.capture (w.source.first b')|
          + (2 * B.report + e
            + 2 * B.clockRate * |(w.speaker r).out ((w.speaker r).first b) - s₂|
            + B.clockRate * |(w.speaker r).out ((w.speaker r).first b)
                - w.source.capture (w.source.first b')|
            + B.deviceRate * ((k : ℝ) - (w.speaker r).first b) / w.rate)) := by
  have hτ := target_time_error w B hw r (b' := b') hk (L := L) hθ
  set cf := w.source.capture (w.source.first b')
  set τ := cf + ((w.speaker r).reported b + ((k : ℝ) - (w.speaker r).first b) / w.rate + θ - L
    - w.source.reported b') with hτdef
  set err := 2 * B.report + e
    + 2 * B.clockRate * |(w.speaker r).out ((w.speaker r).first b) - s₂|
    + B.clockRate * |(w.speaker r).out ((w.speaker r).first b) - cf|
    + B.deviceRate * ((k : ℝ) - (w.speaker r).first b) / w.rate
  have hpos : ((w.speaker r).reported b + ((k : ℝ) - (w.speaker r).first b) / w.rate + θ - L
      - w.source.reported b') = τ - cf := by rw [hτdef]; ring
  rw [hpos]
  have hcap := captured_nominal w hw.2.1 (w.source.first b') τ
  have hε := B.deviceRate_nonneg
  have h1 : |τ - cf| ≤ |(w.speaker r).out k - L - cf| + err := by
    calc |τ - cf| = |(τ - ((w.speaker r).out k - L)) + ((w.speaker r).out k - L - cf)| := by ring_nf
      _ ≤ |τ - ((w.speaker r).out k - L)| + |(w.speaker r).out k - L - cf| := abs_add_le _ _
      _ ≤ err + |(w.speaker r).out k - L - cf| := by linarith
      _ = |(w.speaker r).out k - L - cf| + err := by ring
  calc |w.captured (w.source.first b' + (τ - cf) * w.rate) - ((w.speaker r).out k - L)|
      = |(w.captured (w.source.first b' + (τ - cf) * w.rate) - τ) + (τ - ((w.speaker r).out k - L))| := by
        ring_nf
    _ ≤ |w.captured (w.source.first b' + (τ - cf) * w.rate) - τ| + |τ - ((w.speaker r).out k - L)| :=
        abs_add_le _ _
    _ ≤ B.deviceRate * |τ - cf| + err := add_le_add hcap hτ
    _ ≤ B.deviceRate * (|(w.speaker r).out k - L - cf| + err) + err :=
        by gcongr
    _ = err + B.deviceRate * (|(w.speaker r).out k - L - cf| + err) := by ring

/-- **The baseline's target at a request.** Consider a world that satisfies
the bounds, and a step `n` at which the host of speaker `r`, other than the
sender's host, handles request `b`. Suppose an earlier request `b₀` of `r`
occurred more than the longest round trip between that host and the sender
before request `b`, and a block `b''` was handed over more than the longest
delay from the sender to that host before request `b`. Then every output
sample `k` of the block has a target, and the sound at the target was
captured within an explicit error of `o(k) - L`. The error grows with the
ages `A₁ = a(b) - a(b₀)` and `A₂ = a(b) - h(b'')`, where `a(b)` is the true
time of request `b` and `h(b'')` is the true time of the handoff of block
`b''`. -/
theorem target_band (w : World H R) (B : Bounds H) (hw : w.WithinBounds B) (lookahead : ℕ+)
    (hsender : p.sender = w.sender) (hrate : p.rate = w.rate) (hnodup : p.speakers.Nodup)
    (hcopies : B.lossRun < p.copies) (hperiod : 0 ≤ p.period) (hL : 0 ≤ p.latency)
    {r : Fin R} (hh : w.host r ∈ p.speakers) (hhs : w.host r ≠ w.sender)
    {n b : ℕ}
    (he : earliest (((solution p : Solution H R Payload).states w lookahead n).key w)
      ((solution p : Solution H R Payload).states w lookahead n).due = some (.asked r b))
    {b₀ b'' : ℕ}
    (hb₀ : (w.speaker r).asked b₀ + B.delayMost (w.host r) w.sender + B.delayMost w.sender (w.host r)
      < (w.speaker r).asked b)
    (hb'' : w.source.handed b'' + B.delayMost w.sender (w.host r) < (w.speaker r).asked b)
    {k : ℕ} (hk : k ∈ (w.speaker r).block b) :
    ∃ x, target p (memoryOf p (w.host r)
        (((solution p : Solution H R Payload).states w lookahead n).views (w.host r)))
        ((w.speaker r).first b) ((w.speaker r).reported b) k = some x ∧
      |w.captured x - ((w.speaker r).out k - p.latency)|
        ≤ (2 * B.report
            + (max (B.delayMost (w.host r) w.sender - B.delayLeast w.sender (w.host r))
                (B.delayMost w.sender (w.host r) - B.delayLeast (w.host r) w.sender)
              + B.clockRate * (B.delayMost (w.host r) w.sender + B.delayMost w.sender (w.host r))) / 2
            + 2 * B.clockRate * (B.leadMost + ((w.speaker r).asked b - (w.speaker r).asked b₀)
                + p.period / (1 - B.clockRate))
            + B.clockRate * (B.leadMost + ((w.speaker r).asked b - w.source.handed b'') + B.handoff
                + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate)
            + B.deviceRate * (B.blockMost - 1) / w.rate)
          + B.deviceRate * (p.latency + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate
            + (B.leadMost + ((w.speaker r).asked b - w.source.handed b'') + B.handoff
                + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate)
            + (2 * B.report
            + (max (B.delayMost (w.host r) w.sender - B.delayLeast w.sender (w.host r))
                (B.delayMost w.sender (w.host r) - B.delayLeast (w.host r) w.sender)
              + B.clockRate * (B.delayMost (w.host r) w.sender + B.delayMost w.sender (w.host r))) / 2
            + 2 * B.clockRate * (B.leadMost + ((w.speaker r).asked b - (w.speaker r).asked b₀)
                + p.period / (1 - B.clockRate))
            + B.clockRate * (B.leadMost + ((w.speaker r).asked b - w.source.handed b'') + B.handoff
                + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate)
            + B.deviceRate * (B.blockMost - 1) / w.rate)) := by
  set h := w.host r with hhdef
  have hw' := hw
  obtain ⟨hclocks, hsrc, hspk, -, -, hhand, hlead, hblocks, hblocksr, hdelays, -⟩ := hw'
  -- The step's event is the request.
  have hn := Solution.handled_of_asked w (solution p) lookahead he
  have htime : (solution p : Solution H R Payload).eventTime w lookahead n = (w.speaker r).asked b :=
    Solution.handled_time w (solution p) lookahead hn
  -- The block remembered.
  obtain ⟨β, hblock, hββ, hβt⟩ := block_memory p w B hw lookahead hsender hnodup hcopies hh hhs
    (k := n) (by rw [htime]; exact hb'')
  rw [htime] at hβt
  -- The remembered clock estimate, from a recent query.
  obtain ⟨n₀, hn₀b, he₀⟩ := request_step p w B hw lookahead r b₀
  have hh₀ := Solution.handled_of_asked w (solution p) lookahead he₀
  obtain ⟨t₁, θ, s, hoff, hst₁, hs⟩ := offset_recent p w B hw lookahead hsender hcopies hperiod
    hhs hh₀ (k := n) (by rw [htime]; linarith)
  obtain ⟨s₁, s₂, s₄, hs₁, hs₄, hd1, hd1', hd2, hd2', hθ⟩ :=
    offset_sample p w B hw lookahead hsender hhs hoff
  rw [htime] at hs₄
  have hpos₁ := B.delayLeast_pos h w.sender
  have hpos₂ := B.delayLeast_pos w.sender h
  have hNTP := offset_error (S := w.clock w.sender) (hclocks h) hd1 hd1' hd2 hd2' hpos₁ hpos₂
  rw [← hθ] at hNTP
  have hss₁ : s ≤ s₁ := by
    rw [← hs₁] at hst₁
    exact (w.clock h).strictMono.le_iff_le.mp hst₁
  -- The target.
  have htarget : target p (memoryOf p h (((solution p : Solution H R Payload).states w lookahead n).views h))
      ((w.speaker r).first b) ((w.speaker r).reported b) k
      = some (w.source.first β + (((w.speaker r).reported b + ((k : ℝ) - (w.speaker r).first b) / w.rate
          + θ - p.latency) - w.source.reported β) * w.rate) := by
    simp only [target, hblock, hoff, hrate]
  refine ⟨_, htarget, ?_⟩
  have hkb : (w.speaker r).first b ≤ k ∧ k < (w.speaker r).first (b + 1) := by
    unfold PlaybackDevice.block at hk
    rw [List.mem_range'_1] at hk
    have := (w.speaker r).first_strictMono (Nat.lt_succ_self b)
    omega
  have hcap := captured_target w B hw r (b' := β) hkb.1 (L := p.latency) hNTP
  have e1 : w.source.first β + ((w.speaker r).reported b + ((k : ℝ) - (w.speaker r).first b) / w.rate
        + θ - p.latency - w.source.reported β) * w.rate
      = w.source.first β + (((w.speaker r).reported b + ((k : ℝ) - (w.speaker r).first b) / w.rate
        + θ - p.latency) - w.source.reported β) * w.rate := by ring
  rw [e1] at hcap
  refine hcap.trans ?_
  -- The spans in the bound.
  set g := (w.speaker r).first b
  set og := (w.speaker r).out g
  set cf := w.source.capture (w.source.first β)
  have hrate0 := w.rate_pos
  have hεC := B.clockRate_nonneg
  have hεD := B.deviceRate_nonneg
  have hεD1 := B.deviceRate_lt_one
  have hεC1 := B.clockRate_lt_one
  have hleadb := hlead r b
  have hbefore := (w.speaker r).asked_before b
  -- The age of the estimate's query at the request.
  have hspan₁ : |og - s₂| ≤ B.leadMost + ((w.speaker r).asked b - (w.speaker r).asked b₀)
      + p.period / (1 - B.clockRate) := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- The block's span.
  have hcfβ : cf ≤ w.source.handed β := by
    have h1 := w.source.handed_after β
    have h2 : w.source.first β ≤ w.source.first (β + 1) - 1 := by
      have := w.source.first_strictMono (Nat.lt_succ_self β)
      simp only [Nat.succ_eq_add_one] at this
      omega
    have := w.source.capture_strictMono.monotone h2
    linarith
  have hcf'' : w.source.handed b'' - B.handoff - (B.blockMost - 1) * (1 + B.deviceRate) / w.rate
      ≤ cf := by
    have h1 := hhand b''
    have hfirst : w.source.first b'' ≤ w.source.first (b'' + 1) - 1 := by
      have := w.source.first_strictMono (Nat.lt_succ_self b'')
      simp only [Nat.succ_eq_add_one] at this
      omega
    have hspan := (CaptureDevice.capture_sub_mem hsrc hfirst).2
    have hsize := (hblocks b'').2
    have hcast : ((w.source.first (b'' + 1) - 1 : ℕ) : ℝ) - (w.source.first b'' : ℝ)
        ≤ (B.blockMost : ℝ) - 1 := by
      have hb1 := B.blockLeast_pos.trans_le B.blockLeast_le
      have : w.source.first (b'' + 1) - 1 ≤ w.source.first b'' + (B.blockMost - 1) := by omega
      have : ((w.source.first (b'' + 1) - 1 : ℕ) : ℝ) ≤ (w.source.first b'' : ℝ)
          + ((B.blockMost - 1 : ℕ) : ℝ) := by exact_mod_cast this
      have h3 : ((B.blockMost - 1 : ℕ) : ℝ) = (B.blockMost : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ B.blockMost)]; simp
      linarith
    have hcoef : 0 ≤ (1 + B.deviceRate) / w.rate := div_nonneg (by linarith) hrate0.le
    have hmul := mul_le_mul_of_nonneg_left hcast hcoef
    have hmono : w.source.capture (w.source.first b'') ≤ cf :=
      w.source.capture_strictMono.monotone (w.source.first_strictMono.monotone hββ)
    have e : (B.blockMost - 1 : ℝ) * (1 + B.deviceRate) / w.rate
        = (1 + B.deviceRate) / w.rate * (B.blockMost - 1) := by ring
    rw [e]
    linarith
  have hspan₂ : |og - cf| ≤ B.leadMost + ((w.speaker r).asked b - w.source.handed b'') + B.handoff
      + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- The output sample's place in its block.
  have hkg : ((k : ℝ) - g) ≤ (B.blockMost : ℝ) - 1 := by
    have hsize := (hblocksr r b).2
    have : k ≤ g + (B.blockMost - 1) := by omega
    have hb1 := B.blockLeast_pos.trans_le B.blockLeast_le
    have : (k : ℝ) ≤ (g : ℝ) + ((B.blockMost - 1 : ℕ) : ℝ) := by exact_mod_cast this
    have h3 : ((B.blockMost - 1 : ℕ) : ℝ) = (B.blockMost : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ B.blockMost)]; simp
    linarith
  have hkg0 : (0 : ℝ) ≤ (k : ℝ) - g := by
    have : (g : ℝ) ≤ k := by exact_mod_cast hkb.1
    linarith
  have hout := (PlaybackDevice.out_sub_mem (hspk r) hkb.1).2
  have hcoef : 0 ≤ (1 + B.deviceRate) / w.rate := div_nonneg (by linarith) hrate0.le
  have hok : (w.speaker r).out k - og ≤ (B.blockMost - 1) * (1 + B.deviceRate) / w.rate := by
    have := mul_le_mul_of_nonneg_left hkg hcoef
    have e : (B.blockMost - 1 : ℝ) * (1 + B.deviceRate) / w.rate
        = (1 + B.deviceRate) / w.rate * (B.blockMost - 1) := by ring
    rw [e]
    linarith
  have hspan₃ : |(w.speaker r).out k - p.latency - cf| ≤ p.latency
      + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate
      + (B.leadMost + ((w.speaker r).asked b - w.source.handed b'') + B.handoff
        + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate) := by
    have hok0 : og ≤ (w.speaker r).out k :=
      (w.speaker r).out_strictMono.monotone hkb.1
    have hcfo : cf ≤ og := by linarith
    have hspan0 : 0 ≤ (B.blockMost - 1 : ℝ) * (1 + B.deviceRate) / w.rate := by
      have hb1 : (1 : ℝ) ≤ B.blockMost := by
        exact_mod_cast B.blockLeast_pos.trans_le B.blockLeast_le
      apply div_nonneg _ hrate0.le
      exact mul_nonneg (by linarith) (by linarith)
    have hS2 : 0 ≤ B.leadMost + ((w.speaker r).asked b - w.source.handed b'') + B.handoff
        + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate := le_trans (abs_nonneg _) hspan₂
    have hoc := le_abs_self (og - cf)
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hkgρ : B.deviceRate * ((k : ℝ) - g) / w.rate ≤ B.deviceRate * (B.blockMost - 1) / w.rate := by
    apply div_le_div_of_nonneg_right _ hrate0.le
    exact mul_le_mul_of_nonneg_left hkg hεD
  have h1 := mul_le_mul_of_nonneg_left hspan₁ (show 0 ≤ 2 * B.clockRate by linarith)
  have h2 := mul_le_mul_of_nonneg_left hspan₂ hεC
  have herr : 2 * B.report
        + (max (B.delayMost h w.sender - B.delayLeast w.sender h)
            (B.delayMost w.sender h - B.delayLeast h w.sender)
          + B.clockRate * (B.delayMost h w.sender + B.delayMost w.sender h)) / 2
        + 2 * B.clockRate * |og - s₂| + B.clockRate * |og - cf| + B.deviceRate * ((k : ℝ) - g) / w.rate
      ≤ 2 * B.report
        + (max (B.delayMost h w.sender - B.delayLeast w.sender h)
            (B.delayMost w.sender h - B.delayLeast h w.sender)
          + B.clockRate * (B.delayMost h w.sender + B.delayMost w.sender h)) / 2
        + 2 * B.clockRate * (B.leadMost + ((w.speaker r).asked b - (w.speaker r).asked b₀)
            + p.period / (1 - B.clockRate))
        + B.clockRate * (B.leadMost + ((w.speaker r).asked b - w.source.handed b'') + B.handoff
            + (B.blockMost - 1) * (1 + B.deviceRate) / w.rate)
        + B.deviceRate * (B.blockMost - 1) / w.rate := by
    linarith
  exact add_le_add herr (mul_le_mul_of_nonneg_left (add_le_add hspan₃ herr) hεD)

end Unisono.Solutions.FixedDelay
