/-
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.
-/
module
public import Unisono.Solutions.Controller.SteppedLevel
public import Unisono.Spec.Models.GenerativeSteadyBound

/-!
# What a block of the source needs

A speaker plays a position only if the capture block that the position
needs arrived before the playback device requested the block of the output
sample. The *need* of a capture block at a speaker is a level at which the
block is in time for every position that needs it. A host can compute it
from what it observes, and report it to the sender.

* `needOf`: the need of capture block `c` at speaker `r`, with clocks at
  constant rates, in seconds of the sender's clock: the time from the
  capture of the block's first frame to the arrival of the block, minus the
  asymmetry of the speaker's host, plus the request lead, the time of one
  playback block and the time of `ahead` frames.
* `arrival_lt_asked_of_needOf_le`: if the level of a position that is due
  is at least the need of the block that the position needs, taken with the
  resampler's lookahead for `ahead`, that block arrives strictly before the
  request. With `speaker_plays_of_levels`, the position then plays.
* `level_lt_needOf_of_silent`: so, from some output sample on, an output
  sample that plays nothing of the source has a due position whose level is
  below the need of its block.
* `NeedSettings`, `needOfBlock`, `blockNeeds`, `measuredNeed`: what a host
  computes. From its estimate `cl` of the sender's clock, its estimate `dl`
  of when its output samples leave, the reading of its clock at which a
  block arrived and the block's header, the need of the block is the
  sender's reading at the arrival, plus the lead and one playback block in
  the sender's seconds, minus the capture time of the first position that
  needs the block. A clock query reports the largest need of the blocks that
  arrived since the host sent the newest query that has been answered.
* `needOfBlock_eq`: with clocks at constant rates and exact lines, what the
  host computes for a block is `needOf` with the told bound `ahead` on the
  lookahead.

The need is cautious by the time of one output sample and by the frames
between the lookahead and its told bound. Nothing here says which needs
reach the sender, or what the level rule does with them.
-/

@[expose] public noncomputable section

namespace Unisono.Solutions.Controller

open Unisono.Spec Unisono.Spec.GenerativeWorld

variable {H : Type} {R : ℕ} {m : GenerativeWorld H R} {f : Member H R} {d : Draw H R}
  {w : World H R}

/-- **The need of capture block `c` at speaker `r`**, with clocks at
constant rates, in seconds of the sender's clock: the rate of the sender's
clock times the following. The true time from the capture of the block's
first frame to the arrival of the block at the speaker's host, minus the
asymmetry of that host, plus the request lead in true time, the time of one
playback block and the time of `ahead` frames. -/
def needOf (m : GenerativeWorld H R) (f : Member H R) (d : Draw H R) (w : World H R)
    (ahead : ℝ) (r : Fin R) (c : ℕ) : ℝ :=
  Real.exp (d.logRate m.sender)
    * (d.arrival f m.sender (m.host r) (w.source.handed c)
      - w.source.capture (c * m.blockSize)
      - (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
        - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2
      + leadOf m d r + (m.blockSize : ℝ) * outputPeriodOf m d r
      + ahead * capturePeriodOf m d)

/-- **A block is in time when the level covers its need.** In a world whose
clocks run at constant rates, let the position `x` be due at output sample
`k` of speaker `r`, and let the level of `x` be at least the need of the
capture block that `x` needs, taken with the resampler's lookahead. Then the
message of that block arrives strictly before the playback device requests
the block of the output sample. -/
theorem arrival_lt_asked_of_needOf_le (hS : ConstantRates m f d w) (lookahead : ℕ+)
    {ann : ℕ → ℝ × ℝ} {r : Fin R} {k : ℕ} {x : ℝ} (hx : IsDue m f d w ann r k x)
    (hneed : needOf m f d w ((lookahead : ℕ) : ℝ) r (neededBlock m lookahead x)
      ≤ levelAt ann m.blockSize x) :
    d.arrival f m.sender (m.host r) (w.source.handed (neededBlock m lookahead x))
      < (w.speaker r).asked (k / m.blockSize) := by
  have hrs := Real.exp_pos (d.logRate m.sender)
  have hpc := capturePeriodOf_pos m d
  have hpr := outputPeriodOf_pos m d r
  obtain ⟨hxB, hxe⟩ := hx
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hxB
  have hla : (1 : ℝ) ≤ ((lookahead : ℕ) : ℝ) := by exact_mod_cast lookahead.pos
  obtain ⟨c, hc⟩ : ∃ c, c = neededBlock m lookahead x := ⟨_, rfl⟩
  rw [← hc] at hneed ⊢
  -- The block that the position needs starts less than the lookahead after it.
  have hcB : ((c * m.blockSize : ℕ) : ℝ) < x + ((lookahead : ℕ) : ℝ) := by
    have hpos : 0 < ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ := Nat.ceil_pos.mpr (by linarith)
    have h1 : c * m.blockSize ≤ ⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 := by
      rw [hc]
      exact Nat.div_mul_le_self _ _
    have h2 := Nat.ceil_lt_add_one (a := x + ((lookahead : ℕ) : ℝ)) (by linarith)
    have h3 : ((c * m.blockSize : ℕ) : ℝ) ≤ ((⌈x + ((lookahead : ℕ) : ℝ)⌉₊ - 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [Nat.cast_sub hpos, Nat.cast_one] at h3
    linarith
  have hcap : w.captured x - w.source.capture (c * m.blockSize)
      = (x - ((c * m.blockSize : ℕ) : ℝ)) * capturePeriodOf m d := by
    rw [hS.captured, hS.capture]
    unfold capturePeriodOf
    ring
  have hask := hS.asked_eq r (k / m.blockSize)
  have hout := hS.out_eq r k
  have hkB : (k : ℝ) < ((k / m.blockSize : ℕ) : ℝ) * m.blockSize + m.blockSize := by
    exact_mod_cast Nat.lt_div_mul_add m.blockSize_pos
  have h2 : -((lookahead : ℕ) : ℝ) * capturePeriodOf m d
      < (x - ((c * m.blockSize : ℕ) : ℝ)) * capturePeriodOf m d :=
    mul_lt_mul_of_pos_right (by linarith) hpc
  have h3 := mul_lt_mul_of_pos_right hkB hpr
  unfold needOf at hneed
  simp only [latencyOf] at hxe
  have h4 := (le_div_iff₀' hrs).mpr hneed
  linarith

variable [DecidableEq H]

/-- **An output sample that plays nothing had a level below a need.** In
the setting of `speaker_plays_of_levels`, let also every announced level be
at least `Llo`. Then, from some output sample on: if output sample `k` plays
nothing of the source, a position is due at `k` whose level is less than the
need of the capture block that it needs, taken with the resampler's
lookahead. -/
theorem level_lt_needOf_of_silent (p : FixedDelay.Params H) (hS : ConstantRates m f d w)
    (lookahead : ℕ+) {clockEst : ClockEstimator} {deviceEst : DeviceEstimator}
    (hdev : deviceEst.Exact) (levelRule : LevelRule H R) (ann : ℕ → ℝ × ℝ)
    (hann : ∀ i b, 1 ≤ b →
      (solution p clockEst deviceEst levelRule : Solution H R Payload).handled w lookahead i
        = some (w.sender, w.source.handed b,
          .handed ((w.source.block b).map fun k => (k, w.target k)) (w.source.reported b)) →
      levelRule.announce
          (((solution p clockEst deviceEst levelRule : Solution H R Payload).states w
              lookahead i).views w.sender
            ++ [⟨(w.clock w.sender).read (w.source.handed b),
              .handed ((w.source.block b).map fun k => (k, w.target k))
                (w.source.reported b)⟩])
          (w.source.first b) = ann b)
    (hcont : ∀ b, 1 ≤ b → (ann (b + 1)).1 = (ann b).1 + (m.blockSize : ℝ) * (ann b).2)
    (hadv : ∀ b, 1 ≤ b → 0 < Real.exp (d.logRate m.sender)
      / (m.rate * Real.exp (d.deviceLogRate none)) + (ann b).2)
    {Llo : ℝ} (hlo : ∀ b, 1 ≤ b → Llo ≤ (ann b).1)
    (hps : p.sender = m.sender) (hnodup : p.speakers.Nodup) (hcopies : 0 < p.copies)
    (r : Fin R) (hnos : m.host r ≠ m.sender) (hpsp : m.host r ∈ p.speakers) {T₀ : Time}
    (hline : ClockLineFrom (solution p clockEst deviceEst levelRule) w lookahead
      clockEst (m.host r) (exchangeLine m f d (m.host r)) T₀) :
    ∃ K, ∀ k, K ≤ k →
      (solution p clockEst deviceEst levelRule : Solution H R Payload).plays w lookahead
          r k = none →
      ∃ x, IsDue m f d w ann r k x
        ∧ levelAt ann m.blockSize x
          < needOf m f d w ((lookahead : ℕ) : ℝ) r (neededBlock m lookahead x) := by
  have hrs := Real.exp_pos (d.logRate m.sender)
  have hpr := outputPeriodOf_pos m d r
  obtain ⟨K, hK⟩ := speaker_plays_of_levels p hS lookahead hdev levelRule ann hann hcont hadv
    hps hnodup hcopies r hnos hpsp hline
  -- From some output sample on, the first frame of capture block one is due.
  obtain ⟨K₂, hK₂⟩ := exists_nat_ge
    (((Real.exp (d.logRate m.sender) / (m.rate * Real.exp (d.deviceLogRate none))
          * (m.blockSize : ℝ) + (ann 1).1) / Real.exp (d.logRate m.sender)
        + w.source.capture 0
        + (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
          - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2
        - (w.speaker r).out 0) / outputPeriodOf m d r)
  refine ⟨max K K₂, fun k hk hnone => ?_⟩
  obtain ⟨-, -, h3⟩ := hK k (le_trans (le_max_left _ _) hk)
  have hkK₂ : ((K₂ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hk
  have hdue : Real.exp (d.logRate m.sender) / (m.rate * Real.exp (d.deviceLogRate none))
        * (m.blockSize : ℝ) + (ann 1).1
      ≤ Real.exp (d.logRate m.sender)
        * ((w.speaker r).out k - w.source.capture 0
          - (d.split m.sender (m.host r) * f.roundTrip m.sender (m.host r)
            - d.split (m.host r) m.sender * f.roundTrip (m.host r) m.sender) / 2) := by
    have h1 := (div_le_iff₀ hpr).mp (hK₂.trans hkK₂)
    have h2 := hS.out_eq r k
    rw [← div_le_iff₀' hrs]
    linarith
  obtain ⟨x, hx⟩ := exists_isDue hS hcont hadv hlo r hdue
  refine ⟨x, hx, ?_⟩
  by_contra hcon
  have harr := arrival_lt_asked_of_needOf_le hS lookahead hx (not_lt.mp hcon)
  rw [h3 x hx harr] at hnone
  exact absurd hnone (by simp)

/-- The settings that a host uses to compute needs. All three are told. -/
structure NeedSettings where
  /-- The request lead of the playback devices, in seconds. -/
  lead : ℝ
  /-- The number of output samples of a playback block. -/
  blockSize : ℕ
  /-- An upper bound for the resampler's lookahead, in frames. -/
  ahead : ℝ

/-- **The need of a block, as a host computes it.** The host's estimate `cl`
of the sender's clock gives the sender's reading when the block arrived, at
the reading `τ` of the host's clock. The lead and one playback block are
`lead * rate + blockSize` output samples; an output sample takes `dl.slope`
on the host's clock by the host's estimate `dl` of when its output samples
leave, and `cl.slope` times that on the sender's clock. The first position
that needs the block is `ahead` frames before the block's first frame; its
capture time on the sender's clock, by the block's header, is
`hd.capture - ahead * hd.period`. -/
def needOfBlock (p : FixedDelay.Params H) (s : NeedSettings) (cl dl : Line) (τ : ℝ)
    (hd : Header) : ℝ :=
  cl.eval τ + cl.slope * dl.slope * (s.lead * p.rate + s.blockSize)
    - (hd.capture - s.ahead * hd.period)

/-- The needs of the blocks that arrived in a view at readings of the
host's clock at or after `start`, or of all the blocks if there is no
`start`. -/
def blockNeeds (p : FixedDelay.Params H) (s : NeedSettings) (cl dl : Line) (start : Option ℝ)
    (l : List (Event H R Payload)) : List ℝ :=
  l.filterMap fun e =>
    match e.observation with
    | .received _ (.block first _ capture period level slope) _ _ =>
        if (start.map fun t => decide (t ≤ e.reading)).getD true then
          some (needOfBlock p s cl dl e.reading ⟨first, capture, period, level, slope⟩)
        else none
    | _ => none

/-- **The need that a clock query reports.** When a playback device of the
host requests a block, with the host's estimates of the sender's clock and
of when that device's output samples leave: the largest need of the blocks
that arrived since the host sent the newest clock query that has been
answered. There is none while an estimate is missing or no such block
arrived. -/
def measuredNeed (p : FixedDelay.Params H) (clockEst : ClockEstimator)
    (deviceEst : DeviceEstimator) (s : NeedSettings) :
    H → List (Event H R Payload) → Option ℝ := fun h l =>
  match l.getLast?, clockOf p clockEst h l with
  | some e, some cl =>
      match e.observation with
      | .asked r _ _ =>
          match deviceEst (playbackReports r l) with
          | some dl =>
              (blockNeeds p s cl dl (((exchangesOf l).map Exchange.sent).max?) l).max?
          | none => none
      | _ => none
  | _, _ => none

omit [DecidableEq H] in
/-- **With exact lines a host computes the need of a block.** In a world
whose clocks run at constant rates, take for `cl` the line of the undelayed
exchanges of the host of speaker `r`, for `dl` the line on which the
readings of that host's clock lie when the speaker's output samples leave,
for `τ` the reading of the host's clock when capture block `c` arrived, and
a header with the exact capture time and period of the block. If the
settings are the model's lead, block size and rate, the host computes
`needOf` with `ahead`. -/
theorem needOfBlock_eq (hS : ConstantRates m f d w) (p : FixedDelay.Params H)
    (s : NeedSettings) (hrate : p.rate = m.rate) (hlead : s.lead = m.lead)
    (hsB : s.blockSize = m.blockSize) (r : Fin R) (c : ℕ) {hd : Header}
    (hcap : hd.capture = f.captureStart + Real.exp (d.logRate m.sender)
      / (m.rate * Real.exp (d.deviceLogRate none)) * ((c * m.blockSize : ℕ) : ℝ))
    (hper : hd.period = Real.exp (d.logRate m.sender)
      / (m.rate * Real.exp (d.deviceLogRate none))) :
    needOfBlock p s (exchangeLine m f d (m.host r))
        ⟨f.speakerStart (m.device r), Real.exp (d.logRate (m.host r))
          / (m.rate * Real.exp (d.deviceLogRate (some (m.device r))))⟩
        ((w.clock (m.host r)).read
          (d.arrival f m.sender (m.host r) (w.source.handed c))) hd
      = needOf m f d w s.ahead r c := by
  have hρ := m.rate_pos.ne'
  have hrs := (Real.exp_pos (d.logRate m.sender)).ne'
  have hrh := (Real.exp_pos (d.logRate (m.host r))).ne'
  have hgc := (Real.exp_pos (d.deviceLogRate none)).ne'
  have hgr := (Real.exp_pos (d.deviceLogRate (some (m.device r)))).ne'
  unfold needOfBlock needOf
  rw [hcap, hper, hrate, hlead, hsB, hS.clock, hS.capture]
  simp only [Line.eval, exchangeLine, leadOf, outputPeriodOf, capturePeriodOf]
  field_simp
  ring

end Unisono.Solutions.Controller
